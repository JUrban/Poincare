(* ========================================================================= *)
(* pc_moi_s34_h1: the Sec 34 unit s34_h1.  Main theorem LEMMA4 :             *)
(* |- MOI_S34_LEMMA4 (pc_moi_s34_stmt.ml; Moise, Geometric Topology in       *)
(* Dimensions 2 and 3, GTM 47, Sec 34, p.241, Lemma 4): a polyhedral 3-cell *)
(* c with h(s) inside interior c and c inside a suitable open w0 has trace *)
(* on the face torus T = f1(N_s) carrying H_1(T).  Route (the book's cycles *)
(* Z^1, Z_1, Z_2, by Mayer-Vietoris, pc_top_mv): R = h(Bd s) carries H_1(T) *)
(* (frame, LOOPS_CARRIED_IMP_CARRIES_H1).  Step A: Mayer-Vietoris on the   *)
(* contractible image cc of a cone on Bd s (pieces cc INTER interior c and  *)
(* cc minus (c minus u)) and the derived-neighbourhood retraction of a      *)
(* triangulated pair (c INTER t2, frontier c INTER t2), t2 a polyhedral     *)
(* neighbourhood of cc INTER c in interior T: a subset of frontier c INTER  *)
(* interior T carries.  Step B: Mayer-Vietoris on the 2-sphere frontier c  *)
(* and the retraction of (frontier c INTER T, frontier c INTER q), q = T   *)
(* INTER f1(Bd N): frontier c INTER q carries, and it is the trace on T.   *)
(* w0 avoids cc minus interior T and the vertex balls of the vertices     *)
(* outside s, so that the points of frontier c on T outside interior T lie *)
(* on f1(Bd N).  The crossing and finiteness hypotheses are not needed.    *)
(* Contents, in order: carrying lemmas; the pair retraction; the             *)
(* Mayer-Vietoris push and trivial H_1; the cone; Steps A and B; complex and *)
(* face-torus facts; path-connectedness and the cone image; LEMMA4.          *)
(* ========================================================================= *)

needs "src/pc_moi_s34_stmt.ml";;
needs "src/pc_top_mv.ml";;
needs "src/pc_moi_fnd_h1.ml";;
needs "src/pc_moi_fnd_rn.ml";;
needs "src/pc_moi_s34_outer.ml";;
needs "src/pc_moi_s34_fball.ml";;
needs "src/pc_top_lochom.ml";;
needs "src/pc_moi_cglue.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Carrying H_1: monotonicity, transport by homotopic maps, and the         *)
(* Mayer-Vietoris step (a class carried by r SUBSET a comes from a INTER b  *)
(* when a UNION b is an open cover of a space with trivial H_1).            *)
(* ------------------------------------------------------------------------- *)

let MOI_S4J_CARRIES_MONO = prove
 (`!(j:real^N->bool) k s.
     j SUBSET k /\ k SUBSET s /\ carries_h1 j s ==> carries_h1 k s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[carries_h1; group_image] THEN STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`&1:int`; `subtopology euclidean (k:real^N->bool)`;
                   `subtopology euclidean (s:real^N->bool)`; `\x:real^N. x`]
                  GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY) THEN
    SIMP_TAC[group_homomorphism];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN
   `hom_induced (&1) (subtopology euclidean (j:real^N->bool),{})
                     (subtopology euclidean s,{}) (\x. x) =
    hom_induced (&1) (subtopology euclidean k,{}) (subtopology euclidean s,{}) (\x. x) o
    hom_induced (&1) (subtopology euclidean j,{}) (subtopology euclidean k,{}) (\x. x)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC ATOP_HOM_INDUCED_INCLUSIONS THEN
    ASM_SIMP_TAC[ATOP_CONTINUOUS_MAP_INCLUSION; SUBSET_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
  MP_TAC(ISPECL [`&1:int`; `subtopology euclidean (j:real^N->bool)`;
                 `subtopology euclidean (k:real^N->bool)`; `\x:real^N. x`]
                GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY) THEN
  SIMP_TAC[group_homomorphism]);;

let MOI_S4J_HOM_IN = prove
 (`!G H (f:A->B) x.
     group_homomorphism (G,H) f /\ x IN group_carrier G ==> f x IN group_carrier H`,
  REWRITE_TAC[group_homomorphism] THEN SET_TAC[]);;

let MOI_S4J_MV_LIFT = prove
 (`!top s t (a:((num->real)->A)frag->bool).
     open_in top s /\ open_in top t /\ topspace top = s UNION t /\
     trivial_group (homology_group(&1,top)) /\
     a IN group_carrier (homology_group(&1,subtopology top s))
     ==> ?c. c IN group_carrier (homology_group(&1,subtopology top (s INTER t))) /\
             hom_induced (&1) (subtopology top (s INTER t),{}) (subtopology top s,{})
                         (\x. x) c = a`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`&1:int`; `top:A topology`; `s:A->bool`; `t:A->bool`]
    (REWRITE_RULE[ATOP_MAYER_VIETORIS_STATEMENT] ATOP_MAYER_VIETORIS)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd:(((num->real)->A)frag->bool)->((num->real)->A)frag->bool`
    (MP_TAC o CONJUNCT1)) THEN
  DISCH_THEN(MP_TAC o SPEC
   `(a:((num->real)->A)frag->bool,
     group_id (homology_group(&1,subtopology top (t:A->bool))))` o
   MATCH_MP (REWRITE_RULE[IMP_CONJ] ATOP_EXACT_IMAGE)) THEN
  REWRITE_TAC[PROD_GROUP; IN_CROSS; GROUP_ID] THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN
    MATCH_MP_TAC ATOP_TRIVIAL_GROUP_ELEMENT THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC GROUP_DIV THEN CONJ_TAC THEN MATCH_MP_TAC MOI_S4J_HOM_IN THENL
     [EXISTS_TAC `homology_group(&1,subtopology top (s:A->bool))` THEN
      ASM_REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY];
      EXISTS_TAC `homology_group(&1,subtopology top (t:A->bool))` THEN
      REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY; GROUP_ID]];
    ALL_TAC] THEN
  REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]);;

let MOI_S4J_SUBTOP = prove
 (`!(x:real^N->bool) a. a SUBSET x
                        ==> subtopology (subtopology euclidean x) a = subtopology euclidean a`,
  SIMP_TAC[SUBTOPOLOGY_SUBTOPOLOGY; SET_RULE `(a:real^N->bool) SUBSET x ==> x INTER a = a`]);;

let MOI_S4J_MV_CARRIES = prove
 (`!(x:real^N->bool) a b r t.
     open_in (subtopology euclidean x) a /\ open_in (subtopology euclidean x) b /\
     x = a UNION b /\
     trivial_group (homology_group(&1,subtopology euclidean x)) /\
     r SUBSET a /\ a SUBSET t /\ carries_h1 r t
     ==> carries_h1 (a INTER b) t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    concl th = `(x:real^N->bool) = a UNION b`)) THEN
  UNDISCH_TAC `carries_h1 (r:real^N->bool) t` THEN
  REWRITE_TAC[carries_h1; group_image] THEN DISCH_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`&1:int`; `subtopology euclidean ((a:real^N->bool) INTER b)`;
                   `subtopology euclidean (t:real^N->bool)`; `\x:real^N. x`]
                  GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY) THEN
    SIMP_TAC[group_homomorphism];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:((num->real)->real^N)frag->bool` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `?z. z IN group_carrier (homology_group(&1,subtopology euclidean (r:real^N->bool))) /\
        hom_induced (&1) (subtopology euclidean r,{}) (subtopology euclidean t,{})
                    (\x. x) z = y`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC
     `IMAGE (hom_induced (&1) (subtopology euclidean (r:real^N->bool),{})
                             (subtopology euclidean t,{}) (\x. x))
            (group_carrier (homology_group (&1,subtopology euclidean r))) =
      group_carrier (homology_group (&1,subtopology euclidean t))` THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `y:((num->real)->real^N)frag->bool`) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `aa = hom_induced (&1) (subtopology euclidean (r:real^N->bool),{})
                               (subtopology euclidean a,{}) (\x. x) z` THEN
  SUBGOAL_THEN `aa IN group_carrier (homology_group(&1,subtopology euclidean (a:real^N->bool)))`
  ASSUME_TAC THENL
   [EXPAND_TAC "aa" THEN MATCH_MP_TAC MOI_S4J_HOM_IN THEN
    EXISTS_TAC `homology_group(&1,subtopology euclidean (r:real^N->bool))` THEN
    ASM_REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean ((a:real^N->bool) UNION b)`;
                 `a:real^N->bool`; `b:real^N->bool`; `aa:((num->real)->real^N)frag->bool`]
    MOI_S4J_MV_LIFT) THEN
  SUBGOAL_THEN
   `subtopology (subtopology euclidean ((a:real^N->bool) UNION b)) a =
    subtopology euclidean a /\
    subtopology (subtopology euclidean ((a:real^N->bool) UNION b)) (a INTER b) =
    subtopology euclidean (a INTER b)`
  (fun th -> REWRITE_TAC[th; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_S4J_SUBTOP THEN SET_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:((num->real)->real^N)frag->bool` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `c:((num->real)->real^N)frag->bool` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `hom_induced (&1) (subtopology euclidean ((a:real^N->bool) INTER b),{})
                     (subtopology euclidean t,{}) (\x. x) =
    hom_induced (&1) (subtopology euclidean a,{}) (subtopology euclidean t,{}) (\x. x) o
    hom_induced (&1) (subtopology euclidean (a INTER b),{}) (subtopology euclidean a,{}) (\x. x)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC ATOP_HOM_INDUCED_INCLUSIONS THEN
    ASM_SIMP_TAC[ATOP_CONTINUOUS_MAP_INCLUSION; SUBSET_REFL; INTER_SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `hom_induced (&1) (subtopology euclidean (r:real^N->bool),{})
                           (subtopology euclidean a,{}) (\x. x) z = aa` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`&1:int`; `subtopology euclidean (r:real^N->bool)`; `{}:real^N->bool`;
                 `subtopology euclidean (a:real^N->bool)`; `{}:real^N->bool`;
                 `subtopology euclidean (t:real^N->bool)`; `{}:real^N->bool`]
    ATOP_HOM_INDUCED_INCLUSIONS) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[ATOP_CONTINUOUS_MAP_INCLUSION; EMPTY_SUBSET]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[REWRITE_RULE[o_THM] (ONCE_REWRITE_RULE[FUN_EQ_THM] th)]) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Carrying H_1 is transported along a homotopy (in t) from the             *)
(* inclusion of x to a map into y.                                          *)
(* ------------------------------------------------------------------------- *)

let MOI_S4J_CARRIES_HOMOTOPIC = prove
 (`!(x:real^N->bool) y t g.
     carries_h1 x t /\ x SUBSET t /\ y SUBSET t /\
     continuous_map (subtopology euclidean x,subtopology euclidean y) g /\
     homotopic_with (\h. T) (subtopology euclidean x,subtopology euclidean t) (\x. x) g
     ==> carries_h1 y t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `carries_h1 (x:real^N->bool) t` THEN
  REWRITE_TAC[carries_h1; group_image] THEN DISCH_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`&1:int`; `subtopology euclidean (y:real^N->bool)`;
                   `subtopology euclidean (t:real^N->bool)`; `\x:real^N. x`]
                  GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY) THEN
    SIMP_TAC[group_homomorphism];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `hom_induced (&1) (subtopology euclidean (x:real^N->bool),{})
                     (subtopology euclidean t,{}) (\x. x) =
    hom_induced (&1) (subtopology euclidean x,{}) (subtopology euclidean t,{})
                (g:real^N->real^N)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMOLOGY_HOMOTOPY_AXIOM THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_MONO THEN
    EXISTS_TAC `\h:real^N->real^N. T` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IMAGE_CLAUSES; EMPTY_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `hom_induced (&1) (subtopology euclidean (x:real^N->bool),{})
                     (subtopology euclidean t,{}) (g:real^N->real^N) =
    hom_induced (&1) (subtopology euclidean y,{}) (subtopology euclidean t,{}) (\x. x) o
    hom_induced (&1) (subtopology euclidean x,{}) (subtopology euclidean y,{}) g`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`&1:int`; `subtopology euclidean (x:real^N->bool)`;
                   `subtopology euclidean (y:real^N->bool)`;
                   `subtopology euclidean (t:real^N->bool)`;
                   `g:real^N->real^N`; `\x:real^N. x`] HOM_INDUCED_COMPOSE_EMPTY) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[ATOP_CONTINUOUS_MAP_INCLUSION]; ALL_TAC] THEN
    REWRITE_TAC[o_DEF; ETA_AX] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `z:((num->real)->real^N)frag->bool` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `?w. w IN group_carrier (homology_group(&1,subtopology euclidean (x:real^N->bool))) /\
        z = hom_induced (&1) (subtopology euclidean x,{}) (subtopology euclidean t,{})
                        (\x. x) w`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC
     `IMAGE (hom_induced (&1) (subtopology euclidean (x:real^N->bool),{})
                             (subtopology euclidean t,{}) (\x. x))
            (group_carrier (homology_group (&1,subtopology euclidean x))) =
      group_carrier (homology_group (&1,subtopology euclidean t))` THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `z:((num->real)->real^N)frag->bool`) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `hom_induced (&1) (subtopology euclidean (x:real^N->bool),{})
                          (subtopology euclidean y,{}) (g:real^N->real^N) w` THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `z = hom_induced (&1) (subtopology euclidean (x:real^N->bool),{})
                                     (subtopology euclidean t,{}) (\x. x) w` THEN
    DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC
     `hom_induced (&1) (subtopology euclidean (x:real^N->bool),{})
                       (subtopology euclidean t,{}) (\x. x) =
      hom_induced (&1) (subtopology euclidean x,{}) (subtopology euclidean t,{})
                  (g:real^N->real^N)` THEN
    DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC
     `hom_induced (&1) (subtopology euclidean (x:real^N->bool),{})
                       (subtopology euclidean t,{}) (g:real^N->real^N) =
      hom_induced (&1) (subtopology euclidean y,{}) (subtopology euclidean t,{}) (\x. x) o
      hom_induced (&1) (subtopology euclidean x,{}) (subtopology euclidean y,{}) g` THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_THM];
    MATCH_MP_TAC MOI_S4J_HOM_IN THEN
    EXISTS_TAC `homology_group(&1,subtopology euclidean (x:real^N->bool))` THEN
    ASM_REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY]]);;

(* ------------------------------------------------------------------------- *)
(* A compact polyhedron q inside a compact polyhedron p is a                *)
(* neighbourhood deformation retract: triangulate the pair                 *)
(* (POLYTOPES_SIMPLICIAL_REFINEMENT) and use the derived neighbourhood and *)
(* its retraction (DERIVED_NBHD_BASIC, DERIVED_NBHD_DEFORMATION_RETRACT).  *)
(* ------------------------------------------------------------------------- *)

let MOI_S4J_PAIR_TRIANGULATION = prove
 (`!(p:real^N->bool) q.
     pl_polyhedron p /\ pl_polyhedron q /\ q SUBSET p
     ==> ?t l. simplicial_complex t /\ UNIONS t = p /\
               simplicial_subcomplex l t /\ UNIONS l = q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_polyhedron] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `cp:(real^N->bool)->bool` STRIP_ASSUME_TAC)
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `cq:(real^N->bool)->bool` STRIP_ASSUME_TAC)
      ASSUME_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq (concl th) && is_var (lhs (concl th))))) THEN
  MP_TAC(ISPEC `cp UNION cq:(real^N->bool)->bool` POLYTOPES_SIMPLICIAL_REFINEMENT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_UNION; IN_UNION] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^N->bool)->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ref")))) THEN
  EXISTS_TAC `t:(real^N->bool)->bool` THEN
  EXISTS_TAC `{s:real^N->bool | s IN t /\ s SUBSET UNIONS cq}` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `UNIONS t = UNIONS (cp UNION cq:(real^N->bool)->bool)` THEN
    UNDISCH_TAC `UNIONS cq SUBSET UNIONS (cp:(real^N->bool)->bool)` THEN
    REWRITE_TAC[UNIONS_UNION] THEN SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[simplicial_subcomplex; SUBSET; IN_ELIM_THM] THEN
    CONJ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `f:real^N->bool`] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `simplicial_complex (t:(real^N->bool)->bool)` THEN
      REWRITE_TAC[simplicial_complex] THEN
      DISCH_THEN(MP_TAC o SPECL [`f:real^N->bool`; `s:real^N->bool`] o
        CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `f:real^N->bool`] FACE_OF_IMP_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y:real^N) IN f` THEN SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN
  GEN_REWRITE_TAC LAND_CONV [IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "ref" (MP_TAC o SPEC `k:real^N->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_UNION]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(x:real^N) IN k` THEN
  FIRST_ASSUM(fun th -> if concl th = `(k:real^N->bool) = UNIONS f`
                        then SUBST1_TAC th else failwith "") THEN
  GEN_REWRITE_TAC LAND_CONV [IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EXISTS_TAC `s:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `(f:(real^N->bool)->bool) SUBSET t` THEN
    UNDISCH_TAC `(s:real^N->bool) IN f` THEN SET_TAC[];
    UNDISCH_TAC `(k:real^N->bool) IN cq` THEN
    UNDISCH_TAC `(k:real^N->bool) = UNIONS f` THEN
    UNDISCH_TAC `(s:real^N->bool) IN f` THEN SET_TAC[]]);;

let MOI_S4J_PAIR_RETRACT = prove
 (`!(p:real^N->bool) q.
     pl_polyhedron p /\ pl_polyhedron q /\ q SUBSET p
     ==> ?u r. open u /\ q SUBSET u /\
               continuous_map (subtopology euclidean (p INTER u),subtopology euclidean q) r /\
               homotopic_with (\h. T)
                 (subtopology euclidean (p INTER u),subtopology euclidean p) (\x. x) r`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S4J_PAIR_TRIANGULATION) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^N->bool)->bool` (X_CHOOSE_THEN
    `l:(real^N->bool)->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `lf_simplicial_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    DERIVED_NBHD_BASIC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    DERIVED_NBHD_DEFORMATION_RETRACT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->real^N` STRIP_ASSUME_TAC o CONJUNCT2) THEN
  ABBREV_TAC `n = derived_nbhd (t:(real^N->bool)->bool) l` THEN
  MP_TAC(ISPECL [`subtopology euclidean (p:real^N->bool)`;
                 `n:real^N->bool`] OPEN_IN_INTERIOR_OF) THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`u:real^N->bool`; `r:real^N->real^N`] THEN
  SUBGOAL_THEN `(p:real^N->bool) INTER u SUBSET n` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`subtopology euclidean (p:real^N->bool)`;
                   `n:real^N->bool`] INTERIOR_OF_SUBSET) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:real^N->bool) SUBSET p INTER u` ASSUME_TAC THENL
   [UNDISCH_TAC `(q:real^N->bool) SUBSET subtopology euclidean p interior_of n` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `retraction (n,q) (r:real^N->real^N)` THEN
  REWRITE_TAC[retraction] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    UNDISCH_TAC `(q:real^N->bool) SUBSET p INTER u` THEN SET_TAC[];
    REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `n:real^N->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (r:real^N->real^N) n` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC HOMOTOPIC_WITH_MONO THEN
    EXISTS_TAC `\h:real^N->real^N. !x. x IN q ==> h x = x` THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_SUBSET_RIGHT THEN
    EXISTS_TAC `n:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_SUBSET_LEFT THEN
    EXISTS_TAC `n:real^N->bool` THEN ASM_REWRITE_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* Mayer-Vietoris followed by a push.  x is covered by a and by x minus     *)
(* (k minus u); H_1(x) is trivial, so the classes of t carried by r inside *)
(* a are carried by a INTER u, and a map g of p INTER u into q, homotopic  *)
(* in p to the identity, carries them on to q.                              *)
(* ------------------------------------------------------------------------- *)

let MOI_S4J_MV_PUSH = prove
 (`!(x:real^N->bool) a k u r t p q g.
     closed k /\ open u /\ open_in (subtopology euclidean x) a /\ a SUBSET k /\
     x INTER k SUBSET a UNION u /\
     trivial_group (homology_group(&1,subtopology euclidean x)) /\
     r SUBSET a /\ a SUBSET p /\ p SUBSET t /\ q SUBSET t /\ carries_h1 r t /\
     continuous_map (subtopology euclidean (p INTER u),subtopology euclidean q) g /\
     homotopic_with (\h. T)
       (subtopology euclidean (p INTER u),subtopology euclidean p) (\x. x) g
     ==> carries_h1 q t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean x) ((x:real^N->bool) DIFF (k DIFF u))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(x:real^N->bool) DIFF (k DIFF u) =
                  x INTER ((:real^N) DIFF (k DIFF u))` SUBST1_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[GSYM closed] THEN
    MATCH_MP_TAC CLOSED_DIFF THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N->bool) = a UNION (x DIFF (k DIFF u))` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N->bool) INTER k SUBSET a UNION u` THEN
    UNDISCH_TAC `(a:real^N->bool) SUBSET x` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^N->bool) SUBSET t` ASSUME_TAC THENL
   [UNDISCH_TAC `(a:real^N->bool) SUBSET p` THEN
    UNDISCH_TAC `(p:real^N->bool) SUBSET t` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `carries_h1 (a INTER (x DIFF (k DIFF u))) (t:real^N->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4J_MV_CARRIES THEN
    MAP_EVERY EXISTS_TAC [`x:real^N->bool`; `r:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th] THEN
      ASSUME_TAC th) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `a INTER (x DIFF (k DIFF u)) SUBSET (p:real^N->bool) INTER u`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(a:real^N->bool) SUBSET p` THEN
    UNDISCH_TAC `(a:real^N->bool) SUBSET k` THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S4J_CARRIES_HOMOTOPIC THEN
  MAP_EVERY EXISTS_TAC [`a INTER (x DIFF (k DIFF u)):real^N->bool`;
                        `g:real^N->real^N`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `a INTER (x DIFF (k DIFF u)) SUBSET (p:real^N->bool) INTER u` THEN
    UNDISCH_TAC `(p:real^N->bool) SUBSET t` THEN SET_TAC[];
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
    EXISTS_TAC `(p:real^N->bool) INTER u` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC HOMOTOPIC_WITH_SUBSET_LEFT THEN
    EXISTS_TAC `(p:real^N->bool) INTER u` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_SUBSET_RIGHT THEN
    EXISTS_TAC `p:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Trivial H_1: contractible sets and PL 2-spheres in real^3 (homeomorphic *)
(* to the unit sphere, REDUCED_HOMOLOGY_GROUP_SPHERE of pc_top_lochom).     *)
(* ------------------------------------------------------------------------- *)

let MOI_S4J_H1_CONTRACTIBLE = prove
 (`!s:real^N->bool.
     contractible s ==> trivial_group (homology_group(&1,subtopology euclidean s))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TRIVIAL_HOMOLOGY_GROUP_CONTRACTIBLE_SPACE THEN
  ASM_REWRITE_TAC[CONTRACTIBLE_SPACE_EUCLIDEAN] THEN INT_ARITH_TAC);;

let MOI_S4J_H1_SPHERE2 = prove
 (`!s:real^3->bool.
     pl_sphere 2 s ==> trivial_group (homology_group(&1,subtopology euclidean s))`,
  GEN_TAC THEN REWRITE_TAC[pl_sphere; pl_homeomorphism; ARITH_RULE `2 + 1 = 3`] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(s:real^3->bool) homeomorphic sphere(vec 0:real^3,&1)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^3->bool`; `relative_frontier (k:real^3->bool)`;
                   `sphere(vec 0:real^3,&1)`] HOMEOMORPHIC_TRANS) THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
      MAP_EVERY EXISTS_TAC [`f:real^3->real^3`; `g:real^3->real^3`] THEN
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN `sphere(vec 0:real^3,&1) = relative_frontier(cball(vec 0,&1))`
      SUBST1_TAC THENL
       [REWRITE_TAC[RELATIVE_FRONTIER_CBALL; REAL_OF_NUM_EQ; ARITH_EQ]; ALL_TAC] THEN
      MATCH_MP_TAC HOMEOMORPHIC_RELATIVE_FRONTIERS_CONVEX_BOUNDED_SETS THEN
      REWRITE_TAC[CONVEX_CBALL; BOUNDED_CBALL; AFF_DIM_CBALL; REAL_LT_01;
                  DIMINDEX_3] THEN
      REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
        ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_BOUNDED];
        ASM_MESON_TAC[AFF_DIM_SIMPLEX]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`&1:int`; `subtopology euclidean (sphere(vec 0:real^3,&1))`;
                 `subtopology euclidean (s:real^3->bool)`]
    HOMEOMORPHIC_SPACE_IMP_ISOMORPHIC_HOMOLOGY_GROUPS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[HOMEOMORPHIC_SPACE_EUCLIDEAN] THEN
    ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP ISOMORPHIC_GROUP_TRIVIALITY) THEN
  MP_TAC(ISPECL [`&1:int`; `subtopology euclidean (sphere(vec 0:real^3,&1))`]
    UN_REDUCED_HOMOLOGY_GROUP) THEN
  ANTS_TAC THENL [INT_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC(CONJUNCT2 REDUCED_HOMOLOGY_GROUP_SPHERE) THEN
  REWRITE_TAC[DIMINDEX_3; REAL_LT_01] THEN CONV_TAC NUM_REDUCE_CONV THEN
  INT_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* The cone from a point p of r outside the face s over a compact subset b  *)
(* of s: compact, contractible, inside r, and it meets s only in b (the    *)
(* face property along the segments from p).                                *)
(* ------------------------------------------------------------------------- *)

let MOI_S4J_CONE = prove
 (`!(s:real^N->bool) r p b.
     s face_of r /\ convex r /\ p IN r /\ ~(p IN s) /\ compact b /\
     ~(b = {}) /\ b SUBSET s
     ==> compact (UNIONS {segment[p,y] | y IN b}) /\
         contractible (UNIONS {segment[p,y] | y IN b}) /\
         UNIONS {segment[p,y] | y IN b} SUBSET r /\
         b SUBSET UNIONS {segment[p,y] | y IN b} /\
         UNIONS {segment[p,y] | y IN b} INTER s SUBSET b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(s:real^N->bool) SUBSET r` ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_OF_IMP_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN UNIONS {segment[p:real^N,y] | y IN b} <=>
                    ?y. y IN b /\ z IN segment[p,y]`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `UNIONS {segment[p:real^N,y] | y IN b} =
      {(&1 - u) % x + u % y | &0 <= u /\ u <= &1 /\ x IN {p} /\ y IN b}`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[EXTENSION] THEN
      REWRITE_TAC[IN_ELIM_THM; IN_SING; IN_SEGMENT] THEN MESON_TAC[];
      MATCH_MP_TAC COMPACT_CONVEX_COMBINATIONS THEN
      ASM_REWRITE_TAC[COMPACT_SING]];
    MATCH_MP_TAC STARLIKE_IMP_CONTRACTIBLE THEN REWRITE_TAC[starlike] THEN
    EXISTS_TAC `p:real^N` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `~(b:real^N->bool = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN MESON_TAC[ENDS_IN_SEGMENT];
      X_GEN_TAC `z:real^N` THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[SUBSET] THEN X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `segment[p:real^N,z] SUBSET segment[p,y]` MP_TAC THENL
       [MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
        ASM_REWRITE_TAC[CONVEX_SEGMENT; ENDS_IN_SEGMENT];
        UNDISCH_TAC `(w:real^N) IN segment[p,z]` THEN SET_TAC[]]];
    ASM_REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `segment[p:real^N,y] SUBSET r` MP_TAC THENL
     [MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y:real^N) IN b` THEN UNDISCH_TAC `(b:real^N->bool) SUBSET s` THEN
      UNDISCH_TAC `(s:real^N->bool) SUBSET r` THEN SET_TAC[];
      UNDISCH_TAC `(z:real^N) IN segment[p,y]` THEN SET_TAC[]];
    ASM_REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[ENDS_IN_SEGMENT];
    ASM_REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `z:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)
      ASSUME_TAC) THEN
    ASM_CASES_TAC `z:real^N = y` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `z:real^N = p` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^N) IN segment(p,y)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[open_segment; IN_DIFF; IN_INSERT; NOT_IN_EMPTY];
      ALL_TAC] THEN
    UNDISCH_TAC `(s:real^N->bool) face_of r` THEN REWRITE_TAC[face_of] THEN
    DISCH_THEN(MP_TAC o SPECL [`p:real^N`; `y:real^N`; `z:real^N`] o
      CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:real^N) IN b` THEN UNDISCH_TAC `(b:real^N->bool) SUBSET s` THEN
    UNDISCH_TAC `(s:real^N->bool) SUBSET r` THEN SET_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* PL 3-balls in real^3: the facts used below (the frontier is a PL       *)
(* 2-sphere by MOI_SCD_BALL_BOUNDARY_PLH, as in pc_moi_s35_ext).            *)
(* ------------------------------------------------------------------------- *)

let MOI_S4J_BALL3_FACTS = prove
 (`!c:real^3->bool.
     pl_ball 3 c
     ==> compact c /\ closed c /\ pl_polyhedron c /\
         pl_sphere 2 (frontier c) /\ pl_polyhedron (frontier c) /\
         frontier c SUBSET c /\ c DIFF interior c SUBSET frontier c /\
         trivial_group (homology_group(&1,subtopology euclidean (frontier c)))`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_CGL_PL_BALL_BASIC) THEN
  SUBGOAL_THEN `closed (c:real^3->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere 2 (frontier c:real^3->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `pl_ball 3 (c:real^3->bool)` THEN
    REWRITE_TAC[pl_ball; pl_sphere; ARITH_RULE `2 + 1 = 3`] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
      (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SCD_BALL_BOUNDARY_PLH THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_SCD_PL_SPHERE_POLYHEDRON];
    ASM_SIMP_TAC[FRONTIER_SUBSET_CLOSED];
    ASM_SIMP_TAC[frontier; CLOSURE_CLOSED; SUBSET_REFL];
    MATCH_MP_TAC MOI_S4J_H1_SPHERE2 THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Step A (the cycle Z^1 pushed to the frontier).  cc is a compact          *)
(* contractible set containing rr, which carries H_1(t) and lies inside c; *)
(* cc meets c only inside interior t.  Mayer-Vietoris on cc (pieces cc     *)
(* INTER interior c and cc minus (c minus u)) and the retraction of a     *)
(* polyhedral neighbourhood t2 of cc INTER c onto frontier c INTER t2 give  *)
(* a carrying subset of frontier c INTER interior t.                        *)
(* ------------------------------------------------------------------------- *)

let MOI_S4J_STEP_A = prove
 (`!(cc:real^3->bool) rr t c.
     compact cc /\ contractible cc /\ rr SUBSET cc /\ carries_h1 rr t /\
     pl_ball 3 c /\ rr SUBSET interior c /\ cc INTER c SUBSET interior t
     ==> ?r. r SUBSET frontier c INTER interior t /\ carries_h1 r t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4J_BALL3_FACTS) THEN
  MP_TAC(ISPECL [`cc INTER c:real^3->bool`; `interior t:real^3->bool`]
    MOI_FMB_COMPACT_CUBE_NBHD) THEN
  ASM_SIMP_TAC[COMPACT_INTER_CLOSED; OPEN_INTERIOR] THEN
  DISCH_THEN(X_CHOOSE_THEN `P:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `t2 = UNIONS (P:(real^3->bool)->bool)` THEN
  SUBGOAL_THEN `pl_polyhedron (t2:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "t2" THEN REWRITE_TAC[pl_polyhedron] THEN
    EXISTS_TAC `P:(real^3->bool)->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(t2:real^3->bool) SUBSET interior t` ASSUME_TAC THENL
   [EXPAND_TAC "t2" THEN REWRITE_TAC[UNIONS_SUBSET] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `cc INTER c SUBSET (t2:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `interior (t2:real^3->bool)` THEN
    ASM_REWRITE_TAC[INTERIOR_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c INTER t2:real^3->bool`; `frontier c INTER t2:real^3->bool`]
    MOI_S4J_PAIR_RETRACT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[PL_POLYHEDRON_INTER] THEN
    UNDISCH_TAC `frontier c SUBSET (c:real^3->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `g:real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `frontier c INTER t2:real^3->bool` THEN CONJ_TAC THENL
   [UNDISCH_TAC `(t2:real^3->bool) SUBSET interior t` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean cc) (cc INTER interior c:real^3->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[OPEN_INTERIOR]; ALL_TAC] THEN
  SUBGOAL_THEN `cc INTER interior c SUBSET (c:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `c:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `cc INTER c SUBSET (cc INTER interior c) UNION (u:real^3->bool)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `frontier c INTER t2 SUBSET (u:real^3->bool)` THEN
    UNDISCH_TAC `cc INTER c SUBSET (t2:real^3->bool)` THEN
    UNDISCH_TAC `(c:real^3->bool) DIFF interior c SUBSET frontier c` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `trivial_group (homology_group(&1,subtopology euclidean (cc:real^3->bool)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4J_H1_CONTRACTIBLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(rr:real^3->bool) SUBSET cc INTER interior c` ASSUME_TAC THENL
   [UNDISCH_TAC `(rr:real^3->bool) SUBSET cc` THEN
    UNDISCH_TAC `(rr:real^3->bool) SUBSET interior c` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `cc INTER interior c SUBSET (c:real^3->bool) INTER t2` ASSUME_TAC THENL
   [UNDISCH_TAC `cc INTER c SUBSET (t2:real^3->bool)` THEN
    UNDISCH_TAC `cc INTER interior c SUBSET (c:real^3->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^3->bool) INTER t2 SUBSET t /\ frontier c INTER t2 SUBSET t`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `t:real^3->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(t2:real^3->bool) SUBSET interior t` THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S4J_MV_PUSH THEN
  MAP_EVERY EXISTS_TAC [`cc:real^3->bool`; `cc INTER interior c:real^3->bool`;
    `c:real^3->bool`; `u:real^3->bool`; `rr:real^3->bool`;
    `c INTER t2:real^3->bool`; `g:real^3->real^3`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Step B (the cycle moved onto q).  r carries H_1(t) inside frontier c    *)
(* INTER interior t, and q contains the points of frontier c on t outside  *)
(* interior t.  Mayer-Vietoris on the 2-sphere frontier c (pieces frontier *)
(* c INTER interior t and frontier c minus (t minus u)) and the retraction *)
(* of the pair (frontier c INTER t, frontier c INTER q).                   *)
(* ------------------------------------------------------------------------- *)

let MOI_S4J_STEP_B = prove
 (`!(c:real^3->bool) t q r.
     pl_ball 3 c /\ compact t /\ pl_polyhedron t /\ pl_polyhedron q /\
     q SUBSET t /\ frontier c INTER (t DIFF interior t) SUBSET q /\
     r SUBSET frontier c INTER interior t /\ carries_h1 r t
     ==> carries_h1 (frontier c INTER q) t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4J_BALL3_FACTS) THEN
  MP_TAC(ISPECL [`frontier c INTER t:real^3->bool`;
                 `frontier c INTER q:real^3->bool`] MOI_S4J_PAIR_RETRACT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[PL_POLYHEDRON_INTER] THEN
    UNDISCH_TAC `(q:real^3->bool) SUBSET t` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `g:real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `closed (t:real^3->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (frontier c))
                        (frontier c INTER interior t:real^3->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[OPEN_INTERIOR]; ALL_TAC] THEN
  SUBGOAL_THEN `frontier c INTER interior t SUBSET (t:real^3->bool) /\
                frontier c INTER interior t SUBSET frontier c INTER t`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `t:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `frontier c INTER t SUBSET
                (frontier c INTER interior t) UNION (u:real^3->bool)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `frontier c INTER q SUBSET (u:real^3->bool)` THEN
    UNDISCH_TAC `frontier c INTER (t DIFF interior t) SUBSET (q:real^3->bool)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier c INTER t SUBSET (t:real^3->bool) /\
                frontier c INTER q SUBSET t`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(q:real^3->bool) SUBSET t` THEN SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_S4J_MV_PUSH THEN
  MAP_EVERY EXISTS_TAC [`frontier c:real^3->bool`;
    `frontier c INTER interior t:real^3->bool`; `t:real^3->bool`;
    `u:real^3->bool`; `r:real^3->bool`; `frontier c INTER t:real^3->bool`;
    `g:real^3->real^3`] THEN
  ASM_REWRITE_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* Finite unions of PL polyhedra.                                            *)
(* ------------------------------------------------------------------------- *)

let MOI_S4J_PL_POLYHEDRON_UNIONS = prove
 (`!f:(real^N->bool)->bool.
     FINITE f /\ (!x. x IN f ==> pl_polyhedron x) ==> pl_polyhedron (UNIONS f)`,
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_0; UNIONS_INSERT; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[pl_polyhedron] THEN EXISTS_TAC `{}:(real^N->bool)->bool` THEN
    REWRITE_TAC[FINITE_EMPTY; NOT_IN_EMPTY; UNIONS_0];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC PL_POLYHEDRON_UNION THEN ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* A 2-simplex s of kk: the facts used, and a point p outside s in a       *)
(* 3-simplex r of kk having s as a face (MOI_S4O_KK_PURE).                  *)
(* ------------------------------------------------------------------------- *)

let MOI_S4J_SIMP2 = prove
 (`!(tt:(real^N->bool)->bool) kk s.
     moi_s34_tube tt kk /\ s IN moi_s34_simp kk (&2)
     ==> s IN kk /\ kk SUBSET tt /\ lf_simplicial_complex kk /\
         compact s /\ convex s /\ ~(s = {}) /\
         ~(relative_frontier s = {}) /\ compact (relative_frontier s) /\
         relative_frontier s SUBSET s /\ path_connected (relative_frontier s) /\
         FINITE {v | v IN s /\ {v} IN kk} /\
         (?r p. r IN kk /\ convex r /\ s face_of r /\ p IN r /\ ~(p IN s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s34_tube]) THEN
  SUBGOAL_THEN `lf_simplicial_complex (kk:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN `(kk:(real^N->bool)->bool) SUBSET tt` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex]; ALL_TAC] THEN
  SUBGOAL_THEN `&2 simplex (s:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `lf_simplicial_complex (kk:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `n:int`) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (s:real^N->bool) /\ convex s /\ polytope s`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_POLYTOPE];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(s:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `aff_dim (s:real^N->bool) = &2` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(relative_frontier (s:real^N->bool) = {})` ASSUME_TAC THENL
   [REWRITE_TAC[RELATIVE_FRONTIER_EQ_EMPTY] THEN DISCH_TAC THEN
    MP_TAC(ISPEC `s:real^N->bool` AFFINE_BOUNDED_EQ_LOWDIM) THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `path_connected (relative_frontier (s:real^N->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC PATH_CONNECTED_SPHERE_GEN THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^N. v IN s /\ {v} IN kk ==> {v} face_of s` ASSUME_TAC THENL
   [X_GEN_TAC `v:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `{v:real^N} = {v} INTER s` SUBST1_TAC THENL
     [UNDISCH_TAC `(v:real^N) IN s` THEN SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `lf_simplicial_complex (kk:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPECL [`{v:real^N}`; `s:real^N->bool`] o
      CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {v:real^N | v IN s /\ {v} IN kk}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{v:real^N | v extreme_point_of s}` THEN
    ASM_SIMP_TAC[FINITE_POLYHEDRON_EXTREME_POINTS; POLYTOPE_IMP_POLYHEDRON] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; GSYM FACE_OF_SING] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?v:real^N. v IN s /\ {v} IN kk` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `s:real^N->bool` EXTREME_POINT_EXISTS_CONVEX) THEN
    ASM_REWRITE_TAC[GSYM FACE_OF_SING] THEN
    DISCH_THEN(X_CHOOSE_TAC `v:real^N`) THEN EXISTS_TAC `v:real^N` THEN
    CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN SET_TAC[];
      UNDISCH_TAC `lf_simplicial_complex (kk:(real^N->bool)->bool)` THEN
      REWRITE_TAC[lf_simplicial_complex] THEN
      DISCH_THEN(MP_TAC o SPECL [`{v:real^N}`; `s:real^N->bool`] o
        CONJUNCT1 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?r p:real^N. r IN kk /\ convex r /\ s face_of r /\ p IN r /\ ~(p IN s)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `v:real^N`; `s:real^N->bool`] MOI_S4O_KK_PURE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(s:real^N->bool) face_of r` ASSUME_TAC THENL
     [SUBGOAL_THEN `s:real^N->bool = s INTER r` SUBST1_TAC THENL
       [UNDISCH_TAC `(s:real^N->bool) SUBSET r` THEN SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `lf_simplicial_complex (kk:(real^N->bool)->bool)` THEN
      REWRITE_TAC[lf_simplicial_complex] THEN
      DISCH_THEN(MP_TAC o SPECL [`s:real^N->bool`; `r:real^N->bool`] o
        CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `convex (r:real^N->bool)` ASSUME_TAC THENL
     [UNDISCH_TAC `lf_simplicial_complex (kk:(real^N->bool)->bool)` THEN
      REWRITE_TAC[lf_simplicial_complex] THEN
      DISCH_THEN(MP_TAC o SPEC `r:real^N->bool` o CONJUNCT1) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[SIMPLEX_IMP_CONVEX];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((r:real^N->bool) SUBSET s)` MP_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `r:real^N->bool = s` SUBST_ALL_TAC THENL
       [UNDISCH_TAC `(r:real^N->bool) SUBSET s` THEN
        UNDISCH_TAC `(s:real^N->bool) SUBSET r` THEN SET_TAC[];
        UNDISCH_TAC `aff_dim (s:real^N->bool) = &3` THEN
        ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
      REWRITE_TAC[SUBSET; NOT_FORALL_THM; NOT_IMP] THEN
      DISCH_THEN(X_CHOOSE_THEN `p:real^N` STRIP_ASSUME_TAC) THEN
      MAP_EVERY EXISTS_TAC [`r:real^N->bool`; `p:real^N`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[COMPACT_RELATIVE_FRONTIER; RELATIVE_FRONTIER_SUBSET;
               COMPACT_IMP_CLOSED]);;


(* ------------------------------------------------------------------------- *)
(* The tube N: the union of the vertex balls; Bd N inside N; each vertex    *)
(* ball meets Bd N in a polyhedron (the chain description of pc_moi_fnd_tubea *)
(* used as in MOI_S4O_Z_POLY).                                              *)
(* ------------------------------------------------------------------------- *)

let MOI_S4J_NB_FACTS = prove
 (`!(tt:(real^N->bool)->bool) kk.
     moi_s34_tube tt kk
     ==> moi_s34_nb tt kk = UNIONS {moi_s34_vb tt kk v | v | {v} IN kk} /\
         moi_s34_bd tt kk SUBSET moi_s34_nb tt kk`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s34_tube] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[moi_s34_nb; moi_s34_vb] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`]
      MOI_FTA_NBHD_UNION_CELLS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `!v:real^N. {v} IN skeleton 1 kk <=> {v} IN kk`
      (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[skeleton; IN_ELIM_THM; AFF_DIM_SING; INT_POS];
    REWRITE_TAC[moi_s34_bd; moi_s34_nb; derived_frontier] THEN
    MATCH_MP_TAC FRONTIER_OF_SUBSET_CLOSED_IN THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`]
      DERIVED_NBHD_BASIC) THEN
    ASM_SIMP_TAC[]]);;

let MOI_S4J_VB_BD_POLY = prove
 (`!(tt:(real^N->bool)->bool) kk v.
     moi_s34_tube tt kk /\ {v} IN kk
     ==> pl_polyhedron (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s34_tube] THEN STRIP_TAC THEN
  SUBGOAL_THEN `{v:real^N} IN skeleton 1 kk` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[skeleton; IN_ELIM_THM; AFF_DIM_SING; INT_POS]; ALL_TAC] THEN
  REWRITE_TAC[moi_s34_vb; moi_s34_bd] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`;
                 `v:real^N`] MOI_FTA_CELL_FRONTIER_CHAINS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC MOI_FTA_CHAIN_UNIONS_POLY THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `skeleton 1 (kk:(real^N->bool)->bool)`;
                 `v:real^N`] MOI_FTA_SETUP) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The face torus T = f1(N_s): compact, a polyhedron, T INTER f1(Bd N) a     *)
(* polyhedron, and near h(s), away from the other vertex balls, the points *)
(* of T outside interior T lie on f1(Bd N).                                 *)
(* ------------------------------------------------------------------------- *)

let MOI_S4J_T_FACTS = prove
 (`!(tt:(real^N->bool)->bool) kk (h:real^N->real^3) ep (f1:real^N->real^3) car s.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     s IN moi_s34_simp kk (&2)
     ==> compact (IMAGE f1 (moi_s34_ft tt kk s)) /\
         pl_polyhedron (IMAGE f1 (moi_s34_ft tt kk s)) /\
         pl_polyhedron (IMAGE f1 (moi_s34_ft tt kk s) INTER
                        IMAGE f1 (moi_s34_bd tt kk)) /\
         (!w. open w /\
              (!v. {v} IN kk /\ ~(v IN s)
                   ==> DISJOINT w (IMAGE f1 (moi_s34_vb tt kk v)))
              ==> w INTER (IMAGE f1 (moi_s34_ft tt kk s) DIFF
                           interior (IMAGE f1 (moi_s34_ft tt kk s)))
                  SUBSET IMAGE f1 (moi_s34_bd tt kk))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `s:real^N->bool`] MOI_S4J_SIMP2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`]
    MOI_S4J_NB_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "nbu") ASSUME_TAC) THEN
  UNDISCH_TAC `moi_s34_frame tt kk h ep (f1:real^N->real^3) car` THEN
  REWRITE_TAC[moi_s34_frame] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "bdfr")
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "vb") (K ALL_TAC)))))))) THEN
  ABBREV_TAC `V = {v:real^N | v IN s /\ {v} IN kk}` THEN
  SUBGOAL_THEN `moi_s34_ft tt kk s = UNIONS (IMAGE (moi_s34_vb tt kk) (V:real^N->bool))`
  (LABEL_TAC "ftu") THENL
   [EXPAND_TAC "V" THEN REWRITE_TAC[moi_s34_ft] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^N. v IN V ==> {v} IN kk` (LABEL_TAC "vk") THENL
   [EXPAND_TAC "V" THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^N. {v} IN kk ==> moi_s34_vb tt kk v SUBSET moi_s34_nb tt kk`
  (LABEL_TAC "vbn") THENL
   [USE_THEN "nbu" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s34_ft tt kk s SUBSET moi_s34_nb (tt:(real^N->bool)->bool) kk`
  ASSUME_TAC THENL
   [USE_THEN "ftu" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    USE_THEN "vbn" MATCH_MP_TAC THEN USE_THEN "vk" MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s) =
                UNIONS (IMAGE (\v. IMAGE f1 (moi_s34_vb tt kk v)) V)`
  (LABEL_TAC "tu") THENL
   [USE_THEN "ftu" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[IMAGE_UNIONS; GSYM IMAGE_o; o_DEF];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^N. v IN V
                ==> pl_ball 3 (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v))`
  (LABEL_TAC "pb") THENL
   [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    USE_THEN "vb" (MP_TAC o SPEC `v:real^N`) THEN
    ANTS_TAC THENL
     [USE_THEN "vk" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)) /\
                pl_polyhedron (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s))`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "tu" (fun th -> REWRITE_TAC[th]) THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_UNIONS; MATCH_MP_TAC MOI_S4J_PL_POLYHEDRON_UNIONS] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN BETA_TAC THEN
    (CONJ_TAC THENL [MATCH_MP_TAC FINITE_IMAGE THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    USE_THEN "pb" (fun th -> MP_TAC(MATCH_MP MOI_CGL_PL_BALL_BASIC
      (MP (SPEC `v:real^N` th) (ASSUME `(v:real^N) IN V`)))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s) INTER IMAGE f1 (moi_s34_bd tt kk) =
    IMAGE f1 (moi_s34_ft tt kk s INTER moi_s34_bd tt kk)`
  (LABEL_TAC "ti") THENL
   [MATCH_MP_TAC(SET_RULE
     `!(f:real^N->real^3) n a b.
        (!x y. x IN n /\ y IN n /\ f x = f y ==> x = y) /\
        a SUBSET n /\ b SUBSET n
        ==> IMAGE f a INTER IMAGE f b = IMAGE f (a INTER b)`) THEN
    EXISTS_TAC `moi_s34_nb (tt:(real^N->bool)->bool) kk` THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_polyhedron (moi_s34_ft tt kk s INTER moi_s34_bd (tt:(real^N->bool)->bool) kk)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `moi_s34_ft tt kk s INTER moi_s34_bd (tt:(real^N->bool)->bool) kk =
      UNIONS (IMAGE (\v. moi_s34_vb tt kk v INTER moi_s34_bd tt kk) V)`
    SUBST1_TAC THENL
     [USE_THEN "ftu" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[EXTENSION; IN_INTER; IN_UNIONS; EXISTS_IN_IMAGE] THEN
      BETA_TAC THEN REWRITE_TAC[IN_INTER] THEN MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_S4J_PL_POLYHEDRON_UNIONS THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN BETA_TAC THEN
    CONJ_TAC THENL [MATCH_MP_TAC FINITE_IMAGE THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_S4J_VB_BD_POLY THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      USE_THEN "vk" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_polyhedron (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s) INTER
                   IMAGE f1 (moi_s34_bd tt kk))`
  ASSUME_TAC THENL
   [USE_THEN "ti" (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN
    EXISTS_TAC `moi_s34_nb (tt:(real^N->bool)->bool) kk` THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `moi_s34_ft tt kk s SUBSET moi_s34_nb (tt:(real^N->bool)->bool) kk` THEN
      SET_TAC[];
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. open w /\
        (!v. {v} IN kk /\ ~(v IN s)
             ==> DISJOINT w (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)))
        ==> w INTER (IMAGE f1 (moi_s34_ft tt kk s) DIFF
                     interior (IMAGE f1 (moi_s34_ft tt kk s)))
            SUBSET IMAGE f1 (moi_s34_bd tt kk)`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^3->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dis")) THEN
    SUBGOAL_THEN `IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk) INTER w SUBSET
                  IMAGE f1 (moi_s34_ft tt kk s)` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `y:real^3` THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `?v:real^N. {v} IN kk /\ x IN moi_s34_vb tt kk v`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^N) IN moi_s34_nb tt kk` THEN
        USE_THEN "nbu" (fun th -> REWRITE_TAC[th]) THEN
        REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
        ALL_TAC] THEN
      ASM_CASES_TAC `(v:real^N) IN s` THENL
       [EXISTS_TAC `x:real^N` THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        USE_THEN "ftu" (fun th -> REWRITE_TAC[th]) THEN
        REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN EXISTS_TAC `v:real^N` THEN
        CONJ_TAC THENL
         [EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM] THEN
          CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
          FIRST_ASSUM ACCEPT_TAC];
        USE_THEN "dis" (MP_TAC o SPEC `v:real^N`) THEN
        ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
        DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN
        MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        EXISTS_TAC `x:real^N` THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)) INTER w SUBSET
                  interior (IMAGE f1 (moi_s34_ft tt kk s))` ASSUME_TAC THENL
     [MATCH_MP_TAC INTERIOR_MAXIMAL THEN CONJ_TAC THENL
       [MP_TAC(ISPEC `IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)` INTERIOR_SUBSET) THEN
        UNDISCH_TAC `IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk) INTER w SUBSET
                     IMAGE f1 (moi_s34_ft tt kk s)` THEN SET_TAC[];
        MATCH_MP_TAC OPEN_INTER THEN REWRITE_TAC[OPEN_INTERIOR] THEN
        FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s) SUBSET
                  IMAGE f1 (moi_s34_nb tt kk)` ASSUME_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    USE_THEN "bdfr" (fun th -> REWRITE_TAC[GSYM th]) THEN
    UNDISCH_TAC `IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s) SUBSET
                 IMAGE f1 (moi_s34_nb tt kk)` THEN
    UNDISCH_TAC `interior (IMAGE (f1:real^N->real^3) (moi_s34_nb tt kk)) INTER w SUBSET
                 interior (IMAGE f1 (moi_s34_ft tt kk s))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;


(* ------------------------------------------------------------------------- *)
(* A set whose loops are carried by a path-connected subset is              *)
(* path-connected (a constant loop is homotopic to a loop of j, and the    *)
(* homotopy moves the base point along a path).                             *)
(* ------------------------------------------------------------------------- *)

let MOI_S4J_LOOPS_PATH_CONNECTED = prove
 (`!(j:real^N->bool) t.
     path_connected j /\ j SUBSET t /\ loops_carried j t ==> path_connected t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x:real^N. x IN t ==> ?a. a IN j /\ path_component t x a`
  (LABEL_TAC "rep") THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    UNDISCH_TAC `loops_carried (j:real^N->bool) t` THEN REWRITE_TAC[loops_carried] THEN
    DISCH_THEN(MP_TAC o SPEC `linepath(x:real^N,x)`) THEN
    REWRITE_TAC[PATH_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                PATH_IMAGE_LINEPATH; SEGMENT_REFL; SING_SUBSET] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^1->real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `pathstart (q:real^1->real^N)` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPECL [`t:real^N->bool`; `linepath(x:real^N,x)`; `q:real^1->real^N`;
                   `vec 0:real^1`] HOMOTOPIC_LOOPS_IMP_PATH_COMPONENT_VALUE) THEN
    ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL] THEN
    REWRITE_TAC[pathstart; LINEPATH_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[path_connected; GSYM path_component] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
  USE_THEN "rep" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:real^N) IN t`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
  USE_THEN "rep" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(y:real^N) IN t`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `path_component (t:real^N->bool) a b` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP PATH_COMPONENT_MONO (ASSUME `(j:real^N->bool) SUBSET t`)) THEN
    DISCH_THEN(MP_TAC o SPEC `a:real^N`) THEN REWRITE_TAC[SUBSET; IN] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `path_connected (j:real^N->bool)` THEN
    REWRITE_TAC[path_connected; GSYM path_component] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ASM_MESON_TAC[PATH_COMPONENT_TRANS; PATH_COMPONENT_SYM]);;

(* ------------------------------------------------------------------------- *)
(* The image under h of the cone from a point of a 3-simplex r of kk over  *)
(* Bd s: compact, contractible, containing h(Bd s), meeting h(s) only in   *)
(* h(Bd s).                                                                 *)
(* ------------------------------------------------------------------------- *)

let MOI_S4J_CONE_IMAGE = prove
 (`!(tt:(real^N->bool)->bool) kk (h:real^N->real^3) s.
     moi_s34_tube tt kk /\ moi_s34_emb h (UNIONS tt) /\ s IN moi_s34_simp kk (&2)
     ==> ?cc. compact cc /\ contractible cc /\
              IMAGE h (relative_frontier s) SUBSET cc /\
              cc INTER IMAGE h s SUBSET IMAGE h (relative_frontier s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `s:real^N->bool`] MOI_S4J_SIMP2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `r:real^N->bool`; `p:real^N`;
                 `relative_frontier (s:real^N->bool)`] MOI_S4J_CONE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `D = UNIONS {segment[p:real^N,y] | y IN relative_frontier s}` THEN
  UNDISCH_TAC `moi_s34_emb (h:real^N->real^3) (UNIONS tt)` THEN
  REWRITE_TAC[moi_s34_emb] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(r:real^N->bool) SUBSET UNIONS tt` ASSUME_TAC THENL
   [UNDISCH_TAC `(r:real^N->bool) IN kk` THEN
    UNDISCH_TAC `(kk:(real^N->bool)->bool) SUBSET tt` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool) SUBSET UNIONS tt` ASSUME_TAC THENL
   [UNDISCH_TAC `(s:real^N->bool) IN kk` THEN
    UNDISCH_TAC `(kk:(real^N->bool)->bool) SUBSET tt` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(D:real^N->bool) SUBSET UNIONS tt` ASSUME_TAC THENL
   [UNDISCH_TAC `(D:real^N->bool) SUBSET r` THEN
    UNDISCH_TAC `(r:real^N->bool) SUBSET UNIONS tt` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^N->real^3) continuous_on D` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `UNIONS tt:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (h:real^N->real^3) D` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`D:real^N->bool`; `h:real^N->real^3`;
                   `IMAGE (h:real^N->real^3) D`] HOMEOMORPHISM_COMPACT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[SUBSET];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `g:real^3->real^N`) THEN
    MP_TAC(ISPECL [`D:real^N->bool`; `IMAGE (h:real^N->real^3) D`]
      HOMEOMORPHIC_CONTRACTIBLE) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `g:real^3->real^N`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(SET_RULE
     `!(f:real^N->real^3) n a b c.
        (!x y. x IN n /\ y IN n /\ f x = f y ==> x = y) /\
        a SUBSET n /\ b SUBSET n /\ a INTER b SUBSET c
        ==> IMAGE f a INTER IMAGE f b SUBSET IMAGE f c`) THEN
    EXISTS_TAC `UNIONS tt:real^N->bool` THEN ASM_REWRITE_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* Lemma 4 (Moise p.241).  w0 lies in the open set w avoiding the vertex  *)
(* balls of the vertices outside s (MOI_S4Q_AVOID_VB) and misses the       *)
(* compact set cc DIFF interior T, cc the cone image; for a PL 3-ball c    *)
(* with h(s) SUBSET interior c, c SUBSET w0, Step A and Step B give the    *)
(* carrying of H_1(T) by frontier c INTER T INTER f1(Bd N), the trace on T. *)
(* ------------------------------------------------------------------------- *)

let LEMMA4 = prove
 (MOI_S34_LEMMA4,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `s:real^N->bool`] MOI_S4J_SIMP2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `s:real^N->bool`]
    MOI_S4J_T_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "avoid")))) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `s:real^N->bool`] MOI_S4J_CONE_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `cc:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `pl_solid_torus (IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)) /\
    IMAGE (h:real^N->real^3) (relative_frontier s) SUBSET
    interior (IMAGE f1 (moi_s34_ft tt kk s)) /\
    loops_carried (IMAGE h (relative_frontier s)) (IMAGE f1 (moi_s34_ft tt kk s))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s34_frame tt kk h ep (f1:real^N->real^3) car` THEN
    REWRITE_TAC[moi_s34_frame] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1 o funpow 9 CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `s:real^N->bool`]
    MOI_S4Q_AVOID_VB) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `moi_s34_frame tt kk h ep (f1:real^N->real^3) car` THEN
    REWRITE_TAC[moi_s34_frame] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `w:real^3->bool` STRIP_ASSUME_TAC)] THEN
  ABBREV_TAC `tor = IMAGE (f1:real^N->real^3) (moi_s34_ft tt kk s)` THEN
  ABBREV_TAC `rr = IMAGE (h:real^N->real^3) (relative_frontier s)` THEN
  SUBGOAL_THEN `(rr:real^3->bool) SUBSET tor` ASSUME_TAC THENL
   [MP_TAC(ISPEC `tor:real^3->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(rr:real^3->bool) SUBSET interior tor` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^N->real^3) continuous_on relative_frontier s` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s34_emb (h:real^N->real^3) (UNIONS tt)` THEN
    REWRITE_TAC[moi_s34_emb] THEN STRIP_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `UNIONS tt:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `relative_frontier (s:real^N->bool) SUBSET s` THEN
    UNDISCH_TAC `(s:real^N->bool) IN kk` THEN
    UNDISCH_TAC `(kk:(real^N->bool)->bool) SUBSET tt` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `carries_h1 rr (tor:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOOPS_CARRIED_IMP_CARRIES_H1 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S4J_LOOPS_PATH_CONNECTED THEN EXISTS_TAC `rr:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "rr" THEN
    MATCH_MP_TAC PATH_CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (cc DIFF interior tor:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_DIFF THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED; OPEN_INTERIOR];
    ALL_TAC] THEN
  SUBGOAL_THEN `(rr:real^3->bool) SUBSET IMAGE (h:real^N->real^3) s` ASSUME_TAC THENL
   [EXPAND_TAC "rr" THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `w INTER ((:real^3) DIFF (cc DIFF interior tor))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[GSYM closed]; ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `IMAGE (h:real^N->real^3) s SUBSET w` THEN
    UNDISCH_TAC `cc INTER IMAGE (h:real^N->real^3) s SUBSET rr` THEN
    UNDISCH_TAC `(rr:real^3->bool) SUBSET interior tor` THEN SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `c:real^3->bool` THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4J_BALL3_FACTS) THEN
  SUBGOAL_THEN `(c:real^3->bool) SUBSET w /\ cc INTER c SUBSET interior tor`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `c SUBSET w INTER ((:real^3) DIFF (cc DIFF interior tor))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(rr:real^3->bool) SUBSET interior c` ASSUME_TAC THENL
   [UNDISCH_TAC `(rr:real^3->bool) SUBSET IMAGE (h:real^N->real^3) s` THEN
    UNDISCH_TAC `IMAGE (h:real^N->real^3) s SUBSET interior c` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`cc:real^3->bool`; `rr:real^3->bool`; `tor:real^3->bool`;
                 `c:real^3->bool`] MOI_S4J_STEP_A) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `frontier c INTER (tor DIFF interior tor) SUBSET
                tor INTER IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`
  ASSUME_TAC THENL
   [USE_THEN "avoid" (MP_TAC o SPEC `w:real^3->bool`) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    UNDISCH_TAC `frontier c SUBSET (c:real^3->bool)` THEN
    UNDISCH_TAC `(c:real^3->bool) SUBSET w` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:real^3->bool`; `tor:real^3->bool`;
                 `tor INTER IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`;
                 `r0:real^3->bool`] MOI_S4J_STEP_B) THEN
  ASM_REWRITE_TAC[INTER_SUBSET] THEN
  MATCH_MP_TAC(TAUT `(p <=> q) ==> p ==> q`) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[moi_s34_trace] THEN SET_TAC[]);;

