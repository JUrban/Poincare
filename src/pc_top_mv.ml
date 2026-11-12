(* ========================================================================= *)
(* pc_top_mv: Mayer-Vietoris for HOL Light singular homology of general     *)
(* topological spaces (homology.ml), from the Eilenberg-Steenrod axioms of  *)
(* the library (exactness of pairs and triples, naturality, excision).      *)
(*   G1 (ATOP_RELATIVE_MV_STATEMENT): the two diagram chases of Hatcher's   *)
(*   Lemma 3.27 for relative classes of an open pair (s, t).                *)
(*   G6 (ATOP_MAYER_VIETORIS_STATEMENT): the absolute Mayer-Vietoris        *)
(*   sequence of an open cover {s, t}, with exactness at all three places.  *)
(* Depends on the library and pc_top_iface (statement constants).          *)
(* ========================================================================= *)

needs "src/pc_top_iface.ml";;

prioritize_real();;
type_invention_error := true;;

let ATOP_EXCISION_MV = prove
 (`!q top s t:A->bool.
        open_in top s /\ open_in top t
        ==> group_isomorphism
              (relative_homology_group(q,subtopology top s,s INTER t),
               relative_homology_group(q,subtopology top (s UNION t),t))
              (hom_induced q (subtopology top s,s INTER t)
                             (subtopology top (s UNION t),t) (\x. x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(s:A->bool) SUBSET topspace top /\ t SUBSET topspace top`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`q:int`; `subtopology top (s UNION t:A->bool)`; `s UNION t:A->bool`;
                 `t:A->bool`; `t DIFF s:A->bool`] HOMOLOGY_EXCISION_AXIOM) THEN
  REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
  SUBGOAL_THEN `(s UNION t) INTER (s UNION t) = s UNION t:A->bool /\
                (s UNION t) INTER ((s UNION t) DIFF (t DIFF s)) = s:A->bool /\
                t DIFF (t DIFF s) = s INTER t:A->bool`
  (fun th -> REWRITE_TAC[th]) THENL [SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[SUBSET_UNION] THEN
  SUBGOAL_THEN
   `subtopology top (s UNION t) closure_of (t DIFF s) = t DIFF s:A->bool /\
    subtopology top (s UNION t) interior_of t = t:A->bool`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[CLOSURE_OF_EQ] THEN
      SUBGOAL_THEN `t DIFF s:A->bool = (s UNION t) DIFF ((s UNION t) INTER s)`
      SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC CLOSED_IN_DIFF THEN CONJ_TAC THENL
       [MP_TAC(ISPEC `subtopology top (s UNION t:A->bool)` CLOSED_IN_TOPSPACE) THEN
        REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN MATCH_MP_TAC EQ_IMP THEN
        AP_TERM_TAC THEN ASM SET_TAC[];
        MATCH_MP_TAC OPEN_IN_SUBTOPOLOGY_INTER_OPEN THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[INTERIOR_OF_EQ] THEN
      SUBGOAL_THEN `t:A->bool = (s UNION t) INTER t` (fun th ->
        GEN_REWRITE_TAC RAND_CONV [th]) THENL [SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC OPEN_IN_SUBTOPOLOGY_INTER_OPEN THEN ASM_REWRITE_TAC[]];
    SET_TAC[]]);;

let ATOP_HOM_INDUCED_INCLUSIONS = prove
 (`!p top1 s1 top2 s2 top3 (s3:A->bool).
        continuous_map (top1,top2) (\x. x) /\ continuous_map (top2,top3) (\x. x) /\
        s1 SUBSET s2 /\ s2 SUBSET s3
        ==> hom_induced p (top2,s2) (top3,s3) (\x. x) o
            hom_induced p (top1,s1) (top2,s2) (\x. x) =
            hom_induced p (top1,s1) (top3,s3) (\x. x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:int`; `top1:A topology`; `s1:A->bool`; `top2:A topology`;
                 `s2:A->bool`; `top3:A topology`; `s3:A->bool`; `\x:A. x`; `\x:A. x`]
                HOM_INDUCED_COMPOSE) THEN
  ASM_REWRITE_TAC[IMAGE_ID] THEN
  SUBGOAL_THEN `(\x:A. x) o (\x:A. x) = (\x. x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; MESON_TAC[]]);;

let ATOP_CONTINUOUS_MAP_INCLUSION = prove
 (`!top s t:A->bool.
        s SUBSET t
        ==> continuous_map (subtopology top s,subtopology top t) (\x. x) /\
            continuous_map (subtopology top s,top) (\x. x) /\
            continuous_map (top,top) (\x. x)`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; CONTINUOUS_MAP_ID] THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY; IMAGE_ID] THEN
  SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; CONTINUOUS_MAP_ID] THEN ASM SET_TAC[]);;


let ATOP_GROUP_HOM_ID = prove
 (`!G H (f:A->B). group_homomorphism (G,H) f ==> f(group_id G) = group_id H`,
  SIMP_TAC[group_homomorphism]);;

let ATOP_TRIVIAL_GROUP_ELEMENT = prove
 (`!G (x:A). trivial_group G /\ x IN group_carrier G ==> x = group_id G`,
  REWRITE_TAC[trivial_group] THEN SET_TAC[]);;

let ATOP_RELATIVE_MV_INJ = prove
 (`!p top s t:A->bool.
        open_in top s /\ open_in top t /\
        trivial_group(relative_homology_group(p + &1,top,s UNION t))
        ==> !a. a IN group_carrier(relative_homology_group(p,top,s INTER t)) /\
                hom_induced p (top,s INTER t) (top,s) (\x. x) a =
                group_id(relative_homology_group(p,top,s)) /\
                hom_induced p (top,s INTER t) (top,t) (\x. x) a =
                group_id(relative_homology_group(p,top,t))
                ==> a = group_id(relative_homology_group(p,top,s INTER t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `a:((num->real)->A)frag->bool` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`p:int`; `top:A topology`; `s:A->bool`; `s INTER t:A->bool`]
                HOMOLOGY_EXACTNESS_TRIPLE_3) THEN
  REWRITE_TAC[INTER_SUBSET; group_exactness] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "kh") (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "ex1"))) THEN
  SUBGOAL_THEN
   `?b. b IN group_carrier(relative_homology_group(p,subtopology top s,s INTER t)) /\
        a = hom_induced p (subtopology top s,s INTER t) (top,s INTER t) (\x:A. x) b`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `a IN group_kernel (relative_homology_group (p,top,s INTER t),
                         relative_homology_group (p,top,s))
                        (hom_induced p (top,s INTER t) (top,s) (\x:A. x))`
    MP_TAC THENL [ASM_REWRITE_TAC[group_kernel; IN_ELIM_THM]; ALL_TAC] THEN
    REMOVE_THEN "ex1" (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[group_image; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `hom_induced p (subtopology top (s UNION t),t) (top,t) (\x:A. x)
      (hom_induced p (subtopology top s,s INTER t)
                     (subtopology top (s UNION t),t) (\x. x) b) =
    group_id(relative_homology_group(p,top,t))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p:int`; `subtopology top (s:A->bool)`; `s INTER t:A->bool`;
                   `subtopology top (s UNION t:A->bool)`; `t:A->bool`;
                   `top:A topology`; `t:A->bool`] ATOP_HOM_INDUCED_INCLUSIONS) THEN
    MP_TAC(ISPECL [`p:int`; `subtopology top (s:A->bool)`; `s INTER t:A->bool`;
                   `top:A topology`; `s INTER t:A->bool`;
                   `top:A topology`; `t:A->bool`] ATOP_HOM_INDUCED_INCLUSIONS) THEN
    SIMP_TAC[ATOP_CONTINUOUS_MAP_INCLUSION; SUBSET_UNION; INTER_SUBSET;
             SUBSET_REFL; CONTINUOUS_MAP_ID; CONTINUOUS_MAP_FROM_SUBTOPOLOGY] THEN
    DISCH_THEN(MP_TAC o C AP_THM `b:((num->real)->A)frag->bool`) THEN
    DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o C AP_THM `b:((num->real)->A)frag->bool`) THEN
                         MP_TAC th) THEN
    REWRITE_TAC[o_THM] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC
     `a = hom_induced p (subtopology top s,s INTER t) (top,s INTER t) (\x:A. x) b` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `hom_induced p (subtopology top s,s INTER t) (subtopology top (s UNION t),t)
                  (\x:A. x) b =
    group_id(relative_homology_group(p,subtopology top (s UNION t),t))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p + &1:int`; `top:A topology`; `s UNION t:A->bool`; `t:A->bool`]
                  HOMOLOGY_EXACTNESS_TRIPLE_2) THEN
    REWRITE_TAC[SUBSET_UNION; group_exactness; INT_ARITH `(p + &1) - &1:int = p`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "ex2"))) THEN
    SUBGOAL_THEN
     `hom_induced p (subtopology top s,s INTER t) (subtopology top (s UNION t),t)
                    (\x:A. x) b IN
      group_kernel (relative_homology_group (p,subtopology top (s UNION t),t),
                    relative_homology_group (p,top,t))
                   (hom_induced p (subtopology top (s UNION t),t) (top,t) (\x:A. x))`
    MP_TAC THENL
     [ASM_REWRITE_TAC[group_kernel; IN_ELIM_THM; HOM_INDUCED]; ALL_TAC] THEN
    REMOVE_THEN "ex2" (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[group_image; IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:((num->real)->A)frag->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `c = group_id(relative_homology_group(p + &1,top,s UNION t:A->bool))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC ATOP_TRIVIAL_GROUP_ELEMENT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC ATOP_GROUP_HOM_ID THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:int`; `top:A topology`; `s:A->bool`; `t:A->bool`]
                ATOP_EXCISION_MV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP GROUP_ISOMORPHISM_IMP_MONOMORPHISM) THEN
  REWRITE_TAC[GROUP_MONOMORPHISM_ALT_EQ] THEN
  DISCH_THEN(MP_TAC o SPEC `b:((num->real)->A)frag->bool` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC
   `a = hom_induced p (subtopology top s,s INTER t) (top,s INTER t) (\x:A. x)
          (group_id (relative_homology_group (p,subtopology top s,s INTER t)))` THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC ATOP_GROUP_HOM_ID THEN
  REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED]);;

let ATOP_ABELIAN_MUL_DIV = prove
 (`!G x (y:A). abelian_group G /\ x IN group_carrier G /\ y IN group_carrier G
               ==> group_mul G x (group_div G y x) = y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `group_mul G x (group_div G y x) = group_mul G (group_div G y x) (x:A)`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[abelian_group]) THEN
    ASM_SIMP_TAC[GROUP_DIV];
    ASM_SIMP_TAC[group_div; GSYM GROUP_MUL_ASSOC; GROUP_INV;
                 GROUP_MUL_LINV; GROUP_MUL_RID]]);;

let ATOP_RELATIVE_MV_GLUE = prove
 (`!p top s t:A->bool.
        open_in top s /\ open_in top t
        ==> !a b. a IN group_carrier(relative_homology_group(p,top,s)) /\
                  b IN group_carrier(relative_homology_group(p,top,t)) /\
                  hom_induced p (top,s) (top,s UNION t) (\x. x) a =
                  hom_induced p (top,t) (top,s UNION t) (\x. x) b
                  ==> ?c. c IN group_carrier(relative_homology_group(p,top,s INTER t)) /\
                          hom_induced p (top,s INTER t) (top,s) (\x. x) c = a /\
                          hom_induced p (top,s INTER t) (top,t) (\x. x) c = b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:((num->real)->A)frag->bool`; `b:((num->real)->A)frag->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `hom_relboundary p (top:A topology,s,s INTER t) a =
    group_id(relative_homology_group(p - &1,subtopology top s,s INTER t))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p:int`; `top:A topology`; `s:A->bool`; `s INTER t:A->bool`;
                   `top:A topology`; `s UNION t:A->bool`; `t:A->bool`; `\x:A. x`]
                  NATURALITY_HOM_INDUCED_RELBOUNDARY) THEN
    REWRITE_TAC[CONTINUOUS_MAP_ID; IMAGE_ID; SUBSET_UNION; INTER_SUBSET] THEN
    DISCH_THEN(MP_TAC o C AP_THM `a:((num->real)->A)frag->bool`) THEN
    REWRITE_TAC[o_THM] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`p:int`; `top:A topology`; `s UNION t:A->bool`; `t:A->bool`]
                  HOMOLOGY_EXACTNESS_TRIPLE_1) THEN
    REWRITE_TAC[SUBSET_UNION; group_exactness] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
    DISCH_THEN(MP_TAC o SPEC
      `hom_induced p (top,t) (top,s UNION t) (\x:A. x) b` o
      REWRITE_RULE[EXTENSION]) THEN
    REWRITE_TAC[group_image; group_kernel; IN_IMAGE; IN_ELIM_THM] THEN
    MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> ((p <=> q) ==> r)`) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`p - &1:int`; `top:A topology`; `s:A->bool`; `t:A->bool`]
                  ATOP_EXCISION_MV) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP GROUP_ISOMORPHISM_IMP_MONOMORPHISM) THEN
    REWRITE_TAC[GROUP_MONOMORPHISM_ALT_EQ] THEN
    DISCH_THEN(MP_TAC o SPEC `hom_relboundary p (top,s,s INTER t:A->bool) a` o
      CONJUNCT2) THEN
    ASM_REWRITE_TAC[HOM_RELBOUNDARY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?c1. c1 IN group_carrier(relative_homology_group(p,top,s INTER t)) /\
         a = hom_induced p (top,s INTER t) (top,s) (\x:A. x) c1`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p:int`; `top:A topology`; `s:A->bool`; `s INTER t:A->bool`]
                  HOMOLOGY_EXACTNESS_TRIPLE_1) THEN
    REWRITE_TAC[INTER_SUBSET; group_exactness] THEN
    DISCH_THEN(MP_TAC o SPEC `a:((num->real)->A)frag->bool` o
      REWRITE_RULE[EXTENSION] o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[group_image; group_kernel; IN_IMAGE; IN_ELIM_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c. hom_induced p (top,t) (top,s UNION t) (\x:A. x)
          (hom_induced p (top,s INTER t) (top,t) (\x:A. x) c) =
        hom_induced p (top,s) (top,s UNION t) (\x:A. x)
          (hom_induced p (top,s INTER t) (top,s) (\x:A. x) c)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`p:int`; `top:A topology`; `s INTER t:A->bool`; `top:A topology`;
                   `t:A->bool`; `top:A topology`; `s UNION t:A->bool`]
                  ATOP_HOM_INDUCED_INCLUSIONS) THEN
    MP_TAC(ISPECL [`p:int`; `top:A topology`; `s INTER t:A->bool`; `top:A topology`;
                   `s:A->bool`; `top:A topology`; `s UNION t:A->bool`]
                  ATOP_HOM_INDUCED_INCLUSIONS) THEN
    REWRITE_TAC[CONTINUOUS_MAP_ID; INTER_SUBSET; SUBSET_UNION] THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `g = group_div (relative_homology_group(p,top,t)) b
          (hom_induced p (top,s INTER t) (top,t) (\x:A. x) c1)` THEN
  SUBGOAL_THEN `g IN group_carrier(relative_homology_group(p,top,t:A->bool))`
  ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN MATCH_MP_TAC GROUP_DIV THEN ASM_REWRITE_TAC[HOM_INDUCED];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?d. d IN group_carrier(relative_homology_group(p,subtopology top s,s INTER t)) /\
        g = hom_induced p (subtopology top (s UNION t),t) (top,t) (\x:A. x)
              (hom_induced p (subtopology top s,s INTER t)
                             (subtopology top (s UNION t),t) (\x. x) d)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `?d'. d' IN group_carrier(relative_homology_group(p,subtopology top (s UNION t),t)) /\
           g = hom_induced p (subtopology top (s UNION t),t) (top,t) (\x:A. x) d'`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`p:int`; `top:A topology`; `s UNION t:A->bool`; `t:A->bool`]
                    HOMOLOGY_EXACTNESS_TRIPLE_3) THEN
      REWRITE_TAC[SUBSET_UNION; group_exactness] THEN
      DISCH_THEN(MP_TAC o SPEC `g:((num->real)->A)frag->bool` o
        REWRITE_RULE[EXTENSION] o CONJUNCT2 o CONJUNCT2) THEN
      REWRITE_TAC[group_image; group_kernel; IN_IMAGE; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o snd o EQ_IMP_RULE) THEN
      MATCH_MP_TAC(TAUT `q /\ (p ==> r) ==> (q ==> p) ==> r`) THEN
      CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "g" THEN
      MP_TAC(ISPECL [`relative_homology_group(p,top,t:A->bool)`;
                     `relative_homology_group(p,top,s UNION t:A->bool)`;
                     `hom_induced p (top,t) (top,s UNION t) (\x:A. x)`]
                    GROUP_HOMOMORPHISM_DIV) THEN
      REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED] THEN
      DISCH_THEN(MP_TAC o SPECL
       [`b:((num->real)->A)frag->bool`;
        `hom_induced p (top,s INTER t) (top,t) (\x:A. x) c1`]) THEN
      ASM_REWRITE_TAC[HOM_INDUCED] THEN DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN
       `hom_induced p (top,s) (top,s UNION t) (\x:A. x)
          (hom_induced p (top,s INTER t) (top,s) (\x:A. x) c1) =
        hom_induced p (top,t) (top,s UNION t) (\x:A. x) b`
      SUBST1_TAC THENL
       [UNDISCH_TAC `a = hom_induced p (top,s INTER t) (top,s) (\x:A. x) c1` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC GROUP_DIV_REFL THEN REWRITE_TAC[HOM_INDUCED]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`p:int`; `top:A topology`; `s:A->bool`; `t:A->bool`]
                  ATOP_EXCISION_MV) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP GROUP_ISOMORPHISM_IMP_EPIMORPHISM) THEN
    REWRITE_TAC[group_epimorphism] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\u. (d':((num->real)->A)frag->bool) IN u` o
      CONJUNCT2) THEN
    REWRITE_TAC[IN_IMAGE] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:((num->real)->A)frag->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `d:((num->real)->A)frag->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `g = hom_induced p (subtopology top (s UNION t),t) (top,t) (\x:A. x) d'` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC
   `group_mul (relative_homology_group(p,top,s INTER t)) c1
      (hom_induced p (subtopology top s,s INTER t) (top,s INTER t) (\x:A. x) d)` THEN
  SUBGOAL_THEN
   `hom_induced p (subtopology top s,s INTER t) (top,s INTER t) (\x:A. x) d IN
    group_carrier(relative_homology_group(p,top,s INTER t))`
  ASSUME_TAC THENL [REWRITE_TAC[HOM_INDUCED]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC GROUP_MUL THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`p:int`; `top:A topology`; `s INTER t:A->bool`; `top:A topology`;
                   `s:A->bool`; `\x:A. x`] GROUP_HOMOMORPHISM_HOM_INDUCED) THEN
    REWRITE_TAC[group_homomorphism] THEN
    DISCH_THEN(fun th -> ASM_SIMP_TAC[CONJUNCT2(CONJUNCT2(CONJUNCT2 th))]) THEN
    SUBGOAL_THEN
     `hom_induced p (top,s INTER t) (top,s) (\x:A. x)
        (hom_induced p (subtopology top s,s INTER t) (top,s INTER t) (\x. x) d) =
      group_id(relative_homology_group(p,top,s))`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL [`p:int`; `top:A topology`; `s:A->bool`; `s INTER t:A->bool`]
                    HOMOLOGY_EXACTNESS_TRIPLE_3) THEN
      REWRITE_TAC[INTER_SUBSET; group_exactness] THEN
      DISCH_THEN(MP_TAC o SPEC
        `hom_induced p (subtopology top s,s INTER t) (top,s INTER t) (\x:A. x) d` o
        REWRITE_RULE[EXTENSION] o CONJUNCT2 o CONJUNCT2) THEN
      REWRITE_TAC[group_image; group_kernel; IN_IMAGE; IN_ELIM_THM] THEN
      MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> ((p <=> q) ==> r)`) THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; SIMP_TAC[]];
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC GROUP_MUL_RID THEN
      ASM_REWRITE_TAC[HOM_INDUCED]];
    MP_TAC(ISPECL [`p:int`; `top:A topology`; `s INTER t:A->bool`; `top:A topology`;
                   `t:A->bool`; `\x:A. x`] GROUP_HOMOMORPHISM_HOM_INDUCED) THEN
    REWRITE_TAC[group_homomorphism] THEN
    DISCH_THEN(fun th -> ASM_SIMP_TAC[CONJUNCT2(CONJUNCT2(CONJUNCT2 th))]) THEN
    SUBGOAL_THEN
     `hom_induced p (top,s INTER t) (top,t) (\x:A. x)
        (hom_induced p (subtopology top s,s INTER t) (top,s INTER t) (\x. x) d) = g`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`p:int`; `subtopology top (s:A->bool)`; `s INTER t:A->bool`;
                     `subtopology top (s UNION t:A->bool)`; `t:A->bool`;
                     `top:A topology`; `t:A->bool`] ATOP_HOM_INDUCED_INCLUSIONS) THEN
      MP_TAC(ISPECL [`p:int`; `subtopology top (s:A->bool)`; `s INTER t:A->bool`;
                     `top:A topology`; `s INTER t:A->bool`;
                     `top:A topology`; `t:A->bool`] ATOP_HOM_INDUCED_INCLUSIONS) THEN
      SIMP_TAC[ATOP_CONTINUOUS_MAP_INCLUSION; SUBSET_UNION; INTER_SUBSET;
               SUBSET_REFL; CONTINUOUS_MAP_ID; CONTINUOUS_MAP_FROM_SUBTOPOLOGY] THEN
      REWRITE_TAC[FUN_EQ_THM; o_THM] THEN MESON_TAC[];
      EXPAND_TAC "g" THEN MATCH_MP_TAC ATOP_ABELIAN_MUL_DIV THEN
      ASM_REWRITE_TAC[ABELIAN_RELATIVE_HOMOLOGY_GROUP; HOM_INDUCED]]]);;

let ATOP_RELATIVE_MV = prove
 (`ATOP_RELATIVE_MV_STATEMENT (:A)`,
  REWRITE_TAC[ATOP_RELATIVE_MV_STATEMENT] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC ATOP_RELATIVE_MV_INJ THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC ATOP_RELATIVE_MV_GLUE THEN ASM_REWRITE_TAC[]]);;


(* ========================================================================= *)
(* The algebra of the Mayer-Vietoris sequence: from the long                *)
(* exact sequences of the pairs (t, s INTER t) and (X, s), the excision     *)
(* isomorphism between them and naturality, the three exactness statements  *)
(* (abstract groups; each lemma uses only the hypotheses it needs).          *)
(* ========================================================================= *)

let ATOP_EXACT_KERNEL = prove
 (`!G H K (f:A->B) (g:B->C) x.
        group_exactness (G,H,K) (f,g) /\ x IN group_carrier G
        ==> g(f x) = group_id K`,
  REWRITE_TAC[group_exactness; group_image; group_kernel; EXTENSION] THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[]);;

let ATOP_EXACT_IMAGE = prove
 (`!G H K (f:A->B) (g:B->C) y.
        group_exactness (G,H,K) (f,g) /\ y IN group_carrier H /\ g y = group_id K
        ==> ?x. x IN group_carrier G /\ f x = y`,
  REWRITE_TAC[group_exactness; group_image; group_kernel; EXTENSION] THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[]);;

let ATOP_HOMOMORPHISM_IN = prove
 (`!G H (f:A->B) x.
        group_homomorphism (G,H) f /\ x IN group_carrier G ==> f x IN group_carrier H`,
  REWRITE_TAC[group_homomorphism; SUBSET; FORALL_IN_IMAGE] THEN MESON_TAC[]);;

let ATOP_EXACT_HOMS = prove
 (`!G H K (f:A->B) (g:B->C).
        group_exactness (G,H,K) (f,g)
        ==> group_homomorphism (G,H) f /\ group_homomorphism (H,K) g`,
  SIMP_TAC[group_exactness]);;

(* Exactness at H_{p-1}(s INTER t).                                          *)

let ATOP_MV_EXACT_3 = prove
 (`!GD GE GL GF GK GM (qX:D->E) (dX:E->L) (e:F->E) e' (dT:F->K) (iS1:K->L) (iT1:K->M).
        group_exactness (GD,GE,GL) (qX,dX) /\
        group_exactness (GF,GK,GM) (dT,iT1) /\
        group_isomorphisms (GF,GE) (e,e') /\
        group_homomorphism (GK,GL) iS1 /\
        (!y. y IN group_carrier GF ==> dX(e y) = iS1(dT y))
        ==> group_exactness (GD,GK,prod_group GL GM)
              (dT o e' o qX,(\c. iS1 c,iT1 c))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(MATCH_MP ATOP_EXACT_HOMS th))
   (CONJUNCTS_THEN2
    (fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(MATCH_MP ATOP_EXACT_HOMS th))
    (CONJUNCTS_THEN2
     (fun th -> ASSUME_TAC th THEN
                STRIP_ASSUME_TAC(GEN_REWRITE_RULE I [group_isomorphisms] th))
     STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[group_exactness; GROUP_HOMOMORPHISM_PAIRED] THEN CONJ_TAC THENL
   [MATCH_MP_TAC GROUP_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC `GF:F group` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC GROUP_HOMOMORPHISM_COMPOSE THEN
    EXISTS_TAC `GE:E group` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[group_image; group_kernel; EXTENSION; IN_IMAGE; IN_ELIM_THM;
              PROD_GROUP; PAIR_EQ; o_THM] THEN
  X_GEN_TAC `c:K` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:D` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(qX:D->E) x IN group_carrier GE /\ (e':E->F) (qX x) IN group_carrier GF`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[ATOP_HOMOMORPHISM_IN]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[ATOP_HOMOMORPHISM_IN];
      FIRST_X_ASSUM(MP_TAC o SPEC `(e':E->F) (qX(x:D))`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC ATOP_EXACT_KERNEL THEN
      MAP_EVERY EXISTS_TAC [`GD:D group`; `GE:E group`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC ATOP_EXACT_KERNEL THEN
      MAP_EVERY EXISTS_TAC [`GF:F group`; `GK:K group`] THEN ASM_REWRITE_TAC[]];
    STRIP_TAC THEN
    MP_TAC(ISPECL [`GF:F group`; `GK:K group`; `GM:M group`; `dT:F->K`; `iT1:K->M`;
                   `c:K`] ATOP_EXACT_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y:F` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`GD:D group`; `GE:E group`; `GL:L group`; `qX:D->E`; `dX:E->L`;
                   `(e:F->E) y`] ATOP_EXACT_IMAGE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN ASM_MESON_TAC[ATOP_HOMOMORPHISM_IN]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:D` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `x:D` THEN ASM_SIMP_TAC[]]);;

let ATOP_HOMOMORPHISM_DIFF = prove
 (`!G1 G2 H (f:A->C) (g:B->C).
        abelian_group H /\ group_homomorphism (G1,H) f /\ group_homomorphism (G2,H) g
        ==> group_homomorphism (prod_group G1 G2,H) (\(a,b). group_div H (f a) (g b))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LAMBDA_PAIR; group_div] THEN
  MATCH_MP_TAC ABELIAN_GROUP_HOMOMORPHISM_GROUP_MUL THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `(\p:A#B. (f:A->C) (FST p)) = f o FST` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ASM_REWRITE_TAC[GROUP_HOMOMORPHISM_OF_FST]];
    SUBGOAL_THEN `(\p:A#B. group_inv H ((g:B->C) (SND p))) = (group_inv H o g) o SND`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; REWRITE_TAC[GROUP_HOMOMORPHISM_OF_SND]] THEN
    MATCH_MP_TAC GROUP_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC `H:C group` THEN
    ASM_REWRITE_TAC[ABELIAN_GROUP_HOMOMORPHISM_INVERSION]]);;

(* Exactness at H_p(X).                                                        *)

let ATOP_MV_EXACT_2 = prove
 (`!GB GC GD GE GF GK (jS:B->D) (jT:C->D) (qX:D->E) (rT:C->F) (e:F->E) e' (dT:F->K).
        abelian_group GD /\
        group_exactness (GB,GD,GE) (jS,qX) /\
        group_exactness (GC,GF,GK) (rT,dT) /\
        group_homomorphism (GC,GD) jT /\
        group_isomorphisms (GF,GE) (e,e') /\
        (!y. y IN group_carrier GC ==> e(rT y) = qX(jT y))
        ==> group_exactness (prod_group GB GC,GD,GK)
              ((\(a,b). group_div GD (jS a) (jT b)),dT o e' o qX)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
   (fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(MATCH_MP ATOP_EXACT_HOMS th))
   (CONJUNCTS_THEN2
    (fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(MATCH_MP ATOP_EXACT_HOMS th))
    (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2
      (fun th -> ASSUME_TAC th THEN
                 STRIP_ASSUME_TAC(GEN_REWRITE_RULE I [group_isomorphisms] th))
      (LABEL_TAC "N2")))))) THEN
  SUBGOAL_THEN `group_homomorphism (GD,GK) ((dT:F->K) o (e':E->F) o (qX:D->E))` ASSUME_TAC THENL
   [MATCH_MP_TAC GROUP_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC `GF:F group` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC GROUP_HOMOMORPHISM_COMPOSE THEN
    EXISTS_TAC `GE:E group` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[group_exactness; ATOP_HOMOMORPHISM_DIFF] THEN
  REWRITE_TAC[group_image; group_kernel; EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
  REWRITE_TAC[EXISTS_PAIR_THM; PROD_GROUP; IN_CROSS] THEN
  X_GEN_TAC `x:D` THEN EQ_TAC THENL
   [REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:B`; `b:C`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(jS:B->D) a IN group_carrier GD /\ (jT:C->D) b IN group_carrier GD /\
                  (rT:C->F) b IN group_carrier GF`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ATOP_HOMOMORPHISM_IN]; ALL_TAC] THEN
    ASM_SIMP_TAC[GROUP_DIV] THEN
    MP_TAC(ISPECL [`GD:D group`; `GK:K group`; `(dT:F->K) o (e':E->F) o (qX:D->E)`]
                  GROUP_HOMOMORPHISM_DIV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ASM_SIMP_TAC[th]) THEN
    REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(qX:D->E) (jS (a:B)) = group_id GE` SUBST1_TAC THENL
     [MATCH_MP_TAC ATOP_EXACT_KERNEL THEN
      MAP_EVERY EXISTS_TAC [`GB:B group`; `GD:D group`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "N2" (fun th ->
      REWRITE_TAC[GSYM(MATCH_MP th (ASSUME `(b:C) IN group_carrier GC`))]) THEN
    ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `(dT:F->K) (rT (b:C)) = group_id GK` SUBST1_TAC THENL
     [MATCH_MP_TAC ATOP_EXACT_KERNEL THEN
      MAP_EVERY EXISTS_TAC [`GC:C group`; `GF:F group`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(e':E->F) (group_id GE) = group_id GF /\
                  (dT:F->K) (group_id GF) = group_id GK`
    (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[group_homomorphism]; ALL_TAC] THEN
    SIMP_TAC[GROUP_DIV_REFL; GROUP_ID];
    REWRITE_TAC[o_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(qX:D->E) x IN group_carrier GE /\ (e':E->F) (qX x) IN group_carrier GF`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ATOP_HOMOMORPHISM_IN]; ALL_TAC] THEN
    MP_TAC(ISPECL [`GC:C group`; `GF:F group`; `GK:K group`; `rT:C->F`; `dT:F->K`;
                   `(e':E->F) (qX(x:D))`] ATOP_EXACT_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `b:C` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(jT:C->D) b IN group_carrier GD` ASSUME_TAC THENL
     [ASM_MESON_TAC[ATOP_HOMOMORPHISM_IN]; ALL_TAC] THEN
    SUBGOAL_THEN `(qX:D->E) x = qX(jT(b:C))` ASSUME_TAC THENL
     [USE_THEN "N2" (fun th ->
        REWRITE_TAC[GSYM(MATCH_MP th (ASSUME `(b:C) IN group_carrier GC`))]) THEN
      UNDISCH_TAC `(rT:C->F) b = (e':E->F) ((qX:D->E) x)` THEN DISCH_THEN SUBST1_TAC THEN
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`GB:B group`; `GD:D group`; `GE:E group`; `jS:B->D`; `qX:D->E`;
                   `group_div GD x ((jT:C->D) b)`] ATOP_EXACT_IMAGE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[GROUP_DIV] THEN
      MP_TAC(ISPECL [`GD:D group`; `GE:E group`; `qX:D->E`] GROUP_HOMOMORPHISM_DIV) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ASM_SIMP_TAC[th]) THEN
      MATCH_MP_TAC GROUP_DIV_REFL THEN ASM_MESON_TAC[ATOP_HOMOMORPHISM_IN];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:B` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`a:B`; `group_inv GC (b:C)`] THEN
    ASM_SIMP_TAC[GROUP_INV] THEN
    SUBGOAL_THEN `(jT:C->D) (group_inv GC b) = group_inv GD (jT b)` SUBST1_TAC THENL
     [ASM_MESON_TAC[group_homomorphism]; ALL_TAC] THEN
    ASM_SIMP_TAC[group_div; GROUP_INV_INV; GSYM GROUP_MUL_ASSOC; GROUP_INV;
                 GROUP_MUL_LINV; GROUP_MUL_RID]]);;

(* Exactness at H_p(s) x H_p(t).                                              *)

let ATOP_MV_EXACT_1 = prove
 (`!GA GB GC GD GE GF GP GQ (iS:A->B) (iT:A->C) (jS:B->D) (jT:C->D) (qX:D->E)
    (rT:C->F) (e:F->E) (e2:Q->P) (dX2:P->B) (dT2:Q->A).
        abelian_group GB /\ abelian_group GD /\
        group_exactness (GP,GB,GD) (dX2,jS) /\
        group_exactness (GB,GD,GE) (jS,qX) /\
        group_exactness (GA,GC,GF) (iT,rT) /\
        group_exactness (GQ,GA,GC) (dT2,iT) /\
        group_homomorphism (GA,GB) iS /\ group_homomorphism (GC,GD) jT /\
        group_monomorphism (GF,GE) e /\ group_epimorphism (GQ,GP) e2 /\
        (!y. y IN group_carrier GC ==> e(rT y) = qX(jT y)) /\
        (!c. c IN group_carrier GA ==> jS(iS c) = jT(iT c)) /\
        (!w. w IN group_carrier GQ ==> dX2(e2 w) = iS(dT2 w))
        ==> group_exactness (GA,prod_group GB GC,GD)
              ((\c. iS c,iT c),(\(a,b). group_div GD (jS a) (jT b)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun t -> FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ATOP_EXACT_HOMS o
     check (fun th -> concl th = t)))
   [`group_exactness (GP,GB,GD) (dX2:P->B,jS:B->D)`;
    `group_exactness (GB,GD,GE) (jS:B->D,qX:D->E)`;
    `group_exactness (GA,GC,GF) (iT:A->C,rT:C->F)`;
    `group_exactness (GQ,GA,GC) (dT2:Q->A,iT:A->C)`] THEN
  ASM_SIMP_TAC[group_exactness; GROUP_HOMOMORPHISM_PAIRED; ATOP_HOMOMORPHISM_DIFF] THEN
  REWRITE_TAC[group_image; group_kernel; EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
  REWRITE_TAC[FORALL_PAIR_THM; PROD_GROUP; IN_CROSS; PAIR_EQ] THEN
  MAP_EVERY X_GEN_TAC [`a:B`; `b:C`] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `c:A` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(iS:A->B) c IN group_carrier GB /\ (iT:A->C) c IN group_carrier GC /\
                  (jT:C->D) (iT c) IN group_carrier GD`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ATOP_HOMOMORPHISM_IN]; ALL_TAC] THEN
    ASM_SIMP_TAC[GROUP_DIV_REFL];
    STRIP_TAC] THEN
  SUBGOAL_THEN `(jS:B->D) a IN group_carrier GD /\ (jT:C->D) b IN group_carrier GD /\
                (rT:C->F) b IN group_carrier GF`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ATOP_HOMOMORPHISM_IN]; ALL_TAC] THEN
  SUBGOAL_THEN `(jS:B->D) a = jT(b:C)` ASSUME_TAC THENL
   [ASM_MESON_TAC[GROUP_DIV_EQ_ID]; ALL_TAC] THEN
  SUBGOAL_THEN `(rT:C->F) b = group_id GF` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [GROUP_MONOMORPHISM_ALT_EQ] o
      check (fun th -> concl th = `group_monomorphism (GF,GE) (e:F->E)`)) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP th
      (ASSUME `(rT:C->F) b IN group_carrier GF`))]) THEN
    ASM_SIMP_TAC[] THEN UNDISCH_TAC `(jS:B->D) a = jT(b:C)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC ATOP_EXACT_KERNEL THEN
    MAP_EVERY EXISTS_TAC [`GB:B group`; `GD:D group`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`GA:A group`; `GC:C group`; `GF:F group`; `iT:A->C`; `rT:C->F`; `b:C`]
                ATOP_EXACT_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `c1:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(iS:A->B) c1 IN group_carrier GB` ASSUME_TAC THENL
   [ASM_MESON_TAC[ATOP_HOMOMORPHISM_IN]; ALL_TAC] THEN
  MP_TAC(ISPECL [`GP:P group`; `GB:B group`; `GD:D group`; `dX2:P->B`; `jS:B->D`;
                 `group_div GB a ((iS:A->B) c1)`] ATOP_EXACT_IMAGE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[GROUP_DIV] THEN
    MP_TAC(ISPECL [`GB:B group`; `GD:D group`; `jS:B->D`] GROUP_HOMOMORPHISM_DIV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ASM_SIMP_TAC[th]) THEN
    MATCH_MP_TAC GROUP_DIV_REFL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:P` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?w':Q. w' IN group_carrier GQ /\ (e2:Q->P) w' = w` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [group_epimorphism] o
      check (fun th -> concl th = `group_epimorphism (GQ,GP) (e2:Q->P)`)) THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `w:P`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(dT2:Q->A) w' IN group_carrier GA` ASSUME_TAC THENL
   [ASM_MESON_TAC[ATOP_HOMOMORPHISM_IN]; ALL_TAC] THEN
  EXISTS_TAC `group_mul GA c1 ((dT2:Q->A) w')` THEN
  ASM_SIMP_TAC[GROUP_MUL] THEN
  SUBGOAL_THEN `(iS:A->B) (group_mul GA (c1:A) ((dT2:Q->A) (w':Q))) =
                group_mul GB (iS c1) (iS(dT2 w')) /\
                (iT:A->C) (group_mul GA c1 (dT2 w')) = group_mul GC (iT c1) (iT(dT2 w'))`
  (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[group_homomorphism]; ALL_TAC] THEN
  SUBGOAL_THEN `(iT:A->C) (dT2(w':Q)) = group_id GC` SUBST1_TAC THENL
   [MATCH_MP_TAC ATOP_EXACT_KERNEL THEN
    MAP_EVERY EXISTS_TAC [`GQ:Q group`; `GA:A group`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GROUP_MUL_RID] THEN
  SUBGOAL_THEN `(iS:A->B) (dT2(w':Q)) = group_div GB a (iS c1)` SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `w':Q` o
      check (fun th -> free_in `dX2:P->B` (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC ATOP_ABELIAN_MUL_DIV THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The absolute Mayer-Vietoris sequence (G6) from the library               *)
(* axioms (long exact sequences of the pairs (t, s INTER t) and (X, s),      *)
(* naturality of the boundary, excision of X - t).                           *)
(* ========================================================================= *)

let ATOP_SUBTOPOLOGY_INTER = prove
 (`!top s t:A->bool.
        subtopology (subtopology top t) (s INTER t) = subtopology top (s INTER t) /\
        subtopology (subtopology top s) (s INTER t) = subtopology top (s INTER t)`,
  REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN REPEAT GEN_TAC THEN
  CONJ_TAC THEN AP_TERM_TAC THEN SET_TAC[]);;

let ATOP_MV_FACTS = prove
 (`!top s t:A->bool.
        open_in top s /\ open_in top t /\ topspace top = s UNION t
        ==> (!q. group_isomorphism
                  (relative_homology_group(q,subtopology top t,s INTER t),
                   relative_homology_group(q,top,s))
                  (hom_induced q (subtopology top t,s INTER t) (top,s) (\x. x))) /\
            (!q. group_exactness
                  (homology_group(q,subtopology top t),
                   relative_homology_group(q,subtopology top t,s INTER t),
                   homology_group(q - &1,subtopology top (s INTER t)))
                  (hom_induced q (subtopology top t,{}) (subtopology top t,s INTER t) (\x. x),
                   hom_boundary q (subtopology top t,s INTER t))) /\
            (!q. group_exactness
                  (relative_homology_group(q,subtopology top t,s INTER t),
                   homology_group(q - &1,subtopology top (s INTER t)),
                   homology_group(q - &1,subtopology top t))
                  (hom_boundary q (subtopology top t,s INTER t),
                   hom_induced (q - &1) (subtopology top (s INTER t),{})
                                        (subtopology top t,{}) (\x. x))) /\
            (!q. group_exactness
                  (homology_group(q,subtopology top (s INTER t)),
                   homology_group(q,subtopology top t),
                   relative_homology_group(q,subtopology top t,s INTER t))
                  (hom_induced q (subtopology top (s INTER t),{}) (subtopology top t,{}) (\x. x),
                   hom_induced q (subtopology top t,{}) (subtopology top t,s INTER t) (\x. x))) /\
            (!q y. y IN group_carrier(relative_homology_group(q,subtopology top t,s INTER t))
                   ==> hom_boundary q (top,s)
                         (hom_induced q (subtopology top t,s INTER t) (top,s) (\x. x) y) =
                       hom_induced (q - &1) (subtopology top (s INTER t),{})
                                            (subtopology top s,{}) (\x. x)
                         (hom_boundary q (subtopology top t,s INTER t) y)) /\
            (!q y. hom_induced q (subtopology top t,s INTER t) (top,s) (\x. x)
                     (hom_induced q (subtopology top t,{}) (subtopology top t,s INTER t)
                                  (\x. x) y) =
                   hom_induced q (top,{}) (top,s) (\x. x)
                     (hom_induced q (subtopology top t,{}) (top,{}) (\x. x) y)) /\
            (!q c. hom_induced q (subtopology top s,{}) (top,{}) (\x. x)
                     (hom_induced q (subtopology top (s INTER t),{})
                                    (subtopology top s,{}) (\x. x) c) =
                   hom_induced q (subtopology top t,{}) (top,{}) (\x. x)
                     (hom_induced q (subtopology top (s INTER t),{})
                                    (subtopology top t,{}) (\x. x) c))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(s:A->bool) SUBSET topspace top /\ t SUBSET topspace top`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `q:int` THEN
    MP_TAC(ISPECL [`q:int`; `top:A topology`; `t:A->bool`; `s:A->bool`]
                  ATOP_EXCISION_MV) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `t INTER s:A->bool = s INTER t /\ t UNION s:A->bool = topspace top`
     (fun th -> REWRITE_TAC[th; SUBTOPOLOGY_TOPSPACE]) THEN
    ASM SET_TAC[];
    X_GEN_TAC `q:int` THEN
    MP_TAC(ISPECL [`q:int`; `subtopology top (t:A->bool)`; `s INTER t:A->bool`]
                  HOMOLOGY_EXACTNESS_AXIOM_1) THEN
    REWRITE_TAC[ATOP_SUBTOPOLOGY_INTER];
    X_GEN_TAC `q:int` THEN
    MP_TAC(ISPECL [`q:int`; `subtopology top (t:A->bool)`; `s INTER t:A->bool`]
                  HOMOLOGY_EXACTNESS_AXIOM_2) THEN
    REWRITE_TAC[ATOP_SUBTOPOLOGY_INTER];
    X_GEN_TAC `q:int` THEN
    MP_TAC(ISPECL [`q:int`; `subtopology top (t:A->bool)`; `s INTER t:A->bool`]
                  HOMOLOGY_EXACTNESS_AXIOM_3) THEN
    REWRITE_TAC[ATOP_SUBTOPOLOGY_INTER];
    MAP_EVERY X_GEN_TAC [`q:int`; `y:((num->real)->A)frag->bool`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`q:int`; `subtopology top (t:A->bool)`; `s INTER t:A->bool`;
                   `top:A topology`; `s:A->bool`; `\x:A. x`] NATURALITY_HOM_INDUCED) THEN
    REWRITE_TAC[ATOP_SUBTOPOLOGY_INTER; IMAGE_ID; INTER_SUBSET] THEN
    SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; CONTINUOUS_MAP_ID] THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM] THEN SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`q:int`; `y:((num->real)->A)frag->bool`] THEN
    MP_TAC(ISPECL [`q:int`; `subtopology top (t:A->bool)`; `{}:A->bool`;
                   `subtopology top (t:A->bool)`; `s INTER t:A->bool`;
                   `top:A topology`; `s:A->bool`] ATOP_HOM_INDUCED_INCLUSIONS) THEN
    MP_TAC(ISPECL [`q:int`; `subtopology top (t:A->bool)`; `{}:A->bool`;
                   `top:A topology`; `{}:A->bool`;
                   `top:A topology`; `s:A->bool`] ATOP_HOM_INDUCED_INCLUSIONS) THEN
    SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; CONTINUOUS_MAP_ID; EMPTY_SUBSET;
             INTER_SUBSET; SUBSET_REFL] THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM] THEN SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`q:int`; `c:((num->real)->A)frag->bool`] THEN
    MP_TAC(ISPECL [`q:int`; `subtopology top (s INTER t:A->bool)`; `{}:A->bool`;
                   `subtopology top (s:A->bool)`; `{}:A->bool`;
                   `top:A topology`; `{}:A->bool`] ATOP_HOM_INDUCED_INCLUSIONS) THEN
    MP_TAC(ISPECL [`q:int`; `subtopology top (s INTER t:A->bool)`; `{}:A->bool`;
                   `subtopology top (t:A->bool)`; `{}:A->bool`;
                   `top:A topology`; `{}:A->bool`] ATOP_HOM_INDUCED_INCLUSIONS) THEN
    SIMP_TAC[ATOP_CONTINUOUS_MAP_INCLUSION; INTER_SUBSET; SUBSET_REFL;
             CONTINUOUS_MAP_FROM_SUBTOPOLOGY; CONTINUOUS_MAP_ID] THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM] THEN SIMP_TAC[]]);;

(* G6: the Mayer-Vietoris sequence of an open cover.                         *)

let ATOP_MAYER_VIETORIS = prove
 (`ATOP_MAYER_VIETORIS_STATEMENT (:A)`,
  REWRITE_TAC[ATOP_MAYER_VIETORIS_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`p:int`; `top:A topology`; `s:A->bool`; `t:A->bool`] THEN
  DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP ATOP_MV_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "X") (CONJUNCTS_THEN2 (LABEL_TAC "L1")
    (CONJUNCTS_THEN2 (LABEL_TAC "L2") (CONJUNCTS_THEN2 (LABEL_TAC "L3")
    (CONJUNCTS_THEN2 (LABEL_TAC "N1") (CONJUNCTS_THEN2 (LABEL_TAC "N2")
      (LABEL_TAC "N3"))))))) THEN
  USE_THEN "X" (MP_TAC o SPEC `p:int`) THEN
  REWRITE_TAC[group_isomorphism] THEN
  DISCH_THEN(X_CHOOSE_TAC `e':(((num->real)->A)frag->bool)->((num->real)->A)frag->bool`) THEN
  EXISTS_TAC
   `hom_boundary p (subtopology top t,s INTER t) o
    (e':(((num->real)->A)frag->bool)->((num->real)->A)frag->bool) o
    hom_induced p (top,{}) (top,s) (\x:A. x)` THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL
     [`homology_group(p,subtopology top (s INTER t:A->bool))`;
      `homology_group(p,subtopology top (s:A->bool))`;
      `homology_group(p,subtopology top (t:A->bool))`;
      `homology_group(p,top:A topology)`;
      `relative_homology_group(p,top:A topology,s)`;
      `relative_homology_group(p,subtopology top t,s INTER t:A->bool)`;
      `relative_homology_group(p + &1,top:A topology,s)`;
      `relative_homology_group(p + &1,subtopology top t,s INTER t:A->bool)`;
      `hom_induced p (subtopology top (s INTER t),{}) (subtopology top s,{}) (\x:A. x)`;
      `hom_induced p (subtopology top (s INTER t),{}) (subtopology top t,{}) (\x:A. x)`;
      `hom_induced p (subtopology top s,{}) (top,{}) (\x:A. x)`;
      `hom_induced p (subtopology top t,{}) (top,{}) (\x:A. x)`;
      `hom_induced p (top,{}) (top,s) (\x:A. x)`;
      `hom_induced p (subtopology top t,{}) (subtopology top t,s INTER t) (\x:A. x)`;
      `hom_induced p (subtopology top t,s INTER t) (top,s) (\x:A. x)`;
      `hom_induced (p + &1) (subtopology top t,s INTER t) (top,s) (\x:A. x)`;
      `hom_boundary (p + &1) (top,s:A->bool)`;
      `hom_boundary (p + &1) (subtopology top t,s INTER t:A->bool)`]
     (INST_TYPE [`:Z`,`:A`] ATOP_MV_EXACT_1)) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[homology_group; ABELIAN_RELATIVE_HOMOLOGY_GROUP] THEN
    REWRITE_TAC[GSYM homology_group; GROUP_HOMOMORPHISM_HOM_INDUCED] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`p + &1:int`; `top:A topology`; `s:A->bool`]
                    HOMOLOGY_EXACTNESS_AXIOM_2) THEN
      REWRITE_TAC[INT_ARITH `(p + &1) - &1:int = p`];
      REWRITE_TAC[HOMOLOGY_EXACTNESS_AXIOM_3];
      USE_THEN "L3" (ACCEPT_TAC o SPEC `p:int`);
      USE_THEN "L2" (MP_TAC o SPEC `p + &1:int`) THEN
      REWRITE_TAC[INT_ARITH `(p + &1) - &1:int = p`];
      USE_THEN "X" (MP_TAC o SPEC `p:int`) THEN
      SIMP_TAC[GROUP_ISOMORPHISM_IMP_MONOMORPHISM];
      USE_THEN "X" (MP_TAC o SPEC `p + &1:int`) THEN
      SIMP_TAC[GROUP_ISOMORPHISM_IMP_EPIMORPHISM];
      USE_THEN "N2" (fun th -> REWRITE_TAC[th]);
      USE_THEN "N3" (fun th -> REWRITE_TAC[th]);
      USE_THEN "N1" (MP_TAC o SPEC `p + &1:int`) THEN
      REWRITE_TAC[INT_ARITH `(p + &1) - &1:int = p`]];
    MP_TAC(ISPECL
     [`homology_group(p,subtopology top (s:A->bool))`;
      `homology_group(p,subtopology top (t:A->bool))`;
      `homology_group(p,top:A topology)`;
      `relative_homology_group(p,top:A topology,s)`;
      `relative_homology_group(p,subtopology top t,s INTER t:A->bool)`;
      `homology_group(p - &1,subtopology top (s INTER t:A->bool))`;
      `hom_induced p (subtopology top s,{}) (top,{}) (\x:A. x)`;
      `hom_induced p (subtopology top t,{}) (top,{}) (\x:A. x)`;
      `hom_induced p (top,{}) (top,s) (\x:A. x)`;
      `hom_induced p (subtopology top t,{}) (subtopology top t,s INTER t) (\x:A. x)`;
      `hom_induced p (subtopology top t,s INTER t) (top,s) (\x:A. x)`;
      `e':(((num->real)->A)frag->bool)->((num->real)->A)frag->bool`;
      `hom_boundary p (subtopology top t,s INTER t:A->bool)`]
     ATOP_MV_EXACT_2) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[homology_group; ABELIAN_RELATIVE_HOMOLOGY_GROUP] THEN
    REWRITE_TAC[GSYM homology_group; GROUP_HOMOMORPHISM_HOM_INDUCED] THEN
    ASM_REWRITE_TAC[HOMOLOGY_EXACTNESS_AXIOM_3] THEN REPEAT CONJ_TAC THEN
    FIRST [USE_THEN "L1" (ACCEPT_TAC o SPEC `p:int`);
           USE_THEN "N2" (fun th -> REWRITE_TAC[th])];
    MP_TAC(ISPECL
     [`homology_group(p,top:A topology)`;
      `relative_homology_group(p,top:A topology,s)`;
      `homology_group(p - &1,subtopology top (s:A->bool))`;
      `relative_homology_group(p,subtopology top t,s INTER t:A->bool)`;
      `homology_group(p - &1,subtopology top (s INTER t:A->bool))`;
      `homology_group(p - &1,subtopology top (t:A->bool))`;
      `hom_induced p (top,{}) (top,s) (\x:A. x)`;
      `hom_boundary p (top,s:A->bool)`;
      `hom_induced p (subtopology top t,s INTER t) (top,s) (\x:A. x)`;
      `e':(((num->real)->A)frag->bool)->((num->real)->A)frag->bool`;
      `hom_boundary p (subtopology top t,s INTER t:A->bool)`;
      `hom_induced (p - &1) (subtopology top (s INTER t),{})
                            (subtopology top s,{}) (\x:A. x)`;
      `hom_induced (p - &1) (subtopology top (s INTER t),{})
                            (subtopology top t,{}) (\x:A. x)`]
     ATOP_MV_EXACT_3) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[HOMOLOGY_EXACTNESS_AXIOM_1; GROUP_HOMOMORPHISM_HOM_INDUCED] THEN
    REPEAT CONJ_TAC THEN
    FIRST [USE_THEN "L2" (ACCEPT_TAC o SPEC `p:int`);
           USE_THEN "N1" (ACCEPT_TAC o SPEC `p:int`);
           REWRITE_TAC[homology_group; GROUP_HOMOMORPHISM_HOM_INDUCED]]]);;

(* The same statements under library-style names, with the statement        *)
(* constants unfolded.                                                       *)

let HOMOLOGY_MAYER_VIETORIS = REWRITE_RULE[ATOP_MAYER_VIETORIS_STATEMENT] ATOP_MAYER_VIETORIS;;

let RELATIVE_HOMOLOGY_MAYER_VIETORIS = REWRITE_RULE[ATOP_RELATIVE_MV_STATEMENT] ATOP_RELATIVE_MV;;

