(* ========================================================================= *)
(* pc_top_fclass: local homology of a topological manifold over compact     *)
(* sets (Hatcher, Algebraic Topology, Lemma 3.27).                           *)
(*   M1 (ATOP_LOCAL_HOMOLOGY_COMPACT_STATEMENT): for compact K in an        *)
(*   n-manifold, H_p(M, M - K) is trivial for p > n, a class of             *)
(*   H_n(M, M - K) with zero restrictions to the points of K is zero, and a *)
(*   locally consistent family of local classes on K is the restriction of  *)
(*   one class.                                                              *)
(* Route as in Hatcher: chart-convex sets (G2 through the chart), finite    *)
(* unions of such (relative Mayer-Vietoris, G1), compact sets in a chart     *)
(* (a relative cycle has a compact boundary, so its class comes from a      *)
(* finite union of chart balls around K), arbitrary compact sets (finitely  *)
(* many chart pieces), and the existence part by gluing local classes.     *)
(* Depends on the library, pc_top_iface, pc_top_mv and pc_top_lochom.       *)
(*                                                                           *)
(* The property atop_lhc, its Mayer-Vietoris step, and the                  *)
(* chart cases.                                                              *)
(* ========================================================================= *)

needs "src/pc_top_iface.ml";;
needs "src/pc_top_mv.ml";;
needs "src/pc_top_lochom.ml";;

prioritize_real();;
type_invention_error := true;;

let atop_lhc = new_definition
 `atop_lhc n (top:A topology) k <=>
    (!p. &n < p ==> trivial_group(relative_homology_group(p,top,topspace top DIFF k))) /\
    (!a. a IN group_carrier(relative_homology_group(&n,top,topspace top DIFF k)) /\
         (!x. x IN k
              ==> hom_induced (&n) (top,topspace top DIFF k)
                              (top,topspace top DELETE x) (\x. x) a =
                  group_id(relative_homology_group(&n,top,topspace top DELETE x)))
         ==> a = group_id(relative_homology_group(&n,top,topspace top DIFF k)))`;;

let ATOP_RESTRICT_COMPOSE = prove
 (`!p top s t u (c:((num->real)->A)frag->bool).
        s SUBSET t /\ t SUBSET u
        ==> hom_induced p (top,t) (top,u) (\x. x) (hom_induced p (top,s) (top,t) (\x. x) c) =
            hom_induced p (top,s) (top,u) (\x. x) c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:int`; `top:A topology`; `s:A->bool`; `top:A topology`;
                 `t:A->bool`; `top:A topology`; `u:A->bool`]
                ATOP_HOM_INDUCED_INCLUSIONS) THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_ID] THEN
  DISCH_THEN(MP_TAC o C AP_THM `c:((num->real)->A)frag->bool`) THEN
  REWRITE_TAC[o_THM]);;

let ATOP_LHC_UNION = prove
 (`!n top a b:A->bool.
        closed_in top a /\ closed_in top b /\
        atop_lhc n top a /\ atop_lhc n top b /\ atop_lhc n top (a INTER b)
        ==> atop_lhc n top (a UNION b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[atop_lhc] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `open_in top (topspace top DIFF a:A->bool) /\ open_in top (topspace top DIFF b) /\
    (topspace top DIFF a) UNION (topspace top DIFF b) = topspace top DIFF (a INTER b) /\
    (topspace top DIFF a) INTER (topspace top DIFF b) = topspace top DIFF (a UNION b)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_TOPSPACE] THEN SET_TAC[]; ALL_TAC] THEN
  MP_TAC(GEN `p:int` (ISPECL [`p:int`; `top:A topology`; `topspace top DIFF a:A->bool`;
                 `topspace top DIFF b:A->bool`] ATOP_RELATIVE_MV_INJ)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "inj") THEN CONJ_TAC THENL
   [X_GEN_TAC `p:int` THEN DISCH_TAC THEN
    REWRITE_TAC[trivial_group] THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_SING] THEN
    X_GEN_TAC `c:((num->real)->A)frag->bool` THEN
    EQ_TAC THENL [ALL_TAC; DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GROUP_ID]] THEN
    DISCH_TAC THEN
    REMOVE_THEN "inj" (MP_TAC o SPEC `p:int`) THEN
    ANTS_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        free_in `a INTER b:A->bool` (concl th) && not(free_in `a UNION b:A->bool` (concl th)) &&
        (let v,bod = dest_forall(concl th) in type_of v = `:int`))) THEN
      ASM_INT_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN MATCH_MP_TAC ATOP_TRIVIAL_GROUP_ELEMENT THEN
    REWRITE_TAC[HOM_INDUCED] THEN ASM_SIMP_TAC[];
    X_GEN_TAC `c:((num->real)->A)frag->bool` THEN STRIP_TAC THEN
    REMOVE_THEN "inj" (MP_TAC o SPEC `&n:int`) THEN
    ANTS_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        free_in `a INTER b:A->bool` (concl th) && not(free_in `a UNION b:A->bool` (concl th)) &&
        (let v,bod = dest_forall(concl th) in type_of v = `:int`))) THEN
      INT_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[HOM_INDUCED] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) ATOP_RESTRICT_COMPOSE o lhand o snd) THEN
    (ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]);;

let ATOP_LHC_EMPTY = prove
 (`!n top:A topology. atop_lhc n top {}`,
  REWRITE_TAC[atop_lhc; DIFF_EMPTY; NOT_IN_EMPTY] THEN
  MESON_TAC[TRIVIAL_RELATIVE_HOMOLOGY_GROUP_TOPSPACE; ATOP_TRIVIAL_GROUP_ELEMENT]);;

let ATOP_LHC_CHART_CONVEX = prove
 (`!top u (h:A->real^N) g k.
        hausdorff_space top /\ locally_euclidean_space (:N) top /\ open_in top u /\
        homeomorphic_maps (subtopology top u,euclidean) (h,g) /\
        compact k /\ convex k
        ==> atop_lhc (dimindex(:N)) top (IMAGE g k)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `k:real^N->bool = {}` THEN ASM_REWRITE_TAC[IMAGE_CLAUSES; ATOP_LHC_EMPTY] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `c:real^N` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  MP_TAC(ISPECL [`top:A topology`; `u:A->bool`; `h:A->real^N`; `g:real^N->A`]
                ATOP_CHART_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(g:real^N->A) c IN IMAGE g k /\ g c IN topspace top` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!p. group_isomorphism
          (relative_homology_group(p,top,topspace top DIFF IMAGE (g:real^N->A) k),
           relative_homology_group(p,top,topspace top DELETE g c))
          (hom_induced p (top,topspace top DIFF IMAGE g k)
                         (top,topspace top DELETE g c) (\x. x))`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC ATOP_CHART_LOCAL_HOMOLOGY_ISO THEN
    MAP_EVERY EXISTS_TAC [`u:A->bool`; `h:A->real^N`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[atop_lhc] THEN CONJ_TAC THENL
   [X_GEN_TAC `p:int` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP GROUP_ISOMORPHISM_IMP_ISOMORPHIC o SPEC `p:int`) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP ISOMORPHIC_GROUP_TRIVIALITY th]) THEN
    MP_TAC(ISPECL [`top:A topology`; `(g:real^N->A) c`]
           (REWRITE_RULE[ATOP_MANIFOLD_LOCAL_HOMOLOGY_STATEMENT]
                        ATOP_MANIFOLD_LOCAL_HOMOLOGY)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    ASM_INT_ARITH_TAC;
    X_GEN_TAC `a:((num->real)->A)frag->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&(dimindex(:N)):int`) THEN
    DISCH_THEN(MP_TAC o MATCH_MP GROUP_ISOMORPHISM_IMP_MONOMORPHISM) THEN
    REWRITE_TAC[group_monomorphism] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    ASM_SIMP_TAC[GROUP_ID] THEN
    MATCH_MP_TAC(GSYM ATOP_GROUP_HOM_ID) THEN
    REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED]]);;

let ATOP_LHC_CHART_CONVEX_UNIONS = prove
 (`!top u (h:A->real^N) g l.
        hausdorff_space top /\ locally_euclidean_space (:N) top /\ open_in top u /\
        homeomorphic_maps (subtopology top u,euclidean) (h,g) /\
        FINITE l /\ (!c. c IN l ==> compact c /\ convex c)
        ==> atop_lhc (dimindex(:N)) top (IMAGE g (UNIONS l))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `u:A->bool`; `h:A->real^N`; `g:real^N->A`]
                ATOP_CHART_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s. compact s ==> closed_in top (IMAGE (g:real^N->A) s)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `euclidean:(real^N)topology` THEN ASM_REWRITE_TAC[COMPACT_IN_EUCLIDEAN];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m ll. FINITE ll /\ CARD ll <= m /\ (!c. c IN ll ==> compact c /\ convex c)
          ==> atop_lhc (dimindex(:N)) top (IMAGE (g:real^N->A) (UNIONS ll))`
   (fun th -> ASM_MESON_TAC[th; LE_REFL]) THEN
  INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN SUBGOAL_THEN `ll:(real^N->bool)->bool = {}` SUBST1_TAC THENL
     [UNDISCH_TAC `CARD(ll:(real^N->bool)->bool) <= 0` THEN
      ASM_SIMP_TAC[ARITH_RULE `n <= 0 <=> n = 0`; CARD_EQ_0];
      REWRITE_TAC[UNIONS_0; IMAGE_CLAUSES; ATOP_LHC_EMPTY]];
    ALL_TAC] THEN
  X_GEN_TAC `ll:(real^N->bool)->bool` THEN STRIP_TAC THEN
  ASM_CASES_TAC `ll:(real^N->bool)->bool = {}` THEN
  ASM_REWRITE_TAC[UNIONS_0; IMAGE_CLAUSES; ATOP_LHC_EMPTY] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `c:real^N->bool` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  SUBGOAL_THEN `ll = (c:real^N->bool) INSERT (ll DELETE c)` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[UNIONS_INSERT; IMAGE_UNION] THEN
  SUBGOAL_THEN `FINITE (ll DELETE (c:real^N->bool)) /\ CARD (ll DELETE c) <= m /\
                (!d. d IN ll DELETE c ==> compact d /\ convex d) /\
                compact c /\ convex c`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[FINITE_DELETE; CARD_DELETE; IN_DELETE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC ATOP_LHC_UNION THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC COMPACT_UNIONS THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC ATOP_LHC_CHART_CONVEX THEN
    MAP_EVERY EXISTS_TAC [`u:A->bool`; `h:A->real^N`] THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN
     `IMAGE (g:real^N->A) c INTER IMAGE g (UNIONS (ll DELETE c)) =
      IMAGE g (UNIONS (IMAGE (\d. c INTER d) (ll DELETE c)))`
    SUBST1_TAC THENL
     [SUBGOAL_THEN `!x y. (g:real^N->A) x = g y ==> x = y` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[GSYM(MATCH_MP IMAGE_INTER_INJ
        (ASSUME `!x y. (g:real^N->A) x = g y ==> x = y`))] THEN AP_TERM_TAC THEN
      REWRITE_TAC[INTER_UNIONS; SIMPLE_IMAGE];
      ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE; COMPACT_INTER; CONVEX_INTER] THEN
    TRANS_TAC LE_TRANS `CARD(ll DELETE (c:real^N->bool))` THEN
    ASM_SIMP_TAC[CARD_IMAGE_LE]]);;

let ATOP_RELCYCLE_BOUNDARY_SUPPORT = prove
 (`!p top (s:A->bool) z.
        singular_relcycle (p,top,s) z
        ==> ?c. compact_in top c /\ c SUBSET s /\
                !t. c SUBSET t ==> singular_relcycle (p,top,t) z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SINGULAR_RELCYCLE; SINGULAR_CHAIN_SUBTOPOLOGY] THEN
  STRIP_TAC THEN
  EXISTS_TAC `UNIONS (IMAGE (\f:(num->real)->A. IMAGE f (standard_simplex (p - 1)))
                            (frag_support (chain_boundary p z)))` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_UNIONS THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_FRAG_SUPPORT; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `f:(num->real)->A` THEN DISCH_TAC THEN
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology (product_topology (:num) (\i. euclideanreal))
                            (standard_simplex (p - 1))` THEN
    REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; SUBSET_REFL; COMPACT_IN_STANDARD_SIMPLEX] THEN
    UNDISCH_TAC `singular_chain (p - 1,top) (chain_boundary p (z:((num->real)->A)frag))` THEN
    REWRITE_TAC[singular_chain; SUBSET] THEN
    DISCH_THEN(MP_TAC o SPEC `f:(num->real)->A`) THEN
    ASM_SIMP_TAC[IN; singular_simplex];
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
    X_GEN_TAC `t:A->bool` THEN REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[]]);;

let ATOP_RELCLASS_APPROX = prove
 (`!q top u (h:A->real^N) g k a.
        hausdorff_space top /\ open_in top u /\
        homeomorphic_maps (subtopology top u,euclidean) (h,g) /\
        compact_in top k /\ k SUBSET u /\
        a IN group_carrier(relative_homology_group(&q,top,topspace top DIFF k))
        ==> ?f d a'.
             FINITE f /\ f SUBSET IMAGE h k /\ &0 < d /\
             k SUBSET IMAGE g (UNIONS (IMAGE (\c. cball(c,d)) f)) /\
             a' IN group_carrier(relative_homology_group
                     (&q,top,topspace top DIFF IMAGE g (UNIONS (IMAGE (\c. cball(c,d)) f)))) /\
             hom_induced (&q)
               (top,topspace top DIFF IMAGE g (UNIONS (IMAGE (\c. cball(c,d)) f)))
               (top,topspace top DIFF k) (\x. x) a' = a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `u:A->bool`; `h:A->real^N`; `g:real^N->A`]
                ATOP_CHART_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC
   `a IN group_carrier(relative_homology_group(&q,top,topspace top DIFF (k:A->bool)))` THEN
  REWRITE_TAC[RELATIVE_HOMOLOGY_GROUP; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:((num->real)->A)frag` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ATOP_RELCYCLE_BOUNDARY_SUPPORT) THEN
  DISCH_THEN(X_CHOOSE_THEN `c0:A->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `c0 SUBSET topspace (top:A topology)` ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN `open {v:real^N | ~((g:real^N->A) v IN c0)}` ASSUME_TAC THENL
   [REWRITE_TAC[OPEN_IN] THEN
    SUBGOAL_THEN
     `{v:real^N | ~((g:real^N->A) v IN c0)} =
      {v | v IN topspace euclidean /\ g v IN topspace top DIFF c0}`
    SUBST1_TAC THENL
     [REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV; IN_DIFF; EXTENSION; IN_ELIM_THM] THEN
      ASM SET_TAC[];
      MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC OPEN_IN_DIFF THEN
      ASM_MESON_TAC[OPEN_IN_TOPSPACE; COMPACT_IN_IMP_CLOSED_IN]];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (IMAGE (h:A->real^N) k)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM COMPACT_IN_EUCLIDEAN] THEN MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology top (u:A->bool)` THEN ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h:A->real^N) k SUBSET {v | ~((g:real^N->A) v IN c0)}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(g:real^N->A)(h x) = x` SUBST1_TAC THENL
     [ASM SET_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (h:A->real^N) k`;
                 `(:real^N) DIFF {v | ~((g:real^N->A) v IN c0)}`]
                SEPARATE_COMPACT_CLOSED) THEN
  ASM_REWRITE_TAC[GSYM OPEN_CLOSED] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `IMAGE (h:A->real^N) k` COMPACT_IMP_TOTALLY_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `d0 / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^N->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `kk = IMAGE (g:real^N->A) (UNIONS (IMAGE (\c. cball(c,d0 / &2)) f))` THEN
  SUBGOAL_THEN `(k:A->bool) SUBSET kk` ASSUME_TAC THENL
   [EXPAND_TAC "kk" THEN REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(h:A->real^N) x IN UNIONS(IMAGE (\x. ball(x,d0 / &2)) f)` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE; IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(h:A->real^N) x` THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `c:real^N` THEN
    ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `c0 SUBSET topspace top DIFF (kk:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "kk" THEN
    REWRITE_TAC[SUBSET; IN_DIFF; IN_IMAGE; IN_UNIONS; EXISTS_IN_IMAGE; NOT_EXISTS_THM] THEN
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `v:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `c:real^N` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`c:real^N`; `v:real^N`] o check (fun th ->
      is_forall(concl th) && free_in `d0:real` (concl th))) THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; IN_ELIM_THM; NOT_IMP] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(v:real^N) IN cball(c,d0 / &2)` THEN REWRITE_TAC[IN_CBALL] THEN
    UNDISCH_TAC `&0 < d0` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`f:real^N->bool`; `d0 / &2`;
    `homologous_rel (q,top,topspace top DIFF kk) (z:((num->real)->A)frag)`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `singular_relcycle (q,top,topspace top DIFF kk) (z:((num->real)->A)frag)`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REWRITE_TAC[RELATIVE_HOMOLOGY_GROUP; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    W(MP_TAC o PART_MATCH (lhand o rand) HOM_INDUCED_CHAIN_MAP o lhand o snd) THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_ID; IMAGE_ID] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_MESON_TAC[CHAIN_MAP_ID; SINGULAR_RELCYCLE]]);;

let ATOP_LHC_BALL_RESTRICT = prove
 (`!p top u (h:A->real^N) g c d kk b y.
        hausdorff_space top /\ open_in top u /\
        homeomorphic_maps (subtopology top u,euclidean) (h,g) /\
        IMAGE g (cball(c,d)) SUBSET kk /\ kk SUBSET topspace top /\ &0 <= d /\
        b IN group_carrier(relative_homology_group(p,top,topspace top DIFF kk)) /\
        hom_induced p (top,topspace top DIFF kk) (top,topspace top DELETE g c) (\x. x) b =
        group_id(relative_homology_group(p,top,topspace top DELETE g c)) /\
        y IN IMAGE g (cball(c,d))
        ==> hom_induced p (top,topspace top DIFF kk) (top,topspace top DELETE y) (\x. x) b =
            group_id(relative_homology_group(p,top,topspace top DELETE y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `bb = hom_induced p (top,topspace top DIFF kk)
                     (top,topspace top DIFF IMAGE (g:real^N->A) (cball(c,d))) (\x. x) b` THEN
  SUBGOAL_THEN `(g:real^N->A) c IN IMAGE g (cball(c,d))` ASSUME_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[CENTRE_IN_CBALL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN IMAGE (g:real^N->A) (cball(c,d))
        ==> hom_induced p (top,topspace top DIFF IMAGE g (cball(c,d)))
                          (top,topspace top DELETE z) (\x. x) bb =
            hom_induced p (top,topspace top DIFF kk) (top,topspace top DELETE z) (\x. x) b`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "bb" THEN MATCH_MP_TAC ATOP_RESTRICT_COMPOSE THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `bb = group_id(relative_homology_group
           (p,top,topspace top DIFF IMAGE (g:real^N->A) (cball(c,d))))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p:int`; `top:A topology`; `u:A->bool`; `h:A->real^N`; `g:real^N->A`;
                   `cball(c:real^N,d)`; `(g:real^N->A) c`] ATOP_CHART_LOCAL_HOMOLOGY_ISO) THEN
    ASM_REWRITE_TAC[COMPACT_CBALL; CONVEX_CBALL] THEN
    DISCH_THEN(MP_TAC o MATCH_MP GROUP_ISOMORPHISM_IMP_MONOMORPHISM) THEN
    REWRITE_TAC[group_monomorphism] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    REWRITE_TAC[GROUP_ID] THEN CONJ_TAC THENL
     [EXPAND_TAC "bb" THEN REWRITE_TAC[HOM_INDUCED]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC ATOP_GROUP_HOM_ID THEN
    REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:A`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC ATOP_GROUP_HOM_ID THEN
  REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED]);;

let ATOP_LHC_CHART_COMPACT = prove
 (`!top u (h:A->real^N) g k.
        hausdorff_space top /\ locally_euclidean_space (:N) top /\ open_in top u /\
        homeomorphic_maps (subtopology top u,euclidean) (h,g) /\
        compact_in top k /\ k SUBSET u
        ==> atop_lhc (dimindex(:N)) top k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `u:A->bool`; `h:A->real^N`; `g:real^N->A`]
                ATOP_CHART_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!f d. FINITE f /\ &0 < d
          ==> atop_lhc (dimindex(:N)) top
                (IMAGE (g:real^N->A) (UNIONS (IMAGE (\c. cball(c,d)) f)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC ATOP_LHC_CHART_CONVEX_UNIONS THEN
    MAP_EVERY EXISTS_TAC [`u:A->bool`; `h:A->real^N`] THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE; COMPACT_CBALL; CONVEX_CBALL];
    ALL_TAC] THEN
  REWRITE_TAC[atop_lhc] THEN CONJ_TAC THENL
   [X_GEN_TAC `p:int` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?q. (p:int) = &q` (X_CHOOSE_THEN `q:num` SUBST_ALL_TAC) THENL
     [REWRITE_TAC[INT_OF_NUM_EXISTS] THEN
      UNDISCH_TAC `&(dimindex(:N)):int < p` THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[trivial_group] THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_SING] THEN X_GEN_TAC `a:((num->real)->A)frag->bool` THEN
    EQ_TAC THENL [ALL_TAC; DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GROUP_ID]] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`q:num`; `top:A topology`; `u:A->bool`; `h:A->real^N`;
                   `g:real^N->A`; `k:A->bool`; `a:((num->real)->A)frag->bool`]
                  ATOP_RELCLASS_APPROX) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`f:real^N->bool`; `d:real`; `a':((num->real)->A)frag->bool`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN
     `a' = group_id(relative_homology_group(&q,top,
             topspace top DIFF IMAGE (g:real^N->A) (UNIONS (IMAGE (\c. cball(c,d)) f))))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC ATOP_TRIVIAL_GROUP_ELEMENT THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`f:real^N->bool`; `d:real`] o
        check (fun th -> is_forall(concl th) &&
                         type_of(fst(dest_forall(concl th))) = `:real^N->bool`)) THEN
      ASM_REWRITE_TAC[atop_lhc] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC ATOP_GROUP_HOM_ID THEN REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED]];
    X_GEN_TAC `a:((num->real)->A)frag->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`dimindex(:N)`; `top:A topology`; `u:A->bool`; `h:A->real^N`;
                   `g:real^N->A`; `k:A->bool`; `a:((num->real)->A)frag->bool`]
                  ATOP_RELCLASS_APPROX) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`f:real^N->bool`; `d:real`; `a':((num->real)->A)frag->bool`] THEN
    STRIP_TAC THEN
    ABBREV_TAC `kk = IMAGE (g:real^N->A) (UNIONS (IMAGE (\c. cball(c,d)) f))` THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `a:((num->real)->A)frag->bool`)) THEN
    SUBGOAL_THEN
     `a' = group_id(relative_homology_group(&(dimindex(:N)),top:A topology,
                                             topspace top DIFF kk))`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`f:real^N->bool`; `d:real`] o
        check (fun th -> is_forall(concl th) &&
                         type_of(fst(dest_forall(concl th))) = `:real^N->bool`)) THEN
      ASM_REWRITE_TAC[atop_lhc] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      SUBGOAL_THEN `?c. c IN f /\ (y:A) IN IMAGE g (cball(c:real^N,d))`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(y:A) IN kk` THEN EXPAND_TAC "kk" THEN
        REWRITE_TAC[IN_IMAGE; IN_UNIONS; EXISTS_IN_IMAGE] THEN MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `?x0:A. x0 IN k /\ (c:real^N) = (h:A->real^N) x0`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(f:real^N->bool) SUBSET IMAGE (h:A->real^N) k` THEN
        REWRITE_TAC[SUBSET; IN_IMAGE] THEN DISCH_THEN(MP_TAC o SPEC `c:real^N`) THEN
        ASM_REWRITE_TAC[] THEN MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(g:real^N->A) c = x0` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        MP_TAC(ASSUME `!x:A. x IN u ==> (g:real^N->A)((h:A->real^N) x) = x`) THEN
        DISCH_THEN MATCH_MP_TAC THEN
        UNDISCH_TAC `(k:A->bool) SUBSET u` THEN UNDISCH_TAC `(x0:A) IN k` THEN
        SET_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC ATOP_LHC_BALL_RESTRICT THEN
      MAP_EVERY EXISTS_TAC [`u:A->bool`; `h:A->real^N`; `g:real^N->A`;
                            `c:real^N`; `d:real`] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [EXPAND_TAC "kk" THEN MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
        X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN EXISTS_TAC `c:real^N` THEN
        ASM_REWRITE_TAC[];
        EXPAND_TAC "kk" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
        X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
        UNDISCH_TAC `(u:A->bool) SUBSET topspace top` THEN
        MP_TAC(ASSUME `!y:real^N. (g:real^N->A) y IN u`) THEN SET_TAC[];
        UNDISCH_TAC `&0 < d` THEN REAL_ARITH_TAC;
        MP_TAC(ISPECL [`&(dimindex(:N)):int`; `top:A topology`; `topspace top DIFF kk:A->bool`;
                       `topspace top DIFF k:A->bool`; `topspace top DELETE (x0:A)`;
                       `a':((num->real)->A)frag->bool`] ATOP_RESTRICT_COMPOSE) THEN
        ANTS_TAC THENL
         [UNDISCH_TAC `(k:A->bool) SUBSET kk` THEN UNDISCH_TAC `(x0:A) IN k` THEN SET_TAC[];
          DISCH_THEN(SUBST1_TAC o SYM)] THEN
        FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
          rhs(concl th) = `a:((num->real)->A)frag->bool`)) THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          free_in `a:((num->real)->A)frag->bool` (concl th))) THEN
        ASM_REWRITE_TAC[]];
      MATCH_MP_TAC ATOP_GROUP_HOM_ID THEN REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED]]]);;


(* ========================================================================= *)
(* Arbitrary compact sets (finitely many chart pieces), the existence part   *)
(* (gluing local classes), and M1.                                           *)
(* ========================================================================= *)

let ATOP_CHART_BALL_INSIDE = prove
 (`!top (w:A->bool) x.
        hausdorff_space top /\ locally_euclidean_space (:N) top /\
        open_in top w /\ x IN w
        ==> ?u (h:A->real^N) g r.
                open_in top u /\ homeomorphic_maps (subtopology top u,euclidean) (h,g) /\
                &0 < r /\ IMAGE g (cball(h x,r)) SUBSET w INTER u /\
                open_in top (IMAGE g (ball(h x,r))) /\ x IN IMAGE g (ball(h x,r))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o REWRITE_RULE[locally_euclidean_space]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:A->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  REWRITE_TAC[homeomorphic_space; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`h:A->real^N`; `g:real^N->A`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `u:A->bool`; `h:A->real^N`; `g:real^N->A`]
                ATOP_CHART_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open {v:real^N | (g:real^N->A) v IN w}` MP_TAC THENL
   [REWRITE_TAC[OPEN_IN] THEN
    SUBGOAL_THEN `{v:real^N | (g:real^N->A) v IN w} =
                  {v | v IN topspace euclidean /\ g v IN w}` SUBST1_TAC THENL
     [REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_CONTAINS_CBALL] THEN DISCH_THEN(MP_TAC o SPEC `(h:A->real^N) x`) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`u:A->bool`; `h:A->real^N`; `g:real^N->A`; `r:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `cball((h:A->real^N) x,r) SUBSET {v | (g:real^N->A) v IN w}` THEN
    MP_TAC(ASSUME `!y:real^N. (g:real^N->A) y IN u`) THEN SET_TAC[];
    MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `u:A->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ASSUME `homeomorphic_maps (subtopology top u,euclidean)
                                     (h:A->real^N,g)`) THEN
    REWRITE_TAC[HOMEOMORPHIC_MAPS_MAP] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`g:real^N->A`; `euclidean:(real^N)topology`;
                   `subtopology top (u:A->bool)`; `ball((h:A->real^N) x,r)`]
                  HOMEOMORPHIC_MAP_OPENNESS) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN; SUBSET_UNIV; GSYM OPEN_IN; OPEN_BALL];
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(h:A->real^N) x` THEN
    ASM_SIMP_TAC[CENTRE_IN_BALL]]);;

let ATOP_COMPACT_FINITE_PIECES = prove
 (`!top (k:A->bool) W.
        hausdorff_space top /\ locally_euclidean_space (:N) top /\ compact_in top k /\
        (!x. x IN k ==> open_in top (W x) /\ x IN W x)
        ==> ?f. FINITE f /\ UNIONS f = k /\
                !s. s IN f
                    ==> compact_in top s /\ s SUBSET k /\
                        ?x u (h:A->real^N) g.
                            x IN k /\ s SUBSET W x /\ open_in top u /\
                            homeomorphic_maps (subtopology top u,euclidean) (h,g) /\
                            s SUBSET u`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. ?u (h:A->real^N) g r.
          x IN k
          ==> open_in top u /\ homeomorphic_maps (subtopology top u,euclidean) (h,g) /\
              &0 < r /\ IMAGE g (cball(h x,r)) SUBSET W x INTER u /\
              open_in top (IMAGE g (ball(h x,r))) /\ x IN IMAGE g (ball(h x,r))`
  MP_TAC THENL
   [X_GEN_TAC `x:A` THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC ATOP_CHART_BALL_INSIDE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:A->A->bool`; `h:A->A->real^N`; `g:A->real^N->A`; `r:A->real`] THEN
  DISCH_TAC THEN
  MP_TAC(GEN_REWRITE_RULE I [compact_in] (ASSUME `compact_in top (k:A->bool)`)) THEN
  DISCH_THEN(MP_TAC o SPEC
    `IMAGE (\x. IMAGE ((g:A->real^N->A) x) (ball((h:A->A->real^N) x x,r x))) k` o
    CONJUNCT2) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_FINITE_SUBSET_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC
   `IMAGE (\x. k INTER IMAGE ((g:A->real^N->A) x) (cball((h:A->A->real^N) x x,r x))) t` THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN SET_TAC[];
      UNDISCH_TAC
       `k SUBSET UNIONS (IMAGE (\x. IMAGE ((g:A->real^N->A) x)
                                         (ball((h:A->A->real^N) x x,r x))) t)` THEN
      REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE; IN_INTER] THEN
      MESON_TAC[REWRITE_RULE[SUBSET] BALL_SUBSET_CBALL; IN_IMAGE]];
    ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:A) IN k` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o check (fun th -> is_forall(concl th) &&
    free_in `r:A->real` (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_INTER_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `euclidean:(real^N)topology` THEN
    REWRITE_TAC[COMPACT_IN_EUCLIDEAN; COMPACT_CBALL] THEN
    MP_TAC(ISPECL [`top:A topology`; `(u:A->A->bool) x`; `(h:A->A->real^N) x`;
                   `(g:A->real^N->A) x`] ATOP_CHART_FACTS) THEN
    ASM_SIMP_TAC[];
    SET_TAC[];
    MAP_EVERY EXISTS_TAC [`x:A`; `(u:A->A->bool) x`; `(h:A->A->real^N) x`;
                          `(g:A->real^N->A) x`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

let ATOP_LHC_COMPACT = prove
 (`!top k:A->bool.
        hausdorff_space top /\ locally_euclidean_space (:N) top /\ compact_in top k
        ==> atop_lhc (dimindex(:N)) top k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `k:A->bool`; `\x:A. topspace(top:A topology)`]
                ATOP_COMPACT_FINITE_PIECES) THEN
  ASM_REWRITE_TAC[OPEN_IN_TOPSPACE] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE; SUBSET]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `k:A->bool`)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall(concl th) &&
    type_of(fst(dest_forall(concl th))) = `:A->bool`)) THEN
  UNDISCH_TAC `FINITE (f:(A->bool)->bool)` THEN
  SPEC_TAC(`f:(A->bool)->bool`,`f:(A->bool)->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_0; ATOP_LHC_EMPTY; UNIONS_INSERT; FORALL_IN_INSERT] THEN
  MAP_EVERY X_GEN_TAC [`s:A->bool`; `f:(A->bool)->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC) THEN
  SUBGOAL_THEN `compact_in top (UNIONS f:A->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_UNIONS THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC ATOP_LHC_UNION THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[COMPACT_IN_IMP_CLOSED_IN];
    ASM_MESON_TAC[COMPACT_IN_IMP_CLOSED_IN];
    MATCH_MP_TAC ATOP_LHC_CHART_COMPACT THEN
    MAP_EVERY EXISTS_TAC [`u:A->bool`; `h:A->real^N`; `g:real^N->A`] THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC ATOP_LHC_CHART_COMPACT THEN
    MAP_EVERY EXISTS_TAC [`u:A->bool`; `h:A->real^N`; `g:real^N->A`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_INTER_CLOSED_IN THEN ASM_MESON_TAC[COMPACT_IN_IMP_CLOSED_IN];
      ASM SET_TAC[]]]);;

let ATOP_LH_SAME_RESTRICTIONS = prove
 (`!top k (a:((num->real)->A)frag->bool) b.
        hausdorff_space top /\ locally_euclidean_space (:N) top /\ compact_in top k /\
        a IN group_carrier(relative_homology_group
                             (&(dimindex(:N)),top,topspace top DIFF k)) /\
        b IN group_carrier(relative_homology_group
                             (&(dimindex(:N)),top,topspace top DIFF k)) /\
        (!x. x IN k
             ==> hom_induced (&(dimindex(:N))) (top,topspace top DIFF k)
                             (top,topspace top DELETE x) (\x. x) a =
                 hom_induced (&(dimindex(:N))) (top,topspace top DIFF k)
                             (top,topspace top DELETE x) (\x. x) b)
        ==> a = b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `k:A->bool`] ATOP_LHC_COMPACT) THEN
  ASM_REWRITE_TAC[atop_lhc] THEN
  DISCH_THEN(MP_TAC o SPEC
   `group_div (relative_homology_group(&(dimindex(:N)),top:A topology,topspace top DIFF k))
              (a:((num->real)->A)frag->bool) b` o CONJUNCT2) THEN
  ASM_SIMP_TAC[GROUP_DIV_EQ_ID; GROUP_DIV] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`relative_homology_group(&(dimindex(:N)),top:A topology,
                                          topspace top DIFF k)`;
                 `relative_homology_group(&(dimindex(:N)),top:A topology,
                                          topspace top DELETE (x:A))`;
                 `hom_induced (&(dimindex(:N))) (top:A topology,topspace top DIFF k)
                              (top,topspace top DELETE (x:A)) (\x. x)`]
                GROUP_HOMOMORPHISM_DIV) THEN
  REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED] THEN
  DISCH_THEN(fun th -> ASM_SIMP_TAC[th]) THEN
  ASM_SIMP_TAC[GROUP_DIV_REFL; HOM_INDUCED]);;

let ATOP_LH_EXISTENCE = prove
 (`!top k (mu:A->((num->real)->A)frag->bool).
        hausdorff_space top /\ locally_euclidean_space (:N) top /\ compact_in top k /\
        (!x. x IN k
             ==> ?w b. open_in top w /\ x IN w /\
                       b IN group_carrier(relative_homology_group
                              (&(dimindex(:N)),top,topspace top DIFF w)) /\
                       !y. y IN w INTER k
                           ==> hom_induced (&(dimindex(:N))) (top,topspace top DIFF w)
                                 (top,topspace top DELETE y) (\x. x) b = mu y)
        ==> ?a. a IN group_carrier(relative_homology_group
                       (&(dimindex(:N)),top,topspace top DIFF k)) /\
                !x. x IN k
                    ==> hom_induced (&(dimindex(:N))) (top,topspace top DIFF k)
                                    (top,topspace top DELETE x) (\x. x) a = mu x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`W:A->A->bool`; `B:A->((num->real)->A)frag->bool`] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `k:A->bool`; `W:A->A->bool`]
                ATOP_COMPACT_FINITE_PIECES) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `k:A->bool`)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall(concl th) &&
    type_of(fst(dest_forall(concl th))) = `:A->bool`)) THEN
  UNDISCH_TAC `FINITE (f:(A->bool)->bool)` THEN
  SPEC_TAC(`f:(A->bool)->bool`,`f:(A->bool)->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_0; UNIONS_INSERT; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  CONJ_TAC THENL [MESON_TAC[GROUP_ID]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:A->bool`; `f:(A->bool)->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a':((num->real)->A)frag->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `compact_in top (UNIONS f:A->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_UNIONS THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN k` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o check (fun th -> is_forall(concl th) &&
    free_in `B:A->((num->real)->A)frag->bool` (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC
   `as = hom_induced (&(dimindex(:N))) (top,topspace top DIFF W(x:A))
                     (top,topspace top DIFF s) (\x. x)
                     ((B:A->((num->real)->A)frag->bool) x)` THEN
  SUBGOAL_THEN
   `as IN group_carrier(relative_homology_group
            (&(dimindex(:N)),top,topspace top DIFF (s:A->bool))) /\
    !y. y IN s
        ==> hom_induced (&(dimindex(:N))) (top,topspace top DIFF s)
                        (top,topspace top DELETE y) (\x. x) as = mu y`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "as" THEN REWRITE_TAC[HOM_INDUCED] THEN X_GEN_TAC `y:A` THEN
    DISCH_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) ATOP_RESTRICT_COMPOSE o lhand o snd) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`&(dimindex(:N)):int`; `top:A topology`; `topspace top DIFF s:A->bool`;
                 `topspace top DIFF UNIONS f:A->bool`] ATOP_RELATIVE_MV_GLUE) THEN
  ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_TOPSPACE; COMPACT_IN_IMP_CLOSED_IN] THEN
  DISCH_THEN(MP_TAC o SPECL [`as:((num->real)->A)frag->bool`;
                              `a':((num->real)->A)frag->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(topspace top DIFF s) UNION (topspace top DIFF UNIONS f) =
    topspace top DIFF (s INTER UNIONS f:A->bool) /\
    (topspace top DIFF s) INTER (topspace top DIFF UNIONS f) =
    topspace top DIFF (s UNION UNIONS f:A->bool)`
  (fun th -> REWRITE_TAC[th]) THENL [SET_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC ATOP_LH_SAME_RESTRICTIONS THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `s INTER UNIONS f:A->bool`] THEN
    ASM_REWRITE_TAC[HOM_INDUCED] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_INTER_CLOSED_IN THEN ASM_SIMP_TAC[COMPACT_IN_IMP_CLOSED_IN];
      ALL_TAC] THEN
    X_GEN_TAC `y:A` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`&(dimindex(:N)):int`; `top:A topology`; `topspace top DIFF s:A->bool`;
                   `topspace top DIFF (s INTER UNIONS f):A->bool`;
                   `topspace top DELETE (y:A)`;
                   `as:((num->real)->A)frag->bool`] ATOP_RESTRICT_COMPOSE) THEN
    MP_TAC(ISPECL [`&(dimindex(:N)):int`; `top:A topology`;
                   `topspace top DIFF UNIONS f:A->bool`;
                   `topspace top DIFF (s INTER UNIONS f):A->bool`;
                   `topspace top DELETE (y:A)`;
                   `a':((num->real)->A)frag->bool`] ATOP_RESTRICT_COMPOSE) THEN
    REPEAT(ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:((num->real)->A)frag->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `c:((num->real)->A)frag->bool` THEN ASM_REWRITE_TAC[IN_UNION] THEN
  X_GEN_TAC `y:A` THEN STRIP_TAC THENL
   [MP_TAC(ISPECL [`&(dimindex(:N)):int`; `top:A topology`;
                   `topspace top DIFF (s UNION UNIONS f:A->bool)`;
                   `topspace top DIFF s:A->bool`; `topspace top DELETE (y:A)`;
                   `c:((num->real)->A)frag->bool`] ATOP_RESTRICT_COMPOSE);
    MP_TAC(ISPECL [`&(dimindex(:N)):int`; `top:A topology`;
                   `topspace top DIFF (s UNION UNIONS f:A->bool)`;
                   `topspace top DIFF UNIONS f:A->bool`; `topspace top DELETE (y:A)`;
                   `c:((num->real)->A)frag->bool`] ATOP_RESTRICT_COMPOSE)] THEN
  (ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)]) THEN
  ASM_SIMP_TAC[]);;

let ATOP_LOCAL_HOMOLOGY_COMPACT = prove
 (`ATOP_LOCAL_HOMOLOGY_COMPACT_STATEMENT (:A) (:N)`,
  REWRITE_TAC[ATOP_LOCAL_HOMOLOGY_COMPACT_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `k:A->bool`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `k:A->bool`] ATOP_LHC_COMPACT) THEN
  ASM_REWRITE_TAC[atop_lhc] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `mu:A->((num->real)->A)frag->bool` THEN DISCH_TAC THEN
  MATCH_MP_TAC ATOP_LH_EXISTENCE THEN ASM_REWRITE_TAC[]);;


