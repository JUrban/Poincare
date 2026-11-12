(* ========================================================================= *)
(* pc_top_orient: simply connected topological manifolds are orientable    *)
(* (Hatcher, Algebraic Topology, Section 3.3: the orientable double cover   *)
(* and Proposition 3.25).                                                    *)
(*   M4 (ATOP_SC_ORIENTABLE_STATEMENT): a Hausdorff, locally Euclidean and  *)
(*   simply connected space has a homology orientation in dimension         *)
(*   dimindex(:N) (integer coefficients).                                    *)
(* Route: the points of the orientation cover are pairs (x,a) with a a      *)
(* generator of H_n(M,M-x); its topology has as basis the sheets of the     *)
(* classes b of H_n(M,M-w), w open, whose restrictions to the points of w   *)
(* are generators. FST is a two-sheeted covering map: around each point    *)
(* there are an open v and a compact k containing v with every restriction  *)
(* H_p(M,M-k) -> H_p(M,M-y), y in k, an isomorphism (from M1), and the two  *)
(* generators of H_n(M,M-k) give the two sheets over v. A continuous        *)
(* section (COVERING_MAP_SECTION of pc_top_cover) is an orientation.        *)
(* Depends on the library, pc_top_iface, pc_top_cover, pc_top_lochom and    *)
(* pc_top_fclass.                                                            *)
(*                                                                           *)
(* Generators of infinite cyclic groups, small isomorphism                  *)
(* neighbourhoods and openness of agreement sets of local classes.          *)
(* ========================================================================= *)

needs "src/pc_top_iface.ml";;
needs "src/pc_top_cover.ml";;
needs "src/pc_top_lochom.ml";;
needs "src/pc_top_fclass.ml";;

prioritize_real();;
type_invention_error := true;;

let ATOP_GENERATOR_ISOMORPHISM = prove
 (`!G H (f:A->B) a.
        group_isomorphism (G,H) f /\ a IN group_carrier G
        ==> (subgroup_generated H {f a} = H <=> subgroup_generated G {a} = G)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBGROUP_GENERATED_EQ] THEN
  MP_TAC(ISPECL [`G:A group`; `H:B group`; `f:A->B`; `{a:A}`]
                SUBGROUP_GENERATED_BY_HOMOMORPHIC_IMAGE) THEN
  ASM_SIMP_TAC[GROUP_ISOMORPHISM_IMP_HOMOMORPHISM; SING_SUBSET; IMAGE_CLAUSES] THEN
  DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [GROUP_ISOMORPHISM]) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    is_comb(lhs(concl th)) && fst(dest_const(fst(strip_comb(lhs(concl th))))) = "IMAGE")) THEN
  MP_TAC(ISPECL [`G:A group`; `{a:A}`] GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET) THEN
  DISCH_TAC THEN EQ_TAC THENL [DISCH_TAC; DISCH_THEN SUBST1_TAC THEN REFL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(f:A->B) x IN IMAGE f (group_carrier(subgroup_generated G {a}))`
  MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `x:A = y` (fun th -> ASM_REWRITE_TAC[th]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(y:A) IN group_carrier(subgroup_generated G {a})` THEN
  UNDISCH_TAC `group_carrier(subgroup_generated G {a:A}) SUBSET group_carrier G` THEN
  SET_TAC[]);;

let ATOP_INTEGER_GROUP_GENERATORS = prove
 (`!a. subgroup_generated integer_group {a} = integer_group <=> a = &1 \/ a = -- &1`,
  GEN_TAC THEN REWRITE_TAC[SUBGROUP_GENERATED_EQ] THEN
  SIMP_TAC[CARRIER_SUBGROUP_GENERATED_BY_SING; INTEGER_GROUP; IN_UNIV;
           GROUP_ZPOW_INTEGER_GROUP] THEN
  GEN_REWRITE_TAC LAND_CONV [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
  EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC `&1:int`) THEN REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:int` (MP_TAC o SYM)) THEN
    REWRITE_TAC[INT_MUL_EQ_1] THEN INT_ARITH_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:int` THEN
    REWRITE_TAC[] THENL
     [EXISTS_TAC `x:int` THEN INT_ARITH_TAC;
      EXISTS_TAC `--x:int` THEN INT_ARITH_TAC]]);;

let ATOP_INFINITE_CYCLIC_GENERATORS = prove
 (`!G:A group.
        G isomorphic_group integer_group
        ==> ?g. g IN group_carrier G /\ ~(group_inv G g = g) /\
                !a. a IN group_carrier G
                    ==> (subgroup_generated G {a} = G <=> a = g \/ a = group_inv G g)`,
  GEN_TAC THEN REWRITE_TAC[isomorphic_group; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `f:A->int` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GROUP_ISOMORPHISM]) THEN
  REWRITE_TAC[INTEGER_GROUP] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `?g:A. g IN group_carrier G /\ (f:A->int) g = &1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (f:A->int) (group_carrier G) = (:int)` THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:A->int)(group_inv G g) = -- &1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`G:A group`; `integer_group`; `f:A->int`] GROUP_HOMOMORPHISM_INV) THEN
    ASM_SIMP_TAC[INTEGER_GROUP];
    ALL_TAC] THEN
  EXISTS_TAC `g:A` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `(f:A->int)(group_inv G g) = -- &1` THEN ASM_REWRITE_TAC[] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `a:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`G:A group`; `integer_group`; `f:A->int`; `a:A`]
                ATOP_GENERATOR_ISOMORPHISM) THEN
  ASM_REWRITE_TAC[ATOP_INTEGER_GROUP_GENERATORS] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [DISJ1_TAC; DISJ2_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[GROUP_INV]);;

let ATOP_SMALL_ISO_NEIGHBOURHOOD = prove
 (`!top (w:A->bool) x.
        hausdorff_space top /\ locally_euclidean_space (:N) top /\
        open_in top w /\ x IN w
        ==> ?v k. open_in top v /\ x IN v /\ v SUBSET k /\ k SUBSET w /\
                  compact_in top k /\
                  !p y. y IN k
                        ==> group_isomorphism
                              (relative_homology_group(p,top,topspace top DIFF k),
                               relative_homology_group(p,top,topspace top DELETE y))
                              (hom_induced p (top,topspace top DIFF k)
                                             (top,topspace top DELETE y) (\x. x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `w:A->bool`; `x:A`] ATOP_CHART_BALL_INSIDE) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:A->bool`; `h:A->real^N`; `g:real^N->A`; `r:real`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `u:A->bool`; `h:A->real^N`; `g:real^N->A`]
                ATOP_CHART_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (g:real^N->A) (ball((h:A->real^N) x,r))`;
                        `IMAGE (g:real^N->A) (cball((h:A->real^N) x,r))`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[BALL_SUBSET_CBALL];
    ASM SET_TAC[];
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `euclidean:(real^N)topology` THEN
    ASM_REWRITE_TAC[COMPACT_IN_EUCLIDEAN; COMPACT_CBALL];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC ATOP_CHART_LOCAL_HOMOLOGY_ISO THEN
    MAP_EVERY EXISTS_TAC [`u:A->bool`; `h:A->real^N`] THEN
    ASM_REWRITE_TAC[COMPACT_CBALL; CONVEX_CBALL]]);;

let ATOP_AGREEMENT_OPEN = prove
 (`!top (w:A->bool) w' b b'.
        hausdorff_space top /\ locally_euclidean_space (:N) top /\
        open_in top w /\ open_in top w' /\
        b IN group_carrier(relative_homology_group(&(dimindex(:N)),top,topspace top DIFF w)) /\
        b' IN group_carrier(relative_homology_group(&(dimindex(:N)),top,topspace top DIFF w'))
        ==> open_in top
             {y | y IN w INTER w' /\
                  hom_induced (&(dimindex(:N))) (top,topspace top DIFF w)
                              (top,topspace top DELETE y) (\x. x) b =
                  hom_induced (&(dimindex(:N))) (top,topspace top DIFF w')
                              (top,topspace top DELETE y) (\x. x) b'}`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
  X_GEN_TAC `y:A` THEN REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `w INTER w':A->bool`; `y:A`]
                ATOP_SMALL_ISO_NEIGHBOURHOOD) THEN
  ASM_SIMP_TAC[OPEN_IN_INTER; IN_INTER; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`v:A->bool`; `k:A->bool`] THEN STRIP_TAC THEN
  EXISTS_TAC `v:A->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(k:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `hom_induced (&(dimindex(:N))) (top,topspace top DIFF w)
                (top,topspace top DIFF k) (\x. x) b =
    hom_induced (&(dimindex(:N))) (top,topspace top DIFF w')
                (top,topspace top DIFF k) (\x:A. x) b'`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`&(dimindex(:N)):int`; `y:A`]) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP GROUP_ISOMORPHISM_IMP_MONOMORPHISM) THEN
    REWRITE_TAC[group_monomorphism] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    REWRITE_TAC[HOM_INDUCED] THEN
    MP_TAC(ISPECL [`&(dimindex(:N)):int`; `top:A topology`; `topspace top DIFF w:A->bool`;
                   `topspace top DIFF k:A->bool`; `topspace top DELETE (y:A)`;
                   `b:((num->real)->A)frag->bool`] ATOP_RESTRICT_COMPOSE) THEN
    MP_TAC(ISPECL [`&(dimindex(:N)):int`; `top:A topology`; `topspace top DIFF w':A->bool`;
                   `topspace top DIFF k:A->bool`; `topspace top DELETE (y:A)`;
                   `b':((num->real)->A)frag->bool`] ATOP_RESTRICT_COMPOSE) THEN
    REPEAT(ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTER] THEN X_GEN_TAC `z:A` THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`&(dimindex(:N)):int`; `top:A topology`; `topspace top DIFF w:A->bool`;
                 `topspace top DIFF k:A->bool`; `topspace top DELETE (z:A)`;
                 `b:((num->real)->A)frag->bool`] ATOP_RESTRICT_COMPOSE) THEN
  MP_TAC(ISPECL [`&(dimindex(:N)):int`; `top:A topology`; `topspace top DIFF w':A->bool`;
                 `topspace top DIFF k:A->bool`; `topspace top DELETE (z:A)`;
                 `b':((num->real)->A)frag->bool`] ATOP_RESTRICT_COMPOSE) THEN
  REPEAT(ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)]) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The orientation cover as a topology from a basis of                      *)
(* sheets; intersections of basic sets, local sheets through a point.       *)
(* ------------------------------------------------------------------------- *)

let atop_ocover_sheet = new_definition
 `atop_ocover_sheet n (top:A topology) w b =
    IMAGE (\y. y,hom_induced (&n) (top,topspace top DIFF w)
                             (top,topspace top DELETE y) (\x. x) b) w`;;

let atop_ocover_basic = new_definition
 `atop_ocover_basic n (top:A topology) s <=>
    ?w b. open_in top w /\
          b IN group_carrier(relative_homology_group(&n,top,topspace top DIFF w)) /\
          (!y. y IN w
               ==> homology_local_orientation n top y
                     (hom_induced (&n) (top,topspace top DIFF w)
                                  (top,topspace top DELETE y) (\x. x) b)) /\
          s = atop_ocover_sheet n top w b`;;

let atop_ocover = new_definition
 `atop_ocover n (top:A topology) = topology (ARBITRARY UNION_OF atop_ocover_basic n top)`;;

let ATOP_IN_OCOVER_SHEET = prove
 (`!n (top:A topology) w b y c.
        (y,c) IN atop_ocover_sheet n top w b <=>
        y IN w /\
        c = hom_induced (&n) (top,topspace top DIFF w) (top,topspace top DELETE y)
                        (\x. x) b`,
  REWRITE_TAC[atop_ocover_sheet; IN_IMAGE; PAIR_EQ] THEN MESON_TAC[]);;

let ATOP_OCOVER_BASIC_INTER = prove
 (`!top s t:A#(((num->real)->A)frag->bool)->bool.
        hausdorff_space top /\ locally_euclidean_space (:N) top /\
        atop_ocover_basic (dimindex(:N)) top s /\ atop_ocover_basic (dimindex(:N)) top t
        ==> atop_ocover_basic (dimindex(:N)) top (s INTER t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[atop_ocover_basic] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `w:A->bool` (X_CHOOSE_THEN `b:((num->real)->A)frag->bool`
      STRIP_ASSUME_TAC))
   (X_CHOOSE_THEN `w':A->bool` (X_CHOOSE_THEN `b':((num->real)->A)frag->bool`
      STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC
   `aa = {y:A | y IN w INTER w' /\
                hom_induced (&(dimindex(:N))) (top,topspace top DIFF w)
                            (top,topspace top DELETE y) (\x. x) b =
                hom_induced (&(dimindex(:N))) (top,topspace top DIFF w')
                            (top,topspace top DELETE y) (\x. x) b'}` THEN
  SUBGOAL_THEN `open_in top (aa:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "aa" THEN MATCH_MP_TAC ATOP_AGREEMENT_OPEN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(aa:A->bool) SUBSET w /\ aa SUBSET topspace top` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(w:A->bool) SUBSET topspace top` MP_TAC THENL
     [ASM_SIMP_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
    EXPAND_TAC "aa" THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:A. y IN aa
          ==> (y IN w /\ y IN w' /\
               hom_induced (&(dimindex(:N))) (top,topspace top DIFF w)
                           (top,topspace top DELETE y) (\x. x) b =
               hom_induced (&(dimindex(:N))) (top,topspace top DIFF w')
                           (top,topspace top DELETE y) (\x. x) b') /\
              hom_induced (&(dimindex(:N))) (top,topspace top DIFF aa)
                (top,topspace top DELETE y) (\x. x)
                (hom_induced (&(dimindex(:N))) (top,topspace top DIFF w)
                   (top,topspace top DIFF aa) (\x:A. x) b) =
              hom_induced (&(dimindex(:N))) (top,topspace top DIFF w)
                (top,topspace top DELETE y) (\x. x) b`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `(y:A) IN aa` THEN EXPAND_TAC "aa" THEN
      REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN MESON_TAC[];
      MATCH_MP_TAC ATOP_RESTRICT_COMPOSE THEN
      UNDISCH_TAC `(y:A) IN aa` THEN UNDISCH_TAC `(aa:A->bool) SUBSET w` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`aa:A->bool`;
    `hom_induced (&(dimindex(:N))) (top,topspace top DIFF w)
                 (top,topspace top DIFF aa) (\x:A. x) b`] THEN
  ASM_REWRITE_TAC[HOM_INDUCED] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:A`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN NO_TAC) ;
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_INTER; ATOP_IN_OCOVER_SHEET] THEN
  MAP_EVERY X_GEN_TAC [`y:A`; `c:((num->real)->A)frag->bool`] THEN
  ASM_CASES_TAC `(y:A) IN aa` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `y:A`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `~((y:A) IN aa)` THEN EXPAND_TAC "aa" THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN MESON_TAC[]]);;

let ATOP_IN_GRAPH = prove
 (`!(f:A->B) v y c. (y,c) IN IMAGE (\y. y,f y) v <=> y IN v /\ c = f y`,
  REWRITE_TAC[IN_IMAGE; PAIR_EQ] THEN MESON_TAC[]);;

let ATOP_FST_IMAGE_GRAPH = prove
 (`!(f:A->B) v. IMAGE FST (IMAGE (\y. y,f y) v) = v`,
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; FST; IMAGE_ID]);;

let ATOP_OCOVER_OPEN_IN = prove
 (`!top:A topology.
        hausdorff_space top /\ locally_euclidean_space (:N) top
        ==> open_in (atop_ocover (dimindex(:N)) top) =
            ARBITRARY UNION_OF atop_ocover_basic (dimindex(:N)) top`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[atop_ocover] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 topology_tybij)] THEN
  MATCH_MP_TAC ISTOPOLOGY_BASE THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ATOP_OCOVER_BASIC_INTER THEN ASM_REWRITE_TAC[]);;

let ATOP_OCOVER_BASIC_OPEN = prove
 (`!top s:A#(((num->real)->A)frag->bool)->bool.
        hausdorff_space top /\ locally_euclidean_space (:N) top /\
        atop_ocover_basic (dimindex(:N)) top s
        ==> open_in (atop_ocover (dimindex(:N)) top) s`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ATOP_OCOVER_OPEN_IN] THEN
  MATCH_MP_TAC ARBITRARY_UNION_OF_INC THEN ASM_REWRITE_TAC[]);;

let ATOP_OCOVER_SHEET_BASIC = prove
 (`!n top v k (c:((num->real)->A)frag->bool).
        open_in top v /\ v SUBSET k /\
        (!y. y IN v
             ==> homology_local_orientation n top y
                   (hom_induced (&n) (top,topspace top DIFF k)
                                (top,topspace top DELETE y) (\x. x) c))
        ==> atop_ocover_basic n top
              (IMAGE (\y. y,hom_induced (&n) (top,topspace top DIFF k)
                                        (top,topspace top DELETE y) (\x. x) c) v)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[atop_ocover_basic; atop_ocover_sheet] THEN
  MAP_EVERY EXISTS_TAC
   [`v:A->bool`;
    `hom_induced (&n) (top,topspace top DIFF k)
                 (top,topspace top DIFF v) (\x:A. x) c`] THEN
  SUBGOAL_THEN
   `!y. y IN v
        ==> hom_induced (&n) (top,topspace top DIFF v)
              (top,topspace top DELETE y) (\x. x)
              (hom_induced (&n) (top,topspace top DIFF k)
                 (top,topspace top DIFF v) (\x:A. x) c) =
            hom_induced (&n) (top,topspace top DIFF k)
              (top,topspace top DELETE y) (\x. x) c`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC ATOP_RESTRICT_COMPOSE THEN
    UNDISCH_TAC `(y:A) IN v` THEN UNDISCH_TAC `(v:A->bool) SUBSET k` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[HOM_INDUCED] THEN
  MATCH_MP_TAC(SET_RULE
   `!f g:A->B. (!y. y IN v ==> f y = g y) ==> IMAGE f v = IMAGE g v`) THEN
  ASM_SIMP_TAC[]);;

let ATOP_OCOVER_LOCAL_SHEET = prove
 (`!n top u (x:A) a.
        hausdorff_space top /\ locally_euclidean_space (:N) top /\
        open_in top u /\ x IN u /\ homology_local_orientation n top x a
        ==> ?v k c. open_in top v /\ x IN v /\ v SUBSET k /\ k SUBSET u /\
                    compact_in top k /\
                    c IN group_carrier(relative_homology_group
                                        (&n,top,topspace top DIFF k)) /\
                    hom_induced (&n) (top,topspace top DIFF k)
                                (top,topspace top DELETE x) (\x. x) c = a /\
                    (!p y. y IN k
                           ==> group_isomorphism
                                 (relative_homology_group(p,top,topspace top DIFF k),
                                  relative_homology_group(p,top,topspace top DELETE y))
                                 (hom_induced p (top,topspace top DIFF k)
                                                (top,topspace top DELETE y) (\x. x))) /\
                    (!y. y IN k
                         ==> homology_local_orientation n top y
                               (hom_induced (&n) (top,topspace top DIFF k)
                                            (top,topspace top DELETE y) (\x. x) c))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `u:A->bool`; `x:A`] ATOP_SMALL_ISO_NEIGHBOURHOOD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:A->bool` (X_CHOOSE_THEN `k:A->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(x:A) IN k` ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homology_local_orientation]) THEN
  SUBGOAL_THEN
   `?c. c IN group_carrier(relative_homology_group(&n,top,topspace top DIFF k)) /\
        hom_induced (&n) (top,topspace top DIFF k) (top,topspace top DELETE x)
                    (\x:A. x) c = a`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `!f:B->B s t (a:B). IMAGE f s = t /\ a IN t ==> ?c. c IN s /\ f c = a`) THEN
    EXISTS_TAC
     `group_carrier(relative_homology_group(&n,top,topspace top DELETE (x:A)))` THEN
    ASM_REWRITE_TAC[ETA_AX] THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(x:A) IN k`) o SPECL [`&n:int`; `x:A`]) THEN
    SIMP_TAC[GROUP_ISOMORPHISM];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`v:A->bool`; `k:A->bool`; `c:((num->real)->A)frag->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o C MATCH_MP (ASSUME `(y:A) IN k`) o SPECL [`&n:int`; `y:A`]) THEN
  REWRITE_TAC[homology_local_orientation; HOM_INDUCED] THEN
  MP_TAC(ISPECL
   [`relative_homology_group(&n,top,topspace top DIFF (k:A->bool))`;
    `relative_homology_group(&n,top,topspace top DELETE (y:A))`;
    `hom_induced (&n) (top,topspace top DIFF k) (top,topspace top DELETE (y:A))
                 (\x:A. x)`;
    `c:((num->real)->A)frag->bool`] ATOP_GENERATOR_ISOMORPHISM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL
   [`relative_homology_group(&n,top,topspace top DIFF (k:A->bool))`;
    `relative_homology_group(&n,top,topspace top DELETE (x:A))`;
    `hom_induced (&n) (top,topspace top DIFF k) (top,topspace top DELETE (x:A))
                 (\x:A. x)`;
    `c:((num->real)->A)frag->bool`] ATOP_GENERATOR_ISOMORPHISM) THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The points of the cover, FST is continuous and open,                     *)
(* FST is a homeomorphism on each sheet, local orientations exist, and      *)
(* locally Euclidean spaces are locally path connected.                     *)
(* ------------------------------------------------------------------------- *)

let ATOP_OCOVER_TOPSPACE = prove
 (`!top:A topology.
        hausdorff_space top /\ locally_euclidean_space (:N) top
        ==> topspace(atop_ocover (dimindex(:N)) top) =
            {(x,a) | x IN topspace top /\
                     homology_local_orientation (dimindex(:N)) top x a}`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `a:((num->real)->A)frag->bool`] THEN EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPEC `atop_ocover (dimindex(:N)) (top:A topology)` OPEN_IN_TOPSPACE) THEN
    ASM_SIMP_TAC[ATOP_OCOVER_OPEN_IN; ARBITRARY_UNION_OF_ALT] THEN
    DISCH_THEN(MP_TAC o SPEC `x:A,(a:((num->real)->A)frag->bool)`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:A#(((num->real)->A)frag->bool)->bool`
      STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [atop_ocover_basic] o
                 GEN_REWRITE_RULE I [IN]) THEN
    DISCH_THEN(X_CHOOSE_THEN `w:A->bool` (X_CHOOSE_THEN
      `b:((num->real)->A)frag->bool` STRIP_ASSUME_TAC)) THEN
    UNDISCH_TAC `(x:A,(a:((num->real)->A)frag->bool)) IN t` THEN
    ASM_REWRITE_TAC[ATOP_IN_OCOVER_SHEET] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    STRIP_TAC THEN
    MP_TAC(ISPECL [`dimindex(:N)`; `top:A topology`; `topspace top:A->bool`; `x:A`;
                   `a:((num->real)->A)frag->bool`] ATOP_OCOVER_LOCAL_SHEET) THEN
    ASM_REWRITE_TAC[OPEN_IN_TOPSPACE] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:A->bool` (X_CHOOSE_THEN `k:A->bool`
      (X_CHOOSE_THEN `c:((num->real)->A)frag->bool` STRIP_ASSUME_TAC))) THEN
    MP_TAC(ISPECL [`dimindex(:N)`; `top:A topology`; `v:A->bool`; `k:A->bool`;
                   `c:((num->real)->A)frag->bool`] ATOP_OCOVER_SHEET_BASIC) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP ATOP_OCOVER_BASIC_OPEN o
               CONJ (ASSUME `hausdorff_space(top:A topology)`) o
               CONJ (ASSUME `locally_euclidean_space (:N) (top:A topology)`)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[ATOP_IN_GRAPH]]);;

let ATOP_OCOVER_IN_TOPSPACE = prove
 (`!top:A topology x a.
        hausdorff_space top /\ locally_euclidean_space (:N) top
        ==> ((x,a) IN topspace(atop_ocover (dimindex(:N)) top) <=>
             x IN topspace top /\ homology_local_orientation (dimindex(:N)) top x a)`,
  SIMP_TAC[ATOP_OCOVER_TOPSPACE; IN_ELIM_PAIR_THM]);;

let ATOP_OCOVER_FST_OPEN_MAP = prove
 (`!top:A topology.
        hausdorff_space top /\ locally_euclidean_space (:N) top
        ==> open_map (atop_ocover (dimindex(:N)) top,top) FST`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[open_map] THEN
  ASM_SIMP_TAC[ATOP_OCOVER_OPEN_IN; ARBITRARY_UNION_OF_ALT] THEN
  X_GEN_TAC `u:A#(((num->real)->A)frag->bool)->bool` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM; FST] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `a:((num->real)->A)frag->bool`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A,(a:((num->real)->A)frag->bool)`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:A#(((num->real)->A)frag->bool)->bool`
    STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [atop_ocover_basic] o
                 GEN_REWRITE_RULE I [IN]) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A->bool` (X_CHOOSE_THEN
    `b:((num->real)->A)frag->bool` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `w:A->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `(x:A,(a:((num->real)->A)frag->bool)) IN t` THEN
    ASM_REWRITE_TAC[ATOP_IN_OCOVER_SHEET] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE FST (t:A#(((num->real)->A)frag->bool)->bool)` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[atop_ocover_sheet; ATOP_FST_IMAGE_GRAPH; SUBSET_REFL];
      MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]]]);;

let ATOP_OCOVER_FST_CONTINUOUS = prove
 (`!top:A topology.
        hausdorff_space top /\ locally_euclidean_space (:N) top
        ==> continuous_map (atop_ocover (dimindex(:N)) top,top) FST`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[continuous_map; FORALL_PAIR_THM] THEN
  ASM_SIMP_TAC[ATOP_OCOVER_IN_TOPSPACE; FST] THEN
  X_GEN_TAC `u:A->bool` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `a:((num->real)->A)frag->bool`] THEN
  ASM_SIMP_TAC[ATOP_OCOVER_IN_TOPSPACE; FST] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`dimindex(:N)`; `top:A topology`; `u:A->bool`; `x:A`;
                 `a:((num->real)->A)frag->bool`] ATOP_OCOVER_LOCAL_SHEET) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:A->bool` (X_CHOOSE_THEN `k:A->bool`
    (X_CHOOSE_THEN `c:((num->real)->A)frag->bool` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC
   `IMAGE (\y. y,hom_induced (&(dimindex(:N))) (top,topspace top DIFF k)
                             (top,topspace top DELETE y) (\x:A. x) c) v` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ATOP_OCOVER_BASIC_OPEN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC ATOP_OCOVER_SHEET_BASIC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SUBSET];
    ASM_REWRITE_TAC[ATOP_IN_GRAPH];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[ATOP_OCOVER_IN_TOPSPACE; FST] THEN
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:A) IN k` ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]]);;

let ATOP_OCOVER_SHEET_HOMEOMORPHIC = prove
 (`!top v k (c:((num->real)->A)frag->bool).
        hausdorff_space top /\ locally_euclidean_space (:N) top /\
        open_in top v /\ v SUBSET k /\
        (!y. y IN v
             ==> homology_local_orientation (dimindex(:N)) top y
                   (hom_induced (&(dimindex(:N))) (top,topspace top DIFF k)
                                (top,topspace top DELETE y) (\x. x) c))
        ==> homeomorphic_map
             (subtopology (atop_ocover (dimindex(:N)) top)
                (IMAGE (\y. y,hom_induced (&(dimindex(:N))) (top,topspace top DIFF k)
                                          (top,topspace top DELETE y) (\x. x) c) v),
              subtopology top v) FST`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`dimindex(:N)`; `top:A topology`; `v:A->bool`; `k:A->bool`;
                 `c:((num->real)->A)frag->bool`] ATOP_OCOVER_SHEET_BASIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ATOP_OCOVER_BASIC_OPEN o
              CONJ (ASSUME `hausdorff_space(top:A topology)`) o
              CONJ (ASSUME `locally_euclidean_space (:N) (top:A topology)`)) THEN
  MP_TAC(ISPECL
   [`\y. hom_induced (&(dimindex(:N))) (top,topspace top DIFF k)
                     (top,topspace top DELETE y) (\x:A. x) c`; `v:A->bool`]
   ATOP_FST_IMAGE_GRAPH) THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!z1 z2. z1 IN IMAGE (\y. y,hom_induced (&(dimindex(:N))) (top,topspace top DIFF k)
                                 (top,topspace top DELETE y) (\x:A. x) c) v /\
            z2 IN IMAGE (\y. y,hom_induced (&(dimindex(:N))) (top,topspace top DIFF k)
                                 (top,topspace top DELETE y) (\x:A. x) c) v
            ==> (FST z1 = FST z2 <=> z1 = z2)`
  ASSUME_TAC THENL
   [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; FST; PAIR_EQ] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `S = IMAGE (\y. y,hom_induced (&(dimindex(:N))) (top,topspace top DIFF k)
                                 (top,topspace top DELETE y) (\x:A. x) c) v` THEN
  SUBGOAL_THEN `topspace(subtopology (atop_ocover (dimindex(:N)) (top:A topology))
                         (S:A#(((num->real)->A)frag->bool)->bool)) = S`
  ASSUME_TAC THENL
   [MATCH_MP_TAC TOPSPACE_SUBTOPOLOGY_SUBSET THEN ASM_SIMP_TAC[OPEN_IN_SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC BIJECTIVE_OPEN_IMP_HOMEOMORPHIC_MAP THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; SUBSET_REFL] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
    ASM_SIMP_TAC[ATOP_OCOVER_FST_CONTINUOUS];
    ASM_SIMP_TAC[OPEN_MAP_IN_SUBTOPOLOGY; SUBSET_REFL] THEN
    MATCH_MP_TAC OPEN_MAP_FROM_SUBTOPOLOGY THEN
    ASM_SIMP_TAC[ATOP_OCOVER_FST_OPEN_MAP];
    ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC TOPSPACE_SUBTOPOLOGY_SUBSET THEN ASM_SIMP_TAC[OPEN_IN_SUBSET];
    ASM_REWRITE_TAC[]]);;

let ATOP_LOCAL_ORIENTATION_EXISTS = prove
 (`!top:A topology x.
        hausdorff_space top /\ locally_euclidean_space (:N) top /\ x IN topspace top
        ==> ?a. homology_local_orientation (dimindex(:N)) top x a`,
  REPEAT STRIP_TAC THEN
  MP_TAC ATOP_MANIFOLD_LOCAL_HOMOLOGY THEN
  REWRITE_TAC[ATOP_MANIFOLD_LOCAL_HOMOLOGY_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `x:A`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP ATOP_INFINITE_CYCLIC_GENERATORS o CONJUNCT1 o CONJUNCT2) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:((num->real)->A)frag->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `g:((num->real)->A)frag->bool` THEN
  ASM_SIMP_TAC[homology_local_orientation]);;

let ATOP_LOCALLY_EUCLIDEAN_IMP_LOCALLY_PATH_CONNECTED = prove
 (`!top:A topology.
        locally_euclidean_space (:N) top ==> locally_path_connected_space top`,
  GEN_TAC THEN REWRITE_TAC[locally_euclidean_space] THEN DISCH_TAC THEN
  REWRITE_TAC[LOCALLY_PATH_CONNECTED_SPACE] THEN
  MAP_EVERY X_GEN_TAC [`v:A->bool`; `x:A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `locally_path_connected_space (subtopology top (u:A->bool))`
  MP_TAC THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP HOMEOMORPHIC_LOCALLY_PATH_CONNECTED_SPACE
                                       th]) THEN
    MP_TAC(ISPEC `(:real^N)` LOCALLY_PATH_CONNECTED_SPACE_SUBTOPOLOGY_EUCLIDEAN) THEN
    REWRITE_TAC[SUBTOPOLOGY_UNIV; LOCALLY_PATH_CONNECTED_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[LOCALLY_PATH_CONNECTED_SPACE] THEN
  DISCH_THEN(MP_TAC o SPECL [`u INTER v:A->bool`; `x:A`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_INTER] THEN MATCH_MP_TAC OPEN_IN_SUBTOPOLOGY_INTER_OPEN THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `w:A->bool` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `u:A->bool` THEN
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[PATH_CONNECTED_IN_SUBTOPOLOGY];
    ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Two sheets over small neighbourhoods, FST is a                           *)
(* covering map, a continuous section is an orientation, and M4.            *)
(* ------------------------------------------------------------------------- *)

let ATOP_OCOVER_TWO_SHEETS = prove
 (`!top:A topology y0.
        hausdorff_space top /\ locally_euclidean_space (:N) top /\ y0 IN topspace top
        ==> ?v. open_in top v /\ y0 IN v /\
                ?vs. UNIONS vs =
                     {z | z IN topspace(atop_ocover (dimindex(:N)) top) /\ FST z IN v} /\
                     (!U. U IN vs ==> open_in (atop_ocover (dimindex(:N)) top) U) /\
                     pairwise DISJOINT vs /\
                     (!U. U IN vs
                          ==> homeomorphic_map
                                (subtopology (atop_ocover (dimindex(:N)) top) U,
                                 subtopology top v) FST)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `topspace top:A->bool`; `y0:A`]
                ATOP_SMALL_ISO_NEIGHBOURHOOD) THEN
  ASM_REWRITE_TAC[OPEN_IN_TOPSPACE] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:A->bool` (X_CHOOSE_THEN `k:A->bool` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `v:A->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(y0:A) IN k` ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `relative_homology_group(&(dimindex(:N)),top,topspace top DIFF (k:A->bool))
    isomorphic_group integer_group`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL
     [`relative_homology_group(&(dimindex(:N)),top,topspace top DIFF (k:A->bool))`;
      `relative_homology_group(&(dimindex(:N)),top,topspace top DELETE (y0:A))`;
      `integer_group`] ISOMORPHIC_GROUP_TRANS) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[isomorphic_group] THEN
      EXISTS_TAC `hom_induced (&(dimindex(:N))) (top,topspace top DIFF k)
                              (top,topspace top DELETE (y0:A)) (\x:A. x)` THEN
      ASM_SIMP_TAC[];
      MP_TAC ATOP_MANIFOLD_LOCAL_HOMOLOGY THEN
      REWRITE_TAC[ATOP_MANIFOLD_LOCAL_HOMOLOGY_STATEMENT] THEN
      DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `y0:A`]) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP ATOP_INFINITE_CYCLIC_GENERATORS) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:((num->real)->A)frag->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!c y. c IN group_carrier
                 (relative_homology_group(&(dimindex(:N)),top,topspace top DIFF k)) /\
          y IN k
          ==> (homology_local_orientation (dimindex(:N)) top y
                 (hom_induced (&(dimindex(:N))) (top,topspace top DIFF k)
                              (top,topspace top DELETE y) (\x:A. x) c) <=>
               c = g \/
               c = group_inv(relative_homology_group
                               (&(dimindex(:N)),top,topspace top DIFF k)) g)`
  (LABEL_TAC "key") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[homology_local_orientation; HOM_INDUCED] THEN
    FIRST_ASSUM(ASSUME_TAC o C MATCH_MP (ASSUME `(y:A) IN k`) o
                SPECL [`&(dimindex(:N)):int`; `y:A`]) THEN
    MP_TAC(ISPECL
     [`relative_homology_group(&(dimindex(:N)),top,topspace top DIFF (k:A->bool))`;
      `relative_homology_group(&(dimindex(:N)),top,topspace top DELETE (y:A))`;
      `hom_induced (&(dimindex(:N))) (top,topspace top DIFF k)
                   (top,topspace top DELETE (y:A)) (\x:A. x)`;
      `c:((num->real)->A)frag->bool`] ATOP_GENERATOR_ISOMORPHISM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c. c = g \/
        c = group_inv(relative_homology_group
                        (&(dimindex(:N)),top,topspace top DIFF k)) g
        ==> c IN group_carrier
                   (relative_homology_group(&(dimindex(:N)),top,topspace top DIFF k)) /\
            !y. y IN v
                ==> homology_local_orientation (dimindex(:N)) top y
                      (hom_induced (&(dimindex(:N))) (top,topspace top DIFF k)
                                   (top,topspace top DELETE y) (\x:A. x) c)`
  (LABEL_TAC "ok") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `c IN group_carrier(relative_homology_group
                           (&(dimindex(:N)),top,topspace top DIFF (k:A->bool)))`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN ASM_SIMP_TAC[GROUP_INV];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:A) IN k` ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `DISJOINT
     (IMAGE (\y. y,hom_induced (&(dimindex(:N))) (top,topspace top DIFF k)
                               (top,topspace top DELETE y) (\x:A. x) g) v)
     (IMAGE (\y. y,hom_induced (&(dimindex(:N))) (top,topspace top DIFF k)
                               (top,topspace top DELETE y) (\x:A. x)
                    (group_inv(relative_homology_group
                                 (&(dimindex(:N)),top,topspace top DIFF k)) g)) v)`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_DISJOINT; EXISTS_PAIR_THM; FORALL_PAIR_THM; ATOP_IN_GRAPH;
                NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`y:A`; `a:((num->real)->A)frag->bool`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:A) IN k` ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(y:A) IN k`) o
                SPECL [`&(dimindex(:N)):int`; `y:A`]) THEN
    REWRITE_TAC[GROUP_ISOMORPHISM] THEN
    DISCH_THEN(MP_TAC o SPECL
     [`g:((num->real)->A)frag->bool`;
      `group_inv(relative_homology_group
                   (&(dimindex(:N)),top,topspace top DIFF (k:A->bool))) g`] o
      CONJUNCT2 o CONJUNCT2) THEN
    ASM_SIMP_TAC[GROUP_INV] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC
   `{IMAGE (\y. y,hom_induced (&(dimindex(:N))) (top,topspace top DIFF k)
                              (top,topspace top DELETE y) (\x:A. x) g) v,
     IMAGE (\y. y,hom_induced (&(dimindex(:N))) (top,topspace top DIFF k)
                              (top,topspace top DELETE y) (\x:A. x)
                   (group_inv(relative_homology_group
                                (&(dimindex(:N)),top,topspace top DIFF k)) g)) v}` THEN
  REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; PAIRWISE_INSERT; PAIRWISE_SING;
              IN_SING] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_2] THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_UNION; ATOP_IN_GRAPH; IN_ELIM_THM; FST] THEN
    ASM_SIMP_TAC[ATOP_OCOVER_IN_TOPSPACE] THEN
    MAP_EVERY X_GEN_TAC [`y:A`; `a:((num->real)->A)frag->bool`] THEN
    ASM_CASES_TAC `(y:A) IN v` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(y:A) IN k /\ y IN topspace top` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_SIMP_TAC[GROUP_INV];
      DISCH_TAC THEN
      SUBGOAL_THEN
       `?c. c IN group_carrier(relative_homology_group
                                (&(dimindex(:N)),top,topspace top DIFF k)) /\
            hom_induced (&(dimindex(:N))) (top,topspace top DIFF k)
                        (top,topspace top DELETE y) (\x:A. x) c = a`
      STRIP_ASSUME_TAC THENL
       [MATCH_MP_TAC(SET_RULE
         `!f:B->B s t (a:B). IMAGE f s = t /\ a IN t ==> ?c. c IN s /\ f c = a`) THEN
        EXISTS_TAC
         `group_carrier(relative_homology_group
                          (&(dimindex(:N)),top,topspace top DELETE (y:A)))` THEN
        REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
         [FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(y:A) IN k`) o
                      SPECL [`&(dimindex(:N)):int`; `y:A`]) THEN
          SIMP_TAC[GROUP_ISOMORPHISM];
          ASM_MESON_TAC[homology_local_orientation]];
        ALL_TAC] THEN
      USE_THEN "key" (MP_TAC o SPECL [`c:((num->real)->A)frag->bool`; `y:A`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_MESON_TAC[]];
    MATCH_MP_TAC ATOP_OCOVER_BASIC_OPEN THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      MATCH_MP_TAC ATOP_OCOVER_SHEET_BASIC THEN
      USE_THEN "ok" (MP_TAC o SPEC `g:((num->real)->A)frag->bool`) THEN
      REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC ATOP_OCOVER_BASIC_OPEN THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      MATCH_MP_TAC ATOP_OCOVER_SHEET_BASIC THEN
      USE_THEN "ok" (MP_TAC o SPEC
        `group_inv(relative_homology_group
                     (&(dimindex(:N)),top,topspace top DIFF (k:A->bool))) g`) THEN
      REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]];
    GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC (K ALL_TAC)) THEN
    ASM_MESON_TAC[DISJOINT_SYM];
    MATCH_MP_TAC ATOP_OCOVER_SHEET_HOMEOMORPHIC THEN
    USE_THEN "ok" (MP_TAC o SPEC `g:((num->real)->A)frag->bool`) THEN
    REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC ATOP_OCOVER_SHEET_HOMEOMORPHIC THEN
    USE_THEN "ok" (MP_TAC o SPEC
      `group_inv(relative_homology_group
                   (&(dimindex(:N)),top,topspace top DIFF (k:A->bool))) g`) THEN
    REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

let ATOP_OCOVER_COVERING_MAP = prove
 (`!top:A topology.
        hausdorff_space top /\ locally_euclidean_space (:N) top
        ==> covering_map (atop_ocover (dimindex(:N)) top,top) FST`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[covering_map] THEN
  ASM_SIMP_TAC[ATOP_OCOVER_FST_CONTINUOUS] THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:A` THEN
    REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM; FST] THEN
    ASM_SIMP_TAC[ATOP_OCOVER_IN_TOPSPACE] THEN
    EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `x:A`] ATOP_LOCAL_ORIENTATION_EXISTS) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    X_GEN_TAC `y0:A` THEN DISCH_TAC THEN
    MATCH_MP_TAC ATOP_OCOVER_TWO_SHEETS THEN ASM_REWRITE_TAC[]]);;

let ATOP_SECTION_ORIENTATION = prove
 (`!top:A topology s.
        hausdorff_space top /\ locally_euclidean_space (:N) top /\
        continuous_map (top,atop_ocover (dimindex(:N)) top) s /\
        (!y. y IN topspace top ==> FST(s y) = y)
        ==> homology_orientation (dimindex(:N)) top (\y. SND(s y))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!y. y IN topspace top
        ==> (y,SND((s:A->A#(((num->real)->A)frag->bool)) y)) IN
            topspace(atop_ocover (dimindex(:N)) top)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(y,SND((s:A->A#(((num->real)->A)frag->bool)) y)) = s y`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM PAIR] THEN ASM_SIMP_TAC[PAIR_EQ];
      FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [continuous_map]) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN topspace top
        ==> homology_local_orientation (dimindex(:N)) top x
              (SND((s:A->A#(((num->real)->A)frag->bool)) x))`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `x:A`;
                   `SND((s:A->A#(((num->real)->A)frag->bool)) x)`]
                  ATOP_OCOVER_IN_TOPSPACE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[homology_orientation] THEN ASM_SIMP_TAC[] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`dimindex(:N)`; `top:A topology`; `topspace top:A->bool`; `x:A`;
                 `SND((s:A->A#(((num->real)->A)frag->bool)) x)`]
                ATOP_OCOVER_LOCAL_SHEET) THEN
  ASM_SIMP_TAC[OPEN_IN_TOPSPACE] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:A->bool` (X_CHOOSE_THEN `k:A->bool`
    (X_CHOOSE_THEN `c:((num->real)->A)frag->bool` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`dimindex(:N)`; `top:A topology`; `v:A->bool`; `k:A->bool`;
                 `c:((num->real)->A)frag->bool`] ATOP_OCOVER_SHEET_BASIC) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ATOP_OCOVER_BASIC_OPEN o
              CONJ (ASSUME `hausdorff_space(top:A topology)`) o
              CONJ (ASSUME `locally_euclidean_space (:N) (top:A topology)`)) THEN
  ABBREV_TAC
   `S = IMAGE (\y. y,hom_induced (&(dimindex(:N))) (top,topspace top DIFF k)
                                 (top,topspace top DELETE y) (\x:A. x) c) v` THEN
  ABBREV_TAC
   `w = {y | y IN topspace top /\ (s:A->A#(((num->real)->A)frag->bool)) y IN S}` THEN
  SUBGOAL_THEN `open_in top (w:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
    EXISTS_TAC `atop_ocover (dimindex(:N)) (top:A topology)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN w
        ==> y IN v /\
            SND((s:A->A#(((num->real)->A)frag->bool)) y) =
            hom_induced (&(dimindex(:N))) (top,topspace top DIFF k)
                        (top,topspace top DELETE y) (\x:A. x) c`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:A` THEN
    REWRITE_TAC[SYM(ASSUME `{y | y IN topspace top /\
                   (s:A->A#(((num->real)->A)frag->bool)) y IN S} = w`)] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    UNDISCH_TAC `(s:A->A#(((num->real)->A)frag->bool)) y IN S` THEN
    SUBGOAL_THEN `(s:A->A#(((num->real)->A)frag->bool)) y = (y,SND(s y))`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM PAIR] THEN ASM_SIMP_TAC[PAIR_EQ]; ALL_TAC] THEN
    REWRITE_TAC[SYM(ASSUME
     `IMAGE (\y. y,hom_induced (&(dimindex(:N))) (top,topspace top DIFF k)
                               (top,topspace top DELETE y) (\x:A. x) c) v = S`)] THEN
    REWRITE_TAC[ATOP_IN_GRAPH];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN w` ASSUME_TAC THENL
   [REWRITE_TAC[SYM(ASSUME `{y | y IN topspace top /\
                   (s:A->A#(((num->real)->A)frag->bool)) y IN S} = w`)] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(s:A->A#(((num->real)->A)frag->bool)) x = (x,SND(s x))`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM PAIR] THEN ASM_SIMP_TAC[PAIR_EQ]; ALL_TAC] THEN
    REWRITE_TAC[SYM(ASSUME
     `IMAGE (\y. y,hom_induced (&(dimindex(:N))) (top,topspace top DIFF k)
                               (top,topspace top DELETE y) (\x:A. x) c) v = S`)] THEN
    ASM_REWRITE_TAC[ATOP_IN_GRAPH];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`w:A->bool`;
    `hom_induced (&(dimindex(:N))) (top,topspace top DIFF k)
                 (top,topspace top DIFF w) (\x:A. x) c`] THEN
  ASM_REWRITE_TAC[HOM_INDUCED] THEN
  SUBGOAL_THEN `(w:A->bool) SUBSET v` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(z:A) IN w`)) THEN SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(y:A) IN w`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC ATOP_RESTRICT_COMPOSE THEN
  MAP_EVERY UNDISCH_TAC
   [`(y:A) IN w`; `(w:A->bool) SUBSET v`; `(v:A->bool) SUBSET k`] THEN
  SET_TAC[]);;

let ATOP_SC_ORIENTABLE = prove
 (`ATOP_SC_ORIENTABLE_STATEMENT (:A) (:N)`,
  REWRITE_TAC[ATOP_SC_ORIENTABLE_STATEMENT] THEN
  X_GEN_TAC `top:A topology` THEN STRIP_TAC THEN
  REWRITE_TAC[homology_orientable] THEN
  ASM_CASES_TAC `topspace top:A->bool = {}` THENL
   [EXISTS_TAC `(\x. {}):A->((num->real)->A)frag->bool` THEN
    ASM_REWRITE_TAC[homology_orientation; NOT_IN_EMPTY];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `x0:A` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  MP_TAC(ISPECL [`top:A topology`; `x0:A`] ATOP_LOCAL_ORIENTATION_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `a0:((num->real)->A)frag->bool`) THEN
  MP_TAC(ISPECL [`atop_ocover (dimindex(:N)) (top:A topology)`; `top:A topology`;
                 `FST:A#(((num->real)->A)frag->bool)->A`;
                 `(x0:A,(a0:((num->real)->A)frag->bool))`] COVERING_MAP_SECTION) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[ATOP_OCOVER_COVERING_MAP; ATOP_OCOVER_IN_TOPSPACE] THEN
    MATCH_MP_TAC ATOP_LOCALLY_EUCLIDEAN_IMP_LOCALLY_PATH_CONNECTED THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:A->A#(((num->real)->A)frag->bool)` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\y:A. SND((s:A->A#(((num->real)->A)frag->bool)) y)` THEN
  MATCH_MP_TAC ATOP_SECTION_ORIENTATION THEN ASM_REWRITE_TAC[]);;

