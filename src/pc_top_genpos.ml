(* ========================================================================= *)
(* pc_top_genpos: general position for the pi_1 of a punctured manifold.   *)
(*   M5 (ATOP_PUNCTURED_SIMPLY_CONNECTED_STATEMENT): a simply connected      *)
(*   Hausdorff topological manifold of dimension at least 3 stays simply    *)
(*   connected after removing a point.                                       *)
(* Route: a map from a compact set of R^M into a sphere of R^N, M < N,       *)
(* extends to all of R^M (the library's cofinite extension one dimension     *)
(* up, with the exceptional points pushed off the copy of R^M); hence a map  *)
(* of a compact space embedded in R^M into a manifold can be changed inside *)
(* a chart ball so that it misses the centre (ATOP_PUSH_OFF_CHART).  Paths   *)
(* (M = 1) and path homotopies of loops (M = 2) in M are pushed off x.      *)
(* Depends on the library, pc_top_iface, pc_top_cover and pc_top_lochom.    *)
(*                                                                           *)
(* The extension and push-off lemmas.                                       *)
(* ========================================================================= *)

needs "src/pc_top_iface.ml";;
needs "src/pc_top_cover.ml";;
needs "src/pc_top_lochom.ml";;

prioritize_real();;
type_invention_error := true;;

let EXTEND_MAP_LOWDIM_TO_SPHERE = prove
 (`!f:real^M->real^N s a r.
        dimindex(:M) < dimindex(:N) /\ &0 <= r /\
        compact s /\ f continuous_on s /\ IMAGE f s SUBSET sphere(a,r)
        ==> ?g. g continuous_on (:real^M) /\
                IMAGE g (:real^M) SUBSET sphere(a,r) /\
                !x. x IN s ==> g x = f x`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `s' = IMAGE (\x:real^M. pastecart x (vec 0:real^1)) s` THEN
  SUBGOAL_THEN `compact(s':real^(M,1)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "s'" THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(f:real^M->real^N) o (fstcart:real^(M,1)finite_sum->real^M)`;
                 `s':real^(M,1)finite_sum->bool`;
                 `a:real^N`; `r:real`;
                 `{z:real^(M,1)finite_sum | ~(sndcart z = vec 0)}`]
                EXTEND_MAP_UNIV_TO_SPHERE_COFINITE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      EXPAND_TAC "s'" THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
      REWRITE_TAC[GSYM IMAGE_o; o_DEF; FSTCART_PASTECART; IMAGE_ID] THEN
      ASM_REWRITE_TAC[ETA_AX];
      EXPAND_TAC "s'" THEN REWRITE_TAC[GSYM IMAGE_o; o_DEF; FSTCART_PASTECART] THEN
      ASM_REWRITE_TAC[ETA_AX; IMAGE_ID];
      X_GEN_TAC `c:real^(M,1)finite_sum->bool` THEN STRIP_TAC THEN
      SUBGOAL_THEN `open(c:real^(M,1)finite_sum->bool)` ASSUME_TAC THENL
       [MATCH_MP_TAC OPEN_COMPONENTS THEN
        EXISTS_TAC `(:real^(M,1)finite_sum) DIFF s'` THEN
        ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED];
        ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_NONEMPTY) THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_TAC `z:real^(M,1)finite_sum`) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `z:real^(M,1)finite_sum` o
        REWRITE_RULE[OPEN_CONTAINS_BALL]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
      ASM_CASES_TAC `sndcart(z:real^(M,1)finite_sum) = vec 0` THENL
       [EXISTS_TAC `pastecart (fstcart(z:real^(M,1)finite_sum)) (lift(d / &2))` THEN
        REWRITE_TAC[SNDCART_PASTECART; GSYM LIFT_NUM; LIFT_EQ] THEN
        CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
        REWRITE_TAC[IN_BALL] THEN
        SUBGOAL_THEN
         `dist(z,pastecart (fstcart z) (lift(d / &2))) =
          dist(sndcart(z:real^(M,1)finite_sum),lift(d / &2))` SUBST1_TAC THENL
         [MESON_TAC[PASTECART_FST_SND; DIST_PASTECART_CANCEL]; ALL_TAC] THEN
        ASM_REWRITE_TAC[DIST_0; NORM_LIFT] THEN ASM_REAL_ARITH_TAC;
        EXISTS_TAC `z:real^(M,1)finite_sum` THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`k:real^(M,1)finite_sum->bool`; `g:real^(M,1)finite_sum->real^N`] THEN
  STRIP_TAC THEN
  EXISTS_TAC `(g:real^(M,1)finite_sum->real^N) o (\x:real^M. pastecart x (vec 0:real^1))` THEN
  SUBGOAL_THEN
   `!x:real^M. pastecart x (vec 0:real^1) IN (:real^(M,1)finite_sum) DIFF k`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^M` THEN REWRITE_TAC[IN_DIFF; IN_UNIV] THEN DISCH_TAC THEN
    UNDISCH_TAC `(k:real^(M,1)finite_sum->bool) SUBSET {z | ~(sndcart z = vec 0)}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `pastecart (x:real^M) (vec 0:real^1)`) THEN
    ASM_REWRITE_TAC[SNDCART_PASTECART];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      CONTINUOUS_ON_SUBSET) o check (fun th -> is_binary "continuous_on" (concl th))) THEN
    ASM SET_TAC[];
    REWRITE_TAC[IMAGE_o] THEN ASM SET_TAC[];
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (x:real^M) (vec 0:real^1)` o
      check (fun th -> is_forall(concl th) && free_in `s':real^(M,1)finite_sum->bool` (concl th))) THEN
    REWRITE_TAC[o_THM; FSTCART_PASTECART] THEN DISCH_THEN MATCH_MP_TAC THEN
    EXPAND_TAC "s'" THEN REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]]);;

let ATOP_INVERSE_CHART_FACTS = prove
 (`!top w (e:real^N->A).
        hausdorff_space top /\ open_in top w /\
        homeomorphic_map (euclidean,subtopology top w) e
        ==> ?g0. continuous_map (subtopology top w,euclidean) g0 /\
                 (!v. g0(e v) = v) /\ (!y. y IN w ==> e(g0 y) = y) /\
                 continuous_map (euclidean,subtopology top w) e /\
                 continuous_map (euclidean,top) e /\
                 (!v. e v IN w) /\ w SUBSET topspace top /\
                 (!u. open u ==> open_in top (IMAGE e u)) /\
                 (!s. compact s ==> compact_in top (IMAGE e s) /\
                                    closed_in top (IMAGE e s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(w:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `topspace(subtopology top w) = w:A->bool` ASSUME_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `g0:A->real^N` o GEN_REWRITE_RULE I [HOMEOMORPHIC_MAP_MAPS]) THEN
  EXISTS_TAC `g0:A->real^N` THEN
  MP_TAC(ASSUME `homeomorphic_maps (euclidean,subtopology top w) (e:real^N->A,g0)`) THEN
  REWRITE_TAC[homeomorphic_maps] THEN
  ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!v:real^N. (e:real^N->A) v IN w` ASSUME_TAC THENL
   [X_GEN_TAC `v:real^N` THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE o
      check (fun th -> concl th =
        `continuous_map (euclidean,subtopology top w) (e:real^N->A)`)) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (euclidean,top) (e:real^N->A)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_INTO_FULLTOPOLOGY THEN
    EXISTS_TAC `w:A->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `u:real^N->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `w:A->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`e:real^N->A`; `euclidean:(real^N)topology`;
                   `subtopology top (w:A->bool)`; `u:real^N->bool`]
                  HOMEOMORPHIC_MAP_OPENNESS) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN; SUBSET_UNIV; GSYM OPEN_IN];
    X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `euclidean:(real^N)topology` THEN
      ASM_REWRITE_TAC[COMPACT_IN_EUCLIDEAN];
      ASM_MESON_TAC[COMPACT_IN_IMP_CLOSED_IN]]]);;

let ATOP_PUSH_OFF_CHART = prove
 (`!X top (H:B->A) (iota:B->real^M) w (e:real^N->A).
     dimindex(:M) < dimindex(:N) /\
     compact_space X /\ continuous_map (X,euclidean) iota /\
     (!y z. y IN topspace X /\ z IN topspace X /\ iota y = iota z ==> y = z) /\
     hausdorff_space top /\ continuous_map (X,top) H /\
     open_in top w /\ homeomorphic_map (euclidean,subtopology top w) e
     ==> ?H'. continuous_map (X,top) H' /\
              (!z. z IN topspace X ==> ~(H' z = e(vec 0))) /\
              (!z. ~(z IN topspace X /\ H z IN IMAGE e (ball(vec 0,&1)))
                   ==> H' z = H z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `w:A->bool`; `e:real^N->A`]
                ATOP_INVERSE_CHART_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `g0:A->real^N` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC
   `c = {z | z IN topspace X /\
             (H:B->A) z IN IMAGE (e:real^N->A) (sphere(vec 0,&1))}` THEN
  SUBGOAL_THEN
   `!z:B. z IN c <=>
          z IN topspace X /\ (H:B->A) z IN IMAGE (e:real^N->A) (sphere(vec 0,&1))`
  (LABEL_TAC "cdef") THENL [EXPAND_TAC "c" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `closed_in X (c:B->bool) /\ c SUBSET topspace X` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAP_PREIMAGE THEN
    EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[COMPACT_SPHERE];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in X (c:B->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CLOSED_IN_COMPACT_SPACE]; ALL_TAC] THEN
  SUBGOAL_THEN `topspace(subtopology X c) = c:B->bool` ASSUME_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology X (c:B->bool)`;
                 `subtopology euclidean (IMAGE (iota:B->real^M) c)`;
                 `euclidean:(real^N)topology`; `iota:B->real^M`;
                 `(g0:A->real^N) o (H:B->A)`]
                QUOTIENT_MAP_LIFT_EXISTS) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_IMP_QUOTIENT_MAP THEN
      ASM_SIMP_TAC[COMPACT_SPACE_SUBTOPOLOGY; HAUSDORFF_SPACE_SUBTOPOLOGY;
                   HAUSDORFF_SPACE_EUCLIDEAN; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
      REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
      ASM_SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; SUBSET_REFL];
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `subtopology top (w:A->bool)` THEN
      ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
      ASM_SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:B` THEN
      USE_THEN "cdef" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[IN_IMAGE] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[o_THM] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; o_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `f0:real^M->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`f0:real^M->real^N`; `IMAGE (iota:B->real^M) c`;
                 `vec 0:real^N`; `&1`] EXTEND_MAP_LOWDIM_TO_SPHERE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POS] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM COMPACT_IN_EUCLIDEAN] THEN MATCH_MP_TAC IMAGE_COMPACT_IN THEN
      EXISTS_TAC `X:B topology` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[GSYM CONTINUOUS_MAP_EUCLIDEAN];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:B` THEN
      USE_THEN "cdef" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[IN_IMAGE] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[o_THM]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^M->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!z:B. z IN topspace X /\ (H:B->A) z IN IMAGE (e:real^N->A) (sphere(vec 0,&1))
          ==> e((g:real^M->real^N)((iota:B->real^M) z)) = H z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(g:real^M->real^N)((iota:B->real^M) z) = f0(iota z)` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        free_in `g:real^M->real^N` (concl th))) THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `z:B` THEN
      USE_THEN "cdef" (fun th -> ASM_REWRITE_TAC[th]);
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(H:B->A) z IN IMAGE (e:real^N->A) (sphere(vec 0,&1))` THEN
    REWRITE_TAC[IN_IMAGE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `closed_in X {z | z IN topspace X /\
                     (H:B->A) z IN IMAGE (e:real^N->A) (cball(vec 0,&1))} /\
    closed_in X {z | z IN topspace X /\
                     (H:B->A) z IN topspace top DIFF IMAGE (e:real^N->A) (ball(vec 0,&1))}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAP_PREIMAGE THEN
    EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[COMPACT_CBALL] THEN
    MATCH_MP_TAC CLOSED_IN_DIFF THEN ASM_SIMP_TAC[CLOSED_IN_TOPSPACE; OPEN_BALL];
    ALL_TAC] THEN
  EXISTS_TAC
   `\z. if z IN topspace X /\ (H:B->A) z IN IMAGE (e:real^N->A) (ball(vec 0,&1))
        then e((g:real^M->real^N)((iota:B->real^M) z)) else H z` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(INST_TYPE [`:bool`,`:K`] PASTING_LEMMA_CLOSED) THEN
    MAP_EVERY EXISTS_TAC
     [`\b. if b then (\z. (e:real^N->A)((g:real^M->real^N)((iota:B->real^M) z)))
           else (H:B->A)`;
      `\b. if b then {z | z IN topspace X /\
                          (H:B->A) z IN IMAGE (e:real^N->A) (cball(vec 0,&1))}
           else {z | z IN topspace X /\
                     H z IN topspace top DIFF IMAGE e (ball(vec 0,&1))}`;
      `{T,F}`] THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; FORALL_IN_INSERT; NOT_IN_EMPTY;
                EXISTS_IN_INSERT] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
      SUBGOAL_THEN
       `(\z. (e:real^N->A)((g:real^M->real^N)((iota:B->real^M) z))) = e o g o iota`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `euclidean:(real^N)topology` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `euclidean:(real^M)topology` THEN
      ASM_REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN_EUCLIDEAN];
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN ASM_REWRITE_TAC[];
      REPEAT GEN_TAC THEN MAP_EVERY BOOL_CASES_TAC [`i:bool`; `j:bool`] THEN
      REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_DIFF] THEN STRIP_TAC THEN
      (FIRST_X_ASSUM MATCH_MP_TAC ORELSE
       (CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC)) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(H:B->A) x IN IMAGE (e:real^N->A) (cball(vec 0,&1))` THEN
      UNDISCH_TAC `~((H:B->A) x IN IMAGE (e:real^N->A) (ball(vec 0,&1)))` THEN
      REWRITE_TAC[IN_IMAGE; IN_CBALL_0; IN_BALL_0; IN_SPHERE_0] THEN
      MESON_TAC[REAL_LE_LT];
      X_GEN_TAC `z:B` THEN DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM; IN_DIFF] THEN
      ASM_CASES_TAC `(H:B->A) z IN IMAGE (e:real^N->A) (ball(vec 0,&1))` THEN
      ASM_REWRITE_TAC[] THENL
       [UNDISCH_TAC `(H:B->A) z IN IMAGE (e:real^N->A) (ball(vec 0,&1))` THEN
        MESON_TAC[IMAGE_SUBSET; BALL_SUBSET_CBALL; SUBSET];
        MATCH_MP_TAC(TAUT `q ==> p \/ q`) THEN
        MP_TAC(ISPECL [`X:B topology`; `top:A topology`; `H:B->A`]
                      CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
        ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[]]];
    X_GEN_TAC `z:B` THEN DISCH_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THENL
     [DISCH_THEN(MP_TAC o AP_TERM `g0:A->real^N`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN
      UNDISCH_TAC `IMAGE (g:real^M->real^N) (:real^M) SUBSET sphere(vec 0,&1)` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV; IN_SPHERE_0] THEN
      DISCH_THEN(MP_TAC o SPEC `(iota:B->real^M) z`) THEN
      ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
      UNDISCH_TAC
       `~((z:B) IN topspace X /\ (H:B->A) z IN IMAGE (e:real^N->A) (ball(vec 0,&1)))` THEN
      ASM_REWRITE_TAC[CONTRAPOS_THM] THEN DISCH_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `vec 0:real^N` THEN ASM_REWRITE_TAC[CENTRE_IN_BALL; REAL_LT_01]];
    X_GEN_TAC `z:B` THEN DISCH_TAC THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Charts centred at a point avoiding a compact set, the push-off of paths   *)
(* and of null-homotopies of loops, and M5.                                  *)
(* ========================================================================= *)

let ATOP_CHART_AT_POINT_AVOIDING = prove
 (`!top (x:A) k.
        hausdorff_space top /\ locally_euclidean_space (:N) top /\
        x IN topspace top /\ compact_in top k /\ ~(x IN k)
        ==> ?w (e:real^N->A).
                open_in top w /\ homeomorphic_map (euclidean,subtopology top w) e /\
                e(vec 0) = x /\ DISJOINT k (IMAGE e (ball(vec 0,&1)))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o REWRITE_RULE[locally_euclidean_space]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:A->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  REWRITE_TAC[homeomorphic_space; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`h:A->real^N`; `g:real^N->A`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `u:A->bool`; `h:A->real^N`; `g:real^N->A`]
                ATOP_CHART_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `homeomorphic_map (euclidean,subtopology top u) (g:real^N->A)`
  ASSUME_TAC THENL
   [MP_TAC(ASSUME `homeomorphic_maps (subtopology top u,euclidean)
                                     (h:A->real^N,g)`) THEN
    SIMP_TAC[HOMEOMORPHIC_MAPS_MAP];
    ALL_TAC] THEN
  SUBGOAL_THEN `open {v:real^N | ~((g:real^N->A) v IN k)}` MP_TAC THENL
   [REWRITE_TAC[OPEN_IN] THEN
    SUBGOAL_THEN
     `{v:real^N | ~((g:real^N->A) v IN k)} =
      {v | v IN topspace euclidean /\ g v IN topspace top DIFF k}`
    SUBST1_TAC THENL
     [REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV; IN_DIFF; EXTENSION; IN_ELIM_THM] THEN
      ASM SET_TAC[];
      MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC OPEN_IN_DIFF THEN
      ASM_MESON_TAC[OPEN_IN_TOPSPACE; COMPACT_IN_IMP_CLOSED_IN]];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `(h:A->real^N) x`) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC
   [`u:A->bool`; `(g:real^N->A) o (\v. r % v + (h:A->real^N) x)`] THEN
  ASM_SIMP_TAC[o_THM; VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHIC_MAP_COMPOSE THEN
    EXISTS_TAC `euclidean:(real^N)topology` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS] THEN
    EXISTS_TAC `\y:real^N. inv r % (y - (h:A->real^N) x)` THEN
    REWRITE_TAC[homeomorphic_maps; CONTINUOUS_MAP_EUCLIDEAN_EUCLIDEAN;
                TOPSPACE_EUCLIDEAN; IN_UNIV] THEN
    ASM_SIMP_TAC[VECTOR_ARITH `(a + b) - b:real^N = a`; VECTOR_MUL_ASSOC;
                 REAL_MUL_LINV; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID;
                 VECTOR_SUB_ADD] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN REWRITE_TAC[CONTINUOUS_ON_ID];
      MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
      SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST]];
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE; o_THM] THEN
    X_GEN_TAC `y:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `y:A`)) THEN
    UNDISCH_TAC `ball((h:A->real^N) x,r) SUBSET {v | ~((g:real^N->A) v IN k)}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `r % v + (h:A->real^N) x`) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_BALL; dist; VECTOR_ARITH `c - (x + c):real^N = --x`; NORM_NEG;
                NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    ASM_SIMP_TAC[REAL_LT_LMUL_EQ] THEN
    UNDISCH_TAC `(v:real^N) IN ball(vec 0,&1)` THEN REWRITE_TAC[IN_BALL_0]]);;

let ATOP_PATH_AVOIDING_POINT = prove
 (`!top (x:A) (q:real->A).
        hausdorff_space top /\ locally_euclidean_space (:N) top /\
        2 <= dimindex(:N) /\ x IN topspace top /\ path_in top q /\
        ~(q(&0) = x) /\ ~(q(&1) = x)
        ==> ?q'. path_in (subtopology top (topspace top DELETE x)) q' /\
                 q'(&0) = q(&0) /\ q'(&1) = q(&1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(q:real->A)(&0) IN topspace top /\ q(&1) IN topspace top`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `path_in top (q:real->A)` THEN REWRITE_TAC[path_in] THEN
    DISCH_THEN(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; SUBSET; FORALL_IN_IMAGE] THEN
    DISCH_THEN(fun th -> CONJ_TAC THEN MATCH_MP_TAC th) THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`top:A topology`; `x:A`; `{(q:real->A)(&0), q(&1)}`]
               ATOP_CHART_AT_POINT_AVOIDING) THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ANTS_TAC THENL
   [MATCH_MP_TAC FINITE_IMP_COMPACT_IN THEN
    ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; INSERT_SUBSET; EMPTY_SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`w:A->bool`; `e:real^N->A`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology euclideanreal (real_interval[&0,&1])`; `top:A topology`;
                 `q:real->A`; `lift`; `w:A->bool`; `e:real^N->A`]
                ATOP_PUSH_OFF_CHART) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[DIMINDEX_1; LIFT_EQ] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[path_in]) THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      MATCH_MP_TAC COMPACT_SPACE_SUBTOPOLOGY THEN
      REWRITE_TAC[COMPACT_IN_EUCLIDEANREAL_INTERVAL];
      MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
      REWRITE_TAC[CONTINUOUS_MAP_LIFT];
      MESON_TAC[LIFT_EQ]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q':real->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `q':real->A` THEN
  SUBGOAL_THEN `~((q:real->A)(&0) IN IMAGE (e:real^N->A) (ball(vec 0,&1))) /\
                ~(q(&1) IN IMAGE e (ball(vec 0,&1)))` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[PATH_IN_SUBTOPOLOGY; path_in] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[IN_DELETE] THEN CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE o
      check (fun th -> concl th = `continuous_map
        (subtopology euclideanreal (real_interval[&0,&1]),top) (q':real->A)`)) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN ASM SET_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
      is_forall(concl th) && free_in `(e:real^N->A)(vec 0)` (concl th))) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY]]);;

let ATOP_CONTRACTIBLE_LOOP_AVOIDING_POINT = prove
 (`!top (x:A) (p:real->A).
        hausdorff_space top /\ locally_euclidean_space (:N) top /\
        3 <= dimindex(:N) /\ x IN topspace top /\
        path_in (subtopology top (topspace top DELETE x)) p /\
        homotopic_with (\r. r(&0) = p(&0) /\ r(&1) = p(&1))
          (subtopology euclideanreal (real_interval[&0,&1]),top) p (\t. p(&0))
        ==> homotopic_with (\r. r(&0) = p(&0) /\ r(&1) = p(&1))
              (subtopology euclideanreal (real_interval[&0,&1]),
               subtopology top (topspace top DELETE x)) p (\t. p(&0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC
   `homotopic_with (\r. r(&0) = p(&0) /\ r(&1) = p(&1))
      (subtopology euclideanreal (real_interval[&0,&1]),top) p (\t. (p:real->A)(&0))` THEN
  REWRITE_TAC[homotopic_with] THEN
  DISCH_THEN(X_CHOOSE_THEN `H:real#real->A` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `path_in (subtopology top (topspace top DELETE x)) (p:real->A)` THEN
  REWRITE_TAC[PATH_IN_SUBTOPOLOGY; path_in] THEN STRIP_TAC THEN
  ABBREV_TAC `k = IMAGE (p:real->A) (real_interval[&0,&1])` THEN
  SUBGOAL_THEN `compact_in top (k:A->bool) /\ ~((x:A) IN k)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_COMPACT_IN THEN
      EXISTS_TAC `subtopology euclideanreal (real_interval[&0,&1])` THEN
      ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; SUBSET_REFL;
                      COMPACT_IN_EUCLIDEANREAL_INTERVAL];
      REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[IN_DELETE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&0:real) IN real_interval[&0,&1] /\ (&1:real) IN real_interval[&0,&1]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t s. t IN real_interval[&0,&1] /\ s IN real_interval[&0,&1] /\
          (t = &0 \/ t = &1 \/ s = &0 \/ s = &1)
          ==> (H:real#real->A)(t,s) IN k`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    EXPAND_TAC "k" THEN REWRITE_TAC[IN_IMAGE] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [EXISTS_TAC `s:real` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `&0:real` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `&0:real` THEN ASM_SIMP_TAC[];
      EXISTS_TAC `&1:real` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`top:A topology`; `x:A`; `k:A->bool`] ATOP_CHART_AT_POINT_AVOIDING) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`w:A->bool`; `e:real^N->A`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                                (subtopology euclideanreal (real_interval[&0,&1]))`;
                 `top:A topology`; `H:real#real->A`;
                 `\z:real#real. vector[FST z; SND z]:real^2`;
                 `w:A->bool`; `e:real^N->A`]
                ATOP_PUSH_OFF_CHART) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[DIMINDEX_2] THEN REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      REWRITE_TAC[COMPACT_SPACE_PROD_TOPOLOGY] THEN DISJ2_TAC THEN
      REPEAT CONJ_TAC THEN MATCH_MP_TAC COMPACT_SPACE_SUBTOPOLOGY THEN
      REWRITE_TAC[COMPACT_IN_EUCLIDEANREAL_INTERVAL];
      REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE_REAL; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
      REWRITE_TAC[ETA_AX] THEN CONJ_TAC THEN
      MATCH_MP_TAC CONTINUOUS_MAP_INTO_FULLTOPOLOGY THEN
      EXISTS_TAC `real_interval[&0,&1]` THEN
      REWRITE_TAC[CONTINUOUS_MAP_FST; CONTINUOUS_MAP_SND];
      REWRITE_TAC[FORALL_PAIR_THM; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; PAIR_EQ] THEN
      MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `H':real#real->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!t s. ~((t,s) IN topspace (prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                                             (subtopology euclideanreal (real_interval[&0,&1]))) /\
            ~((H:real#real->A)(t,s) IN k)) ==> H'(t,s) = H(t,s)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; IN_CROSS; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY]
    THEN RULE_ASSUM_TAC(REWRITE_RULE[TOPSPACE_PROD_TOPOLOGY; IN_CROSS;
                                     TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY]) THEN
  SUBGOAL_THEN
   `!t s. (t IN real_interval[&0,&1] /\ s IN real_interval[&0,&1] /\
           (t = &0 \/ t = &1 \/ s = &0 \/ s = &1)) \/
          ~(t IN real_interval[&0,&1] /\ s IN real_interval[&0,&1])
          ==> (H':real#real->A)(t,s) = H(t,s)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[homotopic_with] THEN EXISTS_TAC `H':real#real->A` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_PROD_TOPOLOGY;
                TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; IN_DELETE] THEN
    X_GEN_TAC `z:real#real` THEN DISCH_TAC THEN CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE o
        check (fun th -> is_comb(concl th) &&
          free_in `H':real#real->A` (concl th) &&
          fst(dest_const(fst(strip_comb(concl th)))) = "continuous_map")) THEN
      REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
      ASM SET_TAC[];
      ASM_MESON_TAC[]];
    X_GEN_TAC `s:real` THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(H:real#real->A)(&0,s)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    X_GEN_TAC `s:real` THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(H:real#real->A)(&1,s)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(H':real#real->A)(t,&0) = H(t,&0) /\ H'(t,&1) = H(t,&1)`
    (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]]]);;

let ATOP_PUNCTURED_SIMPLY_CONNECTED = prove
 (`ATOP_PUNCTURED_SIMPLY_CONNECTED_STATEMENT (:A) (:N)`,
  REWRITE_TAC[ATOP_PUNCTURED_SIMPLY_CONNECTED_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `x:A`] THEN STRIP_TAC THEN
  REWRITE_TAC[SIMPLY_CONNECTED_SPACE_EQ_CONTRACTIBLE_PATH] THEN CONJ_TAC THENL
   [REWRITE_TAC[path_connected_space; TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_DELETE] THEN
    MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
    MP_TAC(ISPEC `top:A topology` TOPC_SIMPLY_CONNECTED_IMP_PATH_CONNECTED) THEN
    ASM_REWRITE_TAC[path_connected_space] THEN
    DISCH_THEN(MP_TAC o SPECL [`a:A`; `b:A`]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real->A` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPECL [`top:A topology`; `x:A`; `q:real->A`] ATOP_PATH_AVOIDING_POINT) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `q':real->A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `q':real->A` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `p:real->A` THEN STRIP_TAC THEN
    SUBGOAL_THEN `path_in top (p:real->A)` ASSUME_TAC THENL
     [ASM_MESON_TAC[PATH_IN_SUBTOPOLOGY]; ALL_TAC] THEN
    MP_TAC(SPEC `p:real->A` (CONJUNCT2 (GEN_REWRITE_RULE I
      [SIMPLY_CONNECTED_SPACE_EQ_CONTRACTIBLE_PATH]
      (ASSUME `simply_connected_space (top:A topology)`)))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`top:A topology`; `x:A`; `p:real->A`]
                 ATOP_CONTRACTIBLE_LOOP_AVOIDING_POINT) THEN
    ASM_REWRITE_TAC[]]);;

