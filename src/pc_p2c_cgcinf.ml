(* ========================================================================= *)
(* Unit pc_p2c_cgcinf (Part 2C, used in the pc_p2c_cg route): C-infinity     *)
(* convergence calculus.  Uniform bounds on all jets plus uniform            *)
(* convergence give convergence of all partial derivatives; compositions,    *)
(* products and blends of convergent families converge; small jets of G - G0 *)
(* give small lck_dist2 m G0 G.                                              *)
(* ========================================================================= *)

needs "src/pc_p2c_cgsub.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Convergence of all partials from jet bounds.  If a sequence               *)
(* of maps has uniform jet bounds of every order on ball(c,2r) and converges *)
(* uniformly to f on ball(c,r), then all its iterated partials converge      *)
(* uniformly on ball(c,r) to those of f: otherwise some subsequence stays    *)
(* away, and P2CS_JET_SUBSEQ gives a further subsequence converging to a     *)
(* limit that agrees with f on the ball.                                     *)
(* ------------------------------------------------------------------------- *)

let P2CI_SUBSEQ_CHOICE = prove
 (`!(Q:num->bool). (!K. ?n. K <= n /\ Q n)
                   ==> ?sigma. (!m n:num. m < n ==> sigma m < sigma n) /\ !k. Q(sigma k)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `nk:num->num` (LABEL_TAC "nk")) THEN
  MP_TAC(prove_recursive_functions_exist num_RECURSION
    `(sigma:num->num) 0 = nk 0 /\ !k. sigma(SUC k) = nk(sigma k + 1)`) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `sigma:num->num` THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "nk" (MP_TAC o SPEC `(sigma:num->num) k + 1`) THEN ARITH_TAC;
    INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

let P2CI_CINF_FROM_BOUNDS = prove
 (`!(Fs:num->real^M->real^N) f c r.
     &0 < r /\
     (?N. !n. N <= n ==> smooth_map_on (ball(c,&2 * r)) (Fs n)) /\
     smooth_map_on (ball(c,r)) f /\
     (!m. ?B N. !n y. N <= n /\ y IN ball(c,&2 * r) ==> pde_jetn m (Fs n) y <= B) /\
     (!e. &0 < e ==> ?N. !n y. N <= n /\ y IN ball(c,r) ==> norm(Fs n y - f y) < e)
     ==> !l. ALL (\j. 1 <= j /\ j <= dimindex(:M)) l
             ==> !e. &0 < e
                     ==> ?K. !n y. K <= n /\ y IN ball(c,r)
                                   ==> norm(iterated_partial l (Fs n) y -
                                            iterated_partial l f y) < e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_TAC `N0:num`)
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "jet") (LABEL_TAC "c0"))))) THEN
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; NOT_FORALL_THM; NOT_IMP; REAL_NOT_LT]) THEN
  SUBGOAL_THEN
   `?sigma. (!m n:num. m < n ==> sigma m < sigma n) /\
            !k. ?y. y IN ball(c:real^M,r) /\
                    e <= norm(iterated_partial l ((Fs:num->real^M->real^N) (sigma k)) y -
                              iterated_partial l f y)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC P2CI_SUBSEQ_CHOICE THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(LABEL_TAC "sbig" o MATCH_MP MONOTONE_BIGGER) THEN
  MP_TAC(ISPECL [`\(i:num) n. (Fs:num->real^M->real^N) ((sigma:num->num) n)`;
                 `\i:num. ball(c:real^M,&2 * r)`; `\i:num. (c:real^M)`; `\i:num. (r:real)`]
                P2CS_JET_SUBSEQ) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[NUM_COUNTABLE];
      GEN_TAC THEN REWRITE_TAC[OPEN_BALL; SUBSET; IN_CBALL; IN_BALL] THEN
      ASM_REAL_ARITH_TAC;
      GEN_TAC THEN EXISTS_TAC `N0:num` THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "sbig" (fun th -> REWRITE_TAC[th]);
      MAP_EVERY X_GEN_TAC [`i:num`; `m:num`] THEN
      USE_THEN "jet" (MP_TAC o SPEC `m:num`) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `B:real` THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N1:num` THEN
      DISCH_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "sbig" (fun th -> REWRITE_TAC[th])];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tau:num->num` (X_CHOOSE_THEN `H:num->real^M->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `0`)))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "hconv")) THEN
  FIRST_ASSUM(LABEL_TAC "tbig" o MATCH_MP MONOTONE_BIGGER o
              check (fun th -> can (find_term ((=) `tau:num->num`)) (concl th))) THEN
  SUBGOAL_THEN `!y. y IN ball(c:real^M,r) ==> (H:num->real^M->real^N) 0 y = f y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
    EXISTS_TAC `\k. (Fs:num->real^M->real^N) ((sigma:num->num) ((tau:num->num) k)) y` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`\k. (Fs:num->real^M->real^N) ((sigma:num->num) ((tau:num->num) k))`;
                     `(H:num->real^M->real^N) 0`; `ball(c:real^M,r)`; `y:real^M`]
                    P2CS_UNIF_LIM) THEN
      BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "hconv" (MP_TAC o SPEC `[]:num list`) THEN REWRITE_TAC[ALL; iterated_partial];
      MP_TAC(ISPECL [`\k. (Fs:num->real^M->real^N) ((sigma:num->num) ((tau:num->num) k))`;
                     `f:real^M->real^N`; `ball(c:real^M,r)`; `y:real^M`] P2CS_UNIF_LIM) THEN
      BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `e':real` THEN DISCH_TAC THEN
      USE_THEN "c0" (MP_TAC o C MP (ASSUME `&0 < e'`) o SPEC `e':real`) THEN
      DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN EXISTS_TAC `N2:num` THEN
      MAP_EVERY X_GEN_TAC [`k:num`; `y':real^M`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(tau:num->num) k` THEN CONJ_TAC THENL
       [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "tbig" (fun th -> REWRITE_TAC[th]);
        USE_THEN "sbig" (fun th -> REWRITE_TAC[th])]];
    ALL_TAC] THEN
  USE_THEN "hconv" (MP_TAC o C MP (ASSUME `&0 < e`) o SPEC `e:real` o
                    C MP (ASSUME `ALL (\j. 1 <= j /\ j <= dimindex(:M)) l`) o
                    SPEC `l:num list`) THEN
  DISCH_THEN(X_CHOOSE_THEN `K:num` (MP_TAC o SPEC `K:num`)) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `y:real^M` STRIP_ASSUME_TAC o SPEC `(tau:num->num) K` o
                check (fun th -> is_forall(concl th) &&
                  can (find_term ((=) `sigma:num->num`)) (concl th) &&
                  can (find_term (fun t -> is_const t && fst(dest_const t) = "iterated_partial"))
                      (concl th))) THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^M`) THEN ASM_REWRITE_TAC[LE_REFL] THEN
  SUBGOAL_THEN `iterated_partial l ((H:num->real^M->real^N) 0) y = iterated_partial l f y`
  SUBST1_TAC THENL
   [MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN EXISTS_TAC `ball(c:real^M,r)` THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Convergence near a point.  p2ci_near z0 Fs f: on a ball                    *)
(* around z0 the maps are eventually smooth, the limit f is smooth, all jets  *)
(* are eventually uniformly bounded, and the convergence is uniform.  Then    *)
(* all partials converge on a smaller ball; conversely convergence of all     *)
(* partials on a ball gives p2ci_near.                                        *)
(* ------------------------------------------------------------------------- *)

let p2ci_near = new_definition
 `p2ci_near (z0:real^M) (Fs:num->real^M->real^N) f <=>
    ?r. &0 < r /\
        (?N. !n. N <= n ==> smooth_map_on (ball(z0,r)) (Fs n)) /\
        smooth_map_on (ball(z0,r)) f /\
        (!m. ?B N. !n y. N <= n /\ y IN ball(z0,r) ==> pde_jetn m (Fs n) y <= B) /\
        (!e. &0 < e ==> ?N. !n y. N <= n /\ y IN ball(z0,r) ==> norm(Fs n y - f y) < e)`;;

let P2CI_NEAR_PARTIALS = prove
 (`!(z0:real^M) (Fs:num->real^M->real^N) f.
     p2ci_near z0 Fs f
     ==> ?r. &0 < r /\
             !l. ALL (\j. 1 <= j /\ j <= dimindex(:M)) l
                 ==> !e. &0 < e
                         ==> ?K. !n y. K <= n /\ y IN ball(z0,r)
                                       ==> norm(iterated_partial l (Fs n) y -
                                                iterated_partial l f y) < e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2ci_near] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r / &2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC P2CI_CINF_FROM_BOUNDS THEN
  REWRITE_TAC[REAL_ARITH `&2 * r / &2 = r`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    EXISTS_TAC `N:num` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(z0:real^M,r)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `&0 < e`) o SPEC `e:real` o
                  check (fun th -> is_forall(concl th) &&
                    can (find_term (fun t -> is_const t && fst(dest_const t) = "vector_norm"))
                        (concl th))) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N1:num` THEN DISCH_TAC THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:real^M) IN ball(z0,r / &2)` THEN REWRITE_TAC[IN_BALL] THEN
    ASM_REAL_ARITH_TAC]);;

(* Bounds of the jets of a smooth map on a compact subset of its domain. *)

let P2CI_JETN_BOUNDED = prove
 (`!U K (f:real^M->real^N) m.
     open U /\ smooth_map_on U f /\ compact K /\ K SUBSET U
     ==> ?B. !l y. l IN pde_index_lists m (:M) /\ y IN K
                   ==> norm(iterated_partial l f y) <= B`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!l. ?Bl. !y. y IN K ==> norm(iterated_partial l (f:real^M->real^N) y) <= Bl`
  MP_TAC THENL
   [X_GEN_TAC `l:num list` THEN
    MP_TAC(ISPECL [`iterated_partial l (f:real^M->real^N)`; `K:real^M->bool`]
                  COMPACT_CONTINUOUS_IMAGE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `U:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_ITERATED_PARTIAL THEN ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
      REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN MESON_TAC[]];
    REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `Bf:(num)list->real`) THEN
    EXISTS_TAC `sum (pde_index_lists m (:M)) (\l. abs((Bf:(num)list->real) l))` THEN
    MAP_EVERY X_GEN_TAC [`l:num list`; `y:real^M`] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((Bf:(num)list->real) l)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `x <= b ==> x <= abs b`) THEN ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`{l:num list}`; `pde_index_lists m (:M)`;
                     `\l. abs((Bf:(num)list->real) l)`] SUM_SUBSET_SIMPLE) THEN
      ASM_REWRITE_TAC[PDE_INDEX_LISTS_FINITE; REAL_ABS_POS; SUM_SING; SING_SUBSET] THEN
      BETA_TAC THEN REWRITE_TAC[]]]);;

(* From convergence of all partials on a ball to p2ci_near. *)

let P2CI_NEAR_OF_PARTIALS = prove
 (`!(z0:real^M) (Fs:num->real^M->real^N) f r.
     &0 < r /\ (?N. !n. N <= n ==> smooth_map_on (ball(z0,r)) (Fs n)) /\
     smooth_map_on (ball(z0,r)) f /\
     (!l. ALL (\j. 1 <= j /\ j <= dimindex(:M)) l
          ==> !e. &0 < e
                  ==> ?K. !n y. K <= n /\ y IN ball(z0,r)
                                ==> norm(iterated_partial l (Fs n) y -
                                         iterated_partial l f y) < e)
     ==> p2ci_near z0 Fs f`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_TAC `N0:num`)
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "conv")))) THEN
  REWRITE_TAC[p2ci_near] THEN EXISTS_TAC `r / &2` THEN
  SUBGOAL_THEN `ball(z0:real^M,r / &2) SUBSET ball(z0,r)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    EXISTS_TAC `N0:num` THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `ball(z0:real^M,r)` THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(z0:real^M,r)` THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `m:num` THEN
    MP_TAC(ISPECL [`ball(z0:real^M,r)`; `cball(z0:real^M,r / &2)`; `f:real^M->real^N`;
                   `m:num`] P2CI_JETN_BOUNDED) THEN
    ASM_REWRITE_TAC[OPEN_BALL; COMPACT_CBALL] THEN ANTS_TAC THENL
     [REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `Bf:real`) THEN
    SUBGOAL_THEN
     `!l. l IN pde_index_lists m (:M)
          ==> ?K. !n y. K <= n /\ y IN ball(z0,r)
                        ==> norm(iterated_partial l ((Fs:num->real^M->real^N) n) y -
                                 iterated_partial l f y) < &1`
    MP_TAC THENL
     [X_GEN_TAC `l:num list` THEN REWRITE_TAC[pde_index_lists; IN_ELIM_THM] THEN
      STRIP_TAC THEN
      USE_THEN "conv" (MP_TAC o C MP (ASSUME `ALL (\j. 1 <= j /\ j <= dimindex(:M)) l`) o
                       SPEC `l:num list`) THEN
      DISCH_THEN(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
    DISCH_THEN(X_CHOOSE_TAC `Kf:(num)list->num`) THEN
    MP_TAC(ISPEC `IMAGE (Kf:(num)list->num) (pde_index_lists m (:M))` num_FINITE) THEN
    SIMP_TAC[FINITE_IMAGE; PDE_INDEX_LISTS_FINITE; FORALL_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_TAC `Km:num`) THEN
    EXISTS_TAC `&(CARD(pde_index_lists m (:M))) * (Bf + &1)` THEN
    EXISTS_TAC `Km:num` THEN MAP_EVERY X_GEN_TAC [`n:num`; `y:real^M`] THEN STRIP_TAC THEN
    REWRITE_TAC[pde_jetn] THEN MATCH_MP_TAC SUM_BOUND THEN
    REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
    BETA_TAC THEN
    SUBGOAL_THEN `(y:real^M) IN ball(z0,r) /\ y IN cball(z0,r / &2)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[SUBSET; BALL_SUBSET_CBALL]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `y:real^M`] o
                  C MP (ASSUME `(l:num list) IN pde_index_lists m (:M)`) o SPEC `l:num list` o
                  check (fun th -> can (find_term ((=) `Kf:(num)list->num`)) (concl th) &&
                                   not(can (find_term ((=) `Km:num`)) (concl th)))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `Km:num` THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`l:num list`; `y:real^M`] o
                  check (fun th -> can (find_term ((=) `Bf:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN NORM_ARITH_TAC;
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "conv" (MP_TAC o C MP (ASSUME `&0 < e`) o SPEC `e:real` o
                     C MP (REWRITE_CONV[ALL] `ALL (\j. 1 <= j /\ j <= dimindex(:M)) []` |>
                           EQT_ELIM) o SPEC `[]:num list`) THEN
    REWRITE_TAC[iterated_partial] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `K:num` THEN
    DISCH_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]);;

(* Constant sequences and local agreement. *)

let P2CI_NEAR_CONST = prove
 (`!(z0:real^M) (f:real^M->real^N) r.
     &0 < r /\ smooth_map_on (ball(z0,r)) f ==> p2ci_near z0 (\n. f) f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CI_NEAR_OF_PARTIALS THEN EXISTS_TAC `r:real` THEN
  ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN MESON_TAC[]);;

let P2CI_NEAR_EQ = prove
 (`!(z0:real^M) (Fs:num->real^M->real^N) f Gs g r N0.
     p2ci_near z0 Gs g /\ &0 < r /\
     (!n z. N0 <= n /\ z IN ball(z0,r) ==> Fs n z = Gs n z) /\
     (!z. z IN ball(z0,r) ==> f z = g z)
     ==> p2ci_near z0 Fs f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2ci_near] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `r0:real` (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (X_CHOOSE_TAC `N1:num`) (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 (LABEL_TAC "jet") (LABEL_TAC "c0"))))))
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "fg") (LABEL_TAC "eq")))) THEN
  EXISTS_TAC `min r r0` THEN
  SUBGOAL_THEN `ball(z0:real^M,min r r0) SUBSET ball(z0,r) /\
                ball(z0:real^M,min r r0) SUBSET ball(z0,r0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    EXISTS_TAC `N0 + N1:num` THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `(Gs:num->real^M->real^N) n` THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN USE_THEN "fg" MATCH_MP_TAC THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(z0:real^M,r0)` THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `g:real^M->real^N` THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN USE_THEN "eq" MATCH_MP_TAC THEN
      ASM SET_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(z0:real^M,r0)` THEN
      ASM_REWRITE_TAC[]];
    X_GEN_TAC `m:num` THEN USE_THEN "jet" (MP_TAC o SPEC `m:num`) THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` (X_CHOOSE_TAC `N2:num`)) THEN
    MAP_EVERY EXISTS_TAC [`B:real`; `N0 + N2:num`] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `y:real^M`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `pde_jetn m ((Fs:num->real^M->real^N) n) y =
                  pde_jetn m ((Gs:num->real^M->real^N) n) y`
    SUBST1_TAC THENL
     [MATCH_MP_TAC P2CT_JETN_LOCAL THEN EXISTS_TAC `ball(z0:real^M,min r r0)` THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN REPEAT STRIP_TAC THEN USE_THEN "fg" MATCH_MP_TAC THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]];
      FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]]];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "c0" (MP_TAC o C MP (ASSUME `&0 < e`) o SPEC `e:real`) THEN
    DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN EXISTS_TAC `N0 + N2:num` THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `y:real^M`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(Fs:num->real^M->real^N) n y = Gs n y /\ (f:real^M->real^N) y = g y`
    (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THENL
       [USE_THEN "fg" MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]];
        USE_THEN "eq" MATCH_MP_TAC THEN ASM SET_TAC[]];
      FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]]]]);;

(* ------------------------------------------------------------------------- *)
(* Compositions.  Jets of Ts o As at y are bounded in terms of                *)
(* the jets of As at y and of Ts at As y (P2CT_COMPOSE_JET_UNIFORM), and a    *)
(* composition of families converging near z0 and near A z0 converges near   *)
(* z0.                                                                        *)
(* ------------------------------------------------------------------------- *)

let P2CI_SUM_TERM_LE = prove
 (`!(f:num->real) m i. i <= m /\ (!k. &0 <= f k) ==> f i <= sum(0..m) f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{i:num}`; `0..m`; `f:num->real`] SUM_SUBSET_SIMPLE) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; SUM_SING; SING_SUBSET; IN_NUMSEG; LE_0]);;

let P2CI_COMPOSE_JETS = prove
 (`!m (BA:num->real) (BT:num->real).
     ?C. !s0 t0 (As:real^M->real^N) (Ts:real^N->real^P) y.
           open s0 /\ open t0 /\ smooth_map_on s0 As /\ IMAGE As s0 SUBSET t0 /\
           smooth_map_on t0 Ts /\ y IN s0 /\
           (!k. k <= m ==> pde_jetn (SUC k) As y <= BA k) /\
           (!k. k <= m ==> pde_jetn k Ts (As y) <= BT k)
           ==> pde_jetn m (Ts o As) y <= C`,
  REPEAT GEN_TAC THEN
  MP_TAC(GEN `k:num` (ISPECL [`k:num`; `(BA:num->real) k`]
     (INST_TYPE [`:M`,`:N`; `:N`,`:M`; `:P`,`:P`] P2CT_COMPOSE_JET_UNIFORM))) THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `Cc:num->real` (LABEL_TAC "cc")) THEN
  EXISTS_TAC `&(CARD(pde_index_lists m (:M))) *
              sum(0..m) (\k. abs((Cc:num->real) k) * abs((BT:num->real) k))` THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[pde_jetn] THEN
  MATCH_MP_TAC SUM_BOUND THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
  X_GEN_TAC `l:num list` THEN REWRITE_TAC[pde_index_lists; IN_ELIM_THM] THEN STRIP_TAC THEN
  BETA_TAC THEN
  USE_THEN "cc" (MP_TAC o SPEC `LENGTH(l:num list)`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPECL
    [`s0:real^M->bool`; `t0:real^N->bool`; `As:real^M->real^N`; `Ts:real^N->real^P`;
     `y:real^M`])) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `pde_jetn (SUC(LENGTH(l:num list))) (As:real^M->real^N) y` THEN
    ASM_SIMP_TAC[PDE_JETN_PARTIAL];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `l:num list`) THEN ASM_REWRITE_TAC[o_DEF] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(Cc:num->real)(LENGTH(l:num list)) *
              pde_jetn (LENGTH l) (Ts:real^N->real^P) ((As:real^M->real^N) y)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs((Cc:num->real)(LENGTH(l:num list))) * abs((BT:num->real)(LENGTH l))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(Cc:num->real)(LENGTH(l:num list)) * (BT:num->real)(LENGTH l)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[];
      REWRITE_TAC[GSYM REAL_ABS_MUL; REAL_ABS_LE]];
    MP_TAC(ISPECL [`\k. abs((Cc:num->real) k) * abs((BT:num->real) k)`; `m:num`;
                   `LENGTH(l:num list)`] P2CI_SUM_TERM_LE) THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_ABS_POS]]);;

let P2CI_LIP_ARITH = prove
 (`!L a b e. &0 <= a /\ abs L * a < e / &2 /\ b < e / &2 ==> L * a + b < e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `L * a <= abs L * a` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_ABS_LE]; ASM_REAL_ARITH_TAC]);;

let P2CI_NEAR_COMPOSE = prove
 (`!(z0:real^M) (As:num->real^M->real^N) A (Ts:num->real^N->real^P) Tl.
     p2ci_near z0 As A /\ p2ci_near (A z0) Ts Tl
     ==> p2ci_near z0 (\n. Ts n o As n) (Tl o A)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2ci_near] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `rA:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_TAC `NA:num`)
       (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "jA") (LABEL_TAC "cA"))))))
    (X_CHOOSE_THEN `rT:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_TAC `NT:num`)
       (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "jT") (LABEL_TAC "cT"))))))) THEN
  ABBREV_TAC `w0 = (A:real^M->real^N) z0` THEN
  SUBGOAL_THEN `?d. &0 < d /\ d <= rA /\
                    !z. z IN ball(z0:real^M,d) ==> (A:real^M->real^N) z IN ball(w0,rT / &2)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`A:real^M->real^N`; `ball(z0:real^M,rA)`] CONTINUOUS_ON_EQ_CONTINUOUS_AT) THEN
    REWRITE_TAC[OPEN_BALL] THEN DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
    ANTS_TAC THENL [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `z0:real^M`) THEN ASM_REWRITE_TAC[CENTRE_IN_BALL; continuous_at] THEN
    DISCH_THEN(MP_TAC o SPEC `rT / &2`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min d rA` THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_BALL] THEN REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(z0:real^M,d) SUBSET ball(z0,rA)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_BALL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "cA" (MP_TAC o SPEC `rT / &2`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "c2")) THEN
  SUBGOAL_THEN `!n z. N2 <= n /\ z IN ball(z0:real^M,d)
                      ==> (As:num->real^M->real^N) n z IN ball(w0,rT)`
  (LABEL_TAC "img") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "c2" (MP_TAC o SPECL [`n:num`; `z:real^M`]) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^M` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `A:real^M->real^N`)) (concl th) &&
      can (find_term ((=) `d:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[IN_BALL] THEN
    MP_TAC(ISPECL [`w0:real^N`; `(A:real^M->real^N) z`;
                   `(As:num->real^M->real^N) n z`] DIST_TRIANGLE) THEN
    REWRITE_TAC[dist] THEN MP_TAC(ISPECL [`(As:num->real^M->real^N) n z`;
                                          `(A:real^M->real^N) z`] NORM_SUB) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[SKOLEM_THM] o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `As:num->real^M->real^N`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "pde_jetn")) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `BA:num->real` (X_CHOOSE_THEN `NAf:num->num` (LABEL_TAC "bA"))) THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[SKOLEM_THM] o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `Ts:num->real^N->real^P`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "pde_jetn")) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `BT:num->real` (X_CHOOSE_THEN `NTf:num->num` (LABEL_TAC "bT"))) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC `NA + NT + N2:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `ball(w0:real^N,rT)` THEN
    REWRITE_TAC[OPEN_BALL] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
      USE_THEN "img" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(z0:real^M,rA)` THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `ball(w0:real^N,rT)` THEN
    REWRITE_TAC[OPEN_BALL] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `z:real^M` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `A:real^M->real^N`)) (concl th) &&
        can (find_term ((=) `d:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`w0:real^N`; `rT / &2`; `rT:real`] SUBSET_BALL) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SET_TAC[]];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(z0:real^M,rA)` THEN
      ASM_REWRITE_TAC[]];
    X_GEN_TAC `m:num` THEN
    MP_TAC(ISPECL [`m:num`; `\k. (BA:num->real)(SUC k)`; `BT:num->real`]
                  (INST_TYPE [`:M`,`:M`; `:N`,`:N`; `:P`,`:P`] P2CI_COMPOSE_JETS)) THEN
    BETA_TAC THEN DISCH_THEN(X_CHOOSE_TAC `C:real`) THEN EXISTS_TAC `C:real` THEN
    MP_TAC(ISPEC `IMAGE (\k. (NAf:num->num)(SUC k) + (NTf:num->num) k) (0..m)` num_FINITE) THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; FORALL_IN_IMAGE; IN_NUMSEG; LE_0] THEN
    DISCH_THEN(X_CHOOSE_TAC `Nb:num`) THEN EXISTS_TAC `NA + NT + N2 + Nb:num` THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `y:real^M`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`ball(z0:real^M,d)`; `ball(w0:real^N,rT)`] THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(z0:real^M,rA)` THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
      USE_THEN "img" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN USE_THEN "bA" MATCH_MP_TAC THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `Nb:num`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        ASM SET_TAC[]];
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN USE_THEN "bT" MATCH_MP_TAC THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `Nb:num`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        USE_THEN "img" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    ABBREV_TAC `L = &(dimindex(:N)) * (BT:num->real) 1` THEN
    USE_THEN "cA" (MP_TAC o SPEC `e / &2 / (abs L + &1)`) THEN ANTS_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N3:num` (LABEL_TAC "c3")) THEN
    USE_THEN "cT" (MP_TAC o SPEC `e / &2`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N4:num` (LABEL_TAC "c4")) THEN
    EXISTS_TAC `NT + N2 + N3 + N4 + (NTf:num->num) 1` THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `y:real^M`] THEN STRIP_TAC THEN
    REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(As:num->real^M->real^N) n y IN ball(w0,rT) /\
                  (A:real^M->real^N) y IN ball(w0,rT)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [USE_THEN "img" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        FIRST_X_ASSUM(MP_TAC o SPEC `y:real^M` o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `A:real^M->real^N`)) (concl th) &&
          can (find_term ((=) `d:real`)) (concl th))) THEN
        ASM_REWRITE_TAC[IN_BALL] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(Ts:num->real^N->real^P) n`; `ball(w0:real^N,rT)`; `ball(w0:real^N,rT)`;
                   `[]:num list`; `1`; `(BT:num->real) 1`] P2CS_PARTIAL_LIPSCHITZ) THEN
    REWRITE_TAC[OPEN_BALL; CONVEX_BALL; SUBSET_REFL; ALL; LENGTH; iterated_partial] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ANTS_TAC THENL
     [CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
      REPEAT STRIP_TAC THEN USE_THEN "bT" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`(As:num->real^M->real^N) n y`; `(A:real^M->real^N) y`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    USE_THEN "c3" (MP_TAC o SPECL [`n:num`; `y:real^M`]) THEN
    ANTS_TAC THENL [CONJ_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]]; DISCH_TAC] THEN
    USE_THEN "c4" (MP_TAC o SPECL [`n:num`; `(A:real^M->real^N) y`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `norm((Ts:num->real^N->real^P) n ((As:num->real^M->real^N) n y) -
                     Ts n ((A:real^M->real^N) y)) +
                norm(Ts n (A y) - (Tl:real^N->real^P)(A y))` THEN
    CONJ_TAC THENL [REWRITE_TAC[GSYM dist; DIST_TRIANGLE]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `L * norm((As:num->real^M->real^N) n y - (A:real^M->real^N) y) +
                norm((Ts:num->real^N->real^P) n (A y) - (Tl:real^N->real^P)(A y))` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC P2CI_LIP_ARITH THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN
    UNDISCH_TAC `norm((As:num->real^M->real^N) n y - (A:real^M->real^N) y) <
                 e / &2 / (abs L + &1)` THEN
    SIMP_TAC[REAL_LT_RDIV_EQ; REAL_ARITH `&0 < abs L + &1`] THEN
    MP_TAC(ISPEC `(As:num->real^M->real^N) n y - (A:real^M->real^N) y` NORM_POS_LE) THEN
    REAL_ARITH_TAC]);;

(* Sums, and products with a fixed smooth scalar function. *)

let P2CI_NEAR_ADD = prove
 (`!(z0:real^M) (As:num->real^M->real^N) A Bs B.
     p2ci_near z0 As A /\ p2ci_near z0 Bs B
     ==> p2ci_near z0 (\n z. As n z + Bs n z) (\z. A z + B z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2ci_near] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `rA:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_TAC `NA:num`)
       (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "jA") (LABEL_TAC "cA"))))))
    (X_CHOOSE_THEN `rB:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_TAC `NB:num`)
       (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "jB") (LABEL_TAC "cB"))))))) THEN
  EXISTS_TAC `min rA rB` THEN
  SUBGOAL_THEN `ball(z0:real^M,min rA rB) SUBSET ball(z0,rA) /\
                ball(z0:real^M,min rA rB) SUBSET ball(z0,rB)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    EXISTS_TAC `NA + NB:num` THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN REWRITE_TAC[OPEN_BALL; ETA_AX] THEN CONJ_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THENL
     [EXISTS_TAC `ball(z0:real^M,rA)`; EXISTS_TAC `ball(z0:real^M,rB)`] THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN REWRITE_TAC[OPEN_BALL; ETA_AX] THEN CONJ_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THENL
     [EXISTS_TAC `ball(z0:real^M,rA)`; EXISTS_TAC `ball(z0:real^M,rB)`] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `m:num` THEN
    USE_THEN "jA" (X_CHOOSE_THEN `B1:real` (X_CHOOSE_TAC `N1:num`) o SPEC `m:num`) THEN
    USE_THEN "jB" (X_CHOOSE_THEN `B2:real` (X_CHOOSE_TAC `N2:num`) o SPEC `m:num`) THEN
    MAP_EVERY EXISTS_TAC [`B1 + B2:real`; `NA + NB + N1 + N2:num`] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `y:real^M`] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `pde_jetn m ((As:num->real^M->real^N) n) y +
                pde_jetn m ((Bs:num->real^M->real^N) n) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2CT_JETN_ADD THEN EXISTS_TAC `ball(z0:real^M,min rA rB)` THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THENL
       [EXISTS_TAC `ball(z0:real^M,rA)`; EXISTS_TAC `ball(z0:real^M,rB)`] THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      (CONJ_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]])];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "cA" (MP_TAC o SPEC `e / &2`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
    USE_THEN "cB" (MP_TAC o SPEC `e / &2`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN EXISTS_TAC `N1 + N2:num` THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `y:real^M`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `y:real^M`] o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `N2:num`)) (concl th))) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `y:real^M`] o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `N1:num`)) (concl th))) THEN
    ANTS_TAC THENL [CONJ_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]]; DISCH_TAC] THEN
    ANTS_TAC THENL [CONJ_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]]; DISCH_TAC] THEN
    REWRITE_TAC[VECTOR_ARITH `(a + b) - (c + d):real^N = (a - c) + (b - d)`] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `norm((As:num->real^M->real^N) n y - (A:real^M->real^N) y) +
                norm((Bs:num->real^M->real^N) n y - (B:real^M->real^N) y)` THEN
    REWRITE_TAC[NORM_TRIANGLE] THEN ASM_REAL_ARITH_TAC]);;

let P2CI_MUL5_LE = prove
 (`!a b c x x' y y'. &0 <= a /\ &0 <= b /\ &0 <= c /\ &0 <= x /\ x <= x' /\
                     &0 <= y /\ y <= y'
                     ==> a * b * c * x * y <= a * b * c * x' * y'`,
  REPEAT STRIP_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]) THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]);;

(* Bilinear combinations of two convergent families. *)

let P2CI_BILINEAR_ARITH = prove
 (`!Bb a b ma mb d e.
     &0 <= Bb /\ &0 <= a /\ &0 <= b /\ &0 <= ma /\ &0 <= mb /\
     a <= d /\ b <= d /\ &0 < d /\ d <= &1 /\ d * (Bb * (ma + mb + &1) + &1) <= e /\ &0 < e
     ==> Bb * a * (mb + b) + Bb * ma * b < e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `Bb * a * (mb + b) <= Bb * d * (mb + &1) /\ Bb * ma * b <= Bb * ma * d`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= d * Bb * (ma + mb + &1)` MP_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2CI_NEAR_BILINEAR = prove
 (`!(bb:real^P->real^Q->real^K) Bb (z0:real^M) (As:num->real^M->real^P) A
    (Bs:num->real^M->real^Q) B.
     bilinear bb /\ &0 <= Bb /\ (!u v. norm(bb u v) <= Bb * norm u * norm v) /\
     p2ci_near z0 As A /\ p2ci_near z0 Bs B
     ==> p2ci_near z0 (\n z. bb (As n z) (Bs n z)) (\z. bb (A z) (B z))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2ci_near] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "bnd") (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `rA:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_TAC `NA:num`)
       (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "jA") (LABEL_TAC "cA"))))))
    (X_CHOOSE_THEN `rB:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_TAC `NB:num`)
       (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "jB") (LABEL_TAC "cB")))))))))) THEN
  ABBREV_TAC `s = min rA rB / &2` THEN
  SUBGOAL_THEN `&0 < s /\ ball(z0:real^M,s) SUBSET ball(z0,rA) /\
                ball(z0:real^M,s) SUBSET ball(z0,rB) /\
                cball(z0:real^M,s) SUBSET ball(z0,rA) /\ cball(z0:real^M,s) SUBSET ball(z0,rB)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `?MA MB. &0 <= MA /\ &0 <= MB /\
                        !y. y IN ball(z0:real^M,s)
                            ==> norm((A:real^M->real^P) y) <= MA /\
                                norm((B:real^M->real^Q) y) <= MB`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ball(z0:real^M,rA)`; `cball(z0:real^M,s)`; `A:real^M->real^P`; `0`]
                  P2CI_JETN_BOUNDED) THEN
    MP_TAC(ISPECL [`ball(z0:real^M,rB)`; `cball(z0:real^M,s)`; `B:real^M->real^Q`; `0`]
                  P2CI_JETN_BOUNDED) THEN
    ASM_REWRITE_TAC[OPEN_BALL; COMPACT_CBALL] THEN
    DISCH_THEN(X_CHOOSE_THEN `M2:real` (LABEL_TAC "m2")) THEN
    DISCH_THEN(X_CHOOSE_THEN `M1:real` (LABEL_TAC "m1")) THEN
    MAP_EVERY EXISTS_TAC [`abs M1`; `abs M2`] THEN REWRITE_TAC[REAL_ABS_POS] THEN
    X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^M) IN cball(z0,s)` ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET; BALL_SUBSET_CBALL]; ALL_TAC] THEN
    REMOVE_THEN "m1" (MP_TAC o SPECL [`[]:num list`; `y:real^M`]) THEN
    REMOVE_THEN "m2" (MP_TAC o SPECL [`[]:num list`; `y:real^M`]) THEN
    ASM_REWRITE_TAC[iterated_partial; pde_index_lists; IN_ELIM_THM; LENGTH; ALL; LE_REFL] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `s:real` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC `NA + NB:num` THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_BILINEAR_OPEN THEN ASM_REWRITE_TAC[OPEN_BALL; ETA_AX] THEN
    CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THENL
     [EXISTS_TAC `ball(z0:real^M,rA)`; EXISTS_TAC `ball(z0:real^M,rB)`] THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    MATCH_MP_TAC SMOOTH_MAP_ON_BILINEAR_OPEN THEN ASM_REWRITE_TAC[OPEN_BALL; ETA_AX] THEN
    CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THENL
     [EXISTS_TAC `ball(z0:real^M,rA)`; EXISTS_TAC `ball(z0:real^M,rB)`] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `m:num` THEN
    USE_THEN "jA" (X_CHOOSE_THEN `B1:real` (X_CHOOSE_TAC `N1:num`) o SPEC `m:num`) THEN
    USE_THEN "jB" (X_CHOOSE_THEN `B2:real` (X_CHOOSE_TAC `N2:num`) o SPEC `m:num`) THEN
    EXISTS_TAC `&(CARD(pde_index_lists m (:M))) * &2 pow m * Bb * abs B1 * abs B2` THEN
    EXISTS_TAC `NA + NB + N1 + N2:num` THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `y:real^M`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`bb:real^P->real^Q->real^K`; `Bb:real`; `ball(z0:real^M,s)`; `m:num`;
                   `(As:num->real^M->real^P) n`; `(Bs:num->real^M->real^Q) n`; `y:real^M`]
                  P2CT_BILINEAR_JETN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THENL
       [EXISTS_TAC `ball(z0:real^M,rA)`; EXISTS_TAC `ball(z0:real^M,rB)`] THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    MATCH_MP_TAC P2CI_MUL5_LE THEN ASM_REWRITE_TAC[PDE_JETN_POS; REAL_POS] THEN
    SIMP_TAC[REAL_POW_LE; REAL_POS] THEN CONJ_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `x <= b ==> x <= abs b`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THEN TRY(ASM_ARITH_TAC) THEN ASM SET_TAC[];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    ABBREV_TAC `d = min (&1) (e / (Bb * (MA + MB + &1) + &1))` THEN
    SUBGOAL_THEN `&0 < d /\ d <= &1 /\ d * (Bb * (MA + MB + &1) + &1) <= e` STRIP_ASSUME_TAC
    THENL
     [SUBGOAL_THEN `&0 < Bb * (MA + MB + &1) + &1` ASSUME_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      EXPAND_TAC "d" THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
        REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `e / (Bb * (MA + MB + &1) + &1) * (Bb * (MA + MB + &1) + &1)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
           [REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_IMP_LE]];
          ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ; REAL_LE_REFL]]];
      ALL_TAC] THEN
    USE_THEN "cA" (MP_TAC o C MP (ASSUME `&0 < d`) o SPEC `d:real`) THEN
    DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
    USE_THEN "cB" (MP_TAC o C MP (ASSUME `&0 < d`) o SPEC `d:real`) THEN
    DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN EXISTS_TAC `N1 + N2:num` THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `y:real^M`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `y:real^M`] o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `N2:num`)) (concl th))) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `y:real^M`] o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `N1:num`)) (concl th))) THEN
    ANTS_TAC THENL [CONJ_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]]; DISCH_TAC] THEN
    ANTS_TAC THENL [CONJ_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]]; DISCH_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^M` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `MA:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(bb:real^P->real^Q->real^K) ((As:num->real^M->real^P) n y) ((Bs:num->real^M->real^Q) n y) -
      bb ((A:real^M->real^P) y) ((B:real^M->real^Q) y) =
      bb (As n y - A y) (Bs n y) + bb (A y) (Bs n y - B y)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `bilinear (bb:real^P->real^Q->real^K)` THEN
      REWRITE_TAC[bilinear] THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
      FIRST_ASSUM(MP_TAC o SPEC `(Bs:num->real^M->real^Q) n y` o
                  check (fun th -> is_forall(concl th))) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(A:real^M->real^P) y` o
                  check (fun th -> is_forall(concl th))) THEN
      REWRITE_TAC[linear] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[VECTOR_ARITH `x - y:real^N = x + --(&1) % y`] THEN
      ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `Bb * norm((As:num->real^M->real^P) n y - A y) * (MB + norm((Bs:num->real^M->real^Q) n y - B y)) +
                Bb * MA * norm((Bs:num->real^M->real^Q) n y - B y)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm((bb:real^P->real^Q->real^K) ((As:num->real^M->real^P) n y - A y) ((Bs:num->real^M->real^Q) n y)) +
                  norm(bb ((A:real^M->real^P) y) ((Bs:num->real^M->real^Q) n y - B y))` THEN
      REWRITE_TAC[NORM_TRIANGLE] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THENL
       [EXISTS_TAC `Bb * norm((As:num->real^M->real^P) n y - A y) * norm((Bs:num->real^M->real^Q) n y)`;
        EXISTS_TAC `Bb * norm((A:real^M->real^P) y) * norm((Bs:num->real^M->real^Q) n y - B y)`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE; REAL_LE_REFL] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`(Bs:num->real^M->real^Q) n y`; `(B:real^M->real^Q) y`] NORM_TRIANGLE_SUB) THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC P2CI_BILINEAR_ARITH THEN EXISTS_TAC `d:real` THEN
      ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE]]]);;

let P2CI_NEAR_SMUL = prove
 (`!(z0:real^M) (As:num->real^M->real^N) A (mu:real^M->real^1) r.
     p2ci_near z0 As A /\ &0 < r /\ smooth_map_on (ball(z0,r)) mu
     ==> p2ci_near z0 (\n z. drop(mu z) % As n z) (\z. drop(mu z) % A z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\(a:real^1) (v:real^N). drop a % v`; `&1`; `z0:real^M`;
                 `\n:num. (mu:real^M->real^1)`; `mu:real^M->real^1`;
                 `As:num->real^M->real^N`; `A:real^M->real^N`] P2CI_NEAR_BILINEAR) THEN
  BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_POS] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[bilinear; linear; DROP_ADD; DROP_CMUL] THEN REPEAT STRIP_TAC THEN
    VECTOR_ARITH_TAC;
    REWRITE_TAC[NORM_MUL; NORM_1; REAL_MUL_LID; REAL_LE_REFL];
    MATCH_MP_TAC P2CI_NEAR_CONST THEN EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[]]);;

(* Partial derivatives and linear images. *)

let P2CI_NEAR_PARTIAL = prove
 (`!(z0:real^M) (Fs:num->real^M->real^N) f i.
     p2ci_near z0 Fs f /\ 1 <= i /\ i <= dimindex(:M)
     ==> p2ci_near z0 (\n. partial_derivative i (Fs n)) (partial_derivative i f)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pc")) o
              MATCH_MP P2CI_NEAR_PARTIALS) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [p2ci_near]) THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `N0:num`) (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))))) THEN
  MATCH_MP_TAC P2CI_NEAR_OF_PARTIALS THEN EXISTS_TAC `min r r0` THEN
  SUBGOAL_THEN `ball(z0:real^M,min r r0) SUBSET ball(z0,r) /\
                ball(z0:real^M,min r r0) SUBSET ball(z0,r0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    EXISTS_TAC `N0:num` THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(z0:real^M,r0)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN
    ASM_SIMP_TAC[OPEN_BALL];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(z0:real^M,r0)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    X_GEN_TAC `l:num list` THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "pc" (MP_TAC o SPEC `APPEND l [i:num]`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[ALL_APPEND; ALL]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o C MP (ASSUME `&0 < e`) o SPEC `e:real`) THEN
    REWRITE_TAC[ITERATED_PARTIAL_APPEND; iterated_partial] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `K:num` THEN DISCH_TAC THEN
    REPEAT STRIP_TAC THEN BETA_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]);;

let P2CI_NEAR_LINEAR = prove
 (`!(z0:real^M) (Fs:num->real^M->real^N) f (L:real^N->real^P).
     p2ci_near z0 Fs f /\ linear L
     ==> p2ci_near z0 (\n z. L(Fs n z)) (\z. L(f z))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`z0:real^M`; `Fs:num->real^M->real^N`; `f:real^M->real^N`;
                 `\n:num. (L:real^N->real^P)`; `L:real^N->real^P`] P2CI_NEAR_COMPOSE) THEN
  ASM_REWRITE_TAC[o_DEF] THEN BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC P2CI_NEAR_CONST THEN EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
  SUBGOAL_THEN `(L:real^N->real^P) = L o (\x. x)` SUBST1_TAC THENL
   [REWRITE_TAC[o_DEF; ETA_AX]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
  ASM_REWRITE_TAC[OPEN_BALL; SMOOTH_MAP_ON_ID]);;

(* ------------------------------------------------------------------------- *)
(* Covariant C^m distance from C-infinity convergence.  Finite               *)
(* sums, differences and products of families converging near z0 converge;  *)
(* a family of (0,k)-tensor fields whose components tend to 0 near z0 keeps  *)
(* this property under lnabla of a fixed smooth metric G0 (expand the        *)
(* derivative in partials and the Christoffel slot in the basis); hence if   *)
(* the matrices Gs n converge to G0 in C-infinity near z0 then lck_dist2 m   *)
(* G0 (Gs n) tends to 0 near z0 (P2CI_LCK_NEAR), and uniformly on compact    *)
(* sets (P2CI_LCK_COMPACT).                                                  *)
(* ------------------------------------------------------------------------- *)

let P2CI_NEAR_VSUM = prove
 (`!(z0:real^M) (Fs:A->num->real^M->real^N) f s.
     FINITE s /\ (!i. i IN s ==> p2ci_near z0 (Fs i) (f i))
     ==> p2ci_near z0 (\n y. vsum s (\i. Fs i n y)) (\y. vsum s (\i. f i y))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[VSUM_CLAUSES] THEN MATCH_MP_TAC P2CI_NEAR_CONST THEN
    EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01; SMOOTH_MAP_ON_CONST];
    MAP_EVERY X_GEN_TAC [`x:A`; `s:A->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[FORALL_IN_INSERT] THEN STRIP_TAC THEN
    SIMP_TAC[VSUM_CLAUSES; ASSUME `FINITE(s:A->bool)`; ASSUME `~((x:A) IN s)`] THEN
    MP_TAC(ISPECL [`z0:real^M`; `(Fs:A->num->real^M->real^N) x`; `(f:A->real^M->real^N) x`;
                   `\n y. vsum s (\i. (Fs:A->num->real^M->real^N) i n y)`;
                   `\y. vsum s (\i. (f:A->real^M->real^N) i y)`] P2CI_NEAR_ADD) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REMOVE_THEN "ih" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let P2CI_ZERO_VSUM = prove
 (`!(z0:real^M) (Fs:A->num->real^M->real^N) s.
     FINITE s /\ (!i. i IN s ==> p2ci_near z0 (Fs i) (\y. vec 0))
     ==> p2ci_near z0 (\n y. vsum s (\i. Fs i n y)) (\y. vec 0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`z0:real^M`; `Fs:A->num->real^M->real^N`; `\i:A y:real^M. vec 0:real^N`;
                 `s:A->bool`] P2CI_NEAR_VSUM) THEN
  ASM_REWRITE_TAC[VSUM_0]);;

let P2CI_NEAR_NEG = prove
 (`!(z0:real^M) (Fs:num->real^M->real^N) f.
     p2ci_near z0 Fs f ==> p2ci_near z0 (\n z. --(Fs n z)) (\z. --(f z))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`z0:real^M`; `Fs:num->real^M->real^N`; `f:real^M->real^N`;
                 `\x:real^N. --x`] P2CI_NEAR_LINEAR) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      REWRITE_TAC[linear] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC];
    REWRITE_TAC[]]);;

let P2CI_NEAR_TO_ZERO = prove
 (`!(z0:real^M) (Fs:num->real^M->real^N) f.
     p2ci_near z0 Fs f ==> p2ci_near z0 (\n z. Fs n z - f z) (\z. vec 0)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC o REWRITE_RULE[p2ci_near]) THEN
  MP_TAC(ISPECL [`z0:real^M`; `Fs:num->real^M->real^N`; `f:real^M->real^N`;
                 `\n:num z:real^M. --((f:real^M->real^N) z)`;
                 `\z:real^M. --((f:real^M->real^N) z)`] P2CI_NEAR_ADD) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`z0:real^M`; `\n:num. (f:real^M->real^N)`; `f:real^M->real^N`]
                  P2CI_NEAR_NEG) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC P2CI_NEAR_CONST THEN EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM VECTOR_SUB; VECTOR_SUB_REFL]]);;

let P2CI_ZERO_SUB = prove
 (`!(z0:real^M) (As:num->real^M->real^N) Bs.
     p2ci_near z0 As (\y. vec 0) /\ p2ci_near z0 Bs (\y. vec 0)
     ==> p2ci_near z0 (\n y. As n y - Bs n y) (\y. vec 0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`z0:real^M`; `As:num->real^M->real^N`; `\y:real^M. vec 0:real^N`;
                 `\n:num y:real^M. --((Bs:num->real^M->real^N) n y)`;
                 `\y:real^M. --(vec 0:real^N)`] P2CI_NEAR_ADD) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC P2CI_NEAR_NEG THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[VECTOR_NEG_0; VECTOR_ADD_LID; GSYM VECTOR_SUB; VECTOR_SUB_REFL]]);;

let P2CI_ZERO_SMUL = prove
 (`!(z0:real^M) (As:num->real^M->real^N) (mu:real^M->real^1) r.
     p2ci_near z0 As (\z. vec 0) /\ &0 < r /\ smooth_map_on (ball(z0,r)) mu
     ==> p2ci_near z0 (\n z. drop(mu z) % As n z) (\z. vec 0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`z0:real^M`; `As:num->real^M->real^N`; `\z:real^M. vec 0:real^N`;
                 `mu:real^M->real^1`; `r:real`] P2CI_NEAR_SMUL) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_RZERO]);;

let P2CI_ZERO_PARTIAL = prove
 (`!(z0:real^M) (Fs:num->real^M->real^N) i.
     p2ci_near z0 Fs (\z. vec 0) /\ 1 <= i /\ i <= dimindex(:M)
     ==> p2ci_near z0 (\n. partial_derivative i (Fs n)) (\z. vec 0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`z0:real^M`; `Fs:num->real^M->real^N`; `\z:real^M. vec 0:real^N`; `i:num`]
                P2CI_NEAR_PARTIAL) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; partial_derivative; FRECHET_DERIVATIVE_CONST_AT]);;

let P2CI_ZERO_MUL = prove
 (`!(z0:real^M) (a:num->real^M->real) b (B:real^M->real^1).
     p2ci_near z0 (\n y. lift(a n y)) (\y. vec 0) /\ p2ci_near z0 (\n y. lift(b n y)) B
     ==> p2ci_near z0 (\n y. lift(a n y * b n y)) (\y. vec 0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\(x:real^1) (y:real^1). drop x % y`; `&1`; `z0:real^M`;
                 `\n:num y:real^M. lift((a:num->real^M->real) n y)`; `\y:real^M. vec 0:real^1`;
                 `\n:num y:real^M. lift((b:num->real^M->real) n y)`; `B:real^M->real^1`]
                P2CI_NEAR_BILINEAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POS] THEN CONJ_TAC THENL
     [REWRITE_TAC[bilinear; linear; DROP_ADD; DROP_CMUL] THEN REPEAT STRIP_TAC THEN
      VECTOR_ARITH_TAC;
      REWRITE_TAC[NORM_MUL; NORM_1; REAL_MUL_LID; REAL_LE_REFL]];
    REWRITE_TAC[LIFT_DROP; DROP_VEC; VECTOR_MUL_LZERO; GSYM LIFT_CMUL]]);;

(* Expansions of the two terms of lnabla. *)

let P2CI_FD_EXPAND = prove
 (`!(f:real^M->real^N) y v.
     f differentiable (at y)
     ==> frechet_derivative f (at y) v =
         vsum(1..dimindex(:M)) (\j. v$j % partial_derivative j f y)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
  ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL; partial_derivative]);;

let P2CI_SLOT_EXPAND_LIFT = prove
 (`!k U (tf:real^N->(num->real^N)->real) y i u v.
     ltensor_field k U tf /\ y IN U /\ 1 <= i /\ i <= k
     ==> lift(tf y (\j. if j = i then v else u j)) =
         vsum(1..dimindex(:N))
             (\q. v$q % lift(tf y (\j. if j = i then basis q else u j)))`,
  REWRITE_TAC[ltensor_field] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`i:num`; `u:num->real^N`] o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
                          [MATCH_MP LRG_SLOT_EXPAND th]) THEN
  REWRITE_TAC[LIFT_SUM; o_DEF; LIFT_CMUL]);;

let P2CI_LNABLA_EXPAND = prove
 (`!k S (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y u.
     open S /\ ltensor_field k S tf /\ (!u. smooth_map_on S (\y. lift(tf y u))) /\ y IN S
     ==> lift(lnabla k G tf y u) =
         vsum(1..dimindex(:N))
             (\j. (u(k + 1))$j % partial_derivative j (\x. lift(tf x u)) y) -
         vsum(1..k) (\i. vsum(1..dimindex(:N))
                          (\q. (christoffel G y (u(k + 1)) (u i))$q %
                               lift(tf y (\j. if j = i then basis q else u j))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lnabla; LIFT_SUB; LIFT_DROP; LIFT_SUM] THEN
  BINOP_TAC THENL
   [MATCH_MP_TAC P2CI_FD_EXPAND THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `S:real^N->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG; o_THM] THEN
    STRIP_TAC THEN MATCH_MP_TAC P2CI_SLOT_EXPAND_LIFT THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `S:real^N->bool`] THEN ASM_REWRITE_TAC[]]);;

(* Families of tensor fields whose components tend to 0 near z0. *)

let p2ci_tnear = new_definition
 `p2ci_tnear k (z0:real^N) (tfs:num->real^N->(num->real^N)->real) <=>
    (?r N. &0 < r /\
           !n. N <= n ==> ltensor_field k (ball(z0,r)) (tfs n) /\
                          !u. smooth_map_on (ball(z0,r)) (\y. lift(tfs n y u))) /\
    !u. p2ci_near z0 (\n y. lift(tfs n y u)) (\y. vec 0)`;;

let P2CI_TNEAR_LNABLA = prove
 (`!U (G0:real^N->real^N^N) k z0 tfs.
     metric_field U G0 /\ z0 IN U /\ p2ci_tnear k z0 tfs
     ==> p2ci_tnear (k + 1) z0 (\n. lnabla k G0 (tfs n))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2ci_tnear] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `N0:num` STRIP_ASSUME_TAC))
                     (LABEL_TAC "near")))) THEN
  SUBGOAL_THEN `?r1. &0 < r1 /\ ball(z0:real^N,r1) SUBSET U` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field; OPEN_CONTAINS_BALL]; ALL_TAC] THEN
  ABBREV_TAC `s = min r r1` THEN
  SUBGOAL_THEN `&0 < s /\ ball(z0:real^N,s) SUBSET ball(z0,r) /\ ball(z0:real^N,s) SUBSET U`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(z0:real^N,r1)` THEN
      CONJ_TAC THENL [MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (ball(z0:real^N,s)) G0` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n:num. N0 <= n
        ==> ltensor_field k (ball(z0:real^N,s))
              ((tfs:num->real^N->(num->real^N)->real) n) /\
            !u. smooth_map_on (ball(z0,s)) (\y. lift(tfs n y u))`
  (LABEL_TAC "fld") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `ltensor_field k (ball(z0:real^N,r)) (tfs (n:num))` THEN
      REWRITE_TAC[ltensor_field] THEN ASM_MESON_TAC[SUBSET];
      GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `ball(z0:real^N,r)` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`s:real`; `N0:num`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC LNABLA_TENSOR_FIELD THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `u:num->real^N` THEN
  MATCH_MP_TAC P2CI_NEAR_EQ THEN
  EXISTS_TAC
   `\n y. vsum(1..dimindex(:N))
            (\j. ((u:num->real^N)(k + 1))$j %
                 partial_derivative j
                   (\x. lift((tfs:num->real^N->(num->real^N)->real) n x u)) y) -
          vsum(1..k) (\i. vsum(1..dimindex(:N))
            (\q. (christoffel (G0:real^N->real^N^N) y (u(k + 1)) (u i))$q %
                 lift(tfs n y (\j. if j = i then basis q else u j))))` THEN
  EXISTS_TAC `\y:real^N. vec 0:real^1` THEN
  MAP_EVERY EXISTS_TAC [`s:real`; `N0:num`] THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    MAP_EVERY X_GEN_TAC [`n:num`; `z:real^N`] THEN STRIP_TAC THEN
    MATCH_MP_TAC P2CI_LNABLA_EXPAND THEN EXISTS_TAC `ball(z0:real^N,s)` THEN
    ASM_SIMP_TAC[OPEN_BALL]] THEN
  MATCH_MP_TAC P2CI_ZERO_SUB THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2CI_ZERO_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`z0:real^N`;
                   `\n:num. partial_derivative j
                     (\x. lift((tfs:num->real^N->(num->real^N)->real) n x u))`;
                   `\y:real^N. lift(((u:num->real^N)(k + 1))$j)`; `&1`] P2CI_ZERO_SMUL) THEN
    REWRITE_TAC[LIFT_DROP; SMOOTH_MAP_ON_CONST; REAL_LT_01] THEN
    DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC P2CI_ZERO_PARTIAL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2CI_ZERO_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC P2CI_ZERO_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `q:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`z0:real^N`;
                   `\n:num y:real^N. lift((tfs:num->real^N->(num->real^N)->real) n y
                       (\j. if j = i then basis q else (u:num->real^N) j))`;
                   `\y:real^N. lift((christoffel (G0:real^N->real^N^N) y
                                       ((u:num->real^N)(k + 1)) (u i))$q)`;
                   `s:real`] P2CI_ZERO_SMUL) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(\y. lift((christoffel (G0:real^N->real^N^N) y ((u:num->real^N)(k + 1)) (u i))$q)) =
      (\x:real^N. lift(x$q)) o (\y. christoffel G0 y (u(k + 1)) (u i))`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN REWRITE_TAC[OPEN_BALL; LINEAR_LIFT_COMPONENT] THEN
    MATCH_MP_TAC LRG_CHRISTOFFEL_SMOOTH THEN ASM_REWRITE_TAC[]]);;

let P2CI_TNEAR_ITER = prove
 (`!U (G0:real^N->real^N^N) k z0 tfs.
     metric_field U G0 /\ z0 IN U /\ p2ci_tnear k z0 tfs
     ==> !l. p2ci_tnear (k + l) z0 (\n. lnabla_iter k l G0 (tfs n))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [ASM_REWRITE_TAC[lnabla_iter; ADD_CLAUSES; ETA_AX];
    REWRITE_TAC[lnabla_iter; ADD_CLAUSES; ADD1] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G0:real^N->real^N^N`; `k + l:num`; `z0:real^N`;
                   `\n:num. lnabla_iter k l (G0:real^N->real^N^N)
                              ((tfs:num->real^N->(num->real^N)->real) n)`]
                  P2CI_TNEAR_LNABLA) THEN
    ASM_REWRITE_TAC[]]);;

(* The base case: the difference of the metric forms. *)

let P2CI_LMETRIC2_FIELD = prove
 (`!U (G:real^N->real^N^N).
     open U /\ smooth_map_on U (vectorize o G)
     ==> ltensor_field 2 U (lmetric2 G) /\
         (!u. smooth_map_on U (\y. lift(lmetric2 G y u)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[ltensor_field; lmetric2] THEN X_GEN_TAC `y:real^N` THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN BINOP_TAC THEN TRY AP_TERM_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `u:num->real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `i = 1 \/ i = 2` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN REWRITE_TAC[ARITH] THENL
     [ONCE_REWRITE_TAC[DOT_SYM] THEN REWRITE_TAC[LINEAR_LIFT_DOT];
      SUBGOAL_THEN
       `(\v. lift((u:num->real^N) 1 dot ((G:real^N->real^N^N) y ** v))) =
        (\v. (\x. lift(u 1 dot x)) ((\v. G y ** v) v))`
      SUBST1_TAC THENL [REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC LRG_LINEAR_COMPOSE_LAMBDA THEN
      REWRITE_TAC[LINEAR_LIFT_DOT; MATRIX_VECTOR_MUL_LINEAR]];
    GEN_TAC THEN REWRITE_TAC[lmetric2] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONST; LRG_SMOOTH_MATVEC]]);;

let P2CI_TNEAR_METRIC = prove
 (`!(G0:real^N->real^N^N) (Gs:num->real^N->real^N^N) z0.
     p2ci_near z0 (\n. vectorize o Gs n) (vectorize o G0)
     ==> p2ci_tnear 2 z0 (\n z u. lmetric2 (Gs n) z u - lmetric2 G0 z u)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2ci_tnear] THEN CONJ_TAC THENL
   [FIRST_ASSUM(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC o REWRITE_RULE[p2ci_near]) THEN
    MAP_EVERY EXISTS_TAC [`r:real`; `N:num`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`ball(z0:real^N,r)`; `(Gs:num->real^N->real^N^N) n`] P2CI_LMETRIC2_FIELD) THEN
    MP_TAC(ISPECL [`ball(z0:real^N,r)`; `G0:real^N->real^N^N`] P2CI_LMETRIC2_FIELD) THEN
    ASM_SIMP_TAC[OPEN_BALL] THEN REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC LRG_TENSOR_FIELD_SUB THEN ASM_REWRITE_TAC[ETA_AX];
      REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
      ASM_REWRITE_TAC[OPEN_BALL]];
    ALL_TAC] THEN
  X_GEN_TAC `u:num->real^N` THEN
  SUBGOAL_THEN `linear (\x:real^(N,N)finite_prod. matrify x ** (u:num->real^N) 2)` ASSUME_TAC
  THENL
   [MP_TAC(INST_TYPE [] (LRG_BILINEAR_MATRIFY_MUL:thm)) THEN
    REWRITE_TAC[bilinear] THEN DISCH_THEN(MP_TAC o SPEC `(u:num->real^N) 2` o CONJUNCT2) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`z0:real^N`;
                 `\n:num. (vectorize:real^N^N->real^(N,N)finite_prod) o
                         (Gs:num->real^N->real^N^N) n`;
                 `(vectorize:real^N^N->real^(N,N)finite_prod) o (G0:real^N->real^N^N)`;
                 `\x:real^(N,N)finite_prod. lift((u:num->real^N) 1 dot (matrify x ** u 2))`]
                P2CI_NEAR_LINEAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(\x:real^(N,N)finite_prod. lift((u:num->real^N) 1 dot (matrify x ** u 2))) =
      (\x. (\y. lift(u 1 dot y)) ((\x. matrify x ** u 2) x))`
    SUBST1_TAC THENL [REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC LRG_LINEAR_COMPOSE_LAMBDA THEN ASM_REWRITE_TAC[LINEAR_LIFT_DOT];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP P2CI_NEAR_TO_ZERO) THEN
  REWRITE_TAC[o_THM; MATRIFY_VECTORIZE; lmetric2; LIFT_SUB] THEN
  DISCH_THEN ACCEPT_TAC);;

(* The squared tensor norm and the lck distance. *)

let P2CI_INV_PRODUCT_SMOOTH = prove
 (`!U (G:real^N->real^N^N) k i j.
     metric_field U G /\ i IN index_tuples k (:N) /\ j IN index_tuples k (:N)
     ==> smooth_map_on U (\y. lift(product(1..k) (\m. matrix_inv(G y)$(i m)$(j m))))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [metric_field]) THEN
  SUBGOAL_THEN
   `!a b. 1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
          ==> smooth_map_on U (\y. lift(matrix_inv((G:real^N->real^N^N) y)$a$b))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `\z. matrix_inv((G:real^N->real^N^N) z)`]
           LRG_SMOOTH_VECTORIZE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC LRG_SMOOTH_MATRIX_INV THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[LRG_METRIC_INVERTIBLE];
    ALL_TAC] THEN
  MATCH_MP_TAC LRG_SMOOTH_LIFT_PRODUCT_REAL THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `m:num` THEN
  STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`i:num->num`; `k:num`; `m:num`] LRG_INDEX_TUPLES_RANGE) THEN
  MP_TAC(ISPECL [`j:num->num`; `k:num`; `m:num`] LRG_INDEX_TUPLES_RANGE) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let P2CI_LTNORM2_NEAR = prove
 (`!U (G0:real^N->real^N^N) k z0 tfs.
     metric_field U G0 /\ z0 IN U /\ p2ci_tnear k z0 tfs
     ==> p2ci_near z0 (\n y. lift(ltnorm2 k G0 (tfs n) y)) (\y. vec 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2ci_tnear] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?r1. &0 < r1 /\ ball(z0:real^N,r1) SUBSET U` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field; OPEN_CONTAINS_BALL]; ALL_TAC] THEN
  REWRITE_TAC[ltnorm2; LIFT_SUM; o_DEF] THEN
  MATCH_MP_TAC P2CI_ZERO_VSUM THEN REWRITE_TAC[LRG_INDEX_TUPLES_FINITE] THEN
  X_GEN_TAC `i:num->num` THEN DISCH_TAC THEN
  MATCH_MP_TAC P2CI_ZERO_VSUM THEN REWRITE_TAC[LRG_INDEX_TUPLES_FINITE] THEN
  X_GEN_TAC `j:num->num` THEN DISCH_TAC THEN
  MATCH_MP_TAC P2CI_ZERO_MUL THEN EXISTS_TAC `\y:real^N. vec 0:real^1` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC P2CI_ZERO_MUL THEN
  EXISTS_TAC `\y. lift(product(1..k) (\m. matrix_inv((G0:real^N->real^N^N) y)$(i m)$(j m)))` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC P2CI_NEAR_CONST THEN EXISTS_TAC `r1:real` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2CI_INV_PRODUCT_SMOOTH THEN ASM_REWRITE_TAC[]);;

let P2CI_LCK_NEAR = prove
 (`!U (G0:real^N->real^N^N) (Gs:num->real^N->real^N^N) z0 m.
     metric_field U G0 /\ z0 IN U /\
     p2ci_near z0 (\n. vectorize o Gs n) (vectorize o G0)
     ==> p2ci_near z0 (\n y. lift(lck_dist2 m G0 (Gs n) y)) (\y. vec 0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lck_dist2; LIFT_SUM; o_DEF] THEN
  MATCH_MP_TAC P2CI_ZERO_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `l:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G0:real^N->real^N^N`; `2 + l`; `z0:real^N`;
                 `\n:num. lnabla_iter 2 l (G0:real^N->real^N^N)
                            (\z u. lmetric2 ((Gs:num->real^N->real^N^N) n) z u -
                                   lmetric2 G0 z u)`]
                P2CI_LTNORM2_NEAR) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G0:real^N->real^N^N`; `2`; `z0:real^N`;
                 `\n:num z:real^N u:num->real^N.
                    lmetric2 ((Gs:num->real^N->real^N^N) n) z u - lmetric2 G0 z u`]
                P2CI_TNEAR_ITER) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[P2CI_TNEAR_METRIC];
    DISCH_THEN(ACCEPT_TAC o SPEC `l:num`)]);;

(* Uniformity on compact sets. *)

let P2CI_NEAR_COMPACT = prove
 (`!(K:real^M->bool) (Fs:num->real^M->real^N) f.
     compact K /\ (!z. z IN K ==> p2ci_near z Fs f)
     ==> !e. &0 < e ==> ?N. !n y. N <= n /\ y IN K ==> norm(Fs n y - f y) < e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!z. z IN K ==> ?r N. &0 < r /\
                         !n y. N <= n /\ y IN ball(z:real^M,r)
                               ==> norm((Fs:num->real^M->real^N) n y - f y) < e`
  MP_TAC THENL
   [X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^M`) THEN ASM_REWRITE_TAC[p2ci_near] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `r:real` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `rr:real^M->real` (X_CHOOSE_TAC `NN:real^M->num`)) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COMPACT_EQ_HEINE_BOREL]) THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (\z:real^M. ball(z,rr z)) K`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; OPEN_BALL; SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN EXISTS_TAC `y:real^M` THEN
    ASM_SIMP_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> b /\ a /\ c`] THEN
  REWRITE_TAC[EXISTS_FINITE_SUBSET_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real^M->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `IMAGE (NN:real^M->num) C` num_FINITE) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  EXISTS_TAC `N:num` THEN MAP_EVERY X_GEN_TAC [`n:num`; `y:real^M`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?z:real^M. z IN C /\ y IN ball(z,rr z)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(K:real^M->bool) SUBSET UNIONS (IMAGE (\z:real^M. ball(z,rr z)) C)` THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^M) IN K` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^M` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `rr:real^M->real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `N:num` THEN
  ASM_SIMP_TAC[]);;

let P2CI_LCK_COMPACT = prove
 (`!U (G0:real^N->real^N^N) (Gs:num->real^N->real^N^N) K.
     metric_field U G0 /\ compact K /\ K SUBSET U /\
     (!z. z IN K ==> p2ci_near z (\n. vectorize o Gs n) (vectorize o G0))
     ==> !m e. &0 < e ==> ?N. !n y. N <= n /\ y IN K ==> lck_dist2 m G0 (Gs n) y < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`K:real^N->bool`;
                 `\n:num y:real^N. lift(lck_dist2 m (G0:real^N->real^N^N)
                                      ((Gs:num->real^N->real^N^N) n) y)`;
                 `\y:real^N. vec 0:real^1`] P2CI_NEAR_COMPACT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC P2CI_LCK_NEAR THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM SET_TAC[]; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[VECTOR_SUB_RZERO; NORM_LIFT] THEN
    MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `abs x < e ==> x < e`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Matrix fields.  Convergence near z0 is componentwise; for                 *)
(* vectorized matrix fields it is entrywise.  Products and transposes of     *)
(* convergent matrix fields, Jacobian matrices of convergent maps, and       *)
(* compositions converge; hence pullback metrics mpullback (Rs n) (Gs n)    *)
(* converge to mpullback R G (P2CI_NEAR_MPULLBACK).                          *)
(* ------------------------------------------------------------------------- *)

let P2CI_NEAR_BILINEAR2 = prove
 (`!(bb:real^P->real^Q->real^K) (z0:real^M) (As:num->real^M->real^P) A
    (Bs:num->real^M->real^Q) B.
     bilinear bb /\ p2ci_near z0 As A /\ p2ci_near z0 Bs B
     ==> p2ci_near z0 (\n z. bb (As n z) (Bs n z)) (\z. bb (A z) (B z))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Bb:real` STRIP_ASSUME_TAC o MATCH_MP BILINEAR_BOUNDED_POS) THEN
  MATCH_MP_TAC P2CI_NEAR_BILINEAR THEN EXISTS_TAC `Bb:real` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

let P2CI_NEAR_COMPONENTS = prove
 (`!(z0:real^M) (Fs:num->real^M->real^N) f.
     p2ci_near z0 Fs f <=>
     !k. 1 <= k /\ k <= dimindex(:N)
         ==> p2ci_near z0 (\n y. lift(Fs n y$k)) (\y. lift(f y$k))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`z0:real^M`; `Fs:num->real^M->real^N`; `f:real^M->real^N`;
                   `\x:real^N. lift(x$k)`] P2CI_NEAR_LINEAR) THEN
    ASM_REWRITE_TAC[LINEAR_LIFT_COMPONENT];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`z0:real^M`;
                   `\k:num n:num y:real^M. drop(lift((Fs:num->real^M->real^N) n y$k)) %
                                          (basis k:real^N)`;
                   `\k:num y:real^M. drop(lift((f:real^M->real^N) y$k)) % (basis k:real^N)`;
                   `1..dimindex(:N)`] P2CI_NEAR_VSUM) THEN
    REWRITE_TAC[LIFT_DROP; BASIS_EXPANSION; FINITE_NUMSEG; IN_NUMSEG; ETA_AX] THEN
    DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`z0:real^M`; `\n:num y:real^M. lift((Fs:num->real^M->real^N) n y$k)`;
                   `\y:real^M. lift((f:real^M->real^N) y$k)`;
                   `\x:real^1. drop x % (basis k:real^N)`] P2CI_NEAR_LINEAR) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN REPEAT STRIP_TAC THEN
        VECTOR_ARITH_TAC];
      REWRITE_TAC[LIFT_DROP]]]);;

let P2CI_NEAR_MATRIX = prove
 (`!(z0:real^M) (As:num->real^M->real^N^N) A.
     p2ci_near z0 (\n. vectorize o As n) (vectorize o A) <=>
     !i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
           ==> p2ci_near z0 (\n y. lift(As n y$i$j)) (\y. lift(A y$i$j))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`z0:real^M`;
                   `\n:num. (vectorize:real^N^N->real^(N,N)finite_prod) o
                            (As:num->real^M->real^N^N) n`;
                   `(vectorize:real^N^N->real^(N,N)finite_prod) o (A:real^M->real^N^N)`;
                   `\x:real^(N,N)finite_prod. lift((matrify x:real^N^N)$i$j)`]
                  P2CI_NEAR_LINEAR) THEN
    ASM_REWRITE_TAC[LRG_LINEAR_MATRIFY_ENTRY; o_THM; MATRIFY_VECTORIZE];
    DISCH_TAC THEN GEN_REWRITE_TAC I [P2CI_NEAR_COMPONENTS] THEN
    REWRITE_TAC[DIMINDEX_FINITE_PROD; o_THM] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[VECTORIZE_COMPONENT] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    SUBGOAL_THEN `~(dimindex(:N) = 0)` ASSUME_TAC THENL
     [REWRITE_TAC[DIMINDEX_NONZERO]; ALL_TAC] THEN
    ASM_SIMP_TAC[MOD_LT_EQ; ARITH_RULE `1 <= 1 + a`;
                 ARITH_RULE `1 + a <= n <=> a < n`; RDIV_LT_EQ] THEN
    ASM_ARITH_TAC]);;

let P2CI_NEAR_MATMUL = prove
 (`!(z0:real^M) (As:num->real^M->real^N^N) A (Bs:num->real^M->real^N^N) B.
     p2ci_near z0 (\n. vectorize o As n) (vectorize o A) /\
     p2ci_near z0 (\n. vectorize o Bs n) (vectorize o B)
     ==> p2ci_near z0 (\n. vectorize o (\z. As n z ** Bs n z))
                      (vectorize o (\z. A z ** B z))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\(m1:real^(N,N)finite_prod) (m2:real^(N,N)finite_prod).
                    (vectorize:real^N^N->real^(N,N)finite_prod)
                      ((matrify m1:real^N^N) ** (matrify m2:real^N^N))`;
                 `z0:real^M`;
                 `\n:num. (vectorize:real^N^N->real^(N,N)finite_prod) o
                          (As:num->real^M->real^N^N) n`;
                 `(vectorize:real^N^N->real^(N,N)finite_prod) o (A:real^M->real^N^N)`;
                 `\n:num. (vectorize:real^N^N->real^(N,N)finite_prod) o
                          (Bs:num->real^M->real^N^N) n`;
                 `(vectorize:real^N^N->real^(N,N)finite_prod) o (B:real^M->real^N^N)`]
                P2CI_NEAR_BILINEAR2) THEN
  ASM_REWRITE_TAC[LRG_BILINEAR_MATRIX_MUL] THEN
  REWRITE_TAC[o_DEF; MATRIFY_VECTORIZE]);;

let P2CI_NEAR_TRANSP = prove
 (`!(z0:real^M) (As:num->real^M->real^N^N) A.
     p2ci_near z0 (\n. vectorize o As n) (vectorize o A)
     ==> p2ci_near z0 (\n. vectorize o (\z. transp(As n z)))
                      (vectorize o (\z. transp(A z)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`z0:real^M`;
                 `\n:num. (vectorize:real^N^N->real^(N,N)finite_prod) o
                          (As:num->real^M->real^N^N) n`;
                 `(vectorize:real^N^N->real^(N,N)finite_prod) o (A:real^M->real^N^N)`;
                 `\x:real^(N,N)finite_prod.
                    (vectorize:real^N^N->real^(N,N)finite_prod) (transp(matrify x:real^N^N))`]
                P2CI_NEAR_LINEAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[linear; MATRIFY_ADD; MATRIFY_CMUL; TRANSP_MATRIX_ADD;
                    TRANSP_MATRIX_CMUL; VECTORIZE_ADD; VECTORIZE_CMUL];
    REWRITE_TAC[o_DEF; MATRIFY_VECTORIZE]]);;

let P2CI_NEAR_JACOBIAN = prove
 (`!(z0:real^N) (Rs:num->real^N->real^N) R.
     p2ci_near z0 Rs R
     ==> p2ci_near z0 (\n. vectorize o (\z. matrix(frechet_derivative (Rs n) (at z))))
                      (vectorize o (\z. matrix(frechet_derivative R (at z))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[P2CI_NEAR_MATRIX] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MATRIX_COMPONENT] THEN REWRITE_TAC[GSYM partial_derivative] THEN
  MP_TAC(ISPECL [`z0:real^N`; `\n:num. partial_derivative j ((Rs:num->real^N->real^N) n)`;
                 `partial_derivative j (R:real^N->real^N)`;
                 `\x:real^N. lift(x$i)`] P2CI_NEAR_LINEAR) THEN
  REWRITE_TAC[LINEAR_LIFT_COMPONENT] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC P2CI_NEAR_PARTIAL THEN ASM_REWRITE_TAC[]);;

let P2CI_NEAR_COMPOSE_MATRIX = prove
 (`!(z0:real^M) (Rs:num->real^M->real^P) R (Gs:num->real^P->real^N^N) G.
     p2ci_near z0 Rs R /\ p2ci_near (R z0) (\n. vectorize o Gs n) (vectorize o G)
     ==> p2ci_near z0 (\n. vectorize o (\z. Gs n (Rs n z))) (vectorize o (\z. G(R z)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`z0:real^M`; `Rs:num->real^M->real^P`; `R:real^M->real^P`;
                 `\n:num. (vectorize:real^N^N->real^(N,N)finite_prod) o
                          (Gs:num->real^P->real^N^N) n`;
                 `(vectorize:real^N^N->real^(N,N)finite_prod) o (G:real^P->real^N^N)`]
                P2CI_NEAR_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[o_DEF]);;

let P2CI_NEAR_MPULLBACK = prove
 (`!(z0:real^N) (Rs:num->real^N->real^N) R (Gs:num->real^N->real^N^N) G.
     p2ci_near z0 Rs R /\ p2ci_near (R z0) (\n. vectorize o Gs n) (vectorize o G)
     ==> p2ci_near z0 (\n. vectorize o mpullback (Rs n) (Gs n))
                      (vectorize o mpullback R G)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!(h:real^N->real^N) (H:real^N->real^N^N).
      mpullback h H = \y. transp(matrix(frechet_derivative h (at y))) **
                          H(h y) ** matrix(frechet_derivative h (at y))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM; mpullback]; ALL_TAC] THEN
  MATCH_MP_TAC P2CI_NEAR_MATMUL THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2CI_NEAR_TRANSP THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC P2CI_NEAR_JACOBIAN THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2CI_NEAR_MATMUL THEN REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2CI_NEAR_COMPOSE_MATRIX THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2CI_NEAR_JACOBIAN THEN ASM_REWRITE_TAC[]]]);;

