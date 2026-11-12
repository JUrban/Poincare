(* ========================================================================= *)
(* pc_moi_lt_gpb2: general position for the loop theorem (Moise p.184),      *)
(* from the chart step to the crossings.  Main theorem (statements of        *)
(* pc_moi_lt_gpbstmt.ml):                                                    *)
(*   GP_FROM_STEP = MOI_LGB_GP_FROM_STEP                                      *)
(*                = MOI_LGB_CHART_STEP ==> MOI_LT2_GP_CROSSINGS              *)
(* The chart step is the antecedent (proved in pc_moi_lt_gpb1); this file   *)
(* builds the adapted atlas, starts from the pulled-back triangulation,     *)
(* iterates the chart step over the atlas and reads off the crossings.      *)
(* ========================================================================= *)

let moi_lgb2_saved_interface = !the_interface;;
needs "Multivariate/cross.ml";;
the_interface := moi_lgb2_saved_interface;;
needs "src/pc_moi_lt_gpbstmt.ml";;
needs "src/pc_moi_lt_gpa.ml";;
needs "src/pc_moi_lt_charts.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Helpers for the adapted atlas.  Finite lf complexes are                  *)
(* simplicial complexes; iterated barycentric subdivisions refine; unions   *)
(* of refinements compose; a PL map is affine on finitely many polytopes    *)
(* covering a compact subset of its domain.                                 *)
(* ========================================================================= *)

let MOI_LGB2_LF_FINITE_SC = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ lf_simplicial_complex c ==> simplicial_complex c`,
  REWRITE_TAC[simplicial_complex; lf_simplicial_complex] THEN MESON_TAC[]);;

let MOI_LGB2_UNION_OF_TRANS = prove
 (`!(a:(real^N->bool)->bool) b c.
     (!t. t IN a ==> ?f. f SUBSET b /\ t = UNIONS f) /\
     (!t. t IN b ==> ?f. f SUBSET c /\ t = UNIONS f)
     ==> !t. t IN a ==> ?f. f SUBSET c /\ t = UNIONS f`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `{r:real^N->bool | r IN c /\ r SUBSET t}` THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real^N->bool` o check (fun th ->
    can (find_term ((=) `a:(real^N->bool)->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `?r:real^N->bool. r IN f /\ x IN r` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN t` THEN
    UNDISCH_TAC `t:real^N->bool = UNIONS f` THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[IN_UNIONS];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:real^N->bool` o check (fun th ->
    can (find_term ((=) `b:(real^N->bool)->bool`)) (concl th) &&
    is_forall (concl th))) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?q:real^N->bool. q IN g /\ x IN q` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN r` THEN
    UNDISCH_TAC `r:real^N->bool = UNIONS g` THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[IN_UNIONS];
    ALL_TAC] THEN
  EXISTS_TAC `q:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `t:real^N->bool = UNIONS f` THEN
  UNDISCH_TAC `r:real^N->bool = UNIONS g` THEN
  UNDISCH_TAC `(q:real^N->bool) IN g` THEN UNDISCH_TAC `(r:real^N->bool) IN f` THEN
  SET_TAC[]);;

let MOI_LGB2_ITER_BARY = prove
 (`!c:(real^N->bool)->bool.
     simplicial_complex c
     ==> !n. simplicial_complex (ITER n barycentric_subdivision c) /\
             UNIONS (ITER n barycentric_subdivision c) = UNIONS c /\
             (!s. s IN ITER n barycentric_subdivision c /\ ~(s = {})
                  ==> ?s'. s' IN c /\ s SUBSET s') /\
             (!s'. s' IN c
                   ==> ?f. f SUBSET ITER n barycentric_subdivision c /\
                           s' = UNIONS f)`,
  GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN REWRITE_TAC[ITER] THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MESON_TAC[SUBSET_REFL];
      X_GEN_TAC `s':real^N->bool` THEN DISCH_TAC THEN
      EXISTS_TAC `{s':real^N->bool}` THEN REWRITE_TAC[UNIONS_1] THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `b = ITER n barycentric_subdivision (c:(real^N->bool)->bool)` THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  SUBGOAL_THEN `lf_simplicial_complex (b:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FMB_SC_LF]; ALL_TAC] THEN
  MP_TAC(ISPEC `b:(real^N->bool)->bool` BARYCENTRIC_SUBDIVISION_REFINES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_SIMPLICIAL_COMPLEX;
               UNIONS_BARYCENTRIC_SUBDIVISION] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool` o check (fun th ->
      can (find_term ((=) `{}:real^N->bool`)) (concl th) &&
      can (find_term ((=) `barycentric_subdivision:((real^N->bool)->bool)->
                                                     (real^N->bool)->bool`))
        (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real^N->bool` o check (fun th ->
      can (find_term ((=) `{}:real^N->bool`)) (concl th) &&
      can (find_term ((=) `c:(real^N->bool)->bool`)) (concl th))) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[];
    MATCH_MP_TAC MOI_LGB2_UNION_OF_TRANS THEN
    EXISTS_TAC `b:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]]);;

let MOI_LGB2_COMPACT_PL_PIECES = prove
 (`!(s:real^M->bool) u (f:real^M->real^N).
        compact s /\ s SUBSET u /\ pl_map_on u f
        ==> ?d. FINITE d /\ s SUBSET UNIONS d /\
                !k. k IN d ==> polytope k /\ k SUBSET u /\
                               ?l y. linear l /\ !z. z IN k ==> f z = l z + y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_map_on] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]))) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real^M->(real^M->bool)->bool`
    (X_CHOOSE_TAC `U:real^M->real^M->bool`)) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COMPACT_EQ_HEINE_BOREL]) THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (U:real^M->real^M->bool) s`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^M->real^M->bool`; `s:real^M->bool`;
                 `v:(real^M->bool)->bool`] FINITE_SUBSET_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:real^M->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `UNIONS (IMAGE (C:real^M->(real^M->bool)->bool) s0)` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[FINITE_UNIONS; FORALL_IN_IMAGE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[SUBSET]];
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?x:real^M. x IN s0 /\ y IN (U:real^M->real^M->bool) x`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `s SUBSET UNIONS (v:(real^M->bool)->bool)` THEN
      ASM_REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^M`) THEN ASM_REWRITE_TAC[] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^M) IN u /\ (y:real^M) IN u` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(y:real^M) IN UNIONS ((C:real^M->(real^M->bool)->bool) x)`
    MP_TAC THENL
     [SUBGOAL_THEN
       `u INTER (U:real^M->real^M->bool) x SUBSET
        UNIONS ((C:real^M->(real^M->bool)->bool) x)`
      MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM SET_TAC[];
      REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN ASM_MESON_TAC[]];
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN ASM_MESON_TAC[SUBSET]]);;

let MOI_LGB2_HALF_CBALL_COMPACT = prove
 (`!(K:real^3->bool) r.
     (K = ball(vec 0,&1) \/ K = ball(vec 0,&1) INTER {z:real^3 | &0 <= z$3}) /\
     r < &1
     ==> compact {z | z IN K /\ norm z <= r}`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 DISJ_CASES_TAC ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `{z:real^3 | z IN ball(vec 0,&1) /\ norm z <= r} = cball(vec 0,r)`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_BALL_0; IN_CBALL_0] THEN
      GEN_TAC THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[COMPACT_CBALL]];
    SUBGOAL_THEN
     `{z:real^3 | z IN ball(vec 0,&1) INTER {z | &0 <= z$3} /\ norm z <= r} =
      cball(vec 0,r) INTER {z | z$3 >= &0}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_BALL_0; IN_CBALL_0;
                  real_ge] THEN
      GEN_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
      REWRITE_TAC[COMPACT_CBALL; CLOSED_HALFSPACE_COMPONENT_GE]]]);;

let MOI_LGB2_CHART_PREIMAGE = prove
 (`!(u:real^N->bool) (h:real^N->real^3) h' r.
     pl_homeomorphism (u,IMAGE h u) (h,h') /\
     (IMAGE h u = ball(vec 0,&1) \/
      IMAGE h u = ball(vec 0,&1) INTER {z:real^3 | &0 <= z$3}) /\ r < &1
     ==> compact {p | p IN u /\ norm(h p) <= r} /\
         open_in (subtopology euclidean u) {p | p IN u /\ norm(h p) < r}`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  SUBGOAL_THEN `homeomorphism (u,IMAGE h u) ((h:real^N->real^3),h')` MP_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `{p | p IN u /\ norm((h:real^N->real^3) p) <= r} =
      IMAGE h' {z | z IN IMAGE h u /\ norm z <= r}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN X_GEN_TAC `p:real^N` THEN
      EQ_TAC THENL
       [STRIP_TAC THEN EXISTS_TAC `(h:real^N->real^3) p` THEN ASM_SIMP_TAC[] THEN
        ASM_MESON_TAC[];
        DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[IN_IMAGE]];
      ALL_TAC] THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (h:real^N->real^3) u` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC MOI_LGB2_HALF_CBALL_COMPACT THEN ASM_MESON_TAC[]];
    SUBGOAL_THEN
     `{p | p IN u /\ norm((h:real^N->real^3) p) < r} =
      {p | p IN u /\ h p IN ball(vec 0,r)}`
    SUBST1_TAC THENL [REWRITE_TAC[IN_BALL_0]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN
    ASM_REWRITE_TAC[OPEN_BALL]]);;

let MOI_LGB2_UNIONS_C_COMPACT = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c ==> compact(UNIONS c)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPACT_UNIONS THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FM3_LF_COMPACT THEN
  EXISTS_TAC `c:(real^N->bool)->bool` THEN
  ASM_MESON_TAC[combinatorial_manifold_with_boundary]);;

let MOI_LGB2_CHART_CORE = prove
 (`!(c:(real^N->bool)->bool) y.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\ y IN UNIONS c
     ==> ?u (h:real^N->real^3) h' kk V C dl.
           open_in (subtopology euclidean (UNIONS c)) u /\
           pl_homeomorphism (u,IMAGE h u) (h,h') /\
           ((u INTER complex_boundary c = {} /\ IMAGE h u = ball(vec 0,&1)) \/
            (IMAGE h u = ball(vec 0,&1) INTER {z:real^3 | &0 <= z$3} /\
             IMAGE h (u INTER complex_boundary c) =
             IMAGE h u INTER {z:real^3 | z$3 = &0})) /\
           compact kk /\ kk SUBSET u /\
           open_in (subtopology euclidean (UNIONS c)) V /\ y IN V /\
           V SUBSET kk /\ compact C /\ C SUBSET u /\ &0 < dl /\
           (!z k. z IN UNIONS c /\ k IN kk /\ dist(z,k) < dl ==> z IN C)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `y:real^N`; `&1`] MANIFOLD_CHARTS) THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `h:real^N->real^3`
    (X_CHOOSE_THEN `h':real^3->real^N` (MAP_EVERY ASSUME_TAC o CONJUNCTS)))) THEN
  SUBGOAL_THEN
   `(u INTER complex_boundary c = {} /\ IMAGE (h:real^N->real^3) u = ball(vec 0,&1)) \/
    (IMAGE h u = ball(vec 0,&1) INTER {z:real^3 | &0 <= z$3} /\
     IMAGE h (u INTER complex_boundary c) = IMAGE h u INTER {z:real^3 | z$3 = &0})`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (h:real^N->real^3) u = ball(vec 0,&1) \/
    IMAGE h u = ball(vec 0,&1) INTER {z:real^3 | &0 <= z$3}`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                 `&1 / &2`] MOI_LGB2_CHART_PREIMAGE) THEN
  MP_TAC(ISPECL [`u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                 `&3 / &4`] MOI_LGB2_CHART_PREIMAGE) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  STRIP_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `W = {p | p IN u /\ norm((h:real^N->real^3) p) < &3 / &4}` THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (UNIONS c)) (W:real^N->bool)`
  ASSUME_TAC THENL [ASM_MESON_TAC[OPEN_IN_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `closed(UNIONS c DIFF W:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_IN_CLOSED_TRANS THEN
    EXISTS_TAC `UNIONS c:real^N->bool` THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; MOI_LGB2_UNIONS_C_COMPACT] THEN
    MATCH_MP_TAC CLOSED_IN_DIFF THEN ASM_REWRITE_TAC[CLOSED_IN_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{p | p IN u /\ norm((h:real^N->real^3) p) <= &1 / &2}`;
                 `UNIONS c DIFF W:real^N->bool`] SEPARATE_COMPACT_CLOSED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "W" THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_DIFF; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:real^N` THEN ASM_CASES_TAC `(x:real^N) IN u` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC
   [`u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
    `{p | p IN u /\ norm((h:real^N->real^3) p) <= &1 / &2}`;
    `{p | p IN u /\ norm((h:real^N->real^3) p) < &1 / &2}`;
    `{p | p IN u /\ norm((h:real^N->real^3) p) <= &3 / &4}`; `dl:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SET_TAC[];
    ASM_MESON_TAC[OPEN_IN_TRANS];
    ASM_REWRITE_TAC[IN_ELIM_THM; NORM_0] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE];
    SET_TAC[];
    MAP_EVERY X_GEN_TAC [`z:real^N`; `k:real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^N) IN W` MP_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`k:real^N`; `z:real^N`]) THEN
      ASM_REWRITE_TAC[IN_DIFF] THEN
      UNDISCH_TAC `dist(z:real^N,k) < dl` THEN
      MP_TAC(ISPECL [`z:real^N`; `k:real^N`] DIST_SYM) THEN REAL_ARITH_TAC;
      EXPAND_TAC "W" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      MESON_TAC[REAL_LT_IMP_LE; REAL_ARITH `x < &3 / &4 ==> x <= &3 / &4`]]]);;

let MOI_LGB2_FINITE_MIN_POS = prove
 (`!(Y:A->bool) (f:A->real).
     FINITE Y /\ (!y. y IN Y ==> &0 < f y)
     ==> ?e. &0 < e /\ !y. y IN Y ==> e <= f y`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `Y:A->bool = {}` THENL
   [ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN MESON_TAC[REAL_LT_01]; ALL_TAC] THEN
  STRIP_TAC THEN EXISTS_TAC `inf (IMAGE (f:A->real) Y)` THEN
  ASM_SIMP_TAC[REAL_LT_INF_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[REAL_INF_LE_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY; EXISTS_IN_IMAGE] THEN
  EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[REAL_LE_REFL]);;

let MOI_LGB2_MARGIN = prove
 (`!(tt:(real^N->bool)->bool) kk C D (u:real^N->bool) (h:real^N->real^3) X e dl.
     simplicial_complex tt /\ UNIONS tt = X /\
     (!s. s IN tt ==> diameter s < e) /\ &3 * e <= dl /\
     (!z k. z IN X /\ k IN kk /\ dist(z,k) < dl ==> z IN C) /\
     C SUBSET u /\ C SUBSET UNIONS D /\
     (!k. k IN D ==> (?l y. linear l /\ !z. z IN k ==> h z = l z + y) /\
                     ?f. f SUBSET tt /\ k = UNIONS f)
     ==> !s1 s2 s3. s1 IN tt /\ s2 IN tt /\ s3 IN tt /\ ~(s1 INTER kk = {}) /\
                    ~(s1 INTER s2 = {}) /\ ~(s2 INTER s3 = {})
                    ==> s3 SUBSET u /\
                        ?l y. linear l /\ !x. x IN s3 ==> h x = l x + y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN tt ==> bounded s /\ convex s`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_CON_SC_CONVEX; MOI_FMB_SC_LF; MOI_FM3_LF_COMPACT;
                  COMPACT_IMP_BOUNDED];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s3:real^N->bool) SUBSET C` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    UNDISCH_TAC `~(s1 INTER kk:real^N->bool = {})` THEN
    UNDISCH_TAC `~(s1 INTER s2:real^N->bool = {})` THEN
    UNDISCH_TAC `~(s2 INTER s3:real^N->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `z2:real^N` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `z1:real^N` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^N` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `dl:real`)) (concl th) && is_forall (concl th))) THEN
    EXISTS_TAC `k:real^N` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `UNIONS tt:real^N->bool = X` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `dist(z:real^N,z2) < e /\ dist(z2:real^N,z1) < e /\
                  dist(z1:real^N,k) < e`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[dist] THEN REPEAT CONJ_TAC THEN
      MATCH_MP_TAC REAL_LET_TRANS THENL
       [EXISTS_TAC `diameter(s3:real^N->bool)`;
        EXISTS_TAC `diameter(s2:real^N->bool)`;
        EXISTS_TAC `diameter(s1:real^N->bool)`] THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC DIAMETER_BOUNDED_BOUND THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`z:real^N`; `z2:real^N`; `z1:real^N`] DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`z:real^N`; `z1:real^N`; `k:real^N`] DIST_TRIANGLE) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(relative_interior (s3:real^N->bool) = {})` MP_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `z:real^N` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  SUBGOAL_THEN `(z:real^N) IN s3` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `?k:real^N->bool. k IN D /\ z IN k` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:real^N->bool` o check (fun th ->
    can (find_term ((=) `D:(real^N->bool)->bool`)) (concl th) &&
    is_forall (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `l:real^N->real^3` (X_CHOOSE_THEN `y:real^3`
      STRIP_ASSUME_TAC))
    (X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `?s':real^N->bool. s' IN f /\ z IN s'` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^N) IN k` THEN
    UNDISCH_TAC `k:real^N->bool = UNIONS f` THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[IN_UNIONS];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s3:real^N->bool) SUBSET s'` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SCF_RELINT_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `z:real^N`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`l:real^N->real^3`; `y:real^3`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `k:real^N->bool = UNIONS f` THEN DISCH_THEN SUBST1_TAC THEN
  ASM SET_TAC[]);;

let MOI_LGB2_CORE_COVER = prove
 (`!(c:(real^N->bool)->bool) ks (VV:real^N->real^N->bool).
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     compact ks /\ ks SUBSET UNIONS c /\
     (!y. y IN UNIONS c
          ==> open_in (subtopology euclidean (UNIONS c)) (VV y) /\ y IN VV y)
     ==> ?Y r. FINITE Y /\ Y SUBSET UNIONS c /\ &0 < r /\
               !x z. x IN UNIONS c /\ z IN ks /\ dist(x,z) < r
                     ==> ?y. y IN Y /\ x IN VV y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COMPACT_EQ_HEINE_BOREL_SUBTOPOLOGY]) THEN
  DISCH_THEN(MP_TAC o SPEC
    `IMAGE (\y:real^N. ks INTER (VV:real^N->real^N->bool) y) (UNIONS c)`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE] THEN CONJ_TAC THENL
     [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      MATCH_MP_TAC OPEN_IN_SUBTOPOLOGY_INTER_SUBSET THEN
      EXISTS_TAC `UNIONS c:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `UNIONS c INTER (VV:real^N->real^N->bool) y = VV y`
      SUBST1_TAC THENL
       [MATCH_MP_TAC(SET_RULE `!a b:real^N->bool. b SUBSET a ==> a INTER b = b`) THEN
        MATCH_MP_TAC OPEN_IN_IMP_SUBSET THEN
        EXISTS_TAC `euclidean:(real^N)topology` THEN ASM_SIMP_TAC[];
        ASM_SIMP_TAC[]];
      REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(z:real^N) IN UNIONS c` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(z:real^N) IN (VV:real^N->real^N->bool) z` ASSUME_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_UNIONS] THEN
      EXISTS_TAC `ks INTER (VV:real^N->real^N->bool) z` THEN
      ASM_REWRITE_TAC[IN_INTER] THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `z:real^N` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`\y:real^N. ks INTER (VV:real^N->real^N->bool) y`;
                 `UNIONS c:real^N->bool`; `f':(real^N->bool)->bool`]
    FINITE_SUBSET_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Y:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  SUBGOAL_THEN `ks SUBSET UNIONS (IMAGE (VV:real^N->real^N->bool) Y)` ASSUME_TAC THENL
   [UNDISCH_TAC `ks SUBSET UNIONS (f':(real^N->bool)->bool)` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE; IN_INTER] THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `W = UNIONS (IMAGE (VV:real^N->real^N->bool) Y)` THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (UNIONS c)) (W:real^N->bool)`
  ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN MATCH_MP_TAC OPEN_IN_UNIONS THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed(UNIONS c DIFF W:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_IN_CLOSED_TRANS THEN
    EXISTS_TAC `UNIONS c:real^N->bool` THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; MOI_LGB2_UNIONS_C_COMPACT] THEN
    MATCH_MP_TAC CLOSED_IN_DIFF THEN ASM_REWRITE_TAC[CLOSED_IN_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ks:real^N->bool`; `UNIONS c DIFF W:real^N->bool`]
    SEPARATE_COMPACT_CLOSED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ks SUBSET (W:real^N->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`Y:real^N->bool`; `r:real`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `z:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^N) IN W` MP_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`z:real^N`; `x:real^N`] o check (fun th ->
      can (find_term ((=) `r:real`)) (concl th) && is_forall (concl th))) THEN
    ASM_REWRITE_TAC[IN_DIFF] THEN
    UNDISCH_TAC `dist(x:real^N,z) < r` THEN
    MP_TAC(ISPECL [`x:real^N`; `z:real^N`] DIST_SYM) THEN REAL_ARITH_TAC;
    EXPAND_TAC "W" THEN REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN MESON_TAC[]]);;

(* ========================================================================= *)
(* The adapted atlas exists (the term MOI_LGB_ATLAS_EXISTS).                *)
(* Charts with compact cores at all points (CHART_CORE), a finite subcover  *)
(* of ks and the radius r (CORE_COVER), the PL pieces of the charts on      *)
(* their collars (COMPACT_PL_PIECES), a common simplicial refinement of t   *)
(* and the pieces (SIMPLICIAL_COMPLEX_REFINE_POLYTOPES), iterated           *)
(* barycentric subdivision below a third of the collar radii (MARGIN).      *)
(* ========================================================================= *)

let MOI_LGB2_ATLAS = prove
 (MOI_LGB_ATLAS_EXISTS,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `UNIONS c:real^N->bool = {}` THENL
   [MAP_EVERY EXISTS_TAC
     [`{}:(real^N->bool)->bool`;
      `{}:((real^N->bool)#(real^N->real^3)#(real^3->real^N)#(real^N->bool))->bool`;
      `&1`] THEN
    ASM_REWRITE_TAC[moi_lgb_atlas; simplicial_complex; FINITE_EMPTY; NOT_IN_EMPTY;
                    UNIONS_0; INTER_EMPTY; REAL_LT_01] THEN
    MESON_TAC[EMPTY_SUBSET; UNIONS_0];
    ALL_TAC] THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_LGB2_CHART_CORE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `U:real^N->real^N->bool`
    (X_CHOOSE_THEN `H:real^N->real^N->real^3`
    (X_CHOOSE_THEN `H':real^N->real^3->real^N`
    (X_CHOOSE_THEN `KK:real^N->real^N->bool`
    (X_CHOOSE_THEN `VV:real^N->real^N->bool`
    (X_CHOOSE_THEN `CC:real^N->real^N->bool`
    (X_CHOOSE_THEN `DL:real^N->real` (LABEL_TAC "ch")))))))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `ks:real^N->bool`;
                 `VV:real^N->real^N->bool`] MOI_LGB2_CORE_COVER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    USE_THEN "ch" (MP_TAC o SPEC `y:real^N`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Y:real^N->bool` (X_CHOOSE_THEN `r:real`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!y:real^N. y IN Y
        ==> ?d. FINITE d /\ CC y SUBSET UNIONS d /\
                !k. k IN d ==> polytope k /\ k SUBSET (U:real^N->real^N->bool) y /\
                               ?l b. linear l /\
                                     !z. z IN k ==> (H:real^N->real^N->real^3) y z =
                                                    l z + b`
  MP_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_LGB2_COMPACT_PL_PIECES THEN REWRITE_TAC[ETA_AX] THEN
    USE_THEN "ch" (MP_TAC o SPEC `y:real^N`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SIMP_TAC[pl_homeomorphism];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `D:real^N->(real^N->bool)->bool` (LABEL_TAC "pc")) THEN
  SUBGOAL_THEN `simplicial_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_LGB2_LF_FINITE_SC]; ALL_TAC] THEN
  UNDISCH_TAC `subdivides (t:(real^N->bool)->bool) c` THEN
  REWRITE_TAC[subdivides] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`;
                 `UNIONS (IMAGE (D:real^N->(real^N->bool)->bool) Y)`]
    SIMPLICIAL_COMPLEX_REFINE_POLYTOPES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[FINITE_UNIONS; FORALL_IN_IMAGE] THEN
      ASM_SIMP_TAC[FINITE_IMAGE] THEN ASM_MESON_TAC[];
      REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN
      X_GEN_TAC `k:real^N->bool` THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
      USE_THEN "pc" (MP_TAC o C MATCH_MP (ASSUME `(y:real^N) IN Y`) o
                     SPEC `y:real^N`) THEN
      DISCH_THEN(MP_TAC o SPEC `k:real^N->bool` o CONJUNCT2 o CONJUNCT2) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      USE_THEN "ch" (MP_TAC o SPEC `y:real^N`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN
      DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`Y:real^N->bool`; `\y:real^N. (DL:real^N->real) y / &3`]
    MOI_LGB2_FINITE_MIN_POS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> &0 < x / &3`) THEN
    USE_THEN "ch" (MP_TAC o SPEC `y:real^N`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t1:(real^N->bool)->bool`; `e:real`]
    ITERATED_BARYCENTRIC_SUBDIVISION_FINE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  MP_TAC(ISPEC `t1:(real^N->bool)->bool` MOI_LGB2_ITER_BARY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
  ABBREV_TAC `tt = ITER n barycentric_subdivision (t1:(real^N->bool)->bool)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~(c:(real^N->bool)->bool = {}) /\ ~(t:(real^N->bool)->bool = {}) /\
                ~(t1:(real^N->bool)->bool = {})`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `~(UNIONS c:real^N->bool = {})` THEN ASM_REWRITE_TAC[UNIONS_0] THEN
    ASM_MESON_TAC[UNIONS_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN tt ==> ?s'. s' IN t1 /\ s SUBSET s'`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    ASM_CASES_TAC `s:real^N->bool = {}` THENL
     [UNDISCH_TAC `~(t1:(real^N->bool)->bool = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN ASM_MESON_TAC[EMPTY_SUBSET];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN tt ==> ?s'. s' IN t /\ s SUBSET s'`
  ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN tt ==> ?s'. s' IN c /\ s SUBSET s'`
  ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN t ==> ?f. f SUBSET tt /\ s = UNIONS f`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LGB2_UNION_OF_TRANS THEN
    EXISTS_TAC `t1:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN c ==> ?f. f SUBSET tt /\ s = UNIONS f`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LGB2_UNION_OF_TRANS THEN
    EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k:real^N->bool. k IN UNIONS (IMAGE (D:real^N->(real^N->bool)->bool) Y)
                     ==> ?f. f SUBSET tt /\ k = UNIONS f`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LGB2_UNION_OF_TRANS THEN
    EXISTS_TAC `t1:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS tt:real^N->bool = UNIONS c` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`tt:(real^N->bool)->bool`;
    `IMAGE (\y:real^N. ((U:real^N->real^N->bool) y,
                        (H:real^N->real^N->real^3) y,
                        (H':real^N->real^3->real^N) y,
                        (KK:real^N->real^N->bool) y)) Y`;
    `r:real`] THEN
  ASM_REWRITE_TAC[moi_lgb_atlas] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool` o check (fun th ->
      can (find_term ((=) `c:(real^N->bool)->bool`)) (concl th) &&
      can (find_term ((=) `tt:(real^N->bool)->bool`)) (concl th) &&
      is_forall (concl th) &&
      can (find_term ((=) `UNIONS:((real^N->bool)->bool)->real^N->bool`))
        (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `f:(real^N->bool)->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `s:real^N->bool = UNIONS f` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `(s:real^N->bool) IN c` THEN SET_TAC[];
    ASM_SIMP_TAC[FINITE_IMAGE];
    REWRITE_TAC[IN_IMAGE; PAIR_EQ] THEN
    MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `h:real^N->real^3`;
                         `h':real^3->real^N`; `kk:real^N->bool`] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "ch" (MP_TAC o SPEC `y:real^N`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_LGB2_MARGIN THEN
    MAP_EVERY EXISTS_TAC [`(CC:real^N->real^N->bool) y`;
                          `(D:real^N->(real^N->bool)->bool) y`;
                          `UNIONS c:real^N->bool`; `e:real`;
                          `(DL:real^N->real) y`] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "pc" (MP_TAC o C MATCH_MP (ASSUME `(y:real^N) IN Y`) o
                   SPEC `y:real^N`) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `x <= d / &3 ==> &3 * x <= d`) THEN ASM_SIMP_TAC[];
      X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN CONJ_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `D:real^N->(real^N->bool)->bool`)) (concl th) &&
        can (find_term ((=) `tt:(real^N->bool)->bool`)) (concl th))) THEN
      REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN ASM_MESON_TAC[]];
    X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool` o check (fun th ->
      can (find_term ((=) `t:(real^N->bool)->bool`)) (concl th) &&
      can (find_term ((=) `tt:(real^N->bool)->bool`)) (concl th) &&
      is_forall (concl th) &&
      can (find_term ((=) `UNIONS:((real^N->bool)->bool)->real^N->bool`))
        (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `f:(real^N->bool)->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `s:real^N->bool = UNIONS f` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `(s:real^N->bool) IN t` THEN
    UNDISCH_TAC `UNIONS t:real^N->bool = UNIONS c` THEN SET_TAC[];
    MAP_EVERY X_GEN_TAC [`x:real^N`; `z:real^N`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `z:real^N`] o check (fun th ->
      can (find_term ((=) `VV:real^N->real^N->bool`)) (concl th) &&
      can (find_term ((=) `r:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`(U:real^N->real^N->bool) y`;
                          `(H:real^N->real^N->real^3) y`;
                          `(H':real^N->real^3->real^N) y`;
                          `(KK:real^N->real^N->bool) y`] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[];
      USE_THEN "ch" (MP_TAC o SPEC `y:real^N`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN ASM SET_TAC[]]]);;

(* ========================================================================= *)
(* Euclidean tools for the local crossing models: maps affine on            *)
(* two closed half spaces are PL, one-sided shears are PL homeomorphisms of *)
(* the whole space, linear maps from three independent functionals.        *)
(* ========================================================================= *)

(* VECTOR_ARITH_TAC after abstracting the dot products of the goal (which  *)
(* VECTOR_ARITH would otherwise expand into sums).                          *)

let rec moi_lgb2_tsize t =
  if is_comb t then moi_lgb2_tsize (rator t) + moi_lgb2_tsize (rand t) + 1
  else if is_abs t then moi_lgb2_tsize (body t) + 1
  else 1;;

let MOI_LGB2_VARITH_TAC : tactic =
  fun (asl,w as gl) ->
    let is_dot t = is_comb t && is_comb (rator t) &&
                   (let c = rator(rator t) in is_const c && fst(dest_const c) = "dot") in
    let dots = sort (fun a b -> moi_lgb2_tsize a > moi_lgb2_tsize b)
                 (setify Term.(<) (find_terms is_dot w)) in
    (MAP_EVERY (fun t -> TRY(SPEC_TAC(t,genvar(type_of t)))) dots THEN
     REPEAT GEN_TAC THEN VECTOR_ARITH_TAC) gl;;

let MOI_LGB2_PL_TWO_PIECE = prove
 (`!(f:real^M->real^N) (n:real^M) l1 y1 l2 y2.
     linear l1 /\ linear l2 /\
     (!z. &0 <= n dot z ==> f z = l1 z + y1) /\
     (!z. n dot z <= &0 ==> f z = l2 z + y2)
     ==> pl_map_on (:real^M) f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pl_map_on; IN_UNIV; INTER_UNIV] THEN
  X_GEN_TAC `x:real^M` THEN
  MAP_EVERY EXISTS_TAC
   [`{interval[x - vec 1:real^M,x + vec 1] INTER {z:real^M | n dot z >= &0},
      interval[x - vec 1:real^M,x + vec 1] INTER {z:real^M | n dot z <= &0}}`;
    `interval(x - vec 1:real^M,x + vec 1)`] THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; OPEN_INTERVAL; SUBSET_UNIV] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_INTERVAL; VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT;
                VEC_COMPONENT] THEN
    REPEAT STRIP_TAC THEN REAL_ARITH_TAC;
    MP_TAC(ISPECL [`x - vec 1:real^M`; `x + vec 1:real^M`]
      INTERVAL_OPEN_SUBSET_CLOSED) THEN
    REWRITE_TAC[SUBSET; UNIONS_INSERT; UNIONS_0; UNION_EMPTY; IN_UNION; IN_INTER;
                IN_ELIM_THM; real_ge] THEN
    MESON_TAC[REAL_LE_TOTAL];
    REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC POLYTOPE_INTER_POLYHEDRON THEN
      REWRITE_TAC[POLYTOPE_INTERVAL; POLYHEDRON_HALFSPACE_GE];
      MAP_EVERY EXISTS_TAC [`l1:real^M->real^N`; `y1:real^N`] THEN
      ASM_SIMP_TAC[IN_INTER; IN_ELIM_THM; real_ge];
      MATCH_MP_TAC POLYTOPE_INTER_POLYHEDRON THEN
      REWRITE_TAC[POLYTOPE_INTERVAL; POLYHEDRON_HALFSPACE_LE];
      MAP_EVERY EXISTS_TAC [`l2:real^M->real^N`; `y2:real^N`] THEN
      ASM_SIMP_TAC[IN_INTER; IN_ELIM_THM]]]);;

let MOI_LGB2_LINEAR_SHEAR = prove
 (`!(n:real^N) (v:real^N) a. linear (\z. z + (a * (n dot z)) % v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linear; DOT_RADD; DOT_RMUL] THEN
  REPEAT STRIP_TAC THENL
   [SPEC_TAC(`(n:real^N) dot x`,`p:real`) THEN SPEC_TAC(`(n:real^N) dot y`,`q:real`);
    SPEC_TAC(`(n:real^N) dot x`,`p:real`)] THEN
  VECTOR_ARITH_TAC);;

let MOI_LGB2_SHEAR = prove
 (`!(n:real^N) (v:real^N).
     &0 < &1 + n dot v
     ==> pl_homeomorphism ((:real^N),(:real^N))
           ((\z. if n dot z <= &0 then z + (n dot z) % v else z),
            (\z. if n dot z <= &0 then z - ((n dot z) / (&1 + n dot v)) % v else z))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `a = (n:real^N) dot v` THEN
  SUBGOAL_THEN
   `!z:real^N. n dot (z + (n dot z) % v) = (n dot z) * (&1 + a) /\
               n dot (z - ((n dot z) / (&1 + a)) % v) = (n dot z) / (&1 + a)`
  ASSUME_TAC THENL
   [GEN_TAC THEN ASM_REWRITE_TAC[DOT_RADD; DOT_RSUB; DOT_RMUL] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&0 < &1 + a` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ABBREV_TAC `f = \z:real^N. if n dot z <= &0 then z + (n dot z) % v else z` THEN
  ABBREV_TAC
   `g = \z:real^N. if n dot z <= &0 then z - ((n dot z) / (&1 + a)) % v else z` THEN
  SUBGOAL_THEN `pl_map_on (:real^N) (f:real^N->real^N) /\ pl_map_on (:real^N) (g:real^N->real^N)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_LGB2_PL_TWO_PIECE THEN
    EXISTS_TAC `n:real^N` THENL
     [MAP_EVERY EXISTS_TAC [`\z:real^N. z`; `vec 0:real^N`;
                            `\z:real^N. z + (&1 * (n dot z)) % v`; `vec 0:real^N`] THEN
      EXPAND_TAC "f";
      MAP_EVERY EXISTS_TAC [`\z:real^N. z`; `vec 0:real^N`;
                            `\z:real^N. z + (--inv(&1 + a) * (n dot z)) % v`;
                            `vec 0:real^N`] THEN
      EXPAND_TAC "g"] THEN
    REWRITE_TAC[LINEAR_ID; MOI_LGB2_LINEAR_SHEAR; VECTOR_ADD_RID] THEN
    REPEAT STRIP_TAC THEN
    (ASM_CASES_TAC `(n:real^N) dot z <= &0` THEN ASM_REWRITE_TAC[]) THEN
    TRY(SUBGOAL_THEN `(n:real^N) dot z = &0` SUBST1_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; VECTOR_MUL_LZERO; VECTOR_ADD_RID;
                VECTOR_SUB_RZERO; REAL_MUL_LID; REAL_MUL_RZERO] THEN
    SPEC_TAC(`(n:real^N) dot z`,`t:real`) THEN SPEC_TAC(`inv(&1 + a)`,`w:real`) THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(!z:real^N. g ((f:real^N->real^N) z) = z) /\
                (!z:real^N. f ((g:real^N->real^N) z) = z)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `z:real^N` THEN
    MAP_EVERY EXPAND_TAC ["f"; "g"] THEN BETA_TAC THEN
    ASM_CASES_TAC `(n:real^N) dot z <= &0` THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `((n:real^N) dot z) * (&1 + a) <= &0` (fun th -> REWRITE_TAC[th]) THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= --x * y ==> x * y <= &0`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `(((n:real^N) dot z) * (&1 + a)) / (&1 + a) = n dot z` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < &1 + a` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      SPEC_TAC(`(n:real^N) dot z`,`t:real`) THEN GEN_TAC THEN VECTOR_ARITH_TAC;
      SUBGOAL_THEN `((n:real^N) dot z) / (&1 + a) <= &0` (fun th -> REWRITE_TAC[th]) THENL
       [REWRITE_TAC[real_div] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= --x * y ==> x * y <= &0`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SPEC_TAC(`((n:real^N) dot z) / (&1 + a)`,`t:real`) THEN GEN_TAC THEN
      VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[homeomorphism; IN_UNIV] THEN
  ASM_SIMP_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN ASM_MESON_TAC[]);;

let MOI_LGB2_LINEAR_PLH_UNIV = prove
 (`!(l:real^N->real^N) (c:real^N).
     linear l /\ (!x y. l x = l y ==> x = y)
     ==> ?g. pl_homeomorphism ((:real^N),(:real^N)) ((\z. l z + c),g)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `l:real^N->real^N` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
  ASM_REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `l':real^N->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `l:real^N->real^N` LINEAR_INJECTIVE_IMP_SURJECTIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!y:real^N. l ((l':real^N->real^N) y) = y` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `\w:real^N. (l':real^N->real^N) w - l' c` THEN
  MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC PL_MAP_ON_AFFINE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_OPEN THEN REWRITE_TAC[OPEN_UNIV]] THEN
  SUBGOAL_THEN `!z:real^N. (l':real^N->real^N) (l z + c) - l' c = z /\
                           l ((l':real^N->real^N) z - l' c) + c = z`
  ASSUME_TAC THENL
   [GEN_TAC THEN ASM_SIMP_TAC[LINEAR_ADD; LINEAR_SUB] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[homeomorphism; IN_UNIV] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; CONTINUOUS_ON_CONST];
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; CONTINUOUS_ON_CONST]]);;

let MOI_LGB2_CROSS_INDEP = prove
 (`!(n1:real^3) n2 x.
     ~(n1 cross n2 = vec 0) /\ n1 dot x = &0 /\ n2 dot x = &0 /\
     (n1 cross n2) dot x = &0
     ==> x = vec 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(n1 cross n2) cross (x:real^3) = vec 0` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[CROSS_SKEW] THEN REWRITE_TAC[CROSS_LAGRANGE] THEN
    ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n1 cross n2:real^3`; `x:real^3`] NORM_AND_CROSS_EQ_0) THEN
  ASM_REWRITE_TAC[]);;

let MOI_LGB2_LIN3 = prove
 (`!(n1:real^3) n2 n3 (z0:real^3).
     (!x. n1 dot x = &0 /\ n2 dot x = &0 /\ n3 dot x = &0 ==> x = vec 0)
     ==> ?f'. pl_homeomorphism ((:real^3),(:real^3))
                ((\z. vector[n1 dot (z - z0); n2 dot (z - z0); n3 dot (z - z0)]:real^3),f')`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `l = \z:real^3. vector[n1 dot z; n2 dot z; n3 dot z]:real^3` THEN
  SUBGOAL_THEN `linear (l:real^3->real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN REWRITE_TAC[linear; DOT_RADD; DOT_RMUL] THEN
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
             VECTOR_MUL_COMPONENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y. (l:real^3->real^3) x = l y ==> x = y` ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN EXPAND_TAC "l" THEN
    BETA_TAC THEN DISCH_THEN(MP_TAC o GEN_REWRITE_RULE I [CART_EQ]) THEN
    SIMP_TAC[DIMINDEX_3; FORALL_3; VECTOR_3] THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[DOT_RSUB; REAL_SUB_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:real^3->real^3`; `--((l:real^3->real^3) z0)`]
    MOI_LGB2_LINEAR_PLH_UNIV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `f':real^3->real^3`) THEN EXISTS_TAC `f':real^3->real^3` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb(concl th) &&
     fst(dest_const(fst(strip_comb(concl th)))) = "pl_homeomorphism")) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^3` THEN
  EXPAND_TAC "l" THEN
  SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
           VECTOR_NEG_COMPONENT; DOT_RSUB] THEN
  REAL_ARITH_TAC);;

let MOI_LGB2_MODEL_M1 = prove
 (`!(z0:real^3) (n1:real^3) n2.
     ~(n1 cross n2 = vec 0)
     ==> ?f f'. pl_homeomorphism ((:real^3),(:real^3)) (f,f') /\ f z0 = vec 0 /\
                (!z. n1 dot (z - z0) = &0 ==> (f z)$1 = &0) /\
                (!z. n2 dot (z - z0) = &0 ==> (f z)$2 = &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n1:real^3`; `n2:real^3`; `n1 cross n2:real^3`; `z0:real^3`]
    MOI_LGB2_LIN3) THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_LGB2_CROSS_INDEP THEN
    MAP_EVERY EXISTS_TAC [`n1:real^3`; `n2:real^3`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `f':real^3->real^3`) THEN
  MAP_EVERY EXISTS_TAC
   [`\z. vector[n1 dot (z - z0); n2 dot (z - z0);
                (n1 cross n2) dot (z - z0)]:real^3`; `f':real^3->real^3`] THEN
  ASM_REWRITE_TAC[VECTOR_SUB_REFL; DOT_RZERO; VECTOR_3] THEN
  SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VEC_COMPONENT]);;

let MOI_LGB2_SEPARATE = prove
 (`!(d:real^3) a b.
     ~(d cross a = vec 0) /\ ~(d cross b = vec 0) /\
     (!s t s' t'. &0 < s /\ &0 < s' ==> ~(t % d + s % a = t' % d + s' % b))
     ==> ?nn. nn dot d = &0 /\ &0 < nn dot a /\ nn dot b < &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(b cross d) dot (a:real^3) = a dot (b cross d) /\
                (a cross d) dot (b:real^3) = --(a dot (b cross d))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[cross; DOT_3; VECTOR_3] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `(a:real^3) dot (b cross d) = &0` THENL
   [ALL_TAC;
    EXISTS_TAC `inv((a:real^3) dot (b cross d)) % ((a + b) cross d)` THEN
    ASM_REWRITE_TAC[DOT_LMUL; CROSS_LADD; DOT_LADD; DOT_CROSS_SELF;
                    REAL_ADD_LID; REAL_ADD_RID; REAL_MUL_RZERO] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_01; REAL_MUL_RNEG] THEN REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `~(d:real^3 = vec 0) /\ ~(a cross d = vec 0) /\ ~(b cross d = vec 0)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[CROSS_LZERO];
      ONCE_REWRITE_TAC[CROSS_SKEW] THEN ASM_REWRITE_TAC[VECTOR_NEG_EQ_0];
      ONCE_REWRITE_TAC[CROSS_SKEW] THEN ASM_REWRITE_TAC[VECTOR_NEG_EQ_0]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?lam mu. b:real^3 = lam % a + mu % d` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(a cross d) cross (b cross d) = vec 0:real^3` MP_TAC THENL
     [REWRITE_TAC[CROSS_CROSS_DET; GSYM DOT_CROSS_DET; CROSS_REFL; DOT_RZERO] THEN
      ONCE_REWRITE_TAC[CROSS_SKEW] THEN
      ASM_REWRITE_TAC[DOT_RNEG; REAL_NEG_0; VECTOR_MUL_LZERO; VECTOR_SUB_REFL];
      ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [CROSS_EQ_0] THEN
    GEN_REWRITE_TAC LAND_CONV [COLLINEAR_LEMMA] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `lam:real`) THEN
    SUBGOAL_THEN `(b - lam % a) cross d = vec 0:real^3` MP_TAC THENL
     [ASM_REWRITE_TAC[CROSS_LSUB; CROSS_LMUL; VECTOR_SUB_REFL]; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [CROSS_EQ_0] THEN
    ONCE_REWRITE_TAC[SET_RULE `{a:real^3,b,c} = {a,c,b}`] THEN
    GEN_REWRITE_TAC LAND_CONV [COLLINEAR_LEMMA] THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`lam:real`; `&0`] THEN
      UNDISCH_TAC `b - lam % a = vec 0:real^3` THEN VECTOR_ARITH_TAC;
      MAP_EVERY EXISTS_TAC [`lam:real`; `c:real`] THEN
      UNDISCH_TAC `b - lam % a = c % d:real^3` THEN VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `lam < &0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    ASM_CASES_TAC `lam = &0` THENL
     [UNDISCH_TAC `~(d cross b = vec 0:real^3)` THEN
      ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID; CROSS_RMUL; CROSS_REFL;
                      VECTOR_MUL_RZERO];
      FIRST_X_ASSUM(MP_TAC o SPECL [`lam:real`; `mu:real`; `&1`; `&0`] o
        check (is_forall o concl)) THEN
      ASM_REWRITE_TAC[REAL_LT_01] THEN
      MATCH_MP_TAC(TAUT `p /\ q ==> ~(p ==> ~q)`) THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC]];
    ALL_TAC] THEN
  EXISTS_TAC `d cross (a cross d):real^3` THEN
  REWRITE_TAC[DOT_CROSS_SELF] THEN
  SUBGOAL_THEN `&0 < (d cross (a cross d)) dot (a:real^3)` ASSUME_TAC THENL
   [REWRITE_TAC[CROSS_LAGRANGE; DOT_LSUB; DOT_LMUL] THEN
    MP_TAC(ISPECL [`d:real^3`; `a:real^3`] NORM_CROSS_DOT) THEN
    SUBGOAL_THEN `&0 < norm(d cross a:real^3) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_MUL; NORM_POW_2] THEN
    REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL; DOT_CROSS_SELF; REAL_MUL_RZERO;
                  REAL_ADD_RID] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < --l * x ==> l * x < &0`) THEN
  MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC);;

let MOI_LGB2_TRANSLATE_PLH = prove
 (`!c:real^N. pl_homeomorphism ((:real^N),(:real^N)) ((\z. z + c),(\z. z - c))`,
  GEN_TAC THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN CONJ_TAC THENL
   [REWRITE_TAC[homeomorphism; IN_UNIV; EXTENSION; IN_IMAGE] THEN
    SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID;
             CONTINUOUS_ON_CONST] THEN
    REPEAT CONJ_TAC THEN X_GEN_TAC `x:real^N` THEN
    FIRST [VECTOR_ARITH_TAC;
           EXISTS_TAC `x - c:real^N` THEN VECTOR_ARITH_TAC;
           EXISTS_TAC `x + c:real^N` THEN VECTOR_ARITH_TAC];
    MP_TAC(ISPECL [`(:real^N)`; `\z:real^N. z`; `c:real^N`] PL_MAP_ON_AFFINE) THEN
    SIMP_TAC[LINEAR_ID; LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV]]);;

let MOI_LGB2_SH_POS = prove
 (`!(n:real^N) v w.
     &0 <= n dot w ==> (if n dot w <= &0 then w + (n dot w) % v else w) = w`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `(n:real^N) dot w = &0` SUBST1_TAC THENL
   [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC]);;

let MOI_LGB2_SH_NEG = prove
 (`!(n:real^N) v w.
     n dot w <= &0
     ==> (if n dot w <= &0 then w + (n dot w) % v else w) = w + (n dot w) % v`,
  SIMP_TAC[]);;

let MOI_LGB2_MODEL_M2 = prove
 (`!(z0:real^3) (d:real^3) a b nb.
     ~(nb dot d = &0) /\ ~(d cross a = vec 0) /\ ~(d cross b = vec 0) /\
     (!s t s' t'. &0 < s /\ &0 < s' ==> ~(t % d + s % a = t' % d + s' % b))
     ==> ?f f'. pl_homeomorphism ((:real^3),(:real^3)) (f,f') /\ f z0 = vec 0 /\
                (!s t. &0 <= s ==> (f (z0 + t % d + s % a))$1 = &0) /\
                (!s t. &0 <= s ==> (f (z0 + t % d + s % b))$1 = &0) /\
                (!z. nb dot (z - z0) = &0 ==> (f z)$2 = &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`d:real^3`; `a:real^3`; `b:real^3`] MOI_LGB2_SEPARATE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `nn:real^3` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `al = ((nb:real^3) dot (a + b)) / (nb dot d)` THEN
  SUBGOAL_THEN `al * ((nb:real^3) dot d) = nb dot a + nb dot b` ASSUME_TAC THENL
   [EXPAND_TAC "al" THEN REWRITE_TAC[DOT_RADD] THEN
    UNDISCH_TAC `~((nb:real^3) dot d = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ABBREV_TAC `v = inv((nn:real^3) dot b) % (al % d - a - b:real^3)` THEN
  SUBGOAL_THEN
   `(nb:real^3) dot v = &0 /\ &0 < &1 + (nn:real^3) dot v /\
    b + (nn dot b) % v = al % d - a:real^3`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN REWRITE_TAC[DOT_RMUL; DOT_RSUB; VECTOR_MUL_ASSOC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_LZERO] THEN
      UNDISCH_TAC `&0 < (nn:real^3) dot a` THEN
      UNDISCH_TAC `(nn:real^3) dot b < &0` THEN
      SPEC_TAC(`(nn:real^3) dot a`,`p:real`) THEN
      SPEC_TAC(`(nn:real^3) dot b`,`q:real`) THEN
      REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
      SUBGOAL_THEN `&1 + inv q * (--p - q) = --p / q` SUBST1_TAC THENL
       [UNDISCH_TAC `q < &0` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      REWRITE_TAC[real_div; REAL_MUL_LNEG] THEN
      MATCH_MP_TAC(REAL_ARITH `x * y < &0 ==> &0 < --(x * y)`) THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < x * --y ==> x * y < &0`) THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM REAL_INV_NEG] THEN MATCH_MP_TAC REAL_LT_INV THEN
      ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `((nn:real^3) dot b) * inv(nn dot b) = &1` SUBST1_TAC THENL
       [MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`nn:real^3`; `v:real^3`] MOI_LGB2_SHEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `--z0:real^3` MOI_LGB2_TRANSLATE_PLH) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`d cross a:real^3`; `nb:real^3`; `(d cross a) cross nb:real^3`;
                 `vec 0:real^3`] MOI_LGB2_LIN3) THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_LGB2_CROSS_INDEP THEN
    MAP_EVERY EXISTS_TAC [`d cross a:real^3`; `nb:real^3`] THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[CROSS_EQ_0] THEN ONCE_REWRITE_TAC[COLLINEAR_LEMMA] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(nb:real^3 = vec 0)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~(vec 0 dot (d:real^3) = &0)` THEN
      REWRITE_TAC[DOT_LZERO];
      ASM_REWRITE_TAC[]] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real` SUBST_ALL_TAC) THEN
    UNDISCH_TAC `~((k % (d cross a)) dot (d:real^3) = &0)` THEN
    REWRITE_TAC[DOT_LMUL; DOT_CROSS_SELF; REAL_MUL_RZERO];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `l':real^3->real^3`) THEN
  ABBREV_TAC
   `L = \w:real^3. vector[(d cross a) dot (w - vec 0); nb dot (w - vec 0);
                          ((d cross a) cross nb) dot (w - vec 0)]:real^3` THEN
  ABBREV_TAC `SH = \z:real^3. if nn dot z <= &0 then z + (nn dot z) % v else z` THEN
  ABBREV_TAC `TR = \z:real^3. z + --z0` THEN
  MAP_EVERY EXISTS_TAC
   [`(L:real^3->real^3) o (SH:real^3->real^3) o (TR:real^3->real^3)`;
    `((\z:real^3. z - --z0) o
      (\z. if nn dot z <= &0 then z - ((nn dot z) / (&1 + nn dot v)) % v else z)) o
     (l':real^3->real^3)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(:real^3)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(:real^3)` THEN
      MAP_EVERY EXPAND_TAC ["SH"; "TR"] THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "L" THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w:real^3. (L:real^3->real^3) w = vector[(d cross a) dot w; nb dot w;
                                             ((d cross a) cross nb) dot w]`
  ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[VECTOR_SUB_RZERO]; ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. (TR:real^3->real^3) z = z - z0` ASSUME_TAC THENL
   [EXPAND_TAC "TR" THEN REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[o_THM; VECTOR_3] THEN REPEAT CONJ_TAC THENL
   [EXPAND_TAC "SH" THEN REWRITE_TAC[VECTOR_SUB_REFL; DOT_RZERO; REAL_LE_REFL] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; DOT_RZERO] THEN
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VEC_COMPONENT];
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[VECTOR_ARITH `(z0 + t % d + s % a) - z0:real^3 = t % d + s % a`] THEN
    EXPAND_TAC "SH" THEN
    SUBGOAL_THEN `&0 <= (nn:real^3) dot (t % d + s % a)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL; REAL_MUL_RZERO; REAL_ADD_LID] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_LGB2_SH_POS] THEN
    REWRITE_TAC[DOT_RADD; DOT_RMUL; DOT_CROSS_SELF] THEN REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[VECTOR_ARITH `(z0 + t % d + s % b) - z0:real^3 = t % d + s % b`] THEN
    EXPAND_TAC "SH" THEN
    SUBGOAL_THEN `(nn:real^3) dot (t % d + s % b) = s * (nn dot b)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL; REAL_MUL_RZERO; REAL_ADD_LID];
      ALL_TAC] THEN
    SUBGOAL_THEN `(nn:real^3) dot (t % d + s % b) <= &0` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= s * --x ==> s * x <= &0`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_LGB2_SH_NEG] THEN
    REWRITE_TAC[VECTOR_ARITH
     `(t % d + s % b) + (s * x) % v:real^3 = t % d + s % (b + x % v)`] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DOT_RADD; DOT_RMUL; DOT_RSUB; DOT_CROSS_SELF] THEN REAL_ARITH_TAC;
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN EXPAND_TAC "SH" THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL; REAL_MUL_RZERO; REAL_ADD_RID]]);;

let MOI_LGB2_TRIPLE_IDS = prove
 (`(!x y z:real^3. (x cross z) cross (y cross z) = --((x cross z) dot y) % z) /\
   (!x y z:real^3. (y cross z) dot x = --((x cross z) dot y)) /\
   (!x y z:real^3. (x cross z) dot y = --((x cross y) dot z)) /\
   (!x y z:real^3. (x cross y) cross z = (x dot z) % y - (y dot z) % x)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  SIMP_TAC[cross; DOT_3; VECTOR_3; CART_EQ; DIMINDEX_3; FORALL_3;
           VECTOR_NEG_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_SUB_COMPONENT] THEN
  REAL_ARITH_TAC);;

let MOI_LGB2_MODEL_M3 = prove
 (`!(z0:real^3) (nu:real^3) d1 d2 a1 a2 b1 b2.
     nu dot d1 = &0 /\ nu dot d2 = &0 /\ ~(d1 cross d2 = vec 0) /\
     &0 < nu dot a1 /\ nu dot a2 < &0 /\ &0 < nu dot b1 /\ nu dot b2 < &0
     ==> ?f f'. pl_homeomorphism ((:real^3),(:real^3)) (f,f') /\ f z0 = vec 0 /\
                (!s t. &0 <= s ==> (f (z0 + t % d1 + s % a1))$1 = &0) /\
                (!s t. &0 <= s ==> (f (z0 + t % d1 + s % a2))$1 = &0) /\
                (!s t. &0 <= s ==> (f (z0 + t % d2 + s % b1))$2 = &0) /\
                (!s t. &0 <= s ==> (f (z0 + t % d2 + s % b2))$2 = &0) /\
                (!z. (f z)$3 = nu dot (z - z0))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `n1 = (d1:real^3) cross nu` THEN
  ABBREV_TAC `n2 = (d2:real^3) cross nu` THEN
  ABBREV_TAC `ka = (n1:real^3) dot d2` THEN
  SUBGOAL_THEN `~(nu:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `&0 < vec 0 dot (a1:real^3)` THEN
    REWRITE_TAC[DOT_LZERO; REAL_LT_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(n1:real^3) dot d1 = &0 /\ (n2:real^3) dot d2 = &0 /\
    (n1:real^3) dot nu = &0 /\ (n2:real^3) dot nu = &0 /\
    (n2:real^3) dot d1 = --ka /\ n1 cross n2 = --ka % (nu:real^3)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["n1"; "n2"; "ka"] THEN REWRITE_TAC[DOT_CROSS_SELF] THEN
    MP_TAC(ISPECL [`d1:real^3`; `d2:real^3`; `nu:real^3`]
             (CONJUNCT1(CONJUNCT2 MOI_LGB2_TRIPLE_IDS))) THEN
    MP_TAC(ISPECL [`d1:real^3`; `d2:real^3`; `nu:real^3`]
             (CONJUNCT1 MOI_LGB2_TRIPLE_IDS)) THEN
    EXPAND_TAC "n1" THEN CONV_TAC TAUT;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(ka = &0)` ASSUME_TAC THENL
   [EXPAND_TAC "ka" THEN EXPAND_TAC "n1" THEN
    MP_TAC(ISPECL [`d1:real^3`; `d2:real^3`; `nu:real^3`]
             (CONJUNCT1(CONJUNCT2(CONJUNCT2 MOI_LGB2_TRIPLE_IDS)))) THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_NEG_EQ_0] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`d1 cross d2:real^3`; `nu:real^3`] NORM_AND_CROSS_EQ_0) THEN
    MP_TAC(ISPECL [`d1:real^3`; `d2:real^3`; `nu:real^3`]
             (CONJUNCT2(CONJUNCT2(CONJUNCT2 MOI_LGB2_TRIPLE_IDS)))) THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `(d1:real^3) dot nu = &0 /\ (d2:real^3) dot nu = &0`
    STRIP_ASSUME_TAC THENL [ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_SUB_REFL];
    ALL_TAC] THEN
  ABBREV_TAC
   `wp = (((n2:real^3) dot b1) / (((nu:real^3) dot b1) * ka)) % (d1:real^3) +
         (--(((n1:real^3) dot a1) / ((nu dot a1) * ka))) % (d2:real^3)` THEN
  ABBREV_TAC
   `wm = (((n2:real^3) dot b2) / (((nu:real^3) dot b2) * ka)) % (d1:real^3) +
         (--(((n1:real^3) dot a2) / ((nu dot a2) * ka))) % (d2:real^3)` THEN
  SUBGOAL_THEN
   `(nu:real^3) dot wp = &0 /\ (nu:real^3) dot wm = &0 /\
    (n1:real^3) dot (a1 + (nu dot a1) % wp) = &0 /\
    (n2:real^3) dot (b1 + (nu dot b1) % wp) = &0 /\
    (n1:real^3) dot (a2 + (nu dot a2) % wm) = &0 /\
    (n2:real^3) dot (b2 + (nu dot b2) % wm) = &0`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["wp"; "wm"] THEN
    ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL; REAL_MUL_RZERO; REAL_ADD_RID;
                    REAL_ADD_LID] THEN
    REPEAT CONJ_TAC THEN
    MAP_EVERY (fun t -> UNDISCH_TAC t)
     [`~(ka = &0)`; `&0 < (nu:real^3) dot a1`; `(nu:real^3) dot a2 < &0`;
      `&0 < (nu:real^3) dot b1`; `(nu:real^3) dot b2 < &0`] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ABBREV_TAC
   `SP = \z:real^3. if --nu dot z <= &0 then z + (--nu dot z) % --wp else z` THEN
  ABBREV_TAC `SM = \z:real^3. if nu dot z <= &0 then z + (nu dot z) % wm else z` THEN
  ABBREV_TAC `TR = \z:real^3. z + --z0` THEN
  ABBREV_TAC
   `LL = \w:real^3. vector[n1 dot (w - vec 0); n2 dot (w - vec 0);
                           nu dot (w - vec 0)]:real^3` THEN
  MP_TAC(ISPECL [`--nu:real^3`; `--wp:real^3`] MOI_LGB2_SHEAR) THEN
  ASM_REWRITE_TAC[DOT_LNEG; DOT_RNEG; REAL_NEG_NEG; REAL_ADD_RID; REAL_LT_01] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`nu:real^3`; `wm:real^3`] MOI_LGB2_SHEAR) THEN
  ASM_REWRITE_TAC[REAL_ADD_RID; REAL_LT_01] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `--z0:real^3` MOI_LGB2_TRANSLATE_PLH) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`n1:real^3`; `n2:real^3`; `nu:real^3`; `vec 0:real^3`]
    MOI_LGB2_LIN3) THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_LGB2_CROSS_INDEP THEN
    MAP_EVERY EXISTS_TAC [`n1:real^3`; `n2:real^3`] THEN
    ASM_REWRITE_TAC[DOT_LMUL; REAL_MUL_RZERO; VECTOR_MUL_EQ_0; REAL_NEG_EQ_0];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `l':real^3->real^3`) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DOT_LNEG; DOT_RNEG; REAL_NEG_NEG; REAL_ADD_RID]) THEN
  EXISTS_TAC `(LL:real^3->real^3) o (SM:real^3->real^3) o (SP:real^3->real^3) o
              (TR:real^3->real^3)` THEN
  EXISTS_TAC
   `(((\z:real^3. z - --z0) o
      (\z. if --nu dot z <= &0 then z - (--(nu dot z) / &1) % --wp else z)) o
     (\z. if nu dot z <= &0 then z - ((nu dot z) / &1) % wm else z)) o
    (l':real^3->real^3)` THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(:real^3)` THEN
           CONJ_TAC) THEN
    MAP_EVERY EXPAND_TAC ["LL"; "SM"; "SP"; "TR"] THEN
    ASM_REWRITE_TAC[DOT_LNEG] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `wp:real^3`)) (concl th) &&
      can (find_term ((=) `pl_homeomorphism:(real^3->bool)#(real^3->bool)->(real^3->real^3)#(real^3->real^3)->bool`)) (concl th))) THEN
    REWRITE_TAC[DOT_LNEG; REAL_NEG_NEG] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!z:real^3. (TR:real^3->real^3) z = z - z0) /\
    (!w:real^3. (LL:real^3->real^3) w = vector[n1 dot w; n2 dot w; nu dot w]) /\
    (!w:real^3. nu dot ((SP:real^3->real^3) w) = nu dot w) /\
    (!w:real^3. nu dot ((SM:real^3->real^3) w) = nu dot w)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN GEN_TAC THEN MAP_EVERY EXPAND_TAC ["TR"; "LL"; "SP"; "SM"] THEN
    REWRITE_TAC[VECTOR_SUB_RZERO] THEN TRY MOI_LGB2_VARITH_TAC THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL; DOT_RNEG; REAL_MUL_RZERO; REAL_NEG_0;
                    REAL_ADD_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!w:real^3. &0 <= nu dot w
                ==> (SM:real^3->real^3) ((SP:real^3->real^3) w) = w + (nu dot w) % wp) /\
    (!w:real^3. nu dot w <= &0
                ==> (SM:real^3->real^3) ((SP:real^3->real^3) w) = w + (nu dot w) % wm) /\
    (SM:real^3->real^3) ((SP:real^3->real^3) (vec 0)) = vec 0`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(SP:real^3->real^3) w = w + (nu dot w) % wp` ASSUME_TAC THENL
       [EXPAND_TAC "SP" THEN REWRITE_TAC[] THEN
        COND_CASES_TAC THENL [MOI_LGB2_VARITH_TAC; ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "SM" THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `(nu:real^3) dot (w + (nu dot w) % wp) = nu dot w` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL; REAL_MUL_RZERO; REAL_ADD_RID]; ALL_TAC] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `(nu:real^3) dot w = &0` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC; MOI_LGB2_VARITH_TAC];
      X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(SP:real^3->real^3) w = w` SUBST1_TAC THENL
       [EXPAND_TAC "SP" THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
        SUBGOAL_THEN `(nu:real^3) dot w = &0` SUBST1_TAC THENL
         [ASM_REAL_ARITH_TAC; MOI_LGB2_VARITH_TAC];
        ALL_TAC] THEN
      EXPAND_TAC "SM" THEN ASM_REWRITE_TAC[];
      MAP_EVERY EXPAND_TAC ["SP"; "SM"] THEN
      REWRITE_TAC[DOT_RZERO; REAL_NEG_0; REAL_LE_REFL; VECTOR_MUL_LZERO;
                  VECTOR_ADD_LID]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[o_THM; VECTOR_3] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[VECTOR_SUB_REFL] THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VEC_COMPONENT; DOT_RZERO];
    MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN DISCH_TAC THEN
    REWRITE_TAC[VECTOR_ARITH `(z0 + t % d + s % a) - z0:real^3 = t % d + s % a`] THEN
    SUBGOAL_THEN `(nu:real^3) dot (t % d1 + s % a1) = s * (nu dot a1)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL; REAL_MUL_RZERO; REAL_ADD_LID]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (nu:real^3) dot (t % d1 + s % a1)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    REWRITE_TAC[VECTOR_ARITH
     `(t % d1 + s % a1) + (s * c) % wp:real^3 = t % d1 + s % (a1 + c % wp)`] THEN
    ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL; REAL_MUL_RZERO; REAL_ADD_RID];
    MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN DISCH_TAC THEN
    REWRITE_TAC[VECTOR_ARITH `(z0 + t % d + s % a) - z0:real^3 = t % d + s % a`] THEN
    SUBGOAL_THEN `(nu:real^3) dot (t % d1 + s % a2) = s * (nu dot a2)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL; REAL_MUL_RZERO; REAL_ADD_LID]; ALL_TAC] THEN
    SUBGOAL_THEN `(nu:real^3) dot (t % d1 + s % a2) <= &0` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= s * --x ==> s * x <= &0`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    REWRITE_TAC[VECTOR_ARITH
     `(t % d1 + s % a2) + (s * c) % wm:real^3 = t % d1 + s % (a2 + c % wm)`] THEN
    ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL; REAL_MUL_RZERO; REAL_ADD_RID];
    MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN DISCH_TAC THEN
    REWRITE_TAC[VECTOR_ARITH `(z0 + t % d + s % a) - z0:real^3 = t % d + s % a`] THEN
    SUBGOAL_THEN `(nu:real^3) dot (t % d2 + s % b1) = s * (nu dot b1)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL; REAL_MUL_RZERO; REAL_ADD_LID]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (nu:real^3) dot (t % d2 + s % b1)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    REWRITE_TAC[VECTOR_ARITH
     `(t % d2 + s % b1) + (s * c) % wp:real^3 = t % d2 + s % (b1 + c % wp)`] THEN
    ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL; REAL_MUL_RZERO; REAL_ADD_RID];
    MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN DISCH_TAC THEN
    REWRITE_TAC[VECTOR_ARITH `(z0 + t % d + s % a) - z0:real^3 = t % d + s % a`] THEN
    SUBGOAL_THEN `(nu:real^3) dot (t % d2 + s % b2) = s * (nu dot b2)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL; REAL_MUL_RZERO; REAL_ADD_LID]; ALL_TAC] THEN
    SUBGOAL_THEN `(nu:real^3) dot (t % d2 + s % b2) <= &0` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= s * --x ==> s * x <= &0`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    REWRITE_TAC[VECTOR_ARITH
     `(t % d2 + s % b2) + (s * c) % wm:real^3 = t % d2 + s % (b2 + c % wm)`] THEN
    ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL; REAL_MUL_RZERO; REAL_ADD_RID]]);;

(* ========================================================================= *)
(* From a local model chart to the crossing chart: the preimage             *)
(* of a double point, compactness near it, shrinking the chart to a small  *)
(* ball and reading off the exact sheets and the double image.              *)
(* ========================================================================= *)

let MOI_LGB2_PREIMAGE2 = prove
 (`!(c:(real^N->bool)->bool) (g:real^2->real^N) y x1 x2.
     moi_lt_singular_disk c g /\ x1 IN std_triangle /\ x2 IN std_triangle /\
     ~(x1 = x2) /\ g x1 = y /\ g x2 = y
     ==> !x. x IN std_triangle /\ g x = y ==> x = x1 \/ x = x2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lt_singular_disk] THEN STRIP_TAC THEN
  X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
  ASM_CASES_TAC `x:real^2 = x1` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `x:real^2 = x2` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check (is_forall o concl)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `{x1:real^2,x2,x} SUBSET {x | x IN std_triangle /\ (g:real^2->real^N) x = y}`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(x1:real^2 = x) /\ ~(x2:real^2 = x)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`{x1:real^2,x2,x}`;
                 `{x | x IN std_triangle /\ (g:real^2->real^N) x = y}`] CARD_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `CARD {x1:real^2,x2,x} = 3` SUBST1_TAC THENL
   [SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  UNDISCH_TAC `CARD {x | x IN std_triangle /\ (g:real^2->real^N) x = y} <= 2` THEN
  ARITH_TAC);;

let MOI_LGB2_NEAR_PREIMAGE = prove
 (`!(g:real^2->real^N) y N1 N2.
     g continuous_on std_triangle /\
     open_in (subtopology euclidean std_triangle) N1 /\
     open_in (subtopology euclidean std_triangle) N2 /\
     (!x. x IN std_triangle /\ g x = y ==> x IN N1 UNION N2)
     ==> ?e. &0 < e /\
             !x. x IN std_triangle /\ dist(g x,y) < e ==> x IN N1 UNION N2`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `kk = std_triangle DIFF (N1 UNION N2:real^2->bool)` THEN
  SUBGOAL_THEN `compact (kk:real^2->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_IN_COMPACT THEN EXISTS_TAC `std_triangle` THEN
    REWRITE_TAC[MOI_LTD_STD_TRIANGLE_BASIC] THEN EXPAND_TAC "kk" THEN
    MATCH_MP_TAC CLOSED_IN_DIFF THEN REWRITE_TAC[CLOSED_IN_REFL] THEN
    MATCH_MP_TAC OPEN_IN_UNION THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (IMAGE (g:real^2->real^N) kk)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `std_triangle` THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "kk" THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((y:real^N) IN IMAGE (g:real^2->real^N) kk)` ASSUME_TAC THENL
   [EXPAND_TAC "kk" THEN REWRITE_TAC[IN_IMAGE; IN_DIFF] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`y:real^N`; `IMAGE (g:real^2->real^N) kk`] CLOSED_APPROACHABLE) THEN
  ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(g:real^2->real^N) x`) THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "kk" THEN ASM SET_TAC[]);;

let MOI_LGB2_CHART_SHRINK = prove
 (`!(u:real^N->bool) (H:real^N->real^M) H' y e.
     homeomorphism (u,IMAGE H u) (H,H') /\ y IN u /\ &0 < e
     ==> ?r. &0 < r /\ !p. p IN u /\ norm(H p - H y) < r ==> dist(p,y) < e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  UNDISCH_TAC `(H':real^M->real^N) continuous_on IMAGE (H:real^N->real^M) u` THEN
  REWRITE_TAC[continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `(H:real^N->real^M) y`) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `p:real^N` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(H:real^N->real^M) p`) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE; dist]);;

let MOI_LGB2_TRANSFER_CHART = prove
 (`!(c:(real^N->bool)->bool) u (H:real^N->real^3) H' (y:real^N) K rho.
     open_in (subtopology euclidean (UNIONS c)) u /\ y IN u /\
     homeomorphism (u,IMAGE H u) (H,H') /\ pl_map_on u H /\ H y = vec 0 /\
     (!z t. z IN K /\ &0 < t ==> t % z IN K) /\
     &0 < rho /\ IMAGE H u INTER ball(vec 0,rho) = K INTER ball(vec 0,rho)
     ==> open_in (subtopology euclidean (UNIONS c))
                 {p | p IN u /\ H p IN ball(vec 0,rho)} /\
         y IN {p | p IN u /\ H p IN ball(vec 0,rho)} /\
         pl_homeomorphism
           ({p | p IN u /\ H p IN ball(vec 0,rho)},
            IMAGE (\p. inv rho % H p) {p | p IN u /\ H p IN ball(vec 0,rho)})
           ((\p. inv rho % H p),(\z. H'(rho % z))) /\
         IMAGE (\p. inv rho % H p) {p | p IN u /\ H p IN ball(vec 0,rho)} =
         ball(vec 0,&1) INTER K`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `u' = {p | p IN u /\ (H:real^N->real^3) p IN ball(vec 0,rho)}` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `open_in (subtopology euclidean u) (u':real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "u'" THEN MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u':real^N->bool) SUBSET u` ASSUME_TAC THENL
   [EXPAND_TAC "u'" THEN SET_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_TRANS];
    EXPAND_TAC "u'" THEN ASM_REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL];
    MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN CONJ_TAC THENL
     [REWRITE_TAC[homeomorphism] THEN REPEAT CONJ_TAC THENL
       [X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN BETA_TAC THEN
        ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ;
                     VECTOR_MUL_LID] THEN
        ASM SET_TAC[];
        MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `u:real^N->bool` THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
        BETA_TAC THEN
        ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ;
                     VECTOR_MUL_LID] THEN
        SUBGOAL_THEN `(H':real^3->real^N) (H p) = p` SUBST1_TAC THENL
         [ASM SET_TAC[]; REWRITE_TAC[]];
        REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
        MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (\x:real^N. x) u'` THEN
        CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[IMAGE_ID]] THEN
        MATCH_MP_TAC IMAGE_EQ THEN X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
        ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ;
                     VECTOR_MUL_LID] THEN
        ASM SET_TAC[];
        SUBGOAL_THEN `(\z:real^3. (H':real^3->real^N) (rho % z)) =
                      H' o (\z. rho % z)` SUBST1_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_SCALING];
          ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `IMAGE (H:real^N->real^3) u` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `p:real^N` THEN
        DISCH_TAC THEN
        ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ;
                     VECTOR_MUL_LID] THEN
        ASM SET_TAC[]];
      MATCH_MP_TAC PL_MAP_ON_CMUL THEN MATCH_MP_TAC PL_MAP_ON_SUBSET THEN
      EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `open_in (subtopology euclidean u) (u':real^N->bool)` THEN
      REWRITE_TAC[OPEN_IN_OPEN] THEN
      DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOCALLY_POLYHEDRAL_INTER_OPEN THEN
      ASM_MESON_TAC[PL_MAP_ON_IMP_LOCALLY_POLYHEDRAL]];
    EXPAND_TAC "u'" THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
    X_GEN_TAC `z:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `p:real^N` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `norm((H:real^N->real^3) p) < rho` ASSUME_TAC THENL
       [ASM_MESON_TAC[IN_BALL_0]; ALL_TAC] THEN
      SUBGOAL_THEN `(H:real^N->real^3) p IN K INTER ball(vec 0,rho)` MP_TAC THENL
       [UNDISCH_TAC `IMAGE (H:real^N->real^3) u INTER ball(vec 0,rho) =
                     K INTER ball(vec 0,rho)` THEN
        DISCH_THEN(fun th -> REWRITE_TAC[SYM th] THEN ASSUME_TAC th) THEN
        ASM_SIMP_TAC[IN_INTER; FUN_IN_IMAGE];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_INTER; IN_BALL_0] THEN STRIP_TAC THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[NORM_MUL; REAL_ABS_INV; REAL_ARITH `&0 < rho ==> abs rho = rho`] THEN
        ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
        ASM_SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ; REAL_MUL_LID];
        UNDISCH_TAC `!z t. z IN K /\ &0 < t ==> t % (z:real^3) IN K` THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ]];
      REWRITE_TAC[IN_BALL_0] THEN STRIP_TAC THEN
      SUBGOAL_THEN `rho % (z:real^3) IN K INTER ball(vec 0,rho)` MP_TAC THENL
       [REWRITE_TAC[IN_INTER; IN_BALL_0] THEN CONJ_TAC THENL
         [UNDISCH_TAC `!z t. z IN K /\ &0 < t ==> t % (z:real^3) IN K` THEN
          DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          ASM_SIMP_TAC[NORM_MUL; REAL_ARITH `&0 < rho ==> abs rho = rho`] THEN
          GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
          MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      UNDISCH_TAC `IMAGE (H:real^N->real^3) u INTER ball(vec 0,rho) =
                   K INTER ball(vec 0,rho)` THEN
      DISCH_THEN(fun th -> REWRITE_TAC[SYM th]) THEN
      REWRITE_TAC[IN_INTER; IN_IMAGE; IN_BALL_0] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `p:real^N` STRIP_ASSUME_TAC)
        ASSUME_TAC) THEN
      EXISTS_TAC `p:real^N` THEN ASM_REWRITE_TAC[IN_BALL_0] THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
        ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
        UNDISCH_TAC `rho % (z:real^3) = H(p:real^N)` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]]]]);;

let MOI_LGB2_TRANSFER = prove
 (`!(c:(real^N->bool)->bool) (g:real^2->real^N) y x1 x2 u (H:real^N->real^3) H'
    N1 N2 K O.
     moi_lt_singular_disk c g /\
     x1 IN std_triangle /\ x2 IN std_triangle /\ ~(x1 = x2) /\ g x1 = y /\ g x2 = y /\
     open_in (subtopology euclidean (UNIONS c)) u /\ y IN u /\
     homeomorphism (u,IMAGE H u) (H,H') /\ pl_map_on u H /\ H y = vec 0 /\
     (!z t. z IN K /\ &0 < t ==> t % z IN K) /\
     (?r0. &0 < r0 /\ IMAGE H u INTER ball(vec 0,r0) = K INTER ball(vec 0,r0)) /\
     open_in (subtopology euclidean std_triangle) N1 /\
     open_in (subtopology euclidean std_triangle) N2 /\
     x1 IN N1 /\ x2 IN N2 /\ DISJOINT N1 N2 /\
     IMAGE g N1 SUBSET u /\ IMAGE g N2 SUBSET u /\
     (!x x'. x IN N1 /\ x' IN N1 /\ g x = g x' ==> x = x') /\
     (!x x'. x IN N2 /\ x' IN N2 /\ g x = g x' ==> x = x') /\
     (!x. x IN N1 ==> (H(g x))$1 = &0) /\ (!x. x IN N2 ==> (H(g x))$2 = &0) /\
     (?eta1. &0 < eta1 /\
             !z. z IN K /\ z$1 = &0 /\ norm z < eta1 ==> z IN IMAGE (H o g) N1) /\
     (?eta2. &0 < eta2 /\
             !z. z IN K /\ z$2 = &0 /\ norm z < eta2 ==> z IN IMAGE (H o g) N2) /\
     open_in (subtopology euclidean (UNIONS c)) O /\ y IN O
     ==> ?u' rho n1 n2.
           &0 < rho /\ open_in (subtopology euclidean (UNIONS c)) u' /\ y IN u' /\
           u' SUBSET u /\ u' SUBSET O /\
           pl_homeomorphism (u',IMAGE (\p. inv rho % H p) u')
                            ((\p. inv rho % H p),(\z. H'(rho % z))) /\
           IMAGE (\p. inv rho % H p) u' = ball(vec 0,&1) INTER K /\
           {x | x IN std_triangle /\ g x IN u'} = n1 UNION n2 /\ DISJOINT n1 n2 /\
           IMAGE ((\p. inv rho % H p) o g) n1 =
           IMAGE (\p. inv rho % H p) u' INTER {z:real^3 | z$1 = &0} /\
           IMAGE ((\p. inv rho % H p) o g) n2 =
           IMAGE (\p. inv rho % H p) u' INTER {z:real^3 | z$2 = &0} /\
           IMAGE (\p. inv rho % H p) (moi_lt_double_image g INTER u') =
           IMAGE (\p. inv rho % H p) u' INTER {z:real^3 | z$1 = &0 /\ z$2 = &0} /\
           open_in (subtopology euclidean {x | x IN std_triangle /\ g x IN u'}) n1 /\
           open_in (subtopology euclidean {x | x IN std_triangle /\ g x IN u'}) n2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(g:real^2->real^N) continuous_on std_triangle` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN
    UNDISCH_TAC `moi_lt_singular_disk c (g:real^2->real^N)` THEN
    REWRITE_TAC[moi_lt_singular_disk] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(N1:real^2->bool) SUBSET std_triangle /\ N2 SUBSET std_triangle /\
                u SUBSET UNIONS (c:(real^N->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC OPEN_IN_IMP_SUBSET THENL
     [EXISTS_TAC `euclidean:(real^2)topology`;
      EXISTS_TAC `euclidean:(real^2)topology`;
      EXISTS_TAC `euclidean:(real^N)topology`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^2->real^N`; `y:real^N`; `N1:real^2->bool`; `N2:real^2->bool`]
    MOI_LGB2_NEAR_PREIMAGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:real^2->real^N`; `y:real^N`;
                   `x1:real^2`; `x2:real^2`] MOI_LGB2_PREIMAGE2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[IN_UNION];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "near"))) THEN
  MP_TAC(GEN_REWRITE_RULE I [OPEN_IN_CONTAINS_BALL]
    (ASSUME `open_in (subtopology euclidean (UNIONS c)) (O:real^N->bool)`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `y:real^N`)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`u:real^N->bool`; `H:real^N->real^3`; `H':real^3->real^N`;
                 `y:real^N`; `min e1 e2`] MOI_LGB2_CHART_SHRINK) THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; VECTOR_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "shr"))) THEN
  ABBREV_TAC `rho = min (min r0 r1) (min eta1 eta2)` THEN
  SUBGOAL_THEN `&0 < rho /\ rho <= r0 /\ rho <= r1 /\ rho <= eta1 /\ rho <= eta2`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "rho" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `u:real^N->bool`; `H:real^N->real^3`;
                 `H':real^3->real^N`; `y:real^N`; `K:real^3->bool`; `rho:real`]
    MOI_LGB2_TRANSFER_CHART) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (H:real^N->real^3) u INTER ball(vec 0,r0) =
                 K INTER ball(vec 0,r0)` THEN
    SUBGOAL_THEN `ball(vec 0:real^3,rho) SUBSET ball(vec 0,r0)` MP_TAC THENL
     [MATCH_MP_TAC SUBSET_BALL THEN ASM_REWRITE_TAC[]; SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `u' = {p | p IN u /\ (H:real^N->real^3) p IN ball(vec 0,rho)}` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!p:real^N. p IN u' <=> p IN u /\ norm((H:real^N->real^3) p) < rho`
  ASSUME_TAC THENL
   [EXPAND_TAC "u'" THEN REWRITE_TAC[IN_ELIM_THM; IN_BALL_0]; ALL_TAC] THEN
  SUBGOAL_THEN `!p:real^N. p IN u' ==> dist(p,y) < e1 /\ dist(p,y) < e2`
  ASSUME_TAC THENL
   [GEN_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    USE_THEN "shr" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN std_triangle /\ (g:real^2->real^N) x IN u'
                    ==> x IN N1 \/ x IN N2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM IN_UNION] THEN
    USE_THEN "near" MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE ((\p. inv rho % (H:real^N->real^3) p) o (g:real^2->real^N))
          {x | x IN N1 /\ g x IN u'} =
    (ball(vec 0,&1) INTER K) INTER {z:real^3 | z$1 = &0}`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER; IN_ELIM_THM; o_THM; IN_BALL_0] THEN
    X_GEN_TAC `z:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(z:real^3) IN IMAGE (\p. inv rho % (H:real^N->real^3) p) u'`
      MP_TAC THENL
       [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(g:real^2->real^N) x` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_INTER; IN_BALL_0] THEN SIMP_TAC[] THEN DISCH_TAC THEN
      ASM_SIMP_TAC[VECTOR_MUL_COMPONENT; REAL_MUL_RZERO];
      STRIP_TAC THEN
      SUBGOAL_THEN `rho % (z:real^3) IN IMAGE ((H:real^N->real^3) o (g:real^2->real^N)) N1`
      MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o
          check (fun th -> can (term_match [] `!z. z IN K /\ z$1 = &0 /\ norm z < e
                                                   ==> z IN IMAGE (f:real^2->real^3) s`)
                                (concl th))) THEN
        REPEAT CONJ_TAC THENL
         [UNDISCH_TAC `!z t. z IN K /\ &0 < t ==> t % (z:real^3) IN K` THEN
          DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[VECTOR_MUL_COMPONENT; REAL_MUL_RZERO];
          ASM_SIMP_TAC[NORM_MUL; REAL_ARITH `&0 < rho ==> abs rho = rho`] THEN
          MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `rho:real` THEN
          ASM_REWRITE_TAC[] THEN
          GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
          MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE; o_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
        ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [UNDISCH_TAC `IMAGE (g:real^2->real^N) N1 SUBSET u` THEN
          UNDISCH_TAC `(x:real^2) IN N1` THEN SET_TAC[];
          FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
          ASM_SIMP_TAC[NORM_MUL; REAL_ARITH `&0 < rho ==> abs rho = rho`] THEN
          GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
          MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE ((\p. inv rho % (H:real^N->real^3) p) o (g:real^2->real^N))
          {x | x IN N2 /\ g x IN u'} =
    (ball(vec 0,&1) INTER K) INTER {z:real^3 | z$2 = &0}`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER; IN_ELIM_THM; o_THM; IN_BALL_0] THEN
    X_GEN_TAC `z:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(z:real^3) IN IMAGE (\p. inv rho % (H:real^N->real^3) p) u'`
      MP_TAC THENL
       [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(g:real^2->real^N) x` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_INTER; IN_BALL_0] THEN SIMP_TAC[] THEN DISCH_TAC THEN
      ASM_SIMP_TAC[VECTOR_MUL_COMPONENT; REAL_MUL_RZERO];
      STRIP_TAC THEN
      SUBGOAL_THEN `rho % (z:real^3) IN IMAGE ((H:real^N->real^3) o (g:real^2->real^N)) N2`
      MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o
          check (fun th -> can (term_match [] `!z. z IN K /\ z$2 = &0 /\ norm z < e
                                                   ==> z IN IMAGE (f:real^2->real^3) s`)
                                (concl th))) THEN
        REPEAT CONJ_TAC THENL
         [UNDISCH_TAC `!z t. z IN K /\ &0 < t ==> t % (z:real^3) IN K` THEN
          DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[VECTOR_MUL_COMPONENT; REAL_MUL_RZERO];
          ASM_SIMP_TAC[NORM_MUL; REAL_ARITH `&0 < rho ==> abs rho = rho`] THEN
          MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `rho:real` THEN
          ASM_REWRITE_TAC[] THEN
          GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
          MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE; o_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
        ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [UNDISCH_TAC `IMAGE (g:real^2->real^N) N2 SUBSET u` THEN
          UNDISCH_TAC `(x:real^2) IN N2` THEN SET_TAC[];
          FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
          ASM_SIMP_TAC[NORM_MUL; REAL_ARITH `&0 < rho ==> abs rho = rho`] THEN
          GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
          MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]]]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`u':real^N->bool`; `rho:real`;
                        `{x | x IN N1 /\ (g:real^2->real^N) x IN u'}`;
                        `{x | x IN N2 /\ (g:real^2->real^N) x IN u'}`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [EXPAND_TAC "u'" THEN SET_TAC[];
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o
      check (fun th -> can (term_match [] `ball(a:real^N,b) INTER s SUBSET t`) (concl th))) THEN
    REWRITE_TAC[IN_INTER; IN_BALL] THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `(p:real^N) IN u'` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `u SUBSET UNIONS (c:(real^N->bool)->bool)` THEN SET_TAC[];
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNION] THEN X_GEN_TAC `x:real^2` THEN
    EQ_TAC THENL
     [STRIP_TAC THEN
      SUBGOAL_THEN `(x:real^2) IN N1 \/ x IN N2` MP_TAC THENL
       [UNDISCH_TAC `!x. x IN std_triangle /\ (g:real^2->real^N) x IN u'
                         ==> x IN N1 \/ x IN N2` THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        STRIP_TAC THEN ASM_REWRITE_TAC[]];
      DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THENL
       [UNDISCH_TAC `(N1:real^2->bool) SUBSET std_triangle` THEN
        UNDISCH_TAC `(x:real^2) IN N1` THEN SET_TAC[];
        UNDISCH_TAC `(N2:real^2->bool) SUBSET std_triangle` THEN
        UNDISCH_TAC `(x:real^2) IN N2` THEN SET_TAC[]]];
    UNDISCH_TAC `DISJOINT (N1:real^2->bool) N2` THEN SET_TAC[];
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
    SUBGOAL_THEN
     `!p q:real^N. p IN u' /\ q IN u' /\
                   inv rho % (H:real^N->real^3) p = inv rho % H q ==> p = q`
    ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN REWRITE_TAC[VECTOR_MUL_LCANCEL; REAL_INV_EQ_0] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(p:real^N) IN u /\ (q:real^N) IN u` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `!x:real^N. x IN u ==> (H':real^3->real^N) (H x) = x` THEN
      DISCH_THEN(fun th -> ONCE_REWRITE_TAC[GSYM(MATCH_MP th
        (ASSUME `(p:real^N) IN u`))] THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM(MATCH_MP th (ASSUME `(q:real^N) IN u`))]) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `p:real^N` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      REWRITE_TAC[moi_lt_double_image; IN_ELIM_THM] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^2` (X_CHOOSE_THEN `x':real^2`
        STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
      SUBGOAL_THEN `(?w. w IN N1 /\ (g:real^2->real^N) w = p) /\
                    (?w. w IN N2 /\ (g:real^2->real^N) w = p)`
      STRIP_ASSUME_TAC THENL
       [SUBGOAL_THEN `((x:real^2) IN N1 \/ x IN N2) /\ (x' IN N1 \/ x' IN N2)`
        MP_TAC THENL
         [CONJ_TAC THEN
          UNDISCH_TAC `!x. x IN std_triangle /\ (g:real^2->real^N) x IN u'
                           ==> x IN N1 \/ x IN N2` THEN
          DISCH_THEN MATCH_MP_TAC THEN
          REWRITE_TAC[ASSUME `(g:real^2->real^N) x = p`;
                      ASSUME `(g:real^2->real^N) x' = p`] THEN
          CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `~((x:real^2) IN N1 /\ x' IN N1) /\ ~(x IN N2 /\ x' IN N2)`
        MP_TAC THENL
         [CONJ_TAC THEN STRIP_TAC THEN UNDISCH_TAC `~(x:real^2 = x')` THEN
          REWRITE_TAC[] THENL
           [UNDISCH_TAC `!x x'. x IN N1 /\ x' IN N1 /\ (g:real^2->real^N) x = g x'
                                ==> x = x'`;
            UNDISCH_TAC `!x x'. x IN N2 /\ x' IN N2 /\ (g:real^2->real^N) x = g x'
                                ==> x = x'`] THEN
          DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        UNDISCH_TAC `(g:real^2->real^N) x = p` THEN
        UNDISCH_TAC `(g:real^2->real^N) x' = p` THEN MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(z:real^3) IN IMAGE (\p. inv rho % (H:real^N->real^3) p) u'`
      MP_TAC THENL
       [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `p:real^N` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_INTER] THEN SIMP_TAC[] THEN DISCH_TAC THEN
      ASM_REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN
      UNDISCH_TAC `(w:real^2) IN N1` THEN UNDISCH_TAC `(g:real^2->real^N) w = p` THEN
      UNDISCH_TAC `(w':real^2) IN N2` THEN UNDISCH_TAC `(g:real^2->real^N) w' = p` THEN
      REPEAT DISCH_TAC THEN
      SUBGOAL_THEN `((H:real^N->real^3) p)$1 = &0 /\ (H p)$2 = &0`
      (fun th -> REWRITE_TAC[th; REAL_MUL_RZERO]) THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `(g:real^2->real^N) w = p` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        ASM_SIMP_TAC[];
        UNDISCH_TAC `(g:real^2->real^N) w' = p` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        ASM_SIMP_TAC[]];
      STRIP_TAC THEN
      SUBGOAL_THEN
       `(z:real^3) IN IMAGE ((\p. inv rho % (H:real^N->real^3) p) o (g:real^2->real^N))
                     {x | x IN N1 /\ g x IN u'} /\
        z IN IMAGE ((\p. inv rho % H p) o g) {x | x IN N2 /\ g x IN u'}`
      MP_TAC THENL [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE; o_THM; IN_ELIM_THM] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC)
        (X_CHOOSE_THEN `x':real^2` STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `(g:real^2->real^N) x' = g x` ASSUME_TAC THENL
       [UNDISCH_TAC `!p q:real^N. p IN u' /\ q IN u' /\
                      inv rho % (H:real^N->real^3) p = inv rho % H q ==> p = q` THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `z = inv rho % (H:real^N->real^3) ((g:real^2->real^N) x)` THEN
        UNDISCH_TAC `z = inv rho % (H:real^N->real^3) ((g:real^2->real^N) x')` THEN
        MESON_TAC[];
        ALL_TAC] THEN
      EXISTS_TAC `(g:real^2->real^N) x` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[moi_lt_double_image; IN_ELIM_THM] THEN
      MAP_EVERY EXISTS_TAC [`x:real^2`; `x':real^2`] THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `(N1:real^2->bool) SUBSET std_triangle` THEN
        UNDISCH_TAC `(x:real^2) IN N1` THEN SET_TAC[];
        UNDISCH_TAC `(N2:real^2->bool) SUBSET std_triangle` THEN
        UNDISCH_TAC `(x':real^2) IN N2` THEN SET_TAC[];
        UNDISCH_TAC `DISJOINT (N1:real^2->bool) N2` THEN
        UNDISCH_TAC `(x:real^2) IN N1` THEN UNDISCH_TAC `(x':real^2) IN N2` THEN
        SET_TAC[]]];
    UNDISCH_TAC `open_in (subtopology euclidean std_triangle) (N1:real^2->bool)` THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^2->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `v:real^2->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    UNDISCH_TAC `open_in (subtopology euclidean std_triangle) (N2:real^2->bool)` THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^2->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `v:real^2->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

(* ========================================================================= *)
(* Generic facts for the local analysis: carriers and stars in a            *)
(* simplicial complex, affine images of affine hulls, pulling inclusions    *)
(* of affine hulls back through a map affine and injective on a convex set. *)
(* ========================================================================= *)

let MOI_LGB2_SC_CARRIER = prove
 (`!(K:(real^N->bool)->bool) x.
     simplicial_complex K /\ x IN UNIONS K
     ==> ?s. s IN K /\ x IN relative_interior s /\
             !t. t IN K /\ x IN t ==> s face_of t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `lf_simplicial_complex (K:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FMB_SC_LF]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `x:real^N`] IN_RELATIVE_INTERIOR_OF_FACE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MOI_FM3_LF_CONVEX]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(s:real^N->bool) IN K` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FM3_LF_FACE]; ALL_TAC] THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t':real^N->bool` THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_FM3_LF_SUBSET_FACE THEN EXISTS_TAC `K:(real^N->bool)->bool` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FM3_LF_RELINT_SUBSET THEN
  MAP_EVERY EXISTS_TAC [`K:(real^N->bool)->bool`; `x:real^N`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_LGB2_STAR_NBHD = prove
 (`!(K:(real^N->bool)->bool) x.
     simplicial_complex K
     ==> ?d. &0 < d /\
             !z. z IN UNIONS K /\ dist(z,x) < d ==> ?r. r IN K /\ x IN r /\ z IN r`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `M = UNIONS {r | r IN K /\ ~((x:real^N) IN r)}` THEN
  SUBGOAL_THEN `closed (M:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_MESON_TAC[simplicial_complex];
      REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_MESON_TAC[MOI_FMB_SC_LF; MOI_FM3_LF_COMPACT; COMPACT_IMP_CLOSED]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((x:real^N) IN M)` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`x:real^N`; `M:real^N->bool`] CLOSED_APPROACHABLE) THEN
  ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real^N` THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC)
    ASSUME_TAC) THEN
  EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(x:real^N) IN r` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N`) THEN ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "M" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

let MOI_LGB2_AFF_IMAGE = prove
 (`!(l:real^M->real^N) b s.
     linear l
     ==> IMAGE (\x. l x + b) (affine hull s) = affine hull (IMAGE (\x. l x + b) s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!t:real^M->bool. IMAGE (\x. l x + b) t =
                                  IMAGE (\x:real^N. b + x) (IMAGE l t)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
    MATCH_MP_TAC IMAGE_EQ THEN REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    ASM_SIMP_TAC[AFFINE_HULL_TRANSLATION; AFFINE_HULL_LINEAR_IMAGE]]);;

let MOI_LGB2_PULLBACK_HULL = prove
 (`!(l:real^M->real^N) b (s:real^M->bool) X Y.
     linear l /\ convex s /\
     (!x y. x IN s /\ y IN s /\ l x + b = l y + b ==> x = y) /\
     X SUBSET s /\ Y SUBSET s /\
     IMAGE (\x. l x + b) X SUBSET affine hull (IMAGE (\x. l x + b) Y)
     ==> X SUBSET affine hull Y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^M. (l:real^M->real^N) x + b`; `l:real^M->real^N`;
                 `b:real^N`; `s:real^M->bool`] MOI_LGA_LEFT_INVERSE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^M` (X_CHOOSE_THEN `l':real^N->real^M`
    (X_CHOOSE_THEN `b':real^M` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `!x:real^M. x IN affine hull s ==> g((l:real^M->real^N) x + b) = x`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(l':real^N->real^M) o (l:real^M->real^N)`; `\x:real^M. x`;
                   `(l':real^N->real^M) b + b'`; `vec 0:real^M`; `s:real^M->bool`]
      MOI_REAL_AFFINE_EQ_ON_AFFINE_HULL) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[LINEAR_COMPOSE; LINEAR_ID; o_THM; VECTOR_ADD_RID] THEN
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      MP_TAC(MATCH_MP (ASSUME `!x:real^M. x IN s ==> g((l:real^M->real^N) x + b) = x`)
                      (ASSUME `(x:real^M) IN s`)) THEN
      REWRITE_TAC[ASSUME `!z:real^N. (g:real^N->real^M) z = l' z + b'`] THEN
      SIMP_TAC[MATCH_MP LINEAR_ADD (ASSUME `linear (l':real^N->real^M)`)] THEN
      VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[o_THM; VECTOR_ADD_RID; LINEAR_ADD; VECTOR_ADD_ASSOC] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VECTOR_ADD_ASSOC];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  UNDISCH_TAC `IMAGE (\x. (l:real^M->real^N) x + b) X SUBSET
               affine hull (IMAGE (\x. l x + b) Y)` THEN
  ASM_SIMP_TAC[GSYM MOI_LGB2_AFF_IMAGE] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `x':real^M` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:real^M) IN affine hull s /\ x' IN affine hull s` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC HULL_INC THEN UNDISCH_TAC `(X:real^M->bool) SUBSET s` THEN
      UNDISCH_TAC `(x:real^M) IN X` THEN SET_TAC[];
      MATCH_MP_TAC(SET_RULE `!(a:real^M->bool) b (z:real^M). a SUBSET b /\ z IN a ==> z IN b`) THEN
      EXISTS_TAC `affine hull (Y:real^M->bool)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HULL_MONO THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `x:real^M = x'` (fun th -> ASM_REWRITE_TAC[th]) THEN
  MP_TAC(SPEC `x:real^M` (ASSUME
    `!x:real^M. x IN affine hull s ==> g((l:real^M->real^N) x + b) = x`)) THEN
  MP_TAC(SPEC `x':real^M` (ASSUME
    `!x:real^M. x IN affine hull s ==> g((l:real^M->real^N) x + b) = x`)) THEN
  REWRITE_TAC[ASSUME `(x:real^M) IN affine hull s`;
              ASSUME `(x':real^M) IN affine hull s`;
              ASSUME `(l:real^M->real^N) x + b = l x' + b`] THEN
  MESON_TAC[]);;

(* ========================================================================= *)
(* The source side of the local analysis.  For a triangulation L            *)
(* of std_triangle: carriers are faces, no edge has three triangles, an     *)
(* interior edge has exactly two triangles and an edge in the frontier      *)
(* exactly one; the triangles on an edge cover a neighbourhood of each      *)
(* point of its relative interior.                                          *)
(* ========================================================================= *)

let MOI_LGB2_CARRIER_FACE = prove
 (`!(K:(real^N->bool)->bool) e r x.
     simplicial_complex K /\ e IN K /\ r IN K /\
     x IN relative_interior e /\ x IN r
     ==> e face_of r`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SCF_SUBSET_FACE THEN
  EXISTS_TAC `K:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_SCF_RELINT_SUBSET THEN
  MAP_EVERY EXISTS_TAC [`K:(real^N->bool)->bool`; `x:real^N`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_LGB2_DISK_NOT3 = prove
 (`!L:(real^2->bool)->bool e t1 t2 t3.
        simplicial_complex L /\
        e IN L /\ aff_dim e = &1 /\
        t1 IN L /\ aff_dim t1 = &2 /\ e SUBSET t1 /\
        t2 IN L /\ aff_dim t2 = &2 /\ e SUBSET t2 /\
        t3 IN L /\ aff_dim t3 = &2 /\ e SUBSET t3 /\
        ~(t1 = t2) /\ ~(t1 = t3) /\ ~(t2 = t3)
        ==> F`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `e:real^2->bool`] MOI_SCF_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^2` (X_CHOOSE_THEN `b:real^2`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `a:real^2`; `b:real^2`;
                 `t1:real^2->bool`] MOI_SCF_TRIANGLE_ON_EDGE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `a:real^2`; `b:real^2`;
                 `t2:real^2->bool`] MOI_SCF_TRIANGLE_ON_EDGE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c2:real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(c1:real^2 = c2)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(t1:real^2->bool = t2)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `convex hull {a,b,c1} INTER convex hull {a,b,c2} = convex hull {a:real^2,b}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `{a:real^2,b,c1}`;
                   `{a:real^2,b,c2}`] MOI_REAL_SIMPLICIAL_COMPLEX_INTER_HULL) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^2`; `b:real^2`; `c1:real^2`; `c2:real^2`]
    MOI_SCF_UNFOLD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^2` (X_CHOOSE_THEN `W:real^2->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC))))))) THEN
  MP_TAC(ISPECL [`f:real^2->real^2`; `W:real^2->bool`] INVARIANCE_OF_DOMAIN) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `(f:real^2->real^2) z`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(f:real^2->real^2) z IN closure(relative_interior t3)`
  MP_TAC THENL
   [MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `t3:real^2->bool`]
      MOI_CON_SC_CONVEX) THEN
    MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `t3:real^2->bool`]
      MOI_SCF_SC_CLOSED) THEN
    ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
  DISCH_THEN(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:real^2) IN IMAGE (f:real^2->real^2) W` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_BALL] THEN ASM_MESON_TAC[DIST_SYM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `t3:real^2->bool`;
                 `t1:real^2->bool`] MOI_SCF_DISTINCT_RELINT) THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `t3:real^2->bool`;
                 `t2:real^2->bool`] MOI_SCF_DISTINCT_RELINT) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `IMAGE (f:real^2->real^2) W SUBSET
               convex hull {a,b,c1} UNION convex hull {a,b,c2}` THEN
  UNDISCH_TAC `(y:real^2) IN IMAGE (f:real^2->real^2) W` THEN
  UNDISCH_TAC `(y:real^2) IN relative_interior t3` THEN
  SUBGOAL_THEN `~(t3:real^2->bool = t1) /\ ~(t3 = t2)` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let MOI_LGB2_STD_DIM = prove
 (`aff_dim std_triangle = &2`,
  MESON_TAC[MOI_LTD_STD_TRIANGLE_SIMPLEX; AFF_DIM_SIMPLEX]);;

let MOI_LGB2_DIM_LE_2 = prove
 (`!s:real^2->bool. aff_dim s <= &2`,
  GEN_TAC THEN MP_TAC(ISPEC `s:real^2->bool` AFF_DIM_LE_UNIV) THEN
  REWRITE_TAC[DIMINDEX_2]);;

let MOI_LGB2_EDGE_SOME = prove
 (`!L:(real^2->bool)->bool e.
     simplicial_complex L /\ UNIONS L = std_triangle /\ e IN L /\ aff_dim e = &1
     ==> ?t. t IN L /\ aff_dim t = &2 /\ e SUBSET t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `convex (e:real^2->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_CON_SC_CONVEX]; ALL_TAC] THEN
  SUBGOAL_THEN `~(relative_interior (e:real^2->bool) = {})` MP_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY] THEN DISCH_TAC THEN
    UNDISCH_TAC `aff_dim (e:real^2->bool) = &1` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `x:real^2`) THEN
  SUBGOAL_THEN `(x:real^2) IN e` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `x:real^2`] MOI_LGB2_STAR_NBHD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "star"))) THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  SUBGOAL_THEN `std_triangle INTER ball(x:real^2,d) SUBSET e` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; IN_BALL] THEN X_GEN_TAC `z:real^2` THEN
    STRIP_TAC THEN
    USE_THEN "star" (MP_TAC o SPEC `z:real^2`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[DIST_SYM]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^2->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(e:real^2->bool) face_of r` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_LGB2_CARRIER_FACE THEN
      MAP_EVERY EXISTS_TAC [`L:(real^2->bool)->bool`; `x:real^2`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `e:real^2->bool = r` (fun th -> ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`e:real^2->bool`; `r:real^2->bool`] FACE_OF_AFF_DIM_LT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MOI_CON_SC_CONVEX]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `!t. ~(t IN L /\ aff_dim t = &2 /\ (e:real^2->bool) SUBSET t)` THEN
    REWRITE_TAC[NOT_FORALL_THM] THEN EXISTS_TAC `r:real^2->bool` THEN
    ASM_SIMP_TAC[FACE_OF_IMP_SUBSET] THEN
    MP_TAC(ISPEC `r:real^2->bool` MOI_LGB2_DIM_LE_2) THEN
    UNDISCH_TAC `&1 < aff_dim (r:real^2->bool)` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`std_triangle`; `ball(x:real^2,d)`] AFF_DIM_CONVEX_INTER_OPEN) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[MOI_LTD_STD_TRIANGLE_BASIC; OPEN_BALL] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `x:real^2` THEN
    REWRITE_TAC[IN_INTER; CENTRE_IN_BALL] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[IN_UNIONS];
    ALL_TAC] THEN
  REWRITE_TAC[MOI_LGB2_STD_DIM] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`std_triangle INTER ball(x:real^2,d)`; `e:real^2->bool`]
    AFF_DIM_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN INT_ARITH_TAC);;

let MOI_LGB2_EDGE_LOCAL = prove
 (`!L:(real^2->bool)->bool e x.
     simplicial_complex L /\ UNIONS L = std_triangle /\ e IN L /\ aff_dim e = &1 /\
     x IN relative_interior e
     ==> ?d. &0 < d /\
             !z. z IN std_triangle /\ dist(z,x) < d
                 ==> ?t. t IN L /\ aff_dim t = &2 /\ e SUBSET t /\ z IN t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `x:real^2`] MOI_LGB2_STAR_NBHD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^2`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^2->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(e:real^2->bool) face_of r` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LGB2_CARRIER_FACE THEN
    MAP_EVERY EXISTS_TAC [`L:(real^2->bool)->bool`; `x:real^2`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `e:real^2->bool = r` THENL
   [MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `e:real^2->bool`]
      MOI_LGB2_EDGE_SOME) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^2->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t:real^2->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `r:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[FACE_OF_IMP_SUBSET] THEN
  MP_TAC(ISPECL [`e:real^2->bool`; `r:real^2->bool`] FACE_OF_AFF_DIM_LT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MOI_CON_SC_CONVEX]; ALL_TAC] THEN
  MP_TAC(ISPEC `r:real^2->bool` MOI_LGB2_DIM_LE_2) THEN
  ASM_REWRITE_TAC[] THEN INT_ARITH_TAC);;

let MOI_LGB2_EDGE_INTERIOR = prove
 (`!L:(real^2->bool)->bool e x.
     simplicial_complex L /\ UNIONS L = std_triangle /\ e IN L /\ aff_dim e = &1 /\
     x IN relative_interior e /\ ~(x IN relative_frontier std_triangle)
     ==> ?t1 t2. t1 IN L /\ aff_dim t1 = &2 /\ e SUBSET t1 /\
                 t2 IN L /\ aff_dim t2 = &2 /\ e SUBSET t2 /\ ~(t1 = t2) /\
                 !t. t IN L /\ aff_dim t = &2 /\ e SUBSET t ==> t = t1 \/ t = t2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `e:real^2->bool`]
    MOI_LGB2_EDGE_SOME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real^2->bool` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC
   `?t2:real^2->bool. t2 IN L /\ aff_dim t2 = &2 /\ e SUBSET t2 /\ ~(t2 = t1)` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `t2:real^2->bool` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`t1:real^2->bool`; `t2:real^2->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    TRY(CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
    X_GEN_TAC `t:real^2->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[DE_MORGAN_THM]) THEN
    MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `e:real^2->bool`; `t1:real^2->bool`;
                   `t2:real^2->bool`; `t:real^2->bool`] MOI_LGB2_DISK_NOT3) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `std_triangle`; `\x:real^2. x`;
                 `\x:real^2. x`; `e:real^2->bool`; `t1:real^2->bool`]
    MOI_FM3_DISK_EDGE1) THEN
  ASM_REWRITE_TAC[MOI_LTD_STD_TRIANGLE_SIMPLEX; HOMEOMORPHISM_ID; IMAGE_ID] THEN
  ANTS_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN
    X_GEN_TAC `t:real^2->bool` THEN EQ_TAC THENL
     [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `~((x:real^2) IN relative_frontier std_triangle)` THEN
  UNDISCH_TAC `(x:real^2) IN relative_interior e` THEN
  MP_TAC(ISPEC `e:real^2->bool` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[]);;

let MOI_LGB2_EDGE_FRONTIER = prove
 (`!L:(real^2->bool)->bool e.
     simplicial_complex L /\ UNIONS L = std_triangle /\ e IN L /\ aff_dim e = &1 /\
     e SUBSET relative_frontier std_triangle
     ==> ?t1. t1 IN L /\ aff_dim t1 = &2 /\ e SUBSET t1 /\
              !t. t IN L /\ aff_dim t = &2 /\ e SUBSET t ==> t = t1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `e:real^2->bool`]
    MOI_LGB2_EDGE_SOME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real^2->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t1:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real^2->bool` THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `std_triangle`; `\x:real^2. x`;
                 `\x:real^2. x`; `e:real^2->bool`; `t:real^2->bool`;
                 `t1:real^2->bool`] MOI_FM3_DISK_EDGE2) THEN
  ASM_REWRITE_TAC[MOI_LTD_STD_TRIANGLE_SIMPLEX; HOMEOMORPHISM_ID; IMAGE_ID] THEN
  SUBGOAL_THEN `convex (e:real^2->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_CON_SC_CONVEX]; ALL_TAC] THEN
  SUBGOAL_THEN `~(relative_interior (e:real^2->bool) = {})` MP_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY] THEN DISCH_TAC THEN
    UNDISCH_TAC `aff_dim (e:real^2->bool) = &1` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `(e:real^2->bool) SUBSET relative_frontier std_triangle` THEN
  MP_TAC(ISPEC `e:real^2->bool` RELATIVE_INTERIOR_SUBSET) THEN
  REWRITE_TAC[relative_frontier] THEN SET_TAC[]);;

(* ========================================================================= *)
(* Vector facts in chart coordinates: planes through three points           *)
(* via the cross product, non-degenerate images of triangles, the half-     *)
(* plane parametrization of a triangle on an edge, vertices and opposite    *)
(* sides of two tetrahedra on a common facet, the non-folding of two         *)
(* triangles on an edge, and the local surjectivity at a boundary sheet.    *)
(* ========================================================================= *)

let MOI_LGB2_CROSS_DECOMP = prove
 (`!A B v:real^3.
     ((A cross B) dot (A cross B)) % v =
     ((v cross B) dot (A cross B)) % A + ((A cross v) dot (A cross B)) % B +
     (v dot (A cross B)) % (A cross B)`,
  VEC3_TAC);;

let MOI_LGB2_PLANE_CHAR = prove
 (`!P Q W z:real^3.
     ~((Q - P) cross (W - P) = vec 0)
     ==> (((Q - P) cross (W - P)) dot (z - P) = &0 <=>
          z IN affine hull {P,Q,W})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[AFFINE_HULL_3; IN_ELIM_THM] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`Q - P:real^3`; `W - P:real^3`; `z - P:real^3`]
      MOI_LGB2_CROSS_DECOMP) THEN
    ABBREV_TAC `n:real^3 = (Q - P) cross (W - P)` THEN
    ABBREV_TAC `al = ((z - P) cross (W - P)) dot (n:real^3)` THEN
    ABBREV_TAC `be = ((Q - P) cross (z - P)) dot (n:real^3)` THEN
    SUBGOAL_THEN `(z - P) dot (n:real^3) = &0` SUBST1_TAC THENL
     [ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((n:real^3) dot n = &0)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[DOT_EQ_0]; ALL_TAC] THEN
    SUBGOAL_THEN
     `z - P:real^3 = inv((n:real^3) dot n) % (al % (Q - P) + be % (W - P))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC VECTOR_MUL_LCANCEL_IMP THEN
      EXISTS_TAC `(n:real^3) dot n` THEN ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_RINV; VECTOR_MUL_LID];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC
     [`&1 - inv((n:real^3) dot n) * al - inv(n dot n) * be`;
      `inv((n:real^3) dot n) * al`; `inv((n:real^3) dot n) * be`] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC
     `z - P:real^3 = inv((n:real^3) dot n) % (al % (Q - P) + be % (W - P))` THEN
    VECTOR_ARITH_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(u % P + v % Q + w % W) - P:real^3 = v % (Q - P) + w % (W - P)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `u + v + w = &1` THEN
      REWRITE_TAC[REAL_ARITH `u + v + w = &1 <=> u = &1 - v - w`] THEN
      DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[DOT_RADD; DOT_RMUL; DOT_CROSS_SELF] THEN REAL_ARITH_TAC]);;

let MOI_LGB2_CROSS_INDEP2 = prove
 (`!d a:real^3 x y.
     ~(d cross a = vec 0) /\ x % d + y % a = vec 0 ==> x = &0 /\ y = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [SUBGOAL_THEN `x % (d cross a) = vec 0:real^3` MP_TAC THENL
     [SUBGOAL_THEN `(x % d + y % a) cross (a:real^3) = x % (d cross a)`
      (SUBST1_TAC o SYM) THENL
       [REWRITE_TAC[CROSS_LADD; CROSS_LMUL; CROSS_REFL; VECTOR_MUL_RZERO;
                    VECTOR_ADD_RID];
        ASM_REWRITE_TAC[CROSS_LZERO]];
      ASM_REWRITE_TAC[VECTOR_MUL_EQ_0]];
    SUBGOAL_THEN `y % (d cross a) = vec 0:real^3` MP_TAC THENL
     [ONCE_REWRITE_TAC[GSYM VECTOR_NEG_EQ_0] THEN
      SUBGOAL_THEN `(x % d + y % a) cross (d:real^3) = --(y % (d cross a))`
      (SUBST1_TAC o SYM) THENL
       [REWRITE_TAC[CROSS_LADD; CROSS_LMUL; CROSS_REFL; VECTOR_MUL_RZERO;
                    VECTOR_ADD_LID] THEN
        GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [CROSS_SKEW] THEN
        VECTOR_ARITH_TAC;
        ASM_REWRITE_TAC[CROSS_LZERO]];
      ASM_REWRITE_TAC[VECTOR_MUL_EQ_0]]]);;

let MOI_LGB2_NONDEG = prove
 (`!(f:real^2->real^3) l b p q w.
     linear l /\ ~affine_dependent {p,q,w} /\
     ~(p = q) /\ ~(p = w) /\ ~(q = w) /\
     (!x. x IN convex hull {p,q,w} ==> f x = l x + b) /\
     (!x y. x IN convex hull {p,q,w} /\ y IN convex hull {p,q,w} /\ f x = f y
            ==> x = y)
     ==> ~((f q - f p) cross (f w - f p) = vec 0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^2->real^3`; `l:real^2->real^3`; `b:real^3`;
                 `{p:real^2,q,w}`] MOI_LGA_INDEP_IMAGE) THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN
  SUBGOAL_THEN `(p:real^2) IN convex hull {p,q,w} /\ q IN convex hull {p,q,w} /\
                w IN convex hull {p,q,w}` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((f:real^2->real^3) p = f q) /\ ~(f p = f w) /\ ~(f q = f w)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `((f:real^2->real^3) q - f p) cross (f w - f p) = vec 0` THEN
  REWRITE_TAC[CROSS_EQ_0; GSYM COLLINEAR_3] THEN
  REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT] THEN
  SUBGOAL_THEN `{(f:real^2->real^3) q, f p, f w} = {f p, f q, f w}` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

let MOI_LGB2_TRI_PARAM = prove
 (`!(f:real^2->real^3) l b p q w x0 z.
     linear l /\ (!x. x IN convex hull {p,q,w} ==> f x = l x + b) /\
     x0 IN segment[p,q] /\ z IN convex hull {p,q,w}
     ==> ?t s. &0 <= s /\ f z = f x0 + t % (f q - f p) + s % (f w - f p)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(p:real^2) IN convex hull {p,q,w} /\ q IN convex hull {p,q,w} /\
                w IN convex hull {p,q,w} /\ x0 IN convex hull {p,q,w}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
      ALL_TAC] THEN
    UNDISCH_TAC `(x0:real^2) IN segment[p,q]` THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    MATCH_MP_TAC(SET_RULE `!a b (x:real^2). a SUBSET b ==> x IN a ==> x IN b`) THEN
    MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^2->real^3) z = l z + b /\ f x0 = l x0 + b /\
                f p = l p + b /\ f q = l q + b /\ f w = l w + b`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(z:real^2) IN convex hull {p,q,w}` THEN
  UNDISCH_TAC `(x0:real^2) IN segment[p,q]` THEN
  REWRITE_TAC[IN_SEGMENT; CONVEX_HULL_3; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `mu:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `al:real` (X_CHOOSE_THEN `be:real`
    (X_CHOOSE_THEN `ga:real` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`be - mu:real`; `ga:real`] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL] THEN
  UNDISCH_TAC `al + be + ga = &1` THEN
  REWRITE_TAC[REAL_ARITH `al + be + ga = &1 <=> al = &1 - be - ga`] THEN
  DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC);;

let MOI_LGB2_FOURTH = prove
 (`!V a b d:A. V HAS_SIZE 4 /\ a IN V /\ b IN V /\ d IN V /\
               ~(a = b) /\ ~(a = d) /\ ~(b = d)
               ==> ?e. ~(e = a) /\ ~(e = b) /\ ~(e = d) /\ V = {a,b,d,e}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:A->bool`; `{a:A,b,d}`; `4`; `3`] HAS_SIZE_DIFF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[HAS_SIZE] THEN
      SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
      ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV;
      ASM SET_TAC[]];
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV(RAND_CONV NUM_SUB_CONV)) THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_TAC `e:A`) THEN EXISTS_TAC `e:A` THEN
  ASM SET_TAC[]);;

let MOI_LGB2_TET_ON_TRI = prove
 (`!K a b d (t:real^N->bool).
     simplicial_complex K /\ t IN K /\ aff_dim t = &3 /\
     ~(a = b) /\ ~(a = d) /\ ~(b = d) /\ ~affine_dependent {a,b,d} /\
     convex hull {a,b,d} IN K /\ convex hull {a,b,d} SUBSET t
     ==> ?e. ~(e = a) /\ ~(e = b) /\ ~(e = d) /\ ~affine_dependent {a,b,d,e} /\
             t = convex hull {a,b,d,e}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `t:real^N->bool`]
    MOI_SCF_SC_VERTICES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(V:real^N->bool) HAS_SIZE 4` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[HAS_SIZE; GSYM INT_OF_NUM_EQ] THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {a:real^N,b,d} face_of t` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SCF_SUBSET_FACE]; ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^N) IN V /\ b IN V /\ d IN V` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(a:real^N) extreme_point_of t /\ b extreme_point_of t /\
      d extreme_point_of t`
    MP_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[GSYM FACE_OF_SING] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC FACE_OF_TRANS THEN
    EXISTS_TAC `convex hull {a:real^N,b,d}` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[FACE_OF_SING] THEN
    ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `a:real^N`; `b:real^N`; `d:real^N`]
    MOI_LGB2_FOURTH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e:real^N` THEN ASM_MESON_TAC[]);;

let MOI_LGB2_CONVEX_HULL_4 = prove
 (`!A B D E W:real^N.
     W IN convex hull {A,B,D,E}
     ==> ?u1 u2 u3 u4. &0 <= u1 /\ &0 <= u2 /\ &0 <= u3 /\ &0 <= u4 /\
                       u1 + u2 + u3 + u4 = &1 /\
                       W = u1 % A + u2 % B + u3 % D + u4 % E`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[CONVEX_HULL_INSERT; NOT_INSERT_EMPTY; CONVEX_HULL_3; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` (X_CHOOSE_THEN `v:real`
    (X_CHOOSE_THEN `z:real^N` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC))))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `x1:real` (X_CHOOSE_THEN `x2:real`
    (X_CHOOSE_THEN `x3:real` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`u:real`; `v * x1:real`; `v * x2:real`; `v * x3:real`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `x1 + x2 + x3 = &1` THEN UNDISCH_TAC `u + v = &1` THEN
    CONV_TAC REAL_RING;
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC]);;

let MOI_LGB2_NU_DET = prove
 (`!A B D W:real^3.
     ((B - A) cross (D - A)) dot (W - A) = det(vector[B - A; D - A; W - A])`,
  VEC3_TAC);;

let MOI_LGB2_WING_SIDE = prove
 (`!A B D E W:real^3.
     W IN convex hull {A,B,D,E}
     ==> W IN convex hull {A,B,D} \/
         ?eps. &0 < eps /\
               det(vector[B - A; D - A; W - A]) =
               eps * det(vector[B - A; D - A; E - A])`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MOI_LGB2_CONVEX_HULL_4) THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real` (X_CHOOSE_THEN `u2:real`
    (X_CHOOSE_THEN `u3:real` (X_CHOOSE_THEN `u4:real` STRIP_ASSUME_TAC)))) THEN
  ASM_CASES_TAC `u4 = &0` THENL
   [DISJ1_TAC THEN REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`u1:real`; `u2:real`; `u3:real`] THEN
    UNDISCH_TAC `u1 + u2 + u3 + u4 = &1` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; REAL_ADD_RID] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[];
    DISJ2_TAC THEN EXISTS_TAC `u4:real` THEN CONJ_TAC THENL
     [UNDISCH_TAC `~(u4 = &0)` THEN UNDISCH_TAC `&0 <= u4` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`A:real^3`; `B:real^3`; `D:real^3`; `A:real^3`; `B:real^3`;
                   `D:real^3`; `E:real^3`; `u1:real`; `u2:real`; `u3:real`;
                   `u4:real`] MOI_FM3_DET_AFFINE) THEN
    ASM_REWRITE_TAC[MOI_FM3_DET_TRIVIAL] THEN REAL_ARITH_TAC]);;
let MOI_LGB2_TET_OPP = prove
 (`!a b d e e':real^3.
        ~(e = e') /\
        aff_dim(convex hull {a,b,d,e}) = &3 /\
        aff_dim(convex hull {a,b,d,e'}) = &3 /\
        convex hull {a,b,d,e} INTER convex hull {a,b,d,e'} = convex hull {a,b,d}
        ==> det(vector[b - a; d - a; e - a]) *
            det(vector[b - a; d - a; e' - a]) < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^3`; `b:real^3`; `d:real^3`; `e:real^3`]
    MOI_FM3_TET_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^3`; `b:real^3`; `d:real^3`; `e':real^3`]
    MOI_FM3_TET_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^3`; `b:real^3`; `d:real^3`; `e':real^3`; `e:real^3`]
    MOI_FM3_AFFINE_COORDS_4) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real` (X_CHOOSE_THEN `u2:real`
    (X_CHOOSE_THEN `u3:real` (X_CHOOSE_THEN `u4:real` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN
   `det(vector[b - a; d - a; e - a]:real^3^3) =
    u4 * det(vector[b - a; d - a; e' - a])`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`a:real^3`; `b:real^3`; `d:real^3`; `a:real^3`; `b:real^3`;
                   `d:real^3`; `e':real^3`; `u1:real`; `u2:real`; `u3:real`;
                   `u4:real`] MOI_FM3_DET_AFFINE) THEN
    ASM_REWRITE_TAC[MOI_FM3_DET_TRIVIAL] THEN
    UNDISCH_TAC `e:real^3 = u1 % a + u2 % b + u3 % d + u4 % e'` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < u4` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `&0 < det(vector[b - a; d - a; e' - a]:real^3^3) *
           det(vector[b - a; d - a; e' - a])`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_LT_SQUARE]; ALL_TAC] THEN
    SUBGOAL_THEN `~(u4 = &0)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `~(det(vector[b - a; d - a; e - a]:real^3^3) = &0)` THEN
      ASM_REWRITE_TAC[REAL_MUL_LZERO];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= u4` MP_TAC THENL
     [MP_TAC(ISPECL
       [`&0`; `u4:real`;
        `det(vector[b - a; d - a; e' - a]:real^3^3) *
         det(vector[b - a; d - a; e' - a])`]
        REAL_LE_LMUL_EQ) THEN
      ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC
       `&0 <= det(vector[b - a; d - a; e - a]:real^3^3) *
              det(vector[b - a; d - a; e' - a])` THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `~(u4 = &0)` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u1:real`; `u2:real`; `u3:real`] MOI_FM3_SMALL_STEP) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `((&1 - t) / &3) % a + ((&1 - t) / &3) % b + ((&1 - t) / &3) % d + t % e
    IN convex hull {a,b,d,e:real^3}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FM3_IN_CONVEX_HULL_4 THEN
    UNDISCH_TAC `&0 < t` THEN UNDISCH_TAC `t < &1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((&1 - t) / &3) % a + ((&1 - t) / &3) % b + ((&1 - t) / &3) % d + t % e
    IN convex hull {a,b,d,e':real^3}`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `((&1 - t) / &3) % a + ((&1 - t) / &3) % b + ((&1 - t) / &3) % d +
      t % e =
      ((&1 - t) / &3 + t * u1) % a + ((&1 - t) / &3 + t * u2) % b +
      ((&1 - t) / &3 + t * u3) % d + (t * u4) % e':real^3`
    SUBST1_TAC THENL
     [UNDISCH_TAC `e:real^3 = u1 % a + u2 % b + u3 % d + u4 % e'` THEN
      DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_FM3_IN_CONVEX_HULL_4 THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `t * u1 + t * u2 + t * u3 + t * u4 = t` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN ASM_REWRITE_TAC[REAL_MUL_RID];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN
      UNDISCH_TAC `&0 < t` THEN UNDISCH_TAC `&0 < u4` THEN REAL_ARITH_TAC;
      UNDISCH_TAC `t * u1 + t * u2 + t * u3 + t * u4 = t` THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(((&1 - t) / &3) % a + ((&1 - t) / &3) % b + ((&1 - t) / &3) % d +
      t % e IN convex hull {a,b,d:real^3})`
  ASSUME_TAC THENL
   [REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real` (X_CHOOSE_THEN `q:real`
      (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `t * det(vector[b - a; d - a; e - a]:real^3^3) = &0` MP_TAC THENL
     [MP_TAC(ISPECL [`a:real^3`; `b:real^3`; `d:real^3`; `a:real^3`; `b:real^3`;
                     `d:real^3`; `e:real^3`; `(&1 - t) / &3`; `(&1 - t) / &3`;
                     `(&1 - t) / &3`; `t:real`] MOI_FM3_DET_AFFINE) THEN
      ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[MOI_FM3_DET_TRIVIAL; REAL_MUL_RZERO; REAL_ADD_LID] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC
       `((&1 - t) / &3) % a + ((&1 - t) / &3) % b + ((&1 - t) / &3) % d +
        t % e = p % a + q % b + r % d:real^3` THEN
      DISCH_THEN SUBST1_TAC THEN
      MP_TAC(ISPECL [`a:real^3`; `b:real^3`; `d:real^3`; `a:real^3`;
                     `b:real^3`; `d:real^3`; `p:real`; `q:real`; `r:real`]
        MOI_FM3_DET_AFFINE_3) THEN
      ASM_REWRITE_TAC[MOI_FM3_DET_TRIVIAL] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o REWRITE_RULE[REAL_ENTIRE]) THEN
    UNDISCH_TAC `~(det(vector[b - a; d - a; e - a]:real^3^3) = &0)` THEN
    UNDISCH_TAC `&0 < t` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC
   `convex hull {a,b,d,e} INTER convex hull {a,b,d,e'} =
    convex hull {a:real^3,b,d}` THEN
  REWRITE_TAC[EXTENSION; IN_INTER] THEN
  DISCH_THEN(MP_TAC o SPEC
   `((&1 - t) / &3) % a + ((&1 - t) / &3) % b + ((&1 - t) / &3) % d +
    t % e:real^3`) THEN
  ASM_REWRITE_TAC[]);;

let MOI_LGB2_NEAR_EDGE_PT = prove
 (`!(p:real^N) q w mu s t e.
     &0 < mu /\ mu < &1 /\ &0 <= t /\ abs s <= e /\ abs t <= e /\
     &2 * e <= mu /\ &2 * e <= &1 - mu
     ==> ((&1 - mu) % p + mu % q) + s % (q - p) + t % (w - p) IN
         convex hull {p,q,w}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC [`&1 - mu - s - t`; `mu + s:real`; `t:real`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]; REAL_ARITH_TAC;
    VECTOR_ARITH_TAC]);;

let MOI_LGB2_DIST_STEP = prove
 (`!(x0:real^N) a b u v.
     dist(x0 + a % u + b % v,x0) <= abs a * norm u + abs b * norm v`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[dist; VECTOR_ARITH `(x0 + y) - x0:real^N = y`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(a % (u:real^N)) + norm(b % (v:real^N))` THEN
  REWRITE_TAC[NORM_TRIANGLE; NORM_MUL; REAL_LE_REFL]);;

let MOI_LGB2_AFF_STEP = prove
 (`!(f:real^M->real^N) l b (S:real^M->bool) p q w x0 s t.
     linear l /\ (!x. x IN S ==> f x = l x + b) /\
     p IN S /\ q IN S /\ w IN S /\ x0 IN S /\
     x0 + s % (q - p) + t % (w - p) IN S
     ==> f(x0 + s % (q - p) + t % (w - p)) =
         f x0 + s % (f q - f p) + t % (f w - f p)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL; LINEAR_SUB] THEN
  VECTOR_ARITH_TAC);;

let MOI_LGB2_SMALL_POS = prove
 (`!K m. &0 < m /\ &0 < K ==> ?lam. &0 < lam /\ lam * K <= m`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `m / K` THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_DIV_RMUL; REAL_LT_IMP_NZ; REAL_LE_REFL]);;

let MOI_LGB2_FOLD = prove
 (`!(f:real^2->real^3) p q w w' mu dd.
     ~affine_dependent {p,q,w} /\ ~affine_dependent {p,q,w'} /\
     ~(p = q) /\ ~(p = w) /\ ~(q = w) /\ ~(p = w') /\ ~(q = w') /\
     convex hull {p,q,w} INTER convex hull {p,q,w'} = convex hull {p,q} /\
     (?l b. linear l /\ !x. x IN convex hull {p,q,w} ==> f x = l x + b) /\
     (?l b. linear l /\ !x. x IN convex hull {p,q,w'} ==> f x = l x + b) /\
     &0 < mu /\ mu < &1 /\ &0 < dd /\
     (!x x'. x IN convex hull {p,q,w} UNION convex hull {p,q,w'} /\
             x' IN convex hull {p,q,w} UNION convex hull {p,q,w'} /\
             dist(x,(&1 - mu) % p + mu % q) < dd /\
             dist(x',(&1 - mu) % p + mu % q) < dd /\
             f x = f x' ==> x = x')
     ==> !s t s' t'. &0 < s /\ &0 < s'
                     ==> ~(t % (f q - f p) + s % (f w - f p) =
                           t' % (f q - f p) + s' % (f w' - f p))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `l1:real^2->real^3` (X_CHOOSE_THEN `b1:real^3`
        STRIP_ASSUME_TAC))
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `l2:real^2->real^3` (X_CHOOSE_THEN `b2:real^3`
        STRIP_ASSUME_TAC))
    (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "inj")))))))))))))) THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `t:real`; `s':real`; `t':real`] THEN
  STRIP_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `x0:real^2 = (&1 - mu) % p + mu % q` THEN
  ABBREV_TAC `m = min (min (mu / &2) ((&1 - mu) / &2)) (dd / &2)` THEN
  SUBGOAL_THEN `&0 < m /\ &2 * m <= mu /\ &2 * m <= &1 - mu /\ m < dd`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN UNDISCH_TAC `&0 < mu` THEN UNDISCH_TAC `mu < &1` THEN
    UNDISCH_TAC `&0 < dd` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `P1 = abs t * norm(q - p:real^2) + abs s * norm(w - p:real^2)` THEN
  ABBREV_TAC `P2 = abs t' * norm(q - p:real^2) + abs s' * norm(w' - p:real^2)` THEN
  SUBGOAL_THEN `&0 <= P1 /\ &0 <= P2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["P1"; "P2"] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE];
    ALL_TAC] THEN
  ABBREV_TAC `KK = abs s + abs t + abs s' + abs t' + P1 + P2 + &1` THEN
  MP_TAC(ISPECL [`KK:real`; `m:real`] MOI_LGB2_SMALL_POS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "KK" THEN
    MP_TAC(SPEC `s:real` REAL_ABS_POS) THEN MP_TAC(SPEC `t:real` REAL_ABS_POS) THEN
    MP_TAC(SPEC `s':real` REAL_ABS_POS) THEN MP_TAC(SPEC `t':real` REAL_ABS_POS) THEN
    UNDISCH_TAC `&0 <= P1` THEN UNDISCH_TAC `&0 <= P2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!X. &0 <= X /\ X <= KK ==> lam * X <= m`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lam * KK` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < lam` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(lam * s) <= m /\ abs(lam * t) <= m /\ abs(lam * s') <= m /\
    abs(lam * t') <= m /\ lam * P1 <= m /\ lam * P2 <= m`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `abs lam = lam` (fun th -> REWRITE_TAC[REAL_ABS_MUL; th]) THENL
     [UNDISCH_TAC `&0 < lam` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[REAL_ABS_POS] THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "KK" THEN
    MP_TAC(SPEC `s:real` REAL_ABS_POS) THEN MP_TAC(SPEC `t:real` REAL_ABS_POS) THEN
    MP_TAC(SPEC `s':real` REAL_ABS_POS) THEN MP_TAC(SPEC `t':real` REAL_ABS_POS) THEN
    UNDISCH_TAC `&0 <= P1` THEN UNDISCH_TAC `&0 <= P2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `X:real^2 = x0 + (lam * t) % (q - p) + (lam * s) % (w - p)` THEN
  ABBREV_TAC `X':real^2 = x0 + (lam * t') % (q - p) + (lam * s') % (w' - p)` THEN
  SUBGOAL_THEN `(X:real^2) IN convex hull {p,q,w} /\ X' IN convex hull {p,q,w'}`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["X"; "X'"; "x0"] THEN CONJ_TAC THEN
    MATCH_MP_TAC MOI_LGB2_NEAR_EDGE_PT THEN EXISTS_TAC `m:real` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    UNDISCH_TAC `&0 < lam` THEN UNDISCH_TAC `&0 < s` THEN
    UNDISCH_TAC `&0 < s'` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `dist(X:real^2,x0) < dd /\ dist(X':real^2,x0) < dd`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["X"; "X'"] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THENL
     [EXISTS_TAC `abs(lam * t) * norm(q - p:real^2) + abs(lam * s) * norm(w - p:real^2)`;
      EXISTS_TAC `abs(lam * t') * norm(q - p:real^2) +
                  abs(lam * s') * norm(w' - p:real^2)`] THEN
    REWRITE_TAC[MOI_LGB2_DIST_STEP] THEN
    (SUBGOAL_THEN `abs lam = lam` (fun th -> REWRITE_TAC[REAL_ABS_MUL; th]) THENL
      [UNDISCH_TAC `&0 < lam` THEN REAL_ARITH_TAC; ALL_TAC]) THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC; GSYM REAL_ADD_LDISTRIB] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^2) IN convex hull {p,q,w} /\ q IN convex hull {p,q,w} /\
                w IN convex hull {p,q,w} /\ p IN convex hull {p,q,w'} /\
                q IN convex hull {p,q,w'} /\ w' IN convex hull {p,q,w'}`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x0:real^2) IN convex hull {p,q,w} /\ x0 IN convex hull {p,q,w'}`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "x0" THEN REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN
    CONJ_TAC THEN MAP_EVERY EXISTS_TAC [`&1 - mu`; `mu:real`; `&0`] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; REAL_ADD_RID] THEN
    UNDISCH_TAC `&0 < mu` THEN UNDISCH_TAC `mu < &1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(f:real^2->real^3) X = f x0 + lam % (t % (f q - f p) + s % (f w - f p)) /\
    f X' = f x0 + lam % (t' % (f q - f p) + s' % (f w' - f p))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MAP_EVERY EXPAND_TAC ["X"; "X'"] THEN
    REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
    MATCH_MP_TAC MOI_LGB2_AFF_STEP THENL
     [MAP_EVERY EXISTS_TAC [`l1:real^2->real^3`; `b1:real^3`;
                            `convex hull {p:real^2,q,w}`];
      MAP_EVERY EXISTS_TAC [`l2:real^2->real^3`; `b2:real^3`;
                            `convex hull {p:real^2,q,w'}`]] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `X:real^2 = X'` ASSUME_TAC THENL
   [REMOVE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_UNION];
    ALL_TAC] THEN
  SUBGOAL_THEN `(X:real^2) IN convex hull {p,q}` MP_TAC THENL
   [UNDISCH_TAC `convex hull {p,q,w} INTER convex hull {p,q,w'} =
                 convex hull {p:real^2,q}` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_INTER] THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `X:real^2 = X'` THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; IN_SEGMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `nu:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`p:real^2`; `q:real^2`; `w:real^2`; `mu + lam * t - nu:real`;
                 `lam * s:real`] MOI_SCF_TRI_COORDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(X:real^2) = (&1 - nu) % p + nu % q` THEN
    EXPAND_TAC "X" THEN EXPAND_TAC "x0" THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM] THEN
  UNDISCH_TAC `&0 < lam` THEN UNDISCH_TAC `&0 < s` THEN REAL_ARITH_TAC);;

let MOI_LGB2_HYPERPLANE_1 = prove
 (`{z:real^3 | z$1 = &0} = {z | basis 1 dot z = &0} /\
   {z:real^3 | z$2 = &0} = {z | basis 2 dot z = &0}`,
  SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH]);;

let MOI_LGB2_PLANE_FACTS = prove
 (`!k. 1 <= k /\ k <= 3
       ==> affine {z:real^3 | z$k = &0} /\ aff_dim {z:real^3 | z$k = &0} = &2`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `{z:real^3 | z$k = &0} = {z | basis k dot z = &0}` SUBST1_TAC THENL
   [ASM_SIMP_TAC[DOT_BASIS; DIMINDEX_3]; ALL_TAC] THEN
  REWRITE_TAC[AFFINE_HYPERPLANE] THEN
  MP_TAC(ISPECL [`basis k:real^3`; `&0`] AFF_DIM_HYPERPLANE) THEN
  ASM_SIMP_TAC[BASIS_NONZERO; DIMINDEX_3] THEN DISCH_THEN SUBST1_TAC THEN
  INT_ARITH_TAC);;

let MOI_LGB2_BSURJ = prove
 (`!(f:real^3->real^3) z0 d a e k.
     f continuous_on (:real^3) /\ (!z z'. f z = f z' ==> z = z') /\
     f z0 = vec 0 /\ ~(d cross a = vec 0) /\ 1 <= k /\ k <= 3 /\
     (!s t. (f(z0 + s % d + t % a))$k = &0) /\
     (!z. (f z)$3 = (z - z0)$3) /\ d$3 = &0 /\ &0 < a$3 /\ &0 < e
     ==> ?eta. &0 < eta /\
               !z. &0 <= z$3 /\ z$k = &0 /\ norm z < eta
                   ==> ?s t. &0 <= t /\ abs s < e /\ abs t < e /\
                             z = f(z0 + s % d + t % a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\v:real^2. (f:real^3->real^3)(z0 + v$1 % d + v$2 % a)`;
                 `(:real^2)`; `{z:real^3 | z$k = &0}`; `ball(vec 0:real^2,e)`]
    INVARIANCE_OF_DOMAIN_AFFINE_SETS) THEN
  MP_TAC(SPEC `k:num` MOI_LGB2_PLANE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[AFFINE_UNIV; AFF_DIM_UNIV; DIMINDEX_2] THEN
    REPEAT CONJ_TAC THENL
     [INT_ARITH_TAC;
      SUBGOAL_THEN `(\v:real^2. (f:real^3->real^3)(z0 + v$1 % d + v$2 % a)) =
                    f o (\v. z0 + v$1 % d + v$2 % a)` SUBST1_TAC THENL
       [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
        MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
        MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN REWRITE_TAC[o_DEF] THEN
        SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT; DIMINDEX_2; ARITH];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV]];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`v:real^2`; `v':real^2`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(z0 + (v:real^2)$1 % d + v$2 % a):real^3 =
                    z0 + (v':real^2)$1 % d + v'$2 % a`
      MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o MATCH_MP (VECTOR_ARITH
        `z0 + x1 % d + x2 % a = z0 + y1 % d + y2 % a:real^3
         ==> (x1 - y1) % d + (x2 - y2) % a = vec 0`)) THEN
      DISCH_TAC THEN
      MP_TAC(ISPECL [`d:real^3`; `a:real^3`; `(v:real^2)$1 - (v':real^2)$1`;
                     `(v:real^2)$2 - (v':real^2)$2`] MOI_LGB2_CROSS_INDEP2) THEN
      ASM_REWRITE_TAC[REAL_SUB_0] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2];
      REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN; OPEN_BALL]];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `vec 0:real^3` o CONJUNCT2) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 0:real^2` THEN
    REWRITE_TAC[CENTRE_IN_BALL; VEC_COMPONENT; VECTOR_MUL_LZERO;
                VECTOR_ADD_RID] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `eta:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(z:real^3) IN IMAGE (\v:real^2. (f:real^3->real^3)(z0 + v$1 % d + v$2 % a))
                        (ball(vec 0,e))`
  MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    ASM_REWRITE_TAC[IN_INTER; IN_BALL_0; IN_ELIM_THM];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; IN_BALL_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^2` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`(v:real^2)$1`; `(v:real^2)$2`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `&0 <= (z:real^3)$3` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT;
                VECTOR_MUL_COMPONENT] THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID;
                    REAL_ARITH `(z + y) - z:real = y`] THEN
    DISCH_TAC THEN
    MP_TAC(SPECL [`&0`; `(v:real^2)$2`; `(a:real^3)$3`] REAL_LE_RMUL_EQ) THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO];
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `norm(v:real^2)` THEN
    ASM_REWRITE_TAC[COMPONENT_LE_NORM];
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `norm(v:real^2)` THEN
    ASM_REWRITE_TAC[COMPONENT_LE_NORM]]);;

(* ========================================================================= *)
(* The finishing step.  A chart (u,h,h') of the atlas at y, a PL             *)
(* homeomorphism f of real^3 with f(h y) = 0 and two sheets N1, N2 at the   *)
(* preimages x1, x2 of y mapped by f o h into the planes z1 = 0 and z2 = 0  *)
(* (open in real^2 at an interior point; with the local surjectivity and    *)
(* f preserving the third coordinate at a boundary point) give the crossing *)
(* chart of moi_lt_crossing2_at, through MOI_LGB2_TRANSFER.                 *)
(* ========================================================================= *)

let MOI_LGB2_F_FACTS = prove
 (`!(f:real^3->real^3) f'.
     pl_homeomorphism ((:real^3),(:real^3)) (f,f')
     ==> f continuous_on (:real^3) /\ (!z z'. f z = f z' ==> z = z') /\
         (!z. f'(f z) = z) /\ (!z. f(f' z) = z) /\
         (!s. open s ==> open(IMAGE f s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_homeomorphism; homeomorphism; IN_UNIV] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!z z'. (f:real^3->real^3) z = f z' ==> z = z'` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]);;

let MOI_LGB2_FIN_CHART = prove
 (`!(u:real^N->bool) (h:real^N->real^3) h' (f:real^3->real^3) f'.
     pl_homeomorphism (u,IMAGE h u) (h,h') /\
     pl_homeomorphism ((:real^3),(:real^3)) (f,f')
     ==> homeomorphism (u,IMAGE (f o h) u) (f o h,h' o f') /\
         pl_map_on u (f o h)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_homeomorphism] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `IMAGE (h:real^N->real^3) u` THEN
    ASM_REWRITE_TAC[IMAGE_o] THEN
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`(:real^3)`; `(:real^3)`] THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `(:real^3)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV]]);;

let MOI_LGB2_CB_CLOSED = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c
     ==> closed(complex_boundary c)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[complex_boundary] THEN
  MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC MOI_FM3_LF_COMPACT THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_MESON_TAC[combinatorial_manifold_with_boundary]]);;

let MOI_LGB2_CB_IFF = prove
 (`!(c:(real^N->bool)->bool) u (h:real^N->real^3) h'.
     homeomorphism (u,IMAGE h u) (h,h') /\
     IMAGE h (u INTER complex_boundary c) = IMAGE h u INTER {z:real^3 | z$3 = &0}
     ==> !p. p IN u ==> (p IN complex_boundary c <=> (h p)$3 = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
  EQ_TAC THEN DISCH_TAC THENL
   [SUBGOAL_THEN `(h:real^N->real^3) p IN IMAGE h (u INTER complex_boundary c)`
    MP_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN SIMP_TAC[];
    SUBGOAL_THEN `(h:real^N->real^3) p IN IMAGE h (u INTER complex_boundary c)`
    MP_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `p:real^N = q` (fun th -> ASM_REWRITE_TAC[th]) THEN
    UNDISCH_TAC `homeomorphism (u,IMAGE h u) ((h:real^N->real^3),h')` THEN
    REWRITE_TAC[homeomorphism] THEN ASM_MESON_TAC[]]);;

let MOI_LGB2_FIN_NBHD_INT = prove
 (`!(c:(real^N->bool)->bool) u (h:real^N->real^3) h' y.
     homeomorphism (u,IMAGE h u) (h,h') /\ y IN u /\ ~(y IN complex_boundary c) /\
     ((u INTER complex_boundary c = {} /\ IMAGE h u = ball(vec 0,&1)) \/
      (IMAGE h u = ball(vec 0,&1) INTER {z:real^3 | &0 <= z$3} /\
       IMAGE h (u INTER complex_boundary c) = IMAGE h u INTER {z:real^3 | z$3 = &0}))
     ==> ?e. &0 < e /\ ball(h y,e) SUBSET IMAGE h u`,
  REPEAT GEN_TAC THEN STRIP_TAC THENL
   [MP_TAC(ISPEC `ball(vec 0:real^3,&1)` OPEN_CONTAINS_BALL) THEN
    REWRITE_TAC[OPEN_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `(h:real^N->real^3) y`) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `IMAGE (h:real^N->real^3) u = ball(vec 0,&1)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^N->real^3) y IN IMAGE h u` ASSUME_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `((h:real^N->real^3) y)$3 > &0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`] MOI_LGB2_CB_IFF) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(h:real^N->real^3) y IN IMAGE h u` THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `ball(vec 0:real^3,&1) INTER {z:real^3 | z$3 > &0}`
    OPEN_CONTAINS_BALL) THEN
  SIMP_TAC[OPEN_INTER; OPEN_BALL; OPEN_HALFSPACE_COMPONENT_GT] THEN
  DISCH_THEN(MP_TAC o SPEC `(h:real^N->real^3) y`) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `(h:real^N->real^3) y IN IMAGE h u` THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `ball((h:real^N->real^3) y,e) SUBSET
               ball(vec 0,&1) INTER {z:real^3 | z$3 > &0}` THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN
  MESON_TAC[REAL_ARITH `x > &0 ==> &0 <= x`]);;

let MOI_LGB2_FIN_R0_INT = prove
 (`!(u:real^N->bool) (h:real^N->real^3) (f:real^3->real^3) f' y e.
     pl_homeomorphism ((:real^3),(:real^3)) (f,f') /\ f (h y) = vec 0 /\
     &0 < e /\ ball(h y,e) SUBSET IMAGE h u
     ==> ?r0. &0 < r0 /\
              IMAGE (f o h) u INTER ball(vec 0,r0) = (:real^3) INTER ball(vec 0,r0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB2_F_FACTS) THEN
  MP_TAC(ISPEC `IMAGE (f:real^3->real^3) (ball((h:real^N->real^3) y,e))`
    OPEN_CONTAINS_BALL) THEN
  ASM_SIMP_TAC[OPEN_BALL] THEN DISCH_THEN(MP_TAC o SPEC `vec 0:real^3`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(h:real^N->real^3) y` THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r0:real` THEN ASM_REWRITE_TAC[INTER_UNIV] THEN
  REWRITE_TAC[IMAGE_o] THEN
  MATCH_MP_TAC(SET_RULE `!a b:real^3->bool. a SUBSET b ==> b INTER a = a`) THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `IMAGE (f:real^3->real^3) (ball((h:real^N->real^3) y,e))` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]);;

let MOI_LGB2_FIN_R0_BD = prove
 (`!(u:real^N->bool) (h:real^N->real^3) (f:real^3->real^3) f' y.
     pl_homeomorphism ((:real^3),(:real^3)) (f,f') /\ f (h y) = vec 0 /\
     y IN u /\ IMAGE h u = ball(vec 0,&1) INTER {z:real^3 | &0 <= z$3} /\
     (!z. (f z)$3 = z$3)
     ==> ?r0. &0 < r0 /\
              IMAGE (f o h) u INTER ball(vec 0,r0) =
              {z:real^3 | &0 <= z$3} INTER ball(vec 0,r0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB2_F_FACTS) THEN
  SUBGOAL_THEN `(h:real^N->real^3) y IN ball(vec 0,&1)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(h:real^N->real^3) y IN IMAGE h u` MP_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_INTER] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (f:real^3->real^3) (ball(vec 0,&1))` OPEN_CONTAINS_BALL) THEN
  ASM_SIMP_TAC[OPEN_BALL] THEN DISCH_THEN(MP_TAC o SPEC `vec 0:real^3`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(h:real^N->real^3) y` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r0:real` THEN ASM_REWRITE_TAC[IMAGE_o] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN
  EQ_TAC THENL
   [REWRITE_TAC[IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC)
      ASSUME_TAC) THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(z:real^3) IN IMAGE (f:real^3->real^3) (ball(vec 0,&1))`
    MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `w:real^3` THEN ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    UNDISCH_TAC `&0 <= (z:real^3)$3` THEN ASM_REWRITE_TAC[]]);;

let MOI_LGB2_FIN_ETA_INT = prove
 (`!(g:real^2->real^N) (u:real^N->bool) (h:real^N->real^3) h'
    (f:real^3->real^3) f' N x0 k.
     g continuous_on std_triangle /\ N SUBSET std_triangle /\ open N /\ x0 IN N /\
     IMAGE g N SUBSET u /\ (!x x'. x IN N /\ x' IN N /\ g x = g x' ==> x = x') /\
     homeomorphism (u,IMAGE h u) (h,h') /\
     pl_homeomorphism ((:real^3),(:real^3)) (f,f') /\
     (!x. x IN N ==> (f(h(g x)))$k = &0) /\ f(h(g x0)) = vec 0 /\
     1 <= k /\ k <= 3
     ==> ?eta. &0 < eta /\
               !z. z IN (:real^3) /\ z$k = &0 /\ norm z < eta
                   ==> z IN IMAGE ((f o h) o g) N`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB2_F_FACTS) THEN
  MP_TAC(SPEC `k:num` MOI_LGB2_PLANE_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`((f:real^3->real^3) o (h:real^N->real^3)) o (g:real^2->real^N)`;
                 `(:real^2)`;
                 `{z:real^3 | z$k = &0}`; `N:real^2->bool`]
    INVARIANCE_OF_DOMAIN_AFFINE_SETS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[AFFINE_UNIV; AFF_DIM_UNIV; DIMINDEX_2] THEN
    REPEAT CONJ_TAC THENL
     [INT_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `u:real^N->bool` THEN
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[homeomorphism];
        ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; o_THM] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[o_THM] THEN MAP_EVERY X_GEN_TAC [`x:real^2`; `x':real^2`] THEN
      STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(h:real^N->real^3)(g(x:real^2)) = h(g x')` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `homeomorphism (u,IMAGE h u) ((h:real^N->real^3),h')` THEN
      REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(g:real^2->real^N) x IN u /\ g x' IN u` MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_MESON_TAC[];
      REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `vec 0:real^3` o CONJUNCT2) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_IMAGE; o_THM] THEN EXISTS_TAC `x0:real^2` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `eta:real` THEN ASM_REWRITE_TAC[IN_UNIV] THEN
  X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
  ASM_REWRITE_TAC[IN_INTER; IN_BALL_0; IN_ELIM_THM]);;

let MOI_LGB2_FIN_BD_CLAUSE = prove
 (`!(c:(real^N->bool)->bool) u u' (h:real^N->real^3) h' (f:real^3->real^3) rho.
     homeomorphism (u,IMAGE h u) (h,h') /\ u' SUBSET u /\
     IMAGE h (u INTER complex_boundary c) = IMAGE h u INTER {z:real^3 | z$3 = &0} /\
     (!z. (f z)$3 = z$3) /\ &0 < rho
     ==> IMAGE (\p. inv rho % (f o h) p) (u' INTER complex_boundary c) =
         IMAGE (\p. inv rho % (f o h) p) u' INTER {z:real^3 | z$3 = &0}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`] MOI_LGB2_CB_IFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!p:real^N. (inv rho % ((f:real^3->real^3) o h) p)$3 = &0 <=>
                           ((h:real^N->real^3) p)$3 = &0`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_COMPONENT; o_THM; REAL_ENTIRE; REAL_INV_EQ_0] THEN
    UNDISCH_TAC `&0 < rho` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
  X_GEN_TAC `z:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `p:real^N` STRIP_ASSUME_TAC) THEN
    CONJ_TAC THENL [EXISTS_TAC `p:real^N` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `p:real^N` STRIP_ASSUME_TAC)
      ASSUME_TAC) THEN
    EXISTS_TAC `p:real^N` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z:real^3)$3 = &0` THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(p:real^N) IN u` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[]]);;

let MOI_LGB2_FINISH_INT = prove
 (`!(c:(real^N->bool)->bool) (g:real^2->real^N) y x1 x2 u (h:real^N->real^3) h'
    (f:real^3->real^3) f' N1 N2.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     moi_lt_singular_disk c g /\
     x1 IN std_triangle /\ x2 IN std_triangle /\ ~(x1 = x2) /\ g x1 = y /\ g x2 = y /\
     open_in (subtopology euclidean (UNIONS c)) u /\ y IN u /\
     pl_homeomorphism (u,IMAGE h u) (h,h') /\
     ((u INTER complex_boundary c = {} /\ IMAGE h u = ball(vec 0,&1)) \/
      (IMAGE h u = ball(vec 0,&1) INTER {z:real^3 | &0 <= z$3} /\
       IMAGE h (u INTER complex_boundary c) =
       IMAGE h u INTER {z:real^3 | z$3 = &0})) /\
     pl_homeomorphism ((:real^3),(:real^3)) (f,f') /\ f (h y) = vec 0 /\
     open_in (subtopology euclidean std_triangle) N1 /\
     open_in (subtopology euclidean std_triangle) N2 /\
     x1 IN N1 /\ x2 IN N2 /\ DISJOINT N1 N2 /\
     IMAGE g N1 SUBSET u /\ IMAGE g N2 SUBSET u /\
     (!x x'. x IN N1 /\ x' IN N1 /\ g x = g x' ==> x = x') /\
     (!x x'. x IN N2 /\ x' IN N2 /\ g x = g x' ==> x = x') /\
     (!x. x IN N1 ==> (f(h(g x)))$1 = &0) /\
     (!x. x IN N2 ==> (f(h(g x)))$2 = &0) /\
     ~(y IN complex_boundary c) /\ open N1 /\ open N2
     ==> moi_lt_crossing2_at c g y`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  MP_TAC(ISPECL [`u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                 `f:real^3->real^3`; `f':real^3->real^3`] MOI_LGB2_FIN_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `homeomorphism (u,IMAGE h u) ((h:real^N->real^3),h')`
  ASSUME_TAC THENL [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `u:real^N->bool`; `h:real^N->real^3`;
                 `h':real^3->real^N`; `y:real^N`] MOI_LGB2_FIN_NBHD_INT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`u:real^N->bool`; `h:real^N->real^3`; `f:real^3->real^3`;
                 `f':real^3->real^3`; `y:real^N`; `e:real`] MOI_LGB2_FIN_R0_INT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(g:real^2->real^N) continuous_on std_triangle` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_lt_singular_disk; PL_MAP_ON_IMP_CONTINUOUS_ON]; ALL_TAC] THEN
  SUBGOAL_THEN `(N1:real^2->bool) SUBSET std_triangle /\ N2 SUBSET std_triangle`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^2->real^N`; `u:real^N->bool`; `h:real^N->real^3`;
                 `h':real^3->real^N`; `f:real^3->real^3`; `f':real^3->real^3`;
                 `N1:real^2->bool`; `x1:real^2`; `1`] MOI_LGB2_FIN_ETA_INT) THEN
  ASM_REWRITE_TAC[ARITH] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g:real^2->real^N`; `u:real^N->bool`; `h:real^N->real^3`;
                 `h':real^3->real^N`; `f:real^3->real^3`; `f':real^3->real^3`;
                 `N2:real^2->bool`; `x2:real^2`; `2`] MOI_LGB2_FIN_ETA_INT) THEN
  ASM_REWRITE_TAC[ARITH] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN UNIONS c` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:real^2->real^N`; `y:real^N`;
                 `x1:real^2`; `x2:real^2`; `u:real^N->bool`;
                 `(f:real^3->real^3) o (h:real^N->real^3)`;
                 `(h':real^3->real^N) o (f':real^3->real^3)`;
                 `N1:real^2->bool`; `N2:real^2->bool`; `(:real^3)`;
                 `UNIONS c DIFF complex_boundary (c:(real^N->bool)->bool)`]
    MOI_LGB2_TRANSFER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[o_THM] THEN REWRITE_TAC[IN_UNIV] THEN
    ASM_SIMP_TAC[OPEN_IN_DIFF_CLOSED; MOI_LGB2_CB_CLOSED; IN_DIFF];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u':real^N->bool` (X_CHOOSE_THEN `rho:real`
    (X_CHOOSE_THEN `n1:real^2->bool` (X_CHOOSE_THEN `n2:real^2->bool`
      STRIP_ASSUME_TAC)))) THEN
  REWRITE_TAC[moi_lt_crossing2_at] THEN
  MAP_EVERY EXISTS_TAC
   [`u':real^N->bool`;
    `\p. inv rho % ((f:real^3->real^3) o (h:real^N->real^3)) p`;
    `\z. ((h':real^3->real^N) o (f':real^3->real^3)) (rho % z)`;
    `n1:real^2->bool`; `n2:real^2->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[o_THM] THEN ASM_REWRITE_TAC[VECTOR_MUL_RZERO]; ALL_TAC] THEN
  TRY DISJ1_TAC THEN ASM_REWRITE_TAC[INTER_UNIV] THEN ASM SET_TAC[]);;

let MOI_LGB2_FINISH_BD = prove
 (`!(c:(real^N->bool)->bool) (g:real^2->real^N) y x1 x2 u (h:real^N->real^3) h'
    (f:real^3->real^3) f' N1 N2.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     moi_lt_singular_disk c g /\
     x1 IN std_triangle /\ x2 IN std_triangle /\ ~(x1 = x2) /\ g x1 = y /\ g x2 = y /\
     open_in (subtopology euclidean (UNIONS c)) u /\ y IN u /\
     pl_homeomorphism (u,IMAGE h u) (h,h') /\
     ((u INTER complex_boundary c = {} /\ IMAGE h u = ball(vec 0,&1)) \/
      (IMAGE h u = ball(vec 0,&1) INTER {z:real^3 | &0 <= z$3} /\
       IMAGE h (u INTER complex_boundary c) =
       IMAGE h u INTER {z:real^3 | z$3 = &0})) /\
     pl_homeomorphism ((:real^3),(:real^3)) (f,f') /\ f (h y) = vec 0 /\
     open_in (subtopology euclidean std_triangle) N1 /\
     open_in (subtopology euclidean std_triangle) N2 /\
     x1 IN N1 /\ x2 IN N2 /\ DISJOINT N1 N2 /\
     IMAGE g N1 SUBSET u /\ IMAGE g N2 SUBSET u /\
     (!x x'. x IN N1 /\ x' IN N1 /\ g x = g x' ==> x = x') /\
     (!x x'. x IN N2 /\ x' IN N2 /\ g x = g x' ==> x = x') /\
     (!x. x IN N1 ==> (f(h(g x)))$1 = &0) /\
     (!x. x IN N2 ==> (f(h(g x)))$2 = &0) /\
     y IN complex_boundary c /\ (!z. (f z)$3 = z$3) /\
     (?eta1. &0 < eta1 /\
             !z. &0 <= z$3 /\ z$1 = &0 /\ norm z < eta1
                 ==> z IN IMAGE ((f o h) o g) N1) /\
     (?eta2. &0 < eta2 /\
             !z. &0 <= z$3 /\ z$2 = &0 /\ norm z < eta2
                 ==> z IN IMAGE ((f o h) o g) N2)
     ==> moi_lt_crossing2_at c g y`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  MP_TAC(ISPECL [`u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                 `f:real^3->real^3`; `f':real^3->real^3`] MOI_LGB2_FIN_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `homeomorphism (u,IMAGE h u) ((h:real^N->real^3),h')`
  ASSUME_TAC THENL [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (h:real^N->real^3) u = ball(vec 0,&1) INTER {z:real^3 | &0 <= z$3} /\
    IMAGE h (u INTER complex_boundary c) = IMAGE h u INTER {z:real^3 | z$3 = &0}`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^N->bool`; `h:real^N->real^3`; `f:real^3->real^3`;
                 `f':real^3->real^3`; `y:real^N`] MOI_LGB2_FIN_R0_BD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:real^2->real^N`; `y:real^N`;
                 `x1:real^2`; `x2:real^2`; `u:real^N->bool`;
                 `(f:real^3->real^3) o (h:real^N->real^3)`;
                 `(h':real^3->real^N) o (f':real^3->real^3)`;
                 `N1:real^2->bool`; `N2:real^2->bool`; `{z:real^3 | &0 <= z$3}`;
                 `UNIONS c:real^N->bool`]
    MOI_LGB2_TRANSFER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[o_THM; OPEN_IN_REFL] THEN
    REWRITE_TAC[IN_ELIM_THM; VECTOR_MUL_COMPONENT] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE]; ALL_TAC] THEN
    ASM_MESON_TAC[OPEN_IN_IMP_SUBSET; SUBSET];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u':real^N->bool` (X_CHOOSE_THEN `rho:real`
    (X_CHOOSE_THEN `n1:real^2->bool` (X_CHOOSE_THEN `n2:real^2->bool`
      STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN
   `IMAGE (\p. inv rho % ((f:real^3->real^3) o (h:real^N->real^3)) p)
          (u' INTER complex_boundary c) =
    IMAGE (\p. inv rho % (f o h) p) u' INTER {z:real^3 | z$3 = &0}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LGB2_FIN_BD_CLAUSE THEN
    MAP_EVERY EXISTS_TAC [`u:real^N->bool`; `h':real^3->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_lt_crossing2_at] THEN
  MAP_EVERY EXISTS_TAC
   [`u':real^N->bool`;
    `\p. inv rho % ((f:real^3->real^3) o (h:real^N->real^3)) p`;
    `\z. ((h':real^3->real^N) o (f':real^3->real^3)) (rho % z)`;
    `n1:real^2->bool`; `n2:real^2->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[o_THM] THEN ASM_REWRITE_TAC[VECTOR_MUL_RZERO]);;

(* ========================================================================= *)
(* The configuration at a double point y IN Q of a T-generic                 *)
(* disk inside a chart of the atlas, packed in the local predicate          *)
(* moi_lgb2_ctx: the two preimages x1, x2, the carrier sigma of y in tt     *)
(* (a wall or a cell), the carriers rho1, rho2 of x1, x2 in L, the chart    *)
(* affine on the simplices of tt at y; and the transversality of clause (4) *)
(* moved into the chart.                                                    *)
(* ========================================================================= *)

let MOI_LGB2_AFF_RELINT = prove
 (`!(l:real^M->real^N) b s.
     linear l /\ convex s
     ==> relative_interior (IMAGE (\x. l x + b) s) =
         IMAGE (\x. l x + b) (relative_interior s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!t:real^M->bool. IMAGE (\x. l x + b) t =
                                  IMAGE (\x:real^N. b + x) (IMAGE l t)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
    MATCH_MP_TAC IMAGE_EQ THEN REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    ASM_SIMP_TAC[RELATIVE_INTERIOR_TRANSLATION; RELATIVE_INTERIOR_LINEAR_IMAGE_CONVEX]]);;

let moi_lgb2_ctx = new_definition
 `moi_lgb2_ctx (c:(real^N->bool)->bool) (tt:(real^N->bool)->bool)
     (u:real^N->bool) (h:real^N->real^3) (h':real^3->real^N)
     (L:(real^2->bool)->bool) (g:real^2->real^N) (Q:real^N->bool) (y:real^N)
     (x1:real^2) (x2:real^2) (sigma:real^N->bool)
     (rho1:real^2->bool) (rho2:real^2->bool) <=>
   FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
   simplicial_complex tt /\ simplicial_complex L /\ UNIONS L = std_triangle /\
   moi_lt_singular_disk c g /\ moi_lgb_tgeneric tt L g Q /\ y IN Q /\
   x1 IN std_triangle /\ x2 IN std_triangle /\ ~(x1 = x2) /\ g x1 = y /\ g x2 = y /\
   open_in (subtopology euclidean (UNIONS c)) u /\ y IN u /\
   pl_homeomorphism (u,IMAGE h u) (h,h') /\
   ((u INTER complex_boundary c = {} /\ IMAGE h u = ball(vec 0,&1)) \/
    (IMAGE h u = ball(vec 0,&1) INTER {z:real^3 | &0 <= z$3} /\
     IMAGE h (u INTER complex_boundary c) =
     IMAGE h u INTER {z:real^3 | z$3 = &0})) /\
   (!p p'. p IN u /\ p' IN u /\ h p = h p' ==> p = p') /\
   sigma IN tt /\ y IN relative_interior sigma /\
   (!s. s IN tt /\ y IN s ==> sigma face_of s) /\
   (!s. s IN tt /\ y IN s
        ==> s SUBSET u /\ ?l b. linear l /\ !z. z IN s ==> h z = l z + b) /\
   rho1 IN L /\ x1 IN relative_interior rho1 /\
   (!r. r IN L /\ x1 IN r ==> rho1 face_of r) /\
   rho2 IN L /\ x2 IN relative_interior rho2 /\
   (!r. r IN L /\ x2 IN r ==> rho2 face_of r) /\
   (!r. r IN L ==> (?l b. linear l /\ !z. z IN r ==> g z = l z + b) /\
                   (?s. s IN tt /\ IMAGE g r SUBSET s) /\
                   (!z z'. z IN r /\ z' IN r /\ g z = g z' ==> z = z')) /\
   IMAGE g rho1 SUBSET sigma /\ IMAGE g rho2 SUBSET sigma /\
   (!r r'. r IN L /\ r' IN L /\ x1 IN r /\ x2 IN r' ==> DISJOINT r r') /\
   (aff_dim sigma = &2 \/ aff_dim sigma = &3) /\
   aff_dim (IMAGE g rho1) = aff_dim rho1 /\ aff_dim (IMAGE g rho2) = aff_dim rho2 /\
   (y IN complex_boundary c ==> aff_dim sigma = &2 /\ sigma SUBSET complex_boundary c)`;;

let MOI_LGB2_CTX_SWAP = prove
 (`!(c:(real^N->bool)->bool) tt u h h' L g Q y x1 x2 sigma rho1 rho2.
     moi_lgb2_ctx c tt u h h' L g Q y x1 x2 sigma rho1 rho2
     ==> moi_lgb2_ctx c tt u h h' L g Q y x2 x1 sigma rho2 rho1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lgb2_ctx] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[DISJOINT_SYM]);;

let MOI_LGB2_SETUP_G = prove
 (`!(c:(real^N->bool)->bool) tt L (g:real^2->real^N) Q.
     moi_lt_singular_disk c g /\ moi_lgb_tgeneric tt L g Q
     ==> simplicial_complex L /\ UNIONS L = std_triangle /\
         !r. r IN L ==> (?l b. linear l /\ !z. z IN r ==> g z = l z + b) /\
                        (?s. s IN tt /\ IMAGE g r SUBSET s) /\
                        (!z z'. z IN r /\ z' IN r /\ g z = g z' ==> z = z')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `simplicial_complex (L:(real^2->bool)->bool) /\ UNIONS L = std_triangle /\
    !r. r IN L ==> (?s. s IN tt /\ IMAGE (g:real^2->real^N) r SUBSET s) /\
                   (?l b. linear l /\ !z. z IN r ==> g z = l z + b)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lgb_tgeneric tt L (g:real^2->real^N) Q` THEN
    REWRITE_TAC[moi_lgb_tgeneric; moi_lgb_tlinear] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `r:real^2->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:real^2->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `l:real^2->real^N` (X_CHOOSE_THEN `b:real^N`
      STRIP_ASSUME_TAC))) THEN
  CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`l:real^2->real^N`; `b:real^N`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_LGA_AFFINE_LOCAL_INJ THEN
  MAP_EVERY EXISTS_TAC [`l:real^2->real^N`; `b:real^N`; `std_triangle`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(r:real^2->bool) SUBSET std_triangle` ASSUME_TAC THENL
   [UNDISCH_TAC `UNIONS L = std_triangle` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `(r:real^2->bool) IN L` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_CON_SC_CONVEX]; ALL_TAC] THEN
  UNDISCH_TAC `moi_lt_singular_disk c (g:real^2->real^N)` THEN
  REWRITE_TAC[moi_lt_singular_disk] THEN STRIP_TAC THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    can (find_term ((=) `open:(real^2->bool)->bool`)) (concl th))) THEN
  ASM SET_TAC[]);;

let MOI_LGB2_SETUP = prove
 (`!(c:(real^N->bool)->bool) tt A u h h' kk L (g:real^2->real^N) Q y.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\ moi_lgb_atlas c tt A /\
     (u,h,h',kk) IN A /\ y IN kk /\ moi_lt_singular_disk c g /\
     moi_lgb_tgeneric tt L g Q /\ y IN Q /\ y IN moi_lt_double_image g
     ==> ?x1 x2 sigma rho1 rho2.
           moi_lgb2_ctx c tt u h h' L g Q y x1 x2 sigma rho1 rho2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(y:real^N) IN moi_lt_double_image g` THEN
  REWRITE_TAC[moi_lt_double_image; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `x1:real^2` (X_CHOOSE_THEN `x2:real^2`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`]
    MOI_LGB2_SETUP_G) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "gr"))) THEN
  UNDISCH_TAC `moi_lgb_atlas c tt
    (A:((real^N->bool)#(real^N->real^3)#(real^3->real^N)#(real^N->bool))->bool)` THEN
  REWRITE_TAC[moi_lgb_atlas] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "cov") (CONJUNCTS_THEN2 ASSUME_TAC
      (MP_TAC o SPECL [`u:real^N->bool`; `h:real^N->real^3`;
                       `h':real^3->real^N`; `kk:real^N->bool`]))))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "margin"))))))) THEN
  SUBGOAL_THEN `(y:real^N) IN u` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!p p'. p IN u /\ p' IN u /\ (h:real^N->real^3) p = h p' ==> p = p'`
  ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (u,IMAGE h u) ((h:real^N->real^3),h')` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s IN tt /\ (y:real^N) IN s
        ==> s SUBSET u /\ ?l b. linear l /\ !z. z IN s ==> (h:real^N->real^3) z = l z + b`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN USE_THEN "margin" (MP_TAC o SPECL
      [`s:real^N->bool`; `s:real^N->bool`; `s:real^N->bool`]) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `y:real^N`] MOI_LGB2_SC_CARRIER) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sigma:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `x1:real^2`] MOI_LGB2_SC_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho1:real^2->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `x2:real^2`] MOI_LGB2_SC_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho2:real^2->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!x r. x IN relative_interior r /\ r IN L /\ (g:real^2->real^N) x = y
          ==> IMAGE g r SUBSET sigma`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "gr" (MP_TAC o C MATCH_MP (ASSUME `(r:real^2->bool) IN L`) o
                   SPEC `r:real^2->bool`) THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `l:real^2->real^N` (X_CHOOSE_THEN `b:real^N`
        STRIP_ASSUME_TAC))
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC)
        ASSUME_TAC)) THEN
    SUBGOAL_THEN `(x:real^2) IN r` ASSUME_TAC THENL
     [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (g:real^2->real^N) r = IMAGE (\z. l z + b) r`
    ASSUME_TAC THENL
     [MATCH_MP_TAC IMAGE_EQ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_OF_FACE_OF THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (g:real^2->real^N) r SUBSET s` THEN
      UNDISCH_TAC `(g:real^2->real^N) x = y` THEN
      UNDISCH_TAC `(x:real^2) IN r` THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `IMAGE (g:real^2->real^N) r SUBSET s` THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`l:real^2->real^N`; `b:real^N`; `r:real^2->bool`]
      MOI_LGB2_AFF_RELINT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[MOI_CON_SC_CONVEX]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `y:real^N` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(g:real^2->real^N) x = y` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r r'. r IN L /\ r' IN L /\ (x1:real^2) IN r /\ x2 IN r' ==> DISJOINT r r'`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[DISJOINT] THEN
    UNDISCH_TAC `moi_lgb_tgeneric tt L (g:real^2->real^N) Q` THEN
    REWRITE_TAC[moi_lgb_tgeneric] THEN
    DISCH_THEN(MP_TAC o SPECL [`r:real^2->bool`; `r':real^2->bool`;
                               `x1:real^2`; `x2:real^2`] o
               CONJUNCT1 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x1:real^2) IN rho1 /\ (x2:real^2) IN rho2` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN sigma` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `&2 <= aff_dim(sigma:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC(INT_ARITH `~(x <= &1) ==> &2 <= x:int`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `DISJOINT (rho1:real^2->bool) rho2` ASSUME_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `DISJOINT:(real^2->bool)->(real^2->bool)->bool`))
          (concl th) && is_forall (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `moi_lgb_tgeneric tt L (g:real^2->real^N) Q` THEN
    REWRITE_TAC[moi_lgb_tgeneric] THEN
    DISCH_THEN(MP_TAC o SPECL [`rho1:real^2->bool`; `rho2:real^2->bool`;
                               `sigma:real^N->bool`] o
               CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> F`) THEN
    ASM_REWRITE_TAC[IN_IMAGE] THEN CONJ_TAC THENL
     [EXISTS_TAC `x1:real^2` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `x2:real^2` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(sigma:real^N->bool) <= &3` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `sigma:real^N->bool`]
      MOI_CON_SC_SIMPLEX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `n:int`) THEN
    FIRST_ASSUM(MP_TAC o SPEC `sigma:real^N->bool` o
      check (fun th -> can (find_term ((=) `(h:real^N->real^3)`)) (concl th) &&
                       is_forall (concl th))) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `l:real^N->real^3` (X_CHOOSE_THEN `b:real^3`
        STRIP_ASSUME_TAC))) THEN
    MP_TAC(ISPECL [`n:int`; `h:real^N->real^3`; `l:real^N->real^3`; `b:real^3`;
                   `sigma:real^N->bool`] MOI_LGA_SIMPLEX_IMAGE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `p':real^N`)) (concl th))) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN
    MP_TAC(ISPEC `IMAGE (h:real^N->real^3) sigma` AFF_DIM_LE_UNIV) THEN
    REWRITE_TAC[DIMINDEX_3] THEN
    UNDISCH_TAC `n simplex (sigma:real^N->bool)` THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r x. r IN L /\ x IN r
          ==> aff_dim (IMAGE (g:real^2->real^N) r) = aff_dim r`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `r:real^2->bool`]
      MOI_CON_SC_SIMPLEX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `n:int`) THEN
    USE_THEN "gr" (MP_TAC o C MATCH_MP (ASSUME `(r:real^2->bool) IN L`) o
                   SPEC `r:real^2->bool`) THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `l:real^2->real^N` (X_CHOOSE_THEN `b:real^N`
        STRIP_ASSUME_TAC))
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC)
        ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`n:int`; `g:real^2->real^N`; `l:real^2->real^N`; `b:real^N`;
                   `r:real^2->bool`] MOI_LGA_SIMPLEX_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN
    ASM_MESON_TAC[AFF_DIM_SIMPLEX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(y:real^N) IN complex_boundary c
    ==> aff_dim (sigma:real^N->bool) = &2 /\ sigma SUBSET complex_boundary c`
  ASSUME_TAC THENL
   [REWRITE_TAC[complex_boundary; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC) THEN
    USE_THEN "cov" (MP_TAC o C MATCH_MP (ASSUME `(w:real^N->bool) IN c`) o
                    SPEC `w:real^N->bool`) THEN
    DISCH_THEN(X_CHOOSE_THEN `d:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(y:real^N) IN UNIONS d` MP_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER] THEN REWRITE_TAC[IN_UNIONS] THEN
      EXISTS_TAC `sigma:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(s:real^N->bool) IN tt /\ s SUBSET w` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `UNIONS d:real^N->bool` THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[INTER_SUBSET]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(sigma:real^N->bool) SUBSET w` ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FACE_OF_IMP_SUBSET THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`sigma:real^N->bool`; `w:real^N->bool`] AFF_DIM_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&2 <= aff_dim(sigma:real^N->bool)` THEN
      INT_ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `z:real^N` THEN
      DISCH_TAC THEN EXISTS_TAC `w:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`x1:real^2`; `x2:real^2`; `sigma:real^N->bool`;
                        `rho1:real^2->bool`; `rho2:real^2->bool`] THEN
  REWRITE_TAC[moi_lgb2_ctx] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `relative_interior:(real^2->bool)->real^2->bool`))
        (concl th) && is_forall (concl th))) THEN
    EXISTS_TAC `x1:real^2` THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `relative_interior:(real^2->bool)->real^2->bool`))
        (concl th) && is_forall (concl th))) THEN
    EXISTS_TAC `x2:real^2` THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `&2 <= aff_dim(sigma:real^N->bool)` THEN
    UNDISCH_TAC `aff_dim(sigma:real^N->bool) <= &3` THEN INT_ARITH_TAC;
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]]);;

let MOI_LGB2_CTX_BASIC = prove
 (`!(c:(real^N->bool)->bool) tt u h h' L g Q y x1 x2 sigma rho1 rho2.
     moi_lgb2_ctx c tt u h h' L g Q y x1 x2 sigma rho1 rho2
     ==> x1 IN rho1 /\ x2 IN rho2 /\ y IN sigma /\ DISJOINT rho1 rho2 /\
         y IN IMAGE g rho1 /\ y IN IMAGE g rho2 /\
         sigma SUBSET u /\
         (?l b. linear l /\ !z. z IN sigma ==> h z = l z + b) /\
         convex sigma /\ convex rho1 /\ convex rho2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lgb2_ctx] THEN
  DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  SUBGOAL_THEN `(x1:real^2) IN rho1 /\ (x2:real^2) IN rho2 /\ (y:real^N) IN sigma`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_IMAGE] THEN REPEAT CONJ_TAC THEN
  ASM_MESON_TAC[MOI_CON_SC_CONVEX]);;

let MOI_LGB2_CLAUSE4 = prove
 (`!(c:(real^N->bool)->bool) tt u h h' L g Q y x1 x2 sigma rho1 rho2.
     moi_lgb2_ctx c tt u h h' L g Q y x1 x2 sigma rho1 rho2
     ==> aff_dim sigma <= aff_dim (IMAGE g rho1) + aff_dim (IMAGE g rho2) /\
         aff_dim (affine hull (IMAGE g rho1) INTER affine hull (IMAGE g rho2)) =
         aff_dim (IMAGE g rho1) + aff_dim (IMAGE g rho2) - aff_dim sigma`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB2_CTX_BASIC) THEN
  FIRST_X_ASSUM(MAP_EVERY ASSUME_TAC o CONJUNCTS o
    GEN_REWRITE_RULE I [moi_lgb2_ctx]) THEN
  UNDISCH_TAC `moi_lgb_tgeneric tt L (g:real^2->real^N) Q` THEN
  REWRITE_TAC[moi_lgb_tgeneric] THEN
  DISCH_THEN(MP_TAC o SPECL [`rho1:real^2->bool`; `rho2:real^2->bool`;
                             `sigma:real^N->bool`] o
             CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[UNION_SUBSET] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC FACE_OF_IMP_SUBSET THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `y:real^N` THEN
    ASM_REWRITE_TAC[]]);;

let MOI_LGB2_TRANSV = prove
 (`!(c:(real^N->bool)->bool) tt u (h:real^N->real^3) h' L g Q y x1 x2 sigma
    rho1 rho2.
     moi_lgb2_ctx c tt u h h' L g Q y x1 x2 sigma rho1 rho2 /\
     aff_dim rho2 < aff_dim sigma
     ==> ~(IMAGE (h o g) rho1 SUBSET affine hull (IMAGE (h o g) rho2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB2_CTX_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB2_CLAUSE4) THEN
  FIRST_X_ASSUM(MAP_EVERY ASSUME_TAC o CONJUNCTS o
    GEN_REWRITE_RULE I [moi_lgb2_ctx]) THEN
  SUBGOAL_THEN
   `!X:real^2->bool. IMAGE (g:real^2->real^N) X SUBSET sigma
                     ==> IMAGE ((h:real^N->real^3) o g) X =
                         IMAGE (\x. l x + b) (IMAGE g X)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC IMAGE_EQ THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`l:real^N->real^3`; `b:real^3`; `sigma:real^N->bool`;
                 `IMAGE (g:real^2->real^N) rho1`; `IMAGE (g:real^2->real^N) rho2`]
    MOI_LGB2_PULLBACK_HULL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `p':real^N`)) (concl th))) THEN
    ASM_SIMP_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `affine hull (IMAGE (g:real^2->real^N) rho1) INTER
    affine hull (IMAGE g rho2) = affine hull (IMAGE g rho1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!a b:real^N->bool. a SUBSET b ==> a INTER b = a`) THEN
    MATCH_MP_TAC HULL_MINIMAL THEN ASM_REWRITE_TAC[AFFINE_AFFINE_HULL];
    ALL_TAC] THEN
  UNDISCH_TAC
   `aff_dim (affine hull (IMAGE (g:real^2->real^N) rho1) INTER
             affine hull (IMAGE g rho2)) =
    aff_dim (IMAGE g rho1) + aff_dim (IMAGE g rho2) -
    aff_dim (sigma:real^N->bool)` THEN
  ASM_REWRITE_TAC[AFF_DIM_AFFINE_HULL] THEN
  UNDISCH_TAC `aff_dim (rho2:real^2->bool) < aff_dim (sigma:real^N->bool)` THEN
  INT_ARITH_TAC);;

let MOI_LGB2_DIMS = prove
 (`!(c:(real^N->bool)->bool) tt u h h' L g Q y x1 x2 sigma rho1 rho2.
     moi_lgb2_ctx c tt u h h' L g Q y x1 x2 sigma rho1 rho2
     ==> (aff_dim sigma = &3 /\
          ((aff_dim rho1 = &2 /\ aff_dim rho2 = &2) \/
           (aff_dim rho1 = &1 /\ aff_dim rho2 = &2) \/
           (aff_dim rho1 = &2 /\ aff_dim rho2 = &1))) \/
         (aff_dim sigma = &2 /\ aff_dim rho1 = &1 /\ aff_dim rho2 = &1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB2_CTX_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB2_CLAUSE4) THEN
  FIRST_X_ASSUM(MAP_EVERY ASSUME_TAC o CONJUNCTS o
    GEN_REWRITE_RULE I [moi_lgb2_ctx]) THEN
  SUBGOAL_THEN `&0 <= aff_dim (rho1:real^2->bool) /\ &0 <= aff_dim (rho2:real^2->bool)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[AFF_DIM_POS_LE] THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `rho1:real^2->bool` MOI_LGB2_DIM_LE_2) THEN
  MP_TAC(ISPEC `rho2:real^2->bool` MOI_LGB2_DIM_LE_2) THEN
  SUBGOAL_THEN
   `aff_dim (sigma:real^N->bool) = &2
    ==> ~(aff_dim (rho1:real^2->bool) = &2) /\ ~(aff_dim (rho2:real^2->bool) = &2)`
  MP_TAC THENL
   [DISCH_TAC THEN CONJ_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `moi_lgb_tgeneric tt L (g:real^2->real^N) Q` THEN
    REWRITE_TAC[moi_lgb_tgeneric] THENL
     [DISCH_THEN(MP_TAC o SPECL [`rho1:real^2->bool`; `sigma:real^N->bool`] o
                 CONJUNCT1 o CONJUNCT2 o CONJUNCT2);
      DISCH_THEN(MP_TAC o SPECL [`rho2:real^2->bool`; `sigma:real^N->bool`] o
                 CONJUNCT1 o CONJUNCT2 o CONJUNCT2)] THEN
    ASM_REWRITE_TAC[INT_LE_REFL] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `y:real^N` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC
   `aff_dim (sigma:real^N->bool) <=
    aff_dim (IMAGE (g:real^2->real^N) rho1) + aff_dim (IMAGE g rho2)` THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `aff_dim (sigma:real^N->bool) = &2 \/ aff_dim sigma = &3` THEN
  UNDISCH_TAC `&0 <= aff_dim (rho1:real^2->bool)` THEN
  UNDISCH_TAC `&0 <= aff_dim (rho2:real^2->bool)` THEN
  INT_ARITH_TAC);;

(* ========================================================================= *)
(* The sheets at the two preimages.  Source side: a triangle                *)
(* carrier contains a ball; an interior edge carrier has two triangles      *)
(* covering a ball; a frontier edge carrier has one triangle covering a     *)
(* neighbourhood in std_triangle.  Chart side: h o g is affine and          *)
(* injective on each simplex of L at x1 or x2.                              *)
(* ========================================================================= *)

let MOI_LGB2_SHEET_TRI = prove
 (`!(L:(real^2->bool)->bool) rho x.
     simplicial_complex L /\ rho IN L /\ aff_dim rho = &2 /\
     x IN relative_interior rho
     ==> ?p q w. rho = convex hull {p,q,w} /\ ~affine_dependent {p,q,w} /\
                 ~(p = q) /\ ~(p = w) /\ ~(q = w) /\
                 ?d. &0 < d /\ ball(x,d) SUBSET rho`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `rho:real^2->bool`]
    MOI_SCF_SC_VERTICES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^2->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(V:real^2->bool) HAS_SIZE 3` MP_TAC THENL
   [ASM_REWRITE_TAC[HAS_SIZE; GSYM INT_OF_NUM_EQ] THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[MOI_SCF_HAS_SIZE_3] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^2` (X_CHOOSE_THEN `q:real^2`
    (X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`p:real^2`; `q:real^2`; `w:real^2`] THEN
  UNDISCH_THEN `V = {p:real^2,q,w}` SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `relative_interior rho = interior (rho:real^2->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC RELATIVE_INTERIOR_INTERIOR THEN
    REWRITE_TAC[GSYM AFF_DIM_EQ_FULL; DIMINDEX_2] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `interior (rho:real^2->bool)` OPEN_CONTAINS_BALL) THEN
  REWRITE_TAC[OPEN_INTERIOR] THEN DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `interior (rho:real^2->bool)` THEN
  ASM_REWRITE_TAC[INTERIOR_SUBSET] THEN
  UNDISCH_TAC `rho = convex hull {p:real^2,q,w}` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[INTERIOR_SUBSET]);;

let MOI_LGB2_STD_INTERIOR = prove
 (`!x:real^2. x IN std_triangle /\ ~(x IN relative_frontier std_triangle)
              ==> ?d. &0 < d /\ ball(x,d) SUBSET std_triangle`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^2) IN interior std_triangle` MP_TAC THENL
   [SUBGOAL_THEN `relative_interior std_triangle = interior std_triangle`
    (SUBST1_TAC o SYM) THENL
     [MATCH_MP_TAC RELATIVE_INTERIOR_INTERIOR THEN
      REWRITE_TAC[GSYM AFF_DIM_EQ_FULL; DIMINDEX_2; MOI_LGB2_STD_DIM];
      ALL_TAC] THEN
    UNDISCH_TAC `~((x:real^2) IN relative_frontier std_triangle)` THEN
    UNDISCH_TAC `(x:real^2) IN std_triangle` THEN
    REWRITE_TAC[relative_frontier] THEN
    MP_TAC(ISPEC `std_triangle` CLOSURE_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `interior std_triangle` OPEN_CONTAINS_BALL) THEN
  REWRITE_TAC[OPEN_INTERIOR] THEN DISCH_THEN(fun th -> DISCH_THEN
    (MP_TAC o MATCH_MP th)) THEN
  MESON_TAC[INTERIOR_SUBSET; SUBSET_TRANS]);;

let MOI_LGB2_SHEET_EDGE2 = prove
 (`!(L:(real^2->bool)->bool) e x.
     simplicial_complex L /\ UNIONS L = std_triangle /\ e IN L /\ aff_dim e = &1 /\
     x IN relative_interior e /\ ~(x IN relative_frontier std_triangle)
     ==> ?p q w w' mu.
           e = convex hull {p,q} /\ ~(p = q) /\ &0 < mu /\ mu < &1 /\
           x = (&1 - mu) % p + mu % q /\
           convex hull {p,q,w} IN L /\ convex hull {p,q,w'} IN L /\
           ~affine_dependent {p,q,w} /\ ~affine_dependent {p,q,w'} /\
           ~(p = w) /\ ~(q = w) /\ ~(p = w') /\ ~(q = w') /\ ~(w = w') /\
           convex hull {p,q,w} INTER convex hull {p,q,w'} = convex hull {p,q} /\
           ?d. &0 < d /\ ball(x,d) SUBSET std_triangle /\
               !z. z IN ball(x,d)
                   ==> z IN convex hull {p,q,w} \/ z IN convex hull {p,q,w'}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `e:real^2->bool`; `x:real^2`]
    MOI_LGB2_EDGE_INTERIOR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real^2->bool` (X_CHOOSE_THEN `t2:real^2->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "uniq")))))))))) THEN
  SUBGOAL_THEN `(x:real^2) IN std_triangle` ASSUME_TAC THENL
   [UNDISCH_TAC `UNIONS L = std_triangle` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `e:real^2->bool` THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPEC `x:real^2` MOI_LGB2_STD_INTERIOR) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `e:real^2->bool`; `x:real^2`]
    MOI_LGB2_EDGE_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "loc"))) THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `e:real^2->bool`] MOI_SCF_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^2` (X_CHOOSE_THEN `q:real^2`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `p:real^2`; `q:real^2`;
                 `t1:real^2->bool`] MOI_SCF_TRIANGLE_ON_EDGE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `p:real^2`; `q:real^2`;
                 `t2:real^2->bool`] MOI_SCF_TRIANGLE_ON_EDGE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w':real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(w:real^2 = w')` ASSUME_TAC THENL
   [DISCH_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^2) IN relative_interior (convex hull {p,q})` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; RELATIVE_INTERIOR_SEGMENT;
                  IN_SEGMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `mu:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`p:real^2`; `q:real^2`; `w:real^2`; `w':real^2`;
                        `mu:real`] THEN
  SUBGOAL_THEN `convex hull {p:real^2,q,w} IN L /\ convex hull {p,q,w'} IN L`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `e = convex hull {p:real^2,q}` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `{p:real^2,q,w}`;
                   `{p:real^2,q,w'}`] MOI_REAL_SIMPLICIAL_COMPLEX_INTER_HULL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN AP_TERM_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `min d1 d2:real` THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(x:real^2,d1)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `z:real^2` THEN REWRITE_TAC[IN_BALL; REAL_LT_MIN] THEN STRIP_TAC THEN
  USE_THEN "loc" (MP_TAC o SPEC `z:real^2`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `ball(x:real^2,d1) SUBSET std_triangle` THEN
      REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[DIST_SYM]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^2->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "uniq" (MP_TAC o SPEC `t:real^2->bool`) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let MOI_LGB2_SHEET_EDGE1 = prove
 (`!(L:(real^2->bool)->bool) e x.
     simplicial_complex L /\ UNIONS L = std_triangle /\ e IN L /\ aff_dim e = &1 /\
     x IN relative_interior e /\ e SUBSET relative_frontier std_triangle
     ==> ?p q w mu.
           e = convex hull {p,q} /\ ~(p = q) /\ &0 < mu /\ mu < &1 /\
           x = (&1 - mu) % p + mu % q /\
           convex hull {p,q,w} IN L /\ ~affine_dependent {p,q,w} /\
           ~(p = w) /\ ~(q = w) /\
           ?d. &0 < d /\
               !z. z IN std_triangle /\ dist(z,x) < d ==> z IN convex hull {p,q,w}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `e:real^2->bool`]
    MOI_LGB2_EDGE_FRONTIER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real^2->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "uniq"))))) THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `e:real^2->bool`; `x:real^2`]
    MOI_LGB2_EDGE_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "loc"))) THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `e:real^2->bool`] MOI_SCF_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^2` (X_CHOOSE_THEN `q:real^2`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `p:real^2`; `q:real^2`;
                 `t1:real^2->bool`] MOI_SCF_TRIANGLE_ON_EDGE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:real^2) IN relative_interior (convex hull {p,q})` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; RELATIVE_INTERIOR_SEGMENT;
                  IN_SEGMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `mu:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`p:real^2`; `q:real^2`; `w:real^2`; `mu:real`] THEN
  SUBGOAL_THEN `e = convex hull {p:real^2,q} /\ convex hull {p,q,w} IN L`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
  USE_THEN "loc" (MP_TAC o SPEC `z:real^2`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^2->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "uniq" (MP_TAC o SPEC `t:real^2->bool`) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let MOI_LGB2_CTX_PHI = prove
 (`!(c:(real^N->bool)->bool) tt u (h:real^N->real^3) h' L g Q y x1 x2 sigma
    rho1 rho2 r x.
     moi_lgb2_ctx c tt u h h' L g Q y x1 x2 sigma rho1 rho2 /\
     r IN L /\ x IN r /\ g x = y
     ==> IMAGE g r SUBSET u /\
         (?l b. linear l /\ !z. z IN r ==> h(g z) = l z + b) /\
         (!z z'. z IN r /\ z' IN r /\ h(g z) = h(g z') ==> z = z') /\
         (?s. s IN tt /\ IMAGE g r SUBSET s /\ sigma face_of s /\
              (?l b. linear l /\ !z. z IN s ==> h z = l z + b))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MAP_EVERY ASSUME_TAC o CONJUNCTS o
    GEN_REWRITE_RULE I [moi_lgb2_ctx]) THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(r:real^2->bool) IN L`) o
    check (fun th -> can (find_term ((=) `z':real^2`)) (concl th) &&
                     is_forall (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `lg:real^2->real^N` (X_CHOOSE_THEN `bg:real^N`
      STRIP_ASSUME_TAC))
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC)
      ASSUME_TAC)) THEN
  SUBGOAL_THEN `(y:real^N) IN s` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (g:real^2->real^N) r SUBSET s` THEN
    UNDISCH_TAC `(g:real^2->real^N) x = y` THEN
    UNDISCH_TAC `(x:real^2) IN r` THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (CONJ (ASSUME `(s:real^N->bool) IN tt`)
                                         (ASSUME `(y:real^N) IN s`)) o
    SPEC `s:real^N->bool` o
    check (fun th -> can (find_term ((=) `(h:real^N->real^3)`)) (concl th) &&
                     is_forall (concl th) &&
                     can (find_term ((=) `u:real^N->bool`)) (concl th) &&
                     not (can (find_term ((=) `p':real^N`)) (concl th)))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `lh:real^N->real^3` (X_CHOOSE_THEN `bh:real^3`
      STRIP_ASSUME_TAC))) THEN
  REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    MAP_EVERY EXISTS_TAC [`(lh:real^N->real^3) o (lg:real^2->real^N)`;
                          `(lh:real^N->real^3) bg + bh`] THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[LINEAR_COMPOSE]; ALL_TAC] THEN
    X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(g:real^2->real^N) z IN s` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(h:real^N->real^3)((g:real^2->real^N) z) = lh(g z) + bh`
    SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(g:real^2->real^N) z = lg z + bg` SUBST1_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[LINEAR_ADD] THEN VECTOR_ARITH_TAC;
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `z':real^2`)) (concl th) &&
      not (can (find_term ((=) `L:(real^2->bool)->bool`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `p':real^N`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`lh:real^N->real^3`; `bh:real^3`] THEN
    ASM_REWRITE_TAC[]]);;

let MOI_LGB2_TWO_BALLS = prove
 (`!x1 x2:real^2 d1 d2.
     ~(x1 = x2) /\ &0 < d1 /\ &0 < d2
     ==> ?d. &0 < d /\ d <= d1 /\ d <= d2 /\ DISJOINT (ball(x1,d)) (ball(x2,d))`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `min (min d1 d2) (dist(x1:real^2,x2) / &2)` THEN
  SUBGOAL_THEN `&0 < dist(x1:real^2,x2)` ASSUME_TAC THENL
   [MATCH_MP_TAC DIST_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC; REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_BALL; NOT_IN_EMPTY] THEN
  X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`x1:real^2`; `z:real^2`; `x2:real^2`] DIST_TRIANGLE) THEN
  MP_TAC(ISPECL [`z:real^2`; `x2:real^2`] DIST_SYM) THEN
  ASM_REAL_ARITH_TAC);;

let MOI_LGB2_PLANE_BASE = prove
 (`!P Q W z z0:real^3.
     ~((Q - P) cross (W - P) = vec 0) /\ z0 IN affine hull {P,Q,W}
     ==> (((Q - P) cross (W - P)) dot (z - z0) = &0 <=>
          z IN affine hull {P,Q,W})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`P:real^3`; `Q:real^3`; `W:real^3`; `z0:real^3`]
    MOI_LGB2_PLANE_CHAR) THEN
  MP_TAC(ISPECL [`P:real^3`; `Q:real^3`; `W:real^3`; `z:real^3`]
    MOI_LGB2_PLANE_CHAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[DOT_RSUB] THEN REAL_ARITH_TAC);;

let MOI_LGB2_TRI_PLANE = prove
 (`!(f:real^2->real^3) l b p q w x0.
     linear l /\ (!x. x IN convex hull {p,q,w} ==> f x = l x + b) /\
     x0 IN convex hull {p,q,w}
     ==> IMAGE f (convex hull {p,q,w}) SUBSET affine hull {f p, f q, f w} /\
         affine hull (IMAGE f (convex hull {p,q,w})) = affine hull {f p, f q, f w} /\
         (~((f q - f p) cross (f w - f p) = vec 0)
          ==> !z. z IN convex hull {p,q,w}
                  ==> ((f q - f p) cross (f w - f p)) dot (f z - f x0) = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^2->real^3`; `l:real^2->real^3`; `b:real^3`;
                 `{p:real^2,q,w}`] MOI_LGA_HULL_IMAGE) THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL; AFFINE_HULL_CONVEX_HULL] THEN
  DISCH_TAC THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(f:real^2->real^3) p`; `(f:real^2->real^3) q`;
                 `(f:real^2->real^3) w`; `(f:real^2->real^3) z`;
                 `(f:real^2->real^3) x0`] MOI_LGB2_PLANE_BASE) THEN
  SUBGOAL_THEN
   `!v. v IN convex hull {p,q,w}
        ==> (f:real^2->real^3) v IN affine hull {f p, f q, f w}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(SET_RULE `!a b (x:real^3). a SUBSET b /\ x IN a ==> x IN b`) THEN
    EXISTS_TAC `convex hull {(f:real^2->real^3) p, f q, f w}` THEN
    REWRITE_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL] THEN
    MP_TAC(ISPECL [`f:real^2->real^3`; `l:real^2->real^3`; `b:real^3`;
                   `{p:real^2,q,w}`] MOI_LGA_HULL_IMAGE) THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[]);;

let MOI_LGB2_CROSS_PARALLEL = prove
 (`!n1 n2:real^3.
     ~(n1 = vec 0) /\ ~(n2 = vec 0) /\ n1 cross n2 = vec 0
     ==> ?k. n2 = k % n1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CROSS_EQ_0; COLLINEAR_LEMMA] THEN
  MESON_TAC[]);;

let MOI_LGB2_SD_FACTS = prove
 (`!(c:(real^N->bool)->bool) (g:real^2->real^N) x.
     moi_lt_singular_disk c g /\ x IN std_triangle
     ==> (x IN relative_frontier std_triangle <=> g x IN complex_boundary c) /\
         ?d. &0 < d /\
             !z z'. z IN std_triangle /\ z' IN std_triangle /\
                    dist(z,x) < d /\ dist(z',x) < d /\ g z = g z' ==> z = z'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lt_singular_disk] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `{x | x IN std_triangle /\ (g:real^2->real^N) x IN complex_boundary c} =
                 relative_frontier std_triangle` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2` o check (fun th ->
    can (find_term ((=) `open:(real^2->bool)->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:real^2->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `n:real^2->bool` OPEN_CONTAINS_BALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER] THEN
  CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
  REWRITE_TAC[IN_BALL] THEN ASM_MESON_TAC[DIST_SYM]);;

(* ========================================================================= *)
(* Helpers for the wall cases.  The model M3 in symmetric form             *)
(* (opposite signs of the wings), the cells on the two sides of a wall      *)
(* carrying the triangles at an edge preimage (three-dimensional, distinct, *)
(* meeting in the wall), the wings on opposite sides of the wall in the     *)
(* chart, and wings off the wall.                                           *)
(* ========================================================================= *)

let MOI_LGB2_PROD_NEG = prove
 (`!x y. x * y < &0 ==> (&0 < x /\ y < &0) \/ (x < &0 /\ &0 < y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `&0 < x` THEN ASM_CASES_TAC `&0 < y` THEN ASM_REWRITE_TAC[] THENL
   [MP_TAC(SPECL [`x:real`; `y:real`] REAL_LT_MUL) THEN ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `~(&0 < y)` THEN REWRITE_TAC[REAL_NOT_LT] THEN
    REWRITE_TAC[REAL_LE_LT] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `x * y < &0` THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
    REAL_ARITH_TAC;
    UNDISCH_TAC `~(&0 < x)` THEN REWRITE_TAC[REAL_NOT_LT] THEN
    REWRITE_TAC[REAL_LE_LT] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `x * y < &0` THEN ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
    REAL_ARITH_TAC;
    MP_TAC(SPECL [`--x:real`; `--y:real`] REAL_LE_MUL) THEN
    ASM_REAL_ARITH_TAC]);;

let MOI_LGB2_MODEL_M3S = prove
 (`!(z0:real^3) (nu:real^3) d1 d2 a1 a2 b1 b2.
     nu dot d1 = &0 /\ nu dot d2 = &0 /\ ~(d1 cross d2 = vec 0) /\
     (nu dot a1) * (nu dot a2) < &0 /\ (nu dot b1) * (nu dot b2) < &0
     ==> ?f f'. pl_homeomorphism ((:real^3),(:real^3)) (f,f') /\ f z0 = vec 0 /\
                (!s t. &0 <= s ==> (f (z0 + t % d1 + s % a1))$1 = &0) /\
                (!s t. &0 <= s ==> (f (z0 + t % d1 + s % a2))$1 = &0) /\
                (!s t. &0 <= s ==> (f (z0 + t % d2 + s % b1))$2 = &0) /\
                (!s t. &0 <= s ==> (f (z0 + t % d2 + s % b2))$2 = &0) /\
                (!z. (f z)$3 = nu dot (z - z0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MOI_LGB2_PROD_NEG) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MOI_LGB2_PROD_NEG) THEN
  STRIP_TAC THEN STRIP_TAC THENL
   [MP_TAC(ISPECL [`z0:real^3`; `nu:real^3`; `d1:real^3`; `d2:real^3`;
                   `a1:real^3`; `a2:real^3`; `b1:real^3`; `b2:real^3`]
      MOI_LGB2_MODEL_M3);
    MP_TAC(ISPECL [`z0:real^3`; `nu:real^3`; `d1:real^3`; `d2:real^3`;
                   `a1:real^3`; `a2:real^3`; `b2:real^3`; `b1:real^3`]
      MOI_LGB2_MODEL_M3);
    MP_TAC(ISPECL [`z0:real^3`; `nu:real^3`; `d1:real^3`; `d2:real^3`;
                   `a2:real^3`; `a1:real^3`; `b1:real^3`; `b2:real^3`]
      MOI_LGB2_MODEL_M3);
    MP_TAC(ISPECL [`z0:real^3`; `nu:real^3`; `d1:real^3`; `d2:real^3`;
                   `a2:real^3`; `a1:real^3`; `b2:real^3`; `b1:real^3`]
      MOI_LGB2_MODEL_M3)] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `f':real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`f:real^3->real^3`; `f':real^3->real^3`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_LGB2_MODEL_M4 = prove
 (`!(z0:real^3) d1 d2 a b.
     z0$3 = &0 /\ d1$3 = &0 /\ d2$3 = &0 /\ ~(d1 cross d2 = vec 0) /\
     &0 < a$3 /\ &0 < b$3
     ==> ?f f'. pl_homeomorphism ((:real^3),(:real^3)) (f,f') /\ f z0 = vec 0 /\
                (!s t. (f (z0 + s % d1 + t % a))$1 = &0) /\
                (!s t. (f (z0 + s % d2 + t % b))$2 = &0) /\
                (!z. (f z)$3 = z$3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`z0:real^3`; `basis 3:real^3`; `d1:real^3`; `d2:real^3`;
                 `a:real^3`; `--a:real^3`; `b:real^3`; `--b:real^3`]
    MOI_LGB2_MODEL_M3) THEN
  SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH; VECTOR_NEG_COMPONENT] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `f':real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`f:real^3->real^3`; `f':real^3->real^3`] THEN
  ASM_REWRITE_TAC[VECTOR_SUB_COMPONENT; REAL_SUB_RZERO] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN ASM_CASES_TAC `&0 <= t` THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `a:real^3`)) (concl th) &&
      not (can (find_term ((=) `--a:real^3`)) (concl th)))) THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`--t:real`; `s:real`] o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `--a:real^3`)) (concl th))) THEN
    REWRITE_TAC[VECTOR_MUL_LNEG; VECTOR_MUL_RNEG; VECTOR_NEG_NEG] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `b:real^3`)) (concl th) &&
      not (can (find_term ((=) `--b:real^3`)) (concl th)))) THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`--t:real`; `s:real`] o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `--b:real^3`)) (concl th))) THEN
    REWRITE_TAC[VECTOR_MUL_LNEG; VECTOR_MUL_RNEG; VECTOR_NEG_NEG] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

let MOI_LGB2_CELL_DIM_LE3 = prove
 (`!(c:(real^N->bool)->bool) tt u (h:real^N->real^3) h' L g Q y x1 x2 sigma
    rho1 rho2 s.
     moi_lgb2_ctx c tt u h h' L g Q y x1 x2 sigma rho1 rho2 /\
     s IN tt /\ y IN s
     ==> aff_dim s <= &3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MAP_EVERY ASSUME_TAC o CONJUNCTS o
    GEN_REWRITE_RULE I [moi_lgb2_ctx]) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `s:real^N->bool`]
    MOI_CON_SC_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `n:int`) THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (CONJ (ASSUME `(s:real^N->bool) IN tt`)
                                         (ASSUME `(y:real^N) IN s`)) o
    SPEC `s:real^N->bool` o
    check (fun th -> can (find_term ((=) `(h:real^N->real^3)`)) (concl th) &&
                     is_forall (concl th) &&
                     can (find_term ((=) `u:real^N->bool`)) (concl th) &&
                     not (can (find_term ((=) `p':real^N`)) (concl th)))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `l:real^N->real^3` (X_CHOOSE_THEN `b:real^3`
      STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`n:int`; `h:real^N->real^3`; `l:real^N->real^3`; `b:real^3`;
                 `s:real^N->bool`] MOI_LGA_SIMPLEX_IMAGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `p':real^N`)) (concl th))) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN
  MP_TAC(ISPEC `IMAGE (h:real^N->real^3) s` AFF_DIM_LE_UNIV) THEN
  REWRITE_TAC[DIMINDEX_3] THEN
  UNDISCH_TAC `n simplex (s:real^N->bool)` THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN INT_ARITH_TAC);;

let MOI_LGB2_CELL3 = prove
 (`!(c:(real^N->bool)->bool) tt u (h:real^N->real^3) h' L g Q y x1 x2 sigma
    rho1 rho2 r x s.
     moi_lgb2_ctx c tt u h h' L g Q y x1 x2 sigma rho1 rho2 /\
     r IN L /\ aff_dim r = &2 /\ x IN r /\ g x = y /\ s IN tt /\
     IMAGE g r SUBSET s
     ==> aff_dim s = &3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN s` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (g:real^2->real^N) r SUBSET s` THEN
    UNDISCH_TAC `(g:real^2->real^N) x = y` THEN
    UNDISCH_TAC `(x:real^2) IN r` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                 `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `y:real^N`; `x1:real^2`; `x2:real^2`; `sigma:real^N->bool`;
                 `rho1:real^2->bool`; `rho2:real^2->bool`; `s:real^N->bool`]
    MOI_LGB2_CELL_DIM_LE3) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MAP_EVERY ASSUME_TAC o CONJUNCTS o
    GEN_REWRITE_RULE I [moi_lgb2_ctx]) THEN
  MATCH_MP_TAC(INT_ARITH `x <= &3 /\ ~(x <= &2) ==> x:int = &3`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `moi_lgb_tgeneric tt L (g:real^2->real^N) Q` THEN
  REWRITE_TAC[moi_lgb_tgeneric] THEN
  DISCH_THEN(MP_TAC o SPECL [`r:real^2->bool`; `s:real^N->bool`] o
    CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE] THEN
  EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[]);;

let MOI_LGB2_CELLS_INTER = prove
 (`!(tt:(real^N->bool)->bool) s s' sigma.
     simplicial_complex tt /\ s IN tt /\ s' IN tt /\ ~(s = s') /\
     aff_dim s = &3 /\ aff_dim s' = &3 /\ sigma face_of s /\ sigma face_of s' /\
     aff_dim sigma = &2
     ==> s INTER s' = sigma`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(s INTER s') face_of (s:real^N->bool) /\ (s INTER s') face_of s'`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `convex(s:real^N->bool) /\ convex(s':real^N->bool)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[MOI_CON_SC_CONVEX]; ALL_TAC] THEN
  SUBGOAL_THEN `(sigma:real^N->bool) SUBSET s INTER s'` ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET_INTER]; ALL_TAC] THEN
  SUBGOAL_THEN `~(s INTER s' = (s:real^N->bool))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(s:real^N->bool) face_of s'` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `s':real^N->bool`] FACE_OF_AFF_DIM_LT) THEN
    ASM_REWRITE_TAC[INT_LT_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s INTER s':real^N->bool`; `s:real^N->bool`]
    FACE_OF_AFF_DIM_LT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(sigma:real^N->bool) face_of (s INTER s')` ASSUME_TAC THENL
   [MATCH_MP_TAC FACE_OF_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[INTER_SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`sigma:real^N->bool`; `s INTER s':real^N->bool`]
    FACE_OF_AFF_DIM_LT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[CONVEX_INTER] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `aff_dim (s INTER s':real^N->bool) < &3` THEN
  ASM_REWRITE_TAC[] THEN INT_ARITH_TAC);;

let MOI_LGB2_CELLS_DIFFER = prove
 (`!(c:(real^N->bool)->bool) tt u (h:real^N->real^3) h' L g Q y x1 x2 sigma
    rho1 rho2 e r r' s s'.
     moi_lgb2_ctx c tt u h h' L g Q y x1 x2 sigma rho1 rho2 /\
     aff_dim sigma = &2 /\ e IN L /\ aff_dim e = &1 /\ IMAGE g e SUBSET sigma /\
     y IN IMAGE g e /\
     r IN L /\ r' IN L /\ ~(r = r') /\ aff_dim r = &2 /\ aff_dim r' = &2 /\
     e SUBSET r /\ e SUBSET r' /\
     s IN tt /\ s' IN tt /\ aff_dim s = &3 /\
     IMAGE g r SUBSET s /\ IMAGE g r' SUBSET s'
     ==> ~(s = s')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MAP_EVERY ASSUME_TAC o CONJUNCTS o
    GEN_REWRITE_RULE I [moi_lgb2_ctx]) THEN
  UNDISCH_TAC `moi_lgb_tgeneric tt L (g:real^2->real^N) Q` THEN
  REWRITE_TAC[moi_lgb_tgeneric] THEN
  DISCH_THEN(MP_TAC o SPECL [`e:real^2->bool`; `r:real^2->bool`;
                             `r':real^2->bool`; `sigma:real^N->bool`] o
    CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `s:real^N->bool`) THEN
  ASM_REWRITE_TAC[UNION_SUBSET] THEN ASM_MESON_TAC[]);;

let MOI_LGB2_WING_OFF = prove
 (`!(c:(real^N->bool)->bool) tt u (h:real^N->real^3) h' L g Q y x1 x2 sigma
    rho1 rho2 p q w x.
     moi_lgb2_ctx c tt u h h' L g Q y x1 x2 sigma rho1 rho2 /\
     aff_dim sigma <= &2 /\
     convex hull {p,q,w} IN L /\ aff_dim(convex hull {p,q,w}) = &2 /\
     IMAGE g (convex hull {p,q}) SUBSET sigma /\
     x IN convex hull {p,q,w} /\ g x = y /\
     IMAGE g (convex hull {p,q,w}) SUBSET u
     ==> ~(h(g w) IN IMAGE h sigma)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB2_CTX_BASIC) THEN
  FIRST_X_ASSUM(MAP_EVERY ASSUME_TAC o CONJUNCTS o
    GEN_REWRITE_RULE I [moi_lgb2_ctx]) THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(g:real^2->real^N) w IN sigma` ASSUME_TAC THENL
   [SUBGOAL_THEN `(g:real^2->real^N) w = z` (fun th -> ASM_REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `p':real^N`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (g:real^2->real^N) (convex hull {p,q,w}) SUBSET u` THEN
      MATCH_MP_TAC(SET_RULE `!(f:real^2->real^N) a b x.
        x IN a ==> IMAGE f a SUBSET b ==> f x IN b`) THEN
      MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `convex hull {p:real^2,q,w} IN L`) o
    check (fun th -> can (find_term ((=) `z':real^2`)) (concl th) &&
                     is_forall (concl th) &&
                     can (find_term ((=) `L:(real^2->bool)->bool`)) (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `lg:real^2->real^N` (X_CHOOSE_THEN `bg:real^N`
      STRIP_ASSUME_TAC)) (K ALL_TAC)) THEN
  SUBGOAL_THEN `IMAGE (g:real^2->real^N) (convex hull {p,q,w}) SUBSET sigma`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:real^2->real^N`; `lg:real^2->real^N`; `bg:real^N`;
                   `{p:real^2,q,w}`] MOI_LGA_HULL_IMAGE) THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC HULL_MINIMAL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN
    UNDISCH_TAC `IMAGE (g:real^2->real^N) (convex hull {p,q}) SUBSET sigma` THEN
    MATCH_MP_TAC(SET_RULE `!(f:real^2->real^N) a b x.
      x IN a ==> IMAGE f a SUBSET b ==> f x IN b`) THEN
    MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_lgb_tgeneric tt L (g:real^2->real^N) Q` THEN
  REWRITE_TAC[moi_lgb_tgeneric] THEN
  DISCH_THEN(MP_TAC o SPECL [`convex hull {p:real^2,q,w}`; `sigma:real^N->bool`] o
    CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE] THEN
  EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[]);;

let MOI_LGB2_HULL4_IMAGE = prove
 (`!(h:real^N->real^3) (s:real^N->bool) A B D E.
     s = convex hull {A,B,D,E} /\
     (?l b. linear l /\ !z. z IN s ==> h z = l z + b)
     ==> IMAGE h s = convex hull {h A, h B, h D, h E} /\
         IMAGE h (convex hull {A,B,D}) = convex hull {h A, h B, h D}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC
    (X_CHOOSE_THEN `l:real^N->real^3` (X_CHOOSE_THEN `b:real^3`
      STRIP_ASSUME_TAC))) THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`h:real^N->real^3`; `l:real^N->real^3`; `b:real^3`;
                   `{A:real^N,B,D,E}`] MOI_LGA_HULL_IMAGE) THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES];
    MP_TAC(ISPECL [`h:real^N->real^3`; `l:real^N->real^3`; `b:real^3`;
                   `{A:real^N,B,D}`] MOI_LGA_HULL_IMAGE) THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC(SET_RULE `!a b (x:real^N). a SUBSET b /\ x IN a ==> x IN b`) THEN
    EXISTS_TAC `convex hull {A:real^N,B,D}` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HULL_MONO THEN SET_TAC[]]);;

let MOI_LGB2_SIMPLEX3_4 = prove
 (`!A B D E:real^N.
     ~affine_dependent {A,B,D,E} /\ ~(A = B) /\ ~(A = D) /\ ~(B = D) /\
     ~(E = A) /\ ~(E = B) /\ ~(E = D)
     ==> &3 simplex (convex hull {A,B,D,E})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[simplex] THEN
  EXISTS_TAC `{A:real^N,B,D,E}` THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC INT_REDUCE_CONV);;

let MOI_LGB2_WALL_SIDES = prove
 (`!(tt:(real^N->bool)->bool) (u:real^N->bool) (h:real^N->real^3) A B D s s'
    W W'.
     simplicial_complex tt /\ convex hull {A,B,D} IN tt /\
     ~affine_dependent {A,B,D} /\ ~(A = B) /\ ~(A = D) /\ ~(B = D) /\
     s IN tt /\ s' IN tt /\ ~(s = s') /\ aff_dim s = &3 /\ aff_dim s' = &3 /\
     convex hull {A,B,D} face_of s /\ convex hull {A,B,D} face_of s' /\
     s SUBSET u /\ s' SUBSET u /\
     (!p p'. p IN u /\ p' IN u /\ h p = h p' ==> p = p') /\
     (?l b. linear l /\ !z. z IN s ==> h z = l z + b) /\
     (?l b. linear l /\ !z. z IN s' ==> h z = l z + b) /\
     W IN IMAGE h s /\ ~(W IN IMAGE h (convex hull {A,B,D})) /\
     W' IN IMAGE h s' /\ ~(W' IN IMAGE h (convex hull {A,B,D}))
     ==> det(vector[h B - h A; h D - h A; W - h A]) *
         det(vector[h B - h A; h D - h A; W' - h A]) < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `s:real^N->bool`; `s':real^N->bool`;
                 `convex hull {A:real^N,B,D}`] MOI_LGB2_CELLS_INTER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_AFFINE_INDEPENDENT] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC INT_REDUCE_CONV;
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `A:real^N`; `B:real^N`; `D:real^N`;
                 `s:real^N->bool`] MOI_LGB2_TET_ON_TRI) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[FACE_OF_IMP_SUBSET]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `E:real^N` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))))) THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `A:real^N`; `B:real^N`; `D:real^N`;
                 `s':real^N->bool`] MOI_LGB2_TET_ON_TRI) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[FACE_OF_IMP_SUBSET]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `E':real^N` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))))) THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`h:real^N->real^3`; `convex hull {A:real^N,B,D,E}`; `A:real^N`;
                 `B:real^N`; `D:real^N`; `E:real^N`] MOI_LGB2_HULL4_IMAGE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC [`l:real^N->real^3`; `b:real^3`] THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`h:real^N->real^3`; `convex hull {A:real^N,B,D,E'}`; `A:real^N`;
                 `B:real^N`; `D:real^N`; `E':real^N`] MOI_LGB2_HULL4_IMAGE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC [`l':real^N->real^3`; `b':real^3`] THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  SUBGOAL_THEN `~(E:real^N = E')` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~(convex hull {A:real^N,B,D,E} = convex hull {A,B,D,E'})` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(E:real^N) IN u /\ (E':real^N) IN u` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    MATCH_MP_TAC(SET_RULE `!a b (x:real^N). a SUBSET b /\ x IN a ==> x IN b`) THENL
     [EXISTS_TAC `convex hull {A:real^N,B,D,E}`;
      EXISTS_TAC `convex hull {A:real^N,B,D,E'}`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((h:real^N->real^3) E = h E')` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(E:real^N = E')` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `p':real^N`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `aff_dim(convex hull {(h:real^N->real^3) A,h B,h D,h E}) = &3 /\
    aff_dim(convex hull {(h:real^N->real^3) A,h B,h D,h E'}) = &3`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (h:real^N->real^3) (convex hull {A,B,D,E}) =
                   convex hull {h A,h B,h D,h E}` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC AFF_DIM_SIMPLEX THEN MATCH_MP_TAC MOI_LGA_SIMPLEX_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`l:real^N->real^3`; `b:real^3`];
      UNDISCH_TAC `IMAGE (h:real^N->real^3) (convex hull {A,B,D,E'}) =
                   convex hull {h A,h B,h D,h E'}` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC AFF_DIM_SIMPLEX THEN MATCH_MP_TAC MOI_LGA_SIMPLEX_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`l':real^N->real^3`; `b':real^3`]] THEN
    ASM_SIMP_TAC[MOI_LGB2_SIMPLEX3_4] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `p':real^N`)) (concl th))) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `convex hull {(h:real^N->real^3) A,h B,h D,h E} INTER
    convex hull {h A,h B,h D,h E'} = convex hull {h A,h B,h D}`
  ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (h:real^N->real^3) (convex hull {A,B,D,E}) =
                 convex hull {h A,h B,h D,h E}` THEN
    UNDISCH_TAC `IMAGE (h:real^N->real^3) (convex hull {A,B,D,E'}) =
                 convex hull {h A,h B,h D,h E'}` THEN
    UNDISCH_TAC `IMAGE (h:real^N->real^3) (convex hull {A,B,D}) =
                 convex hull {h A,h B,h D}` THEN
    REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
    UNDISCH_TAC `convex hull {A,B,D,E} INTER convex hull {A,B,D,E'} =
                 convex hull {A:real^N,B,D}` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `!p p'. p IN u /\ p' IN u /\ (h:real^N->real^3) p = h p'
                        ==> p = p'` THEN
    UNDISCH_TAC `convex hull {A:real^N,B,D,E} SUBSET u` THEN
    UNDISCH_TAC `convex hull {A:real^N,B,D,E'} SUBSET u` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(h:real^N->real^3) A`; `(h:real^N->real^3) B`;
                 `(h:real^N->real^3) D`; `(h:real^N->real^3) E`;
                 `(h:real^N->real^3) E'`] MOI_LGB2_TET_OPP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(h:real^N->real^3) A`; `(h:real^N->real^3) B`;
                 `(h:real^N->real^3) D`; `(h:real^N->real^3) E`; `W:real^3`]
    MOI_LGB2_WING_SIDE) THEN
  MP_TAC(ISPECL [`(h:real^N->real^3) A`; `(h:real^N->real^3) B`;
                 `(h:real^N->real^3) D`; `(h:real^N->real^3) E'`; `W':real^3`]
    MOI_LGB2_WING_SIDE) THEN
  SUBGOAL_THEN
   `W IN convex hull {(h:real^N->real^3) A,h B,h D,h E} /\
    W' IN convex hull {(h:real^N->real^3) A,h B,h D,h E'} /\
    ~(W IN convex hull {(h:real^N->real^3) A,h B,h D}) /\
    ~(W' IN convex hull {(h:real^N->real^3) A,h B,h D})`
  (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `IMAGE (h:real^N->real^3) (convex hull {A,B,D,E}) =
                 convex hull {h A,h B,h D,h E}` THEN
    UNDISCH_TAC `IMAGE (h:real^N->real^3) (convex hull {A,B,D,E'}) =
                 convex hull {h A,h B,h D,h E'}` THEN
    UNDISCH_TAC `IMAGE (h:real^N->real^3) (convex hull {A,B,D}) =
                 convex hull {h A,h B,h D}` THEN
    REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `dA = det(vector[(h:real^N->real^3) B - h A; h D - h A; h E - h A])` THEN
  ABBREV_TAC `dB = det(vector[(h:real^N->real^3) B - h A; h D - h A; h E' - h A])` THEN
  SUBGOAL_THEN `(e1 * dA) * (e2 * dB) = (e1 * e2) * (dA * dB)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `x * y < &0 <=> &0 < x * --y`] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_MUL] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_LGB2_PLANE_IN = prove
 (`!P Q W z:real^3.
     z IN affine hull {P,Q,W} ==> ((Q - P) cross (W - P)) dot (z - P) = &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[AFFINE_HULL_3; IN_ELIM_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(u % P + v % Q + w % W) - P:real^3 = v % (Q - P) + w % (W - P)`
  SUBST1_TAC THENL
   [UNDISCH_TAC `u + v + w = &1` THEN
    REWRITE_TAC[REAL_ARITH `u + v + w = &1 <=> u = &1 - v - w`] THEN
    DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[DOT_RADD; DOT_RMUL; DOT_CROSS_SELF] THEN REAL_ARITH_TAC);;

let MOI_LGB2_AFF_COMB2 = prove
 (`!(f:real^M->real^N) l b (S:real^M->bool) p q t.
     linear l /\ (!z. z IN S ==> f z = l z + b) /\ p IN S /\ q IN S /\
     (&1 - t) % p + t % q IN S
     ==> f((&1 - t) % p + t % q) = (&1 - t) % f p + t % f q`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL] THEN
  VECTOR_ARITH_TAC);;

let MOI_LGB2_LINE_TRANSV = prove
 (`!(Phi:real^2->real^3) l1 b1 l2 b2 p1 q1 p2 q2 mu1 mu2.
     linear l1 /\ (!z. z IN convex hull {p1,q1} ==> Phi z = l1 z + b1) /\
     linear l2 /\ (!z. z IN convex hull {p2,q2} ==> Phi z = l2 z + b2) /\
     Phi((&1 - mu1) % p1 + mu1 % q1) = Phi((&1 - mu2) % p2 + mu2 % q2) /\
     &0 <= mu1 /\ mu1 <= &1 /\ &0 <= mu2 /\ mu2 <= &1 /\
     ~(Phi q1 - Phi p1 = vec 0) /\ ~(Phi q2 - Phi p2 = vec 0) /\
     (Phi q1 - Phi p1) cross (Phi q2 - Phi p2) = vec 0
     ==> IMAGE Phi (convex hull {p1,q1}) SUBSET
         affine hull (IMAGE Phi (convex hull {p2,q2}))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Phi:real^2->real^3`; `l2:real^2->real^3`; `b2:real^3`;
                 `{p2:real^2,q2}`] MOI_LGA_HULL_IMAGE) THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[AFFINE_HULL_CONVEX_HULL] THEN
  MP_TAC(ISPECL [`Phi (q2:real^2) - Phi p2:real^3`; `Phi (q1:real^2) - Phi p1:real^3`]
    MOI_LGB2_CROSS_PARALLEL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[CROSS_SKEW] THEN
    ASM_REWRITE_TAC[VECTOR_NEG_0];
    DISCH_THEN(X_CHOOSE_TAC `k:real`)] THEN
  SUBGOAL_THEN
   `(Phi:real^2->real^3)((&1 - mu1) % p1 + mu1 % q1) =
      (&1 - mu1) % Phi p1 + mu1 % Phi q1 /\
    (Phi:real^2->real^3)((&1 - mu2) % p2 + mu2 % q2) =
      (&1 - mu2) % Phi p2 + mu2 % Phi q2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_LGB2_AFF_COMB2 THENL
     [MAP_EVERY EXISTS_TAC [`l1:real^2->real^3`; `b1:real^3`;
                            `convex hull {p1:real^2,q1}`] THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[HULL_INC; IN_INSERT] THEN
      REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; IN_SEGMENT] THEN
      EXISTS_TAC `mu1:real` THEN ASM_REWRITE_TAC[];
      MAP_EVERY EXISTS_TAC [`l2:real^2->real^3`; `b2:real^3`;
                            `convex hull {p2:real^2,q2}`] THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[HULL_INC; IN_INSERT] THEN
      REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; IN_SEGMENT] THEN
      EXISTS_TAC `mu2:real` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^2` THEN
  REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; IN_SEGMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `tau:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `(Phi:real^2->real^3) z = (&1 - tau) % Phi p1 + tau % Phi q1`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_LGB2_AFF_COMB2 THEN
    MAP_EVERY EXISTS_TAC [`l1:real^2->real^3`; `b1:real^3`;
                          `convex hull {p1:real^2,q1}`] THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[HULL_INC; IN_INSERT] THEN
    REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; IN_SEGMENT] THEN
    EXISTS_TAC `tau:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[AFFINE_HULL_2; IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC
   [`&1 - mu2 - (tau - mu1) * k`; `mu2 + (tau - mu1) * k`] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `(Phi:real^2->real^3)((&1 - mu1) % p1 + mu1 % q1) =
               Phi((&1 - mu2) % p2 + mu2 % q2)` THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(Phi:real^2->real^3) q1 - Phi p1 = k % (Phi q2 - Phi p2)` THEN
  REWRITE_TAC[VECTOR_ARITH `q - p:real^3 = k % x <=> q = p + k % x`] THEN
  DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC);;

let MOI_LGB2_TRI_NEQ = prove
 (`!p q w w':real^N.
     ~affine_dependent {p,q,w} /\ ~affine_dependent {p,q,w'} /\
     ~(w = p) /\ ~(w = q) /\ ~(w = w')
     ==> ~(convex hull {p,q,w} = convex hull {p,q,w'})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{p:real^N,q,w}`; `w:real^N`]
    EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
  MP_TAC(ISPECL [`{p:real^N,q,w'}`; `w:real^N`]
    EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY]);;

let MOI_LGB2_FLIP_TAC : thm_tactic =
  fun th -> if is_eq(concl th) && is_var(lhs(concl th))
            then ASSUME_TAC(SYM th) else ASSUME_TAC th;;

let MOI_LGB2_CTX_CELL = prove
 (`!(c:(real^N->bool)->bool) tt u (h:real^N->real^3) h' L g Q y x1 x2 sigma
    rho1 rho2 s.
     moi_lgb2_ctx c tt u h h' L g Q y x1 x2 sigma rho1 rho2 /\
     s IN tt /\ y IN s
     ==> s SUBSET u /\ sigma face_of s /\
         (?l b. linear l /\ !z. z IN s ==> h z = l z + b)`,
  REWRITE_TAC[moi_lgb2_ctx] THEN MESON_TAC[]);;

let MOI_LGB2_EDGE_SHEET_W = prove
 (`!(c:(real^N->bool)->bool) tt u (h:real^N->real^3) h' L g Q y x1 x2 sigma
    rho1 rho2 A B D.
     moi_lgb2_ctx c tt u h h' L g Q y x1 x2 sigma rho1 rho2 /\
     aff_dim sigma = &2 /\ aff_dim rho1 = &1 /\ ~(y IN complex_boundary c) /\
     sigma = convex hull {A,B,D} /\ ~affine_dependent {A,B,D} /\
     ~(A = B) /\ ~(A = D) /\ ~(B = D)
     ==> ?p q w w' mu d la ba lb bb.
           rho1 = convex hull {p,q} /\ ~(p = q) /\ &0 < mu /\ mu < &1 /\
           (&1 - mu) % p + mu % q = x1 /\
           convex hull {p,q,w} IN L /\ convex hull {p,q,w'} IN L /\
           ~affine_dependent {p,q,w} /\ ~affine_dependent {p,q,w'} /\
           ~(p = w) /\ ~(q = w) /\ ~(p = w') /\ ~(q = w') /\
           linear la /\ (!z. z IN convex hull {p,q,w} ==> h(g z) = la z + ba) /\
           linear lb /\ (!z. z IN convex hull {p,q,w'} ==> h(g z) = lb z + bb) /\
           (!z z'. z IN convex hull {p,q,w} /\ z' IN convex hull {p,q,w} /\
                   h(g z) = h(g z') ==> z = z') /\
           (!z z'. z IN convex hull {p,q,w'} /\ z' IN convex hull {p,q,w'} /\
                   h(g z) = h(g z') ==> z = z') /\
           &0 < d /\ ball(x1,d) SUBSET std_triangle /\
           (!z. z IN ball(x1,d)
                ==> z IN convex hull {p,q,w} \/ z IN convex hull {p,q,w'}) /\
           IMAGE g (ball(x1,d)) SUBSET u /\
           (!z z'. z IN ball(x1,d) /\ z' IN ball(x1,d) /\ g z = g z' ==> z = z') /\
           (((h B - h A) cross (h D - h A)) dot (h(g w) - h(g p))) *
           (((h B - h A) cross (h D - h A)) dot (h(g w') - h(g p))) < &0`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY MOI_LGB2_FLIP_TAC o CONJUNCTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB2_CTX_BASIC) THEN
  FIRST_ASSUM(MAP_EVERY ASSUME_TAC o CONJUNCTS o
    GEN_REWRITE_RULE I [moi_lgb2_ctx]) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:real^2->real^N`; `x1:real^2`]
    MOI_LGB2_SD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `dd:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `rho1:real^2->bool`; `x1:real^2`]
    MOI_LGB2_SHEET_EDGE2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^2` (X_CHOOSE_THEN `q:real^2`
    (X_CHOOSE_THEN `w:real^2` (X_CHOOSE_THEN `w':real^2`
      (X_CHOOSE_THEN `mu:real` (MAP_EVERY MOI_LGB2_FLIP_TAC o CONJUNCTS)))))) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC o
    check (is_exists o concl)) THEN
  SUBGOAL_THEN `(x1:real^2) IN convex hull {p,q,w} /\ x1 IN convex hull {p,q,w'}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN
    CONJ_TAC THEN MAP_EVERY EXISTS_TAC [`&1 - mu`; `mu:real`; `&0`] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; REAL_ADD_RID] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                 `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `y:real^N`; `x1:real^2`; `x2:real^2`; `sigma:real^N->bool`;
                 `rho1:real^2->bool`; `rho2:real^2->bool`;
                 `convex hull {p:real^2,q,w}`; `x1:real^2`] MOI_LGB2_CTX_PHI) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `la:real^2->real^3` (X_CHOOSE_THEN `ba:real^3`
      STRIP_ASSUME_TAC))
    (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `s:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          ASSUME_TAC))))))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                 `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `y:real^N`; `x1:real^2`; `x2:real^2`; `sigma:real^N->bool`;
                 `rho1:real^2->bool`; `rho2:real^2->bool`;
                 `convex hull {p:real^2,q,w'}`; `x1:real^2`] MOI_LGB2_CTX_PHI) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `lb:real^2->real^3` (X_CHOOSE_THEN `bb:real^3`
      STRIP_ASSUME_TAC))
    (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `s':real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          ASSUME_TAC))))))) THEN
  SUBGOAL_THEN `(y:real^N) IN s /\ (y:real^N) IN s'` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (g:real^2->real^N) (convex hull {p,q,w}) SUBSET s`;
      UNDISCH_TAC `IMAGE (g:real^2->real^N) (convex hull {p,q,w'}) SUBSET s'`] THEN
    MATCH_MP_TAC(SET_RULE `!(f:real^2->real^N) a b x z.
      x IN a /\ f x = z ==> IMAGE f a SUBSET b ==> z IN b`) THEN
    EXISTS_TAC `x1:real^2` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                 `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `y:real^N`; `x1:real^2`; `x2:real^2`; `sigma:real^N->bool`;
                 `rho1:real^2->bool`; `rho2:real^2->bool`; `s:real^N->bool`]
    MOI_LGB2_CTX_CELL) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                 `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `y:real^N`; `x1:real^2`; `x2:real^2`; `sigma:real^N->bool`;
                 `rho1:real^2->bool`; `rho2:real^2->bool`; `s':real^N->bool`]
    MOI_LGB2_CTX_CELL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `aff_dim(convex hull {p:real^2,q,w}) = &2 /\
                aff_dim(convex hull {p:real^2,q,w'}) = &2`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_AFFINE_INDEPENDENT] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(s:real^N->bool) = &3 /\ aff_dim(s':real^N->bool) = &3`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_LGB2_CELL3 THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                          `u:real^N->bool`; `h:real^N->real^3`;
                          `h':real^3->real^N`; `L:(real^2->bool)->bool`;
                          `g:real^2->real^N`; `Q:real^N->bool`; `y:real^N`;
                          `x1:real^2`; `x2:real^2`; `sigma:real^N->bool`;
                          `rho1:real^2->bool`; `rho2:real^2->bool`] THENL
     [MAP_EVERY EXISTS_TAC [`convex hull {p:real^2,q,w}`; `x1:real^2`];
      MAP_EVERY EXISTS_TAC [`convex hull {p:real^2,q,w'}`; `x1:real^2`]] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `rho1 SUBSET convex hull {p:real^2,q,w} /\
                rho1 SUBSET convex hull {p:real^2,q,w'}` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `convex hull {p:real^2,q} = rho1` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN CONJ_TAC THEN
    MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(convex hull {p:real^2,q,w} = convex hull {p,q,w'})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LGB2_TRI_NEQ THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(s:real^N->bool = s')` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LGB2_CELLS_DIFFER THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                          `u:real^N->bool`; `h:real^N->real^3`;
                          `h':real^3->real^N`; `L:(real^2->bool)->bool`;
                          `g:real^2->real^N`; `Q:real^N->bool`; `y:real^N`;
                          `x1:real^2`; `x2:real^2`; `sigma:real^N->bool`;
                          `rho1:real^2->bool`; `rho2:real^2->bool`;
                          `rho1:real^2->bool`; `convex hull {p:real^2,q,w}`;
                          `convex hull {p:real^2,q,w'}`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^2->real^N) p IN sigma` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (g:real^2->real^N) rho1 SUBSET sigma` THEN
    UNDISCH_TAC `convex hull {p:real^2,q} = rho1` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(SET_RULE `!(f:real^2->real^N) a b x.
      x IN a ==> IMAGE f a SUBSET b ==> f x IN b`) THEN
    MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(h:real^N->real^3)((g:real^2->real^N) w) IN IMAGE h s /\
    (h:real^N->real^3)((g:real^2->real^N) w') IN IMAGE h s'`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THENL
     [UNDISCH_TAC `IMAGE (g:real^2->real^N) (convex hull {p,q,w}) SUBSET s`;
      UNDISCH_TAC `IMAGE (g:real^2->real^N) (convex hull {p,q,w'}) SUBSET s'`] THEN
    MATCH_MP_TAC(SET_RULE `!(f:real^2->real^N) a b x.
      x IN a ==> IMAGE f a SUBSET b ==> f x IN b`) THEN
    MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~((h:real^N->real^3)((g:real^2->real^N) w) IN IMAGE h sigma) /\
    ~((h:real^N->real^3)((g:real^2->real^N) w') IN IMAGE h sigma)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_LGB2_WING_OFF THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                          `u:real^N->bool`; `h':real^3->real^N`;
                          `L:(real^2->bool)->bool`; `Q:real^N->bool`; `y:real^N`;
                          `x1:real^2`; `x2:real^2`;
                          `rho1:real^2->bool`; `rho2:real^2->bool`;
                          `p:real^2`; `q:real^2`] THEN
    ASM_REWRITE_TAC[INT_LE_REFL] THENL
     [EXISTS_TAC `x1:real^2`; EXISTS_TAC `x1:real^2`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `u:real^N->bool`; `h:real^N->real^3`;
                 `A:real^N`; `B:real^N`; `D:real^N`; `s:real^N->bool`;
                 `s':real^N->bool`; `(h:real^N->real^3)((g:real^2->real^N) w)`;
                 `(h:real^N->real^3)((g:real^2->real^N) w')`]
    MOI_LGB2_WALL_SIDES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (h:real^N->real^3) sigma = convex hull {h A,h B,h D}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h:real^N->real^3`; `l:real^N->real^3`; `b:real^3`;
                   `{A:real^N,B,D}`] MOI_LGA_HULL_IMAGE) THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!W:real^3. ((h B - h A) cross (h D - h A)) dot
               (W - (h:real^N->real^3)((g:real^2->real^N) p)) =
               det(vector[h B - h A; h D - h A; W - h A])`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM MOI_LGB2_NU_DET] THEN
    SUBGOAL_THEN
     `!n:real^3. n dot (W - (h:real^N->real^3)((g:real^2->real^N) p)) =
                 n dot (W - h A) - n dot (h(g p) - h A)`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN REWRITE_TAC[GSYM DOT_RSUB] THEN AP_TERM_TAC THEN
      VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `a - b = a <=> b = &0`] THEN
    MATCH_MP_TAC MOI_LGB2_PLANE_IN THEN
    MATCH_MP_TAC(SET_RULE `!a b (x:real^3). a SUBSET b /\ x IN a ==> x IN b`) THEN
    EXISTS_TAC `convex hull {(h:real^N->real^3) A,h B,h D}` THEN
    REWRITE_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL] THEN
    UNDISCH_TAC `IMAGE (h:real^N->real^3) sigma = convex hull {h A,h B,h D}` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`p:real^2`; `q:real^2`; `w:real^2`; `w':real^2`;
                        `mu:real`; `min d1 dd:real`; `la:real^2->real^3`;
                        `ba:real^3`; `lb:real^2->real^3`; `bb:real^3`] THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  SUBGOAL_THEN `ball(x1:real^2,min d1 dd) SUBSET ball(x1,d1) /\
                ball(x1:real^2,min d1 dd) SUBSET ball(x1,dd)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    ASM SET_TAC[];
    UNDISCH_TAC `IMAGE (g:real^2->real^N) (convex hull {p,q,w}) SUBSET u` THEN
    UNDISCH_TAC `IMAGE (g:real^2->real^N) (convex hull {p,q,w'}) SUBSET u` THEN
    UNDISCH_TAC `!z:real^2. z IN ball(x1,d1)
                 ==> z IN convex hull {p,q,w} \/ z IN convex hull {p,q,w'}` THEN
    UNDISCH_TAC `ball(x1:real^2,min d1 dd) SUBSET ball(x1,d1)` THEN
    SET_TAC[];
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `dd:real`)) (concl th) && is_forall (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ball(x1:real^2,min d1 dd) SUBSET ball(x1,dd)` THEN
    UNDISCH_TAC `ball(x1:real^2,min d1 dd) SUBSET ball(x1,d1)` THEN
    UNDISCH_TAC `ball(x1:real^2,d1) SUBSET std_triangle` THEN
    UNDISCH_TAC `(z:real^2) IN ball(x1,min d1 dd)` THEN
    UNDISCH_TAC `(z':real^2) IN ball(x1,min d1 dd)` THEN
    REWRITE_TAC[SUBSET; IN_BALL] THEN MESON_TAC[DIST_SYM]]);;

let MOI_LGB2_DOT_SUB3 = prove
 (`!n q p a:real^N. n dot (q - p) = n dot (q - a) - n dot (p - a)`,
  REWRITE_TAC[DOT_RSUB] THEN REAL_ARITH_TAC);;

let MOI_LGB2_TRI_RELINT_INT = prove
 (`!(L:(real^2->bool)->bool) t z.
     simplicial_complex L /\ UNIONS L = std_triangle /\ t IN L /\ aff_dim t = &2 /\
     z IN relative_interior t
     ==> ~(z IN relative_frontier std_triangle)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `std_triangle`; `\x:real^2. x`;
                 `\x:real^2. x`; `t:real^2->bool`] MOI_FM3_DISK_TRIANGLE) THEN
  ASM_REWRITE_TAC[MOI_LTD_STD_TRIANGLE_SIMPLEX; HOMEOMORPHISM_ID; IMAGE_ID] THEN
  UNDISCH_TAC `(z:real^2) IN relative_frontier std_triangle` THEN
  UNDISCH_TAC `(z:real^2) IN relative_interior t` THEN
  REWRITE_TAC[relative_frontier] THEN SET_TAC[]);;

let MOI_LGB2_EDGE_SHEET_B = prove
 (`!(c:(real^N->bool)->bool) tt u (h:real^N->real^3) h' L g Q y x1 x2 sigma
    rho1 rho2.
     moi_lgb2_ctx c tt u h h' L g Q y x1 x2 sigma rho1 rho2 /\
     aff_dim sigma = &2 /\ aff_dim rho1 = &1 /\ y IN complex_boundary c
     ==> ?p q w mu d la ba.
           rho1 = convex hull {p,q} /\ ~(p = q) /\ &0 < mu /\ mu < &1 /\
           (&1 - mu) % p + mu % q = x1 /\
           convex hull {p,q,w} IN L /\ ~affine_dependent {p,q,w} /\
           ~(p = w) /\ ~(q = w) /\
           linear la /\ (!z. z IN convex hull {p,q,w} ==> h(g z) = la z + ba) /\
           (!z z'. z IN convex hull {p,q,w} /\ z' IN convex hull {p,q,w} /\
                   h(g z) = h(g z') ==> z = z') /\
           &0 < d /\
           (!z. z IN std_triangle /\ dist(z,x1) < d ==> z IN convex hull {p,q,w}) /\
           IMAGE g (convex hull {p,q,w}) SUBSET u /\
           (!z z'. z IN std_triangle /\ z' IN std_triangle /\
                   dist(z,x1) < d /\ dist(z',x1) < d /\ g z = g z' ==> z = z') /\
           (h(g p))$3 = &0 /\ (h(g q))$3 = &0 /\ &0 < (h(g w))$3`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY MOI_LGB2_FLIP_TAC o CONJUNCTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB2_CTX_BASIC) THEN
  FIRST_ASSUM(MAP_EVERY ASSUME_TAC o CONJUNCTS o
    GEN_REWRITE_RULE I [moi_lgb2_ctx]) THEN
  SUBGOAL_THEN `(sigma:real^N->bool) SUBSET complex_boundary c` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (h:real^N->real^3) u = ball(vec 0,&1) INTER {z:real^3 | &0 <= z$3} /\
    IMAGE h (u INTER complex_boundary c) = IMAGE h u INTER {z:real^3 | z$3 = &0}`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `homeomorphism (u,IMAGE h u) ((h:real^N->real^3),h')`
  ASSUME_TAC THENL [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`] MOI_LGB2_CB_IFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "cbiff") THEN
  SUBGOAL_THEN `(rho1:real^2->bool) SUBSET relative_frontier std_triangle`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^2) IN std_triangle` ASSUME_TAC THENL
     [UNDISCH_TAC `UNIONS L = std_triangle` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:real^2->real^N`; `z:real^2`]
      MOI_LGB2_SD_FACTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:real^2->real^N`; `x1:real^2`]
    MOI_LGB2_SD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `dd:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `rho1:real^2->bool`; `x1:real^2`]
    MOI_LGB2_SHEET_EDGE1) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^2` (X_CHOOSE_THEN `q:real^2`
    (X_CHOOSE_THEN `w:real^2` (X_CHOOSE_THEN `mu:real`
      (MAP_EVERY MOI_LGB2_FLIP_TAC o CONJUNCTS))))) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC o
    check (is_exists o concl)) THEN
  SUBGOAL_THEN `(x1:real^2) IN convex hull {p,q,w}` ASSUME_TAC THENL
   [REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`&1 - mu`; `mu:real`; `&0`] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; REAL_ADD_RID] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                 `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `y:real^N`; `x1:real^2`; `x2:real^2`; `sigma:real^N->bool`;
                 `rho1:real^2->bool`; `rho2:real^2->bool`;
                 `convex hull {p:real^2,q,w}`; `x1:real^2`] MOI_LGB2_CTX_PHI) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `la:real^2->real^3` (X_CHOOSE_THEN `ba:real^3`
      STRIP_ASSUME_TAC))
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  SUBGOAL_THEN `(p:real^2) IN rho1 /\ (q:real^2) IN rho1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `convex hull {p:real^2,q} = rho1` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP_TAC[HULL_INC; IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^2->real^N) p IN sigma /\ (g:real^2->real^N) q IN sigma`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `((h:real^N->real^3)((g:real^2->real^N) p))$3 = &0 /\
                ((h:real^N->real^3)((g:real^2->real^N) q))$3 = &0 /\
                ((h:real^N->real^3) y)$3 = &0`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "cbiff" (MP_TAC o SPEC `(g:real^2->real^N) p`);
      USE_THEN "cbiff" (MP_TAC o SPEC `(g:real^2->real^N) q`);
      USE_THEN "cbiff" (MP_TAC o SPEC `y:real^N`)] THEN
    (ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^2) IN convex hull {p,q,w}` ASSUME_TAC THENL
   [SIMP_TAC[HULL_INC; IN_INSERT]; ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^2->real^N) w IN u` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= ((h:real^N->real^3)((g:real^2->real^N) w))$3` ASSUME_TAC THENL
   [SUBGOAL_THEN `(h:real^N->real^3)((g:real^2->real^N) w) IN IMAGE h u` MP_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(((h:real^N->real^3)((g:real^2->real^N) w))$3 = &0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `~(relative_interior (convex hull {p:real^2,q,w}) = {})` MP_TAC THENL
     [SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY; CONVEX_CONVEX_HULL] THEN
      REWRITE_TAC[CONVEX_HULL_EQ_EMPTY; NOT_INSERT_EMPTY];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `z:real^2` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
    SUBGOAL_THEN `(z:real^2) IN convex hull {p,q,w}` ASSUME_TAC THENL
     [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^2) IN std_triangle` ASSUME_TAC THENL
     [UNDISCH_TAC `UNIONS L = std_triangle` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `convex hull {p:real^2,q,w}` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `convex hull {p:real^2,q,w}`;
                   `z:real^2`] MOI_LGB2_TRI_RELINT_INT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_AFFINE_INDEPENDENT] THEN
      SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
      ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC INT_REDUCE_CONV;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:real^2->real^N`; `z:real^2`]
      MOI_LGB2_SD_FACTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    SUBGOAL_THEN `(g:real^2->real^N) z IN u` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "cbiff" (fun th -> REWRITE_TAC[MATCH_MP
      (SPEC `(g:real^2->real^N) z` th) (ASSUME `(g:real^2->real^N) z IN u`)]) THEN
    MP_TAC(BETA_RULE(ISPECL [`\z:real^2. (h:real^N->real^3)((g:real^2->real^N) z)`;
      `la:real^2->real^3`; `ba:real^3`; `p:real^2`; `q:real^2`;
      `w:real^2`; `x1:real^2`; `z:real^2`] MOI_LGB2_TRI_PARAM)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `mu:real` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real` (X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                    VECTOR_SUB_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`p:real^2`; `q:real^2`; `w:real^2`; `mu:real`;
                        `min d1 dd:real`; `la:real^2->real^3`; `ba:real^3`] THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `dd:real`)) (concl th) && is_forall (concl th))) THEN
    ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC]);;

let MOI_LGB2_BD_ETA = prove
 (`!(f:real^3->real^3) f' (h:real^N->real^3) (g:real^2->real^N) la ba p q w mu
    x0 dlt k.
     pl_homeomorphism ((:real^3),(:real^3)) (f,f') /\ f (h(g x0)) = vec 0 /\
     linear la /\ (!z. z IN convex hull {p,q,w} ==> h(g z) = la z + ba) /\
     ~((h(g q) - h(g p)) cross (h(g w) - h(g p)) = vec 0) /\ 1 <= k /\ k <= 3 /\
     (!s t. (f(h(g x0) + s % (h(g q) - h(g p)) + t % (h(g w) - h(g p))))$k = &0) /\
     (!z. (f z)$3 = (z - h(g x0))$3) /\
     (h(g q) - h(g p))$3 = &0 /\ &0 < (h(g w) - h(g p))$3 /\
     &0 < mu /\ mu < &1 /\ (&1 - mu) % p + mu % q = x0 /\ &0 < dlt
     ==> ?eta. &0 < eta /\
               !z. &0 <= z$3 /\ z$k = &0 /\ norm z < eta
                   ==> z IN IMAGE ((f o h) o g) (ball(x0,dlt) INTER
                                                 convex hull {p,q,w})`,
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY MOI_LGB2_FLIP_TAC o CONJUNCTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB2_F_FACTS) THEN
  ABBREV_TAC `R = norm(q - p:real^2) + norm(w - p:real^2)` THEN
  SUBGOAL_THEN `&0 <= R` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  ABBREV_TAC `ep = min (min (mu / &2) ((&1 - mu) / &2)) (dlt / (R + &1))` THEN
  SUBGOAL_THEN `&0 < ep /\ &2 * ep <= mu /\ &2 * ep <= &1 - mu /\
                ep * (R + &1) <= dlt`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < R + &1` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < dlt / (R + &1)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
    SUBGOAL_THEN `ep <= dlt / (R + &1)` MP_TAC THENL
     [EXPAND_TAC "ep" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "ep" THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `(h:real^N->real^3)((g:real^2->real^N) x0)`;
                 `(h:real^N->real^3)((g:real^2->real^N) q) - h(g p)`;
                 `(h:real^N->real^3)((g:real^2->real^N) w) - h(g p)`;
                 `ep:real`; `k:num`] MOI_LGB2_BSURJ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `eta:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(x0:real^2) IN convex hull {p,q,w}` ASSUME_TAC THENL
   [UNDISCH_TAC `(&1 - mu) % p + mu % q = (x0:real^2)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`&1 - mu`; `mu:real`; `&0`] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; REAL_ADD_RID] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `X:real^2 = x0 + s % (q - p) + t % (w - p)` THEN
  SUBGOAL_THEN `(X:real^2) IN convex hull {p,q,w}` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN UNDISCH_TAC `(&1 - mu) % p + mu % q = (x0:real^2)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC MOI_LGB2_NEAR_EDGE_PT THEN EXISTS_TAC `ep:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `dist(X:real^2,x0) < dlt` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `abs s * norm(q - p:real^2) + abs t * norm(w - p:real^2)` THEN
    REWRITE_TAC[MOI_LGB2_DIST_STEP] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `ep * R` THEN CONJ_TAC THENL
     [EXPAND_TAC "R" THEN REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
      MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `ep * (R + &1) <= dlt` THEN UNDISCH_TAC `&0 < ep` THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; o_THM] THEN EXISTS_TAC `X:real^2` THEN
  ASM_REWRITE_TAC[IN_INTER; IN_BALL] THEN CONJ_TAC THENL
   [AP_TERM_TAC THEN EXPAND_TAC "X" THEN
    MP_TAC(ISPECL [`(h:real^N->real^3) o (g:real^2->real^N)`; `la:real^2->real^3`;
                   `ba:real^3`; `convex hull {p:real^2,q,w}`; `p:real^2`;
                   `q:real^2`; `w:real^2`; `x0:real^2`; `s:real`; `t:real`]
      MOI_LGB2_AFF_STEP) THEN
    REWRITE_TAC[o_THM] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN SIMP_TAC[HULL_INC; IN_INSERT];
      DISCH_THEN SUBST1_TAC THEN REFL_TAC];
    ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The four cases of the configuration.  Cell with two triangle             *)
(* carriers (model M1), cell with an edge and a triangle carrier (M2), wall *)
(* in the interior with two edge carriers (M3), wall in the boundary with   *)
(* two edge carriers (M3 used as M4).  Each gives the crossing chart via    *)
(* FINISH_INT or FINISH_BD.                                                 *)
(* ========================================================================= *)

let MOI_LGB2_CASE_TT = prove
 (`!(c:(real^N->bool)->bool) tt u (h:real^N->real^3) h' L g Q y x1 x2 sigma
    rho1 rho2.
     moi_lgb2_ctx c tt u h h' L g Q y x1 x2 sigma rho1 rho2 /\
     aff_dim sigma = &3 /\ aff_dim rho1 = &2 /\ aff_dim rho2 = &2
     ==> moi_lt_crossing2_at c g y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB2_CTX_BASIC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                 `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `y:real^N`; `x1:real^2`; `x2:real^2`; `sigma:real^N->bool`;
                 `rho1:real^2->bool`; `rho2:real^2->bool`] MOI_LGB2_TRANSV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC; DISCH_TAC] THEN
  FIRST_ASSUM(MAP_EVERY ASSUME_TAC o CONJUNCTS o
    GEN_REWRITE_RULE I [moi_lgb2_ctx]) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                 `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `y:real^N`; `x1:real^2`; `x2:real^2`; `sigma:real^N->bool`;
                 `rho1:real^2->bool`; `rho2:real^2->bool`; `rho1:real^2->bool`;
                 `x1:real^2`] MOI_LGB2_CTX_PHI) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `l1:real^2->real^3` (X_CHOOSE_THEN `b1:real^3`
      STRIP_ASSUME_TAC))
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                 `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `y:real^N`; `x1:real^2`; `x2:real^2`; `sigma:real^N->bool`;
                 `rho1:real^2->bool`; `rho2:real^2->bool`; `rho2:real^2->bool`;
                 `x2:real^2`] MOI_LGB2_CTX_PHI) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `l2:real^2->real^3` (X_CHOOSE_THEN `b2:real^3`
      STRIP_ASSUME_TAC))
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  SUBGOAL_THEN `~((y:real^N) IN complex_boundary c)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `(y:real^N) IN complex_boundary c
                 ==> aff_dim (sigma:real^N->bool) = &2 /\
                     sigma SUBSET complex_boundary c` THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `rho1:real^2->bool`; `x1:real^2`]
    MOI_LGB2_SHEET_TRI) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:real^2` (X_CHOOSE_THEN `q1:real^2`
    (X_CHOOSE_THEN `w1:real^2` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC))))))))) THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `rho2:real^2->bool`; `x2:real^2`]
    MOI_LGB2_SHEET_TRI) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p2:real^2` (X_CHOOSE_THEN `q2:real^2`
    (X_CHOOSE_THEN `w2:real^2` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC))))))))) THEN
  ABBREV_TAC `Phi = (h:real^N->real^3) o (g:real^2->real^N)` THEN
  SUBGOAL_THEN
   `(!z. z IN convex hull {p1,q1,w1} ==> (Phi:real^2->real^3) z = l1 z + b1) /\
    (!z. z IN convex hull {p2,q2,w2} ==> (Phi:real^2->real^3) z = l2 z + b2) /\
    (!z z'. z IN convex hull {p1,q1,w1} /\ z' IN convex hull {p1,q1,w1} /\
            (Phi:real^2->real^3) z = Phi z' ==> z = z') /\
    (!z z'. z IN convex hull {p2,q2,w2} /\ z' IN convex hull {p2,q2,w2} /\
            (Phi:real^2->real^3) z = Phi z' ==> z = z')`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Phi" THEN REWRITE_TAC[o_THM] THEN
    UNDISCH_TAC `rho1 = convex hull {p1:real^2,q1,w1}` THEN
    UNDISCH_TAC `rho2 = convex hull {p2:real^2,q2,w2}` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Phi:real^2->real^3) x1 = (h:real^N->real^3) y /\ Phi x2 = h y`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Phi" THEN ASM_REWRITE_TAC[o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `(x1:real^2) IN convex hull {p1,q1,w1} /\
                (x2:real^2) IN convex hull {p2,q2,w2}` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `n1 = ((Phi:real^2->real^3) q1 - Phi p1) cross (Phi w1 - Phi p1)` THEN
  ABBREV_TAC `n2 = ((Phi:real^2->real^3) q2 - Phi p2) cross (Phi w2 - Phi p2)` THEN
  SUBGOAL_THEN `~(n1:real^3 = vec 0) /\ ~(n2:real^3 = vec 0)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["n1"; "n2"] THEN CONJ_TAC THEN
    MATCH_MP_TAC MOI_LGB2_NONDEG THENL
     [MAP_EVERY EXISTS_TAC [`l1:real^2->real^3`; `b1:real^3`];
      MAP_EVERY EXISTS_TAC [`l2:real^2->real^3`; `b2:real^3`]] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Phi:real^2->real^3`; `l1:real^2->real^3`; `b1:real^3`;
                 `p1:real^2`; `q1:real^2`; `w1:real^2`; `x1:real^2`]
    MOI_LGB2_TRI_PLANE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`Phi:real^2->real^3`; `l2:real^2->real^3`; `b2:real^3`;
                 `p2:real^2`; `q2:real^2`; `w2:real^2`; `x2:real^2`]
    MOI_LGB2_TRI_PLANE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((n1:real^3) cross n2 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`n1:real^3`; `n2:real^3`] MOI_LGB2_CROSS_PARALLEL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `k:real`) THEN
    UNDISCH_TAC `~(IMAGE (Phi:real^2->real^3) rho1 SUBSET
                   affine hull (IMAGE Phi rho2))` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `rho1 = convex hull {p1:real^2,q1,w1}` THEN
    UNDISCH_TAC `rho2 = convex hull {p2:real^2,q2,w2}` THEN
    DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^2` THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`(Phi:real^2->real^3) p2`; `(Phi:real^2->real^3) q2`;
                   `(Phi:real^2->real^3) w2`; `(Phi:real^2->real^3) z`;
                   `(h:real^N->real^3) y`] MOI_LGB2_PLANE_BASE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(Phi:real^2->real^3) x2 = (h:real^N->real^3) y` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[DOT_LMUL] THEN
    ASM_SIMP_TAC[REAL_MUL_RZERO];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(h:real^N->real^3) y`; `n1:real^3`; `n2:real^3`]
    MOI_LGB2_MODEL_M1) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `f':real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`x1:real^2`; `x2:real^2`; `d1:real`; `d2:real`]
    MOI_LGB2_TWO_BALLS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `ball(x1:real^2,d) SUBSET convex hull {p1,q1,w1} /\
                ball(x2:real^2,d) SUBSET convex hull {p2,q2,w2}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_TRANS THENL
     [EXISTS_TAC `ball(x1:real^2,d1)`; EXISTS_TAC `ball(x2:real^2,d2)`] THEN
    ASM_SIMP_TAC[SUBSET_BALL] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {p1:real^2,q1,w1} SUBSET std_triangle /\
                convex hull {p2:real^2,q2,w2} SUBSET std_triangle`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `UNIONS L = std_triangle` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_MESON_TAC[SUBSET; IN_UNIONS];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_LGB2_FINISH_INT THEN
  MAP_EVERY EXISTS_TAC [`x1:real^2`; `x2:real^2`; `u:real^N->bool`;
                        `h:real^N->real^3`; `h':real^3->real^N`;
                        `f:real^3->real^3`; `f':real^3->real^3`;
                        `ball(x1:real^2,d)`; `ball(x2:real^2,d)`] THEN
  ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_SUBSET THEN REWRITE_TAC[OPEN_BALL] THEN ASM SET_TAC[];
    MATCH_MP_TAC OPEN_SUBSET THEN REWRITE_TAC[OPEN_BALL] THEN ASM SET_TAC[];
    ASM SET_TAC[];
    ASM SET_TAC[];
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `z':real^2`)) (concl th) &&
      can (find_term ((=) `p1:real^2`)) (concl th))) THEN
    EXPAND_TAC "Phi" THEN ASM_REWRITE_TAC[o_THM] THEN ASM SET_TAC[];
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `z':real^2`)) (concl th) &&
      can (find_term ((=) `p2:real^2`)) (concl th))) THEN
    EXPAND_TAC "Phi" THEN ASM_REWRITE_TAC[o_THM] THEN ASM SET_TAC[];
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `n1:real^3`)) (concl th) &&
      can (find_term ((=) `f:real^3->real^3`)) (concl th))) THEN
    SUBGOAL_THEN `(h:real^N->real^3) ((g:real^2->real^N) x) = Phi x` SUBST1_TAC THENL
     [EXPAND_TAC "Phi" THEN REWRITE_TAC[o_THM]; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `n1:real^3`)) (concl th) &&
      can (find_term ((=) `Phi:real^2->real^3`)) (concl th))) THEN
    ASM SET_TAC[];
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `n2:real^3`)) (concl th) &&
      can (find_term ((=) `f:real^3->real^3`)) (concl th))) THEN
    SUBGOAL_THEN `(h:real^N->real^3) ((g:real^2->real^N) x) = Phi x` SUBST1_TAC THENL
     [EXPAND_TAC "Phi" THEN REWRITE_TAC[o_THM]; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `n2:real^3`)) (concl th) &&
      can (find_term ((=) `Phi:real^2->real^3`)) (concl th))) THEN
    ASM SET_TAC[]]);;

let MOI_LGB2_CASE_ET = prove
 (`!(c:(real^N->bool)->bool) tt u (h:real^N->real^3) h' L g Q y x1 x2 sigma
    rho1 rho2.
     moi_lgb2_ctx c tt u h h' L g Q y x1 x2 sigma rho1 rho2 /\
     aff_dim sigma = &3 /\ aff_dim rho1 = &1 /\ aff_dim rho2 = &2
     ==> moi_lt_crossing2_at c g y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB2_CTX_BASIC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                 `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `y:real^N`; `x1:real^2`; `x2:real^2`; `sigma:real^N->bool`;
                 `rho1:real^2->bool`; `rho2:real^2->bool`] MOI_LGB2_TRANSV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC; DISCH_TAC] THEN
  FIRST_ASSUM(MAP_EVERY ASSUME_TAC o CONJUNCTS o
    GEN_REWRITE_RULE I [moi_lgb2_ctx]) THEN
  SUBGOAL_THEN `~((y:real^N) IN complex_boundary c)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `(y:real^N) IN complex_boundary c
                 ==> aff_dim (sigma:real^N->bool) = &2 /\
                     sigma SUBSET complex_boundary c` THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:real^2->real^N`; `x1:real^2`]
    MOI_LGB2_SD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `dd:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `rho1:real^2->bool`; `x1:real^2`]
    MOI_LGB2_SHEET_EDGE2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^2` (X_CHOOSE_THEN `q:real^2`
    (X_CHOOSE_THEN `w:real^2` (X_CHOOSE_THEN `w':real^2`
      (X_CHOOSE_THEN `mu:real`
        (MAP_EVERY (fun th -> if is_eq(concl th) &&
                                 lhs(concl th) = `x1:real^2`
                              then ASSUME_TAC(SYM th) else ASSUME_TAC th) o
         CONJUNCTS)))))) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC o
    check (is_exists o concl)) THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `rho2:real^2->bool`; `x2:real^2`]
    MOI_LGB2_SHEET_TRI) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p2:real^2` (X_CHOOSE_THEN `q2:real^2`
    (X_CHOOSE_THEN `w2:real^2` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC))))))))) THEN
  SUBGOAL_THEN `(x1:real^2) IN convex hull {p,q,w} /\ x1 IN convex hull {p,q,w'}`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN
    CONJ_TAC THEN MAP_EVERY EXISTS_TAC [`&1 - mu`; `mu:real`; `&0`] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; REAL_ADD_RID] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                 `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `y:real^N`; `x1:real^2`; `x2:real^2`; `sigma:real^N->bool`;
                 `rho1:real^2->bool`; `rho2:real^2->bool`;
                 `convex hull {p:real^2,q,w}`; `x1:real^2`] MOI_LGB2_CTX_PHI) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `la:real^2->real^3` (X_CHOOSE_THEN `ba:real^3`
      STRIP_ASSUME_TAC))
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                 `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `y:real^N`; `x1:real^2`; `x2:real^2`; `sigma:real^N->bool`;
                 `rho1:real^2->bool`; `rho2:real^2->bool`;
                 `convex hull {p:real^2,q,w'}`; `x1:real^2`] MOI_LGB2_CTX_PHI) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `lb:real^2->real^3` (X_CHOOSE_THEN `bb:real^3`
      STRIP_ASSUME_TAC))
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                 `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `y:real^N`; `x1:real^2`; `x2:real^2`; `sigma:real^N->bool`;
                 `rho1:real^2->bool`; `rho2:real^2->bool`; `rho2:real^2->bool`;
                 `x2:real^2`] MOI_LGB2_CTX_PHI) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `l2:real^2->real^3` (X_CHOOSE_THEN `b2:real^3`
      STRIP_ASSUME_TAC))
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  ABBREV_TAC `Phi = (h:real^N->real^3) o (g:real^2->real^N)` THEN
  SUBGOAL_THEN
   `(!z. z IN convex hull {p,q,w} ==> (Phi:real^2->real^3) z = la z + ba) /\
    (!z. z IN convex hull {p,q,w'} ==> (Phi:real^2->real^3) z = lb z + bb) /\
    (!z. z IN convex hull {p2,q2,w2} ==> (Phi:real^2->real^3) z = l2 z + b2) /\
    (!z z'. z IN convex hull {p,q,w} /\ z' IN convex hull {p,q,w} /\
            (Phi:real^2->real^3) z = Phi z' ==> z = z') /\
    (!z z'. z IN convex hull {p,q,w'} /\ z' IN convex hull {p,q,w'} /\
            (Phi:real^2->real^3) z = Phi z' ==> z = z') /\
    (!z z'. z IN convex hull {p2,q2,w2} /\ z' IN convex hull {p2,q2,w2} /\
            (Phi:real^2->real^3) z = Phi z' ==> z = z')`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Phi" THEN REWRITE_TAC[o_THM] THEN
    UNDISCH_TAC `rho2 = convex hull {p2:real^2,q2,w2}` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Phi:real^2->real^3) x1 = (h:real^N->real^3) y /\ Phi x2 = h y`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Phi" THEN ASM_REWRITE_TAC[o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `(x2:real^2) IN convex hull {p2,q2,w2}` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `dv = (Phi:real^2->real^3) q - Phi p` THEN
  ABBREV_TAC `av = (Phi:real^2->real^3) w - Phi p` THEN
  ABBREV_TAC `bv = (Phi:real^2->real^3) w' - Phi p` THEN
  ABBREV_TAC `nb = ((Phi:real^2->real^3) q2 - Phi p2) cross (Phi w2 - Phi p2)` THEN
  SUBGOAL_THEN `~(nb:real^3 = vec 0) /\ ~((dv:real^3) cross av = vec 0) /\
                ~((dv:real^3) cross bv = vec 0)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["nb"; "dv"; "av"; "bv"] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC MOI_LGB2_NONDEG THENL
     [MAP_EVERY EXISTS_TAC [`l2:real^2->real^3`; `b2:real^3`];
      MAP_EVERY EXISTS_TAC [`la:real^2->real^3`; `ba:real^3`];
      MAP_EVERY EXISTS_TAC [`lb:real^2->real^3`; `bb:real^3`]] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Phi:real^2->real^3`; `l2:real^2->real^3`; `b2:real^3`;
                 `p2:real^2`; `q2:real^2`; `w2:real^2`; `x2:real^2`]
    MOI_LGB2_TRI_PLANE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((nb:real^3) dot dv = &0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~(IMAGE (Phi:real^2->real^3) rho1 SUBSET
                   affine hull (IMAGE Phi rho2))` THEN
    UNDISCH_TAC `rho2 = convex hull {p2:real^2,q2,w2}` THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^2` THEN
    REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^2) IN convex hull {p,q,w}` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^2) IN segment[p,q]` THEN
      REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
      MATCH_MP_TAC(SET_RULE `!a b (x:real^2). a SUBSET b ==> x IN a ==> x IN b`) THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(z:real^2) IN segment[p,q]` THEN REWRITE_TAC[IN_SEGMENT] THEN
    DISCH_THEN(X_CHOOSE_THEN `tau:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
    MP_TAC(ISPECL [`(Phi:real^2->real^3) p2`; `(Phi:real^2->real^3) q2`;
                   `(Phi:real^2->real^3) w2`; `(Phi:real^2->real^3) z`;
                   `(h:real^N->real^3) y`] MOI_LGB2_PLANE_BASE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(Phi:real^2->real^3) x2 = (h:real^N->real^3) y` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `(x1:real^2) + (tau - mu) % (q - p) + &0 % (w - p) = z`
    ASSUME_TAC THENL
     [UNDISCH_TAC `z:real^2 = (&1 - tau) % p + tau % q` THEN
      DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `(&1 - mu) % p + mu % q = (x1:real^2)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`Phi:real^2->real^3`; `la:real^2->real^3`; `ba:real^3`;
                   `convex hull {p:real^2,q,w}`; `p:real^2`; `q:real^2`;
                   `w:real^2`; `x1:real^2`; `tau - mu:real`; `&0`]
      MOI_LGB2_AFF_STEP) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN SIMP_TAC[HULL_INC; IN_INSERT] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID;
                VECTOR_ARITH `(a + x) - a:real^3 = x`] THEN
    ASM_REWRITE_TAC[DOT_RMUL; REAL_MUL_RZERO];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Phi:real^2->real^3`; `p:real^2`; `q:real^2`; `w:real^2`;
                 `w':real^2`; `mu:real`; `min d1 dd:real`] MOI_LGB2_FOLD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN] THEN REPEAT CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`la:real^2->real^3`; `ba:real^3`] THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY EXISTS_TAC [`lb:real^2->real^3`; `bb:real^3`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_LT_MIN] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `dd:real`)) (concl th) && is_forall (concl th))) THEN
    UNDISCH_TAC `(Phi:real^2->real^3) x = Phi x'` THEN EXPAND_TAC "Phi" THEN
    REWRITE_TAC[o_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN ball(x1,d1) /\ x' IN ball(x1,d1)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[IN_BALL] THEN ASM_MESON_TAC[DIST_SYM]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM SET_TAC[]; ASM SET_TAC[];
      ASM_MESON_TAC[DIST_SYM]; ASM_MESON_TAC[DIST_SYM];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `p':real^N`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(h:real^N->real^3) y`; `dv:real^3`; `av:real^3`; `bv:real^3`;
                 `nb:real^3`] MOI_LGB2_MODEL_M2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `f':real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`x1:real^2`; `x2:real^2`; `min d1 dd:real`; `d2:real`]
    MOI_LGB2_TWO_BALLS) THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `ball(x1:real^2,d) SUBSET ball(x1,d1) /\
                ball(x1:real^2,d) SUBSET ball(x1,dd) /\
                ball(x2:real^2,d) SUBSET convex hull {p2,q2,w2}`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(x2:real^2,d2)` THEN
      ASM_SIMP_TAC[SUBSET_BALL] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {p:real^2,q,w} SUBSET std_triangle /\
                convex hull {p:real^2,q,w'} SUBSET std_triangle /\
                convex hull {p2:real^2,q2,w2} SUBSET std_triangle`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `UNIONS L = std_triangle` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_MESON_TAC[SUBSET; IN_UNIONS];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x1:real^2) IN segment[p,q]` ASSUME_TAC THENL
   [REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `mu:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_LGB2_FINISH_INT THEN
  MAP_EVERY EXISTS_TAC [`x1:real^2`; `x2:real^2`; `u:real^N->bool`;
                        `h:real^N->real^3`; `h':real^3->real^N`;
                        `f:real^3->real^3`; `f':real^3->real^3`;
                        `ball(x1:real^2,d)`; `ball(x2:real^2,d)`] THEN
  ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_SUBSET THEN REWRITE_TAC[OPEN_BALL] THEN ASM SET_TAC[];
    MATCH_MP_TAC OPEN_SUBSET THEN REWRITE_TAC[OPEN_BALL] THEN ASM SET_TAC[];
    ASM SET_TAC[];
    ASM SET_TAC[];
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `dd:real`)) (concl th) && is_forall (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ball(x1:real^2,d) SUBSET ball(x1,dd)` THEN
    UNDISCH_TAC `ball(x1:real^2,d) SUBSET ball(x1,d1)` THEN
    UNDISCH_TAC `ball(x1:real^2,d1) SUBSET std_triangle` THEN
    UNDISCH_TAC `(x:real^2) IN ball(x1,d)` THEN
    UNDISCH_TAC `(x':real^2) IN ball(x1,d)` THEN
    REWRITE_TAC[SUBSET; IN_BALL] THEN MESON_TAC[DIST_SYM];
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `z':real^2`)) (concl th) &&
      can (find_term ((=) `p2:real^2`)) (concl th))) THEN
    EXPAND_TAC "Phi" THEN ASM_REWRITE_TAC[o_THM] THEN ASM SET_TAC[];
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN convex hull {p,q,w} \/ x IN convex hull {p,q,w'}`
    MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
     [MP_TAC(ISPECL [`Phi:real^2->real^3`; `la:real^2->real^3`; `ba:real^3`;
                     `p:real^2`; `q:real^2`; `w:real^2`; `x1:real^2`; `x:real^2`]
        MOI_LGB2_TRI_PARAM);
      MP_TAC(ISPECL [`Phi:real^2->real^3`; `lb:real^2->real^3`; `bb:real^3`;
                     `p:real^2`; `q:real^2`; `w':real^2`; `x1:real^2`; `x:real^2`]
        MOI_LGB2_TRI_PARAM)] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real` (X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC)) THEN
    (SUBGOAL_THEN `(h:real^N->real^3) ((g:real^2->real^N) x) = Phi x` SUBST1_TAC THENL
      [EXPAND_TAC "Phi" THEN REWRITE_TAC[o_THM]; ALL_TAC]) THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `(Phi:real^2->real^3) x`)) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `f:real^3->real^3`)) (concl th) &&
      is_forall (concl th) &&
      (can (find_term ((=) `av:real^3`)) (concl th) ||
       can (find_term ((=) `bv:real^3`)) (concl th)))) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `nb:real^3`)) (concl th) &&
      can (find_term ((=) `f:real^3->real^3`)) (concl th))) THEN
    SUBGOAL_THEN `(h:real^N->real^3) ((g:real^2->real^N) x) = Phi x` SUBST1_TAC THENL
     [EXPAND_TAC "Phi" THEN REWRITE_TAC[o_THM]; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `nb:real^3`)) (concl th) &&
      can (find_term ((=) `Phi:real^2->real^3`)) (concl th))) THEN
    ASM SET_TAC[]]);;

let MOI_LGB2_CASE_WI = prove
 (`!(c:(real^N->bool)->bool) tt u (h:real^N->real^3) h' L g Q y x1 x2 sigma
    rho1 rho2.
     moi_lgb2_ctx c tt u h h' L g Q y x1 x2 sigma rho1 rho2 /\
     aff_dim sigma = &2 /\ aff_dim rho1 = &1 /\ aff_dim rho2 = &1 /\
     ~(y IN complex_boundary c)
     ==> moi_lt_crossing2_at c g y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB2_CTX_BASIC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                 `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `y:real^N`; `x1:real^2`; `x2:real^2`; `sigma:real^N->bool`;
                 `rho1:real^2->bool`; `rho2:real^2->bool`] MOI_LGB2_TRANSV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC; DISCH_TAC] THEN
  FIRST_ASSUM(MAP_EVERY ASSUME_TAC o CONJUNCTS o
    GEN_REWRITE_RULE I [moi_lgb2_ctx]) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `sigma:real^N->bool`]
    MOI_SCF_SC_VERTICES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool`
    (MAP_EVERY MOI_LGB2_FLIP_TAC o CONJUNCTS)) THEN
  SUBGOAL_THEN `(V:real^N->bool) HAS_SIZE 3` MP_TAC THENL
   [REWRITE_TAC[HAS_SIZE] THEN ASM_REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN
    ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[MOI_SCF_HAS_SIZE_3] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real^N` (X_CHOOSE_THEN `B:real^N`
    (X_CHOOSE_THEN `D:real^N` (MAP_EVERY MOI_LGB2_FLIP_TAC o CONJUNCTS)))) THEN
  SUBGOAL_THEN `convex hull {A:real^N,B,D} = sigma /\ ~affine_dependent {A,B,D}`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                 `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `y:real^N`; `x1:real^2`; `x2:real^2`; `sigma:real^N->bool`;
                 `rho1:real^2->bool`; `rho2:real^2->bool`; `A:real^N`;
                 `B:real^N`; `D:real^N`] MOI_LGB2_EDGE_SHEET_W) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:real^2` (X_CHOOSE_THEN `q1:real^2`
    (X_CHOOSE_THEN `w1:real^2` (X_CHOOSE_THEN `v1:real^2`
    (X_CHOOSE_THEN `mu1:real` (X_CHOOSE_THEN `d1:real`
    (X_CHOOSE_THEN `la1:real^2->real^3` (X_CHOOSE_THEN `ba1:real^3`
    (X_CHOOSE_THEN `lb1:real^2->real^3` (X_CHOOSE_THEN `bb1:real^3`
      (MAP_EVERY MOI_LGB2_FLIP_TAC o CONJUNCTS))))))))))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                 `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `y:real^N`; `x2:real^2`; `x1:real^2`; `sigma:real^N->bool`;
                 `rho2:real^2->bool`; `rho1:real^2->bool`; `A:real^N`;
                 `B:real^N`; `D:real^N`] MOI_LGB2_EDGE_SHEET_W) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_LGB2_CTX_SWAP THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p2:real^2` (X_CHOOSE_THEN `q2:real^2`
    (X_CHOOSE_THEN `w2:real^2` (X_CHOOSE_THEN `v2:real^2`
    (X_CHOOSE_THEN `mu2:real` (X_CHOOSE_THEN `d2:real`
    (X_CHOOSE_THEN `la2:real^2->real^3` (X_CHOOSE_THEN `ba2:real^3`
    (X_CHOOSE_THEN `lb2:real^2->real^3` (X_CHOOSE_THEN `bb2:real^3`
      (MAP_EVERY MOI_LGB2_FLIP_TAC o CONJUNCTS))))))))))) THEN
  SUBGOAL_THEN `IMAGE (h:real^N->real^3) sigma = convex hull {h A,h B,h D}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h:real^N->real^3`; `l:real^N->real^3`; `b:real^3`;
                   `{A:real^N,B,D}`] MOI_LGA_HULL_IMAGE) THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES];
    ALL_TAC] THEN
  ABBREV_TAC `nu = ((h:real^N->real^3) B - h A) cross (h D - h A)` THEN
  SUBGOAL_THEN
   `!z:real^2. z IN rho1 \/ z IN rho2
               ==> (nu:real^3) dot ((h:real^N->real^3)((g:real^2->real^N) z) - h A) =
                   &0`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "nu" THEN
    MATCH_MP_TAC MOI_LGB2_PLANE_IN THEN
    MATCH_MP_TAC(SET_RULE `!a b (x:real^3). a SUBSET b /\ x IN a ==> x IN b`) THEN
    EXISTS_TAC `convex hull {(h:real^N->real^3) A,h B,h D}` THEN
    REWRITE_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL] THEN
    UNDISCH_TAC `IMAGE (h:real^N->real^3) sigma = convex hull {h A,h B,h D}` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p1:real^2) IN rho1 /\ (q1:real^2) IN rho1 /\
                (p2:real^2) IN rho2 /\ (q2:real^2) IN rho2`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `convex hull {p1:real^2,q1} = rho1` THEN
    UNDISCH_TAC `convex hull {p2:real^2,q2} = rho2` THEN
    REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
    SIMP_TAC[HULL_INC; IN_INSERT];
    ALL_TAC] THEN
  ABBREV_TAC `e1 = (h:real^N->real^3)((g:real^2->real^N) q1) - h(g p1)` THEN
  ABBREV_TAC `e2 = (h:real^N->real^3)((g:real^2->real^N) q2) - h(g p2)` THEN
  SUBGOAL_THEN `(nu:real^3) dot e1 = &0 /\ (nu:real^3) dot e2 = &0`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["e1"; "e2"] THEN
    ONCE_REWRITE_TAC[ISPECL [`nu:real^3`;
      `(h:real^N->real^3)((g:real^2->real^N) q1)`;
      `(h:real^N->real^3)((g:real^2->real^N) p1)`;
      `(h:real^N->real^3) A`] MOI_LGB2_DOT_SUB3] THEN
    ONCE_REWRITE_TAC[ISPECL [`nu:real^3`;
      `(h:real^N->real^3)((g:real^2->real^N) q2)`;
      `(h:real^N->real^3)((g:real^2->real^N) p2)`;
      `(h:real^N->real^3) A`] MOI_LGB2_DOT_SUB3] THEN
    ASM_SIMP_TAC[REAL_SUB_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(e1:real^3 = vec 0) /\ ~(e2:real^3 = vec 0)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["e1"; "e2"] THEN REWRITE_TAC[VECTOR_SUB_EQ] THEN
    CONJ_TAC THEN DISCH_TAC THENL
     [UNDISCH_TAC `~(p1:real^2 = q1)` THEN REWRITE_TAC[] THEN
      CONV_TAC SYM_CONV THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `z':real^2`)) (concl th) &&
        can (find_term ((=) `w1:real^2`)) (concl th)));
      UNDISCH_TAC `~(p2:real^2 = q2)` THEN REWRITE_TAC[] THEN
      CONV_TAC SYM_CONV THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `z':real^2`)) (concl th) &&
        can (find_term ((=) `w2:real^2`)) (concl th)))] THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[HULL_INC; IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x1:real^2) IN segment[p1,q1] /\ (x2:real^2) IN segment[p2,q2]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_SEGMENT] THEN CONJ_TAC THENL
     [EXISTS_TAC `mu1:real`; EXISTS_TAC `mu2:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~((e1:real^3) cross e2 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~(IMAGE ((h:real^N->real^3) o (g:real^2->real^N)) rho1 SUBSET
                   affine hull (IMAGE (h o g) rho2))` THEN
    REWRITE_TAC[] THEN
    UNDISCH_TAC `convex hull {p1:real^2,q1} = rho1` THEN
    UNDISCH_TAC `convex hull {p2:real^2,q2} = rho2` THEN
    REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
    MATCH_MP_TAC MOI_LGB2_LINE_TRANSV THEN
    MAP_EVERY EXISTS_TAC [`la1:real^2->real^3`; `ba1:real^3`;
                          `la2:real^2->real^3`; `ba2:real^3`;
                          `mu1:real`; `mu2:real`] THEN
    ASM_REWRITE_TAC[o_THM] THEN
    REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC(SET_RULE `!a b (x:real^2). a SUBSET b /\ x IN a ==> x IN b`) THEN
      EXISTS_TAC `convex hull {p1:real^2,q1}` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC(SET_RULE `!a b (x:real^2). a SUBSET b /\ x IN a ==> x IN b`) THEN
      EXISTS_TAC `convex hull {p2:real^2,q2}` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(h:real^N->real^3) y`; `nu:real^3`; `e1:real^3`; `e2:real^3`;
                 `(h:real^N->real^3)((g:real^2->real^N) w1) - h(g p1)`;
                 `(h:real^N->real^3)((g:real^2->real^N) v1) - h(g p1)`;
                 `(h:real^N->real^3)((g:real^2->real^N) w2) - h(g p2)`;
                 `(h:real^N->real^3)((g:real^2->real^N) v2) - h(g p2)`]
    MOI_LGB2_MODEL_M3S) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `f':real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`x1:real^2`; `x2:real^2`; `d1:real`; `d2:real`]
    MOI_LGB2_TWO_BALLS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `ball(x1:real^2,d) SUBSET ball(x1,d1) /\
                ball(x2:real^2,d) SUBSET ball(x2,d2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_BALL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean std_triangle) (ball(x1:real^2,d)) /\
    open_in (subtopology euclidean std_triangle) (ball(x2:real^2,d))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC OPEN_SUBSET THEN REWRITE_TAC[OPEN_BALL] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g:real^2->real^N) (ball(x1,d)) SUBSET u /\
                IMAGE (g:real^2->real^N) (ball(x2,d)) SUBSET u`
  STRIP_ASSUME_TAC THENL [CONJ_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!z z'. z IN ball(x1:real^2,d) /\ z' IN ball(x1,d) /\
            (g:real^2->real^N) z = g z' ==> z = z') /\
    (!z z'. z IN ball(x2:real^2,d) /\ z' IN ball(x2,d) /\
            (g:real^2->real^N) z = g z' ==> z = z')`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT STRIP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `d1:real`)) (concl th) && is_forall (concl th) &&
        can (find_term ((=) `z':real^2`)) (concl th)));
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `d2:real`)) (concl th) && is_forall (concl th) &&
        can (find_term ((=) `z':real^2`)) (concl th)))] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN ball(x1:real^2,d)
        ==> ((f:real^3->real^3)((h:real^N->real^3)((g:real^2->real^N) x)))$1 = &0`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN convex hull {p1,q1,w1} \/
                  x IN convex hull {p1,q1,v1}` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
     [MP_TAC(BETA_RULE(ISPECL [`\z:real^2. (h:real^N->real^3)((g:real^2->real^N) z)`;
        `la1:real^2->real^3`; `ba1:real^3`; `p1:real^2`; `q1:real^2`;
        `w1:real^2`; `x1:real^2`; `x:real^2`] MOI_LGB2_TRI_PARAM));
      MP_TAC(BETA_RULE(ISPECL [`\z:real^2. (h:real^N->real^3)((g:real^2->real^N) z)`;
        `lb1:real^2->real^3`; `bb1:real^3`; `p1:real^2`; `q1:real^2`;
        `v1:real^2`; `x1:real^2`; `x:real^2`] MOI_LGB2_TRI_PARAM))] THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real` (X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq (concl th) &&
      lhs (concl th) = `(h:real^N->real^3)((g:real^2->real^N) x)`)) THEN
    REWRITE_TAC[ASSUME `(g:real^2->real^N) x1 = y`;
                ASSUME `(h:real^N->real^3)((g:real^2->real^N) q1) - h(g p1) = e1`] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term ((=) `f:real^3->real^3`)) (concl th) &&
      can (find_term ((=) `e1:real^3`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN ball(x2:real^2,d)
        ==> ((f:real^3->real^3)((h:real^N->real^3)((g:real^2->real^N) x)))$2 = &0`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN convex hull {p2,q2,w2} \/
                  x IN convex hull {p2,q2,v2}` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
     [MP_TAC(BETA_RULE(ISPECL [`\z:real^2. (h:real^N->real^3)((g:real^2->real^N) z)`;
        `la2:real^2->real^3`; `ba2:real^3`; `p2:real^2`; `q2:real^2`;
        `w2:real^2`; `x2:real^2`; `x:real^2`] MOI_LGB2_TRI_PARAM));
      MP_TAC(BETA_RULE(ISPECL [`\z:real^2. (h:real^N->real^3)((g:real^2->real^N) z)`;
        `lb2:real^2->real^3`; `bb2:real^3`; `p2:real^2`; `q2:real^2`;
        `v2:real^2`; `x2:real^2`; `x:real^2`] MOI_LGB2_TRI_PARAM))] THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real` (X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq (concl th) &&
      lhs (concl th) = `(h:real^N->real^3)((g:real^2->real^N) x)`)) THEN
    REWRITE_TAC[ASSUME `(g:real^2->real^N) x2 = y`;
                ASSUME `(h:real^N->real^3)((g:real^2->real^N) q2) - h(g p2) = e2`] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term ((=) `f:real^3->real^3`)) (concl th) &&
      can (find_term ((=) `e2:real^3`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_LGB2_FINISH_INT THEN
  MAP_EVERY EXISTS_TAC [`x1:real^2`; `x2:real^2`; `u:real^N->bool`;
                        `h:real^N->real^3`; `h':real^3->real^N`;
                        `f:real^3->real^3`; `f':real^3->real^3`;
                        `ball(x1:real^2,d)`; `ball(x2:real^2,d)`] THEN
  ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL]);;

let MOI_LGB2_CASE_WB = prove
 (`!(c:(real^N->bool)->bool) tt u (h:real^N->real^3) h' L g Q y x1 x2 sigma
    rho1 rho2.
     moi_lgb2_ctx c tt u h h' L g Q y x1 x2 sigma rho1 rho2 /\
     aff_dim sigma = &2 /\ aff_dim rho1 = &1 /\ aff_dim rho2 = &1 /\
     y IN complex_boundary c
     ==> moi_lt_crossing2_at c g y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB2_CTX_BASIC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                 `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `y:real^N`; `x1:real^2`; `x2:real^2`; `sigma:real^N->bool`;
                 `rho1:real^2->bool`; `rho2:real^2->bool`] MOI_LGB2_TRANSV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                 `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `y:real^N`; `x1:real^2`; `x2:real^2`; `sigma:real^N->bool`;
                 `rho1:real^2->bool`; `rho2:real^2->bool`] MOI_LGB2_EDGE_SHEET_B) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:real^2` (X_CHOOSE_THEN `q1:real^2`
    (X_CHOOSE_THEN `w1:real^2` (X_CHOOSE_THEN `mu1:real`
    (X_CHOOSE_THEN `d1:real` (X_CHOOSE_THEN `la1:real^2->real^3`
    (X_CHOOSE_THEN `ba1:real^3` (MAP_EVERY MOI_LGB2_FLIP_TAC o CONJUNCTS)))))))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                 `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `y:real^N`; `x2:real^2`; `x1:real^2`; `sigma:real^N->bool`;
                 `rho2:real^2->bool`; `rho1:real^2->bool`] MOI_LGB2_EDGE_SHEET_B) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_LGB2_CTX_SWAP THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p2:real^2` (X_CHOOSE_THEN `q2:real^2`
    (X_CHOOSE_THEN `w2:real^2` (X_CHOOSE_THEN `mu2:real`
    (X_CHOOSE_THEN `d2:real` (X_CHOOSE_THEN `la2:real^2->real^3`
    (X_CHOOSE_THEN `ba2:real^3` (MAP_EVERY MOI_LGB2_FLIP_TAC o CONJUNCTS)))))))) THEN
  FIRST_ASSUM(MAP_EVERY ASSUME_TAC o CONJUNCTS o
    GEN_REWRITE_RULE I [moi_lgb2_ctx]) THEN
  SUBGOAL_THEN
   `IMAGE (h:real^N->real^3) u = ball(vec 0,&1) INTER {z:real^3 | &0 <= z$3} /\
    IMAGE h (u INTER complex_boundary c) = IMAGE h u INTER {z:real^3 | z$3 = &0}`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `homeomorphism (u,IMAGE h u) ((h:real^N->real^3),h')`
  ASSUME_TAC THENL [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  SUBGOAL_THEN `((h:real^N->real^3) y)$3 = &0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`] MOI_LGB2_CB_IFF) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `e1 = (h:real^N->real^3)((g:real^2->real^N) q1) - h(g p1)` THEN
  ABBREV_TAC `e2 = (h:real^N->real^3)((g:real^2->real^N) q2) - h(g p2)` THEN
  ABBREV_TAC `a1 = (h:real^N->real^3)((g:real^2->real^N) w1) - h(g p1)` THEN
  ABBREV_TAC `a2 = (h:real^N->real^3)((g:real^2->real^N) w2) - h(g p2)` THEN
  SUBGOAL_THEN `(e1:real^3)$3 = &0 /\ (e2:real^3)$3 = &0 /\
                &0 < (a1:real^3)$3 /\ &0 < (a2:real^3)$3`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["e1"; "e2"; "a1"; "a2"] THEN
    ASM_REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN
    REWRITE_TAC[REAL_SUB_RZERO; REAL_SUB_REFL] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p1:real^2) IN rho1 /\ (q1:real^2) IN rho1 /\
                (p2:real^2) IN rho2 /\ (q2:real^2) IN rho2`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `convex hull {p1:real^2,q1} = rho1` THEN
    UNDISCH_TAC `convex hull {p2:real^2,q2} = rho2` THEN
    REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
    SIMP_TAC[HULL_INC; IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((e1:real^3) cross a1 = vec 0) /\ ~((e2:real^3) cross a2 = vec 0)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["e1"; "e2"; "a1"; "a2"] THEN CONJ_TAC THEN
    MATCH_MP_TAC(BETA_RULE(ISPEC `\z:real^2. (h:real^N->real^3)((g:real^2->real^N) z)`
      MOI_LGB2_NONDEG)) THENL
     [MAP_EVERY EXISTS_TAC [`la1:real^2->real^3`; `ba1:real^3`];
      MAP_EVERY EXISTS_TAC [`la2:real^2->real^3`; `ba2:real^3`]] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(e1:real^3 = vec 0) /\ ~(e2:real^3 = vec 0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THENL
     [UNDISCH_TAC `~((e1:real^3) cross a1 = vec 0)`;
      UNDISCH_TAC `~((e2:real^3) cross a2 = vec 0)`] THEN
    ASM_REWRITE_TAC[CROSS_LZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x1:real^2) IN segment[p1,q1] /\ (x2:real^2) IN segment[p2,q2]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_SEGMENT] THEN CONJ_TAC THENL
     [EXISTS_TAC `mu1:real`; EXISTS_TAC `mu2:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~((e1:real^3) cross e2 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~(IMAGE ((h:real^N->real^3) o (g:real^2->real^N)) rho1 SUBSET
                   affine hull (IMAGE (h o g) rho2))` THEN
    REWRITE_TAC[] THEN
    UNDISCH_TAC `convex hull {p1:real^2,q1} = rho1` THEN
    UNDISCH_TAC `convex hull {p2:real^2,q2} = rho2` THEN
    REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
    MATCH_MP_TAC MOI_LGB2_LINE_TRANSV THEN
    MAP_EVERY EXISTS_TAC [`la1:real^2->real^3`; `ba1:real^3`;
                          `la2:real^2->real^3`; `ba2:real^3`;
                          `mu1:real`; `mu2:real`] THEN
    ASM_REWRITE_TAC[o_THM] THEN
    REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC(SET_RULE `!a b (x:real^2). a SUBSET b /\ x IN a ==> x IN b`) THEN
      EXISTS_TAC `convex hull {p1:real^2,q1}` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC(SET_RULE `!a b (x:real^2). a SUBSET b /\ x IN a ==> x IN b`) THEN
      EXISTS_TAC `convex hull {p2:real^2,q2}` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(h:real^N->real^3) y`; `e1:real^3`; `e2:real^3`;
                 `a1:real^3`; `a2:real^3`] MOI_LGB2_MODEL_M4) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `f':real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`x1:real^2`; `x2:real^2`; `d1:real`; `d2:real`]
    MOI_LGB2_TWO_BALLS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `N1 = std_triangle INTER ball(x1:real^2,d)` THEN
  ABBREV_TAC `N2 = std_triangle INTER ball(x2:real^2,d)` THEN
  SUBGOAL_THEN `(N1:real^2->bool) SUBSET convex hull {p1,q1,w1} /\
                (N2:real^2->bool) SUBSET convex hull {p2,q2,w2}`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["N1"; "N2"] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_BALL] THEN CONJ_TAC THEN
    X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      (can (find_term ((=) `d1:real`)) (concl th) ||
       can (find_term ((=) `d2:real`)) (concl th)) &&
      not (can (find_term ((=) `z':real^2`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `f':real^3->real^3`; `h:real^N->real^3`;
                 `g:real^2->real^N`; `la1:real^2->real^3`; `ba1:real^3`;
                 `p1:real^2`; `q1:real^2`; `w1:real^2`; `mu1:real`; `x1:real^2`;
                 `d:real`; `1`] MOI_LGB2_BD_ETA) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ARITH; VECTOR_SUB_COMPONENT; REAL_SUB_RZERO]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `f':real^3->real^3`; `h:real^N->real^3`;
                 `g:real^2->real^N`; `la2:real^2->real^3`; `ba2:real^3`;
                 `p2:real^2`; `q2:real^2`; `w2:real^2`; `mu2:real`; `x2:real^2`;
                 `d:real`; `2`] MOI_LGB2_BD_ETA) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ARITH; VECTOR_SUB_COMPONENT; REAL_SUB_RZERO]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta2:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!x. x IN N1 ==> ((f:real^3->real^3)((h:real^N->real^3)((g:real^2->real^N) x)))$1 =
                    &0`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    MP_TAC(BETA_RULE(ISPECL [`\z:real^2. (h:real^N->real^3)((g:real^2->real^N) z)`;
      `la1:real^2->real^3`; `ba1:real^3`; `p1:real^2`; `q1:real^2`;
      `w1:real^2`; `x1:real^2`; `x:real^2`] MOI_LGB2_TRI_PARAM)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real` (X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN N2 ==> ((f:real^3->real^3)((h:real^N->real^3)((g:real^2->real^N) x)))$2 =
                    &0`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    MP_TAC(BETA_RULE(ISPECL [`\z:real^2. (h:real^N->real^3)((g:real^2->real^N) z)`;
      `la2:real^2->real^3`; `ba2:real^3`; `p2:real^2`; `q2:real^2`;
      `w2:real^2`; `x2:real^2`; `x:real^2`] MOI_LGB2_TRI_PARAM)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real` (X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_LGB2_FINISH_BD THEN
  MAP_EVERY EXISTS_TAC [`x1:real^2`; `x2:real^2`; `u:real^N->bool`;
                        `h:real^N->real^3`; `h':real^3->real^N`;
                        `f:real^3->real^3`; `f':real^3->real^3`;
                        `N1:real^2->bool`; `N2:real^2->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXPAND_TAC ["N1"; "N2"] THEN
  SIMP_TAC[OPEN_IN_OPEN_INTER; OPEN_BALL] THEN
  ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY EXPAND_TAC ["N1"; "N2"] THEN
    UNDISCH_TAC `DISJOINT (ball(x1:real^2,d)) (ball(x2,d))` THEN SET_TAC[];
    UNDISCH_TAC `(N1:real^2->bool) SUBSET convex hull {p1,q1,w1}` THEN
    UNDISCH_TAC `IMAGE (g:real^2->real^N) (convex hull {p1,q1,w1}) SUBSET u` THEN
    SET_TAC[];
    UNDISCH_TAC `(N2:real^2->bool) SUBSET convex hull {p2,q2,w2}` THEN
    UNDISCH_TAC `IMAGE (g:real^2->real^N) (convex hull {p2,q2,w2}) SUBSET u` THEN
    SET_TAC[];
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `d1:real`)) (concl th) &&
      can (find_term ((=) `z':real^2`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^2) IN ball(x1,d)` THEN
    UNDISCH_TAC `(x':real^2) IN ball(x1,d)` THEN REWRITE_TAC[IN_BALL] THEN
    MP_TAC(ISPECL [`x:real^2`; `x1:real^2`] DIST_SYM) THEN
    MP_TAC(ISPECL [`x':real^2`; `x1:real^2`] DIST_SYM) THEN
    ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `d2:real`)) (concl th) &&
      can (find_term ((=) `z':real^2`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^2) IN ball(x2,d)` THEN
    UNDISCH_TAC `(x':real^2) IN ball(x2,d)` THEN REWRITE_TAC[IN_BALL] THEN
    MP_TAC(ISPECL [`x:real^2`; `x2:real^2`] DIST_SYM) THEN
    MP_TAC(ISPECL [`x':real^2`; `x2:real^2`] DIST_SYM) THEN
    ASM_REAL_ARITH_TAC;
    EXISTS_TAC `eta1:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(SET_RULE `!(f:real^2->real^3) a b z.
      a SUBSET b /\ z IN IMAGE f a ==> z IN IMAGE f b`) THEN
    EXISTS_TAC `ball(x1:real^2,d) INTER convex hull {p1,q1,w1}` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "N1" THEN
      SUBGOAL_THEN `convex hull {p1:real^2,q1,w1} SUBSET std_triangle` MP_TAC THENL
       [UNDISCH_TAC `UNIONS L = std_triangle` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        UNDISCH_TAC `convex hull {p1:real^2,q1,w1} IN L` THEN SET_TAC[];
        SET_TAC[]];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    EXISTS_TAC `eta2:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(SET_RULE `!(f:real^2->real^3) a b z.
      a SUBSET b /\ z IN IMAGE f a ==> z IN IMAGE f b`) THEN
    EXISTS_TAC `ball(x2:real^2,d) INTER convex hull {p2,q2,w2}` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "N2" THEN
      SUBGOAL_THEN `convex hull {p2:real^2,q2,w2} SUBSET std_triangle` MP_TAC THENL
       [UNDISCH_TAC `UNIONS L = std_triangle` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        UNDISCH_TAC `convex hull {p2:real^2,q2,w2} IN L` THEN SET_TAC[];
        SET_TAC[]];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* ========================================================================= *)
(* A map T-generic on a neighbourhood of a double point has a               *)
(* crossing with open sheets there (the local models M1-M4).                *)
(* ========================================================================= *)

let MOI_LGB2_CROSSING = prove
 (`!(c:(real^N->bool)->bool) (tt:(real^N->bool)->bool)
    (A:((real^N->bool)#(real^N->real^3)#(real^3->real^N)#(real^N->bool))->bool)
    u h h' kk (L:(real^2->bool)->bool) (g:real^2->real^N) Q y.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\ moi_lgb_atlas c tt A /\
     (u,h,h',kk) IN A /\ y IN kk /\
     moi_lt_singular_disk c g /\ moi_lgb_tgeneric tt L g Q /\ y IN Q /\
     y IN moi_lt_double_image g
     ==> moi_lt_crossing2_at c g y`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_LGB2_SETUP) THEN
  DISCH_THEN(X_CHOOSE_THEN `x1:real^2` (X_CHOOSE_THEN `x2:real^2`
    (X_CHOOSE_THEN `sigma:real^N->bool` (X_CHOOSE_THEN `rho1:real^2->bool`
      (X_CHOOSE_THEN `rho2:real^2->bool` ASSUME_TAC))))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_LGB2_DIMS) THEN
  STRIP_TAC THENL
   [MATCH_MP_TAC MOI_LGB2_CASE_TT THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `u:real^N->bool`;
                          `h:real^N->real^3`; `h':real^3->real^N`;
                          `L:(real^2->bool)->bool`; `Q:real^N->bool`;
                          `x1:real^2`; `x2:real^2`; `sigma:real^N->bool`;
                          `rho1:real^2->bool`; `rho2:real^2->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_LGB2_CASE_ET THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `u:real^N->bool`;
                          `h:real^N->real^3`; `h':real^3->real^N`;
                          `L:(real^2->bool)->bool`; `Q:real^N->bool`;
                          `x1:real^2`; `x2:real^2`; `sigma:real^N->bool`;
                          `rho1:real^2->bool`; `rho2:real^2->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_LGB2_CASE_ET THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `u:real^N->bool`;
                          `h:real^N->real^3`; `h':real^3->real^N`;
                          `L:(real^2->bool)->bool`; `Q:real^N->bool`;
                          `x2:real^2`; `x1:real^2`; `sigma:real^N->bool`;
                          `rho2:real^2->bool`; `rho1:real^2->bool`] THEN
    ASM_SIMP_TAC[MOI_LGB2_CTX_SWAP];
    ASM_CASES_TAC `(y:real^N) IN complex_boundary c` THENL
     [MATCH_MP_TAC MOI_LGB2_CASE_WB; MATCH_MP_TAC MOI_LGB2_CASE_WI] THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `u:real^N->bool`;
                          `h:real^N->real^3`; `h':real^3->real^N`;
                          `L:(real^2->bool)->bool`; `Q:real^N->bool`;
                          `x1:real^2`; `x2:real^2`; `sigma:real^N->bool`;
                          `rho1:real^2->bool`; `rho2:real^2->bool`] THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The start: a simplicial disk into t is tlinear on the pulled-            *)
(* back triangulation when tt refines t over its image.                     *)
(* ========================================================================= *)

let MOI_LGB2_START = prove
 (`!(c:(real^N->bool)->bool) (t:(real^N->bool)->bool) (tt:(real^N->bool)->bool)
    (k:(real^2->bool)->bool) (f:real^2->real^N).
     simplicial_complex k /\ UNIONS k = std_triangle /\ simplicial_map_on k t f /\
     moi_lt_singular_disk c f /\ simplicial_complex tt /\
     (!s'. s' IN t ==> ?d. d SUBSET tt /\ UNIONS d = s' INTER UNIONS tt) /\
     IMAGE f std_triangle SUBSET UNIONS tt
     ==> ?L0. moi_lgb_tlinear tt L0 f`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `moi_lga_pullback (k:(real^2->bool)->bool) (tt:(real^N->bool)->bool)
                               (f:real^2->real^N)` THEN
  MATCH_MP_TAC MOI_LGB_TLINEAR_SIMPLICIAL THEN
  MP_TAC(ISPECL [`k:(real^2->bool)->bool`; `tt:(real^N->bool)->bool`;
                 `f:real^2->real^N`] MOI_LGA_PULLBACK_COMPLEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `simplicial_map_on k t (f:real^2->real^N)` THEN
      REWRITE_TAC[simplicial_map_on] THEN MESON_TAC[];
      MAP_EVERY X_GEN_TAC [`s:real^2->bool`; `x:real^2`; `y:real^2`] THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `?l b. linear l /\ !x. x IN s ==> (f:real^2->real^N) x = l x + b`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `simplicial_map_on k t (f:real^2->real^N)` THEN
        REWRITE_TAC[simplicial_map_on] THEN
        DISCH_THEN(MP_TAC o SPEC `s:real^2->bool`) THEN ASM_SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(s:real^2->bool) SUBSET std_triangle` ASSUME_TAC THENL
       [UNDISCH_TAC `UNIONS k = std_triangle` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        UNDISCH_TAC `(s:real^2->bool) IN k` THEN SET_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`f:real^2->real^N`; `l:real^2->real^N`; `b:real^N`;
                     `s:real^2->bool`; `std_triangle`] MOI_LGA_AFFINE_LOCAL_INJ) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [ASM_MESON_TAC[MOI_FMB_SC_LF; MOI_FM3_LF_CONVEX]; ALL_TAC] THEN
        X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
        UNDISCH_TAC `moi_lt_singular_disk c (f:real^2->real^N)` THEN
        REWRITE_TAC[moi_lt_singular_disk] THEN
        DISCH_THEN(MP_TAC o SPEC `z:real^2` o CONJUNCT1 o CONJUNCT2 o
                   CONJUNCT2 o CONJUNCT2) THEN
        ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      X_GEN_TAC `s:real^2->bool` THEN DISCH_TAC THEN
      SUBGOAL_THEN `IMAGE (f:real^2->real^N) s IN t` ASSUME_TAC THENL
       [UNDISCH_TAC `simplicial_map_on k t (f:real^2->real^N)` THEN
        REWRITE_TAC[simplicial_map_on] THEN
        DISCH_THEN(MP_TAC o SPEC `s:real^2->bool`) THEN ASM_SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `IMAGE (f:real^2->real^N) s SUBSET UNIONS tt` ASSUME_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `IMAGE (f:real^2->real^N) std_triangle` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
        UNDISCH_TAC `UNIONS k = std_triangle` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        UNDISCH_TAC `(s:real^2->bool) IN k` THEN SET_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `!s'. s' IN t ==> ?d. d SUBSET tt /\
                                        UNIONS d = s' INTER UNIONS (tt:(real^N->bool)->bool)` THEN
      DISCH_THEN(MP_TAC o SPEC `IMAGE (f:real^2->real^N) s`) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `IMAGE (f:real^2->real^N) s INTER UNIONS tt = IMAGE f s`
      SUBST1_TAC THENL [ASM SET_TAC[]; MESON_TAC[]]];
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Iterating the chart step over the finite atlas.                          *)
(* ========================================================================= *)

let MOI_LGB2_HOMOTOPIC_REFL = prove
 (`!(f:real^2->real^N) w.
     f continuous_on std_triangle /\
     IMAGE f (relative_frontier std_triangle) SUBSET w
     ==> homotopic_loops w (f o std_triangle_loop) (f o std_triangle_loop)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HOMOTOPIC_LOOPS_REFL] THEN
  REWRITE_TAC[PATH_IMAGE_COMPOSE; PATHSTART_COMPOSE; PATHFINISH_COMPOSE;
              MOI_LTD_STD_TRIANGLE_LOOP] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN
  REWRITE_TAC[MOI_LTD_STD_TRIANGLE_LOOP] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
  ASM_REWRITE_TAC[MOI_LTD_FRONTIER_SUBSET_TRIANGLE]);;

let MOI_LGB2_CORES_CLOSED = prove
 (`!(c:(real^N->bool)->bool) tt
    (A:((real^N->bool)#(real^N->real^3)#(real^3->real^N)#(real^N->bool))->bool) B.
     moi_lgb_atlas c tt A /\ B SUBSET A
     ==> closed (UNIONS (IMAGE (\p. SND(SND(SND p))) B))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
  MATCH_MP_TAC COMPACT_UNIONS THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `A:((real^N->bool)#(real^N->real^3)#(real^3->real^N)#(real^N->bool))->bool` THEN
    ASM_MESON_TAC[moi_lgb_atlas];
    REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                         `kk:real^N->bool`] THEN
    DISCH_TAC THEN
    UNDISCH_TAC `moi_lgb_atlas c tt
       (A:((real^N->bool)#(real^N->real^3)#(real^3->real^N)#(real^N->bool))->bool)` THEN
    REWRITE_TAC[moi_lgb_atlas] THEN
    DISCH_THEN(MP_TAC o SPECL [`u:real^N->bool`; `h:real^N->real^3`;
                               `h':real^3->real^N`; `kk:real^N->bool`] o
               CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]]]);;

let MOI_LGB2_ITERATE = prove
 (mk_imp(MOI_LGB_CHART_STEP,
  `!(c:(real^N->bool)->bool) (tt:(real^N->bool)->bool)
     (A:((real^N->bool)#(real^N->real^3)#(real^3->real^N)#(real^N->bool))->bool)
     (L0:(real^2->bool)->bool) (f:real^2->real^N) w e.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\ moi_lgb_atlas c tt A /\
     moi_lt_singular_disk c f /\ moi_lgb_tlinear tt L0 f /\
     open_in (subtopology euclidean (complex_boundary c)) w /\
     IMAGE f (relative_frontier std_triangle) SUBSET w /\ &0 < e
     ==> ?g L. moi_lt_singular_disk c g /\
               moi_lgb_tgeneric tt L g (UNIONS (IMAGE (\p. SND(SND(SND p))) A)) /\
               (!x. x IN std_triangle ==> dist(g x,f x) < e) /\
               IMAGE g (relative_frontier std_triangle) SUBSET w /\
               homotopic_loops w (f o std_triangle_loop) (g o std_triangle_loop)`),
  DISCH_THEN(LABEL_TAC "step") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `FINITE (A:((real^N->bool)#(real^N->real^3)#(real^3->real^N)#(real^N->bool))->bool)`
  ASSUME_TAC THENL [ASM_MESON_TAC[moi_lgb_atlas]; ALL_TAC] THEN
  ABBREV_TAC
   `e0 = e / (&(CARD (A:((real^N->bool)#(real^N->real^3)#(real^3->real^N)#
                         (real^N->bool))->bool)) + &1)` THEN
  SUBGOAL_THEN
   `&0 < e0 /\
    (&(CARD (A:((real^N->bool)#(real^N->real^3)#(real^3->real^N)#
                (real^N->bool))->bool)) + &1) * e0 = e`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e0" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `CARD (A:((real^N->bool)#(real^N->real^3)#(real^3->real^N)#
                           (real^N->bool))->bool)` REAL_POS) THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_DIV_LMUL THEN
      MP_TAC(SPEC `CARD (A:((real^N->bool)#(real^N->real^3)#(real^3->real^N)#
                           (real^N->bool))->bool)` REAL_POS) THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^2->real^N) continuous_on std_triangle` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN
    ASM_MESON_TAC[moi_lt_singular_disk];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!B. FINITE B
        ==> B SUBSET (A:((real^N->bool)#(real^N->real^3)#(real^3->real^N)#
                         (real^N->bool))->bool)
            ==> ?g L. moi_lt_singular_disk c g /\
                      moi_lgb_tgeneric tt L g (UNIONS (IMAGE (\p. SND(SND(SND p))) B)) /\
                      (!x. x IN std_triangle
                           ==> dist((g:real^2->real^N) x,f x) <= &(CARD B) * e0) /\
                      IMAGE g (relative_frontier std_triangle) SUBSET w /\
                      homotopic_loops w (f o std_triangle_loop) (g o std_triangle_loop)`
  MP_TAC THENL
   [MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
     [DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [`f:real^2->real^N`; `L0:(real^2->bool)->bool`] THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; UNIONS_0; CARD_CLAUSES; DIST_REFL;
                      REAL_MUL_LZERO; REAL_LE_REFL] THEN
      ASM_SIMP_TAC[MOI_LGB_TGENERIC_EMPTY; MOI_LGB2_HOMOTOPIC_REFL];
      ALL_TAC] THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                         `kk:real^N->bool`;
                         `B:((real^N->bool)#(real^N->real^3)#(real^3->real^N)#
                             (real^N->bool))->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^2->real^N` (X_CHOOSE_THEN `L:(real^2->bool)->bool`
      STRIP_ASSUME_TAC)) THEN
    USE_THEN "step" (MP_TAC o SPECL
     [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
      `A:((real^N->bool)#(real^N->real^3)#(real^3->real^N)#(real^N->bool))->bool`;
      `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
      `L:(real^2->bool)->bool`; `g:real^2->real^N`;
      `UNIONS (IMAGE (\p. SND(SND(SND p)))
         (B:((real^N->bool)#(real^N->real^3)#(real^3->real^N)#(real^N->bool))->bool))`;
      `w:real^N->bool`; `e0:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MOI_LGB2_CORES_CLOSED THEN
      MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
        `A:((real^N->bool)#(real^N->real^3)#(real^3->real^N)#(real^N->bool))->bool`] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `g':real^2->real^N` (X_CHOOSE_THEN `L':(real^2->bool)->bool`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`g':real^2->real^N`; `L':(real^2->bool)->bool`] THEN
    REWRITE_TAC[IMAGE_CLAUSES; UNIONS_INSERT] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[SND] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ONCE_REWRITE_TAC[UNION_COMM] THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[CARD_CLAUSES; GSYM REAL_OF_NUM_SUC] THEN
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH
       `!n a b d. d <= a + b /\ a < e0 /\ b <= n * e0 ==> d <= (n + &1) * e0`) THEN
      MAP_EVERY EXISTS_TAC [`dist((g':real^2->real^N) x,g x)`;
                            `dist((g:real^2->real^N) x,f x)`] THEN
      ASM_SIMP_TAC[DIST_TRIANGLE];
      MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
      EXISTS_TAC `(g:real^2->real^N) o std_triangle_loop` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC
   `A:((real^N->bool)#(real^N->real^3)#(real^3->real^N)#(real^N->bool))->bool`) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^2->real^N` (X_CHOOSE_THEN `L:(real^2->bool)->bool`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`g:real^2->real^N`; `L:(real^2->bool)->bool`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `&(CARD (A:((real^N->bool)#(real^N->real^3)#(real^3->real^N)#
                         (real^N->bool))->bool)) * e0` THEN
  ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `!n. (n + &1) * e0 = e /\ &0 < e0 ==> n * e0 < e`) THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The main theorem GP_FROM_STEP: the atlas around the image, the start,    *)
(* the iteration, and the crossings at the double points.                   *)
(* ========================================================================= *)

let GP_FROM_STEP = prove
 (MOI_LGB_GP_FROM_STEP,
  DISCH_THEN(LABEL_TAC "step") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `compact (IMAGE (f:real^2->real^N) std_triangle) /\
    IMAGE f std_triangle SUBSET UNIONS c`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      REWRITE_TAC[MOI_LTD_STD_TRIANGLE_BASIC] THEN
      MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN
      ASM_MESON_TAC[moi_lt_singular_disk];
      ASM_MESON_TAC[moi_lt_singular_disk]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:(real^N->bool)->bool`;
                 `IMAGE (f:real^2->real^N) std_triangle`] MOI_LGB2_ATLAS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `tt:(real^N->bool)->bool` (X_CHOOSE_THEN
   `A:((real^N->bool)#(real^N->real^3)#(real^3->real^N)#(real^N->bool))->bool`
   (X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cov")))))))) THEN
  SUBGOAL_THEN
   `!x y. x IN UNIONS c /\ y IN IMAGE (f:real^2->real^N) std_triangle /\ dist(x,y) < r
          ==> x IN UNIONS (IMAGE (\p. SND(SND(SND p)))
                 (A:((real^N->bool)#(real^N->real^3)#(real^3->real^N)#
                     (real^N->bool))->bool)) /\
              x IN UNIONS tt`
  (LABEL_TAC "cov2") THENL
   [MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN DISCH_TAC THEN
    USE_THEN "cov" (MP_TAC o SPECL [`x:real^N`; `y:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `h:real^N->real^3`
      (X_CHOOSE_THEN `h':real^3->real^N` (X_CHOOSE_THEN `kk:real^N->bool`
        STRIP_ASSUME_TAC)))) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_UNIONS; IN_IMAGE] THEN EXISTS_TAC `kk:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `(u:real^N->bool,h:real^N->real^3,h':real^3->real^N,kk:real^N->bool)` THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `moi_lgb_atlas c tt
        (A:((real^N->bool)#(real^N->real^3)#(real^3->real^N)#(real^N->bool))->bool)` THEN
      REWRITE_TAC[moi_lgb_atlas] THEN
      DISCH_THEN(MP_TAC o SPECL [`u:real^N->bool`; `h:real^N->real^3`;
                                 `h':real^3->real^N`; `kk:real^N->bool`] o
                 CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^2->real^N) std_triangle SUBSET UNIONS tt` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    USE_THEN "cov2" (MP_TAC o SPECL [`z:real^N`; `z:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[DIST_REFL] THEN ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_complex (tt:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_lgb_atlas]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:(real^N->bool)->bool`;
                 `tt:(real^N->bool)->bool`; `k:(real^2->bool)->bool`;
                 `f:real^2->real^N`] MOI_LGB2_START) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `L0:(real^2->bool)->bool`) THEN
  USE_THEN "step" (fun th -> MP_TAC(ISPECL
    [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
     `A:((real^N->bool)#(real^N->real^3)#(real^3->real^N)#(real^N->bool))->bool`;
     `L0:(real^2->bool)->bool`; `f:real^2->real^N`; `w:real^N->bool`; `r / &2`]
    (MP MOI_LGB2_ITERATE th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^2->real^N` (X_CHOOSE_THEN `L:(real^2->bool)->bool`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `g:real^2->real^N` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  UNDISCH_TAC `(y:real^N) IN moi_lt_double_image g` THEN
  REWRITE_TAC[moi_lt_double_image; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^2` (X_CHOOSE_THEN `x':real^2` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(y:real^N) IN UNIONS c` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lt_singular_disk c (g:real^2->real^N)` THEN
    REWRITE_TAC[moi_lt_singular_disk] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `dist(y:real^N,(f:real^2->real^N) x) < r` ASSUME_TAC THENL
   [UNDISCH_TAC `(g:real^2->real^N) x = y` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `r / &2` THEN
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "cov" (MP_TAC o SPECL [`y:real^N`; `(f:real^2->real^N) x`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `h:real^N->real^3`
    (X_CHOOSE_THEN `h':real^3->real^N` (X_CHOOSE_THEN `kk:real^N->bool`
      STRIP_ASSUME_TAC)))) THEN
  MATCH_MP_TAC MOI_LGB2_CROSSING THEN
  MAP_EVERY EXISTS_TAC
   [`tt:(real^N->bool)->bool`;
    `A:((real^N->bool)#(real^N->real^3)#(real^3->real^N)#(real^N->bool))->bool`;
    `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
    `L:(real^2->bool)->bool`;
    `UNIONS (IMAGE (\p. SND(SND(SND p)))
       (A:((real^N->bool)#(real^N->real^3)#(real^3->real^N)#(real^N->bool))->bool))`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_UNIONS; IN_IMAGE] THEN EXISTS_TAC `kk:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `(u:real^N->bool,h:real^N->real^3,h':real^3->real^N,kk:real^N->bool)` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[moi_lt_double_image; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`x:real^2`; `x':real^2`] THEN ASM_REWRITE_TAC[]]);;

