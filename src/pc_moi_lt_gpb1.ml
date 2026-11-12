(* ========================================================================= *)
(* pc_moi_lt_gpb1: the chart step of the loop theorem, CHART_STEP :          *)
(* |- MOI_LGB_CHART_STEP (pc_moi_lt_gpbstmt.ml).  Builds on pc_moi_lt_gpb1a  *)
(* (Euclidean tools) and pc_moi_lt_gpb1b (cut complex and cone             *)
(* triangulation).  Route: single-vertex generic moves of the vertices of   *)
(* the simplices meeting the core, in chart coordinates (boundary vertices *)
(* first, inside z3 = 0); the moved map is refined along the chart image of *)
(* tt (cells, cones from generic cone points); genericity at Q UNION kk by  *)
(* the last-mover argument, the singular-disk clauses by smallness          *)
(* (MOI_LGB1_STAR_STABLE, MOI_LGB1_TWO_TO_ONE).                             *)
(* The boundary homotopy is MOI_LGB1H_HTPY of pc_moi_lt_gpb1h.              *)
(* ========================================================================= *)

needs "src/pc_moi_lt_gpb1b.ml";;
needs "src/pc_moi_lt_gpb1h.ml";;
needs "src/pc_moi_fnd_m3a.ml";;
needs "src/pc_moi_lt_gpa.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* C1. Generic single-vertex moves.  The movers are processed one at a time *)
(* (boundary movers first); each new position avoids every affine hull of  *)
(* a subset of the points xc of the current configuration (vertex values,   *)
(* the vertices of the chart complex, and affine bases of the intersections *)
(* of two such hulls) that does not contain its space (univ, or z3 = 0 for  *)
(* boundary movers).                                                         *)
(* ------------------------------------------------------------------------- *)

let moi_lgb1_basis = new_definition
 `moi_lgb1_basis (s:real^N->bool) =
    @b. ~affine_dependent b /\ b SUBSET s /\ affine hull b = affine hull s`;;

let MOI_LGB1_BASIS = prove
 (`!s:real^N->bool.
     ~affine_dependent (moi_lgb1_basis s) /\ FINITE (moi_lgb1_basis s) /\
     moi_lgb1_basis s SUBSET s /\ affine hull (moi_lgb1_basis s) = affine hull s`,
  GEN_TAC THEN
  MP_TAC(SELECT_RULE(ISPEC `s:real^N->bool` AFFINE_BASIS_EXISTS)) THEN
  REWRITE_TAC[GSYM moi_lgb1_basis] THEN
  MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]);;

let moi_lgb1_xc = new_definition
 `moi_lgb1_xc (psi:real^2->real^3) (V:real^2->bool) (HV:real^3->bool) =
    (IMAGE psi V UNION HV) UNION
    UNIONS {moi_lgb1_basis (affine hull Y1 INTER affine hull Y2) | Y1,Y2 |
            Y1 SUBSET (IMAGE psi V UNION HV) /\ Y2 SUBSET (IMAGE psi V UNION HV)}`;;

let MOI_LGB1_XC_FINITE = prove
 (`!(psi:real^2->real^3) V HV.
     FINITE V /\ FINITE HV ==> FINITE (moi_lgb1_xc psi V HV)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_lgb1_xc; FINITE_UNION] THEN
  ASM_SIMP_TAC[FINITE_IMAGE] THEN REWRITE_TAC[FINITE_UNIONS] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC
     `IMAGE (\(Y1,Y2). moi_lgb1_basis (affine hull Y1 INTER affine hull (Y2:real^3->bool)))
            ({Y | Y SUBSET (IMAGE (psi:real^2->real^3) V UNION HV)} CROSS
             {Y | Y SUBSET (IMAGE (psi:real^2->real^3) V UNION HV)})` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_CROSS THEN
      ASM_SIMP_TAC[FINITE_POWERSET; FINITE_UNION; FINITE_IMAGE];
      REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_IMAGE; EXISTS_PAIR_THM; IN_CROSS;
                  IN_ELIM_THM] THEN MESON_TAC[]];
    REWRITE_TAC[FORALL_IN_GSPEC; MOI_LGB1_BASIS]]);;

let MOI_LGB1_XC_INTER = prove
 (`!(psi:real^2->real^3) V HV Y1 Y2.
     Y1 SUBSET (IMAGE psi V UNION HV) /\ Y2 SUBSET (IMAGE psi V UNION HV)
     ==> ?B. B SUBSET moi_lgb1_xc psi V HV /\
             affine hull B = affine hull Y1 INTER affine hull Y2`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `moi_lgb1_basis (affine hull Y1 INTER affine hull (Y2:real^3->bool))` THEN
  REWRITE_TAC[MOI_LGB1_BASIS] THEN CONJ_TAC THENL
   [REWRITE_TAC[moi_lgb1_xc] THEN MATCH_MP_TAC(SET_RULE
     `(s:real^3->bool) SUBSET u ==> s SUBSET t UNION u`) THEN
    MATCH_MP_TAC(SET_RULE `(s:real^3->bool) IN c ==> s SUBSET UNIONS c`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`Y1:real^3->bool`; `Y2:real^3->bool`] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[AFFINE_HULL_EQ] THEN SIMP_TAC[AFFINE_INTER; AFFINE_AFFINE_HULL]]);;

let moi_lgb1_at = new_definition
 `moi_lgb1_at (rk:real^2->num) KV (phi0:real^2->real^3) phi p =
    \v. if v IN KV /\ rk p <= rk v then phi0 v else phi v`;;

let moi_lgb1_space = new_definition
 `moi_lgb1_space B (v:real^2) =
    if v IN B then {z:real^3 | z$3 = &0} else (:real^3)`;;

let MOI_LGB1_SPACE_AFFINE = prove
 (`!B v:real^2. affine (moi_lgb1_space B v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lgb1_space] THEN COND_CASES_TAC THEN
  REWRITE_TAC[AFFINE_UNIV] THEN
  SUBGOAL_THEN `{z:real^3 | z$3 = &0} = {z | basis 3 dot z = &0}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
    SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH];
    REWRITE_TAC[AFFINE_HYPERPLANE]]);;

let MOI_LGB1_MOVE_STEP = prove
 (`!(V:real^2->bool) HV B (phi:real^2->real^3) (z0:real^3) v eta.
     FINITE V /\ FINITE HV /\ &0 < eta /\ z0 IN moi_lgb1_space B v
     ==> ?p. norm(p - z0) < eta /\ p IN moi_lgb1_space B v /\
             !Y. Y SUBSET moi_lgb1_xc phi V HV /\
                 ~(moi_lgb1_space B v SUBSET affine hull Y)
                 ==> ~(p IN affine hull Y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`moi_lgb1_space B (v:real^2)`; `moi_lgb1_xc phi V HV`;
                 `moi_lgb1_space B (v:real^2) INTER ball(z0:real^3,eta)`]
    MOI_LGB1_GEN_EXISTS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_LGB1_SPACE_AFFINE; MOI_LGB1_XC_FINITE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[OPEN_BALL];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `z0:real^3` THEN
      ASM_REWRITE_TAC[CENTRE_IN_BALL]];
    MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[IN_INTER; IN_BALL] THEN
    MESON_TAC[DIST_SYM; dist]]);;

let MOI_LGB1_ENUM_BFIRST = prove
 (`!(KV:real^2->bool) B.
     FINITE KV
     ==> ?(f:num->real^2) (N:num). (!i. i < N ==> f i IN KV) /\
               (!x. x IN KV ==> ?i. i < N /\ f i = x) /\
               (!i j. i < N /\ j < N /\ f i = f j ==> i = j) /\
               (!i j. i < N /\ j < N /\ f i IN B /\ ~(f j IN B) ==> i < j)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`KV INTER B:real^2->bool`; `CARD(KV INTER B:real^2->bool)`]
    HAS_SIZE_INDEX) THEN
  MP_TAC(ISPECL [`KV DIFF B:real^2->bool`; `CARD(KV DIFF B:real^2->bool)`]
    HAS_SIZE_INDEX) THEN
  ASM_SIMP_TAC[HAS_SIZE; FINITE_INTER; FINITE_DIFF] THEN
  DISCH_THEN(X_CHOOSE_THEN `f2:num->real^2` (CONJUNCTS_THEN2 (LABEL_TAC "f2in")
    (LABEL_TAC "f2un"))) THEN
  DISCH_THEN(X_CHOOSE_THEN `f1:num->real^2` (CONJUNCTS_THEN2 (LABEL_TAC "f1in")
    (LABEL_TAC "f1un"))) THEN
  ABBREV_TAC `n1 = CARD(KV INTER B:real^2->bool)` THEN
  ABBREV_TAC `n2 = CARD(KV DIFF B:real^2->bool)` THEN
  EXISTS_TAC `\i. if i < n1 then (f1:num->real^2) i else f2 (i - n1)` THEN
  EXISTS_TAC `n1 + n2:num` THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(!i. i < n1 ==> (f1:num->real^2) i IN KV /\ f1 i IN B) /\
    (!i. i < n1 + n2 /\ ~(i < n1) ==> (f2:num->real^2) (i - n1) IN KV /\
                                       ~(f2 (i - n1) IN B))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT STRIP_TAC THENL
     [USE_THEN "f1in" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SET_TAC[]];
      USE_THEN "f1in" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SET_TAC[]];
      USE_THEN "f2in" (MP_TAC o SPEC `i - n1:num`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; SET_TAC[]];
      USE_THEN "f2in" (MP_TAC o SPEC `i - n1:num`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[];
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN ASM_CASES_TAC `(x:real^2) IN B` THENL
     [USE_THEN "f1un" (MP_TAC o SPEC `x:real^2`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC o REWRITE_RULE[EXISTS_UNIQUE]) THEN
      EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      USE_THEN "f2un" (MP_TAC o SPEC `x:real^2`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[IN_DIFF]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC o REWRITE_RULE[EXISTS_UNIQUE]) THEN
      EXISTS_TAC `n1 + m:num` THEN
      ASM_REWRITE_TAC[ARITH_RULE `~(n1 + m < n1:num)`; ADD_SUB2] THEN ASM_ARITH_TAC];
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
    MAP_EVERY ASM_CASES_TAC [`(i:num) < n1`; `(j:num) < n1`] THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THENL
     [USE_THEN "f1un" (MP_TAC o SPEC `(f1:num->real^2) i`) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[IN_INTER]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPECL [`i:num`; `j:num`] o CONJUNCT2 o
                 REWRITE_RULE[EXISTS_UNIQUE_THM]) THEN
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN `(f1:num->real^2) i IN B /\ ~((f2:num->real^2) (j - n1) IN B)`
      MP_TAC THENL [ASM_SIMP_TAC[]; ASM_REWRITE_TAC[] THEN MESON_TAC[]];
      SUBGOAL_THEN `(f1:num->real^2) j IN B /\ ~((f2:num->real^2) (i - n1) IN B)`
      MP_TAC THENL [ASM_SIMP_TAC[]; ASM_REWRITE_TAC[] THEN MESON_TAC[]];
      USE_THEN "f2un" (MP_TAC o SPEC `(f2:num->real^2) (i - n1)`) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[IN_DIFF]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPECL [`i - n1:num`; `j - n1:num`] o CONJUNCT2 o
                 REWRITE_RULE[EXISTS_UNIQUE_THM]) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ASM_ARITH_TAC]];
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
    MAP_EVERY ASM_CASES_TAC [`(i:num) < n1`; `(j:num) < n1`] THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THENL
     [UNDISCH_TAC `~((f1:num->real^2) j IN B)` THEN ASM_SIMP_TAC[];
      ASM_ARITH_TAC;
      UNDISCH_TAC `(f2:num->real^2) (i - n1) IN B` THEN ASM_SIMP_TAC[];
      UNDISCH_TAC `(f2:num->real^2) (i - n1) IN B` THEN ASM_SIMP_TAC[]]]);;

let MOI_LGB1_MOVES = prove
 (`!(V:real^2->bool) KV B (phi0:real^2->real^3) HV eta.
     FINITE V /\ KV SUBSET V /\ FINITE HV /\ &0 < eta /\
     (!v. v IN KV /\ v IN B ==> phi0 v $3 = &0)
     ==> ?phi rk.
          (!v. ~(v IN KV) ==> phi v = phi0 v) /\
          (!v. v IN KV ==> norm(phi v - phi0 v) < eta /\ phi v IN moi_lgb1_space B v) /\
          (!v w. v IN KV /\ w IN KV /\ rk v = rk w ==> v = w) /\
          (!v w. v IN KV /\ w IN KV /\ v IN B /\ ~(w IN B) ==> rk v < rk w) /\
          (!p Y. p IN KV /\ Y SUBSET moi_lgb1_xc (moi_lgb1_at rk KV phi0 phi p) V HV /\
                 ~(moi_lgb1_space B p SUBSET affine hull Y)
                 ==> ~(phi p IN affine hull Y))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`KV:real^2->bool`; `B:real^2->bool`] MOI_LGB1_ENUM_BFIRST) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->real^2` (X_CHOOSE_THEN `N:num`
    (CONJUNCTS_THEN2 (LABEL_TAC "fin") (CONJUNCTS_THEN2 (LABEL_TAC "fon")
      (CONJUNCTS_THEN2 (LABEL_TAC "finj") (LABEL_TAC "fbf")))))) THEN
  ABBREV_TAC `tm = \(i:num) (phi:real^2->real^3) (v:real^2).
                     if ?j. i <= j /\ j < N /\ (f:num->real^2) j = v then phi0 v
                     else phi v` THEN
  SUBGOAL_THEN
   `!n. n <= N
        ==> ?phi:real^2->real^3.
              (!v. ~(?i. i < n /\ (f:num->real^2) i = v) ==> phi v = phi0 v) /\
              (!i. i < n ==> norm(phi(f i) - phi0(f i)) < eta /\
                             phi(f i) IN moi_lgb1_space B (f i)) /\
              (!i Y. i < n /\ Y SUBSET moi_lgb1_xc (tm i phi) V HV /\
                     ~(moi_lgb1_space B (f i) SUBSET affine hull Y)
                     ==> ~(phi(f i) IN affine hull Y))`
  MP_TAC THENL
   [INDUCT_TAC THENL
     [DISCH_TAC THEN EXISTS_TAC `phi0:real^2->real^3` THEN REWRITE_TAC[LT];
      ALL_TAC] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `phi:real^2->real^3` (CONJUNCTS_THEN2 (LABEL_TAC "u")
      (CONJUNCTS_THEN2 (LABEL_TAC "s") (LABEL_TAC "g")))) THEN
    SUBGOAL_THEN `n < N /\ (f:num->real^2) n IN KV` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_ARITH_TAC; USE_THEN "fin" MATCH_MP_TAC THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`V:real^2->bool`; `HV:real^3->bool`; `B:real^2->bool`;
                   `phi:real^2->real^3`; `(phi0:real^2->real^3)((f:num->real^2) n)`;
                   `(f:num->real^2) n`; `eta:real`] MOI_LGB1_MOVE_STEP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[moi_lgb1_space] THEN COND_CASES_TAC THEN
      REWRITE_TAC[IN_UNIV; IN_ELIM_THM] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `!i. i < n ==> ~((f:num->real^2) i = f n)` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      USE_THEN "finj" (MP_TAC o SPECL [`i:num`; `n:num`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `!v. (?j. n <= j /\ j < N /\ (f:num->real^2) j = v)
                      ==> (phi:real^2->real^3) v = phi0 v`
    ASSUME_TAC THENL
     [GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
      USE_THEN "u" MATCH_MP_TAC THEN
      DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
      USE_THEN "finj" (MP_TAC o SPECL [`i:num`; `j:num`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
      ALL_TAC] THEN
    EXISTS_TAC `\v. if v = (f:num->real^2) n then p else (phi:real^2->real^3) v` THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `v:real^2` THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(v = (f:num->real^2) n)` (fun th -> REWRITE_TAC[th]) THENL
       [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
        REWRITE_TAC[] THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
        USE_THEN "u" MATCH_MP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
        MESON_TAC[ARITH_RULE `i < n ==> i < SUC n`]];
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      ASM_CASES_TAC `i:num = n` THENL
       [ASM_REWRITE_TAC[];
        SUBGOAL_THEN `(i:num) < n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[]];
      MAP_EVERY X_GEN_TAC [`i:num`; `Y:real^3->bool`] THEN STRIP_TAC THEN
      ASM_CASES_TAC `i:num = n` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `Y SUBSET moi_lgb1_xc ((tm:num->(real^2->real^3)->real^2->real^3) n
                       (\v. if v = (f:num->real^2) n then p else phi v)) V HV` THEN
        MATCH_MP_TAC(SET_RULE `s = t ==> (Y:real^3->bool) SUBSET s ==> Y SUBSET t`) THEN
        AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        EXPAND_TAC "tm" THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `w:real^2` THEN
        COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
        MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
        EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[LE_REFL];
        SUBGOAL_THEN `(i:num) < n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[] THEN USE_THEN "g" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `Y SUBSET moi_lgb1_xc ((tm:num->(real^2->real^3)->real^2->real^3) i
                       (\v. if v = (f:num->real^2) n then p else phi v)) V HV` THEN
        MATCH_MP_TAC(SET_RULE `s = t ==> (Y:real^3->bool) SUBSET s ==> Y SUBSET t`) THEN
        AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        EXPAND_TAC "tm" THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `w:real^2` THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
        MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
        EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `N:num`) THEN REWRITE_TAC[LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:real^2->real^3` (CONJUNCTS_THEN2 (LABEL_TAC "u")
    (CONJUNCTS_THEN2 (LABEL_TAC "s") (LABEL_TAC "g")))) THEN
  SUBGOAL_THEN `?rk:real^2->num. !v. v IN KV ==> rk v < N /\ (f:num->real^2) (rk v) = v`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `\v:real^2. @i. i < N /\ (f:num->real^2) i = v` THEN
    REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN CONV_TAC SELECT_CONV THEN
    USE_THEN "fon" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i < N ==> (rk:real^2->num) ((f:num->real^2) i) = i` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "finj" MATCH_MP_TAC THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`phi:real^2->real^3`; `rk:real^2->num`] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `v:real^2` THEN DISCH_TAC THEN USE_THEN "u" MATCH_MP_TAC THEN
    ASM_MESON_TAC[];
    X_GEN_TAC `v:real^2` THEN DISCH_TAC THEN
    USE_THEN "s" (MP_TAC o SPEC `(rk:real^2->num) v`) THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN USE_THEN "fbf" MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`q:real^2`; `Y:real^3->bool`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(rk:real^2->num) q < N /\ (f:num->real^2) (rk q) = q`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    USE_THEN "g" (MP_TAC o SPECL [`(rk:real^2->num) q`; `Y:real^3->bool`]) THEN
    MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p ==> q) ==> r`) THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `Y SUBSET moi_lgb1_xc (moi_lgb1_at rk KV phi0 (phi:real^2->real^3) q) V HV` THEN
    MATCH_MP_TAC(SET_RULE `s = t ==> (Y:real^3->bool) SUBSET s ==> Y SUBSET t`) THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    EXPAND_TAC "tm" THEN REWRITE_TAC[moi_lgb1_at; FUN_EQ_THM] THEN
    X_GEN_TAC `w:real^2` THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    EQ_TAC THENL
     [STRIP_TAC THEN EXISTS_TAC `(rk:real^2->num) w` THEN ASM_SIMP_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(w:real^2) IN KV` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]] THEN
      ASM_MESON_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* C2. The one-step dimension count of the last-mover argument: if p is     *)
(* generic for X (avoids every hull of a subset of X not containing S) and *)
(* a point z of Tz lies in conv(p INSERT R) but not in conv R, then the hull *)
(* of p, R and Tz contains S; with a base hypothesis for z in conv R.        *)
(* ------------------------------------------------------------------------- *)

let MOI_LGB1_AFF_UNION_EQ = prove
 (`!(R:real^N->bool) Tz B.
     affine hull B = affine hull Tz
     ==> affine hull (R UNION Tz) = affine hull (R UNION B)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
  MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[AFFINE_AFFINE_HULL; UNION_SUBSET] THEN
  (CONJ_TAC THENL [MESON_TAC[HULL_SUBSET; SUBSET_UNION; SUBSET_TRANS]; ALL_TAC]) THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `affine hull (B:real^N->bool)` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[HULL_SUBSET]; MATCH_MP_TAC HULL_MONO THEN SET_TAC[]];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `affine hull (Tz:real^N->bool)` THEN
    CONJ_TAC THENL [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[HULL_SUBSET];
                    MATCH_MP_TAC HULL_MONO THEN SET_TAC[]]]);;

let MOI_LGB1_GEN_HULL = prove
 (`!(S:real^N->bool) X (p:real^N) R Tz.
     (!Y. Y SUBSET X /\ ~(S SUBSET affine hull Y) ==> ~(p IN affine hull Y)) /\
     R SUBSET X /\ (?B. B SUBSET X /\ affine hull B = affine hull Tz) /\
     p IN affine hull (R UNION Tz)
     ==> S SUBSET affine hull (R UNION Tz)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "gen") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `B:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
  SUBGOAL_THEN `affine hull (R UNION Tz) = affine hull (R UNION B:real^N->bool)`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC MOI_LGB1_AFF_UNION_EQ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `~((p:real^N) IN affine hull (R UNION B))` MP_TAC THENL
   [USE_THEN "gen" MATCH_MP_TAC THEN ASM_REWRITE_TAC[UNION_SUBSET];
    ASM_REWRITE_TAC[]]);;

let MOI_LGB1_STEP = prove
 (`!(S:real^N->bool) X (p:real^N) R Tz z.
     (!Y. Y SUBSET X /\ ~(S SUBSET affine hull Y) ==> ~(p IN affine hull Y)) /\
     R SUBSET X /\ (?B. B SUBSET X /\ affine hull B = affine hull Tz) /\
     z IN convex hull (p INSERT R) /\ z IN Tz /\ ~(z IN convex hull R)
     ==> S SUBSET affine hull (p INSERT (R UNION Tz))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `affine hull (R UNION Tz:real^N->bool)` THEN
  CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC HULL_MONO THEN SET_TAC[]] THEN
  MATCH_MP_TAC MOI_LGB1_GEN_HULL THEN
  MAP_EVERY EXISTS_TAC [`X:real^N->bool`; `p:real^N`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `R:real^N->bool = {}` THENL
   [UNDISCH_TAC `(z:real^N) IN convex hull (p INSERT R)` THEN
    ASM_REWRITE_TAC[CONVEX_HULL_SING; IN_SING] THEN DISCH_THEN SUBST_ALL_TAC THEN
    MATCH_MP_TAC HULL_INC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(z:real^N) IN convex hull (p INSERT R)` THEN
  ASM_SIMP_TAC[CONVEX_HULL_INSERT; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` (X_CHOOSE_THEN `v:real` (X_CHOOSE_THEN `r:real^N`
    STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `~(u = &0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~((z:real^N) IN convex hull R)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `v = &1` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_LID; VECTOR_ADD_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `p:real^N = inv u % z + (&1 - inv u) % r` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `v = &1 - u` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; VECTOR_MUL_LID] THEN
    REWRITE_TAC[VECTOR_ARITH
     `(p:real^N) = (p + a % r) + b % r <=> (a + b) % r = vec 0`] THEN
    REWRITE_TAC[REAL_ARITH `iu * (&1 - u) + (&1 - iu) = &1 - iu * u`] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_SUB_REFL; VECTOR_MUL_LZERO];
    ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[affine] AFFINE_AFFINE_HULL) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HULL_INC THEN ASM SET_TAC[];
    SUBGOAL_THEN `convex hull R SUBSET affine hull (R UNION Tz:real^N->bool)` MP_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `affine hull R:real^N->bool` THEN
      REWRITE_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL] THEN MATCH_MP_TAC HULL_MONO THEN
      SET_TAC[];
      ASM SET_TAC[]];
    REAL_ARITH_TAC]);;

let MOI_LGB1_STEP_BASE = prove
 (`!(S:real^N->bool) X (p:real^N) R Tz.
     p IN S /\
     (!Y. Y SUBSET X /\ ~(S SUBSET affine hull Y) ==> ~(p IN affine hull Y)) /\
     R SUBSET X /\ (?B. B SUBSET X /\ affine hull B = affine hull Tz) /\
     (!q. q IN S /\ ~(q IN affine hull (R UNION Tz))
          ==> S SUBSET affine hull (q INSERT (R UNION Tz)))
     ==> S SUBSET affine hull (p INSERT (R UNION Tz))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `(p:real^N) IN affine hull (R UNION Tz)` THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `affine hull (R UNION Tz:real^N->bool)` THEN
    CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC HULL_MONO THEN SET_TAC[]] THEN
    MATCH_MP_TAC MOI_LGB1_GEN_HULL THEN
    MAP_EVERY EXISTS_TAC [`X:real^N->bool`; `p:real^N`] THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* C3. Affine-hull facts used by the genericity argument: the affine hull  *)
(* of an intersection of convex sets whose relative interiors meet; the    *)
(* modular law for affine hulls through a common point; a hyperplane z3 = 0 *)
(* plus a point off it spans everything; a mover of largest rank; a point  *)
(* of the relative interior of a simplex is off each facet.                 *)
(* ------------------------------------------------------------------------- *)

let MOI_LGB1_AFF_INTER_RELINT = prove
 (`!s t:real^N->bool.
     convex s /\ convex t /\
     ~(relative_interior s INTER relative_interior t = {})
     ==> affine hull (s INTER t) = affine hull s INTER affine hull t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `z:real^N` (CONJUNCTS_THEN MP_TAC)))) THEN
  REWRITE_TAC[IN_RELATIVE_INTERIOR] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`affine hull s INTER affine hull t:real^N->bool`;
                 `ball(z:real^N,min e1 e2)`] AFFINE_HULL_CONVEX_INTER_OPEN) THEN
  ANTS_TAC THENL
   [SIMP_TAC[CONVEX_INTER; AFFINE_IMP_CONVEX; AFFINE_AFFINE_HULL; OPEN_BALL] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `z:real^N` THEN
    ASM_SIMP_TAC[IN_INTER; HULL_INC; CENTRE_IN_BALL; REAL_LT_MIN];
    ALL_TAC] THEN
  SUBGOAL_THEN `affine hull (affine hull s INTER affine hull t) =
                affine hull s INTER affine hull (t:real^N->bool)` SUBST1_TAC THENL
   [MATCH_MP_TAC HULL_P THEN SIMP_TAC[AFFINE_INTER; AFFINE_AFFINE_HULL]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC HULL_MONO THEN
  SUBGOAL_THEN `ball(z:real^N,min e1 e2) SUBSET ball(z,e1) /\
                ball(z:real^N,min e1 e2) SUBSET ball(z,e2)` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM SET_TAC[]);;

let MOI_LGB1_AFF_MODULAR = prove
 (`!(z:real^N) P L Tz.
     affine P /\ affine L /\ z IN P /\ z IN Tz /\ Tz SUBSET L
     ==> affine hull ((P INTER L) UNION Tz) = L INTER affine hull (P UNION Tz)`,
  GEOM_ORIGIN_TAC `z:real^N` THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `vec 0 IN (L:real^N->bool)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `subspace (P:real^N->bool) /\ subspace (L:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_EQ_SUBSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN `affine hull ((P INTER L) UNION Tz) = span ((P INTER L) UNION Tz:real^N->bool) /\
                affine hull (P UNION Tz) = span (P UNION Tz:real^N->bool)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC AFFINE_HULL_EQ_SPAN THEN MATCH_MP_TAC HULL_INC THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPAN_UNION] THEN
  SUBGOAL_THEN `span (P INTER L) = P INTER L /\ span P = (P:real^N->bool)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [ASM_SIMP_TAC[SPAN_EQ_SELF; SUBSPACE_INTER]; ALL_TAC] THEN
  SUBGOAL_THEN `span Tz SUBSET (L:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC SPAN_SUBSET_SUBSPACE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `w:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSPACE_ADD THEN ASM SET_TAC[];
      MAP_EVERY EXISTS_TAC [`x:real^N`; `y:real^N`] THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`x:real^N`; `y:real^N`] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `x:real^N = w - y` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SUBSPACE_SUB THEN ASM SET_TAC[]]);;

let MOI_LGB1_AFF_HYPERPLANE_POINT = prove
 (`!(A:real^3->bool) z.
     {x:real^3 | x$3 = &0} SUBSET affine hull A /\ z IN affine hull A /\ ~(z$3 = &0)
     ==> affine hull A = (:real^3)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM AFF_DIM_EQ_FULL; DIMINDEX_3] THEN
  MATCH_MP_TAC(INT_ARITH `(a:int) <= &3 /\ &3 <= a ==> a = &3`) THEN CONJ_TAC THENL
   [MP_TAC(ISPEC `A:real^3->bool` AFF_DIM_LE_UNIV) THEN REWRITE_TAC[DIMINDEX_3];
    ALL_TAC] THEN
  SUBGOAL_THEN `{x:real^3 | x$3 = &0} = {x | basis 3 dot x = &0}` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim ((z:real^3) INSERT {x:real^3 | x$3 = &0}) = &3`
  (SUBST1_TAC o SYM) THENL
   [ASM_REWRITE_TAC[AFF_DIM_INSERT] THEN
    SIMP_TAC[HULL_P; AFFINE_HYPERPLANE; IN_ELIM_THM; DOT_BASIS; DIMINDEX_3; ARITH] THEN
    ASM_REWRITE_TAC[] THEN
    SIMP_TAC[AFF_DIM_HYPERPLANE; BASIS_NONZERO; DIMINDEX_3; ARITH] THEN INT_ARITH_TAC;
    GEN_REWRITE_TAC RAND_CONV [GSYM AFF_DIM_AFFINE_HULL] THEN
    MATCH_MP_TAC AFF_DIM_SUBSET THEN ASM SET_TAC[]]);;

let MOI_LGB1_LAST = prove
 (`!(Ms:real^2->bool) (rk:real^2->num).
     FINITE Ms /\ ~(Ms = {}) ==> ?p. p IN Ms /\ !q. q IN Ms ==> rk q <= rk p`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\n. ?q:real^2. q IN Ms /\ (rk:real^2->num) q = n` num_MAX) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> (a <=> b) ==> c`) THEN CONJ_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN MESON_TAC[];
      MP_TAC(ISPECL [`rk:real^2->num`; `Ms:real^2->bool`] UPPER_BOUND_FINITE_SET) THEN
      ASM_MESON_TAC[]];
    MESON_TAC[]]);;

let MOI_LGB1_RELINT_OFF_FACET = prove
 (`!(s:real^N->bool) p z.
     ~affine_dependent s /\ p IN s /\ z IN relative_interior (convex hull s)
     ==> ~(z IN convex hull (s DELETE p))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`convex hull (s DELETE p):real^N->bool`; `convex hull s:real^N->bool`]
    FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
      EXISTS_TAC `s DELETE (p:real^N)` THEN REWRITE_TAC[DELETE_SUBSET];
      DISCH_TAC THEN
      UNDISCH_TAC `~affine_dependent (s:real^N->bool)` THEN
      REWRITE_TAC[affine_dependent] THEN EXISTS_TAC `p:real^N` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(SET_RULE `!t. x IN t /\ t SUBSET u ==> (x:real^N) IN u`) THEN
      EXISTS_TAC `convex hull (s DELETE (p:real^N))` THEN
      REWRITE_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL] THEN
      FIRST_X_ASSUM SUBST1_TAC THEN ASM_SIMP_TAC[HULL_INC]];
    ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* C4. The genericity consequences of the moves (abstract: vertex values   *)
(* phi on a finite set V, movers KV with ranks rk, chart vertices HV).      *)
(* INV: for disjoint vertex sets W, W' with a mover and a point z in the    *)
(* relative interiors of the images conv(phi W), conv(phi W') and of a      *)
(* simplex conv YF of chart vertices, the traces of the two images on       *)
(* conv YF span the affine hull of YF (relative transversality).  SINGLE:  *)
(* the space of the last mover of W lies in the hull of conv(phi W) and a  *)
(* chart simplex through a relative interior point.  INSIDE: a moved image *)
(* inside the hull of a chart simplex of dimension <= 2 has only boundary *)
(* vertices.                                                               *)
(* ------------------------------------------------------------------------- *)

let MOI_LGB1_RELINT_IN = prove
 (`!s x:real^N. x IN relative_interior s ==> x IN s`,
  MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]);;

let MOI_LGB1_AT_OTHER = prove
 (`!KV rk (phi0:real^2->real^3) phi p w.
     (!v w. v IN KV /\ w IN KV /\ rk v = rk w ==> v = w) /\ p IN KV /\
     (w IN KV ==> rk w <= rk p) /\ ~(w = p)
     ==> moi_lgb1_at rk KV phi0 phi p w = phi w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_lgb1_at] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `(rk:real^2->num) w = rk p` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM LE_ANTISYM] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

let MOI_LGB1_STEP_AT = prove
 (`!(V:real^2->bool) KV B (phi0:real^2->real^3) phi rk HV W Tz (z:real^3) p.
     (!v w. v IN KV /\ w IN KV /\ rk v = rk w ==> v = w) /\
     (!p Y. p IN KV /\ Y SUBSET moi_lgb1_xc (moi_lgb1_at rk KV phi0 phi p) V HV /\
            ~(moi_lgb1_space B p SUBSET affine hull Y) ==> ~(phi p IN affine hull Y)) /\
     W SUBSET V /\ ~affine_dependent (IMAGE phi W) /\
     (!x y. x IN W /\ y IN W /\ phi x = phi y ==> x = y) /\
     p IN W /\ p IN KV /\ (!q. q IN W /\ q IN KV ==> rk q <= rk p) /\
     (?B0. B0 SUBSET moi_lgb1_xc (moi_lgb1_at rk KV phi0 phi p) V HV /\
           affine hull B0 = affine hull Tz) /\
     z IN relative_interior (convex hull (IMAGE phi W)) /\ z IN Tz
     ==> moi_lgb1_space B p SUBSET affine hull (IMAGE phi W UNION Tz)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`moi_lgb1_space B (p:real^2)`;
                 `moi_lgb1_xc (moi_lgb1_at rk KV (phi0:real^2->real^3) phi p) V HV`;
                 `(phi:real^2->real^3) p`; `IMAGE (phi:real^2->real^3) (W DELETE p)`;
                 `Tz:real^3->bool`; `z:real^3`] MOI_LGB1_STEP) THEN
  SUBGOAL_THEN `(phi:real^2->real^3) p INSERT IMAGE phi (W DELETE p) = IMAGE phi W`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(phi:real^2->real^3) p INSERT (IMAGE phi (W DELETE p) UNION Tz) =
                IMAGE phi W UNION Tz` SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `Y:real^3->bool` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (moi_lgb1_at rk KV (phi0:real^2->real^3) phi p) V` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[moi_lgb1_xc] THEN SET_TAC[]] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DELETE] THEN
    X_GEN_TAC `w:real^2` THEN STRIP_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `w:real^2` THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_LGB1_AT_OTHER THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[MOI_LGB1_RELINT_IN];
    SUBGOAL_THEN `IMAGE (phi:real^2->real^3) (W DELETE p) = IMAGE phi W DELETE phi p`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_LGB1_RELINT_OFF_FACET THEN ASM SET_TAC[]]);;

let MOI_LGB1_INV_HALF = prove
 (`!(V:real^2->bool) KV B (phi0:real^2->real^3) phi rk HV W W' YF (z:real^3) p.
     (!v w. v IN KV /\ w IN KV /\ rk v = rk w ==> v = w) /\
     (!p Y. p IN KV /\ Y SUBSET moi_lgb1_xc (moi_lgb1_at rk KV phi0 phi p) V HV /\
            ~(moi_lgb1_space B p SUBSET affine hull Y) ==> ~(phi p IN affine hull Y)) /\
     W SUBSET V /\ W' SUBSET V /\ DISJOINT W W' /\ YF SUBSET HV /\
     ~affine_dependent (IMAGE phi W) /\
     (!x y. x IN W /\ y IN W /\ phi x = phi y ==> x = y) /\
     p IN W /\ p IN KV /\ (!q. q IN W UNION W' /\ q IN KV ==> rk q <= rk p) /\
     z IN relative_interior (convex hull (IMAGE phi W)) /\
     z IN relative_interior (convex hull (IMAGE phi W')) /\
     z IN relative_interior (convex hull YF) /\
     (p IN B /\ z$3 = &0 ==> affine hull YF SUBSET {x:real^3 | x$3 = &0})
     ==> affine hull ((convex hull (IMAGE phi W) INTER convex hull YF) UNION
                      (convex hull (IMAGE phi W') INTER convex hull YF)) = affine hull YF`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Tz = convex hull (IMAGE (phi:real^2->real^3) W') INTER convex hull YF` THEN
  SUBGOAL_THEN `affine hull (Tz:real^3->bool) =
                affine hull (IMAGE (phi:real^2->real^3) W') INTER affine hull YF`
  ASSUME_TAC THENL
   [EXPAND_TAC "Tz" THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MOI_LGB1_AFF_INTER_RELINT o lhand o snd) THEN
    REWRITE_TAC[CONVEX_CONVEX_HULL; AFFINE_HULL_CONVEX_HULL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3) IN Tz` ASSUME_TAC THENL
   [EXPAND_TAC "Tz" THEN REWRITE_TAC[IN_INTER] THEN
    ASM_MESON_TAC[MOI_LGB1_RELINT_IN];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_lgb1_space B (p:real^2) SUBSET
                affine hull (IMAGE (phi:real^2->real^3) W UNION Tz)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LGB1_STEP_AT THEN
    MAP_EVERY EXISTS_TAC [`V:real^2->bool`; `KV:real^2->bool`; `phi0:real^2->real^3`;
                          `rk:real^2->num`; `HV:real^3->bool`; `z:real^3`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`moi_lgb1_at rk KV (phi0:real^2->real^3) phi p`; `V:real^2->bool`;
                   `HV:real^3->bool`; `IMAGE (phi:real^2->real^3) W'`; `YF:real^3->bool`]
      MOI_LGB1_XC_INTER) THEN
    ANTS_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN
    MATCH_MP_TAC(SET_RULE `(x:real^3) IN s ==> x IN s UNION t`) THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `w:real^2` THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_LGB1_AT_OTHER THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `affine hull (convex hull (IMAGE (phi:real^2->real^3) W) INTER convex hull YF) =
                affine hull (IMAGE phi W) INTER affine hull YF` ASSUME_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) MOI_LGB1_AFF_INTER_RELINT o lhand o snd) THEN
    REWRITE_TAC[CONVEX_CONVEX_HULL; AFFINE_HULL_CONVEX_HULL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[HULL_UNION_LEFT] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`z:real^3`; `affine hull (IMAGE (phi:real^2->real^3) W)`;
                 `affine hull (YF:real^3->bool)`; `Tz:real^3->bool`] MOI_LGB1_AFF_MODULAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[AFFINE_AFFINE_HULL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!t. x IN t /\ t SUBSET u ==> (x:real^3) IN u`) THEN
      EXISTS_TAC `convex hull (IMAGE (phi:real^2->real^3) W)` THEN
      REWRITE_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL] THEN
      ASM_MESON_TAC[MOI_LGB1_RELINT_IN];
      EXPAND_TAC "Tz" THEN MATCH_MP_TAC(SET_RULE
       `(t:real^3->bool) SUBSET u ==> s INTER t SUBSET u`) THEN
      REWRITE_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL]];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `affine hull (affine hull (IMAGE (phi:real^2->real^3) W) UNION Tz) =
                affine hull (IMAGE phi W UNION Tz)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM HULL_UNION_LEFT]; ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `(l:real^3->bool) SUBSET a ==> l INTER a = l`) THEN
  UNDISCH_TAC `moi_lgb1_space B (p:real^2) SUBSET
               affine hull (IMAGE (phi:real^2->real^3) W UNION Tz)` THEN
  REWRITE_TAC[moi_lgb1_space] THEN COND_CASES_TAC THENL
   [ALL_TAC; REWRITE_TAC[UNIV_SUBSET] THEN DISCH_THEN SUBST1_TAC THEN
             REWRITE_TAC[SUBSET_UNIV]] THEN
  DISCH_TAC THEN ASM_CASES_TAC `(z:real^3)$3 = &0` THENL
   [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `affine hull (IMAGE (phi:real^2->real^3) W UNION Tz) = (:real^3)`
  SUBST1_TAC THENL [ALL_TAC; REWRITE_TAC[SUBSET_UNIV]] THEN
  MATCH_MP_TAC MOI_LGB1_AFF_HYPERPLANE_POINT THEN EXISTS_TAC `z:real^3` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN ASM SET_TAC[]);;

let MOI_LGB1_INV = prove
 (`!(V:real^2->bool) KV B (phi0:real^2->real^3) phi rk HV W W' YF (z:real^3).
     FINITE V /\
     (!v w. v IN KV /\ w IN KV /\ rk v = rk w ==> v = w) /\
     (!p Y. p IN KV /\ Y SUBSET moi_lgb1_xc (moi_lgb1_at rk KV phi0 phi p) V HV /\
            ~(moi_lgb1_space B p SUBSET affine hull Y) ==> ~(phi p IN affine hull Y)) /\
     W SUBSET V /\ W' SUBSET V /\ DISJOINT W W' /\ YF SUBSET HV /\
     ~affine_dependent (IMAGE phi W) /\ ~affine_dependent (IMAGE phi W') /\
     (!x y. x IN W /\ y IN W /\ phi x = phi y ==> x = y) /\
     (!x y. x IN W' /\ y IN W' /\ phi x = phi y ==> x = y) /\
     ~((W UNION W') INTER KV = {}) /\
     z IN relative_interior (convex hull (IMAGE phi W)) /\
     z IN relative_interior (convex hull (IMAGE phi W')) /\
     z IN relative_interior (convex hull YF) /\
     (!q. q IN KV /\ q IN B /\ z$3 = &0
          ==> affine hull YF SUBSET {x:real^3 | x$3 = &0})
     ==> affine hull ((convex hull (IMAGE phi W) INTER convex hull YF) UNION
                      (convex hull (IMAGE phi W') INTER convex hull YF)) = affine hull YF`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(W UNION W') INTER KV:real^2->bool`; `rk:real^2->num`] MOI_LGB1_LAST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `V:real^2->bool` THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^2` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC)) THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o GEN_REWRITE_RULE I [IN_UNION]) THENL
   [MATCH_MP_TAC MOI_LGB1_INV_HALF THEN
    MAP_EVERY EXISTS_TAC [`V:real^2->bool`; `KV:real^2->bool`; `B:real^2->bool`;
      `phi0:real^2->real^3`; `rk:real^2->num`; `HV:real^3->bool`; `z:real^3`; `p:real^2`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ONCE_REWRITE_TAC[UNION_COMM] THEN MATCH_MP_TAC MOI_LGB1_INV_HALF THEN
    MAP_EVERY EXISTS_TAC [`V:real^2->bool`; `KV:real^2->bool`; `B:real^2->bool`;
      `phi0:real^2->real^3`; `rk:real^2->num`; `HV:real^3->bool`; `z:real^3`; `p:real^2`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      X_GEN_TAC `q:real^2` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      ASM_MESON_TAC[]]]);;

let MOI_LGB1_SINGLE = prove
 (`!(V:real^2->bool) KV B (phi0:real^2->real^3) phi rk HV W YF (z:real^3) p.
     (!v w. v IN KV /\ w IN KV /\ rk v = rk w ==> v = w) /\
     (!p Y. p IN KV /\ Y SUBSET moi_lgb1_xc (moi_lgb1_at rk KV phi0 phi p) V HV /\
            ~(moi_lgb1_space B p SUBSET affine hull Y) ==> ~(phi p IN affine hull Y)) /\
     W SUBSET V /\ YF SUBSET HV /\ ~affine_dependent (IMAGE phi W) /\
     (!x y. x IN W /\ y IN W /\ phi x = phi y ==> x = y) /\
     p IN W /\ p IN KV /\ (!q. q IN W /\ q IN KV ==> rk q <= rk p) /\
     z IN relative_interior (convex hull (IMAGE phi W)) /\ z IN convex hull YF
     ==> moi_lgb1_space B p SUBSET affine hull (IMAGE phi W UNION YF)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `affine hull (IMAGE (phi:real^2->real^3) W UNION YF) =
                affine hull (IMAGE phi W UNION convex hull YF)` SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[HULL_UNION_RIGHT] THEN REWRITE_TAC[AFFINE_HULL_CONVEX_HULL];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_LGB1_STEP_AT THEN
  MAP_EVERY EXISTS_TAC [`V:real^2->bool`; `KV:real^2->bool`; `phi0:real^2->real^3`;
                        `rk:real^2->num`; `HV:real^3->bool`; `z:real^3`] THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `YF:real^3->bool` THEN
  REWRITE_TAC[AFFINE_HULL_CONVEX_HULL] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `HV:real^3->bool` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[moi_lgb1_xc] THEN SET_TAC[]);;

let MOI_LGB1_AFF_DIM_Z3 = prove
 (`aff_dim {x:real^3 | x$3 = &0} = &2`,
  SUBGOAL_THEN `{x:real^3 | x$3 = &0} = {x | basis 3 dot x = &0}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH];
    SIMP_TAC[AFF_DIM_HYPERPLANE; BASIS_NONZERO; DIMINDEX_3; ARITH] THEN INT_ARITH_TAC]);;

let MOI_LGB1_INSIDE = prove
 (`!(V:real^2->bool) KV B (phi0:real^2->real^3) phi rk HV W YF.
     FINITE V /\
     (!v w. v IN KV /\ w IN KV /\ rk v = rk w ==> v = w) /\
     (!p Y. p IN KV /\ Y SUBSET moi_lgb1_xc (moi_lgb1_at rk KV phi0 phi p) V HV /\
            ~(moi_lgb1_space B p SUBSET affine hull Y) ==> ~(phi p IN affine hull Y)) /\
     W SUBSET V /\ YF SUBSET HV /\ aff_dim YF <= &2 /\ ~(W INTER KV = {}) /\
     IMAGE phi W SUBSET affine hull YF /\
     (!w. w IN W /\ (phi w)$3 = &0 /\ ~(KV INTER B = {}) ==> w IN B)
     ==> W SUBSET B /\ affine hull YF = {x:real^3 | x$3 = &0}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`W INTER KV:real^2->bool`; `rk:real^2->num`] MOI_LGB1_LAST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `V:real^2->bool` THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^2` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `moi_lgb1_space B (p:real^2) SUBSET affine hull (YF:real^3->bool)`
  MP_TAC THENL
   [SUBGOAL_THEN `affine hull (YF:real^3->bool) =
                  affine hull (IMAGE (phi:real^2->real^3) (W DELETE p) UNION YF)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
        MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[AFFINE_AFFINE_HULL; UNION_SUBSET] THEN
        REWRITE_TAC[HULL_SUBSET] THEN ASM SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(phi:real^2->real^3) p IN
                  affine hull (IMAGE phi (W DELETE p) UNION YF)` ASSUME_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!t. x IN t /\ t SUBSET u ==> (x:real^3) IN u`) THEN
      EXISTS_TAC `affine hull (YF:real^3->bool)` THEN
      CONJ_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC HULL_MONO THEN SET_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`p:real^2`;
      `IMAGE (phi:real^2->real^3) (W DELETE p) UNION YF`]) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[moi_lgb1_xc; UNION_SUBSET] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `(s:real^3->bool) SUBSET t ==> s SUBSET (t UNION u) UNION v`) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DELETE] THEN X_GEN_TAC `w:real^2` THEN
      STRIP_TAC THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `w:real^2` THEN
      CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_LGB1_AT_OTHER THEN ASM_MESON_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[moi_lgb1_space] THEN COND_CASES_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `affine hull (YF:real^3->bool) = {x:real^3 | x$3 = &0}` ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [ALL_TAC; ASM_REWRITE_TAC[]] THEN
      MP_TAC(ISPECL [`{x:real^3 | x$3 = &0}`; `affine hull (YF:real^3->bool)`]
        AFF_DIM_EQ_AFFINE_HULL) THEN
      ASM_REWRITE_TAC[MOI_LGB1_AFF_DIM_Z3; AFF_DIM_AFFINE_HULL; HULL_HULL] THEN
      SUBGOAL_THEN `affine hull {x:real^3 | x$3 = &0} = {x | x$3 = &0}` SUBST1_TAC THENL
       [MATCH_MP_TAC HULL_P THEN
        MP_TAC(ISPECL [`{p:real^2}`; `p:real^2`] MOI_LGB1_SPACE_AFFINE) THEN
        REWRITE_TAC[moi_lgb1_space; IN_SING];
        SET_TAC[]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET] THEN X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (phi:real^2->real^3) W SUBSET affine hull YF` THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ASM SET_TAC[]];
    REWRITE_TAC[UNIV_SUBSET] THEN DISCH_TAC THEN
    UNDISCH_TAC `aff_dim (YF:real^3->bool) <= &2` THEN
    ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN ASM_REWRITE_TAC[AFF_DIM_UNIV] THEN
    REWRITE_TAC[DIMINDEX_3] THEN INT_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* C5. Chart facts.  moi_lgb1_t3: the simplices of tt within three steps of *)
(* kk (the margin of the atlas); moi_lgb1_th: their faces in tt;            *)
(* moi_lgb1_chart: the properties of one chart of the atlas.  The chart     *)
(* image H = IMAGE (IMAGE h) (moi_lgb1_th tt kk) is a simplicial complex in *)
(* real^3, h' is affine on its simplices, relative interiors correspond.    *)
(* ------------------------------------------------------------------------- *)

let moi_lgb1_t3 = new_definition
 `moi_lgb1_t3 (tt:(real^N->bool)->bool) (kk:real^N->bool) =
    {s3 | s3 IN tt /\ ?s1 s2. s1 IN tt /\ s2 IN tt /\ ~(s1 INTER kk = {}) /\
                             ~(s1 INTER s2 = {}) /\ ~(s2 INTER s3 = {})}`;;

let moi_lgb1_th = new_definition
 `moi_lgb1_th (tt:(real^N->bool)->bool) (kk:real^N->bool) =
    {s | s IN tt /\ ?s3. s3 IN moi_lgb1_t3 tt kk /\ s SUBSET s3}`;;

let moi_lgb1_chart = new_definition
 `moi_lgb1_chart (c:(real^N->bool)->bool) (tt:(real^N->bool)->bool) (u:real^N->bool)
     (h:real^N->real^3) (h':real^3->real^N) (kk:real^N->bool) <=>
    simplicial_complex tt /\
    open_in (subtopology euclidean (UNIONS c)) u /\ u SUBSET UNIONS tt /\
    pl_homeomorphism (u,IMAGE h u) (h,h') /\
    ((u INTER complex_boundary c = {} /\ IMAGE h u = ball(vec 0,&1)) \/
     (IMAGE h u = ball(vec 0,&1) INTER {z:real^3 | &0 <= z$3} /\
      IMAGE h (u INTER complex_boundary c) = IMAGE h u INTER {z:real^3 | z$3 = &0})) /\
    compact kk /\ kk SUBSET u /\
    (!s. s IN moi_lgb1_t3 tt kk
         ==> s SUBSET u /\ ?l y. linear l /\ !x. x IN s ==> h x = l x + y)`;;

let MOI_LGB1_ATLAS_CHART = prove
 (`!(c:(real^N->bool)->bool) tt A u h h' kk.
     moi_lgb_atlas c tt A /\ (u,h,h',kk) IN A ==> moi_lgb1_chart c tt u h h' kk`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lgb_atlas; moi_lgb1_chart] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N->bool`; `h:real^N->real^3`;
                                `h':real^3->real^N`; `kk:real^N->bool`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[moi_lgb1_t3; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

let MOI_LGB1_CHART_INV = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk.
     moi_lgb1_chart c tt u h h' kk
     ==> (!x. x IN u ==> h' (h x) = x /\ h x IN IMAGE h u) /\
         (!z. z IN IMAGE h u ==> h (h' z) = z /\ h' z IN u) /\
         h continuous_on u /\ h' continuous_on IMAGE h u /\
         (!x x'. x IN u /\ x' IN u /\ h x = h x' ==> x = x')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lgb1_chart; pl_homeomorphism; homeomorphism] THEN
  STRIP_TAC THEN (REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[FUN_IN_IMAGE]; ASM SET_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
    ASM_MESON_TAC[]]));;

let MOI_LGB1_CHART_HS = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk.
     moi_lgb1_chart c tt u h h' kk
     ==> ?hs. (hs = (:real^3) \/ hs = {z:real^3 | &0 <= z$3}) /\
              IMAGE h u = ball(vec 0,&1) INTER hs /\
              (!x. x IN u ==> (x IN complex_boundary c <=>
                               hs = {z:real^3 | &0 <= z$3} /\ (h x)$3 = &0))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_LGB1_CHART_INV) THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_lgb1_chart]) THEN STRIP_TAC THENL
   [EXISTS_TAC `(:real^3)` THEN ASM_REWRITE_TAC[INTER_UNIV] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((:real^3) = {z:real^3 | &0 <= z$3})` (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[EXTENSION; IN_UNIV; IN_ELIM_THM; NOT_FORALL_THM] THEN
      EXISTS_TAC `--(basis 3):real^3` THEN
      SIMP_TAC[VECTOR_NEG_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
      REAL_ARITH_TAC;
      ASM SET_TAC[]];
    EXISTS_TAC `{z:real^3 | &0 <= z$3}` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `(h:real^N->real^3) x IN IMAGE h (u INTER complex_boundary c)` MP_TAC THENL
       [ASM SET_TAC[]; ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN MESON_TAC[]];
      STRIP_TAC THEN
      SUBGOAL_THEN `(h:real^N->real^3) x IN IMAGE h (u INTER complex_boundary c)` MP_TAC THENL
       [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM SET_TAC[];
        REWRITE_TAC[IN_IMAGE; IN_INTER] THEN ASM_MESON_TAC[]]]]);;

let MOI_LGB1_CHART_T3 = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk s.
     moi_lgb1_chart c tt u h h' kk /\ s IN moi_lgb1_t3 tt kk
     ==> s SUBSET u /\ ?l y. linear l /\ !x. x IN s ==> h x = l x + y`,
  REWRITE_TAC[moi_lgb1_chart] THEN MESON_TAC[]);;

let MOI_LGB1_TH_FACTS = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk s.
     moi_lgb1_chart c tt u h h' kk /\ s IN moi_lgb1_th tt kk
     ==> s IN tt /\ s SUBSET u /\
         (?l y. linear l /\ !x. x IN s ==> h x = l x + y) /\
         (!x x'. x IN s /\ x' IN s /\ h x = h x' ==> x = x')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_LGB1_CHART_INV) THEN STRIP_TAC THEN
  UNDISCH_TAC `(s:real^N->bool) IN moi_lgb1_th tt kk` THEN
  REWRITE_TAC[moi_lgb1_th; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `s3:real^N->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `s3:real^N->bool`] MOI_LGB1_CHART_T3) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `l:real^N->real^3`
    (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    MAP_EVERY EXISTS_TAC [`l:real^N->real^3`; `y:real^3`] THEN ASM SET_TAC[];
    ASM SET_TAC[]]);;

let MOI_LGB1_TH_FACE = prove
 (`!(tt:(real^N->bool)->bool) kk s f.
     simplicial_complex tt /\ s IN moi_lgb1_th tt kk /\ f face_of s
     ==> f IN moi_lgb1_th tt kk`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lgb1_th; IN_ELIM_THM] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[simplicial_complex];
    EXISTS_TAC `s3:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET_TRANS]]);;

let MOI_LGB1_TH_SUBSET = prove
 (`!(tt:(real^N->bool)->bool) kk. moi_lgb1_th tt kk SUBSET tt /\
                                  moi_lgb1_t3 tt kk SUBSET moi_lgb1_th tt kk`,
  REWRITE_TAC[moi_lgb1_th; moi_lgb1_t3; SUBSET; IN_ELIM_THM] THEN MESON_TAC[SUBSET_REFL]);;

let MOI_LGB1_H_SC = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk.
     moi_lgb1_chart c tt u h h' kk
     ==> simplicial_complex (IMAGE (IMAGE h) (moi_lgb1_th tt kk))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_LGB1_CHART_INV) THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (tt:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_lgb1_chart]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s IN moi_lgb1_th tt kk
        ==> (s:real^N->bool) IN tt /\ s SUBSET u /\
            (?l y. linear l /\ !x. x IN s ==> (h:real^N->real^3) x = l x + y) /\
            (!x x'. x IN s /\ x' IN s /\ h x = h x' ==> x = x')`
  (LABEL_TAC "th") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MOI_LGB1_TH_FACTS THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `h':real^3->real^N`;
                          `kk:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[simplicial_complex] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `tt:(real^N->bool)->bool` THEN REWRITE_TAC[MOI_LGB1_TH_SUBSET] THEN
    ASM_MESON_TAC[simplicial_complex];
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "th" (MP_TAC o C MATCH_MP (ASSUME `(s:real^N->bool) IN moi_lgb1_th tt kk`)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `l:real^N->real^3` (X_CHOOSE_THEN `y:real^3`
        STRIP_ASSUME_TAC)) ASSUME_TAC))) THEN
    SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` (X_CHOOSE_TAC `n:int`) THENL
     [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
    EXISTS_TAC `n:int` THEN MATCH_MP_TAC MOI_LGA_SIMPLEX_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`l:real^N->real^3`; `y:real^3`] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `f:real^3->bool` THEN X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "th" (MP_TAC o C MATCH_MP (ASSUME `(s:real^N->bool) IN moi_lgb1_th tt kk`)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `l:real^N->real^3` (X_CHOOSE_THEN `y:real^3`
        STRIP_ASSUME_TAC)) ASSUME_TAC))) THEN
    SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` (X_CHOOSE_TAC `n:int`) THENL
     [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
    MP_TAC(ISPECL [`n:int`; `h:real^N->real^3`; `l:real^N->real^3`; `y:real^3`;
                   `s:real^N->bool`] MOI_LGA_FACES_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    MATCH_MP_TAC MOI_LGB1_TH_FACE THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    X_GEN_TAC `s':real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "th" (MP_TAC o C MATCH_MP (ASSUME `(s':real^N->bool) IN moi_lgb1_th tt kk`)) THEN
    USE_THEN "th" (MP_TAC o C MATCH_MP (ASSUME `(s:real^N->bool) IN moi_lgb1_th tt kk`)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `l:real^N->real^3` (X_CHOOSE_THEN `y:real^3`
        STRIP_ASSUME_TAC)) ASSUME_TAC))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `l':real^N->real^3` (X_CHOOSE_THEN `y':real^3`
        STRIP_ASSUME_TAC)) ASSUME_TAC))) THEN
    SUBGOAL_THEN `IMAGE (h:real^N->real^3) s INTER IMAGE h s' = IMAGE h (s INTER s')`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(s INTER s':real^N->bool) face_of s /\ (s INTER s') face_of s'`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
    SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` (X_CHOOSE_TAC `n:int`) THENL
     [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
    SUBGOAL_THEN `?n. n simplex (s':real^N->bool)` (X_CHOOSE_TAC `n':int`) THENL
     [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`n:int`; `h:real^N->real^3`; `l:real^N->real^3`; `y:real^3`;
                     `s:real^N->bool`] MOI_LGA_FACES_IMAGE);
      MP_TAC(ISPECL [`n':int`; `h:real^N->real^3`; `l':real^N->real^3`; `y':real^3`;
                     `s':real^N->bool`] MOI_LGA_FACES_IMAGE)] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    EXISTS_TAC `s INTER s':real^N->bool` THEN ASM_REWRITE_TAC[]]);;

let MOI_LGB1_H_INV = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk S.
     moi_lgb1_chart c tt u h h' kk /\ S IN IMAGE (IMAGE h) (moi_lgb1_th tt kk)
     ==> ?s. s IN moi_lgb1_th tt kk /\ S = IMAGE h s /\ IMAGE h' S = s /\
             (!z. z IN S ==> h (h' z) = z /\ h' z IN s) /\
             (?l y. linear l /\ !z. z IN S ==> h' z = l z + y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_LGB1_CHART_INV) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `s:real^N->bool`] MOI_LGB1_TH_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `l:real^N->real^3` (X_CHOOSE_THEN `y:real^3`
      STRIP_ASSUME_TAC)) ASSUME_TAC))) THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `convex (s:real^N->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` (X_CHOOSE_TAC `n:int`) THENL
     [ASM_MESON_TAC[simplicial_complex; moi_lgb1_chart]; ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:real^N->real^3`; `l:real^N->real^3`; `y:real^3`; `s:real^N->bool`]
    MOI_LGA_LEFT_INVERSE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g0:real^3->real^N` (X_CHOOSE_THEN `l0:real^3->real^N`
    (X_CHOOSE_THEN `b0:real^N` STRIP_ASSUME_TAC))) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; X_GEN_TAC `x:real^N` THEN DISCH_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(h:real^N->real^3) x` THEN ASM SET_TAC[];
    REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM SET_TAC[];
    MAP_EVERY EXISTS_TAC [`l0:real^3->real^N`; `b0:real^N`] THEN
    ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM SET_TAC[]]);;

let MOI_LGB1_RELINT_AFFINE = prove
 (`!(f:real^M->real^N) l y s.
     linear l /\ convex s /\ (!x. x IN s ==> f x = l x + y)
     ==> IMAGE f (relative_interior s) = relative_interior (IMAGE f s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!t. t SUBSET s ==> IMAGE (f:real^M->real^N) t = IMAGE (\x. y + x) (IMAGE l t)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[SUBSET; VECTOR_ADD_SYM];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET_REFL] THEN
  REWRITE_TAC[RELATIVE_INTERIOR_TRANSLATION] THEN
  ASM_SIMP_TAC[RELATIVE_INTERIOR_LINEAR_IMAGE_CONVEX]);;

let MOI_LGB1_HS_RELINT = prove
 (`!(Fs:real^3->bool) z.
     convex Fs /\ Fs SUBSET {x:real^3 | &0 <= x$3} /\ z IN relative_interior Fs /\ z$3 = &0
     ==> Fs SUBSET {x:real^3 | x$3 = &0}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Fs:real^3->bool`; `Fs INTER {x:real^3 | basis 3 dot x = &0}`;
                 `Fs:real^3->bool`] SUBSET_OF_FACE_OF) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[SUBSET_REFL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH; real_ge] THEN ASM SET_TAC[];
      REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `z:real^3` THEN
      ASM_SIMP_TAC[IN_INTER; IN_ELIM_THM; DOT_BASIS; DIMINDEX_3; ARITH] THEN
      ASM_MESON_TAC[MOI_LGB1_RELINT_IN]];
    SIMP_TAC[SUBSET; IN_INTER; IN_ELIM_THM; DOT_BASIS; DIMINDEX_3; ARITH]]);;

(* ------------------------------------------------------------------------- *)
(* C6. Source-side objects.  moi_lgb1_kv: the movers (vertices of the      *)
(* simplices of L whose image meets kk); moi_lgb1_lm: the simplices with a *)
(* mover; moi_lgb1_l3: the simplices whose image lies in a face of a       *)
(* third-step simplex (a subcomplex containing every simplex that meets a  *)
(* simplex with a mover).  The chart map h o g is affine and injective on  *)
(* the simplices of moi_lgb1_l3; boundary vertices are detected by z3 = 0. *)
(* ------------------------------------------------------------------------- *)

let moi_lgb1_kv = new_definition
 `moi_lgb1_kv (L:(real^2->bool)->bool) (g:real^2->real^N) (kk:real^N->bool) =
    {v | {v} IN L /\ ?r. r IN L /\ v IN r /\ ~(IMAGE g r INTER kk = {})}`;;

let moi_lgb1_lm = new_definition
 `moi_lgb1_lm (L:(real^2->bool)->bool) (KV:real^2->bool) =
    {r | r IN L /\ ~(r INTER KV = {})}`;;

let moi_lgb1_l3 = new_definition
 `moi_lgb1_l3 (L:(real^2->bool)->bool) (g:real^2->real^N) (TH:(real^N->bool)->bool) =
    {r | r IN L /\ ?s. s IN TH /\ IMAGE g r SUBSET s}`;;

let MOI_LGB1_LM_SECOND = prove
 (`!(tt:(real^N->bool)->bool) L (g:real^2->real^N) kk R.
     moi_lgb_tlinear tt L g /\ R IN moi_lgb1_lm L (moi_lgb1_kv L g kk)
     ==> ?s1 s2. s1 IN tt /\ s2 IN tt /\ IMAGE g R SUBSET s2 /\
                 ~(s1 INTER kk = {}) /\ ~(s1 INTER s2 = {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lgb_tlinear; moi_lgb1_lm; moi_lgb1_kv] THEN
  REWRITE_TAC[IN_ELIM_THM; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `v:real^2` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(MP_TAC o SPEC `r:real^2->bool`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `R:real^2->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:real^N->bool` STRIP_ASSUME_TAC o CONJUNCT1) THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real^N->bool` STRIP_ASSUME_TAC o CONJUNCT1) THEN
  MAP_EVERY EXISTS_TAC [`s1:real^N->bool`; `s2:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  EXISTS_TAC `(g:real^2->real^N) v` THEN ASM SET_TAC[]);;

let MOI_LGB1_MEET_LM = prove
 (`!(tt:(real^N->bool)->bool) L (g:real^2->real^N) kk R r.
     moi_lgb_tlinear tt L g /\ R IN moi_lgb1_lm L (moi_lgb1_kv L g kk) /\
     r IN L /\ ~(r INTER R = {})
     ==> ?s. s IN moi_lgb1_t3 tt kk /\ IMAGE g r SUBSET s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `L:(real^2->bool)->bool`; `g:real^2->real^N`;
                 `kk:real^N->bool`; `R:real^2->bool`] MOI_LGB1_LM_SECOND) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `r:real^2->bool` o CONJUNCT2 o CONJUNCT2 o
    GEN_REWRITE_RULE I [moi_lgb_tlinear]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC o CONJUNCT1) THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[moi_lgb1_t3; IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC [`s1:real^N->bool`; `s2:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~(r INTER R:real^2->bool = {})` THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  EXISTS_TAC `(g:real^2->real^N) x` THEN ASM SET_TAC[]);;

let MOI_LGB1_MEET_LM_L3 = prove
 (`!(tt:(real^N->bool)->bool) L (g:real^2->real^N) kk R r.
     moi_lgb_tlinear tt L g /\ R IN moi_lgb1_lm L (moi_lgb1_kv L g kk) /\
     r IN L /\ ~(r INTER R = {})
     ==> r IN moi_lgb1_l3 L g (moi_lgb1_th tt kk)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `L:(real^2->bool)->bool`; `g:real^2->real^N`;
                 `kk:real^N->bool`; `R:real^2->bool`; `r:real^2->bool`] MOI_LGB1_MEET_LM) THEN
  ASM_REWRITE_TAC[moi_lgb1_l3; IN_ELIM_THM] THEN
  MESON_TAC[MOI_LGB1_TH_SUBSET; SUBSET]);;

let MOI_LGB1_LM_L3 = prove
 (`!(tt:(real^N->bool)->bool) L (g:real^2->real^N) kk R.
     moi_lgb_tlinear tt L g /\ R IN moi_lgb1_lm L (moi_lgb1_kv L g kk)
     ==> R IN moi_lgb1_l3 L g (moi_lgb1_th tt kk)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_LGB1_MEET_LM_L3 THEN
  EXISTS_TAC `R:real^2->bool` THEN ASM_REWRITE_TAC[INTER_IDEMPOT] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[moi_lgb1_lm; IN_ELIM_THM]; ALL_TAC] THEN
  UNDISCH_TAC `R IN moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)` THEN
  REWRITE_TAC[moi_lgb1_lm; IN_ELIM_THM] THEN SET_TAC[]);;

let MOI_LGB1_L3_SC = prove
 (`!(L:(real^2->bool)->bool) (g:real^2->real^N) TH.
     simplicial_complex L ==> simplicial_complex (moi_lgb1_l3 L g TH) /\
                              moi_lgb1_l3 L g TH SUBSET L`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplicial_complex; moi_lgb1_l3; IN_ELIM_THM] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `L:(real^2->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ASM_MESON_TAC[];
    REPEAT STRIP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `s':real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[FACE_OF_IMP_SUBSET; IMAGE_SUBSET; SUBSET_TRANS];
    ASM_MESON_TAC[];
    SET_TAC[]]);;

let MOI_LGB1_L3_A0 = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) r.
     moi_lgb1_chart c tt u h h' kk /\ moi_lgb_tlinear tt L g /\
     r IN moi_lgb1_l3 L g (moi_lgb1_th tt kk)
     ==> r IN L /\ IMAGE g r SUBSET u /\
         (?l y. linear l /\ !x. x IN r ==> h (g x) = l x + y) /\
         (?S. S IN IMAGE (IMAGE h) (moi_lgb1_th tt kk) /\ IMAGE (h o g) r SUBSET S)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lgb1_l3; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `s:real^N->bool`] MOI_LGB1_TH_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `lh:real^N->real^3` (X_CHOOSE_THEN `yh:real^3`
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "hs")))) ASSUME_TAC))) THEN
  FIRST_ASSUM(MP_TAC o SPEC `r:real^2->bool` o CONJUNCT2 o CONJUNCT2 o
    GEN_REWRITE_RULE I [moi_lgb_tlinear]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `lg:real^2->real^N` (X_CHOOSE_THEN `yg:real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ga"))) o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    MAP_EVERY EXISTS_TAC [`(lh:real^N->real^3) o (lg:real^2->real^N)`;
                          `(lh:real^N->real^3) yg + yh`] THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[LINEAR_COMPOSE]; ALL_TAC] THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(g:real^2->real^N) x IN s` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "hs" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(g:real^2->real^N) x IN s`)]) THEN
    USE_THEN "ga" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(x:real^2) IN r`)]) THEN
    ASM_SIMP_TAC[LINEAR_ADD; o_THM] THEN VECTOR_ARITH_TAC;
    EXISTS_TAC `IMAGE (h:real^N->real^3) s` THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE; IMAGE_o; IMAGE_SUBSET]]);;

let MOI_LGB1_G_INJ_SIMPLEX = prove
 (`!(c:(real^N->bool)->bool) tt L (g:real^2->real^N) r.
     moi_lt_singular_disk c g /\ moi_lgb_tlinear tt L g /\ r IN L
     ==> !x x'. x IN r /\ x' IN r /\ g x = g x' ==> x = x'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lt_singular_disk; moi_lgb_tlinear] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:real^2->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^2->real^N` (X_CHOOSE_THEN `y:real^N`
    STRIP_ASSUME_TAC) o CONJUNCT2) THEN
  MATCH_MP_TAC MOI_LGA_AFFINE_LOCAL_INJ THEN
  MAP_EVERY EXISTS_TAC [`l:real^2->real^N`; `y:real^N`; `std_triangle`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
    ASM SET_TAC[];
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM SET_TAC[]]);;

let MOI_LGB1_G_INJ_STAR = prove
 (`!(c:(real^N->bool)->bool) tt L (g:real^2->real^N) v.
     moi_lt_singular_disk c g /\ moi_lgb_tlinear tt L g /\ {v} IN L
     ==> !x x'. x IN UNIONS {r | r IN L /\ v IN r} /\
                x' IN UNIONS {r | r IN L /\ v IN r} /\ g x = g x' ==> x = x'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lt_singular_disk; moi_lgb_tlinear] THEN
  STRIP_TAC THEN MATCH_MP_TAC MOI_LGB1_STAR_INJ THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v:real^2`) THEN ANTS_TAC THENL
   [REWRITE_TAC[GSYM(ASSUME `UNIONS L = std_triangle`); IN_UNIONS] THEN
    EXISTS_TAC `{v:real^2}` THEN ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

let MOI_LGB1_TRI_NOT_FRONTIER = prove
 (`!R:real^2->bool.
     convex R /\ R SUBSET std_triangle /\ aff_dim R = &2
     ==> ~(R SUBSET relative_frontier std_triangle)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(relative_interior (R:real^2->bool) = {})` MP_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY] THEN DISCH_TAC THEN
    UNDISCH_TAC `aff_dim (R:real^2->bool) = &2` THEN ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_interior (R:real^2->bool) SUBSET relative_interior std_triangle`
  MP_TAC THENL
   [SUBGOAL_THEN `affine hull (R:real^2->bool) = (:real^2) /\
                  affine hull std_triangle = (:real^2)` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM AFF_DIM_EQ_FULL; DIMINDEX_2] THEN ASM_REWRITE_TAC[] THEN
      MESON_TAC[MOI_LTD_STD_TRIANGLE_SIMPLEX; AFF_DIM_SIMPLEX];
      ASM_SIMP_TAC[RELATIVE_INTERIOR_INTERIOR; SUBSET_INTERIOR]];
    ALL_TAC] THEN
  DISCH_TAC THEN DISCH_THEN(MP_TAC o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `x:real^2`) THEN
  SUBGOAL_THEN `(x:real^2) IN relative_frontier std_triangle` MP_TAC THENL
   [ASM_MESON_TAC[SUBSET; MOI_LGB1_RELINT_IN]; ALL_TAC] THEN
  REWRITE_TAC[relative_frontier; IN_DIFF] THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* C7. Smallness tools.  UNIF: a map continuous on a set U open in a closed *)
(* set hs is uniformly close on hs-points near a compact subset of U.        *)
(* moi_lgb1_interp K phi a: a is affine on the simplices of K with values   *)
(* phi at the vertices; such maps exist, have the hulls of the vertex       *)
(* values as images, stay close when the vertex values are close, and agree *)
(* on simplices whose vertex values agree.                                  *)
(* ------------------------------------------------------------------------- *)

let MOI_LGB1_UNIF = prove
 (`!(f:real^3->real^N) U hs K2 d.
     compact K2 /\ K2 SUBSET U /\ closed hs /\ open_in (subtopology euclidean hs) U /\
     f continuous_on U /\ &0 < d
     ==> ?eta. &0 < eta /\
               !z z'. z' IN K2 /\ z IN hs /\ norm(z - z') < eta
                      ==> z IN U /\ dist(f z,f z') < d`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
  SUBGOAL_THEN `closed (hs DIFF U:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_IN_CLOSED_TRANS THEN EXISTS_TAC `hs:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSED_IN_DIFF THEN
    ASM_REWRITE_TAC[CLOSED_IN_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K2:real^3->bool`; `hs DIFF U:real^3->bool`] SEPARATE_COMPACT_CLOSED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `N = hs INTER {x + y:real^3 | x IN K2 /\ y IN cball(vec 0,r0 / &2)}` THEN
  SUBGOAL_THEN `compact (N:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN MATCH_MP_TAC CLOSED_INTER_COMPACT THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC COMPACT_SUMS THEN ASM_REWRITE_TAC[COMPACT_CBALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. z IN hs /\ (?x. x IN K2 /\ norm(z - x) <= r0 / &2)
                           ==> z IN N /\ z IN U` (LABEL_TAC "nb") THENL
   [X_GEN_TAC `z:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC)) THEN
    CONJ_TAC THENL
     [EXPAND_TAC "N" THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`x:real^3`; `z - x:real^3`] THEN
      ASM_REWRITE_TAC[IN_CBALL_0] THEN VECTOR_ARITH_TAC;
      MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^3`; `z:real^3`]) THEN
      ASM_REWRITE_TAC[IN_DIFF; dist] THEN
      UNDISCH_TAC `norm(z - x:real^3) <= r0 / &2` THEN
      REWRITE_TAC[NORM_SUB] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(N:real^3->bool) SUBSET U` ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `x:real^3`
      (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC))) THEN
    USE_THEN "nb" (MP_TAC o SPEC `z:real^3`) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; EXISTS_TAC `x:real^3`] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    UNDISCH_TAC `(y:real^3) IN cball(vec 0,r0 / &2)` THEN
    UNDISCH_TAC `z:real^3 = x + y` THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[IN_CBALL_0; VECTOR_ARITH `(x + y) - x:real^3 = y`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^3->real^N`; `N:real^3->bool`] COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `d:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "uc"))) THEN
  EXISTS_TAC `min d0 (r0 / &2)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`z:real^3`; `z':real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^3) IN N /\ z IN U` STRIP_ASSUME_TAC THENL
   [USE_THEN "nb" MATCH_MP_TAC THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; EXISTS_TAC `z':real^3`] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z':real^3) IN N` ASSUME_TAC THENL
   [USE_THEN "nb" (MP_TAC o SPEC `z':real^3`) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; EXISTS_TAC `z':real^3`] THEN
    ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  USE_THEN "uc" (MP_TAC o SPECL [`z':real^3`; `z:real^3`]) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[dist] THEN ASM_REAL_ARITH_TAC);;

let moi_lgb1_interp = new_definition
 `moi_lgb1_interp (K:(real^2->bool)->bool) (phi:real^2->real^3) (a:real^2->real^3) <=>
    (!r. r IN K ==> ?l y. linear l /\ !x. x IN r ==> a x = l x + y) /\
    (!v. {v} IN K ==> a v = phi v)`;;

let MOI_LGB1_INTERP_EXISTS = prove
 (`!(K:(real^2->bool)->bool) (phi:real^2->real^3).
     simplicial_complex K ==> ?a. moi_lgb1_interp K phi a`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `phi:real^2->real^3`]
    MOI_PTR_SIMPLEXWISE_AFFINE) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `a:real^2->real^3` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[moi_lgb1_interp] THEN X_GEN_TAC `v:real^2` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `{v:real^2}` THEN
  ASM_REWRITE_TAC[MOI_REAL_IN_VERTEX_SETS; IN_SING; NOT_INSERT_EMPTY;
                  AFFINE_INDEPENDENT_1; CONVEX_HULL_SING]);;

let MOI_LGB1_VERTS = prove
 (`!(K:(real^2->bool)->bool) r.
     simplicial_complex K /\ r IN K
     ==> r = convex hull {v | v extreme_point_of r} /\
         FINITE {v | v extreme_point_of r} /\
         ~affine_dependent {v | v extreme_point_of r} /\
         (!v. v extreme_point_of r ==> {v} IN K /\ v IN r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?n. n simplex (r:real^2->bool)` (X_CHOOSE_TAC `n:int`) THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simplex]) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^2->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `{v:real^2 | v extreme_point_of r} = w` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  X_GEN_TAC `v:real^2` THEN DISCH_TAC THEN CONJ_TAC THENL
   [UNDISCH_TAC `simplicial_complex (K:(real^2->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    EXISTS_TAC `r:real^2->bool` THEN ASM_REWRITE_TAC[FACE_OF_SING];
    ASM_MESON_TAC[extreme_point_of]]);;

let MOI_LGB1_INTERP_IMAGE = prove
 (`!(K:(real^2->bool)->bool) phi (a:real^2->real^3) r.
     simplicial_complex K /\ moi_lgb1_interp K phi a /\ r IN K
     ==> IMAGE a r = convex hull (IMAGE phi {v | v extreme_point_of r})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lgb1_interp] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `r:real^2->bool`] MOI_LGB1_VERTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:real^2->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^2->real^3` (X_CHOOSE_THEN `y:real^3`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
  MP_TAC(ISPECL [`a:real^2->real^3`; `l:real^2->real^3`; `y:real^3`;
                 `{v:real^2 | v extreme_point_of r}`] MOI_LGA_HULL_IMAGE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
  ASM_MESON_TAC[]);;

let MOI_LGB1_INTERP_DIFF = prove
 (`!(K:(real^2->bool)->bool) phi phi0 (a:real^2->real^3) a0 r.
     simplicial_complex K /\ moi_lgb1_interp K phi a /\ moi_lgb1_interp K phi0 a0 /\
     r IN K
     ==> IMAGE (\x. a x - a0 x) r =
         convex hull (IMAGE (\v. phi v - phi0 v) {v | v extreme_point_of r})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lgb1_interp] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `r:real^2->bool`] MOI_LGB1_VERTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:real^2->bool`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:real^2->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^2->real^3` (X_CHOOSE_THEN `y:real^3`
    STRIP_ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `l0:real^2->real^3` (X_CHOOSE_THEN `y0:real^3`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
  MP_TAC(ISPECL [`\x. (a:real^2->real^3) x - a0 x`; `\x. (l:real^2->real^3) x - l0 x`;
                 `y - y0:real^3`; `{v:real^2 | v extreme_point_of r}`] MOI_LGA_HULL_IMAGE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LINEAR_COMPOSE_SUB THEN ASM_REWRITE_TAC[ETA_AX];
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `(x:real^2) IN r` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN VECTOR_ARITH_TAC];
    DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
  ASM_MESON_TAC[]);;

let MOI_LGB1_INTERP_CLOSE = prove
 (`!(K:(real^2->bool)->bool) phi phi0 (a:real^2->real^3) a0 r eta.
     simplicial_complex K /\ moi_lgb1_interp K phi a /\ moi_lgb1_interp K phi0 a0 /\
     r IN K /\ (!v. {v} IN K ==> norm(phi v - phi0 v) < eta)
     ==> !x. x IN r ==> norm(a x - a0 x) < eta`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `phi:real^2->real^3`; `phi0:real^2->real^3`;
                 `a:real^2->real^3`; `a0:real^2->real^3`; `r:real^2->bool`]
    MOI_LGB1_INTERP_DIFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(a:real^2->real^3) x - a0 x IN ball(vec 0,eta)` MP_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!s. (z:real^3) IN s /\ s SUBSET t ==> z IN t`) THEN
    EXISTS_TAC `IMAGE (\x. (a:real^2->real^3) x - a0 x) r` THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_MINIMAL THEN
      REWRITE_TAC[CONVEX_BALL; SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_BALL_0] THEN
      MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `r:real^2->bool`] MOI_LGB1_VERTS) THEN
      ASM_SIMP_TAC[]];
    REWRITE_TAC[IN_BALL_0]]);;

let MOI_LGB1_INTERP_IN = prove
 (`!(K:(real^2->bool)->bool) phi (a:real^2->real^3) r hs.
     simplicial_complex K /\ moi_lgb1_interp K phi a /\ r IN K /\ convex hs /\
     (!v. {v} IN K ==> phi v IN hs)
     ==> IMAGE a r SUBSET hs`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `phi:real^2->real^3`; `a:real^2->real^3`;
                 `r:real^2->bool`] MOI_LGB1_INTERP_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC HULL_MINIMAL THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `r:real^2->bool`] MOI_LGB1_VERTS) THEN
  ASM_SIMP_TAC[]);;

let MOI_LGB1_INTERP_AGREE = prove
 (`!(K:(real^2->bool)->bool) phi phi0 (a:real^2->real^3) a0 r.
     simplicial_complex K /\ moi_lgb1_interp K phi a /\ moi_lgb1_interp K phi0 a0 /\
     r IN K /\ (!v. v extreme_point_of r ==> phi v = phi0 v)
     ==> !x. x IN r ==> a x = a0 x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `phi:real^2->real^3`; `phi0:real^2->real^3`;
                 `a:real^2->real^3`; `a0:real^2->real^3`; `r:real^2->bool`]
    MOI_LGB1_INTERP_DIFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(a:real^2->real^3) x - a0 x IN {vec 0}` MP_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!s. (z:real^3) IN s /\ s SUBSET t ==> z IN t`) THEN
    EXISTS_TAC `IMAGE (\x. (a:real^2->real^3) x - a0 x) r` THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_MINIMAL THEN
      REWRITE_TAC[CONVEX_SING; SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_SING] THEN
      ASM_SIMP_TAC[VECTOR_SUB_REFL]];
    REWRITE_TAC[IN_SING] THEN VECTOR_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* C8. The fixed setting of the chart step (moi_lgb1_fix: one chart, the   *)
(* input singular disk, T-generic at Q, the half-space hs of the chart) and *)
(* the choice of the size eta of the vertex moves: for vertex values phi    *)
(* within eta of h o g (moi_lgb1_near, boundary vertices kept in z3 = 0),   *)
(* the interpolation a stays in the chart and h' o a is uniformly close to  *)
(* g, a is injective on the stars inside L3, the centres of the simplices   *)
(* stay in the open cells of their original images, and the zero pattern   *)
(* of z3 at the vertices is unchanged.                                      *)
(* ------------------------------------------------------------------------- *)

let moi_lgb1_fix = new_definition
 `moi_lgb1_fix (c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs <=>
    moi_lgb1_chart c tt u h h' kk /\ moi_lt_singular_disk c g /\
    moi_lgb_tgeneric tt L g Q /\ closed Q /\
    (hs = (:real^3) \/ hs = {z:real^3 | &0 <= z$3}) /\
    IMAGE h u = ball(vec 0,&1) INTER hs /\
    (!x. x IN u ==> (x IN complex_boundary c <=>
                     hs = {z:real^3 | &0 <= z$3} /\ (h x)$3 = &0))`;;

let MOI_LGB1_HS_CLOSED_CONVEX = prove
 (`!hs. (hs = (:real^3) \/ hs = {z:real^3 | &0 <= z$3}) ==> closed hs /\ convex hs`,
  GEN_TAC THEN DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[CLOSED_UNIV; CONVEX_UNIV] THEN
  SUBGOAL_THEN `{z:real^3 | &0 <= z$3} = {z | z$3 >= &0}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_GE; CONVEX_HALFSPACE_COMPONENT_GE]]);;

let MOI_LGB1_FIX_FACTS = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs.
     moi_lgb1_fix c tt u h h' kk L g Q hs
     ==> moi_lgb1_chart c tt u h h' kk /\ moi_lt_singular_disk c g /\
         moi_lgb_tgeneric tt L g Q /\ moi_lgb_tlinear tt L g /\ closed Q /\
         simplicial_complex L /\ UNIONS L = std_triangle /\
         g continuous_on std_triangle /\ simplicial_complex tt /\
         closed hs /\ convex hs /\ IMAGE h u SUBSET hs /\
         open_in (subtopology euclidean hs) (IMAGE h u) /\
         (!x. x IN u ==> h' (h x) = x /\ h x IN IMAGE h u) /\
         (!z. z IN IMAGE h u ==> h (h' z) = z /\ h' z IN u) /\
         h continuous_on u /\ h' continuous_on IMAGE h u /\
         (!x x'. x IN u /\ x' IN u /\ h x = h x' ==> x = x')`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS o GEN_REWRITE_RULE I [moi_lgb1_fix]) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_LGB1_CHART_INV) THEN
  DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_LGB1_HS_CLOSED_CONVEX) THEN
  DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  SUBGOAL_THEN `moi_lgb_tlinear tt L (g:real^2->real^N)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lgb_tgeneric tt L (g:real^2->real^N) Q` THEN
    SIMP_TAC[moi_lgb_tgeneric];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_lgb_tlinear]) THEN
  DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  ASM_REWRITE_TAC[INTER_SUBSET] THEN REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         (UNDISCH_TAC `moi_lt_singular_disk (c:(real^N->bool)->bool) g` THEN
          REWRITE_TAC[moi_lt_singular_disk] THEN
          DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON] THEN
          NO_TAC);
         (UNDISCH_TAC `moi_lgb1_chart (c:(real^N->bool)->bool) tt u h h' kk` THEN
          REWRITE_TAC[moi_lgb1_chart] THEN SIMP_TAC[] THEN NO_TAC);
         (ONCE_REWRITE_TAC[INTER_COMM] THEN MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN
          REWRITE_TAC[OPEN_BALL] THEN NO_TAC)]);;

let moi_lgb1_near = new_definition
 `moi_lgb1_near (K:(real^2->bool)->bool) (phi0:real^2->real^3) phi hs B eta <=>
    !v. {v} IN K ==> norm(phi v - phi0 v) < eta /\ phi v IN hs /\
                     (hs = {z:real^3 | &0 <= z$3} /\ v IN B ==> (phi v)$3 = &0)`;;

let MOI_LGB1_NEAR_MONO = prove
 (`!(K:(real^2->bool)->bool) phi0 phi hs B eta eta'.
     moi_lgb1_near K phi0 phi hs B eta /\ eta <= eta'
     ==> moi_lgb1_near K phi0 phi hs B eta'`,
  REWRITE_TAC[moi_lgb1_near] THEN MESON_TAC[REAL_LTE_TRANS]);;

let MOI_LGB1_A0_INTERP = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs.
     moi_lgb1_fix c tt u h h' kk L g Q hs
     ==> moi_lgb1_interp (moi_lgb1_l3 L g (moi_lgb1_th tt kk)) (\v. h (g v)) (\x. h (g x))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  REWRITE_TAC[moi_lgb1_interp] THEN X_GEN_TAC `r:real^2->bool` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `r:real^2->bool`]
    MOI_LGB1_L3_A0) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let MOI_LGB1_SMALL_UNIF = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs d0.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ &0 < d0
     ==> ?eta. &0 < eta /\
          !phi a. moi_lgb1_near (moi_lgb1_l3 L g (moi_lgb1_th tt kk)) (\v. h (g v)) phi hs
                    (relative_frontier std_triangle) eta /\
                  moi_lgb1_interp (moi_lgb1_l3 L g (moi_lgb1_th tt kk)) phi a
                  ==> !R x. R IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\ x IN R
                            ==> a x IN IMAGE h u /\ dist(h' (a x),g x) < d0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  ABBREV_TAC `L3 = moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)` THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `g:real^2->real^N`;
                 `moi_lgb1_th (tt:(real^N->bool)->bool) kk`] MOI_LGB1_L3_SC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!r. r IN L3 ==> IMAGE (g:real^2->real^N) r SUBSET u` ASSUME_TAC THENL
   [X_GEN_TAC `r:real^2->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `r:real^2->bool`]
      MOI_LGB1_L3_A0) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS L3 SUBSET std_triangle /\ compact (UNIONS L3:real^2->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN MATCH_MP_TAC COMPACT_UNIONS THEN
    CONJ_TAC THENL [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
    ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_COMPACT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h':real^3->real^N`; `IMAGE (h:real^N->real^3) u`; `hs:real^3->bool`;
                 `IMAGE (\x. (h:real^N->real^3) ((g:real^2->real^N) x)) (UNIONS (L3:(real^2->bool)->bool))`; `d0:real`]
    MOI_LGB1_UNIF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(\x. (h:real^N->real^3) ((g:real^2->real^N) x)) = h o g` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `u:real^N->bool` THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `eta:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "un")) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`phi:real^2->real^3`; `a:real^2->real^3`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`R:real^2->bool`; `x:real^2`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(g:real^2->real^N) x IN u` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^2->real^N) x = h' (h (g x):real^3)` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  USE_THEN "un" MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:real^2` THEN ASM SET_TAC[];
    MP_TAC(ISPECL [`L3:(real^2->bool)->bool`; `phi:real^2->real^3`; `a:real^2->real^3`;
                   `R:real^2->bool`; `hs:real^3->bool`] MOI_LGB1_INTERP_IN) THEN
    ANTS_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[moi_lgb1_near];
    MP_TAC(ISPECL [`L3:(real^2->bool)->bool`; `phi:real^2->real^3`;
                   `\v. (h:real^N->real^3) ((g:real^2->real^N) v)`; `a:real^2->real^3`;
                   `\x. (h:real^N->real^3) ((g:real^2->real^N) x)`; `R:real^2->bool`;
                   `eta:real`] MOI_LGB1_INTERP_CLOSE) THEN
    ANTS_TAC THENL [ALL_TAC; DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "L3" THEN MATCH_MP_TAC MOI_LGB1_A0_INTERP THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[moi_lgb1_near]]]);;

let MOI_LGB1_STD_FACTS = prove
 (`aff_dim std_triangle = &2 /\ affine hull std_triangle = (:real^2) /\
   relative_interior std_triangle = interior std_triangle /\
   ~(interior std_triangle = {})`,
  SUBGOAL_THEN `aff_dim std_triangle = &2` ASSUME_TAC THENL
   [MESON_TAC[MOI_LTD_STD_TRIANGLE_SIMPLEX; AFF_DIM_SIMPLEX]; ALL_TAC] THEN
  SUBGOAL_THEN `affine hull std_triangle = (:real^2)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM AFF_DIM_EQ_FULL; DIMINDEX_2]; ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_INTERIOR_INTERIOR] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o MATCH_MP RELATIVE_INTERIOR_INTERIOR) THEN
  SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY; MOI_LTD_STD_TRIANGLE_BASIC]);;

let MOI_LGB1_SMALL_STAR = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs.
     moi_lgb1_fix c tt u h h' kk L g Q hs
     ==> ?eta. &0 < eta /\
          !phi a. moi_lgb1_near (moi_lgb1_l3 L g (moi_lgb1_th tt kk)) (\v. h (g v)) phi hs
                    (relative_frontier std_triangle) eta /\
                  moi_lgb1_interp (moi_lgb1_l3 L g (moi_lgb1_th tt kk)) phi a
                  ==> !v. {v} IN L /\
                          (!r. r IN L /\ v IN r ==> r IN moi_lgb1_l3 L g (moi_lgb1_th tt kk))
                          ==> !x y. x IN UNIONS {r | r IN L /\ v IN r} /\
                                    y IN UNIONS {r | r IN L /\ v IN r} /\ a x = a y
                                    ==> x = y`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  ABBREV_TAC `L3 = moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)` THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `g:real^2->real^N`;
                 `moi_lgb1_th (tt:(real^N->bool)->bool) kk`] MOI_LGB1_L3_SC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!r. r IN L3
                    ==> IMAGE (g:real^2->real^N) r SUBSET u /\
                        ?l y. linear l /\ !x. x IN r ==> (h:real^N->real^3) (g x) = l x + y`
  (LABEL_TAC "a0") THENL
   [X_GEN_TAC `r:real^2->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `r:real^2->bool`]
      MOI_LGB1_L3_A0) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\v:real^2 e. !f:real^2->real^3.
       (!r. r IN L /\ v IN r ==> ?l y. linear l /\ !x. x IN r ==> f x = l x + y) /\
       (!w. {w} IN L /\ w IN UNIONS {r | r IN L /\ v IN r}
            ==> norm(f w - (h:real^N->real^3) ((g:real^2->real^N) w)) < e)
       ==> !x y. x IN UNIONS {r | r IN L /\ v IN r} /\
                 y IN UNIONS {r | r IN L /\ v IN r} /\ f x = f y ==> x = y`;
    `{v:real^2 | {v} IN L /\ !r. r IN L /\ v IN r ==> r IN L3}`] MOI_LGB1_FINITE_EPS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{v:real^2 | {v} IN L}` THEN
      CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
      MATCH_MP_TAC FINITE_IMAGE_INJ THEN REWRITE_TAC[] THEN
      CONJ_TAC THENL [SET_TAC[]; ASM_MESON_TAC[simplicial_complex]];
      REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `f:real^2->real^3` THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[REAL_LTE_TRANS];
      X_GEN_TAC `v:real^2` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      MATCH_MP_TAC MOI_LGB1_STAR_STABLE THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_LGB1_PURE2 THEN
        EXISTS_TAC `std_triangle` THEN ASM_REWRITE_TAC[MOI_LGB1_STD_FACTS] THEN
        REWRITE_TAC[MOI_LTD_STD_TRIANGLE_BASIC] THEN ASM SET_TAC[];
        REPEAT STRIP_TAC THEN ASM_MESON_TAC[];
        MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                       `L:(real^2->bool)->bool`; `g:real^2->real^N`; `v:real^2`]
          MOI_LGB1_G_INJ_STAR) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "gi") THEN
        MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN STRIP_TAC THEN
        USE_THEN "gi" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `(g:real^2->real^N) x IN u /\ g y IN u` STRIP_ASSUME_TAC THENL
         [UNDISCH_TAC `(x:real^2) IN UNIONS {r | r IN L /\ (v:real^2) IN r}` THEN
          UNDISCH_TAC `(y:real^2) IN UNIONS {r | r IN L /\ (v:real^2) IN r}` THEN
          REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
          DISCH_THEN(X_CHOOSE_THEN `r2:real^2->bool` STRIP_ASSUME_TAC) THEN
          DISCH_THEN(X_CHOOSE_THEN `r1:real^2->bool` STRIP_ASSUME_TAC) THEN
          CONJ_TAC THENL
           [USE_THEN "a0" (MP_TAC o SPEC `r1:real^2->bool`);
            USE_THEN "a0" (MP_TAC o SPEC `r2:real^2->bool`)] THEN
          (ANTS_TAC THENL [ASM_MESON_TAC[]; ASM SET_TAC[]]);
          ASM_MESON_TAC[]]]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `eta:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "st")) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`phi:real^2->real^3`; `a:real^2->real^3`] THEN STRIP_TAC THEN
  X_GEN_TAC `v:real^2` THEN STRIP_TAC THEN
  USE_THEN "st" (MP_TAC o SPEC `v:real^2`) THEN ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[moi_lgb1_interp]; ALL_TAC] THEN
  X_GEN_TAC `w:real^2` THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `r:real^2->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `{w:real^2} IN L3` ASSUME_TAC THENL
   [SUBGOAL_THEN `(r:real^2->bool) IN L3` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "L3" THEN REWRITE_TAC[moi_lgb1_l3; IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^2->real^3) w = phi w` SUBST1_TAC THENL
   [ASM_MESON_TAC[moi_lgb1_interp]; ALL_TAC] THEN
  ASM_MESON_TAC[moi_lgb1_near]);;

let moi_lgb1_cen = new_definition
 `moi_lgb1_cen (R:real^2->bool) = @x. x IN relative_interior R`;;

let MOI_LGB1_CEN = prove
 (`!R:real^2->bool. convex R /\ ~(R = {})
                    ==> moi_lgb1_cen R IN relative_interior R /\ moi_lgb1_cen R IN R`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(relative_interior (R:real^2->bool) = {})` MP_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY]; ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN DISCH_THEN(MP_TAC o SELECT_RULE) THEN
  REWRITE_TAC[GSYM moi_lgb1_cen] THEN MESON_TAC[MOI_LGB1_RELINT_IN]);;

let MOI_LGB1_SMALL_SIDE = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs.
     moi_lgb1_fix c tt u h h' kk L g Q hs
     ==> ?eta. &0 < eta /\
          !phi a. moi_lgb1_near (moi_lgb1_l3 L g (moi_lgb1_th tt kk)) (\v. h (g v)) phi hs
                    (relative_frontier std_triangle) eta /\
                  moi_lgb1_interp (moi_lgb1_l3 L g (moi_lgb1_th tt kk)) phi a
                  ==> !R S. R IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\
                            S IN IMAGE (IMAGE h) (moi_lgb1_th tt kk) /\ ~(R = {}) /\
                            h (g (moi_lgb1_cen R)) IN interior S
                            ==> a (moi_lgb1_cen R) IN interior S`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  ABBREV_TAC `L3 = moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)` THEN
  ABBREV_TAC `H = IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)` THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `g:real^2->real^N`;
                 `moi_lgb1_th (tt:(real^N->bool)->bool) kk`] MOI_LGB1_L3_SC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (H:(real^3->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "H" THEN MATCH_MP_TAC MOI_LGB1_H_SC THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `u:real^N->bool`; `h':real^3->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\(p:(real^2->bool)#(real^3->bool)) e.
       !z. norm(z - (h:real^N->real^3) ((g:real^2->real^N) (moi_lgb1_cen (FST p)))) < e
           ==> z IN interior (SND p)`;
    `{(R,S) | R IN L3 /\ S IN H /\ ~(R = {}) /\
              (h:real^N->real^3) ((g:real^2->real^N) (moi_lgb1_cen R)) IN interior S}`]
    MOI_LGB1_FINITE_EPS) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `(L3:(real^2->bool)->bool) CROSS (H:(real^3->bool)->bool)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_CROSS THEN ASM_MESON_TAC[simplicial_complex];
        REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_CROSS] THEN SIMP_TAC[]];
      MESON_TAC[REAL_LTE_TRANS];
      REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
      MAP_EVERY X_GEN_TAC [`R:real^2->bool`; `S:real^3->bool`] THEN STRIP_TAC THEN
      MP_TAC(ISPEC `S:real^3->bool` OPEN_INTERIOR) THEN
      REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
      DISCH_THEN(MP_TAC o SPEC `(h:real^N->real^3) ((g:real^2->real^N) (moi_lgb1_cen R))`) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
      REWRITE_TAC[SUBSET; IN_BALL; dist] THEN MESON_TAC[NORM_SUB]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `eta:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sd")) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`phi:real^2->real^3`; `a:real^2->real^3`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`R:real^2->bool`; `S:real^3->bool`] THEN STRIP_TAC THEN
  USE_THEN "sd" (MP_TAC o SPECL [`R:real^2->bool`; `S:real^3->bool`]) THEN
  ANTS_TAC THENL [REWRITE_TAC[IN_ELIM_PAIR_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`L3:(real^2->bool)->bool`; `phi:real^2->real^3`;
                 `\v. (h:real^N->real^3) ((g:real^2->real^N) v)`; `a:real^2->real^3`;
                 `\x. (h:real^N->real^3) ((g:real^2->real^N) x)`; `R:real^2->bool`;
                 `eta:real`] MOI_LGB1_INTERP_CLOSE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "L3" THEN MATCH_MP_TAC MOI_LGB1_A0_INTERP THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[moi_lgb1_near]];
    DISCH_THEN MATCH_MP_TAC] THEN
  MP_TAC(ISPEC `R:real^2->bool` MOI_LGB1_CEN) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX]);;

let MOI_LGB1_SMALL_Z3 = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs.
     moi_lgb1_fix c tt u h h' kk L g Q hs
     ==> ?eta. &0 < eta /\
          !phi. moi_lgb1_near (moi_lgb1_l3 L g (moi_lgb1_th tt kk)) (\v. h (g v)) phi hs
                  (relative_frontier std_triangle) eta
                ==> !v. {v} IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\
                        hs = {z:real^3 | &0 <= z$3}
                        ==> ((phi v)$3 = &0 <=> v IN relative_frontier std_triangle)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  ABBREV_TAC `L3 = moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)` THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `g:real^2->real^N`;
                 `moi_lgb1_th (tt:(real^N->bool)->bool) kk`] MOI_LGB1_L3_SC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!v. {v} IN L3 /\ hs = {z:real^3 | &0 <= z$3} /\
        ~(v IN relative_frontier std_triangle)
        ==> &0 < ((h:real^N->real^3) ((g:real^2->real^N) v))$3`
  (LABEL_TAC "pos") THENL
   [X_GEN_TAC `v:real^2` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `{v:real^2}`]
      MOI_LGB1_L3_A0) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IMAGE_CLAUSES; SING_SUBSET] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(v:real^2) IN std_triangle` ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_UNIONS; IN_SING]; ALL_TAC] THEN
    SUBGOAL_THEN `~((g:real^2->real^N) v IN complex_boundary c)` ASSUME_TAC THENL
     [UNDISCH_TAC `moi_lt_singular_disk (c:(real^N->bool)->bool) g` THEN
      REWRITE_TAC[moi_lt_singular_disk] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `v:real^2`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `moi_lgb1_fix (c:(real^N->bool)->bool) tt u h h' kk L g Q hs` THEN
    REWRITE_TAC[moi_lgb1_fix] THEN
    DISCH_THEN(MP_TAC o SPEC `(g:real^2->real^N) v` o last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(h:real^N->real^3) ((g:real^2->real^N) v) IN hs` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\v:real^2 e. hs = {z:real^3 | &0 <= z$3} /\ ~(v IN relative_frontier std_triangle)
                  ==> e <= ((h:real^N->real^3) ((g:real^2->real^N) v))$3`;
    `{v:real^2 | {v} IN L3}`] MOI_LGB1_FINITE_EPS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE_INJ THEN REWRITE_TAC[] THEN
      CONJ_TAC THENL [SET_TAC[]; ASM_MESON_TAC[simplicial_complex]];
      MESON_TAC[REAL_LE_TRANS];
      X_GEN_TAC `v:real^2` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
      ASM_CASES_TAC `hs = {z:real^3 | &0 <= z$3} /\ ~(v IN relative_frontier std_triangle)`
      THENL
       [EXISTS_TAC `((h:real^N->real^3) ((g:real^2->real^N) v))$3` THEN
        ASM_REWRITE_TAC[REAL_LE_REFL] THEN USE_THEN "pos" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_LT_01]]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `eta:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "zz")) THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `phi:real^2->real^3` THEN REWRITE_TAC[moi_lgb1_near] THEN
  DISCH_THEN(LABEL_TAC "nr") THEN X_GEN_TAC `v:real^2` THEN STRIP_TAC THEN
  USE_THEN "nr" (MP_TAC o C MATCH_MP (ASSUME `{v:real^2} IN L3`)) THEN STRIP_TAC THEN
  ASM_CASES_TAC `(v:real^2) IN relative_frontier std_triangle` THENL
   [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `eta <= ((h:real^N->real^3) ((g:real^2->real^N) v))$3` ASSUME_TAC THENL
   [USE_THEN "zz" (MP_TAC o SPEC `v:real^2`) THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(phi:real^2->real^3) v - (h:real^N->real^3) ((g:real^2->real^N) v)`;
                 `3`] COMPONENT_LE_NORM) THEN
  SIMP_TAC[VECTOR_SUB_COMPONENT; DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC);;

let MOI_LGB1_SMALL = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs d0.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ &0 < d0
     ==> ?eta. &0 < eta /\
          !phi a. moi_lgb1_near (moi_lgb1_l3 L g (moi_lgb1_th tt kk)) (\v. h (g v)) phi hs
                    (relative_frontier std_triangle) eta /\
                  moi_lgb1_interp (moi_lgb1_l3 L g (moi_lgb1_th tt kk)) phi a
                  ==> (!R x. R IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\ x IN R
                             ==> a x IN IMAGE h u /\ dist(h' (a x),g x) < d0) /\
                      (!v. {v} IN L /\
                           (!r. r IN L /\ v IN r ==> r IN moi_lgb1_l3 L g (moi_lgb1_th tt kk))
                           ==> !x y. x IN UNIONS {r | r IN L /\ v IN r} /\
                                     y IN UNIONS {r | r IN L /\ v IN r} /\ a x = a y
                                     ==> x = y) /\
                      (!R S. R IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\
                             S IN IMAGE (IMAGE h) (moi_lgb1_th tt kk) /\ ~(R = {}) /\
                             h (g (moi_lgb1_cen R)) IN interior S
                             ==> a (moi_lgb1_cen R) IN interior S) /\
                      (!v. {v} IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\
                           hs = {z:real^3 | &0 <= z$3}
                           ==> ((phi v)$3 = &0 <=> v IN relative_frontier std_triangle))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `d0:real`] MOI_LGB1_SMALL_UNIF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "s1"))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`] MOI_LGB1_SMALL_STAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "s2"))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`] MOI_LGB1_SMALL_SIDE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "s3"))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`] MOI_LGB1_SMALL_Z3) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e4:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "s4"))) THEN
  EXISTS_TAC `min (min e1 e2) (min e3 e4)` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`phi:real^2->real^3`; `a:real^2->real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!e. min (min e1 e2) (min e3 e4) <= e
        ==> moi_lgb1_near (moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk))
              (\v. (h:real^N->real^3) (g v)) phi hs (relative_frontier std_triangle) e`
  (LABEL_TAC "nm") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_LGB1_NEAR_MONO THEN
    EXISTS_TAC `min (min e1 e2) (min e3 e4)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "s1" (MP_TAC o SPECL [`phi:real^2->real^3`; `a:real^2->real^3`]);
    USE_THEN "s2" (MP_TAC o SPECL [`phi:real^2->real^3`; `a:real^2->real^3`]);
    USE_THEN "s3" (MP_TAC o SPECL [`phi:real^2->real^3`; `a:real^2->real^3`]);
    USE_THEN "s4" (MP_TAC o SPEC `phi:real^2->real^3`)] THEN
  (ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]]) THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "nm" MATCH_MP_TAC THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* C9. Smallness in the manifold: points close to the image of a simplex   *)
(* with a mover lie only in third-step simplices (MARGIN); boundary points *)
(* close to the image of the frontier lie in w (WSMALL); the double points *)
(* of g in Q on the 1-skeleton keep a positive distance from the images of *)
(* the disjoint simplices (SKEL).                                          *)
(* ------------------------------------------------------------------------- *)

let MOI_LGB1_MARGIN = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs.
     moi_lgb1_fix c tt u h h' kk L g Q hs
     ==> ?d. &0 < d /\
             !R x y s. R IN moi_lgb1_lm L (moi_lgb1_kv L g kk) /\ x IN R /\
                       dist(y,g x) < d /\ s IN tt /\ y IN s
                       ==> s IN moi_lgb1_t3 tt kk`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  ABBREV_TAC `Lm = moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)` THEN
  SUBGOAL_THEN `(Lm:(real^2->bool)->bool) SUBSET L` ASSUME_TAC THENL
   [EXPAND_TAC "Lm" THEN REWRITE_TAC[moi_lgb1_lm] THEN SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS (IMAGE (IMAGE (g:real^2->real^N)) Lm)`;
                 `UNIONS {s:real^N->bool | s IN tt /\ ~(s IN moi_lgb1_t3 tt kk)}`]
    SEPARATE_COMPACT_CLOSED) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_UNIONS THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_IMAGE THEN ASM_MESON_TAC[FINITE_SUBSET; simplicial_complex];
        REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `R:real^2->bool` THEN DISCH_TAC THEN
        MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
          ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
          ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_COMPACT; SUBSET]]];
      MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `tt:(real^N->bool)->bool` THEN
        CONJ_TAC THENL [ASM_MESON_TAC[simplicial_complex]; SET_TAC[]];
        REWRITE_TAC[IN_ELIM_THM] THEN
        ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CLOSED]];
      REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_INTER; IN_UNIONS; IN_ELIM_THM;
                  EXISTS_IN_IMAGE] THEN
      X_GEN_TAC `y:real^N` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `R:real^2->bool` STRIP_ASSUME_TAC)
        (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC)) THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `L:(real^2->bool)->bool`;
                     `g:real^2->real^N`; `kk:real^N->bool`; `R:real^2->bool`]
        MOI_LGB1_LM_SECOND) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
      UNDISCH_TAC `~((s:real^N->bool) IN moi_lgb1_t3 tt kk)` THEN
      REWRITE_TAC[moi_lgb1_t3; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`s1:real^N->bool`; `s2:real^N->bool`] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sep")) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`R:real^2->bool`; `x:real^2`; `y:real^N`; `s:real^N->bool`] THEN
  STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  USE_THEN "sep" (MP_TAC o SPECL [`(g:real^2->real^N) x`; `y:real^N`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; EXISTS_IN_IMAGE] THEN CONJ_TAC THENL
     [EXISTS_TAC `R:real^2->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[REAL_NOT_LE] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]]);;

let MOI_LGB1_WSMALL = prove
 (`!(c:(real^N->bool)->bool) (g:real^2->real^N) w.
     g continuous_on std_triangle /\
     open_in (subtopology euclidean (complex_boundary c)) w /\
     IMAGE g (relative_frontier std_triangle) SUBSET w
     ==> ?d. &0 < d /\
             !x y. x IN relative_frontier std_triangle /\ y IN complex_boundary c /\
                   dist(y,g x) < d ==> y IN w`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `o1:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`IMAGE (g:real^2->real^N) (relative_frontier std_triangle)`;
                 `(:real^N) DIFF o1`] SEPARATE_COMPACT_CLOSED) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
        ASM_REWRITE_TAC[] THEN
        MP_TAC MOI_LTD_STD_TRIANGLE_BASIC THEN
        SIMP_TAC[relative_frontier; CLOSURE_CLOSED] THEN SET_TAC[];
        MATCH_MP_TAC COMPACT_RELATIVE_FRONTIER_BOUNDED THEN
        MESON_TAC[MOI_LTD_STD_TRIANGLE_BASIC; COMPACT_IMP_BOUNDED]];
      REWRITE_TAC[GSYM OPEN_CLOSED] THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `IMAGE (g:real^2->real^N) (relative_frontier std_triangle) SUBSET w` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sep")) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^N`] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[IN_INTER] THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  USE_THEN "sep" (MP_TAC o SPECL [`(g:real^2->real^N) x`; `y:real^N`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE; IN_DIFF; IN_UNIV]; ALL_TAC] THEN
  MP_TAC(ISPECL [`y:real^N`; `(g:real^2->real^N) x`] DIST_SYM) THEN
  ASM_REAL_ARITH_TAC);;

let MOI_LGB1_SKEL = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs.
     moi_lgb1_fix c tt u h h' kk L g Q hs
     ==> ?d. &0 < d /\
             !R R' x y. R IN L /\ R' IN L /\ DISJOINT R R' /\ x IN R /\
                        y IN IMAGE g R' /\ y IN Q /\
                        (?s. s IN tt /\ aff_dim s <= &1 /\ y IN s)
                        ==> d <= dist(g x,y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  SUBGOAL_THEN `!r. r IN L ==> compact (IMAGE (g:real^2->real^N) r)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_COMPACT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (UNIONS {s:real^N->bool | s IN tt /\ aff_dim s <= &1})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `tt:(real^N->bool)->bool` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[simplicial_complex]; SET_TAC[]];
      REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CLOSED]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\(p:(real^2->bool)#(real^2->bool)) d.
       !x y. x IN FST p /\ y IN IMAGE (g:real^2->real^N) (SND p) /\ y IN Q /\
             y IN UNIONS {s:real^N->bool | s IN tt /\ aff_dim s <= &1}
             ==> d <= dist(g x,y)`;
    `{(R,R') | R IN L /\ R' IN L /\ DISJOINT (R:real^2->bool) R'}`]
    MOI_LGB1_FINITE_EPS) THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `(L:(real^2->bool)->bool) CROSS (L:(real^2->bool)->bool)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_CROSS THEN ASM_MESON_TAC[simplicial_complex];
        REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_CROSS] THEN SIMP_TAC[]];
      MESON_TAC[REAL_LE_TRANS];
      MAP_EVERY X_GEN_TAC [`R:real^2->bool`; `R':real^2->bool`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`IMAGE (g:real^2->real^N) R`;
                     `IMAGE (g:real^2->real^N) R' INTER Q INTER
                      UNIONS {s:real^N->bool | s IN tt /\ aff_dim s <= &1}`]
        SEPARATE_COMPACT_CLOSED) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[COMPACT_IMP_CLOSED; CLOSED_INTER] THEN
        UNDISCH_TAC `moi_lgb_tgeneric tt L (g:real^2->real^N) Q` THEN
        REWRITE_TAC[moi_lgb_tgeneric] THEN
        DISCH_THEN(MP_TAC o SPECL [`R:real^2->bool`; `R':real^2->bool`] o last o CONJUNCTS) THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_UNIONS; IN_ELIM_THM; DISJOINT] THEN
        MESON_TAC[];
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[FUN_IN_IMAGE; IN_INTER]]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sk")) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`R:real^2->bool`; `R':real^2->bool`; `x:real^2`; `y:real^N`] THEN
  STRIP_TAC THEN
  USE_THEN "sk" (MP_TAC o SPECL [`R:real^2->bool`; `R':real^2->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* C10. Cone points.  SEQ: points chosen one at a time, each condition      *)
(* depending only on the earlier choices.  CONE_POINTS: for a finite set of *)
(* 2-dimensional cells with a map affine and injective on each, there are   *)
(* cone points in their relative interiors whose images avoid every affine *)
(* hull of points of moi_lgb1_xc (vertex values, chart vertices, images of  *)
(* cell vertices) not containing the plane of the cell, and the cone edges  *)
(* of cells with different planes have disjoint images.                     *)
(* ------------------------------------------------------------------------- *)

let MOI_LGB1_SEQ = prove
 (`!n (G:num->(num->real^2)->real^2->bool).
     (!i c c' x. (!j. j < i ==> c j = c' j) ==> (G i c x <=> G i c' x)) /\
     (!i c. i < n ==> ?x. G i c x)
     ==> ?b. !i. i < n ==> G i b (b i)`,
  INDUCT_TAC THENL [REWRITE_TAC[LT] THEN MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `G:num->(num->real^2)->real^2->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "loc") (LABEL_TAC "ex")) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `G:num->(num->real^2)->real^2->bool`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [USE_THEN "loc" ACCEPT_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN USE_THEN "ex" MATCH_MP_TAC THEN ASM_REWRITE_TAC[LT];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:num->real^2` (LABEL_TAC "ih")) THEN
  USE_THEN "ex" (MP_TAC o SPECL [`n:num`; `b:num->real^2`]) THEN
  REWRITE_TAC[LT] THEN DISCH_THEN(X_CHOOSE_TAC `x:real^2`) THEN
  EXISTS_TAC `\i. if i = n then x else (b:num->real^2) i` THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[LT] THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC) THENL
   [REWRITE_TAC[] THEN
    SUBGOAL_THEN `(G:num->(num->real^2)->real^2->bool) n
                    (\i. if i = n then x else (b:num->real^2) i) x <=> G n b x`
    (fun th -> ASM_REWRITE_TAC[th]) THEN
    USE_THEN "loc" MATCH_MP_TAC THEN REWRITE_TAC[] THEN MESON_TAC[LT_REFL];
    SUBGOAL_THEN `~(i:num = n)` ASSUME_TAC THENL
     [ASM_MESON_TAC[LT_REFL]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(G:num->(num->real^2)->real^2->bool) i
                    (\i. if i = n then x else (b:num->real^2) i) (b i) <=> G i b (b i)`
    SUBST1_TAC THENL
     [USE_THEN "loc" MATCH_MP_TAC THEN REWRITE_TAC[] THEN ASM_MESON_TAC[LT_TRANS; LT_REFL];
      USE_THEN "ih" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

let MOI_LGB1_XC_MONO = prove
 (`!(psi:real^2->real^3) V HV HV'.
     HV SUBSET HV' ==> moi_lgb1_xc psi V HV SUBSET moi_lgb1_xc psi V HV'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_lgb1_xc] THEN
  MATCH_MP_TAC(SET_RULE `(a:real^3->bool) SUBSET a' /\ b SUBSET b'
                         ==> a UNION b SUBSET a' UNION b'`) THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_UNIONS THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `t:real^3->bool` THEN
  DISCH_THEN(X_CHOOSE_THEN `Y1:real^3->bool` (X_CHOOSE_THEN `Y2:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`Y1:real^3->bool`; `Y2:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_LGB1_SEG_BACK = prove
 (`!p q z:real^3 u. z = (&1 - u) % p + u % q /\ u < &1 ==> p IN affine hull {z,q}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[AFFINE_HULL_2; IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC [`inv(&1 - u)`; `--(inv(&1 - u) * u)`] THEN
  SUBGOAL_THEN `~(&1 - u = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [UNDISCH_TAC `~(&1 - u = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV] THEN VECTOR_ARITH_TAC);;

let MOI_LGB1_LINE_PLANE = prove
 (`!(p:real^3) q z PI.
     affine PI /\ ~(p IN PI) /\ z IN affine hull {p,q} /\ z IN PI
     ==> !y. y IN affine hull {p,q} /\ y IN PI ==> y = z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[AFFINE_HULL_2; IN_ELIM_THM] THEN STRIP_TAC THEN
  X_GEN_TAC `y:real^3` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u1:real` (X_CHOOSE_THEN `v1:real`
    STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  UNDISCH_TAC `~((p:real^3) IN PI)` THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(v1 = v:real)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(y:real^3 = z)` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `u1 = u:real` (fun th -> REWRITE_TAC[th]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3) = (v / (v - v1)) % y + (--(v1 / (v - v1))) % z` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `u1 = &1 - v1 /\ u = &1 - v` (CONJUNCTS_THEN SUBST1_TAC) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
    REWRITE_TAC[VECTOR_ARITH
     `(p:real^3) = (a % p + b % q) + (c % p + d % q) <=>
      (a + c - &1) % p + (b + d) % q = vec 0`] THEN
    SUBGOAL_THEN `~(v - v1 = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `v / (v - v1) * (&1 - v1) + --(v1 / (v - v1)) * (&1 - v) - &1 = &0 /\
                  v / (v - v1) * v1 + --(v1 / (v - v1)) * v = &0`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [UNDISCH_TAC `~(v - v1 = &0)` THEN CONV_TAC REAL_FIELD;
      REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID]];
    ALL_TAC] THEN
  FIRST_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [affine]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(v - v1 = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

let MOI_LGB1_AFFINE_COMB = prove
 (`!(a:real^2->real^N) l y P p q u.
     linear l /\ (!x. x IN P ==> a x = l x + y) /\ p IN P /\ q IN P /\
     ((&1 - u) % p + u % q) IN P
     ==> a ((&1 - u) % p + u % q) = (&1 - u) % a p + u % a q`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th; MATCH_MP LINEAR_CMUL th]) THEN
  VECTOR_ARITH_TAC);;

let MOI_LGB1_PLANES_NE = prove
 (`!A B:real^N->bool.
     aff_dim A = &2 /\ aff_dim B = &2 /\ ~(affine hull A = affine hull B)
     ==> ~(affine hull A SUBSET affine hull B)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`affine hull A:real^N->bool`; `affine hull B:real^N->bool`]
    AFF_DIM_EQ_AFFINE_HULL) THEN
  ASM_REWRITE_TAC[HULL_HULL; AFF_DIM_AFFINE_HULL; INT_LE_REFL]);;

let MOI_LGB1_CONE_DISJ = prove
 (`!(a:real^2->real^3) (phi:real^2->real^3) V BP BP' P P' bP bP' w w' YP.
     convex P /\ convex P' /\ aff_dim (IMAGE a P) = &2 /\ aff_dim (IMAGE a P') = &2 /\
     (?l y. linear l /\ !x. x IN P ==> a x = l x + y) /\
     (?l y. linear l /\ !x. x IN P' ==> a x = l x + y) /\
     bP IN P /\ bP' IN P' /\ w IN P /\ w' IN P' /\
     YP SUBSET IMAGE phi V /\ affine hull YP = affine hull (IMAGE a P) /\
     ~(affine hull (IMAGE a P) = affine hull (IMAGE a P')) /\
     a bP' IN BP /\ a w' IN BP /\ a w IN BP /\
     (!Y. Y SUBSET moi_lgb1_xc phi V BP /\ ~(affine hull (IMAGE a P) SUBSET affine hull Y)
          ==> ~(a bP IN affine hull Y)) /\
     (!Y. Y SUBSET moi_lgb1_xc phi V BP' /\ ~(affine hull (IMAGE a P') SUBSET affine hull Y)
          ==> ~(a bP' IN affine hull Y))
     ==> DISJOINT (IMAGE a (segment(bP,w))) (IMAGE a (segment(bP',w')))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (X_CHOOSE_THEN `l:real^2->real^3` (X_CHOOSE_THEN `y:real^3`
      STRIP_ASSUME_TAC))
   (CONJUNCTS_THEN2 (X_CHOOSE_THEN `l':real^2->real^3` (X_CHOOSE_THEN `y':real^3`
      STRIP_ASSUME_TAC))
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "gp") (LABEL_TAC "gp'")))))))))))))))))) THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
  X_GEN_TAC `z:real^3` THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `x:real^2` (CONJUNCTS_THEN2 (LABEL_TAC "zx") (LABEL_TAC "xs")))
    (X_CHOOSE_THEN `x':real^2` (CONJUNCTS_THEN2 (LABEL_TAC "zx'") (LABEL_TAC "xs'")))) THEN
  USE_THEN "xs" (MP_TAC o REWRITE_RULE[IN_SEGMENT]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "xt"))))) THEN
  USE_THEN "xs'" (MP_TAC o REWRITE_RULE[IN_SEGMENT]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t':real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "xt'"))))) THEN
  SUBGOAL_THEN `(x:real^2) IN P` ASSUME_TAC THENL
   [USE_THEN "xt" SUBST1_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[CONVEX_ALT] o
      check (fun th -> concl th = `convex (P:real^2->bool)`)) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(x':real^2) IN P'` ASSUME_TAC THENL
   [USE_THEN "xt'" SUBST1_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[CONVEX_ALT] o
      check (fun th -> concl th = `convex (P':real^2->bool)`)) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3) = (&1 - t) % (a:real^2->real^3) bP + t % a w` (LABEL_TAC "z1") THENL
   [USE_THEN "zx" SUBST1_TAC THEN USE_THEN "xt" SUBST1_TAC THEN
    MATCH_MP_TAC MOI_LGB1_AFFINE_COMB THEN
    MAP_EVERY EXISTS_TAC [`l:real^2->real^3`; `y:real^3`; `P:real^2->bool`] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "xt" (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3) = (&1 - t') % (a:real^2->real^3) bP' + t' % a w'` (LABEL_TAC "z2")
  THENL
   [USE_THEN "zx'" SUBST1_TAC THEN USE_THEN "xt'" SUBST1_TAC THEN
    MATCH_MP_TAC MOI_LGB1_AFFINE_COMB THEN
    MAP_EVERY EXISTS_TAC [`l':real^2->real^3`; `y':real^3`; `P':real^2->bool`] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "xt'" (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3) IN affine hull {(a:real^2->real^3) bP',a w'}` ASSUME_TAC THENL
   [REWRITE_TAC[AFFINE_HULL_2; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`&1 - t'`; `t':real`] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; USE_THEN "z2" ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3) IN affine hull (IMAGE (a:real^2->real^3) P)` ASSUME_TAC THENL
   [MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:real^2` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "zx" ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^2->real^3) bP IN affine hull {z,a w}` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LGB1_SEG_BACK THEN EXISTS_TAC `t:real` THEN
    CONJ_TAC THENL [USE_THEN "z1" ACCEPT_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REMOVE_THEN "zx" (K ALL_TAC) THEN REMOVE_THEN "zx'" (K ALL_TAC) THEN
  REMOVE_THEN "xt" (K ALL_TAC) THEN REMOVE_THEN "xt'" (K ALL_TAC) THEN
  REMOVE_THEN "z1" (K ALL_TAC) THEN REMOVE_THEN "z2" (K ALL_TAC) THEN
  SUBGOAL_THEN `~((a:real^2->real^3) bP' IN affine hull (IMAGE a P))` ASSUME_TAC THENL
   [SUBGOAL_THEN `affine hull (IMAGE (a:real^2->real^3) P) = affine hull YP` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "gp'" MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (phi:real^2->real^3) V` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[moi_lgb1_xc] THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `affine hull (YP:real^3->bool) = affine hull (IMAGE (a:real^2->real^3) P)`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_LGB1_PLANES_NE THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(ASSUME_TAC o SYM) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`phi:real^2->real^3`; `V:real^2->bool`; `BP:real^3->bool`;
                 `{(a:real^2->real^3) bP',a w'}`; `YP:real^3->bool`] MOI_LGB1_XC_INTER) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `B0:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `affine hull B0 = {z:real^3}` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`(a:real^2->real^3) bP'`; `(a:real^2->real^3) w'`; `z:real^3`;
                   `affine hull (IMAGE (a:real^2->real^3) P)`] MOI_LGB1_LINE_PLANE) THEN
    ASM_REWRITE_TAC[AFFINE_AFFINE_HULL] THEN DISCH_THEN(LABEL_TAC "lp") THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_SING] THEN
    X_GEN_TAC `y0:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(fun th -> USE_THEN "lp" (fun lp -> ACCEPT_TAC(MATCH_MP lp th)));
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!q:real^3. affine hull (q INSERT B0) = affine hull {q,z}` ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `(q:real^3) INSERT B0 = {q} UNION B0 /\ {q,z} = {q} UNION {z:real^3}`
    (CONJUNCTS_THEN SUBST1_TAC) THENL [SET_TAC[]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[HULL_UNION_RIGHT] THEN
    REWRITE_TAC[ASSUME `affine hull B0 = {z:real^3}`; AFFINE_HULL_SING];
    ALL_TAC] THEN
  USE_THEN "gp" (MP_TAC o SPEC `(a:real^2->real^3) w INSERT B0`) THEN
  ASM_REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[INSERT_SUBSET] THEN CONJ_TAC THENL
     [REWRITE_TAC[moi_lgb1_xc; IN_UNION] THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`affine hull (IMAGE (a:real^2->real^3) P)`;
                   `affine hull {(a:real^2->real^3) w,z}`] AFF_DIM_SUBSET) THEN
    ASM_REWRITE_TAC[AFF_DIM_AFFINE_HULL] THEN
    MP_TAC(ISPEC `{(a:real^2->real^3) w,z}` AFF_DIM_LE_CARD) THEN
    SIMP_TAC[FINITE_INSERT; FINITE_EMPTY; CARD_CLAUSES; IN_INSERT; NOT_IN_EMPTY] THEN
    COND_CASES_TAC THEN REWRITE_TAC[ARITH] THEN INT_ARITH_TAC;
    ONCE_REWRITE_TAC[SET_RULE `{p,q} = {q,p:real^3}`] THEN ASM_REWRITE_TAC[]]);;

let MOI_LGB1_CONE_POINTS = prove
 (`!(C2:(real^2->bool)->bool) (a:real^2->real^3) (phi:real^2->real^3) V HV.
     FINITE C2 /\ FINITE V /\ FINITE HV /\
     (!P. P IN C2 ==> polytope P /\ convex P /\ aff_dim P = &2 /\
                      aff_dim (IMAGE a P) = &2 /\
                      (?l y. linear l /\ !x. x IN P ==> a x = l x + y) /\
                      (!x y. x IN P /\ y IN P /\ a x = a y ==> x = y) /\
                      (?YP. YP SUBSET IMAGE phi V /\ affine hull YP = affine hull (IMAGE a P)))
     ==> ?b. (!P. P IN C2 ==> b P IN relative_interior P) /\
             (!P Y. P IN C2 /\
                    Y SUBSET moi_lgb1_xc phi V
                      (HV UNION {a w | w | ?P'. P' IN C2 /\ w extreme_point_of P'}) /\
                    ~(affine hull (IMAGE a P) SUBSET affine hull Y)
                    ==> ~(a (b P) IN affine hull Y)) /\
             (!P P' w w'. P IN C2 /\ P' IN C2 /\
                          ~(affine hull (IMAGE a P) = affine hull (IMAGE a P')) /\
                          w extreme_point_of P /\ w' extreme_point_of P'
                          ==> DISJOINT (IMAGE a (segment(b P,w)))
                                       (IMAGE a (segment(b P',w'))))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c2")))) THEN
  ABBREV_TAC `CV = {(a:real^2->real^3) w | w | ?P'. P' IN C2 /\ w extreme_point_of P'}` THEN
  SUBGOAL_THEN `FINITE (CV:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "CV" THEN
    SUBGOAL_THEN `{(a:real^2->real^3) w | w | ?P'. P' IN C2 /\ w extreme_point_of P'} =
                  IMAGE a (UNIONS (IMAGE (\P'. {w | w extreme_point_of P'}) C2))`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIONS; IN_ELIM_THM; EXISTS_IN_IMAGE] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC[FINITE_UNIONS] THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `P:real^2->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC FINITE_POLYHEDRON_EXTREME_POINTS THEN
    MATCH_MP_TAC POLYTOPE_IMP_POLYHEDRON THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`C2:(real^2->bool)->bool`; `CARD(C2:(real^2->bool)->bool)`]
    HAS_SIZE_INDEX) THEN
  ASM_REWRITE_TAC[HAS_SIZE] THEN
  ABBREV_TAC `m = CARD(C2:(real^2->bool)->bool)` THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->real^2->bool` (CONJUNCTS_THEN2
    (LABEL_TAC "fin") (LABEL_TAC "fu"))) THEN
  MP_TAC(ISPECL
   [`m:num`;
    `\i (c:num->real^2) x.
       x IN relative_interior (f i) /\
       !Y. Y SUBSET moi_lgb1_xc phi V
                      (HV UNION CV UNION {(a:real^2->real^3) (c j) | j | (j:num) < i}) /\
           ~(affine hull (IMAGE a (f i)) SUBSET affine hull Y)
           ==> ~(a x IN affine hull Y)`] MOI_LGB1_SEQ) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`i:num`; `c:num->real^2`; `c':num->real^2`; `x:real^2`] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `{(a:real^2->real^3) (c j) | j | (j:num) < i} = {a (c' j) | j | j < i}`
      (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `c:num->real^2`] THEN DISCH_TAC THEN
    USE_THEN "fin" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
    USE_THEN "c2" (MP_TAC o SPEC `(f:num->real^2->bool) i`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `l:real^2->real^3` (X_CHOOSE_THEN `y:real^3`
         STRIP_ASSUME_TAC)) (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))))) THEN
    MP_TAC(ISPECL [`affine hull (IMAGE (a:real^2->real^3) (f(i:num)))`;
                   `moi_lgb1_xc phi V
                      (HV UNION CV UNION {(a:real^2->real^3) (c j) | j | (j:num) < i})`;
                   `relative_interior (IMAGE (a:real^2->real^3) (f(i:num)))`]
      MOI_LGB1_GEN_EXISTS) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[AFFINE_AFFINE_HULL; OPEN_IN_RELATIVE_INTERIOR] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_LGB1_XC_FINITE THEN ASM_REWRITE_TAC[FINITE_UNION] THEN
        SUBGOAL_THEN `{(a:real^2->real^3) (c j) | j | (j:num) < i} =
                      IMAGE (\j. a (c j)) {j | j < i}` SUBST1_TAC THENL
         [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
          SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT]];
        SUBGOAL_THEN `convex (IMAGE (a:real^2->real^3) (f(i:num)))` ASSUME_TAC THENL
         [SUBGOAL_THEN `IMAGE (a:real^2->real^3) (f(i:num)) = IMAGE (\x. l x + y) (f i)`
          SUBST1_TAC THENL
           [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[];
            MATCH_MP_TAC MOI_FGP_CONVEX_AFFINE_IMAGE THEN ASM_REWRITE_TAC[]];
          ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY] THEN DISCH_TAC THEN
          UNDISCH_TAC `aff_dim (IMAGE (a:real^2->real^3) (f(i:num))) = &2` THEN
          ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^3` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`a:real^2->real^3`; `l:real^2->real^3`; `y:real^3`;
                   `(f:num->real^2->bool) i`] MOI_LGB1_RELINT_AFFINE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    UNDISCH_TAC `(p:real^3) IN IMAGE (a:real^2->real^3) (relative_interior (f(i:num)))` THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num->real^2` (LABEL_TAC "cg")) THEN
  EXISTS_TAC `\P:real^2->bool. (c:num->real^2) (@i. i < m /\ f i = P)` THEN
  SUBGOAL_THEN `!P:real^2->bool. P IN C2
                ==> (@i. i < m /\ (f:num->real^2->bool) i = P) < m /\
                    f (@i. i < m /\ f i = P) = P`
  (LABEL_TAC "ix") THENL
   [X_GEN_TAC `P:real^2->bool` THEN DISCH_TAC THEN CONV_TAC SELECT_CONV THEN
    USE_THEN "fu" (MP_TAC o C MATCH_MP (ASSUME `(P:real^2->bool) IN C2`)) THEN
    REWRITE_TAC[EXISTS_UNIQUE] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `P:real^2->bool` THEN DISCH_TAC THEN
    USE_THEN "ix" (MP_TAC o SPEC `P:real^2->bool`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `i = @i. i < m /\ (f:num->real^2->bool) i = P` THEN STRIP_TAC THEN
    USE_THEN "cg" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    UNDISCH_TAC `(f:num->real^2->bool) i = P` THEN DISCH_THEN SUBST1_TAC THEN SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`P:real^2->bool`; `Y:real^3->bool`] THEN STRIP_TAC THEN
    USE_THEN "ix" (MP_TAC o SPEC `P:real^2->bool`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `i = @i. i < m /\ (f:num->real^2->bool) i = P` THEN STRIP_TAC THEN
    USE_THEN "cg" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    UNDISCH_TAC `(f:num->real^2->bool) i = P` THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `moi_lgb1_xc phi V
                  (HV UNION {(a:real^2->real^3) w | w | ?P'. P' IN C2 /\ w extreme_point_of P'})` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_LGB1_XC_MONO THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j w w'. i < m /\ j < m /\ j < i /\
               ~(affine hull (IMAGE (a:real^2->real^3) (f i)) = affine hull (IMAGE a (f j))) /\
               w extreme_point_of (f i) /\ w' extreme_point_of (f j)
               ==> DISJOINT (IMAGE a (segment((c:num->real^2) i,w)))
                            (IMAGE a (segment(c j,w')))`
  (LABEL_TAC "dj") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `(f:num->real^2->bool) i IN C2 /\ f j IN C2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN USE_THEN "fin" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "c2" (STRIP_ASSUME_TAC o C MATCH_MP
      (ASSUME `(f:num->real^2->bool) i IN C2`)) THEN
    USE_THEN "c2" (STRIP_ASSUME_TAC o C MATCH_MP
      (ASSUME `(f:num->real^2->bool) j IN C2`)) THEN
    USE_THEN "cg" (STRIP_ASSUME_TAC o BETA_RULE o C MATCH_MP (ASSUME `(i:num) < m`)) THEN
    USE_THEN "cg" (STRIP_ASSUME_TAC o BETA_RULE o C MATCH_MP (ASSUME `(j:num) < m`)) THEN
    MATCH_MP_TAC MOI_LGB1_CONE_DISJ THEN
    MAP_EVERY EXISTS_TAC
     [`phi:real^2->real^3`; `V:real^2->bool`;
      `HV UNION CV UNION {(a:real^2->real^3) (c k) | k | (k:num) < i}`;
      `HV UNION CV UNION {(a:real^2->real^3) (c k) | k | (k:num) < j}`;
      `(f:num->real^2->bool) i`; `(f:num->real^2->bool) j`;
      `YP:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      ASM_MESON_TAC[];
      ASM_MESON_TAC[MOI_LGB1_RELINT_IN];
      ASM_MESON_TAC[MOI_LGB1_RELINT_IN];
      ASM_MESON_TAC[extreme_point_of];
      ASM_MESON_TAC[extreme_point_of];
      REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN DISJ2_TAC THEN DISJ2_TAC THEN
      EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_UNION] THEN DISJ2_TAC THEN DISJ1_TAC THEN EXPAND_TAC "CV" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
      REWRITE_TAC[IN_UNION] THEN DISJ2_TAC THEN DISJ1_TAC THEN EXPAND_TAC "CV" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`P:real^2->bool`; `P':real^2->bool`; `w:real^2`; `w':real^2`] THEN
  STRIP_TAC THEN
  USE_THEN "ix" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(P:real^2->bool) IN C2`)) THEN
  USE_THEN "ix" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(P':real^2->bool) IN C2`)) THEN
  ABBREV_TAC `i = @i. i < m /\ (f:num->real^2->bool) i = P` THEN
  ABBREV_TAC `j = @i. i < m /\ (f:num->real^2->bool) i = P'` THEN
  SUBGOAL_THEN `~(i:num = j)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC
     `~(affine hull (IMAGE (a:real^2->real^3) P) = affine hull (IMAGE a P'))` THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE `~(i:num = j) ==> j < i \/ i < j`)) THENL
   [USE_THEN "dj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[DISJOINT_SYM] THEN USE_THEN "dj" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* C11. The moved configuration.  moi_lgb1_gen: the vertex values phi and   *)
(* ranks rk produced by MOI_LGB1_MOVES for the movers of the chart step (on *)
(* the vertices of L3, with the chart vertices of H).  Such moves exist     *)
(* within any eta and stay in the half-space; the interpolation a is        *)
(* injective on the union of two meeting simplices of L3.                   *)
(* ------------------------------------------------------------------------- *)

let moi_lgb1_gen = new_definition
 `moi_lgb1_gen (tt:(real^N->bool)->bool) (h:real^N->real^3) kk L (g:real^2->real^N)
               phi rk <=>
    (!v. ~(v IN moi_lgb1_kv L g kk) ==> phi v = h (g v)) /\
    (!v. v IN moi_lgb1_kv L g kk
         ==> phi v IN moi_lgb1_space (relative_frontier std_triangle) v) /\
    (!v w. v IN moi_lgb1_kv L g kk /\ w IN moi_lgb1_kv L g kk /\ rk v = rk w ==> v = w) /\
    (!v w. v IN moi_lgb1_kv L g kk /\ w IN moi_lgb1_kv L g kk /\
           v IN relative_frontier std_triangle /\ ~(w IN relative_frontier std_triangle)
           ==> rk v < rk w) /\
    (!p Y. p IN moi_lgb1_kv L g kk /\
           Y SUBSET moi_lgb1_xc (moi_lgb1_at rk (moi_lgb1_kv L g kk) (\v. h (g v)) phi p)
                      {v | {v} IN moi_lgb1_l3 L g (moi_lgb1_th tt kk)}
                      {z | {z} IN IMAGE (IMAGE h) (moi_lgb1_th tt kk)} /\
           ~(moi_lgb1_space (relative_frontier std_triangle) p SUBSET affine hull Y)
           ==> ~(phi p IN affine hull Y))`;;

let MOI_LGB1_KV_FACTS = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs v.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ v IN moi_lgb1_kv L g kk
     ==> {v} IN moi_lgb1_lm L (moi_lgb1_kv L g kk) /\
         {v} IN moi_lgb1_l3 L g (moi_lgb1_th tt kk)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  SUBGOAL_THEN `{v:real^2} IN moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_lgb1_lm; IN_ELIM_THM] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(v:real^2) IN moi_lgb1_kv L (g:real^2->real^N) kk` THEN
      SIMP_TAC[moi_lgb1_kv; IN_ELIM_THM];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_SING] THEN
      EXISTS_TAC `v:real^2` THEN ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_LGB1_LM_L3 THEN ASM_REWRITE_TAC[]]);;

let MOI_LGB1_POS = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs v.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\
     {v} IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\ hs = {z:real^3 | &0 <= z$3} /\
     ~(v IN relative_frontier std_triangle)
     ==> &0 < ((h:real^N->real^3) (g v))$3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `{v:real^2}`]
    MOI_LGB1_L3_A0) THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES; SING_SUBSET] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(v:real^2) IN std_triangle` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_UNIONS; IN_SING]; ALL_TAC] THEN
  SUBGOAL_THEN `~((g:real^2->real^N) v IN complex_boundary c)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lt_singular_disk (c:(real^N->bool)->bool) g` THEN
    REWRITE_TAC[moi_lt_singular_disk] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^2`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_lgb1_fix (c:(real^N->bool)->bool) tt u h h' kk L g Q hs` THEN
  REWRITE_TAC[moi_lgb1_fix] THEN
  DISCH_THEN(MP_TAC o SPEC `(g:real^2->real^N) v` o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(h:real^N->real^3) ((g:real^2->real^N) v) IN hs` MP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC);;

let MOI_LGB1_HS_KEEP = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs.
     moi_lgb1_fix c tt u h h' kk L g Q hs
     ==> ?e. &0 < e /\
             !v p. {v} IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\
                   ~(v IN relative_frontier std_triangle) /\
                   norm(p - h (g v)) < e ==> p IN hs`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  SUBGOAL_THEN `hs = (:real^3) \/ hs = {z:real^3 | &0 <= z$3}` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_lgb1_fix]; EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[IN_UNIV; REAL_LT_01];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `g:real^2->real^N`;
                 `moi_lgb1_th (tt:(real^N->bool)->bool) kk`] MOI_LGB1_L3_SC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\v:real^2 e. ~(v IN relative_frontier std_triangle)
                  ==> e <= ((h:real^N->real^3) ((g:real^2->real^N) v))$3`;
    `{v:real^2 | {v} IN moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)}`]
    MOI_LGB1_FINITE_EPS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE_INJ THEN REWRITE_TAC[] THEN
      CONJ_TAC THENL [SET_TAC[]; ASM_MESON_TAC[simplicial_complex]];
      MESON_TAC[REAL_LE_TRANS];
      X_GEN_TAC `v:real^2` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
      ASM_CASES_TAC `(v:real^2) IN relative_frontier std_triangle` THENL
       [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_LT_01];
        EXISTS_TAC `((h:real^N->real^3) ((g:real^2->real^N) v))$3` THEN
        ASM_REWRITE_TAC[REAL_LE_REFL] THEN MATCH_MP_TAC MOI_LGB1_POS THEN
        MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
          `u:real^N->bool`; `h':real^3->real^N`; `kk:real^N->bool`;
          `L:(real^2->bool)->bool`; `Q:real^N->bool`; `hs:real^3->bool`] THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ee")) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`v:real^2`; `p:real^3`] THEN STRIP_TAC THEN
  USE_THEN "ee" (MP_TAC o SPEC `v:real^2`) THEN REWRITE_TAC[IN_ELIM_THM] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  MP_TAC(ISPECL [`p - (h:real^N->real^3) ((g:real^2->real^N) v)`; `3`] COMPONENT_LE_NORM) THEN
  SIMP_TAC[VECTOR_SUB_COMPONENT; DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC);;

let MOI_LGB1_BD_ZERO = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs v.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\
     {v} IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\ v IN relative_frontier std_triangle
     ==> hs = {z:real^3 | &0 <= z$3} /\ ((h:real^N->real^3) (g v))$3 = &0 /\
         (h:real^N->real^3) (g v) IN hs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `{v:real^2}`]
    MOI_LGB1_L3_A0) THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES; SING_SUBSET] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(h:real^N->real^3) ((g:real^2->real^N) v) IN hs` ASSUME_TAC THENL
   [ASM SET_TAC[]; ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `(v:real^2) IN std_triangle` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_UNIONS; IN_SING]; ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^2->real^N) v IN complex_boundary c` MP_TAC THENL
   [UNDISCH_TAC `moi_lt_singular_disk (c:(real^N->bool)->bool) g` THEN
    REWRITE_TAC[moi_lt_singular_disk] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^2`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_lgb1_fix (c:(real^N->bool)->bool) tt u h h' kk L g Q hs` THEN
  REWRITE_TAC[moi_lgb1_fix] THEN
  DISCH_THEN(MP_TAC o SPEC `(g:real^2->real^N) v` o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let MOI_LGB1_GEN_MOVES = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs eta.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ &0 < eta
     ==> ?phi rk. moi_lgb1_gen tt h kk L g phi rk /\
                  moi_lgb1_near (moi_lgb1_l3 L g (moi_lgb1_th tt kk)) (\v. h (g v)) phi hs
                    (relative_frontier std_triangle) eta`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  SUBGOAL_THEN `hs = (:real^3) \/ hs = {z:real^3 | &0 <= z$3}` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_lgb1_fix]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`] MOI_LGB1_HS_KEEP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "hk"))) THEN
  ABBREV_TAC `L3 = moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)` THEN
  ABBREV_TAC `KV = moi_lgb1_kv L (g:real^2->real^N) kk` THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `g:real^2->real^N`;
                 `moi_lgb1_th (tt:(real^N->bool)->bool) kk`] MOI_LGB1_L3_SC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LGB1_H_SC THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `u:real^N->bool`; `h':real^3->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{v:real^2 | {v} IN L3}`; `KV:real^2->bool`;
                 `relative_frontier std_triangle`;
                 `\v. (h:real^N->real^3) ((g:real^2->real^N) v)`;
                 `{z:real^3 | {z} IN IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)}`;
                 `min eta e1`] MOI_LGB1_MOVES) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE_INJ THEN REWRITE_TAC[] THEN
      CONJ_TAC THENL [SET_TAC[]; ASM_MESON_TAC[simplicial_complex]];
      EXPAND_TAC "KV" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `v:real^2` THEN
      DISCH_TAC THEN EXPAND_TAC "L3" THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                     `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                     `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                     `hs:real^3->bool`; `v:real^2`] MOI_LGB1_KV_FACTS) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      MATCH_MP_TAC FINITE_IMAGE_INJ THEN REWRITE_TAC[] THEN
      CONJ_TAC THENL [SET_TAC[]; ASM_MESON_TAC[simplicial_complex]];
      ASM_REWRITE_TAC[REAL_LT_MIN];
      X_GEN_TAC `v:real^2` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                     `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                     `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                     `hs:real^3->bool`; `v:real^2`] MOI_LGB1_BD_ZERO) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "L3" THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                     `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                     `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                     `hs:real^3->bool`; `v:real^2`] MOI_LGB1_KV_FACTS) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `phi:real^2->real^3` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `rk:real^2->num` THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "m1") (CONJUNCTS_THEN2 (LABEL_TAC "m2")
    (CONJUNCTS_THEN2 (LABEL_TAC "m3") (CONJUNCTS_THEN2 (LABEL_TAC "m4") (LABEL_TAC "m5"))))) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[moi_lgb1_gen] THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_lgb1_near] THEN X_GEN_TAC `v:real^2` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(h:real^N->real^3) ((g:real^2->real^N) v) IN hs` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `{v:real^2}`]
      MOI_LGB1_L3_A0) THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; SING_SUBSET] THEN STRIP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(v:real^2) IN KV` THENL
   [USE_THEN "m2" (MP_TAC o C MATCH_MP (ASSUME `(v:real^2) IN KV`)) THEN
    REWRITE_TAC[moi_lgb1_space] THEN
    ASM_CASES_TAC `(v:real^2) IN relative_frontier std_triangle` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN STRIP_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[REAL_LTE_TRANS; REAL_MIN_MIN]; ALL_TAC] THEN
      FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (is_disj o concl)) THEN
      ASM_REWRITE_TAC[IN_UNIV; IN_ELIM_THM; REAL_LE_REFL];
      CONJ_TAC THENL [ASM_MESON_TAC[REAL_LTE_TRANS; REAL_MIN_MIN]; ALL_TAC] THEN
      USE_THEN "hk" MATCH_MP_TAC THEN EXISTS_TAC `v:real^2` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[REAL_LTE_TRANS; REAL_MIN_MIN]];
    USE_THEN "m1" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `~((v:real^2) IN KV)`)]) THEN
    ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                   `hs:real^3->bool`; `v:real^2`] MOI_LGB1_BD_ZERO) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [EXPAND_TAC "L3" THEN ASM_REWRITE_TAC[];
                                           SIMP_TAC[]]]);;

let MOI_LGB1_FACE_VERTEX = prove
 (`!(K:(real^2->bool)->bool) R f.
     simplicial_complex K /\ R IN K /\ f face_of R /\ ~(f = {})
     ==> ?w. w extreme_point_of R /\ w IN f /\ {w} IN K`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `R:real^2->bool`] MOI_LGB1_VERTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`{v:real^2 | v extreme_point_of R}`; `f:real^2->bool`]
    FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(f:real^2->bool) face_of convex hull {v | v extreme_point_of R}`
  (fun th -> REWRITE_TAC[th]) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w0:real^2->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(w0:real^2->bool = {})` MP_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(f:real^2->bool = {})` THEN
    ASM_REWRITE_TAC[CONVEX_HULL_EMPTY];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN DISCH_THEN(X_CHOOSE_TAC `w:real^2`) THEN
  EXISTS_TAC `w:real^2` THEN
  SUBGOAL_THEN `(w:real^2) extreme_point_of R` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[HULL_INC]);;

let MOI_LGB1_INJ_PAIR = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_gen tt h kk L g phi rk /\
     moi_lgb1_interp (moi_lgb1_l3 L g (moi_lgb1_th tt kk)) phi a /\
     (!v. {v} IN L /\
          (!r. r IN L /\ v IN r ==> r IN moi_lgb1_l3 L g (moi_lgb1_th tt kk))
          ==> !x y. x IN UNIONS {r | r IN L /\ v IN r} /\
                    y IN UNIONS {r | r IN L /\ v IN r} /\ a x = a y ==> x = y)
     ==> !R R' x y. R IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\
                    R' IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\
                    ~(R INTER R' = {}) /\ x IN R UNION R' /\ y IN R UNION R' /\ a x = a y
                    ==> x = y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "st")))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  ABBREV_TAC `L3 = moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)` THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `g:real^2->real^N`;
                 `moi_lgb1_th (tt:(real^N->bool)->bool) kk`] MOI_LGB1_L3_SC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`R:real^2->bool`; `R':real^2->bool`; `x:real^2`; `y:real^2`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(R:real^2->bool) IN L /\ R' IN L` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `R:real^2->bool`; `R INTER R':real^2->bool`]
    MOI_LGB1_FACE_VERTEX) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:real^2) IN UNIONS {r | r IN L /\ w IN r} /\
                y IN UNIONS {r | r IN L /\ w IN r}` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN ASM SET_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `?R0. R0 IN moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk) /\
                      (w:real^2) IN R0` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `R0:real^2->bool` STRIP_ASSUME_TAC) THEN
    USE_THEN "st" (MP_TAC o SPEC `w:real^2`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `r:real^2->bool` THEN STRIP_TAC THEN
      EXPAND_TAC "L3" THEN MATCH_MP_TAC MOI_LGB1_MEET_LM_L3 THEN
      EXISTS_TAC `R0:real^2->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r z. r IN L3 /\ (w:real^2) IN r /\ z IN r
                      ==> (a:real^2->real^3) z = h ((g:real^2->real^N) z)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`r:real^2->bool`; `z:real^2`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`L3:(real^2->bool)->bool`; `phi:real^2->real^3`;
                   `\v. (h:real^N->real^3) ((g:real^2->real^N) v)`; `a:real^2->real^3`;
                   `\x. (h:real^N->real^3) ((g:real^2->real^N) x)`; `r:real^2->bool`]
      MOI_LGB1_INTERP_AGREE) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ALL_TAC; DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "L3" THEN MATCH_MP_TAC MOI_LGB1_A0_INTERP THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `v:real^2` THEN DISCH_TAC THEN
    UNDISCH_TAC `moi_lgb1_gen tt (h:real^N->real^3) kk L (g:real^2->real^N) phi rk` THEN
    REWRITE_TAC[moi_lgb1_gen] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    REWRITE_TAC[] THEN EXISTS_TAC `r:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[moi_lgb1_lm; IN_ELIM_THM] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `v:real^2` THEN
    ASM_MESON_TAC[extreme_point_of];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^2->real^3) x = h ((g:real^2->real^N) x) /\ a y = h (g y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
    ASM_MESON_TAC[IN_UNION; IN_INTER];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `w:real^2`]
    MOI_LGB1_G_INJ_STAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(g:real^2->real^N) x IN u /\ g y IN u` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `R:real^2->bool`]
      MOI_LGB1_L3_A0) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `R':real^2->bool`]
      MOI_LGB1_L3_A0) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* C12. Relative transversality in chart coordinates (INV_FULL): for        *)
(* disjoint simplices R, R' of L3 and a chart simplex F through a common    *)
(* relative interior point z of their images (h'(z) in Q UNION kk), the     *)
(* traces of the images on F span the affine hull of F.  Moved case by      *)
(* MOI_LGB1_INV; unmoved case by input clause 4 at Q on the faces of R, R'  *)
(* that carry the traces.                                                   *)
(* ------------------------------------------------------------------------- *)

let MOI_LGB1_AFF_TRANSFER = prove
 (`!(f:real^M->real^N) l y s X.
     linear l /\ (!x. x IN s ==> f x = l x + y) /\ X SUBSET s /\
     affine hull X = affine hull s
     ==> affine hull (IMAGE f X) = affine hull (IMAGE f s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!t. t SUBSET s ==> IMAGE (f:real^M->real^N) t = IMAGE (\x. y + x) (IMAGE l t)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[SUBSET; VECTOR_ADD_SYM];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUBSET_REFL; AFFINE_HULL_TRANSLATION; AFFINE_HULL_LINEAR_IMAGE]);;

let MOI_LGB1_UNMOVED_TRACE = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a R Fh.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_gen tt h kk L g phi rk /\
     moi_lgb1_interp (moi_lgb1_l3 L g (moi_lgb1_th tt kk)) phi a /\
     R IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\ R INTER moi_lgb1_kv L g kk = {} /\
     Fh IN IMAGE (IMAGE h) (moi_lgb1_th tt kk)
     ==> (!x. x IN R ==> a x = h (g x)) /\
         ?RF. RF face_of R /\ RF IN L /\ IMAGE a R INTER Fh = IMAGE a RF /\
              RF = {x | x IN R /\ a x IN Fh}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  ABBREV_TAC `L3 = moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)` THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `g:real^2->real^N`;
                 `moi_lgb1_th (tt:(real^N->bool)->bool) kk`] MOI_LGB1_L3_SC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x. x IN R ==> (a:real^2->real^3) x = h ((g:real^2->real^N) x)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`L3:(real^2->bool)->bool`; `phi:real^2->real^3`;
                   `\v. (h:real^N->real^3) ((g:real^2->real^N) v)`; `a:real^2->real^3`;
                   `\x. (h:real^N->real^3) ((g:real^2->real^N) x)`; `R:real^2->bool`]
      MOI_LGB1_INTERP_AGREE) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "L3" THEN MATCH_MP_TAC MOI_LGB1_A0_INTERP THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `v:real^2` THEN DISCH_TAC THEN
    UNDISCH_TAC `moi_lgb1_gen tt (h:real^N->real^3) kk L (g:real^2->real^N) phi rk` THEN
    REWRITE_TAC[moi_lgb1_gen] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    UNDISCH_TAC `R INTER moi_lgb1_kv L (g:real^2->real^N) kk = {}` THEN
    MP_TAC(ISPECL [`R:real^2->bool`; `v:real^2`] extreme_point_of) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `R:real^2->bool`]
    MOI_LGB1_L3_A0) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `l:real^2->real^3` (X_CHOOSE_THEN `y:real^3`
      STRIP_ASSUME_TAC)) (X_CHOOSE_THEN `S0:real^3->bool` STRIP_ASSUME_TAC)))) THEN
  EXISTS_TAC `{x | x IN R /\ (a:real^2->real^3) x IN Fh}` THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `simplicial_complex (IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LGB1_H_SC THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `u:real^N->bool`; `h':real^3->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN R ==> (a:real^2->real^3) x IN S0` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(a:real^2->real^3) x = h ((g:real^2->real^N) x)` SUBST1_TAC THENL
     [MATCH_MP_TAC(ASSUME `!x. x IN R ==> (a:real^2->real^3) x = h ((g:real^2->real^N) x)`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `IMAGE ((h:real^N->real^3) o (g:real^2->real^N)) R SUBSET S0` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{x | x IN R /\ (a:real^2->real^3) x IN Fh} face_of R` ASSUME_TAC THENL
   [SUBGOAL_THEN `{x | x IN R /\ (a:real^2->real^3) x IN Fh} =
                  {x | x IN R /\ a x IN Fh INTER S0}` SUBST1_TAC THENL
     [UNDISCH_TAC `!x. x IN R ==> (a:real^2->real^3) x IN S0` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `{x | x IN R /\ (a:real^2->real^3) x IN S0} = R`
      (fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THENL
     [UNDISCH_TAC `!x. x IN R ==> (a:real^2->real^3) x IN S0` THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_LGB1_FACE_OF_AFFINE_PREIMAGE THEN
    MAP_EVERY EXISTS_TAC [`l:real^2->real^3`; `y:real^3`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_CON_SC_CONVEX THEN EXISTS_TAC `L:(real^2->bool)->bool` THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `!x. x IN R ==> (a:real^2->real^3) x = h ((g:real^2->real^N) x)` THEN
      ASM_MESON_TAC[];
      MATCH_MP_TAC MOI_CON_SC_CONVEX THEN
      EXISTS_TAC `IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)` THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `simplicial_complex (IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk))` THEN
      REWRITE_TAC[simplicial_complex] THEN
      DISCH_THEN(MP_TAC o SPECL [`Fh:real^3->bool`; `S0:real^3->bool`] o last o CONJUNCTS) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; SET_TAC[]]);;

let MOI_LGB1_SPAN_FROM_COUNT = prove
 (`!(A:real^N->bool) B s y.
     A UNION B SUBSET s /\ y IN A /\ y IN B /\
     aff_dim (affine hull A INTER affine hull B) = aff_dim A + aff_dim B - aff_dim s
     ==> affine hull (A UNION B) = affine hull s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC AFF_DIM_EQ_AFFINE_HULL THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`A:real^N->bool`; `B:real^N->bool`] MOI_FGP_AFF_DIM_HULLS_UNION) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `y:real^N` THEN
    ASM_SIMP_TAC[HULL_INC];
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC]);;

let MOI_LGB1_TGEN_CLAUSES = prove
 (`!(tt:(real^N->bool)->bool) L (g:real^2->real^N) Q.
     moi_lgb_tgeneric tt L g Q
     ==> (!r r' x x'. r IN L /\ r' IN L /\ ~(r INTER r' = {}) /\ x IN r /\ x' IN r' /\
                      g x = g x' /\ g x IN Q ==> x = x') /\
         (!r s. r IN L /\ aff_dim r = &2 /\ s IN tt /\ aff_dim s <= &2 /\
                IMAGE g r SUBSET s ==> IMAGE g r INTER Q = {}) /\
         (!e r1 r2 s. e IN L /\ r1 IN L /\ r2 IN L /\ ~(r1 = r2) /\ aff_dim e = &1 /\
                      aff_dim r1 = &2 /\ aff_dim r2 = &2 /\ e SUBSET r1 /\ e SUBSET r2 /\
                      s IN tt /\ aff_dim s = &2 /\ IMAGE g e SUBSET s /\
                      ~(IMAGE g e INTER Q = {})
                      ==> !s'. s' IN tt /\ aff_dim s' = &3
                               ==> ~(IMAGE g r1 UNION IMAGE g r2 SUBSET s')) /\
         (!r r' s. r IN L /\ r' IN L /\ DISJOINT r r' /\ s IN tt /\
                   IMAGE g r UNION IMAGE g r' SUBSET s /\
                   (!s'. s' IN tt /\ IMAGE g r UNION IMAGE g r' SUBSET s' ==> s SUBSET s') /\
                   ~(IMAGE g r INTER IMAGE g r' INTER Q = {})
                   ==> aff_dim s <= aff_dim (IMAGE g r) + aff_dim (IMAGE g r') /\
                       aff_dim (affine hull (IMAGE g r) INTER affine hull (IMAGE g r')) =
                       aff_dim (IMAGE g r) + aff_dim (IMAGE g r') - aff_dim s) /\
         (!r r' s. r IN L /\ r' IN L /\ DISJOINT r r' /\ s IN tt /\ aff_dim s <= &1
                   ==> DISJOINT (IMAGE g r INTER IMAGE g r' INTER Q) s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS o REWRITE_RULE[moi_lgb_tgeneric]) THEN
  ASM_REWRITE_TAC[]);;

let MOI_LGB1_NO_KK = prove
 (`!L (g:real^2->real^N) kk R y.
     simplicial_complex L /\ R IN L /\ R INTER moi_lgb1_kv L g kk = {} /\
     y IN IMAGE g R ==> ~(y IN kk)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(R:real^2->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `(y:real^N) IN IMAGE (g:real^2->real^N) R` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `(R:real^2->bool) face_of R` ASSUME_TAC THENL
   [MATCH_MP_TAC FACE_OF_REFL THEN MATCH_MP_TAC MOI_CON_SC_CONVEX THEN
    EXISTS_TAC `L:(real^2->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `R:real^2->bool`; `R:real^2->bool`]
    MOI_LGB1_FACE_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^2` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `R INTER moi_lgb1_kv L (g:real^2->real^N) kk = {}` THEN
  REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  DISCH_THEN(MP_TAC o SPEC `v:real^2`) THEN ASM_REWRITE_TAC[moi_lgb1_kv; IN_ELIM_THM] THEN
  EXISTS_TAC `R:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `y:real^N` THEN
  ASM_REWRITE_TAC[]);;

let MOI_LGB1_INV_UNMOVED = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a R R' Fh z.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_gen tt h kk L g phi rk /\
     moi_lgb1_interp (moi_lgb1_l3 L g (moi_lgb1_th tt kk)) phi a /\
     R IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\ R' IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\
     DISJOINT R R' /\ (R UNION R') INTER moi_lgb1_kv L g kk = {} /\
     Fh IN IMAGE (IMAGE h) (moi_lgb1_th tt kk) /\
     z IN IMAGE a R /\ z IN IMAGE a R' /\ z IN relative_interior Fh /\
     h' z IN Q UNION kk
     ==> affine hull ((IMAGE a R INTER Fh) UNION (IMAGE a R' INTER Fh)) = affine hull Fh`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `R:real^2->bool`; `Fh:real^3->bool`]
    MOI_LGB1_UNMOVED_TRACE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "aR") (X_CHOOSE_THEN `RF:real^2->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "tR") (LABEL_TAC "dR" o SYM)))))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `R':real^2->bool`; `Fh:real^3->bool`]
    MOI_LGB1_UNMOVED_TRACE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "aR'") (X_CHOOSE_THEN `RF':real^2->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "tR'") (LABEL_TAC "dR'" o SYM)))))) THEN
  USE_THEN "tR" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "tR'" (fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `Fh:real^3->bool`] MOI_LGB1_H_INV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "Fs" o SYM) (CONJUNCTS_THEN2 (LABEL_TAC "sF") (CONJUNCTS_THEN2
      (LABEL_TAC "hh'") (X_CHOOSE_THEN `l':real^3->real^N` (X_CHOOSE_THEN `y':real^N`
        (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "h'aff"))))))))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `s:real^N->bool`] MOI_LGB1_TH_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `lh:real^N->real^3` (X_CHOOSE_THEN `yh:real^3`
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "haff")))) (LABEL_TAC "hinj")))) THEN
  SUBGOAL_THEN `!x x':real^N. x IN u /\ x' IN u /\ (h:real^N->real^3) x = h x' ==> x = x'`
  (LABEL_TAC "hu") THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!r. r IN moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)
                    ==> IMAGE g r SUBSET u`
  (LABEL_TAC "gu") THENL
   [X_GEN_TAC `r:real^2->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `r:real^2->bool`]
      MOI_LGB1_L3_A0) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r rf. r IN moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk) /\
           (!x. x IN r ==> (a:real^2->real^3) x = h (g x)) /\
           rf = {x | x IN r /\ a x IN Fh}
           ==> !x. x IN rf ==> x IN r /\ a x = h (g x) /\ g x IN s`
  (LABEL_TAC "pt") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real^2` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `(a:real^2->real^3) x IN IMAGE h (s:real^N->bool)` MP_TAC THENL
     [USE_THEN "Fs" SUBST1_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(g:real^2->real^N) x = w` (fun th -> ASM_REWRITE_TAC[th]) THEN
    USE_THEN "hu" MATCH_MP_TAC THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "gu" (MP_TAC o SPEC `r:real^2->bool`) THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ASM SET_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  USE_THEN "pt" (MP_TAC o SPECL [`R:real^2->bool`; `RF:real^2->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN USE_THEN "aR" ACCEPT_TAC; DISCH_THEN(LABEL_TAC "pR")] THEN
  USE_THEN "pt" (MP_TAC o SPECL [`R':real^2->bool`; `RF':real^2->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN USE_THEN "aR'" ACCEPT_TAC; DISCH_THEN(LABEL_TAC "pR'")] THEN
  SUBGOAL_THEN `IMAGE (a:real^2->real^3) RF = IMAGE h (IMAGE (g:real^2->real^N) RF) /\
                IMAGE a RF' = IMAGE h (IMAGE g RF')` (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN CONJ_TAC THEN
    MATCH_MP_TAC(SET_RULE `(!x:real^2. x IN s ==> (f:real^2->real^3) x = g x)
                           ==> IMAGE f s = IMAGE g s`) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM IMAGE_UNION] THEN USE_THEN "Fs" (SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC MOI_LGB1_AFF_TRANSFER THEN
  MAP_EVERY EXISTS_TAC [`lh:real^N->real^3`; `yh:real^3`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `IMAGE (g:real^2->real^N) (RF UNION RF') SUBSET s` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNION] THEN X_GEN_TAC `x:real^2` THEN
    STRIP_TAC THENL
     [USE_THEN "pR" (MP_TAC o SPEC `x:real^2`); USE_THEN "pR'" (MP_TAC o SPEC `x:real^2`)] THEN
    ASM_SIMP_TAC[];
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `?x x'. x IN RF /\ x' IN RF' /\ (a:real^2->real^3) x = z /\ a x' = z`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(z:real^3) IN IMAGE (a:real^2->real^3) RF /\ z IN IMAGE a RF'` MP_TAC THENL
     [USE_THEN "tR" (SUBST1_TAC o SYM) THEN USE_THEN "tR'" (SUBST1_TAC o SYM) THEN
      REWRITE_TAC[IN_INTER] THEN
      SUBGOAL_THEN `(z:real^3) IN Fh` ASSUME_TAC THENL
       [MATCH_MP_TAC MOI_LGB1_RELINT_IN THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]];
    ALL_TAC] THEN
  USE_THEN "pR" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(x:real^2) IN RF`)) THEN
  USE_THEN "pR'" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(x':real^2) IN RF'`)) THEN
  SUBGOAL_THEN `(g:real^2->real^N) x' = g x` ASSUME_TAC THENL
   [USE_THEN "hinj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY (fun t -> UNDISCH_TAC t)
     [`(a:real^2->real^3) x = z`; `(a:real^2->real^3) x' = z`;
      `(a:real^2->real^3) x = h ((g:real^2->real^N) x)`;
      `(a:real^2->real^3) x' = h ((g:real^2->real^N) x')`] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h':real^3->real^N) z = g (x:real^2)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(a:real^2->real^3) x = z`)) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "hh'" (MP_TAC o SPEC `(h:real^N->real^3) ((g:real^2->real^N) x)`) THEN
    ANTS_TAC THENL
     [USE_THEN "Fs" (SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THEN USE_THEN "hinj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `RF SUBSET (R:real^2->bool) /\ RF' SUBSET (R':real^2->bool)` STRIP_ASSUME_TAC
  THENL [CONJ_TAC THEN MATCH_MP_TAC FACE_OF_IMP_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^2->real^N) x IN Q` ASSUME_TAC THENL
   [SUBGOAL_THEN `~((g:real^2->real^N) x IN kk)` MP_TAC THENL
     [MATCH_MP_TAC MOI_LGB1_NO_KK THEN
      MAP_EVERY EXISTS_TAC [`L:(real^2->bool)->bool`; `g:real^2->real^N`; `R:real^2->bool`] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `R IN moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)` THEN
        REWRITE_TAC[moi_lgb1_l3; IN_ELIM_THM] THEN SIMP_TAC[];
        UNDISCH_TAC `(R UNION R') INTER moi_lgb1_kv L (g:real^2->real^N) kk = {}` THEN
        SET_TAC[];
        MATCH_MP_TAC FUN_IN_IMAGE THEN UNDISCH_TAC `RF SUBSET (R:real^2->bool)` THEN
        UNDISCH_TAC `(x:real^2) IN RF` THEN SET_TAC[]];
      UNDISCH_TAC `(h':real^3->real^N) z IN Q UNION kk` THEN ASM_REWRITE_TAC[IN_UNION] THEN
      MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^2->real^N) x IN relative_interior s` ASSUME_TAC THENL
   [USE_THEN "sF" (SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`h':real^3->real^N`; `l':real^3->real^N`; `y':real^N`; `Fh:real^3->bool`]
      MOI_LGB1_RELINT_AFFINE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_CON_SC_CONVEX THEN
      EXISTS_TAC `IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_LGB1_H_SC THEN
      MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `u:real^N->bool`;
                            `h':real^3->real^N`] THEN ASM_REWRITE_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(h':real^3->real^N) z = g (x:real^2)`)) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`RF:real^2->bool`; `RF':real^2->bool`; `s:real^N->bool`]
    (el 3 (CONJUNCTS (MATCH_MP MOI_LGB1_TGEN_CLAUSES
       (ASSUME `moi_lgb_tgeneric tt L (g:real^2->real^N) Q`))))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM IMAGE_UNION] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `DISJOINT (R:real^2->bool) R'` THEN
      UNDISCH_TAC `RF SUBSET (R:real^2->bool)` THEN
      UNDISCH_TAC `RF' SUBSET (R':real^2->bool)` THEN SET_TAC[];
      X_GEN_TAC `s':real^N->bool` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `s' INTER s:real^N->bool`; `s:real^N->bool`]
        SUBSET_OF_FACE_OF) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[SUBSET_REFL] THEN CONJ_TAC THENL
         [UNDISCH_TAC `simplicial_complex (tt:(real^N->bool)->bool)` THEN
          REWRITE_TAC[simplicial_complex] THEN
          DISCH_THEN(MP_TAC o SPECL [`s':real^N->bool`; `s:real^N->bool`] o last o CONJUNCTS) THEN
          ASM_SIMP_TAC[];
          REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
          EXISTS_TAC `(g:real^2->real^N) x` THEN ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `IMAGE (g:real^2->real^N) (RF UNION RF') SUBSET s'` THEN
          REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNION] THEN DISCH_THEN MATCH_MP_TAC THEN
          ASM_REWRITE_TAC[]];
        SET_TAC[]];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `(g:real^2->real^N) x` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x':real^2` THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  REWRITE_TAC[IMAGE_UNION] THEN MATCH_MP_TAC MOI_LGB1_SPAN_FROM_COUNT THEN
  EXISTS_TAC `(g:real^2->real^N) x` THEN
  ASM_REWRITE_TAC[GSYM IMAGE_UNION] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x':real^2` THEN ASM_REWRITE_TAC[]]);;

let MOI_LGB1_VERTS_GEN = prove
 (`!(K:(real^N->bool)->bool) r.
     simplicial_complex K /\ r IN K
     ==> r = convex hull {v | v extreme_point_of r} /\
         FINITE {v | v extreme_point_of r} /\
         ~affine_dependent {v | v extreme_point_of r} /\
         (!v. v extreme_point_of r ==> {v} IN K /\ v IN r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?n. n simplex (r:real^N->bool)` (X_CHOOSE_TAC `n:int`) THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simplex]) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `{v:real^N | v extreme_point_of r} = w` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN CONJ_TAC THENL
   [UNDISCH_TAC `simplicial_complex (K:(real^N->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[FACE_OF_SING];
    ASM_MESON_TAC[extreme_point_of]]);;

let MOI_LGB1_EXT_OF_VERTEX = prove
 (`!(K:(real^2->bool)->bool) R v.
     simplicial_complex K /\ R IN K /\ {v} IN K /\ v IN R ==> v extreme_point_of R`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM FACE_OF_SING] THEN
  SUBGOAL_THEN `{v:real^2} = {v} INTER R` SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `simplicial_complex (K:(real^2->bool)->bool)` THEN
  REWRITE_TAC[simplicial_complex] THEN
  DISCH_THEN(MP_TAC o SPECL [`{v:real^2}`; `R:real^2->bool`] o last o CONJUNCTS) THEN
  ASM_SIMP_TAC[]);;

let MOI_LGB1_INV_MOVED = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a R R' Fh z.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_gen tt h kk L g phi rk /\
     moi_lgb1_interp (moi_lgb1_l3 L g (moi_lgb1_th tt kk)) phi a /\
     (!R. R IN moi_lgb1_l3 L g (moi_lgb1_th tt kk)
          ==> !x y. x IN R /\ y IN R /\ a x = a y ==> x = y) /\
     R IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\ R' IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\
     DISJOINT R R' /\ ~((R UNION R') INTER moi_lgb1_kv L g kk = {}) /\
     Fh IN IMAGE (IMAGE h) (moi_lgb1_th tt kk) /\
     z IN relative_interior (IMAGE a R) /\ z IN relative_interior (IMAGE a R') /\
     z IN relative_interior Fh
     ==> affine hull ((IMAGE a R INTER Fh) UNION (IMAGE a R' INTER Fh)) = affine hull Fh`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "gen")
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "inj") STRIP_ASSUME_TAC)))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  ABBREV_TAC `L3 = moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)` THEN
  ABBREV_TAC `H = IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)` THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `g:real^2->real^N`;
                 `moi_lgb1_th (tt:(real^N->bool)->bool) kk`] MOI_LGB1_L3_SC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (H:(real^3->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "H" THEN MATCH_MP_TAC MOI_LGB1_H_SC THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `u:real^N->bool`; `h':real^3->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L3:(real^2->bool)->bool`; `R:real^2->bool`] MOI_LGB1_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "Rc") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Rv")))) THEN
  MP_TAC(ISPECL [`L3:(real^2->bool)->bool`; `R':real^2->bool`] MOI_LGB1_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "Rc'") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Rv'")))) THEN
  MP_TAC(ISPECL [`H:(real^3->bool)->bool`; `Fh:real^3->bool`] MOI_LGB1_VERTS_GEN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "Fc") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Fv")))) THEN
  SUBGOAL_THEN `!r. r IN L3 ==> ?l y. linear l /\ !x. x IN r ==> (a:real^2->real^3) x = l x + y`
  (LABEL_TAC "aff") THENL [ASM_MESON_TAC[moi_lgb1_interp]; ALL_TAC] THEN
  SUBGOAL_THEN `!v. {v} IN L3 ==> (a:real^2->real^3) v = phi v` (LABEL_TAC "av") THENL
   [ASM_MESON_TAC[moi_lgb1_interp]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. r IN L3
        ==> ~affine_dependent (IMAGE (phi:real^2->real^3) {v | v extreme_point_of r}) /\
            (!x y. x IN {v | v extreme_point_of r} /\ y IN {v | v extreme_point_of r} /\
                   phi x = phi y ==> x = y) /\
            convex hull (IMAGE phi {v | v extreme_point_of r}) = IMAGE a r /\
            {v | v extreme_point_of r} SUBSET {v | {v} IN L3}`
  (LABEL_TAC "wr") THENL
   [X_GEN_TAC `r:real^2->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`L3:(real^2->bool)->bool`; `r:real^2->bool`] MOI_LGB1_VERTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rc") (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rv")))) THEN
    SUBGOAL_THEN `IMAGE (phi:real^2->real^3) {v | v extreme_point_of r} =
                  IMAGE a {v | v extreme_point_of r}` SUBST1_TAC THENL
     [MATCH_MP_TAC(SET_RULE `(!x:real^2. x IN s ==> (f:real^2->real^3) x = g x)
                             ==> IMAGE f s = IMAGE g s`) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `v:real^2` THEN DISCH_TAC THEN
      CONV_TAC SYM_CONV THEN USE_THEN "av" MATCH_MP_TAC THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    USE_THEN "aff" (MP_TAC o C MATCH_MP (ASSUME `(r:real^2->bool) IN L3`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `l:real^2->real^3` (X_CHOOSE_THEN `y:real^3`
      STRIP_ASSUME_TAC)) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FGP_INJ_AFFINE_INDEPENDENT THEN
      MAP_EVERY EXISTS_TAC [`l:real^2->real^3`; `y:real^3`] THEN
      USE_THEN "rc" (fun th -> REWRITE_TAC[GSYM th]) THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "inj" (MATCH_ACCEPT_TAC o C MATCH_MP (ASSUME `(r:real^2->bool) IN L3`));
      REWRITE_TAC[IN_ELIM_THM] THEN MAP_EVERY X_GEN_TAC [`p:real^2`; `q:real^2`] THEN
      STRIP_TAC THEN
      USE_THEN "inj" (MP_TAC o C MATCH_MP (ASSUME `(r:real^2->bool) IN L3`)) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[];
      USE_THEN "rc" (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th]) THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_LGA_HULL_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`l:real^2->real^3`; `y:real^3`] THEN
      USE_THEN "rc" (fun th -> REWRITE_TAC[GSYM th]) THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  USE_THEN "wr" (MP_TAC o C MATCH_MP (ASSUME `(R:real^2->bool) IN L3`)) THEN
  USE_THEN "wr" (MP_TAC o C MATCH_MP (ASSUME `(R':real^2->bool) IN L3`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "cR'") ASSUME_TAC))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "cR") ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`{v:real^2 | {v} IN L3}`; `moi_lgb1_kv L (g:real^2->real^N) kk`;
                 `relative_frontier std_triangle`;
                 `\v. (h:real^N->real^3) ((g:real^2->real^N) v)`; `phi:real^2->real^3`;
                 `rk:real^2->num`; `{z:real^3 | {z} IN H}`;
                 `{v:real^2 | v extreme_point_of R}`; `{v:real^2 | v extreme_point_of R'}`;
                 `{v:real^3 | v extreme_point_of Fh}`; `z:real^3`] MOI_LGB1_INV) THEN
  USE_THEN "cR" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "cR'" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "Fc" (fun th -> REWRITE_TAC[GSYM th]) THEN
  USE_THEN "Fc" (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV) [th]) THEN
  REWRITE_TAC[AFFINE_HULL_CONVEX_HULL] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "gen" (STRIP_ASSUME_TAC o
    REWRITE_RULE[ASSUME `moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk) = L3`;
                 ASSUME `IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk) = H`] o
    REWRITE_RULE[moi_lgb1_gen]) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE_INJ THEN REWRITE_TAC[] THEN
    CONJ_TAC THENL [SET_TAC[]; ASM_MESON_TAC[simplicial_complex]];
    UNDISCH_TAC `DISJOINT (R:real^2->bool) R'` THEN
    MP_TAC(ISPEC `R:real^2->bool` extreme_point_of) THEN
    MP_TAC(ISPEC `R':real^2->bool` extreme_point_of) THEN SET_TAC[];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    UNDISCH_TAC `~((R UNION R') INTER moi_lgb1_kv L (g:real^2->real^N) kk = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_UNION; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^2` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `v:real^2` THEN ASM_REWRITE_TAC[] THENL
     [DISJ1_TAC; DISJ2_TAC] THEN
    MATCH_MP_TAC MOI_LGB1_EXT_OF_VERTEX THEN EXISTS_TAC `L3:(real^2->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "L3" THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                   `hs:real^3->bool`; `v:real^2`] MOI_LGB1_KV_FACTS) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    X_GEN_TAC `q:real^2` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                   `hs:real^3->bool`; `q:real^2`] MOI_LGB1_BD_ZERO) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXPAND_TAC "L3" THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                     `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                     `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                     `hs:real^3->bool`; `q:real^2`] MOI_LGB1_KV_FACTS) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      STRIP_TAC] THEN
    MATCH_MP_TAC HULL_MINIMAL THEN
    MP_TAC(ISPECL [`{q:real^2}`; `q:real^2`] MOI_LGB1_SPACE_AFFINE) THEN
    REWRITE_TAC[moi_lgb1_space; IN_SING] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `Fh:real^3->bool` THEN CONJ_TAC THENL
     [USE_THEN "Fc" (fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THEN REWRITE_TAC[HULL_SUBSET];
      MATCH_MP_TAC MOI_LGB1_HS_RELINT THEN EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MOI_CON_SC_CONVEX THEN EXISTS_TAC `H:(real^3->bool)->bool` THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `(Fh:real^3->bool) IN H` THEN EXPAND_TAC "H" THEN
        REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `s0:real^N->bool` STRIP_ASSUME_TAC) THEN
        MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                       `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                       `s0:real^N->bool`] MOI_LGB1_TH_FACTS) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        UNDISCH_TAC `IMAGE (h:real^N->real^3) u SUBSET hs` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(s0:real^N->bool) SUBSET u` THEN SET_TAC[]]]]);;

let MOI_LGB1_INV_FULL = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a R R' Fh z.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_gen tt h kk L g phi rk /\
     moi_lgb1_interp (moi_lgb1_l3 L g (moi_lgb1_th tt kk)) phi a /\
     (!R. R IN moi_lgb1_l3 L g (moi_lgb1_th tt kk)
          ==> !x y. x IN R /\ y IN R /\ a x = a y ==> x = y) /\
     R IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\ R' IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\
     DISJOINT R R' /\ Fh IN IMAGE (IMAGE h) (moi_lgb1_th tt kk) /\
     z IN relative_interior (IMAGE a R) /\ z IN relative_interior (IMAGE a R') /\
     z IN relative_interior Fh /\ h' z IN Q UNION kk
     ==> affine hull ((IMAGE a R INTER Fh) UNION (IMAGE a R' INTER Fh)) = affine hull Fh`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `(R UNION R') INTER moi_lgb1_kv L (g:real^2->real^N) kk = {}` THENL
   [MATCH_MP_TAC MOI_LGB1_INV_UNMOVED THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
      `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
      `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`; `hs:real^3->bool`;
      `phi:real^2->real^3`; `rk:real^2->num`; `z:real^3`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MOI_LGB1_RELINT_IN];
    MATCH_MP_TAC MOI_LGB1_INV_MOVED THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
      `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
      `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`; `hs:real^3->bool`;
      `phi:real^2->real^3`; `rk:real^2->num`; `z:real^3`] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* C13. The moved configuration (moi_lgb1_mvd: moves, interpolation,       *)
(* injectivity on L3 simplices, vertex values in hs with the z3 zero        *)
(* pattern of the boundary) and its single-simplex facts: the z3 = 0 points *)
(* of a moved simplex are exactly its frontier points; no simplex of L3 has *)
(* only boundary vertices unless it lies in the frontier; a moved simplex   *)
(* is not inside the hull of a chart simplex of dimension <= 2 except a     *)
(* boundary edge in z3 = 0; at relative interior points it avoids chart     *)
(* vertices and meets chart edge lines in single points.                    *)
(* ------------------------------------------------------------------------- *)

let moi_lgb1_mvd = new_definition
 `moi_lgb1_mvd (tt:(real^N->bool)->bool) (h:real^N->real^3) kk L (g:real^2->real^N) hs
               phi rk a <=>
    moi_lgb1_gen tt h kk L g phi rk /\
    moi_lgb1_interp (moi_lgb1_l3 L g (moi_lgb1_th tt kk)) phi a /\
    (!R. R IN moi_lgb1_l3 L g (moi_lgb1_th tt kk)
         ==> !x y. x IN R /\ y IN R /\ a x = a y ==> x = y) /\
    (!v. {v} IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) ==> phi v IN hs) /\
    (!v. {v} IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\ hs = {z:real^3 | &0 <= z$3}
         ==> ((phi v)$3 = &0 <=> v IN relative_frontier std_triangle))`;;

let MOI_LGB1_AFF_DIM_AFFINE_LE = prove
 (`!(f:real^M->real^N) l y s.
     linear l /\ (!x. x IN s ==> f x = l x + y) ==> aff_dim (IMAGE f s) <= aff_dim s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (f:real^M->real^N) s = IMAGE (\x. y + x) (IMAGE l s)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN REWRITE_TAC[EXTENSION; IN_IMAGE] THEN
    ASM_MESON_TAC[VECTOR_ADD_SYM];
    REWRITE_TAC[AFF_DIM_TRANSLATION_EQ] THEN ASM_SIMP_TAC[AFF_DIM_LINEAR_IMAGE_LE]]);;

let MOI_LGB1_AFFINE_VSUM = prove
 (`!(f:real^M->real^N) l y W lam.
     linear l /\ (!x. x IN convex hull W ==> f x = l x + y) /\ FINITE W /\
     (!w. w IN W ==> &0 <= lam w) /\ sum W lam = &1
     ==> f (vsum W (\w. lam w % w)) = vsum W (\w. lam w % f w)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `vsum W (\w. lam w % w) IN convex hull (W:real^M->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[CONVEX_HULL_FINITE; IN_ELIM_THM] THEN EXISTS_TAC `lam:real^M->real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `!w. w IN W ==> (f:real^M->real^N) w = l w + y` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[HULL_INC];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS `vsum W (\w. lam w % ((l:real^M->real^N) w + y))` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[LINEAR_VSUM; o_DEF; VECTOR_ADD_LDISTRIB; VSUM_ADD; VSUM_RMUL;
                 LINEAR_CMUL] THEN
    REWRITE_TAC[VECTOR_MUL_LID];
    MATCH_MP_TAC VSUM_EQ THEN ASM_SIMP_TAC[]]);;

let MOI_LGB1_ZERO_COMB = prove
 (`!(W:real^2->bool) (lam:real^2->real) (p:real^2->real^3) (q:real^2->real^3).
     FINITE W /\ (!w. w IN W ==> &0 <= lam w) /\
     (!w. w IN W ==> &0 <= (p w)$3 /\ &0 <= (q w)$3 /\ ((p w)$3 = &0 <=> (q w)$3 = &0))
     ==> ((vsum W (\w. lam w % p w))$3 = &0 <=> (vsum W (\w. lam w % q w))$3 = &0)`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[VSUM_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  SUBGOAL_THEN
   `!r:real^2->real^3. (!w. w IN W ==> &0 <= (r w)$3)
       ==> (sum W (\w. lam w * (r w)$3) = &0 <=> !w. w IN W ==> lam w * (r w)$3 = &0)`
  (LABEL_TAC "sz") THENL
   [REPEAT STRIP_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN MATCH_MP_TAC SUM_POS_EQ_0 THEN ASM_SIMP_TAC[REAL_LE_MUL];
      DISCH_TAC THEN MATCH_MP_TAC SUM_EQ_0 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "sz" (MP_TAC o SPEC `p:real^2->real^3`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  USE_THEN "sz" (MP_TAC o SPEC `q:real^2->real^3`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[REAL_ENTIRE] THEN ASM_MESON_TAC[]);;

let MOI_LGB1_BD_CHAR = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs x.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ x IN std_triangle /\ g x IN u
     ==> (x IN relative_frontier std_triangle <=>
          hs = {z:real^3 | &0 <= z$3} /\ ((h:real^N->real^3) (g x))$3 = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  TRANS_TAC EQ_TRANS `(g:real^2->real^N) x IN complex_boundary c` THEN CONJ_TAC THENL
   [UNDISCH_TAC `moi_lgb1_fix (c:(real^N->bool)->bool) tt u h h' kk L g Q hs` THEN
    REWRITE_TAC[moi_lgb1_fix; moi_lt_singular_disk] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT1 o CONJUNCT2) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
    UNDISCH_TAC `moi_lgb1_fix (c:(real^N->bool)->bool) tt u h h' kk L g Q hs` THEN
    REWRITE_TAC[moi_lgb1_fix] THEN
    DISCH_THEN(MP_TAC o SPEC `(g:real^2->real^N) x` o last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[]]);;

let MOI_LGB1_ZERO_PATTERN = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a R x.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     R IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\ x IN R /\ hs = {z:real^3 | &0 <= z$3}
     ==> ((a x)$3 = &0 <=> x IN relative_frontier std_triangle)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_lgb1_mvd]) THEN
  ABBREV_TAC `L3 = moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)` THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `g:real^2->real^N`;
                 `moi_lgb1_th (tt:(real^N->bool)->bool) kk`] MOI_LGB1_L3_SC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `R:real^2->bool`]
    MOI_LGB1_L3_A0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `l0:real^2->real^3` (X_CHOOSE_THEN `y0:real^3`
      STRIP_ASSUME_TAC)) ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`L3:(real^2->bool)->bool`; `R:real^2->bool`] MOI_LGB1_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "Rc") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Rv")))) THEN
  SUBGOAL_THEN `?l y. linear l /\ !x. x IN R ==> (a:real^2->real^3) x = l x + y`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[moi_lgb1_interp]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^2) IN convex hull {v | v extreme_point_of R}` MP_TAC THENL
   [USE_THEN "Rc" (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[CONVEX_HULL_FINITE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real^2->real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:real^2) IN std_triangle /\ (g:real^2->real^N) x IN u` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `x:real^2`] MOI_LGB1_BD_CHAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(a:real^2->real^3) x = vsum {v | v extreme_point_of R} (\w. lam w % phi w) /\
                (h:real^N->real^3) ((g:real^2->real^N) x) =
                vsum {v | v extreme_point_of R} (\w. lam w % h (g w))`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      can (term_match [] `vsum {v:real^2 | v extreme_point_of R} (\x. lam x % x) = x`)
      (concl th))) ORELSE ALL_TAC THEN
    CONJ_TAC THENL
     [TRANS_TAC EQ_TRANS `vsum {v | v extreme_point_of R} (\w. lam w % (a:real^2->real^3) w)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MOI_LGB1_AFFINE_VSUM THEN
        MAP_EVERY EXISTS_TAC [`l:real^2->real^3`; `y:real^3`] THEN
        USE_THEN "Rc" (fun th -> REWRITE_TAC[GSYM th]) THEN ASM_REWRITE_TAC[IN_ELIM_THM];
        MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
        X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
        UNDISCH_TAC `moi_lgb1_interp L3 (phi:real^2->real^3) a` THEN
        REWRITE_TAC[moi_lgb1_interp] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
        ASM_MESON_TAC[]];
      MATCH_MP_TAC MOI_LGB1_AFFINE_VSUM THEN
      MAP_EVERY EXISTS_TAC [`l0:real^2->real^3`; `y0:real^3`] THEN
      USE_THEN "Rc" (fun th -> REWRITE_TAC[GSYM th]) THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_LGB1_ZERO_COMB THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `w:real^2` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  USE_THEN "Rv" (MP_TAC o C MATCH_MP (ASSUME `(w:real^2) extreme_point_of R`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(w:real^2) IN std_triangle /\ (g:real^2->real^N) w IN u` STRIP_ASSUME_TAC
  THENL [CONJ_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `w:real^2`] MOI_LGB1_BD_CHAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(phi:real^2->real^3) w IN hs /\ (h:real^N->real^3) (g w) IN hs`
  MP_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[]; ASM SET_TAC[]]; ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let MOI_LGB1_WR = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a R.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     R IN moi_lgb1_l3 L g (moi_lgb1_th tt kk)
     ==> ~affine_dependent (IMAGE (phi:real^2->real^3) {v | v extreme_point_of R}) /\
         (!x y. x IN {v | v extreme_point_of R} /\ y IN {v | v extreme_point_of R} /\
                phi x = phi y ==> x = y) /\
         convex hull (IMAGE phi {v | v extreme_point_of R}) = IMAGE a R /\
         {v | v extreme_point_of R} SUBSET {v | {v} IN moi_lgb1_l3 L g (moi_lgb1_th tt kk)} /\
         (!v. v extreme_point_of R ==> a v = phi v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_lgb1_mvd]) THEN
  SUBGOAL_THEN `!x y. x IN R /\ y IN R /\ (a:real^2->real^3) x = a y ==> x = y`
  (LABEL_TAC "ainj") THENL
   [FIRST_ASSUM(fun th -> ACCEPT_TAC(MATCH_MP th
      (ASSUME `R IN moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)`)));
    ALL_TAC] THEN
  ABBREV_TAC `L3 = moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)` THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `g:real^2->real^N`;
                 `moi_lgb1_th (tt:(real^N->bool)->bool) kk`] MOI_LGB1_L3_SC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`L3:(real^2->bool)->bool`; `R:real^2->bool`] MOI_LGB1_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rc") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rv")))) THEN
  SUBGOAL_THEN `!v. v extreme_point_of R ==> (a:real^2->real^3) v = phi v` (LABEL_TAC "av")
  THENL
   [X_GEN_TAC `v:real^2` THEN DISCH_TAC THEN
    UNDISCH_TAC `moi_lgb1_interp L3 (phi:real^2->real^3) a` THEN
    REWRITE_TAC[moi_lgb1_interp] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    ASM_MESON_TAC[];
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `IMAGE (phi:real^2->real^3) {v | v extreme_point_of R} =
                IMAGE a {v | v extreme_point_of R}` SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE `(!x:real^2. x IN s ==> (f:real^2->real^3) x = g x)
                           ==> IMAGE f s = IMAGE g s`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `v:real^2` THEN DISCH_TAC THEN
    CONV_TAC SYM_CONV THEN USE_THEN "av" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?l y. linear l /\ !x. x IN R ==> (a:real^2->real^3) x = l x + y`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[moi_lgb1_interp]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FGP_INJ_AFFINE_INDEPENDENT THEN
    MAP_EVERY EXISTS_TAC [`l:real^2->real^3`; `y:real^3`] THEN
    USE_THEN "rc" (fun th -> REWRITE_TAC[GSYM th]) THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "ainj" ACCEPT_TAC;
    REWRITE_TAC[IN_ELIM_THM] THEN MAP_EVERY X_GEN_TAC [`p:real^2`; `q:real^2`] THEN
    STRIP_TAC THEN USE_THEN "ainj" MATCH_MP_TAC THEN ASM_MESON_TAC[];
    USE_THEN "rc" (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th]) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_LGA_HULL_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`l:real^2->real^3`; `y:real^3`] THEN
    USE_THEN "rc" (fun th -> REWRITE_TAC[GSYM th]) THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]]);;

let MOI_LGB1_NOFLAT = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs R.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ R IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\
     aff_dim R = &2 /\ (!w. w extreme_point_of R ==> w IN relative_frontier std_triangle)
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  ABBREV_TAC `L3 = moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)` THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `g:real^2->real^N`;
                 `moi_lgb1_th (tt:(real^N->bool)->bool) kk`] MOI_LGB1_L3_SC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(R:real^2->bool) SUBSET std_triangle /\ convex R` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC MOI_CON_SC_CONVEX THEN
                    EXISTS_TAC `L3:(real^2->bool)->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `R:real^2->bool` MOI_LGB1_TRI_NOT_FRONTIER) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(R:real^2->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `aff_dim (R:real^2->bool) = &2` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L3:(real^2->bool)->bool`; `R:real^2->bool`; `R:real^2->bool`]
    MOI_LGB1_FACE_VERTEX) THEN
  ASM_SIMP_TAC[FACE_OF_REFL] THEN DISCH_THEN(X_CHOOSE_THEN `w0:real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `w0:real^2`] MOI_LGB1_BD_ZERO) THEN
  ASM_SIMP_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`L3:(real^2->bool)->bool`; `\v. (h:real^N->real^3) ((g:real^2->real^N) v)`;
                 `\x. (h:real^N->real^3) ((g:real^2->real^N) x)`; `R:real^2->bool`]
    MOI_LGB1_INTERP_IMAGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "L3" THEN MATCH_MP_TAC MOI_LGB1_A0_INTERP THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `IMAGE (\x. (h:real^N->real^3) ((g:real^2->real^N) x)) R SUBSET {z:real^3 | z$3 = &0}`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_MINIMAL THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `w:real^2` THEN
      DISCH_TAC THEN
      MP_TAC(ISPECL [`L3:(real^2->bool)->bool`; `R:real^2->bool`] MOI_LGB1_VERTS) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                     `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                     `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                     `hs:real^3->bool`; `w:real^2`] MOI_LGB1_BD_ZERO) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; SIMP_TAC[]];
      MATCH_MP_TAC AFFINE_IMP_CONVEX THEN
      MP_TAC(ISPECL [`{w0:real^2}`; `w0:real^2`] MOI_LGB1_SPACE_AFFINE) THEN
      REWRITE_TAC[moi_lgb1_space; IN_SING]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `x:real^2`] MOI_LGB1_BD_CHAR) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `R:real^2->bool`]
      MOI_LGB1_L3_A0) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM SET_TAC[]];
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (\x. (h:real^N->real^3) ((g:real^2->real^N) x)) R SUBSET
                 {z:real^3 | z$3 = &0}` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[]]);;

let MOI_LGB1_SMALLSPAN = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a R p.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     R IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\ p extreme_point_of R /\
     p IN moi_lgb1_kv L g kk /\
     moi_lgb1_space (relative_frontier std_triangle) p SUBSET affine hull (IMAGE a R)
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  SUBGOAL_THEN `?l y. linear l /\ !x. x IN R ==> (a:real^2->real^3) x = l x + y`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[moi_lgb1_mvd; moi_lgb1_interp]; ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (IMAGE (a:real^2->real^3) R) <= aff_dim R /\ aff_dim R <= &2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MOI_LGB1_AFF_DIM_AFFINE_LE THEN
      MAP_EVERY EXISTS_TAC [`l:real^2->real^3`; `y:real^3`] THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPEC `R:real^2->bool` AFF_DIM_LE_UNIV) THEN REWRITE_TAC[DIMINDEX_2]];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_lgb1_space (relative_frontier std_triangle) p SUBSET
               affine hull (IMAGE (a:real^2->real^3) R)` THEN
  REWRITE_TAC[moi_lgb1_space] THEN COND_CASES_TAC THENL
   [DISCH_TAC;
    REWRITE_TAC[UNIV_SUBSET] THEN DISCH_TAC THEN
    MP_TAC(ISPEC `IMAGE (a:real^2->real^3) R` AFF_DIM_EQ_FULL) THEN
    ASM_REWRITE_TAC[DIMINDEX_3] THEN DISCH_TAC THEN ASM_INT_ARITH_TAC] THEN
  SUBGOAL_THEN `{p:real^2} IN moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                   `hs:real^3->bool`; `p:real^2`] MOI_LGB1_KV_FACTS) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `p:real^2`] MOI_LGB1_BD_ZERO) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `affine hull (IMAGE (a:real^2->real^3) R) = {z:real^3 | z$3 = &0}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    MP_TAC(ISPECL [`{z:real^3 | z$3 = &0}`; `affine hull (IMAGE (a:real^2->real^3) R)`]
      AFF_DIM_EQ_AFFINE_HULL) THEN
    ASM_REWRITE_TAC[MOI_LGB1_AFF_DIM_Z3; AFF_DIM_AFFINE_HULL; HULL_HULL] THEN
    ANTS_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `affine hull {z:real^3 | z$3 = &0} = {z | z$3 = &0}` SUBST1_TAC THENL
     [MATCH_MP_TAC HULL_P THEN
      MP_TAC(ISPECL [`{p:real^2}`; `p:real^2`] MOI_LGB1_SPACE_AFFINE) THEN
      REWRITE_TAC[moi_lgb1_space; IN_SING];
      SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_LGB1_NOFLAT THEN
  MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
    `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
    `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`; `hs:real^3->bool`;
    `R:real^2->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(INT_ARITH `(a:int) <= &2 /\ &2 <= a ==> a = &2`) THEN ASM_REWRITE_TAC[] THEN
    TRANS_TAC INT_LE_TRANS `aff_dim (IMAGE (a:real^2->real^3) R)` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN ASM_REWRITE_TAC[MOI_LGB1_AFF_DIM_Z3] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(w:real^2) IN R` ASSUME_TAC THENL
   [ASM_MESON_TAC[extreme_point_of]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `R:real^2->bool`; `w:real^2`] MOI_LGB1_ZERO_PATTERN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `(a:real^2->real^3) w IN affine hull (IMAGE a R)` MP_TAC THENL
   [MATCH_MP_TAC HULL_INC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[IN_ELIM_THM]]);;

let MOI_LGB1_LAST_VERTEX = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs rk R.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ R IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\
     ~(R INTER moi_lgb1_kv L g kk = {})
     ==> ?p. p extreme_point_of R /\ p IN moi_lgb1_kv L g kk /\
             !q. q IN {v | v extreme_point_of R} /\ q IN moi_lgb1_kv L g kk
                 ==> (rk:real^2->num) q <= rk p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `g:real^2->real^N`;
                 `moi_lgb1_th (tt:(real^N->bool)->bool) kk`] MOI_LGB1_L3_SC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`{v:real^2 | v extreme_point_of R} INTER moi_lgb1_kv L (g:real^2->real^N) kk`;
                 `rk:real^2->num`] MOI_LGB1_LAST) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_INTER THEN DISJ1_TAC THEN
      MP_TAC(ISPECL [`moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)`;
                     `R:real^2->bool`] MOI_LGB1_VERTS) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      UNDISCH_TAC `~(R INTER moi_lgb1_kv L (g:real^2->real^N) kk = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `v:real^2` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `v:real^2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_LGB1_EXT_OF_VERTEX THEN
      EXISTS_TAC `moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)` THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                     `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                     `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                     `hs:real^3->bool`; `v:real^2`] MOI_LGB1_KV_FACTS) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    REWRITE_TAC[IN_INTER; IN_ELIM_THM; CONJ_ASSOC]]);;

let MOI_LGB1_SINGLE_L3 = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a R YF z.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     R IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\ ~(R INTER moi_lgb1_kv L g kk = {}) /\
     YF SUBSET {z | {z} IN IMAGE (IMAGE h) (moi_lgb1_th tt kk)} /\
     z IN relative_interior (IMAGE a R) /\ z IN convex hull YF /\
     YF SUBSET affine hull (IMAGE a R)
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `rk:real^2->num`; `R:real^2->bool`]
    MOI_LGB1_LAST_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `p:real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `R:real^2->bool`] MOI_LGB1_WR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "cR") (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `R:real^2->bool`; `p:real^2`] MOI_LGB1_SMALLSPAN) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `affine hull (IMAGE (a:real^2->real^3) R) =
                affine hull (IMAGE phi {v | v extreme_point_of R} UNION YF)` SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [USE_THEN "cR" (SUBST1_TAC o SYM) THEN REWRITE_TAC[AFFINE_HULL_CONVEX_HULL] THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[AFFINE_AFFINE_HULL; UNION_SUBSET] THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "cR" (SUBST1_TAC o SYM) THEN
      REWRITE_TAC[AFFINE_HULL_CONVEX_HULL; HULL_SUBSET]];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_lgb1_mvd tt (h:real^N->real^3) kk L (g:real^2->real^N) hs phi rk a` THEN
  REWRITE_TAC[moi_lgb1_mvd; moi_lgb1_gen] THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_LGB1_SINGLE THEN
  MAP_EVERY EXISTS_TAC
   [`{v:real^2 | {v} IN moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)}`;
    `moi_lgb1_kv L (g:real^2->real^N) kk`;
    `\v. (h:real^N->real^3) ((g:real^2->real^N) v)`; `rk:real^2->num`;
    `{z:real^3 | {z} IN IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)}`;
    `z:real^3`] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

let MOI_LGB1_NO_HVERTEX = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a R z.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     R IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\ ~(R INTER moi_lgb1_kv L g kk = {}) /\
     z IN relative_interior (IMAGE a R) /\ {z} IN IMAGE (IMAGE h) (moi_lgb1_th tt kk)
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MOI_LGB1_SINGLE_L3 THEN
  MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
    `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
    `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`; `hs:real^3->bool`;
    `phi:real^2->real^3`; `rk:real^2->num`; `a:real^2->real^3`; `R:real^2->bool`;
    `{z:real^3}`; `z:real^3`] THEN
  ASM_REWRITE_TAC[SING_SUBSET; IN_ELIM_THM; CONVEX_HULL_SING; IN_SING] THEN
  MATCH_MP_TAC HULL_INC THEN ASM_MESON_TAC[MOI_LGB1_RELINT_IN]);;

let MOI_LGB1_HEDGE = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a R E z.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     R IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\ ~(R INTER moi_lgb1_kv L g kk = {}) /\
     E IN IMAGE (IMAGE h) (moi_lgb1_th tt kk) /\
     z IN relative_interior (IMAGE a R) /\ z IN E
     ==> ~(affine hull E SUBSET affine hull (IMAGE a R))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `simplicial_complex (IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LGB1_H_SC THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `u:real^N->bool`; `h':real^3->real^N`] THEN
    ASM_MESON_TAC[moi_lgb1_fix];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)`; `E:real^3->bool`]
    MOI_LGB1_VERTS_GEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_LGB1_SINGLE_L3 THEN
  MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
    `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
    `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`; `hs:real^3->bool`;
    `phi:real^2->real^3`; `rk:real^2->num`; `a:real^2->real^3`; `R:real^2->bool`;
    `{v:real^3 | v extreme_point_of E}`; `z:real^3`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `affine hull (E:real^3->bool)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    ASM_MESON_TAC[HULL_INC]]);;

let MOI_LGB1_IN_WALL = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a R Wl.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     R IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\ ~(R INTER moi_lgb1_kv L g kk = {}) /\
     Wl IN IMAGE (IMAGE h) (moi_lgb1_th tt kk) /\ aff_dim Wl <= &2 /\
     IMAGE a R SUBSET affine hull Wl
     ==> R SUBSET relative_frontier std_triangle /\ aff_dim R <= &1 /\
         affine hull Wl = {z:real^3 | z$3 = &0}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  SUBGOAL_THEN
   `!v. {v} IN moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk) /\
        hs = {z:real^3 | &0 <= z$3}
        ==> (((phi:real^2->real^3) v)$3 = &0 <=> v IN relative_frontier std_triangle)`
  (LABEL_TAC "zp") THENL
   [UNDISCH_TAC `moi_lgb1_mvd tt (h:real^N->real^3) kk L (g:real^2->real^N) hs phi rk a` THEN
    SIMP_TAC[moi_lgb1_mvd];
    ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_complex (IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LGB1_H_SC THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `u:real^N->bool`; `h':real^3->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `g:real^2->real^N`;
                 `moi_lgb1_th (tt:(real^N->bool)->bool) kk`] MOI_LGB1_L3_SC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)`; `Wl:real^3->bool`]
    MOI_LGB1_VERTS_GEN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "Wc") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Wv")))) THEN
  MP_TAC(ISPECL [`moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)`; `R:real^2->bool`]
    MOI_LGB1_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "Rc") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Rv")))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `R:real^2->bool`] MOI_LGB1_WR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "cR") (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "av"))))) THEN
  SUBGOAL_THEN `?q:real^2. q extreme_point_of R /\ q IN moi_lgb1_kv L (g:real^2->real^N) kk`
  (X_CHOOSE_THEN `q0:real^2` STRIP_ASSUME_TAC) THENL
   [UNDISCH_TAC `~(R INTER moi_lgb1_kv L (g:real^2->real^N) kk = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^2` STRIP_ASSUME_TAC) THEN EXISTS_TAC `v:real^2` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_LGB1_EXT_OF_VERTEX THEN
    EXISTS_TAC `moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                   `hs:real^3->bool`; `v:real^2`] MOI_LGB1_KV_FACTS) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`{v:real^2 | {v} IN moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)}`;
    `moi_lgb1_kv L (g:real^2->real^N) kk`; `relative_frontier std_triangle`;
    `\v. (h:real^N->real^3) ((g:real^2->real^N) v)`; `phi:real^2->real^3`; `rk:real^2->num`;
    `{z:real^3 | {z} IN IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)}`;
    `{v:real^2 | v extreme_point_of R}`; `{v:real^3 | v extreme_point_of Wl}`]
    MOI_LGB1_INSIDE) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `moi_lgb1_mvd tt (h:real^N->real^3) kk L (g:real^2->real^N) hs phi rk a` THEN
    REWRITE_TAC[moi_lgb1_mvd; moi_lgb1_gen] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE_INJ THEN REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [SET_TAC[];
        UNDISCH_TAC `simplicial_complex (moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk))` THEN
        SIMP_TAC[simplicial_complex]];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
      USE_THEN "Wv" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(v:real^3) extreme_point_of Wl`)]);
      ONCE_REWRITE_TAC[GSYM AFF_DIM_CONVEX_HULL] THEN
      USE_THEN "Wc" (fun th -> REWRITE_TAC[GSYM th]) THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
      EXISTS_TAC `q0:real^2` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (a:real^2->real^3) R` THEN
      CONJ_TAC THENL
       [USE_THEN "cR" (SUBST1_TAC o SYM) THEN REWRITE_TAC[HULL_SUBSET];
        MP_TAC(ASSUME `IMAGE (a:real^2->real^3) R SUBSET affine hull Wl`) THEN
        USE_THEN "Wc" (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [th]) THEN
        REWRITE_TAC[AFFINE_HULL_CONVEX_HULL]];
      X_GEN_TAC `w:real^2` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
      REWRITE_TAC[IN_INTER] THEN DISCH_THEN(X_CHOOSE_THEN `q:real^2` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                     `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                     `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                     `hs:real^3->bool`; `q:real^2`] MOI_LGB1_BD_ZERO) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                       `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                       `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                       `hs:real^3->bool`; `q:real^2`] MOI_LGB1_KV_FACTS) THEN
        ASM_REWRITE_TAC[] THEN SIMP_TAC[];
        STRIP_TAC] THEN
      SUBGOAL_THEN `{w:real^2} IN moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)`
      ASSUME_TAC THENL
       [USE_THEN "Rv" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(w:real^2) extreme_point_of R`)]);
        ALL_TAC] THEN
      USE_THEN "zp" (MP_TAC o C MATCH_MP
        (CONJ (ASSUME `{w:real^2} IN moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)`)
              (ASSUME `hs = {z:real^3 | &0 <= z$3}`))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "aY")) THEN
  SUBGOAL_THEN `affine hull (Wl:real^3->bool) = {z:real^3 | z$3 = &0}` ASSUME_TAC THENL
   [USE_THEN "Wc" (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    ASM_REWRITE_TAC[AFFINE_HULL_CONVEX_HULL];
    ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `q0:real^2`] MOI_LGB1_BD_ZERO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                     `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                     `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                     `hs:real^3->bool`; `q0:real^2`] MOI_LGB1_KV_FACTS) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      UNDISCH_TAC `{v:real^2 | v extreme_point_of R} SUBSET relative_frontier std_triangle` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    STRIP_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                   `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                   `a:real^2->real^3`; `R:real^2->bool`; `x:real^2`] MOI_LGB1_ZERO_PATTERN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `IMAGE (a:real^2->real^3) R SUBSET affine hull Wl` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(INT_ARITH `(a:int) <= &2 /\ ~(a = &2) ==> a <= &1`) THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `R:real^2->bool` AFF_DIM_LE_UNIV) THEN REWRITE_TAC[DIMINDEX_2];
      DISCH_TAC THEN MATCH_MP_TAC MOI_LGB1_NOFLAT THEN
      MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
        `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
        `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`; `hs:real^3->bool`;
        `R:real^2->bool`] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `{v:real^2 | v extreme_point_of R} SUBSET relative_frontier std_triangle` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* C14. The cut complex of the chart step.  moi_lgb1_sml: the smallness of  *)
(* the moved map at scale d0 (chart, closeness to g, margin).  The moved   *)
(* simplices and their cells satisfy moi_lgb1_cutsetup, and the 2-cells    *)
(* get generic cone points (MOI_LGB1_CONE_POINTS).                          *)
(* ------------------------------------------------------------------------- *)

let moi_lgb1_sml = new_definition
 `moi_lgb1_sml (tt:(real^N->bool)->bool) (u:real^N->bool) (h:real^N->real^3) h' kk L
               (g:real^2->real^N) a d0 <=>
    (!R x. R IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\ x IN R
           ==> a x IN IMAGE h u /\ dist(h' (a x),g x) < d0) /\
    (!R x y s. R IN moi_lgb1_lm L (moi_lgb1_kv L g kk) /\ x IN R /\ dist(y,g x) < d0 /\
               s IN tt /\ y IN s ==> s IN moi_lgb1_t3 tt kk)`;;

let MOI_LGB1_AFF_DIM_INJ = prove
 (`!(f:real^M->real^N) l y s.
     linear l /\ convex s /\ (!x. x IN s ==> f x = l x + y) /\
     (!x x'. x IN s /\ x' IN s /\ f x = f x' ==> x = x')
     ==> aff_dim (IMAGE f s) = aff_dim s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INT_LE_ANTISYM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_LGB1_AFF_DIM_AFFINE_LE THEN
    MAP_EVERY EXISTS_TAC [`l:real^M->real^N`; `y:real^N`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `s:real^M->bool` AFFINE_BASIS_EXISTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^M->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `convex hull b SUBSET (s:real^M->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (b:real^M->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  TRANS_TAC INT_LE_TRANS `aff_dim (IMAGE (f:real^M->real^N) b)` THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
    REWRITE_TAC[GSYM(ASSUME `affine hull b = affine hull (s:real^M->bool)`)] THEN
    SUBGOAL_THEN `~affine_dependent (IMAGE (f:real^M->real^N) b)` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FGP_INJ_AFFINE_INDEPENDENT THEN
      MAP_EVERY EXISTS_TAC [`l:real^M->real^N`; `y:real^N`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[AFF_DIM_AFFINE_HULL] THEN
    ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT] THEN
    MATCH_MP_TAC(INT_ARITH `a:int = b ==> a - &1 <= b - &1`) THEN
    REWRITE_TAC[INT_OF_NUM_EQ] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    MATCH_MP_TAC AFF_DIM_SUBSET THEN ASM SET_TAC[]]);;

let MOI_LGB1_UNMOVED_A0 = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a r.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     r IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\ r INTER moi_lgb1_kv L g kk = {}
     ==> !x. x IN r ==> a x = h (g x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `g:real^2->real^N`;
                 `moi_lgb1_th (tt:(real^N->bool)->bool) kk`] MOI_LGB1_L3_SC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)`; `phi:real^2->real^3`;
                 `\v. (h:real^N->real^3) ((g:real^2->real^N) v)`; `a:real^2->real^3`;
                 `\x. (h:real^N->real^3) ((g:real^2->real^N) x)`; `r:real^2->bool`]
    MOI_LGB1_INTERP_AGREE) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `moi_lgb1_mvd tt (h:real^N->real^3) kk L (g:real^2->real^N) hs phi rk a` THEN
    REWRITE_TAC[moi_lgb1_mvd] THEN STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC MOI_LGB1_A0_INTERP THEN ASM_MESON_TAC[];
    X_GEN_TAC `v:real^2` THEN DISCH_TAC THEN
    UNDISCH_TAC `moi_lgb1_mvd tt (h:real^N->real^3) kk L (g:real^2->real^N) hs phi rk a` THEN
    REWRITE_TAC[moi_lgb1_mvd; moi_lgb1_gen] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT1) THEN
    UNDISCH_TAC `r INTER moi_lgb1_kv L (g:real^2->real^N) kk = {}` THEN
    MP_TAC(ISPECL [`r:real^2->bool`; `v:real^2`] extreme_point_of) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

let MOI_LGB1_CUTSETUP = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a d0.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     moi_lgb1_sml tt u h h' kk L g a d0
     ==> moi_lgb1_cutsetup L (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                           (IMAGE (IMAGE h) (moi_lgb1_th tt kk))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  SUBGOAL_THEN `!R. R IN moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)
                    ==> !x y. x IN R /\ y IN R /\ (a:real^2->real^3) x = a y ==> x = y`
  (LABEL_TAC "inj") THENL
   [UNDISCH_TAC `moi_lgb1_mvd tt (h:real^N->real^3) kk L (g:real^2->real^N) hs phi rk a` THEN
    REWRITE_TAC[moi_lgb1_mvd] THEN STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_lgb1_interp (moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)) phi a`
  (LABEL_TAC "itp") THENL
   [UNDISCH_TAC `moi_lgb1_mvd tt (h:real^N->real^3) kk L (g:real^2->real^N) hs phi rk a` THEN
    REWRITE_TAC[moi_lgb1_mvd] THEN STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!R x. R IN moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk) /\ x IN R
                      ==> (a:real^2->real^3) x IN IMAGE (h:real^N->real^3) u /\
                          dist((h':real^3->real^N) (a x),g x) < d0`
  (LABEL_TAC "cl") THENL
   [UNDISCH_TAC `moi_lgb1_sml tt u (h:real^N->real^3) h' kk L (g:real^2->real^N) a d0` THEN
    REWRITE_TAC[moi_lgb1_sml] THEN STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!R x y s. R IN moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk) /\ x IN R /\
                          dist(y,g x) < d0 /\ s IN tt /\ y IN s ==> s IN moi_lgb1_t3 tt kk`
  (LABEL_TAC "mg") THENL
   [UNDISCH_TAC `moi_lgb1_sml tt u (h:real^N->real^3) h' kk L (g:real^2->real^N) a d0` THEN
    REWRITE_TAC[moi_lgb1_sml] THEN STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. r IN moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)
                    ==> r IN moi_lgb1_l3 L g (moi_lgb1_th tt kk)` (LABEL_TAC "mL3") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_LGB1_LM_L3 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!r r'. r IN L /\ r' IN moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk) /\
                       r SUBSET r' /\ ~(r = {})
                       ==> r IN moi_lgb1_l3 L g (moi_lgb1_th tt kk)` (LABEL_TAC "fL3") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_LGB1_MEET_LM_L3 THEN
    EXISTS_TAC `r':real^2->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_lgb1_cutsetup] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_LGB1_H_SC THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `u:real^N->bool`; `h':real^3->real^N`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[moi_lgb1_lm] THEN SET_TAC[];
    REPEAT STRIP_TAC THEN MP_TAC(ISPEC `r:real^2->bool` AFF_DIM_LE_UNIV) THEN
    REWRITE_TAC[DIMINDEX_2];
    REWRITE_TAC[moi_lgb1_lm; IN_ELIM_THM] THEN SET_TAC[];
    X_GEN_TAC `r:real^2->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `r':real^2->bool` STRIP_ASSUME_TAC)) THEN
    ASM_CASES_TAC `r:real^2->bool = {}` THENL
     [MAP_EVERY EXISTS_TAC [`\x:real^2. vec 0:real^3`; `vec 0:real^3`] THEN
      ASM_REWRITE_TAC[LINEAR_ZERO; NOT_IN_EMPTY];
      ALL_TAC] THEN
    USE_THEN "itp" (MATCH_MP_TAC o CONJUNCT1 o REWRITE_RULE[moi_lgb1_interp]) THEN
    USE_THEN "fL3" MATCH_MP_TAC THEN EXISTS_TAC `r':real^2->bool` THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "inj" (MP_TAC o SPEC `r:real^2->bool`) THEN
    ANTS_TAC THENL [USE_THEN "mL3" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `r:real^2->bool` THEN DISCH_TAC THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    USE_THEN "cl" (MP_TAC o SPECL [`r:real^2->bool`; `x:real^2`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "mL3" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      STRIP_TAC] THEN
    SUBGOAL_THEN `(h:real^N->real^3) ((h':real^3->real^N) ((a:real^2->real^3) x)) = a x /\
                  h' (a x) IN u` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(ASSUME `!z. z IN IMAGE (h:real^N->real^3) u
                              ==> h ((h':real^3->real^N) z) = z /\ h' z IN u`) THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(u:real^N->bool) SUBSET UNIONS tt` ASSUME_TAC THENL
     [UNDISCH_TAC `moi_lgb1_chart (c:(real^N->bool)->bool) tt u h h' kk` THEN
      REWRITE_TAC[moi_lgb1_chart] THEN
      DISCH_THEN(ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2);
      ALL_TAC] THEN
    SUBGOAL_THEN `(h':real^3->real^N) ((a:real^2->real^3) x) IN UNIONS tt` MP_TAC THENL
     [UNDISCH_TAC `(u:real^N->bool) SUBSET UNIONS tt` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[IN_UNIONS]] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `s:real^N->bool` THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:real^N->bool`] MOI_LGB1_TH_SUBSET) THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
      USE_THEN "mg" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`r:real^2->bool`; `x:real^2`; `(h':real^3->real^N) (a (x:real^2))`] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(h':real^3->real^N) (a (x:real^2))` THEN
      ASM_REWRITE_TAC[]];
    X_GEN_TAC `r:real^2->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `r':real^2->bool` STRIP_ASSUME_TAC))) THEN
    ASM_CASES_TAC `r:real^2->bool = {}` THENL
     [ASM_REWRITE_TAC[IMAGE_CLAUSES; EMPTY_SUBSET] THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `L:(real^2->bool)->bool`;
                     `g:real^2->real^N`; `kk:real^N->bool`; `r':real^2->bool`]
        MOI_LGB1_LM_SECOND) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC `IMAGE (h:real^N->real^3) s2` THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:real^N->bool`] MOI_LGB1_TH_SUBSET) THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
      REWRITE_TAC[moi_lgb1_t3; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`s1:real^N->bool`; `s2:real^N->bool`] THEN
      ASM_REWRITE_TAC[INTER_IDEMPOT] THEN
      SUBGOAL_THEN `~(r':real^2->bool = {})` MP_TAC THENL
       [UNDISCH_TAC `r' IN moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)` THEN
        REWRITE_TAC[moi_lgb1_lm; IN_ELIM_THM] THEN SET_TAC[];
        ASM SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `r IN moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)` ASSUME_TAC THENL
     [USE_THEN "fL3" MATCH_MP_TAC THEN EXISTS_TAC `r':real^2->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                   `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                   `a:real^2->real^3`; `r:real^2->bool`] MOI_LGB1_UNMOVED_A0) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(r IN moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk))` THEN
      REWRITE_TAC[moi_lgb1_lm; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
      DISCH_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `r:real^2->bool`]
      MOI_LGB1_L3_A0) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `S:real^3->bool` STRIP_ASSUME_TAC o last o CONJUNCTS) THEN
    EXISTS_TAC `S:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE ((h:real^N->real^3) o (g:real^2->real^N)) r` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[IN_IMAGE; o_THM] THEN
    EXISTS_TAC `x:real^2` THEN ASM_SIMP_TAC[]]);;

(* The 2-cells of the moved simplices (the cells that get cone points).     *)

let moi_lgb1_c2 = new_definition
 `moi_lgb1_c2 mv (a:real^2->real^3) (H:(real^3->bool)->bool) =
    {moi_lgb1_cell a r s | r,s | r IN mv /\ s IN H /\ aff_dim (moi_lgb1_cell a r s) = &2}`;;

let MOI_LGB1_C2_CELL = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a d0 P.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     moi_lgb1_sml tt u h h' kk L g a d0 /\
     P IN moi_lgb1_c2 (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a (IMAGE (IMAGE h) (moi_lgb1_th tt kk))
     ==> polytope P /\ convex P /\ aff_dim P = &2 /\
         aff_dim (IMAGE a P) = &2 /\
         (?l y. linear l /\ !x. x IN P ==> a x = l x + y) /\
         (!x y. x IN P /\ y IN P /\ a x = a y ==> x = y) /\
         (?YP. YP SUBSET IMAGE phi {v | {v} IN moi_lgb1_l3 L g (moi_lgb1_th tt kk)} /\
               affine hull YP = affine hull (IMAGE a P))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lgb1_c2; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `r:real^2->bool` (X_CHOOSE_THEN `s:real^3->bool`
      (CONJUNCTS_THEN2 STRIP_ASSUME_TAC SUBST_ALL_TAC)))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `d0:real`] MOI_LGB1_CUTSETUP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `moi_lgb1_interp (moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)) phi a`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lgb1_mvd tt (h:real^N->real^3) kk L (g:real^2->real^N) hs phi rk a` THEN
    REWRITE_TAC[moi_lgb1_mvd] THEN STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `g:real^2->real^N`;
                 `moi_lgb1_th (tt:(real^N->bool)->bool) kk`] MOI_LGB1_L3_SC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `r IN moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LGB1_LM_L3 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)`;
                 `a:real^2->real^3`; `IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)`;
                 `r:real^2->bool`; `s:real^3->bool`] MOI_LGB1_CUT_CELL_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)`;
                 `a:real^2->real^3`; `IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)`;
                 `r:real^2->bool`] MOI_LGB1_SETUP_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_THEN `l:real^2->real^3`
      (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) (LABEL_TAC "rinj"))))) THEN
  SUBGOAL_THEN `aff_dim (r:real^2->bool) = &2` ASSUME_TAC THENL
   [MP_TAC(ISPEC `r:real^2->bool` AFF_DIM_LE_UNIV) THEN
    MP_TAC(ISPECL [`moi_lgb1_cell (a:real^2->real^3) r s`; `r:real^2->bool`] AFF_DIM_SUBSET) THEN
    ASM_REWRITE_TAC[DIMINDEX_2] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN moi_lgb1_cell (a:real^2->real^3) r s ==> a x = l x + y`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_lgb1_cell; IN_ELIM_THM] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x x'. x IN moi_lgb1_cell (a:real^2->real^3) r s /\
                       x' IN moi_lgb1_cell a r s /\ a x = a x' ==> x = x'`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_lgb1_cell; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    USE_THEN "rinj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (IMAGE (a:real^2->real^3) (moi_lgb1_cell a r s)) = &2` ASSUME_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `aff_dim (moi_lgb1_cell (a:real^2->real^3) r s)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC MOI_LGB1_AFF_DIM_INJ THEN
    MAP_EVERY EXISTS_TAC [`l:real^2->real^3`; `y:real^3`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (IMAGE (a:real^2->real^3) r) = &2` ASSUME_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `aff_dim (r:real^2->bool)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC MOI_LGB1_AFF_DIM_INJ THEN
    MAP_EVERY EXISTS_TAC [`l:real^2->real^3`; `y:real^3`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`l:real^2->real^3`; `y:real^3`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `IMAGE (phi:real^2->real^3) {v | v extreme_point_of r}` THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `v:real^2` THEN
    DISCH_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MP_TAC(ISPECL [`moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)`; `r:real^2->bool`]
      MOI_LGB1_VERTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `v:real^2` o last o CONJUNCTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)`; `phi:real^2->real^3`;
                 `a:real^2->real^3`; `r:real^2->bool`] MOI_LGB1_INTERP_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  TRANS_TAC EQ_TRANS `affine hull (IMAGE (a:real^2->real^3) r)` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[AFFINE_HULL_CONVEX_HULL]; ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC AFF_DIM_EQ_AFFINE_HULL THEN
  ASM_SIMP_TAC[IMAGE_SUBSET; INT_LE_REFL]);;

let MOI_LGB1_CONES_EXIST = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a d0.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     moi_lgb1_sml tt u h h' kk L g a d0
     ==> ?b. (!P. P IN moi_lgb1_c2 (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                                   (IMAGE (IMAGE h) (moi_lgb1_th tt kk))
                  ==> b P IN relative_interior P) /\
             (!P Y. P IN moi_lgb1_c2 (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                                     (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) /\
                    Y SUBSET moi_lgb1_xc phi {v | {v} IN moi_lgb1_l3 L g (moi_lgb1_th tt kk)}
                      ({z | {z} IN IMAGE (IMAGE h) (moi_lgb1_th tt kk)} UNION
                       {a w | w | ?P'. P' IN moi_lgb1_c2 (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                                                         (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) /\
                                       w extreme_point_of P'}) /\
                    ~(affine hull (IMAGE a P) SUBSET affine hull Y)
                    ==> ~(a (b P) IN affine hull Y)) /\
             (!P P' w w'. P IN moi_lgb1_c2 (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                                           (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) /\
                          P' IN moi_lgb1_c2 (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                                            (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) /\
                          ~(affine hull (IMAGE a P) = affine hull (IMAGE a P')) /\
                          w extreme_point_of P /\ w' extreme_point_of P'
                          ==> DISJOINT (IMAGE a (segment(b P,w)))
                                       (IMAGE a (segment(b P',w'))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `d0:real`] MOI_LGB1_CUTSETUP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `g:real^2->real^N`;
                 `moi_lgb1_th (tt:(real^N->bool)->bool) kk`] MOI_LGB1_L3_SC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_LGB1_CONE_POINTS THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`L:(real^2->bool)->bool`;
                   `moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)`;
                   `a:real^2->real^3`; `IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)`;
                   `\r s. aff_dim (moi_lgb1_cell (a:real^2->real^3) r s) = &2`]
      MOI_LGB1_CUT_CELLS_FINITE) THEN
    ASM_REWRITE_TAC[moi_lgb1_c2];
    MATCH_MP_TAC FINITE_IMAGE_INJ THEN REWRITE_TAC[] THEN CONJ_TAC THENL
     [SET_TAC[];
      UNDISCH_TAC `simplicial_complex (moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk))` THEN
      SIMP_TAC[simplicial_complex]];
    MATCH_MP_TAC FINITE_IMAGE_INJ THEN REWRITE_TAC[] THEN CONJ_TAC THENL
     [SET_TAC[];
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                     `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`] MOI_LGB1_H_SC) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[simplicial_complex]];
    X_GEN_TAC `P:real^2->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                   `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                   `a:real^2->real^3`; `d0:real`; `P:real^2->bool`] MOI_LGB1_C2_CELL) THEN
    ASM_REWRITE_TAC[]]);;

let MOI_LGB1_CUT_FACTS = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a d0 b.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     moi_lgb1_sml tt u h h' kk L g a d0 /\
     (!P. P IN moi_lgb1_c2 (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                           (IMAGE (IMAGE h) (moi_lgb1_th tt kk))
          ==> b P IN relative_interior P)
     ==> simplicial_complex (moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                                          (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) b) /\
         UNIONS (moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                              (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) b) = std_triangle /\
         (!t. t IN moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                                (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) b
              ==> ?r. r IN L /\ t SUBSET r) /\
         (!t. t IN moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                                (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) b
              ==> (t IN L /\ ~(t IN moi_lgb1_lm L (moi_lgb1_kv L g kk))) \/
                  ?r s. r IN moi_lgb1_lm L (moi_lgb1_kv L g kk) /\
                        s IN IMAGE (IMAGE h) (moi_lgb1_th tt kk) /\
                        t SUBSET moi_lgb1_cell a r s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bri")))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `d0:real`] MOI_LGB1_CUTSETUP) THEN
  ASM_REWRITE_TAC[moi_lgb1_cutsetup] THEN STRIP_TAC THEN
  SUBGOAL_THEN `std_triangle = UNIONS (L:(real^2->bool)->bool)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_LGB1_CUT_COMPLEX THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`r:real^2->bool`; `s:real^3->bool`] THEN STRIP_TAC THEN
  USE_THEN "bri" MATCH_MP_TAC THEN REWRITE_TAC[moi_lgb1_c2; IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC [`r:real^2->bool`; `s:real^3->bool`] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* C15. The moved map: g' = h' o a on the moved simplices, g elsewhere.     *)
(* It agrees with h' o a on the whole of L3 and with g on the unmoved      *)
(* simplices; it is T-linear on the cut complex, PL and continuous, maps   *)
(* into |c| and has the boundary preimage of g.                            *)
(* ------------------------------------------------------------------------- *)

let moi_lgb1_gp = new_definition
 `moi_lgb1_gp mv (g:real^2->real^N) (h':real^3->real^N) (a:real^2->real^3) x =
    if x IN UNIONS mv then h' (a x) else g x`;;

let MOI_LGB1_GP_L3 = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a R x.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     R IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\ x IN R
     ==> moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a x = h' (a x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_lgb1_gp] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `R:real^2->bool`]
    MOI_LGB1_L3_A0) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `R INTER moi_lgb1_kv L (g:real^2->real^N) kk = {}` ASSUME_TAC THENL
   [UNDISCH_TAC `~(x IN UNIONS (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)))` THEN
    REWRITE_TAC[IN_UNIONS; moi_lgb1_lm; IN_ELIM_THM; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `R:real^2->bool`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `R:real^2->bool`] MOI_LGB1_UNMOVED_A0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o C MATCH_MP (ASSUME `(x:real^2) IN R`)) THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(g:real^2->real^N) x IN u` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (g:real^2->real^N) R SUBSET u` THEN
    UNDISCH_TAC `(x:real^2) IN R` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP (SPEC `(g:real^2->real^N) x`
    (ASSUME `!x. x IN u ==> (h':real^3->real^N) ((h:real^N->real^3) x) = x /\
                            h x IN IMAGE h u`))
    (ASSUME `(g:real^2->real^N) x IN u`)) THEN
  SIMP_TAC[]);;

let MOI_LGB1_GP_UNMOVED = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a r x.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     r IN L /\ r INTER moi_lgb1_kv L g kk = {} /\ x IN r
     ==> moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a x = g x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[moi_lgb1_gp] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  UNDISCH_TAC `x IN UNIONS (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk))` THEN
  REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `r':real^2->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `r' IN (L:(real^2->bool)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `r' IN moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)` THEN
    REWRITE_TAC[moi_lgb1_lm; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(r INTER r') IN (L:(real^2->bool)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_complex (L:(real^2->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
      (CONJUNCTS_THEN2 (LABEL_TAC "fc") (LABEL_TAC "ic")))) THEN
    USE_THEN "fc" MATCH_MP_TAC THEN EXISTS_TAC `r:real^2->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(r INTER r') IN moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LGB1_MEET_LM_L3 THEN EXISTS_TAC `r':real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(x:real^2) IN r` THEN UNDISCH_TAC `(x:real^2) IN r'` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `r INTER r':real^2->bool`]
    MOI_LGB1_L3_A0) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `r INTER r':real^2->bool`] MOI_LGB1_UNMOVED_A0) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `r INTER moi_lgb1_kv L (g:real^2->real^N) kk = {}` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[IN_INTER] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(g:real^2->real^N) x IN u` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (g:real^2->real^N) (r INTER r') SUBSET u` THEN
    UNDISCH_TAC `(x:real^2) IN r` THEN UNDISCH_TAC `(x:real^2) IN r'` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP (SPEC `(g:real^2->real^N) x`
    (ASSUME `!x. x IN u ==> (h':real^3->real^N) ((h:real^N->real^3) x) = x /\
                            h x IN IMAGE h u`))
    (ASSUME `(g:real^2->real^N) x IN u`)) THEN
  SIMP_TAC[]);;

let MOI_LGB1_GP_TLINEAR = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a d0 b.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     moi_lgb1_sml tt u h h' kk L g a d0 /\
     (!P. P IN moi_lgb1_c2 (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                           (IMAGE (IMAGE h) (moi_lgb1_th tt kk))
          ==> b P IN relative_interior P)
     ==> moi_lgb_tlinear tt
           (moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                         (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) b)
           (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_LGB1_CUT_FACTS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "inL") (LABEL_TAC "cases")))) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `d0:real`] MOI_LGB1_CUTSETUP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[moi_lgb_tlinear] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real^2->bool` THEN DISCH_TAC THEN
  USE_THEN "cases" (MP_TAC o SPEC `t:real^2->bool`) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  STRIP_TAC THENL
   [SUBGOAL_THEN `t INTER moi_lgb1_kv L (g:real^2->real^N) kk = {}` ASSUME_TAC THENL
     [UNDISCH_TAC `~(t IN moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk))` THEN
      REWRITE_TAC[moi_lgb1_lm; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `!x. x IN t ==> moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk))
                                  g h' a x = g x` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_LGB1_GP_UNMOVED THEN
      MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                            `u:real^N->bool`; `h:real^N->real^3`; `Q:real^N->bool`;
                            `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                            `t:real^2->bool`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `moi_lgb_tlinear tt L (g:real^2->real^N)` THEN
    REWRITE_TAC[moi_lgb_tlinear] THEN
    DISCH_THEN(MP_TAC o SPEC `t:real^2->bool` o last o CONJUNCTS) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `(p ==> p') /\ (q ==> q') ==> p /\ q ==> p' /\ q'`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `s:real^N->bool` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (g:real^2->real^N) t SUBSET s` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
      REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `s:real^3->bool`] MOI_LGB1_H_INV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "seq" o SYM) (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "sinv") (X_CHOOSE_THEN `l2:real^3->real^N`
         (X_CHOOSE_THEN `y2:real^N` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "haff"))))))))) THEN
  SUBGOAL_THEN `s0 IN (tt:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `s0:real^N->bool`] MOI_LGB1_TH_FACTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)`;
                 `a:real^2->real^3`; `IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)`;
                 `r:real^2->bool`] MOI_LGB1_SETUP_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l1:real^2->real^3` (X_CHOOSE_THEN `y1:real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "aaff"))) o
    CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  SUBGOAL_THEN `!x. x IN t ==> (x:real^2) IN r /\ (a:real^2->real^3) x IN s /\
                     moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk))
                       g h' a x = h' (a x)`
  (LABEL_TAC "tx") THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN r /\ (a:real^2->real^3) x IN s` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `t SUBSET moi_lgb1_cell (a:real^2->real^3) r s` THEN
      REWRITE_TAC[SUBSET; moi_lgb1_cell; IN_ELIM_THM] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `x IN UNIONS (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk))`
    ASSUME_TAC THENL
     [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `r:real^2->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[moi_lgb1_gp];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [EXISTS_TAC `s0:real^N->bool` THEN ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    USE_THEN "tx" (MP_TAC o C MATCH_MP (ASSUME `(x:real^2) IN t`)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    USE_THEN "sinv" (MP_TAC o C MATCH_MP (ASSUME `(a:real^2->real^3) x IN s`)) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`(l2:real^3->real^N) o (l1:real^2->real^3)`;
                        `(l2:real^3->real^N) y1 + y2`] THEN
  ASM_SIMP_TAC[LINEAR_COMPOSE] THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  USE_THEN "tx" (MP_TAC o C MATCH_MP (ASSUME `(x:real^2) IN t`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  SUBGOAL_THEN `(h':real^3->real^N) (a (x:real^2)) = l2 (a x) + y2` SUBST1_TAC THENL
   [USE_THEN "haff" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^2->real^3) x = l1 x + y1` SUBST1_TAC THENL
   [USE_THEN "aaff" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[LINEAR_ADD; o_THM] THEN VECTOR_ARITH_TAC);;

let MOI_LGB1_GP_PL = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a d0 b.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     moi_lgb1_sml tt u h h' kk L g a d0 /\
     (!P. P IN moi_lgb1_c2 (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                           (IMAGE (IMAGE h) (moi_lgb1_th tt kk))
          ==> b P IN relative_interior P)
     ==> moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a continuous_on std_triangle /\
         pl_map_on std_triangle (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_LGB1_GP_TLINEAR) THEN
  REWRITE_TAC[moi_lgb_tlinear] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (LABEL_TAC "pw"))) THEN
  MATCH_MP_TAC MOI_REAL_PIECEWISE_AFFINE_UNIONS THEN CONJ_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  X_GEN_TAC `t:real^2->bool` THEN DISCH_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_POLYTOPE]; ALL_TAC] THEN
  USE_THEN "pw" (MP_TAC o SPEC `t:real^2->bool`) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]]);;

let MOI_LGB1_GP_MOVED_FACTS = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a d0 x.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     moi_lgb1_sml tt u h h' kk L g a d0 /\
     x IN UNIONS (moi_lgb1_lm L (moi_lgb1_kv L g kk))
     ==> moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a x = h' (a x) /\
         a x IN IMAGE h u /\ h' (a x) IN u /\ h (h' (a x)) = a x /\
         dist(h' (a x),g x) < d0 /\ g x IN u /\
         (?R. R IN moi_lgb1_lm L (moi_lgb1_kv L g kk) /\
              R IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\ x IN R)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  UNDISCH_TAC `x IN UNIONS (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk))` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC (REWRITE_RULE[IN_UNIONS] th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real^2->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `R IN moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LGB1_LM_L3 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `R:real^2->bool`]
    MOI_LGB1_L3_A0) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(a:real^2->real^3) x IN IMAGE (h:real^N->real^3) u /\
                dist((h':real^3->real^N) (a x),g x) < d0` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lgb1_sml tt u (h:real^N->real^3) h' kk L (g:real^2->real^N) a d0` THEN
    REWRITE_TAC[moi_lgb1_sml] THEN DISCH_THEN(MP_TAC o SPECL [`R:real^2->bool`; `x:real^2`] o
      CONJUNCT1) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP (SPEC `(a:real^2->real^3) x`
    (ASSUME `!z. z IN IMAGE (h:real^N->real^3) u ==> h ((h':real^3->real^N) z) = z /\
                                                     h' z IN u`))
    (ASSUME `(a:real^2->real^3) x IN IMAGE (h:real^N->real^3) u`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[moi_lgb1_gp] THEN CONJ_TAC THENL
   [UNDISCH_TAC `IMAGE (g:real^2->real^N) R SUBSET u` THEN
    UNDISCH_TAC `(x:real^2) IN R` THEN SET_TAC[];
    EXISTS_TAC `R:real^2->bool` THEN ASM_REWRITE_TAC[]]);;

let MOI_LGB1_GP_IMAGE = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a d0.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     moi_lgb1_sml tt u h h' kk L g a d0
     ==> IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a) std_triangle
         SUBSET UNIONS c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  ASM_CASES_TAC `x IN UNIONS (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk))` THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                   `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                   `a:real^2->real^3`; `d0:real`; `x:real^2`] MOI_LGB1_GP_MOVED_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(u:real^N->bool) SUBSET UNIONS c` MP_TAC THENL
     [UNDISCH_TAC `moi_lgb1_chart (c:(real^N->bool)->bool) tt u h h' kk` THEN
      REWRITE_TAC[moi_lgb1_chart] THEN
      DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET o CONJUNCT1 o CONJUNCT2) THEN
      REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[moi_lgb1_gp] THEN
    UNDISCH_TAC `moi_lt_singular_disk (c:(real^N->bool)->bool) g` THEN
    REWRITE_TAC[moi_lt_singular_disk] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

let MOI_LGB1_GP_BOUNDARY = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a d0.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     moi_lgb1_sml tt u h h' kk L g a d0
     ==> {x | x IN std_triangle /\
              moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a x IN complex_boundary c} =
         relative_frontier std_triangle`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  SUBGOAL_THEN `!x. x IN u ==> (x IN complex_boundary c <=>
                     hs = {z:real^3 | &0 <= z$3} /\ ((h:real^N->real^3) x)$3 = &0)`
  (LABEL_TAC "bd") THENL
   [UNDISCH_TAC `moi_lgb1_fix (c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs` THEN
    REWRITE_TAC[moi_lgb1_fix] THEN DISCH_THEN(ACCEPT_TAC o last o CONJUNCTS);
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN std_triangle ==> ((g:real^2->real^N) x IN complex_boundary c <=>
                                           x IN relative_frontier std_triangle)`
  (LABEL_TAC "gbd") THENL
   [UNDISCH_TAC `moi_lt_singular_disk (c:(real^N->bool)->bool) g` THEN
    REWRITE_TAC[moi_lt_singular_disk] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier std_triangle SUBSET std_triangle` ASSUME_TAC THENL
   [MP_TAC MOI_LTD_STD_TRIANGLE_BASIC THEN
    SIMP_TAC[relative_frontier; CLOSURE_CLOSED] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:real^2` THEN
  ASM_CASES_TAC `(x:real^2) IN std_triangle` THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `relative_frontier std_triangle SUBSET std_triangle` THEN
    UNDISCH_TAC `~((x:real^2) IN std_triangle)` THEN SET_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `x IN UNIONS (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk))` THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[moi_lgb1_gp] THEN USE_THEN "gbd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `d0:real`; `x:real^2`] MOI_LGB1_GP_MOVED_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC (MAP_EVERY ASSUME_TAC o CONJUNCTS)) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `R:real^2->bool` STRIP_ASSUME_TAC o check (is_exists o concl)) THEN
  USE_THEN "bd" (MP_TAC o C MATCH_MP
    (ASSUME `(h':real^3->real^N) ((a:real^2->real^3) x) IN u`)) THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `R:real^2->bool`; `x:real^2`] MOI_LGB1_ZERO_PATTERN) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `x:real^2`] MOI_LGB1_BD_CHAR) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `hs = {z:real^3 | &0 <= z$3}` THEN ASM_REWRITE_TAC[] THEN CONV_TAC TAUT);;

let MOI_LGB1_GP_CLOSE = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a d0.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     moi_lgb1_sml tt u h h' kk L g a d0 /\ &0 < d0
     ==> !x. x IN std_triangle
             ==> dist(moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a x,g x) < d0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  ASM_CASES_TAC `x IN UNIONS (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk))` THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                   `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                   `a:real^2->real^3`; `d0:real`; `x:real^2`] MOI_LGB1_GP_MOVED_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[moi_lgb1_gp; DIST_REFL]]);;

let MOI_LGB1_GP_OFF_U = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a d0.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     moi_lgb1_sml tt u h h' kk L g a d0
     ==> !x. x IN std_triangle /\ ~(g x IN u)
             ==> moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a x = g x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
  ASM_CASES_TAC `x IN UNIONS (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk))` THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                   `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                   `a:real^2->real^3`; `d0:real`; `x:real^2`] MOI_LGB1_GP_MOVED_FACTS) THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[moi_lgb1_gp]]);;

(* Uniform local injectivity of the moved map at the Lebesgue scale of the  *)
(* closed stars of L, and the singular disk property.                       *)

let MOI_LGB1_GP_ULI = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a d0 rho.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     moi_lgb1_sml tt u h h' kk L g a d0 /\
     (!v. {v} IN L /\
          (!r. r IN L /\ v IN r ==> r IN moi_lgb1_l3 L g (moi_lgb1_th tt kk))
          ==> !x y. x IN UNIONS {r | r IN L /\ v IN r} /\
                    y IN UNIONS {r | r IN L /\ v IN r} /\ a x = a y ==> x = y) /\
     (!x y. x IN UNIONS L /\ y IN UNIONS L /\ dist(x,y) < rho
            ==> ?v. {v} IN L /\ x IN UNIONS {r | r IN L /\ v IN r} /\
                    y IN UNIONS {r | r IN L /\ v IN r})
     ==> !x y. x IN std_triangle /\ y IN std_triangle /\ dist(x,y) < rho /\
               moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a x =
               moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a y
               ==> x = y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "star") (LABEL_TAC "leb"))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN STRIP_TAC THEN
  USE_THEN "leb" (MP_TAC o SPECL [`x:real^2`; `y:real^2`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^2` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC
   `!r. r IN L /\ (v:real^2) IN r ==> r IN moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)`
  THENL
   [POP_ASSUM(LABEL_TAC "allL3") THEN
    USE_THEN "star" (MP_TAC o SPEC `v:real^2`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `!z. z IN UNIONS {r | r IN L /\ (v:real^2) IN r}
                      ==> moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk))
                            g h' a z = h' (a z) /\
                          (a:real^2->real^3) z IN IMAGE (h:real^N->real^3) u`
    (LABEL_TAC "hz") THENL
     [X_GEN_TAC `z:real^2` THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `r1:real^2->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `r1 IN moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)` ASSUME_TAC THENL
       [USE_THEN "allL3" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MOI_LGB1_GP_L3 THEN
        MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                              `u:real^N->bool`; `h:real^N->real^3`; `Q:real^N->bool`;
                              `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                              `r1:real^2->bool`] THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `moi_lgb1_sml tt u (h:real^N->real^3) h' kk L (g:real^2->real^N) a d0` THEN
        REWRITE_TAC[moi_lgb1_sml] THEN
        DISCH_THEN(MP_TAC o SPECL [`r1:real^2->bool`; `z:real^2`] o CONJUNCT1) THEN
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    USE_THEN "hz" (fun th ->
      MP_TAC(MATCH_MP th (ASSUME `x IN UNIONS {r | r IN L /\ (v:real^2) IN r}`)) THEN
      MP_TAC(MATCH_MP th (ASSUME `y IN UNIONS {r | r IN L /\ (v:real^2) IN r}`))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC) ASSUME_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC) ASSUME_TAC) THEN
    MP_TAC(MATCH_MP (SPEC `(a:real^2->real^3) x`
      (ASSUME `!z. z IN IMAGE (h:real^N->real^3) u ==> h ((h':real^3->real^N) z) = z /\
                                                       h' z IN u`))
      (ASSUME `(a:real^2->real^3) x IN IMAGE (h:real^N->real^3) u`)) THEN
    MP_TAC(MATCH_MP (SPEC `(a:real^2->real^3) y`
      (ASSUME `!z. z IN IMAGE (h:real^N->real^3) u ==> h ((h':real^3->real^N) z) = z /\
                                                       h' z IN u`))
      (ASSUME `(a:real^2->real^3) y IN IMAGE (h:real^N->real^3) u`)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (K ALL_TAC)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (K ALL_TAC)) THEN
    AP_TERM_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `r0:real^2->bool` STRIP_ASSUME_TAC o
    REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
  SUBGOAL_THEN `!r. r IN L /\ (v:real^2) IN r
                    ==> r INTER moi_lgb1_kv L (g:real^2->real^N) kk = {}`
  (LABEL_TAC "um") THENL
   [X_GEN_TAC `r:real^2->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    UNDISCH_TAC `~(r0 IN moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk))` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC MOI_LGB1_MEET_LM_L3 THEN EXISTS_TAC `r:real^2->bool` THEN
    ASM_REWRITE_TAC[moi_lgb1_lm; IN_ELIM_THM] THEN
    UNDISCH_TAC `(v:real^2) IN r` THEN UNDISCH_TAC `(v:real^2) IN r0` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN UNIONS {r | r IN L /\ (v:real^2) IN r}
                    ==> moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk))
                          g h' a z = g z`
  (LABEL_TAC "gz") THENL
   [X_GEN_TAC `z:real^2` THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `r1:real^2->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC MOI_LGB1_GP_UNMOVED THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                          `u:real^N->bool`; `h:real^N->real^3`; `Q:real^N->bool`;
                          `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                          `r1:real^2->bool`] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "um" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `v:real^2`]
    MOI_LGB1_G_INJ_STAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "gz" (fun th ->
    MP_TAC(MATCH_MP th (ASSUME `x IN UNIONS {r | r IN L /\ (v:real^2) IN r}`)) THEN
    MP_TAC(MATCH_MP th (ASSUME `y IN UNIONS {r | r IN L /\ (v:real^2) IN r}`))) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_ASSUM ACCEPT_TAC);;

let MOI_LGB1_GP_DISK = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a d0 b rho.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     moi_lgb1_sml tt u h h' kk L g a d0 /\
     (!P. P IN moi_lgb1_c2 (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                           (IMAGE (IMAGE h) (moi_lgb1_th tt kk))
          ==> b P IN relative_interior P) /\
     (!v. {v} IN L /\
          (!r. r IN L /\ v IN r ==> r IN moi_lgb1_l3 L g (moi_lgb1_th tt kk))
          ==> !x y. x IN UNIONS {r | r IN L /\ v IN r} /\
                    y IN UNIONS {r | r IN L /\ v IN r} /\ a x = a y ==> x = y) /\
     &0 < rho /\
     (!x y. x IN UNIONS L /\ y IN UNIONS L /\ dist(x,y) < rho
            ==> ?v. {v} IN L /\ x IN UNIONS {r | r IN L /\ v IN r} /\
                    y IN UNIONS {r | r IN L /\ v IN r}) /\
     &0 < d0 /\
     (!g':real^2->real^N.
        (!x. x IN std_triangle ==> dist(g' x,g x) < d0) /\
        (!x y. x IN std_triangle /\ y IN std_triangle /\ dist(x,y) < rho /\ g' x = g' y
               ==> x = y)
        ==> !y. FINITE {x | x IN std_triangle /\ g' x = y} /\
                CARD {x | x IN std_triangle /\ g' x = y} <= 2)
     ==> moi_lt_singular_disk c (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "two"))))))))) THEN
  SUBGOAL_THEN `!x y. x IN std_triangle /\ y IN std_triangle /\ dist(x,y) < rho /\
                      moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)) g h' a x =
                      moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a y ==> x = y`
  (LABEL_TAC "uli") THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                   `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                   `a:real^2->real^3`; `d0:real`; `rho:real`] MOI_LGB1_GP_ULI) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_lt_singular_disk] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                   `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                   `a:real^2->real^3`; `d0:real`; `b:(real^2->bool)->real^2`] MOI_LGB1_GP_PL) THEN
    ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                   `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                   `a:real^2->real^3`; `d0:real`] MOI_LGB1_GP_IMAGE) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                   `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                   `a:real^2->real^3`; `d0:real`] MOI_LGB1_GP_BOUNDARY) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN EXISTS_TAC `ball(x:real^2,rho / &2)` THEN
    REWRITE_TAC[OPEN_BALL; IN_INTER; IN_BALL; DIST_REFL] THEN CONJ_TAC THENL
     [UNDISCH_TAC `&0 < rho` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`y:real^2`; `z:real^2`] THEN STRIP_TAC THEN
    USE_THEN "uli" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`y:real^2`; `x:real^2`; `z:real^2`] DIST_TRIANGLE) THEN
    MP_TAC(ISPECL [`x:real^2`; `y:real^2`] DIST_SYM) THEN
    UNDISCH_TAC `dist(x:real^2,y) < rho / &2` THEN UNDISCH_TAC `dist(x:real^2,z) < rho / &2` THEN
    REAL_ARITH_TAC;
    USE_THEN "two" MATCH_MP_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                     `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                     `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                     `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                     `a:real^2->real^3`; `d0:real`] MOI_LGB1_GP_CLOSE) THEN
      ASM_REWRITE_TAC[];
      USE_THEN "uli" ACCEPT_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* C16. Double points of the moved map.  moi_lgb1_sm2: the further          *)
(* smallness facts (star injectivity, sides of centroids, distance of the   *)
(* double points of g in Q on the 1-skeleton).  Carriers in a complex.      *)
(* A double point of g' with an unmoved and with a moved carrier; the       *)
(* pointwise forms of clauses 1 and 5 of tgeneric.                          *)
(* ------------------------------------------------------------------------- *)

let moi_lgb1_sm2 = new_definition
 `moi_lgb1_sm2 (tt:(real^N->bool)->bool) (h:real^N->real^3) kk L (g:real^2->real^N) Q
               (a:real^2->real^3) d0 <=>
    (!v. {v} IN L /\
         (!r. r IN L /\ v IN r ==> r IN moi_lgb1_l3 L g (moi_lgb1_th tt kk))
         ==> !x y. x IN UNIONS {r | r IN L /\ v IN r} /\
                   y IN UNIONS {r | r IN L /\ v IN r} /\ a x = a y ==> x = y) /\
    (!R S. R IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\
           S IN IMAGE (IMAGE h) (moi_lgb1_th tt kk) /\ ~(R = {}) /\
           h (g (moi_lgb1_cen R)) IN interior S
           ==> a (moi_lgb1_cen R) IN interior S) /\
    (!R R' x y. R IN L /\ R' IN L /\ DISJOINT R R' /\ x IN R /\
                y IN IMAGE g R' /\ y IN Q /\
                (?s. s IN tt /\ aff_dim s <= &1 /\ y IN s)
                ==> d0 <= dist(g x,y))`;;

let MOI_LGB1_CARRIER = prove
 (`!(K:(real^M->bool)->bool) x.
     simplicial_complex K /\ x IN UNIONS K
     ==> ?R. R IN K /\ x IN relative_interior R /\
             !S. S IN K /\ x IN S ==> R face_of S`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `s:real^M->bool` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_complex]) THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `x:real^M`] IN_RELATIVE_INTERIOR_OF_FACE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^M->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `f:real^M->bool` THEN
  SUBGOAL_THEN `(f:real^M->bool) IN K` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `S:real^M->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(f INTER S:real^M->bool) face_of f /\ (f INTER S) face_of S`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `f SUBSET (f INTER S:real^M->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_OF_FACE_OF THEN EXISTS_TAC `f:real^M->bool` THEN
    ASM_REWRITE_TAC[SUBSET_REFL; DISJOINT; GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `x:real^M` THEN ASM_REWRITE_TAC[IN_INTER] THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `f INTER S:real^M->bool = f` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `f SUBSET (f INTER S:real^M->bool)` THEN SET_TAC[];
    ASM_REWRITE_TAC[]]);;

let MOI_LGB1_PW_UNMOVED = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a x1 x2 R1 R2.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     R1 IN L /\ x1 IN R1 /\ R1 INTER moi_lgb1_kv L g kk = {} /\
     R2 IN L /\ x2 IN R2 /\ R2 INTER moi_lgb1_kv L g kk = {} /\
     ~(x1 = x2) /\
     moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a x1 =
     moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a x2 /\
     moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a x1 IN Q UNION kk
     ==> moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a x1 = g x1 /\
         moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a x2 = g x2 /\
         g x1 = g x2 /\ g x1 IN Q /\ DISJOINT R1 R2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  SUBGOAL_THEN `moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)) g h' a x1 =
                g x1` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LGB1_GP_UNMOVED THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                          `u:real^N->bool`; `h:real^N->real^3`; `Q:real^N->bool`;
                          `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                          `R1:real^2->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)) g h' a x2 =
                g x2` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LGB1_GP_UNMOVED THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                          `u:real^N->bool`; `h:real^N->real^3`; `Q:real^N->bool`;
                          `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                          `R2:real^2->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^2->real^N) x1 = g x2` ASSUME_TAC THENL
   [TRANS_TAC EQ_TRANS
      `moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)) g h' a x1` THEN
    CONJ_TAC THENL [CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    TRANS_TAC EQ_TRANS
      `moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)) g h' a x2` THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^2->real^N) x1 IN Q` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `g:real^2->real^N`; `kk:real^N->bool`;
                   `R1:real^2->bool`; `(g:real^2->real^N) x1`] MOI_LGB1_NO_KK) THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
    UNDISCH_TAC `moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)) g h' a x1
                 IN Q UNION kk` THEN
    ASM_REWRITE_TAC[IN_UNION] THEN CONV_TAC TAUT;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `L:(real^2->bool)->bool`; `g:real^2->real^N`;
                 `Q:real^N->bool`] MOI_LGB1_TGEN_CLAUSES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`R1:real^2->bool`; `R2:real^2->bool`; `x1:real^2`; `x2:real^2`] o
    CONJUNCT1) THEN
  ASM_REWRITE_TAC[DISJOINT]);;

let MOI_LGB1_PW_MOVED = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a d0 x1 x2 R1 R2.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     moi_lgb1_sml tt u h h' kk L g a d0 /\ moi_lgb1_sm2 tt h kk L g Q a d0 /\
     R1 IN L /\ x1 IN R1 /\ ~(R1 INTER moi_lgb1_kv L g kk = {}) /\
     R2 IN L /\ x2 IN R2 /\ ~(x1 = x2) /\
     moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a x1 =
     moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a x2
     ==> R1 IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\
         R2 IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\
         DISJOINT R1 R2 /\ a x1 = a x2 /\ a x1 IN IMAGE h u /\
         moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a x1 = h' (a x1) /\
         dist(h' (a x1),g x1) < d0 /\
         (!s. s IN tt /\ h' (a x1) IN s ==> s IN moi_lgb1_t3 tt kk)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_lgb1_mvd]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_lgb1_sm2]) THEN
  SUBGOAL_THEN `R1 IN moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[moi_lgb1_lm; IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `R1 IN moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LGB1_LM_L3 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^2->real^3) x1 IN IMAGE (h:real^N->real^3) u /\
                dist((h':real^3->real^N) (a x1),g x1) < d0` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lgb1_sml tt u (h:real^N->real^3) h' kk L (g:real^2->real^N) a d0` THEN
    REWRITE_TAC[moi_lgb1_sml] THEN
    DISCH_THEN(MP_TAC o SPECL [`R1:real^2->bool`; `x1:real^2`] o CONJUNCT1) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)) g h' a x1 =
                (h':real^3->real^N) (a x1)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LGB1_GP_L3 THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                          `u:real^N->bool`; `h:real^N->real^3`; `Q:real^N->bool`;
                          `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                          `R1:real^2->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN tt /\ (h':real^3->real^N) (a (x1:real^2)) IN s
                    ==> s IN moi_lgb1_t3 tt kk` (LABEL_TAC "mg1") THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `moi_lgb1_sml tt u (h:real^N->real^3) h' kk L (g:real^2->real^N) a d0` THEN
    REWRITE_TAC[moi_lgb1_sml] THEN
    DISCH_THEN(MP_TAC o SPECL [`R1:real^2->bool`; `x1:real^2`;
      `(h':real^3->real^N) (a (x1:real^2))`; `s:real^N->bool`] o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `R2 IN moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)` ASSUME_TAC THENL
   [ASM_CASES_TAC `R2 INTER moi_lgb1_kv L (g:real^2->real^N) kk = {}` THENL
     [ALL_TAC;
      MATCH_MP_TAC MOI_LGB1_LM_L3 THEN ASM_REWRITE_TAC[moi_lgb1_lm; IN_ELIM_THM]] THEN
    SUBGOAL_THEN `moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)) g h' a x2 =
                  g x2` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_LGB1_GP_UNMOVED THEN
      MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                            `u:real^N->bool`; `h:real^N->real^3`; `Q:real^N->bool`;
                            `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                            `R2:real^2->bool`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(h':real^3->real^N) (a (x1:real^2)) = (g:real^2->real^N) x2` ASSUME_TAC THENL
     [TRANS_TAC EQ_TRANS
        `moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)) g h' a x1` THEN
      CONJ_TAC THENL [CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      TRANS_TAC EQ_TRANS
        `moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)) g h' a x2` THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `moi_lgb_tlinear tt L (g:real^2->real^N)` THEN REWRITE_TAC[moi_lgb_tlinear] THEN
    DISCH_THEN(MP_TAC o SPEC `R2:real^2->bool` o last o CONJUNCTS) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s2:real^N->bool` STRIP_ASSUME_TAC o CONJUNCT1) THEN
    REWRITE_TAC[moi_lgb1_l3; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `s2:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:real^N->bool`] MOI_LGB1_TH_SUBSET) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    USE_THEN "mg1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (g:real^2->real^N) R2 SUBSET s2` THEN
    UNDISCH_TAC `(x2:real^2) IN R2` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^2->real^3) x2 IN IMAGE (h:real^N->real^3) u` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lgb1_sml tt u (h:real^N->real^3) h' kk L (g:real^2->real^N) a d0` THEN
    REWRITE_TAC[moi_lgb1_sml] THEN
    DISCH_THEN(MP_TAC o SPECL [`R2:real^2->bool`; `x2:real^2`] o CONJUNCT1) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)) g h' a x2 =
                (h':real^3->real^N) (a x2)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LGB1_GP_L3 THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                          `u:real^N->bool`; `h:real^N->real^3`; `Q:real^N->bool`;
                          `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                          `R2:real^2->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h':real^3->real^N) (a (x1:real^2)) = h' (a x2)` ASSUME_TAC THENL
   [TRANS_TAC EQ_TRANS
      `moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)) g h' a x1` THEN
    CONJ_TAC THENL [CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    TRANS_TAC EQ_TRANS
      `moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)) g h' a x2` THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^2->real^3) x1 = a x2` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP (SPEC `(a:real^2->real^3) x1`
      (ASSUME `!z. z IN IMAGE (h:real^N->real^3) u ==> h ((h':real^3->real^N) z) = z /\
                                                       h' z IN u`))
      (ASSUME `(a:real^2->real^3) x1 IN IMAGE (h:real^N->real^3) u`)) THEN
    MP_TAC(MATCH_MP (SPEC `(a:real^2->real^3) x2`
      (ASSUME `!z. z IN IMAGE (h:real^N->real^3) u ==> h ((h':real^3->real^N) z) = z /\
                                                       h' z IN u`))
      (ASSUME `(a:real^2->real^3) x2 IN IMAGE (h:real^N->real^3) u`)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (K ALL_TAC)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (K ALL_TAC)) THEN
    AP_TERM_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[DISJOINT] THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  UNDISCH_TAC `~(x1:real^2 = x2)` THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`] MOI_LGB1_INJ_PAIR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`R1:real^2->bool`; `R2:real^2->bool`] THEN
  ASM_REWRITE_TAC[IN_UNION]);;

let MOI_LGB1_PW1 = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a d0 R R' x x'.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     moi_lgb1_sml tt u h h' kk L g a d0 /\ moi_lgb1_sm2 tt h kk L g Q a d0 /\
     R IN L /\ R' IN L /\ ~(R INTER R' = {}) /\ x IN R /\ x' IN R' /\
     moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a x =
     moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a x' /\
     moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a x IN Q UNION kk
     ==> x = x'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(x':real^2 = x)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(x:real^2 = x')` THEN MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `R INTER moi_lgb1_kv L (g:real^2->real^N) kk = {}` THENL
   [ALL_TAC;
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                   `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                   `a:real^2->real^3`; `d0:real`; `x:real^2`; `x':real^2`;
                   `R:real^2->bool`; `R':real^2->bool`] MOI_LGB1_PW_MOVED) THEN
    ASM_REWRITE_TAC[DISJOINT]] THEN
  ASM_CASES_TAC `R' INTER moi_lgb1_kv L (g:real^2->real^N) kk = {}` THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                   `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                   `a:real^2->real^3`; `x:real^2`; `x':real^2`;
                   `R:real^2->bool`; `R':real^2->bool`] MOI_LGB1_PW_UNMOVED) THEN
    ASM_REWRITE_TAC[DISJOINT];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                   `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                   `a:real^2->real^3`; `d0:real`; `x':real^2`; `x:real^2`;
                   `R':real^2->bool`; `R:real^2->bool`] MOI_LGB1_PW_MOVED) THEN
    ASM_REWRITE_TAC[DISJOINT; INTER_COMM]]);;

let MOI_LGB1_GP_CLAUSE1 = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a d0 b.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     moi_lgb1_sml tt u h h' kk L g a d0 /\ moi_lgb1_sm2 tt h kk L g Q a d0 /\
     (!P. P IN moi_lgb1_c2 (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                           (IMAGE (IMAGE h) (moi_lgb1_th tt kk))
          ==> b P IN relative_interior P)
     ==> !r r' x x'.
           r IN moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                             (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) b /\
           r' IN moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                              (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) b /\
           ~(r INTER r' = {}) /\ x IN r /\ x' IN r' /\
           moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a x =
           moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a x' /\
           moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a x IN Q UNION kk
           ==> x = x'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `d0:real`; `b:(real^2->bool)->real^2`]
    MOI_LGB1_CUT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "inL") (K ALL_TAC)))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  USE_THEN "inL" (MP_TAC o SPEC `r:real^2->bool`) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real^2->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "inL" (MP_TAC o SPEC `r':real^2->bool`) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `R':real^2->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `d0:real`; `R:real^2->bool`; `R':real^2->bool`;
                 `x:real^2`; `x':real^2`] MOI_LGB1_PW1) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `~(r INTER r':real^2->bool = {})` THEN
    UNDISCH_TAC `(r:real^2->bool) SUBSET R` THEN UNDISCH_TAC `(r':real^2->bool) SUBSET R'` THEN
    SET_TAC[];
    UNDISCH_TAC `(r:real^2->bool) SUBSET R` THEN UNDISCH_TAC `(x:real^2) IN r` THEN SET_TAC[];
    UNDISCH_TAC `(r':real^2->bool) SUBSET R'` THEN UNDISCH_TAC `(x':real^2) IN r'` THEN
    SET_TAC[]]);;

let MOI_LGB1_GP_CLAUSE2 = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a d0 b.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     moi_lgb1_sml tt u h h' kk L g a d0 /\
     (!P. P IN moi_lgb1_c2 (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                           (IMAGE (IMAGE h) (moi_lgb1_th tt kk))
          ==> b P IN relative_interior P)
     ==> !r s. r IN moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                                 (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) b /\
               aff_dim r = &2 /\ s IN tt /\ aff_dim s <= &2 /\
               IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a) r SUBSET s
               ==> IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a) r INTER
                   (Q UNION kk) = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `d0:real`; `b:(real^2->bool)->real^2`]
    MOI_LGB1_CUT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "inL") (LABEL_TAC "cases")))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `d0:real`] MOI_LGB1_CUTSETUP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`r:real^2->bool`; `s:real^N->bool`] THEN STRIP_TAC THEN
  USE_THEN "cases" (MP_TAC o SPEC `r:real^2->bool`) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  STRIP_TAC THENL
   [SUBGOAL_THEN `r INTER moi_lgb1_kv L (g:real^2->real^N) kk = {}` ASSUME_TAC THENL
     [UNDISCH_TAC `~(r IN moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk))` THEN
      REWRITE_TAC[moi_lgb1_lm; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk))
                    g h' a) r = IMAGE g r` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!s (f:real^2->real^N) g. (!x. x IN s ==> f x = g x) ==> IMAGE f s = IMAGE g s`) THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_LGB1_GP_UNMOVED THEN
      MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                            `u:real^N->bool`; `h:real^N->real^3`; `Q:real^N->bool`;
                            `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                            `r:real^2->bool`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `!y. y IN IMAGE (g:real^2->real^N) r ==> ~(y IN kk)` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `g:real^2->real^N`; `kk:real^N->bool`;
                     `r:real^2->bool`; `y:real^N`] MOI_LGB1_NO_KK) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `L:(real^2->bool)->bool`; `g:real^2->real^N`;
                   `Q:real^N->bool`] MOI_LGB1_TGEN_CLAUSES) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`r:real^2->bool`; `s:real^N->bool`] o CONJUNCT1 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `!y. y IN IMAGE (g:real^2->real^N) r ==> ~(y IN kk)` THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN
  SUBGOAL_THEN `?x:real^2. x IN r` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN DISCH_TAC THEN
    UNDISCH_TAC `aff_dim (r:real^2->bool) = &2` THEN ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(r:real^2->bool) SUBSET r'` ASSUME_TAC THENL
   [UNDISCH_TAC `r SUBSET moi_lgb1_cell (a:real^2->real^3) r' s'` THEN
    MP_TAC(ISPECL [`a:real^2->real^3`; `r':real^2->bool`; `s':real^3->bool`]
      MOI_LGB1_CELL_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN r ==> (y:real^2) IN UNIONS (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `r':real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(r:real^2->bool) SUBSET r'` THEN
    UNDISCH_TAC `(y:real^2) IN r` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `d0:real`; `x:real^2`] MOI_LGB1_GP_MOVED_FACTS) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
  SUBGOAL_THEN `s IN moi_lgb1_t3 (tt:(real^N->bool)->bool) kk` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lgb1_sml tt u (h:real^N->real^3) h' kk L (g:real^2->real^N) a d0` THEN
    REWRITE_TAC[moi_lgb1_sml] THEN
    DISCH_THEN(MP_TAC o SPECL [`r':real^2->bool`; `x:real^2`;
      `(h':real^3->real^N) (a (x:real^2))`; `s:real^N->bool`] o CONJUNCT2) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [UNDISCH_TAC `(r:real^2->bool) SUBSET r'` THEN
                    UNDISCH_TAC `(x:real^2) IN r` THEN SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk))
                   g h' a) r SUBSET s` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `s IN moi_lgb1_th (tt:(real^N->bool)->bool) kk` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:real^N->bool`] MOI_LGB1_TH_SUBSET) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `s:real^N->bool`] MOI_LGB1_TH_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `lh:real^N->real^3` (X_CHOOSE_THEN `yh:real^3`
       STRIP_ASSUME_TAC)) ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)`;
                 `a:real^2->real^3`; `IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)`;
                 `r':real^2->bool`] MOI_LGB1_SETUP_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_THEN `l1:real^2->real^3`
      (X_CHOOSE_THEN `y1:real^3` STRIP_ASSUME_TAC)) ASSUME_TAC)))) THEN
  SUBGOAL_THEN `IMAGE (a:real^2->real^3) r SUBSET IMAGE (h:real^N->real^3) s` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                   `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                   `a:real^2->real^3`; `d0:real`; `y:real^2`] MOI_LGB1_GP_MOVED_FACTS) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (K ALL_TAC))))) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN
    UNDISCH_TAC `IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk))
                   g h' a) r SUBSET s` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN(MP_TAC o SPEC `y:real^2`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (IMAGE (h:real^N->real^3) s) <= &2` ASSUME_TAC THENL
   [SUBGOAL_THEN `aff_dim (IMAGE (h:real^N->real^3) s) = aff_dim s` SUBST1_TAC THENL
     [MATCH_MP_TAC MOI_LGB1_AFF_DIM_INJ THEN
      MAP_EVERY EXISTS_TAC [`lh:real^N->real^3`; `yh:real^3`] THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (IMAGE (a:real^2->real^3) r) = &2` ASSUME_TAC THENL
   [SUBGOAL_THEN `aff_dim (IMAGE (a:real^2->real^3) r) = aff_dim r` SUBST1_TAC THENL
     [MATCH_MP_TAC MOI_LGB1_AFF_DIM_INJ THEN
      MAP_EVERY EXISTS_TAC [`l1:real^2->real^3`; `y1:real^3`] THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
        UNDISCH_TAC `(r:real^2->bool) SUBSET r'` THEN ASM SET_TAC[];
        UNDISCH_TAC `(r:real^2->bool) SUBSET r'` THEN ASM SET_TAC[]];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (IMAGE (a:real^2->real^3) r') <= &2` ASSUME_TAC THENL
   [SUBGOAL_THEN `aff_dim (IMAGE (a:real^2->real^3) r') = aff_dim r'` SUBST1_TAC THENL
     [MATCH_MP_TAC MOI_LGB1_AFF_DIM_INJ THEN
      MAP_EVERY EXISTS_TAC [`l1:real^2->real^3`; `y1:real^3`] THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPEC `r':real^2->bool` AFF_DIM_LE_UNIV) THEN REWRITE_TAC[DIMINDEX_2]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `r':real^2->bool`; `IMAGE (h:real^N->real^3) s`]
    MOI_LGB1_IN_WALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_LGB1_LM_L3 THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `r' IN moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)` THEN
      REWRITE_TAC[moi_lgb1_lm; IN_ELIM_THM] THEN SIMP_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `affine hull (IMAGE (a:real^2->real^3) r')` THEN
      REWRITE_TAC[HULL_SUBSET] THEN
      SUBGOAL_THEN `affine hull (IMAGE (a:real^2->real^3) r) = affine hull (IMAGE a r')`
        (SUBST1_TAC o SYM) THENL
       [MATCH_MP_TAC AFF_DIM_EQ_AFFINE_HULL THEN ASM_SIMP_TAC[IMAGE_SUBSET];
        MATCH_MP_TAC HULL_MONO THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`r:real^2->bool`; `r':real^2->bool`] AFF_DIM_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `aff_dim (r':real^2->bool) <= &1` THEN INT_ARITH_TAC);;

let MOI_LGB1_LINE_MEET = prove
 (`!(Fl:real^N->bool) M z.
     aff_dim Fl = &1 /\ affine M /\ z IN affine hull Fl /\ z IN M /\
     ~(affine hull Fl SUBSET M)
     ==> affine hull Fl INTER M = {z}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^N) IN affine hull Fl INTER M` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (affine hull Fl INTER M:real^N->bool) < aff_dim (Fl:real^N->bool)`
  MP_TAC THENL
   [MATCH_MP_TAC AFF_DIM_PSUBSET THEN
    SUBGOAL_THEN `affine hull (affine hull Fl INTER M:real^N->bool) = affine hull Fl INTER M`
    SUBST1_TAC THENL
     [REWRITE_TAC[AFFINE_HULL_EQ] THEN MATCH_MP_TAC AFFINE_INTER THEN
      ASM_REWRITE_TAC[AFFINE_AFFINE_HULL];
      REWRITE_TAC[PSUBSET; INTER_SUBSET] THEN
      UNDISCH_TAC `~(affine hull Fl SUBSET (M:real^N->bool))` THEN SET_TAC[]];
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  SUBGOAL_THEN `aff_dim (affine hull Fl INTER M:real^N->bool) = &0` MP_TAC THENL
   [REWRITE_TAC[GSYM INT_LE_ANTISYM] THEN CONJ_TAC THENL
     [UNDISCH_TAC `aff_dim (affine hull Fl INTER M:real^N->bool) < &1` THEN INT_ARITH_TAC;
      REWRITE_TAC[AFF_DIM_POS_LE; GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `z:real^N` THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[AFF_DIM_EQ_0] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^N` ASSUME_TAC) THEN
  UNDISCH_TAC `(z:real^N) IN affine hull Fl INTER M` THEN
  ASM_REWRITE_TAC[IN_SING] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let MOI_LGB1_RELINT_A = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a R x.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     R IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\ x IN relative_interior R
     ==> x IN R /\ a x IN relative_interior (IMAGE a R)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  CONJ_TAC THENL
   [MP_TAC(ISPEC `R:real^2->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(x:real^2) IN relative_interior R` THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_lgb1_mvd tt (h:real^N->real^3) kk L (g:real^2->real^N) hs phi rk a` THEN
  REWRITE_TAC[moi_lgb1_mvd; moi_lgb1_interp] THEN
  DISCH_THEN(MP_TAC o SPEC `R:real^2->bool` o CONJUNCT1 o CONJUNCT1 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^2->real^3` (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`a:real^2->real^3`; `l:real^2->real^3`; `y:real^3`; `R:real^2->bool`]
    MOI_LGB1_RELINT_AFFINE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `g:real^2->real^N`;
                   `moi_lgb1_th (tt:(real^N->bool)->bool) kk`] MOI_LGB1_L3_SC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]);;

let MOI_LGB1_PW5_MOVED = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a d0
    x1 x2 R1 R2 s.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     moi_lgb1_sml tt u h h' kk L g a d0 /\ moi_lgb1_sm2 tt h kk L g Q a d0 /\
     R1 IN L /\ x1 IN relative_interior R1 /\ ~(R1 INTER moi_lgb1_kv L g kk = {}) /\
     R2 IN L /\ x2 IN relative_interior R2 /\ ~(x1 = x2) /\
     moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a x1 =
     moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a x2 /\
     moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a x1 IN Q UNION kk /\
     s IN tt /\ aff_dim s <= &1 /\
     moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a x1 IN s
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  SUBGOAL_THEN `(x1:real^2) IN R1 /\ (x2:real^2) IN R2` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `R1:real^2->bool` RELATIVE_INTERIOR_SUBSET) THEN
    MP_TAC(ISPEC `R2:real^2->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(x1:real^2) IN relative_interior R1` THEN
    UNDISCH_TAC `(x2:real^2) IN relative_interior R2` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `d0:real`; `x1:real^2`; `x2:real^2`;
                 `R1:real^2->bool`; `R2:real^2->bool`] MOI_LGB1_PW_MOVED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "ax12")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "gpx1")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "mg1")))))))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `R2:real^2->bool`; `x2:real^2`] MOI_LGB1_RELINT_A) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "ax12" (fun th -> REWRITE_TAC[SYM th]) THEN STRIP_TAC THEN
  SUBGOAL_THEN `(h':real^3->real^N) (a (x1:real^2)) IN s` ASSUME_TAC THENL
   [REMOVE_THEN "gpx1" (SUBST1_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `R2 INTER moi_lgb1_kv L (g:real^2->real^N) kk = {}` THENL
   [SUBGOAL_THEN `moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)) g h' a x2 =
                  g x2` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_LGB1_GP_UNMOVED THEN
      MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                            `u:real^N->bool`; `h:real^N->real^3`; `Q:real^N->bool`;
                            `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                            `R2:real^2->bool`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(h':real^3->real^N) (a (x1:real^2)) = (g:real^2->real^N) x2` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                     `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                     `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                     `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                     `a:real^2->real^3`; `R1:real^2->bool`; `x1:real^2`] MOI_LGB1_GP_L3) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      TRANS_TAC EQ_TRANS
        `moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)) g h' a x2` THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(g:real^2->real^N) x2 IN Q` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `g:real^2->real^N`; `kk:real^N->bool`;
                     `R2:real^2->bool`; `(g:real^2->real^N) x2`] MOI_LGB1_NO_KK) THEN
      ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
      UNDISCH_TAC `moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)) g h' a x1
                   IN Q UNION kk` THEN
      REWRITE_TAC[ASSUME `moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk))
                            g h' a x1 = moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a x2`;
                  ASSUME `moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk))
                            g h' a x2 = g x2`; IN_UNION] THEN
      CONV_TAC TAUT;
      ALL_TAC] THEN
    UNDISCH_TAC `moi_lgb1_sm2 tt (h:real^N->real^3) kk L (g:real^2->real^N) Q a d0` THEN
    REWRITE_TAC[moi_lgb1_sm2] THEN
    DISCH_THEN(MP_TAC o SPECL [`R1:real^2->bool`; `R2:real^2->bool`; `x1:real^2`;
                               `(g:real^2->real^N) x2`] o last o CONJUNCTS) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FUN_IN_IMAGE] THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(h':real^3->real^N) (a (x1:real^2)) IN s` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `dist((h':real^3->real^N) (a (x1:real^2)),g x1) < d0` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`(g:real^2->real^N) x1`; `(g:real^2->real^N) x2`] DIST_SYM) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `s IN moi_lgb1_th (tt:(real^N->bool)->bool) kk` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:real^N->bool`] MOI_LGB1_TH_SUBSET) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    USE_THEN "mg1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `s:real^N->bool`] MOI_LGB1_TH_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `lh:real^N->real^3` (X_CHOOSE_THEN `yh:real^3`
       STRIP_ASSUME_TAC)) ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`] MOI_LGB1_H_SC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `(a:real^2->real^3) x1 IN IMAGE (h:real^N->real^3) s` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP (SPEC `(a:real^2->real^3) x1`
      (ASSUME `!z. z IN IMAGE (h:real^N->real^3) u ==> h ((h':real^3->real^N) z) = z /\
                                                       h' z IN u`))
      (ASSUME `(a:real^2->real^3) x1 IN IMAGE (h:real^N->real^3) u`)) THEN
    DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)`;
                 `(a:real^2->real^3) x1`] MOI_LGB1_CARRIER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `IMAGE (h:real^N->real^3) s` THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Fz:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fmin")))) THEN
  SUBGOAL_THEN `aff_dim (Fz:real^3->bool) <= &1` ASSUME_TAC THENL
   [TRANS_TAC INT_LE_TRANS `aff_dim (IMAGE (h:real^N->real^3) s)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC AFF_DIM_SUBSET THEN MATCH_MP_TAC FACE_OF_IMP_SUBSET THEN
      USE_THEN "fmin" MATCH_MP_TAC THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
      ALL_TAC] THEN
    SUBGOAL_THEN `aff_dim (IMAGE (h:real^N->real^3) s) = aff_dim s` SUBST1_TAC THENL
     [MATCH_MP_TAC MOI_LGB1_AFF_DIM_INJ THEN
      MAP_EVERY EXISTS_TAC [`lh:real^N->real^3`; `yh:real^3`] THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `R1:real^2->bool`; `x1:real^2`] MOI_LGB1_RELINT_A) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_CASES_TAC `aff_dim (Fz:real^3->bool) <= &0` THENL
   [SUBGOAL_THEN `Fz = {(a:real^2->real^3) x1}` ASSUME_TAC THENL
     [SUBGOAL_THEN `aff_dim (Fz:real^3->bool) = &0` MP_TAC THENL
       [REWRITE_TAC[GSYM INT_LE_ANTISYM] THEN ASM_REWRITE_TAC[AFF_DIM_POS_LE] THEN
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(a:real^2->real^3) x1` THEN
        MP_TAC(ISPEC `Fz:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
        UNDISCH_TAC `(a:real^2->real^3) x1 IN relative_interior Fz` THEN SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[AFF_DIM_EQ_0] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^3` SUBST_ALL_TAC) THEN
      UNDISCH_TAC `(a:real^2->real^3) x1 IN relative_interior {w}` THEN
      REWRITE_TAC[RELATIVE_INTERIOR_SING; IN_SING] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                   `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                   `a:real^2->real^3`; `R1:real^2->bool`; `(a:real^2->real^3) x1`]
      MOI_LGB1_NO_HVERTEX) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(Fz:real^3->bool) IN IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (Fz:real^3->bool) = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `~(aff_dim (Fz:real^3->bool) <= &0)` THEN
    UNDISCH_TAC `aff_dim (Fz:real^3->bool) <= &1` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_lgb1_mvd]) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `R1:real^2->bool`; `R2:real^2->bool`;
                 `Fz:real^3->bool`; `(a:real^2->real^3) x1`] MOI_LGB1_INV_FULL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)) g h' a x1
                 IN Q UNION kk` THEN
    USE_THEN "gpx1" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "inv") THEN
  SUBGOAL_THEN `(a:real^2->real^3) x1 IN Fz` ASSUME_TAC THENL
   [MP_TAC(ISPEC `Fz:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(a:real^2->real^3) x1 IN relative_interior Fz` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^2->real^3) x1 IN IMAGE a R1 /\ a x1 IN IMAGE a R2` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `IMAGE (a:real^2->real^3) R2` RELATIVE_INTERIOR_SUBSET) THEN
    MP_TAC(ISPEC `IMAGE (a:real^2->real^3) R1` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(a:real^2->real^3) x1 IN relative_interior (IMAGE a R1)` THEN
    UNDISCH_TAC `(a:real^2->real^3) x1 IN relative_interior (IMAGE a R2)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `affine hull Fz INTER affine hull (IMAGE (a:real^2->real^3) R1) = {a x1}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LGB1_LINE_MEET THEN
    ASM_SIMP_TAC[AFFINE_AFFINE_HULL; HULL_INC] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                     `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                     `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                     `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                     `a:real^2->real^3`; `R1:real^2->bool`; `Fz:real^3->bool`;
                     `(a:real^2->real^3) x1`] MOI_LGB1_HEDGE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `affine hull Fz INTER affine hull (IMAGE (a:real^2->real^3) R2) = {a x1}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LGB1_LINE_MEET THEN
    ASM_SIMP_TAC[AFFINE_AFFINE_HULL; HULL_INC] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                     `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                     `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                     `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                     `a:real^2->real^3`; `R2:real^2->bool`; `Fz:real^3->bool`;
                     `(a:real^2->real^3) x1`] MOI_LGB1_HEDGE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (Fz:real^3->bool) <= &0` MP_TAC THENL
   [ALL_TAC;
    UNDISCH_TAC `aff_dim (Fz:real^3->bool) = &1` THEN INT_ARITH_TAC] THEN
  ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
  USE_THEN "inv" (SUBST1_TAC o SYM) THEN
  REWRITE_TAC[AFF_DIM_AFFINE_HULL] THEN
  TRANS_TAC INT_LE_TRANS `aff_dim {(a:real^2->real^3) x1}` THEN CONJ_TAC THENL
   [MATCH_MP_TAC AFF_DIM_SUBSET;
    REWRITE_TAC[AFF_DIM_SING; INT_LE_REFL]] THEN
  MP_TAC(ISPECL [`affine:(real^3->bool)->bool`; `Fz:real^3->bool`] HULL_SUBSET) THEN
  MP_TAC(ISPECL [`affine:(real^3->bool)->bool`; `IMAGE (a:real^2->real^3) R1`] HULL_SUBSET) THEN
  MP_TAC(ISPECL [`affine:(real^3->bool)->bool`; `IMAGE (a:real^2->real^3) R2`] HULL_SUBSET) THEN
  UNDISCH_TAC `affine hull Fz INTER affine hull (IMAGE (a:real^2->real^3) R1) = {a x1}` THEN
  UNDISCH_TAC `affine hull Fz INTER affine hull (IMAGE (a:real^2->real^3) R2) = {a x1}` THEN
  SET_TAC[]);;

let MOI_LGB1_PW5 = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a d0 x1 x2 s.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     moi_lgb1_sml tt u h h' kk L g a d0 /\ moi_lgb1_sm2 tt h kk L g Q a d0 /\
     x1 IN std_triangle /\ x2 IN std_triangle /\ ~(x1 = x2) /\
     moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a x1 =
     moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a x2 /\
     moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a x1 IN Q UNION kk /\
     s IN tt /\ aff_dim s <= &1 /\
     moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a x1 IN s
     ==> F`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "e12") STRIP_ASSUME_TAC)))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  SUBGOAL_THEN `moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)) g h' a x2
                IN Q UNION kk /\
                moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a x2 IN s`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)) g h' a x1
                 IN s` THEN
    UNDISCH_TAC `moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)) g h' a x1
                 IN Q UNION kk` THEN
    USE_THEN "e12" (fun th -> REWRITE_TAC[th]) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(x2:real^2 = x1)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(x1:real^2 = x2)` THEN MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `x1:real^2`] MOI_LGB1_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R1:real^2->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `x2:real^2`] MOI_LGB1_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R2:real^2->bool` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `R1 INTER moi_lgb1_kv L (g:real^2->real^N) kk = {}` THENL
   [ALL_TAC;
    MATCH_MP_TAC MOI_LGB1_PW5_MOVED THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                          `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                          `kk:real^N->bool`; `L:(real^2->bool)->bool`; `g:real^2->real^N`;
                          `Q:real^N->bool`; `hs:real^3->bool`; `phi:real^2->real^3`;
                          `rk:real^2->num`; `a:real^2->real^3`; `d0:real`;
                          `x1:real^2`; `x2:real^2`; `R1:real^2->bool`; `R2:real^2->bool`;
                          `s:real^N->bool`] THEN
    ASM_REWRITE_TAC[]] THEN
  ASM_CASES_TAC `R2 INTER moi_lgb1_kv L (g:real^2->real^N) kk = {}` THENL
   [ALL_TAC;
    MATCH_MP_TAC MOI_LGB1_PW5_MOVED THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                          `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                          `kk:real^N->bool`; `L:(real^2->bool)->bool`; `g:real^2->real^N`;
                          `Q:real^N->bool`; `hs:real^3->bool`; `phi:real^2->real^3`;
                          `rk:real^2->num`; `a:real^2->real^3`; `d0:real`;
                          `x2:real^2`; `x1:real^2`; `R2:real^2->bool`; `R1:real^2->bool`;
                          `s:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "e12" (fun th -> REWRITE_TAC[th])] THEN
  SUBGOAL_THEN `(x1:real^2) IN R1 /\ (x2:real^2) IN R2` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `R1:real^2->bool` RELATIVE_INTERIOR_SUBSET) THEN
    MP_TAC(ISPEC `R2:real^2->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(x1:real^2) IN relative_interior R1` THEN
    UNDISCH_TAC `(x2:real^2) IN relative_interior R2` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `x1:real^2`; `x2:real^2`;
                 `R1:real^2->bool`; `R2:real^2->bool`] MOI_LGB1_PW_UNMOVED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "g1") (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "g12") (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `L:(real^2->bool)->bool`; `g:real^2->real^N`;
                 `Q:real^N->bool`] MOI_LGB1_TGEN_CLAUSES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`R1:real^2->bool`; `R2:real^2->bool`; `s:real^N->bool`] o
    last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[DISJOINT; EXTENSION; NOT_IN_EMPTY; IN_INTER] THEN
  DISCH_THEN(MP_TAC o SPEC `(g:real^2->real^N) x1`) THEN
  MATCH_MP_TAC(TAUT `p ==> ~p ==> F`) THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
    USE_THEN "g12" SUBST1_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    USE_THEN "g1" (SUBST1_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC]);;

let MOI_LGB1_GP_CLAUSE5 = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a d0 b.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     moi_lgb1_sml tt u h h' kk L g a d0 /\ moi_lgb1_sm2 tt h kk L g Q a d0 /\
     (!P. P IN moi_lgb1_c2 (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                           (IMAGE (IMAGE h) (moi_lgb1_th tt kk))
          ==> b P IN relative_interior P)
     ==> !r r' s.
           r IN moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                             (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) b /\
           r' IN moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                              (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) b /\
           DISJOINT r r' /\ s IN tt /\ aff_dim s <= &1
           ==> DISJOINT
                 (IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a) r INTER
                  IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a) r' INTER
                  (Q UNION kk)) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `d0:real`; `b:(real^2->bool)->real^2`]
    MOI_LGB1_CUT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "un")
    (CONJUNCTS_THEN2 (LABEL_TAC "inL") (K ALL_TAC)))) THEN
  MAP_EVERY X_GEN_TAC [`r:real^2->bool`; `r':real^2->bool`; `s:real^N->bool`] THEN
  STRIP_TAC THEN
  REWRITE_TAC[DISJOINT; EXTENSION; NOT_IN_EMPTY; IN_INTER; IN_IMAGE] THEN
  X_GEN_TAC `y:real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (X_CHOOSE_THEN `x1:real^2` STRIP_ASSUME_TAC)
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `x2:real^2` STRIP_ASSUME_TAC) ASSUME_TAC)) ASSUME_TAC) THEN
  SUBGOAL_THEN `(x1:real^2) IN std_triangle /\ (x2:real^2) IN std_triangle`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "un" (SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_UNIONS] THEN
    CONJ_TAC THENL
     [EXISTS_TAC `r:real^2->bool`; EXISTS_TAC `r':real^2->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `d0:real`; `x2:real^2`; `x1:real^2`; `s:real^N->bool`]
    MOI_LGB1_PW5) THEN
  REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `y:real^N`)) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `DISJOINT (r:real^2->bool) r'` THEN UNDISCH_TAC `(x1:real^2) IN r` THEN
  UNDISCH_TAC `(x2:real^2) IN r'` THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* C17. Clause 4 of tgeneric for the moved map.  The pieces of the cut      *)
(* complex; cone pieces have their relative interiors inside the 2-cells,   *)
(* whose images have relative interiors in open 3-cells of the chart.       *)
(* ------------------------------------------------------------------------- *)

let MOI_LGB1_CUT_PIECES = prove
 (`!(L:(real^2->bool)->bool) mv (a:real^2->real^3) H b t.
     t IN moi_lgb1_cut L mv a H b
     ==> (t IN L /\ ~(t IN mv)) \/
         (?R S. R IN mv /\ S IN H /\ aff_dim (moi_lgb1_cell a R S) <= &1 /\
                t = moi_lgb1_cell a R S) \/
         (?P f. P IN moi_lgb1_c2 mv a H /\ f face_of P /\ ~(f = P) /\
                t = convex hull (b P INSERT f))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lgb1_cut; moi_lgb1_c2; IN_UNION; IN_ELIM_THM] THEN
  MESON_TAC[]);;

let MOI_LGB1_CONE_RELINT = prove
 (`!(P:real^M->bool) b f.
     polytope P /\ b IN relative_interior P /\ f face_of P /\ ~(f = P)
     ==> relative_interior (convex hull (b INSERT f)) SUBSET relative_interior P`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
  SUBGOAL_THEN `convex hull (b INSERT f) SUBSET (P:real^M->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX; INSERT_SUBSET] THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET; FACE_OF_IMP_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^M) IN P` ASSUME_TAC THENL
   [MP_TAC(ISPEC `convex hull ((b:real^M) INSERT f)` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(y:real^M) IN relative_interior (convex hull (b INSERT f))` THEN
    UNDISCH_TAC `convex hull (b INSERT f) SUBSET (P:real^M->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`P:real^M->bool`; `y:real^M`] IN_RELATIVE_INTERIOR_OF_FACE) THEN
  ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX] THEN
  DISCH_THEN(X_CHOOSE_THEN `F':real^M->bool` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `F':real^M->bool = P` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `convex hull (b INSERT f) SUBSET (F':real^M->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_OF_FACE_OF THEN EXISTS_TAC `P:real^M->bool` THEN
    ASM_REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `y:real^M` THEN
    ASM_REWRITE_TAC[IN_INTER] THEN ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`F':real^M->bool`; `P:real^M->bool`] FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`convex:(real^M->bool)->bool`; `(b:real^M) INSERT f`] HULL_SUBSET) THEN
  UNDISCH_TAC `convex hull (b INSERT f) SUBSET (F':real^M->bool)` THEN
  UNDISCH_TAC `(b:real^M) IN relative_interior P` THEN SET_TAC[]);;

let MOI_LGB1_C2_FACTS = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a d0 P.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     moi_lgb1_sml tt u h h' kk L g a d0 /\
     P IN moi_lgb1_c2 (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                      (IMAGE (IMAGE h) (moi_lgb1_th tt kk))
     ==> ?R S. R IN moi_lgb1_lm L (moi_lgb1_kv L g kk) /\
               R IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\
               S IN IMAGE (IMAGE h) (moi_lgb1_th tt kk) /\
               P = moi_lgb1_cell a R S /\ P SUBSET R /\
               aff_dim P = &2 /\ aff_dim R = &2 /\ aff_dim S = &3 /\
               polytope P /\ convex P /\
               relative_interior (IMAGE a P) SUBSET interior S /\
               relative_interior P SUBSET relative_interior R /\
               affine hull (IMAGE a P) = affine hull (IMAGE a R) /\
               IMAGE a P SUBSET S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `d0:real`; `P:real^2->bool`] MOI_LGB1_C2_CELL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MAP_EVERY ASSUME_TAC o (fun l -> [el 0 l; el 1 l; el 2 l]) o CONJUNCTS) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `d0:real`] MOI_LGB1_CUTSETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  UNDISCH_TAC `P IN moi_lgb1_c2 (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)) a
                   (IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk))` THEN
  REWRITE_TAC[moi_lgb1_c2; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real^2->bool` (X_CHOOSE_THEN `S:real^3->bool`
    (CONJUNCTS_THEN2 STRIP_ASSUME_TAC SUBST_ALL_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`R:real^2->bool`; `S:real^3->bool`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `R IN moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LGB1_LM_L3 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)`;
                 `a:real^2->real^3`; `IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)`;
                 `R:real^2->bool`] MOI_LGB1_SETUP_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_THEN `l:real^2->real^3`
      (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) (LABEL_TAC "rinj"))))) THEN
  SUBGOAL_THEN `moi_lgb1_cell (a:real^2->real^3) R S SUBSET R` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_LGB1_CELL_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (R:real^2->bool) = &2` ASSUME_TAC THENL
   [MP_TAC(ISPEC `R:real^2->bool` AFF_DIM_LE_UNIV) THEN
    MP_TAC(ISPECL [`moi_lgb1_cell (a:real^2->real^3) R S`; `R:real^2->bool`] AFF_DIM_SUBSET) THEN
    ASM_REWRITE_TAC[DIMINDEX_2] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (a:real^2->real^3) (moi_lgb1_cell a R S) SUBSET S` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_LGB1_CELL_IMAGE; INTER_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN moi_lgb1_cell (a:real^2->real^3) R S ==> a x = l x + y`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_lgb1_cell; IN_ELIM_THM] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (IMAGE (a:real^2->real^3) (moi_lgb1_cell a R S)) = &2 /\
                aff_dim (IMAGE (a:real^2->real^3) R) = &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `aff_dim (moi_lgb1_cell (a:real^2->real^3) R S)` THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
      MATCH_MP_TAC MOI_LGB1_AFF_DIM_INJ THEN
      MAP_EVERY EXISTS_TAC [`l:real^2->real^3`; `y:real^3`] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[moi_lgb1_cell; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      USE_THEN "rinj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `aff_dim (R:real^2->bool)` THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
      MATCH_MP_TAC MOI_LGB1_AFF_DIM_INJ THEN
      MAP_EVERY EXISTS_TAC [`l:real^2->real^3`; `y:real^3`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `affine hull (IMAGE (a:real^2->real^3) (moi_lgb1_cell a R S)) =
                affine hull (IMAGE a R)` ASSUME_TAC THENL
   [MATCH_MP_TAC AFF_DIM_EQ_AFFINE_HULL THEN
    ASM_SIMP_TAC[IMAGE_SUBSET; INT_LE_REFL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!W. W IN IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk) /\
                    aff_dim W <= &2 /\
                    IMAGE (a:real^2->real^3) (moi_lgb1_cell a R S) SUBSET affine hull W
                    ==> F` (LABEL_TAC "nowall") THENL
   [X_GEN_TAC `W:real^3->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                   `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                   `a:real^2->real^3`; `R:real^2->bool`; `W:real^3->bool`] MOI_LGB1_IN_WALL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `R IN moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)` THEN
        REWRITE_TAC[moi_lgb1_lm; IN_ELIM_THM] THEN SIMP_TAC[];
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `affine hull (IMAGE (a:real^2->real^3) R)` THEN
        REWRITE_TAC[HULL_SUBSET] THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          concl th = `affine hull (IMAGE (a:real^2->real^3) (moi_lgb1_cell a R S)) =
                      affine hull (IMAGE a R)`)) THEN
        MATCH_MP_TAC HULL_MINIMAL THEN ASM_REWRITE_TAC[AFFINE_AFFINE_HULL]];
      STRIP_TAC THEN UNDISCH_TAC `aff_dim (R:real^2->bool) <= &1` THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (S:real^3->bool) = &3` ASSUME_TAC THENL
   [MP_TAC(ISPEC `S:real^3->bool` AFF_DIM_LE_UNIV) THEN REWRITE_TAC[DIMINDEX_3] THEN
    MATCH_MP_TAC(INT_ARITH `~(x:int <= &2) ==> x <= &3 ==> x = &3`) THEN DISCH_TAC THEN
    USE_THEN "nowall" MATCH_MP_TAC THEN EXISTS_TAC `S:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `S:real^3->bool` THEN
    ASM_REWRITE_TAC[HULL_SUBSET];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SUBSET_RELATIVE_INTERIOR THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC AFF_DIM_EQ_AFFINE_HULL THEN ASM_REWRITE_TAC[INT_LE_REFL]] THEN
  SUBGOAL_THEN `interior S = relative_interior (S:real^3->bool)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RELATIVE_INTERIOR_INTERIOR THEN
    REWRITE_TAC[GSYM AFF_DIM_EQ_FULL; DIMINDEX_3] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex (S:real^3->bool) /\ simplicial_complex
                  (IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk))` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`] MOI_LGB1_H_SC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(w:real^3) IN S` ASSUME_TAC THENL
   [MP_TAC(ISPEC `IMAGE (a:real^2->real^3) (moi_lgb1_cell a R S)` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `IMAGE (a:real^2->real^3) (moi_lgb1_cell a R S) SUBSET S` THEN
    UNDISCH_TAC `(w:real^3) IN relative_interior (IMAGE (a:real^2->real^3) (moi_lgb1_cell a R S))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `w:real^3`] IN_RELATIVE_INTERIOR_OF_FACE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `F':real^3->bool` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `F':real^3->bool = S` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  USE_THEN "nowall" (MP_TAC o SPEC `F':real^3->bool`) THEN REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `simplicial_complex (IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk))` THEN
    REWRITE_TAC[simplicial_complex] THEN ASM_MESON_TAC[];
    MP_TAC(ISPECL [`F':real^3->bool`; `S:real^3->bool`] FACE_OF_AFF_DIM_LT) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `F':real^3->bool` THEN
    REWRITE_TAC[HULL_SUBSET] THEN MATCH_MP_TAC SUBSET_OF_FACE_OF THEN
    EXISTS_TAC `S:real^3->bool` THEN ASM_REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `w:real^3` THEN ASM_REWRITE_TAC[IN_INTER] THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]]);;

(* Abstract cone point and cone edge arguments in the chart.                *)

let MOI_LGB1_PK_T = prove
 (`!X0 (Y:real^3->bool) p RP B.
     (!Y'. Y' SUBSET X0 /\ ~(affine hull RP SUBSET affine hull Y')
           ==> ~(p IN affine hull Y')) /\
     Y SUBSET X0 /\ affine hull Y = affine hull B /\
     affine hull (RP UNION B) = (:real^3) /\ p IN B /\ aff_dim B <= &2
     ==> F`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "good") STRIP_ASSUME_TAC) THEN
  USE_THEN "good" (MP_TAC o SPEC `Y:real^3->bool`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `affine hull (RP UNION B) SUBSET affine hull (B:real^3->bool)` MP_TAC THENL
     [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[AFFINE_AFFINE_HULL; UNION_SUBSET] THEN
      REWRITE_TAC[HULL_SUBSET] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `affine hull (RP:real^3->bool)` THEN ASM_REWRITE_TAC[HULL_SUBSET];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[SUBSET_UNIV; UNIV_SUBSET] THEN DISCH_TAC THEN
    MP_TAC(ISPEC `B:real^3->bool` AFF_DIM_AFFINE_HULL) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[AFF_DIM_UNIV; DIMINDEX_3] THEN
    UNDISCH_TAC `aff_dim (B:real^3->bool) <= &2` THEN INT_ARITH_TAC;
    ASM_SIMP_TAC[HULL_INC]]);;

let MOI_LGB1_EK_T = prove
 (`!X0 (Y:real^3->bool) p w z A A' B RP.
     (!Y'. Y' SUBSET X0 /\ ~(affine hull RP SUBSET affine hull Y')
           ==> ~(p IN affine hull Y')) /\
     Y SUBSET X0 /\ w IN X0 /\ affine hull Y = affine hull B /\
     affine hull (RP UNION B) = (:real^3) /\
     z IN B /\ z IN segment(p,w) /\
     p IN affine hull A /\ w IN affine hull A /\ affine hull B SUBSET affine hull A'
     ==> affine hull (A UNION A') = (:real^3)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "good") STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `affine hull ((w:real^3) INSERT Y) SUBSET affine hull (A UNION A')`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[AFFINE_AFFINE_HULL; INSERT_SUBSET] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`affine:(real^3->bool)->bool`; `A:real^3->bool`;
                     `A UNION A':real^3->bool`] HULL_MONO) THEN
      REWRITE_TAC[SUBSET_UNION] THEN ASM SET_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `affine hull (A':real^3->bool)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `affine hull (Y:real^3->bool)` THEN
        ASM_REWRITE_TAC[HULL_SUBSET];
        MATCH_MP_TAC HULL_MONO THEN REWRITE_TAC[SUBSET_UNION]]];
    ALL_TAC] THEN
  ASM_CASES_TAC `affine hull RP SUBSET affine hull ((w:real^3) INSERT Y)` THENL
   [REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET_UNIV] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `affine hull (RP UNION B) = (:real^3)`)) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `affine hull ((w:real^3) INSERT Y)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[AFFINE_AFFINE_HULL; UNION_SUBSET] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `affine hull (RP:real^3->bool)` THEN
      ASM_REWRITE_TAC[HULL_SUBSET];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `affine hull (B:real^3->bool)` THEN
      REWRITE_TAC[HULL_SUBSET] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `affine hull Y = affine hull (B:real^3->bool)`)) THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[]];
    ALL_TAC] THEN
  USE_THEN "good" (MP_TAC o SPEC `(w:real^3) INSERT Y`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[INSERT_SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `q ==> ~q ==> r`) THEN
  SUBGOAL_THEN `(p:real^3) IN affine hull {z,w}` MP_TAC THENL
   [UNDISCH_TAC `(z:real^3) IN segment(p,w)` THEN REWRITE_TAC[IN_SEGMENT] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)) THEN
    MATCH_MP_TAC MOI_LGB1_SEG_BACK THEN EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `!s t (x:real^3). s SUBSET t ==> x IN s ==> x IN t`) THEN
  MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[AFFINE_AFFINE_HULL; INSERT_SUBSET; EMPTY_SUBSET] THEN
  SIMP_TAC[HULL_INC; IN_INSERT] THEN
  MATCH_MP_TAC(SET_RULE `!s t (x:real^3). s SUBSET t /\ x IN s ==> x IN t`) THEN
  EXISTS_TAC `affine hull (Y:real^3->bool)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC HULL_MONO THEN SET_TAC[]; ASM_SIMP_TAC[HULL_INC]]);;

let MOI_LGB1_CARRIER_UNIQUE = prove
 (`!(K:(real^M->bool)->bool) A B.
     simplicial_complex K /\ A IN K /\ B IN K /\
     ~(relative_interior A INTER relative_interior B = {})
     ==> A = B`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_complex]) THEN
  SUBGOAL_THEN `(A INTER B:real^M->bool) face_of A /\ (A INTER B) face_of B`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(A:real^M->bool) SUBSET A INTER B /\ (B:real^M->bool) SUBSET A INTER B`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_OF_FACE_OF THENL
     [EXISTS_TAC `A:real^M->bool`; EXISTS_TAC `B:real^M->bool`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN
    UNDISCH_TAC `~(relative_interior A INTER relative_interior B:real^M->bool = {})` THEN
    MP_TAC(ISPEC `A:real^M->bool` RELATIVE_INTERIOR_SUBSET) THEN
    MP_TAC(ISPEC `B:real^M->bool` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[];
    SET_TAC[]]);;

let MOI_LGB1_FULLSPAN = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a R1 R2 S z.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     R1 IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\ R2 IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\
     DISJOINT R1 R2 /\ S IN IMAGE (IMAGE h) (moi_lgb1_th tt kk) /\ aff_dim S = &3 /\
     z IN relative_interior (IMAGE a R1) /\ z IN relative_interior (IMAGE a R2) /\
     z IN interior S /\ h' z IN Q UNION kk
     ==> affine hull (IMAGE a R1 UNION IMAGE a R2) = (:real^3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_lgb1_mvd]) THEN
  SUBGOAL_THEN `affine hull (S:real^3->bool) = (:real^3)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM AFF_DIM_EQ_FULL; DIMINDEX_3] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `R1:real^2->bool`; `R2:real^2->bool`;
                 `S:real^3->bool`; `z:real^3`] MOI_LGB1_INV_FULL) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[RELATIVE_INTERIOR_INTERIOR]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`affine:(real^3->bool)->bool`;
                 `(IMAGE (a:real^2->real^3) R1 INTER S) UNION (IMAGE a R2 INTER S)`;
                 `IMAGE (a:real^2->real^3) R1 UNION IMAGE a R2`] HULL_MONO) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [SET_TAC[]; SET_TAC[]]);;

let MOI_LGB1_CARRIER_SUBSET = prove
 (`!(K:(real^M->bool)->bool) A B x.
     simplicial_complex K /\ A IN K /\ B IN K /\ x IN relative_interior A /\ x IN B
     ==> A SUBSET B`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_complex]) THEN
  SUBGOAL_THEN `(A INTER B:real^M->bool) face_of A` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(A:real^M->bool) SUBSET A INTER B` MP_TAC THENL
   [MATCH_MP_TAC SUBSET_OF_FACE_OF THEN EXISTS_TAC `A:real^M->bool` THEN
    ASM_REWRITE_TAC[SUBSET_REFL; DISJOINT; GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `x:real^M` THEN ASM_REWRITE_TAC[IN_INTER] THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    SET_TAC[]]);;

let moi_lgb1_cones = new_definition
 `moi_lgb1_cones (tt:(real^N->bool)->bool) (h:real^N->real^3) kk L (g:real^2->real^N)
                 (phi:real^2->real^3) a b <=>
    (!P. P IN moi_lgb1_c2 (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                          (IMAGE (IMAGE h) (moi_lgb1_th tt kk))
         ==> b P IN relative_interior P) /\
    (!P Y. P IN moi_lgb1_c2 (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                            (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) /\
           Y SUBSET moi_lgb1_xc phi {v | {v} IN moi_lgb1_l3 L g (moi_lgb1_th tt kk)}
             ({z | {z} IN IMAGE (IMAGE h) (moi_lgb1_th tt kk)} UNION
              {a w | w | ?P'. P' IN moi_lgb1_c2 (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                                                (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) /\
                              w extreme_point_of P'}) /\
           ~(affine hull (IMAGE a P) SUBSET affine hull Y)
           ==> ~(a (b P) IN affine hull Y)) /\
    (!P P' w w'. P IN moi_lgb1_c2 (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                                  (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) /\
                 P' IN moi_lgb1_c2 (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                                   (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) /\
                 ~(affine hull (IMAGE a P) = affine hull (IMAGE a P')) /\
                 w extreme_point_of P /\ w' extreme_point_of P'
                 ==> DISJOINT (IMAGE a (segment(b P,w))) (IMAGE a (segment(b P',w'))))`;;

let MOI_LGB1_CONES_FROM = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a d0.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     moi_lgb1_sml tt u h h' kk L g a d0
     ==> ?b. moi_lgb1_cones tt h kk L g phi a b`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[moi_lgb1_cones] THEN
  FIRST_ASSUM(ACCEPT_TAC o MATCH_MP MOI_LGB1_CONES_EXIST));;

let MOI_LGB1_PIECE_CONE = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a d0 b P f x Rx.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     moi_lgb1_sml tt u h h' kk L g a d0 /\ moi_lgb1_cones tt h kk L g phi a b /\
     P IN moi_lgb1_c2 (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                      (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) /\
     f face_of P /\ ~(f = P) /\
     x IN relative_interior (convex hull (b P INSERT f)) /\
     Rx IN L /\ x IN relative_interior Rx
     ==> (!Fz. Fz IN IMAGE (IMAGE h) (moi_lgb1_th tt kk) /\ a x IN relative_interior Fz
               ==> IMAGE a Rx INTER Fz SUBSET affine hull (IMAGE a (convex hull (b P INSERT f)))) \/
         (?S. S IN IMAGE (IMAGE h) (moi_lgb1_th tt kk) /\ aff_dim S = &3 /\
              a x IN interior S /\
              affine hull (IMAGE a P) = affine hull (IMAGE a Rx) /\
              P SUBSET Rx /\ Rx IN moi_lgb1_lm L (moi_lgb1_kv L g kk) /\
              ((convex hull (b P INSERT f) = {b P} /\ x = b P) \/
               (?w. w extreme_point_of P /\ convex hull (b P INSERT f) = convex hull {b P, w} /\
                    ~(b P = w) /\ x IN segment(b P,w))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  SUBGOAL_THEN `(b:(real^2->bool)->real^2) P IN relative_interior P` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lgb1_cones tt (h:real^N->real^3) kk L (g:real^2->real^N) phi a b` THEN
    REWRITE_TAC[moi_lgb1_cones] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `d0:real`; `P:real^2->bool`] MOI_LGB1_C2_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real^2->bool` (X_CHOOSE_THEN `S:real^3->bool`
    (MAP_EVERY ASSUME_TAC o
     filter (fun th -> not (is_eq (concl th) && is_var (lhs (concl th)))) o CONJUNCTS))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `d0:real`] MOI_LGB1_CUTSETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)`;
                 `a:real^2->real^3`; `IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)`;
                 `R:real^2->bool`] MOI_LGB1_SETUP_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_THEN `l:real^2->real^3`
      (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) (LABEL_TAC "rinj"))))) THEN
  SUBGOAL_THEN `(x:real^2) IN relative_interior P` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`P:real^2->bool`; `(b:(real^2->bool)->real^2) P`; `f:real^2->bool`]
      MOI_LGB1_CONE_RELINT) THEN
    ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `Rx:real^2->bool = R` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC MOI_LGB1_CARRIER_UNIQUE THEN EXISTS_TAC `L:(real^2->bool)->bool` THEN
    ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `x:real^2` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `relative_interior P SUBSET relative_interior (R:real^2->bool)` THEN
    UNDISCH_TAC `(x:real^2) IN relative_interior P` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN P ==> (a:real^2->real^3) z = l z + y` ASSUME_TAC THENL
   [UNDISCH_TAC `P SUBSET (R:real^2->bool)` THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^2->real^3) x IN interior S` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!s t (z:real^3). s SUBSET t /\ z IN s ==> z IN t`) THEN
    EXISTS_TAC `relative_interior (IMAGE (a:real^2->real^3) P)` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`a:real^2->real^3`; `l:real^2->real^3`; `y:real^3`; `P:real^2->bool`]
      MOI_LGB1_RELINT_AFFINE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (f:real^2->bool) <= &1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real^2->bool`; `P:real^2->bool`] FACE_OF_AFF_DIM_LT) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~((b:(real^2->bool)->real^2) P IN affine hull f)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`P:real^2->bool`; `f:real^2->bool`]
      AFFINE_HULL_FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(b:(real^2->bool)->real^2) P IN relative_interior P` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `aff_dim (f:real^2->bool) = &1` THENL
   [DISJ1_TAC THEN
    SUBGOAL_THEN `convex hull ((b:(real^2->bool)->real^2) P INSERT f) SUBSET P` ASSUME_TAC THENL
     [MATCH_MP_TAC HULL_MINIMAL THEN ASM_REWRITE_TAC[INSERT_SUBSET] THEN
      ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET; FACE_OF_IMP_SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN `affine hull (IMAGE (a:real^2->real^3)
                    (convex hull ((b:(real^2->bool)->real^2) P INSERT f))) =
                  affine hull (IMAGE a R)` ASSUME_TAC THENL
     [MATCH_MP_TAC AFF_DIM_EQ_AFFINE_HULL THEN CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `aff_dim (IMAGE (a:real^2->real^3) R) = aff_dim R /\
                    aff_dim (IMAGE (a:real^2->real^3)
                      (convex hull ((b:(real^2->bool)->real^2) P INSERT f))) =
                    aff_dim (convex hull (b P INSERT f))` (CONJUNCTS_THEN SUBST1_TAC) THENL
       [CONJ_TAC THEN MATCH_MP_TAC MOI_LGB1_AFF_DIM_INJ THEN
        MAP_EVERY EXISTS_TAC [`l:real^2->real^3`; `y:real^3`] THEN
        ASM_REWRITE_TAC[CONVEX_CONVEX_HULL] THEN ASM SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_INSERT] THEN ASM_REWRITE_TAC[] THEN
      INT_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `Fz:real^3->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (a:real^2->real^3) R` THEN
    REWRITE_TAC[INTER_SUBSET; HULL_SUBSET];
    ALL_TAC] THEN
  DISJ2_TAC THEN EXISTS_TAC `S:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `f:real^2->bool = {}` THENL
   [DISJ1_TAC THEN UNDISCH_TAC `(x:real^2) IN relative_interior
                     (convex hull ((b:(real^2->bool)->real^2) P INSERT f))` THEN
    ASM_REWRITE_TAC[CONVEX_HULL_SING; RELATIVE_INTERIOR_SING; IN_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (f:real^2->bool) = &0` MP_TAC THENL
   [MP_TAC(ISPEC `f:real^2->bool` AFF_DIM_POS_LE) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `aff_dim (f:real^2->bool) <= &1` THEN
    UNDISCH_TAC `~(aff_dim (f:real^2->bool) = &1)` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[AFF_DIM_EQ_0] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^2` SUBST_ALL_TAC) THEN
  DISJ2_TAC THEN EXISTS_TAC `w:real^2` THEN
  UNDISCH_TAC `{w:real^2} face_of P` THEN REWRITE_TAC[FACE_OF_SING] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~((b:(real^2->bool)->real^2) P = w)` ASSUME_TAC THENL
   [UNDISCH_TAC `~((b:(real^2->bool)->real^2) P IN affine hull {w})` THEN
    REWRITE_TAC[AFFINE_HULL_SING; IN_SING];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(x:real^2) IN relative_interior
                 (convex hull {(b:(real^2->bool)->real^2) P, w})` THEN
  ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; RELATIVE_INTERIOR_SEGMENT]);;

let MOI_LGB1_PIECE_TYPE = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a d0 b rho x Rx.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     moi_lgb1_sml tt u h h' kk L g a d0 /\ moi_lgb1_cones tt h kk L g phi a b /\
     rho IN moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                         (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) b /\
     x IN relative_interior rho /\ Rx IN L /\ x IN relative_interior Rx
     ==> (!Fz. Fz IN IMAGE (IMAGE h) (moi_lgb1_th tt kk) /\ a x IN relative_interior Fz
               ==> IMAGE a Rx INTER Fz SUBSET affine hull (IMAGE a rho)) \/
         (?P S. P IN moi_lgb1_c2 (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                                 (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) /\
                S IN IMAGE (IMAGE h) (moi_lgb1_th tt kk) /\ aff_dim S = &3 /\
                a x IN interior S /\
                affine hull (IMAGE a P) = affine hull (IMAGE a Rx) /\
                P SUBSET Rx /\ Rx IN moi_lgb1_lm L (moi_lgb1_kv L g kk) /\
                ((rho = {b P} /\ x = b P) \/
                 (?w. w extreme_point_of P /\ rho = convex hull {b P, w} /\
                      ~(b P = w) /\ x IN segment(b P,w))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  SUBGOAL_THEN `(x:real^2) IN rho /\ (x:real^2) IN Rx` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `rho:real^2->bool` RELATIVE_INTERIOR_SUBSET) THEN
    MP_TAC(ISPEC `Rx:real^2->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(x:real^2) IN relative_interior rho` THEN
    UNDISCH_TAC `(x:real^2) IN relative_interior Rx` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)`;
                 `a:real^2->real^3`; `IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)`;
                 `b:(real^2->bool)->real^2`; `rho:real^2->bool`] MOI_LGB1_CUT_PIECES) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  STRIP_TAC THENL
   [DISJ1_TAC THEN
    SUBGOAL_THEN `rho:real^2->bool = Rx` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC MOI_LGB1_CARRIER_UNIQUE THEN EXISTS_TAC `L:(real^2->bool)->bool` THEN
      ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `x:real^2` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (a:real^2->real^3) Rx` THEN REWRITE_TAC[INTER_SUBSET; HULL_SUBSET];
    DISJ1_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    X_GEN_TAC `Fz:real^3->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (a:real^2->real^3) (moi_lgb1_cell a R S)` THEN
    REWRITE_TAC[HULL_SUBSET; MOI_LGB1_CELL_IMAGE] THEN
    SUBGOAL_THEN `(Rx:real^2->bool) SUBSET R` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_LGB1_CARRIER_SUBSET THEN
      MAP_EVERY EXISTS_TAC [`L:(real^2->bool)->bool`; `x:real^2`] THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `R IN moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)` THEN
        REWRITE_TAC[moi_lgb1_lm; IN_ELIM_THM] THEN SIMP_TAC[];
        MP_TAC(ISPECL [`a:real^2->real^3`; `R:real^2->bool`; `S:real^3->bool`]
          MOI_LGB1_CELL_SUBSET) THEN
        UNDISCH_TAC `(x:real^2) IN moi_lgb1_cell (a:real^2->real^3) R S` THEN SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(Fz:real^3->bool) SUBSET S` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_LGB1_CARRIER_SUBSET THEN
      MAP_EVERY EXISTS_TAC [`IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)`;
                            `(a:real^2->real^3) x`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_LGB1_H_SC THEN
        MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `u:real^N->bool`;
                              `h':real^3->real^N`] THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `(x:real^2) IN moi_lgb1_cell (a:real^2->real^3) R S` THEN
        REWRITE_TAC[moi_lgb1_cell; IN_ELIM_THM] THEN SIMP_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `(Rx:real^2->bool) SUBSET R` THEN UNDISCH_TAC `(Fz:real^3->bool) SUBSET S` THEN
    SET_TAC[];
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                   `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                   `a:real^2->real^3`; `d0:real`; `b:(real^2->bool)->real^2`;
                   `P:real^2->bool`; `f:real^2->bool`; `x:real^2`; `Rx:real^2->bool`]
      MOI_LGB1_PIECE_CONE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_OR THEN REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `S:real^3->bool` (fun th ->
      MAP_EVERY EXISTS_TAC [`P:real^2->bool`; `S:real^3->bool`] THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ACCEPT_TAC th]))]);;

(* The point set of the cone point genericity and its members.             *)

let moi_lgb1_x0 = new_definition
 `moi_lgb1_x0 (tt:(real^N->bool)->bool) (h:real^N->real^3) kk L (g:real^2->real^N)
              (phi:real^2->real^3) a =
    moi_lgb1_xc phi {v | {v} IN moi_lgb1_l3 L g (moi_lgb1_th tt kk)}
      ({z | {z} IN IMAGE (IMAGE h) (moi_lgb1_th tt kk)} UNION
       {a w | w | ?P'. P' IN moi_lgb1_c2 (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                                         (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) /\
                       w extreme_point_of P'})`;;

let MOI_LGB1_CONES_GOOD = prove
 (`!(tt:(real^N->bool)->bool) h kk L (g:real^2->real^N) phi a b P.
     moi_lgb1_cones tt h kk L g phi a b /\
     P IN moi_lgb1_c2 (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                      (IMAGE (IMAGE h) (moi_lgb1_th tt kk))
     ==> b P IN relative_interior P /\
         !Y. Y SUBSET moi_lgb1_x0 tt h kk L g phi a /\
             ~(affine hull (IMAGE a P) SUBSET affine hull Y)
             ==> ~(a (b P) IN affine hull Y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lgb1_cones; moi_lgb1_x0] THEN STRIP_TAC THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[]; REPEAT STRIP_TAC THEN ASM_MESON_TAC[]]);;

let MOI_LGB1_VERTS_X0 = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a R.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     R IN moi_lgb1_l3 L g (moi_lgb1_th tt kk)
     ==> IMAGE phi {v | v extreme_point_of R} SUBSET moi_lgb1_x0 tt h kk L g phi a /\
         affine hull (IMAGE phi {v | v extreme_point_of R}) = affine hull (IMAGE a R) /\
         aff_dim (IMAGE a R) <= &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `g:real^2->real^N`;
                 `moi_lgb1_th (tt:(real^N->bool)->bool) kk`] MOI_LGB1_L3_SC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_lgb1_interp (moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)) phi a`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lgb1_mvd tt (h:real^N->real^3) kk L (g:real^2->real^N) hs phi rk a` THEN
    REWRITE_TAC[moi_lgb1_mvd] THEN STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)`; `R:real^2->bool`]
      MOI_LGB1_VERTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; moi_lgb1_x0; moi_lgb1_xc] THEN
    DISCH_TAC THEN X_GEN_TAC `v:real^2` THEN DISCH_TAC THEN
    REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN DISJ1_TAC THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)`; `phi:real^2->real^3`;
                   `a:real^2->real^3`; `R:real^2->bool`] MOI_LGB1_INTERP_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[AFFINE_HULL_CONVEX_HULL];
    UNDISCH_TAC `moi_lgb1_interp (moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)) phi a` THEN
    REWRITE_TAC[moi_lgb1_interp] THEN
    DISCH_THEN(MP_TAC o SPEC `R:real^2->bool` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `l:real^2->real^3` (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) THEN
    TRANS_TAC INT_LE_TRANS `aff_dim (R:real^2->bool)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_LGB1_AFF_DIM_AFFINE_LE THEN
      MAP_EVERY EXISTS_TAC [`l:real^2->real^3`; `y:real^3`] THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPEC `R:real^2->bool` AFF_DIM_LE_UNIV) THEN REWRITE_TAC[DIMINDEX_2]]]);;

let MOI_LGB1_CV_X0 = prove
 (`!(tt:(real^N->bool)->bool) h kk L (g:real^2->real^N) phi (a:real^2->real^3) P w.
     P IN moi_lgb1_c2 (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                      (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) /\
     w extreme_point_of P
     ==> a w IN moi_lgb1_x0 tt h kk L g phi a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_lgb1_x0; moi_lgb1_xc; IN_UNION] THEN
  DISJ1_TAC THEN DISJ2_TAC THEN DISJ2_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
  EXISTS_TAC `w:real^2` THEN REWRITE_TAC[] THEN EXISTS_TAC `P:real^2->bool` THEN
  ASM_REWRITE_TAC[]);;

let MOI_LGB1_SEG_IMAGE = prove
 (`!(a:real^2->real^3) l y P p q x.
     linear l /\ (!z. z IN P ==> a z = l z + y) /\ convex P /\ p IN P /\ q IN P /\
     ~(a p = a q) /\ x IN segment(p,q)
     ==> a x IN segment(a p,a q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(x:real^2) IN segment(p,q)` THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_LGB1_AFFINE_COMB THEN
  MAP_EVERY EXISTS_TAC [`l:real^2->real^3`; `y:real^3`; `P:real^2->bool`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IN_CONVEX_SET THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

let MOI_LGB1_CONE_POINT_F = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a b P S Rx Rx' x'.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     moi_lgb1_cones tt h kk L g phi a b /\
     P IN moi_lgb1_c2 (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                      (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) /\
     S IN IMAGE (IMAGE h) (moi_lgb1_th tt kk) /\ aff_dim S = &3 /\ a (b P) IN interior S /\
     affine hull (IMAGE a P) = affine hull (IMAGE a Rx) /\
     Rx IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\ b P IN relative_interior Rx /\
     Rx' IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\ x' IN relative_interior Rx' /\
     DISJOINT Rx Rx' /\ a x' = a (b P) /\ h' (a (b P)) IN Q UNION kk
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `Rx:real^2->bool`; `(b:(real^2->bool)->real^2) P`]
    MOI_LGB1_RELINT_A) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `Rx':real^2->bool`; `x':real^2`] MOI_LGB1_RELINT_A) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `Rx:real^2->bool`; `Rx':real^2->bool`; `S:real^3->bool`;
                 `(a:real^2->real^3) (b (P:real^2->bool))`] MOI_LGB1_FULLSPAN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(a:real^2->real^3) x' IN relative_interior (IMAGE a Rx')` THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `h:real^N->real^3`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `phi:real^2->real^3`;
                 `a:real^2->real^3`; `b:(real^2->bool)->real^2`; `P:real^2->bool`]
    MOI_LGB1_CONES_GOOD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "good" o CONJUNCT2)] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `Rx':real^2->bool`] MOI_LGB1_VERTS_X0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MATCH_MP_TAC MOI_LGB1_PK_T THEN
  MAP_EVERY EXISTS_TAC [`moi_lgb1_x0 tt (h:real^N->real^3) kk L (g:real^2->real^N) phi a`;
                        `IMAGE (phi:real^2->real^3) {v | v extreme_point_of Rx'}`;
                        `(a:real^2->real^3) (b (P:real^2->bool))`;
                        `IMAGE (a:real^2->real^3) P`; `IMAGE (a:real^2->real^3) Rx'`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[HULL_UNION_LEFT] THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[GSYM HULL_UNION_LEFT] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x':real^2` THEN ASM_REWRITE_TAC[]]);;

let MOI_LGB1_EDGE_EDGE = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a b P P' S
    Rx Rx' x x' w w'.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     moi_lgb1_cones tt h kk L g phi a b /\
     P IN moi_lgb1_c2 (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                      (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) /\
     P' IN moi_lgb1_c2 (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                       (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) /\
     S IN IMAGE (IMAGE h) (moi_lgb1_th tt kk) /\ aff_dim S = &3 /\ a x IN interior S /\
     affine hull (IMAGE a P) = affine hull (IMAGE a Rx) /\
     affine hull (IMAGE a P') = affine hull (IMAGE a Rx') /\
     Rx IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\ x IN relative_interior Rx /\
     Rx' IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\ x' IN relative_interior Rx' /\
     DISJOINT Rx Rx' /\ a x' = a x /\ h' (a x) IN Q UNION kk /\
     w extreme_point_of P /\ x IN segment(b P,w) /\
     w' extreme_point_of P' /\ x' IN segment(b P',w')
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `affine hull (IMAGE (a:real^2->real^3) P) = affine hull (IMAGE a P')` THENL
   [ALL_TAC;
    UNDISCH_TAC `moi_lgb1_cones tt (h:real^N->real^3) kk L (g:real^2->real^N) phi a b` THEN
    REWRITE_TAC[moi_lgb1_cones] THEN
    DISCH_THEN(MP_TAC o SPECL [`P:real^2->bool`; `P':real^2->bool`; `w:real^2`; `w':real^2`] o
      last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[DISJOINT; EXTENSION; NOT_IN_EMPTY; IN_INTER] THEN
    DISCH_THEN(MP_TAC o SPEC `(a:real^2->real^3) x`) THEN REWRITE_TAC[IN_IMAGE] THEN
    CONJ_TAC THENL
     [EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `x':real^2` THEN ASM_REWRITE_TAC[]]] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `Rx:real^2->bool`; `x:real^2`] MOI_LGB1_RELINT_A) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `Rx':real^2->bool`; `x':real^2`] MOI_LGB1_RELINT_A) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `Rx:real^2->bool`; `Rx':real^2->bool`; `S:real^3->bool`;
                 `(a:real^2->real^3) x`] MOI_LGB1_FULLSPAN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(a:real^2->real^3) x' IN relative_interior (IMAGE a Rx')` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `affine hull (IMAGE (a:real^2->real^3) Rx UNION IMAGE a Rx') =
                affine hull (IMAGE a Rx)` SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[HULL_UNION_RIGHT] THEN
    SUBGOAL_THEN `affine hull (IMAGE (a:real^2->real^3) Rx') = affine hull (IMAGE a Rx)`
    SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM HULL_UNION_RIGHT; UNION_IDEMPOT];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `Rx:real^2->bool`] MOI_LGB1_VERTS_X0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPEC `IMAGE (a:real^2->real^3) Rx` AFF_DIM_AFFINE_HULL) THEN
  ASM_REWRITE_TAC[AFF_DIM_UNIV; DIMINDEX_3] THEN
  UNDISCH_TAC `aff_dim (IMAGE (a:real^2->real^3) Rx) <= &2` THEN INT_ARITH_TAC);;

let MOI_LGB1_CONE_EDGE_T = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a d0 b P S
    Rx Rx' x x' w rho'.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     moi_lgb1_sml tt u h h' kk L g a d0 /\ moi_lgb1_cones tt h kk L g phi a b /\
     P IN moi_lgb1_c2 (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                      (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) /\
     S IN IMAGE (IMAGE h) (moi_lgb1_th tt kk) /\ aff_dim S = &3 /\ a x IN interior S /\
     affine hull (IMAGE a P) = affine hull (IMAGE a Rx) /\ P SUBSET Rx /\
     Rx IN moi_lgb1_lm L (moi_lgb1_kv L g kk) /\
     Rx IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\ x IN relative_interior Rx /\
     w extreme_point_of P /\ ~(b P = w) /\ x IN segment(b P,w) /\
     Rx' IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\ x' IN relative_interior Rx' /\
     DISJOINT Rx Rx' /\ a x' = a x /\ h' (a x) IN Q UNION kk /\
     IMAGE a Rx' INTER S SUBSET affine hull (IMAGE a rho')
     ==> affine hull (IMAGE a (convex hull {b P, w}) UNION IMAGE a rho') = (:real^3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `Rx:real^2->bool`; `x:real^2`] MOI_LGB1_RELINT_A) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `Rx':real^2->bool`; `x':real^2`] MOI_LGB1_RELINT_A) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `Rx:real^2->bool`; `Rx':real^2->bool`; `S:real^3->bool`;
                 `(a:real^2->real^3) x`] MOI_LGB1_FULLSPAN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(a:real^2->real^3) x' IN relative_interior (IMAGE a Rx')` THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN `affine hull (IMAGE (a:real^2->real^3) P UNION IMAGE a Rx') = (:real^3)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `affine hull (IMAGE (a:real^2->real^3) Rx UNION IMAGE a Rx') = (:real^3)`)) THEN
    ONCE_REWRITE_TAC[HULL_UNION_LEFT] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `affine hull (S:real^3->bool) = (:real^3)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM AFF_DIM_EQ_FULL; DIMINDEX_3] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_lgb1_interp (moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)) phi a`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lgb1_mvd tt (h:real^N->real^3) kk L (g:real^2->real^N) hs phi rk a` THEN
    REWRITE_TAC[moi_lgb1_mvd] THEN STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `g:real^2->real^N`;
                 `moi_lgb1_th (tt:(real^N->bool)->bool) kk`] MOI_LGB1_L3_SC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `affine hull (IMAGE (a:real^2->real^3) Rx') SUBSET
                affine hull (IMAGE a rho')` ASSUME_TAC THENL
   [SUBGOAL_THEN `affine hull (IMAGE (a:real^2->real^3) Rx' INTER S) =
                  affine hull (IMAGE a Rx')` (SUBST1_TAC o SYM) THENL
     [MP_TAC(ISPECL [`IMAGE (a:real^2->real^3) Rx'`; `S:real^3->bool`]
        MOI_LGB1_AFF_INTER_RELINT) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [MP_TAC(ISPECL [`moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)`;
                         `phi:real^2->real^3`; `a:real^2->real^3`; `Rx':real^2->bool`]
            MOI_LGB1_INTERP_IMAGE) THEN
          ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CONVEX_CONVEX_HULL];
          MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                         `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`]
            MOI_LGB1_H_SC) THEN
          ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
          ASM_SIMP_TAC[RELATIVE_INTERIOR_INTERIOR; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
          EXISTS_TAC `(a:real^2->real^3) x` THEN ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `(a:real^2->real^3) x' IN relative_interior (IMAGE a Rx')` THEN
          ASM_REWRITE_TAC[]];
        ASM_REWRITE_TAC[INTER_UNIV]];
      MATCH_MP_TAC HULL_MINIMAL THEN ASM_REWRITE_TAC[AFFINE_AFFINE_HULL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)`;
                 `a:real^2->real^3`; `IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)`;
                 `Rx:real^2->bool`] MOI_LGB1_SETUP_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_LGB1_CUTSETUP THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `u:real^N->bool`; `h':real^3->real^N`;
                          `Q:real^N->bool`; `hs:real^3->bool`; `phi:real^2->real^3`;
                          `rk:real^2->num`; `d0:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_THEN `l:real^2->real^3`
      (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) (LABEL_TAC "rinj"))))) THEN
  SUBGOAL_THEN `convex (P:real^2->bool) /\ (b:(real^2->bool)->real^2) P IN P /\ w IN P`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                     `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                     `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                     `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                     `a:real^2->real^3`; `d0:real`; `P:real^2->bool`] MOI_LGB1_C2_CELL) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `h:real^N->real^3`; `kk:real^N->bool`;
                     `L:(real^2->bool)->bool`; `g:real^2->real^N`; `phi:real^2->real^3`;
                     `a:real^2->real^3`; `b:(real^2->bool)->real^2`; `P:real^2->bool`]
        MOI_LGB1_CONES_GOOD) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPEC `P:real^2->bool` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[];
      ASM_MESON_TAC[extreme_point_of]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN P ==> (a:real^2->real^3) z = l z + y` ASSUME_TAC THENL
   [UNDISCH_TAC `P SUBSET (Rx:real^2->bool)` THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~((a:real^2->real^3) (b (P:real^2->bool)) = a w)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~((b:(real^2->bool)->real^2) P = w)` THEN REWRITE_TAC[] THEN
    USE_THEN "rinj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `P SUBSET (Rx:real^2->bool)` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^2->real^3`; `l:real^2->real^3`; `y:real^3`; `P:real^2->bool`;
                 `(b:(real^2->bool)->real^2) P`; `w:real^2`; `x:real^2`] MOI_LGB1_SEG_IMAGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `h:real^N->real^3`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `phi:real^2->real^3`;
                 `a:real^2->real^3`; `b:(real^2->bool)->real^2`; `P:real^2->bool`]
    MOI_LGB1_CONES_GOOD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "good" o CONJUNCT2)] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `Rx':real^2->bool`] MOI_LGB1_VERTS_X0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `h:real^N->real^3`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `phi:real^2->real^3`;
                 `a:real^2->real^3`; `P:real^2->bool`; `w:real^2`] MOI_LGB1_CV_X0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MATCH_MP_TAC MOI_LGB1_EK_T THEN
  MAP_EVERY EXISTS_TAC [`moi_lgb1_x0 tt (h:real^N->real^3) kk L (g:real^2->real^N) phi a`;
                        `IMAGE (phi:real^2->real^3) {v | v extreme_point_of Rx'}`;
                        `(a:real^2->real^3) (b (P:real^2->bool))`; `(a:real^2->real^3) w`;
                        `(a:real^2->real^3) x`; `IMAGE (a:real^2->real^3) Rx'`;
                        `IMAGE (a:real^2->real^3) P`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x':real^2` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC HULL_INC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
    MATCH_MP_TAC HULL_INC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]]);;

(* The double points of the moved map at Q UNION kk in the chart: the        *)
(* L'-carriers of the two preimages span the affine hull of the chart       *)
(* carrier of the image point.                                              *)

let moi_lgb1_kdata_tac pv sv wv =
  X_CHOOSE_THEN pv (X_CHOOSE_THEN sv
    (fun th -> let cs = CONJUNCTS th in
               MAP_EVERY ASSUME_TAC (butlast cs) THEN
               DISJ_CASES_THEN2 (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC)
                 (X_CHOOSE_THEN wv (CONJUNCTS_THEN2 ASSUME_TAC
                    (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC)))
                 (last cs)));;

let MOI_LGB1_KEY4 = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a d0 b
    rho rho' x x' Rx Rx' Fz z.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     moi_lgb1_sml tt u h h' kk L g a d0 /\ moi_lgb1_cones tt h kk L g phi a b /\
     rho IN moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                         (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) b /\
     rho' IN moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                          (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) b /\
     x IN relative_interior rho /\ x' IN relative_interior rho' /\
     Rx IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\ x IN relative_interior Rx /\
     Rx' IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\ x' IN relative_interior Rx' /\
     DISJOINT Rx Rx' /\ a x = z /\ a x' = z /\ h' z IN Q UNION kk /\
     Fz IN IMAGE (IMAGE h) (moi_lgb1_th tt kk) /\ z IN relative_interior Fz
     ==> affine hull Fz SUBSET affine hull (IMAGE a rho UNION IMAGE a rho')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_lgb1_mvd]) THEN
  SUBGOAL_THEN `(Rx:real^2->bool) IN L /\ (Rx':real^2->bool) IN L` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `g:real^2->real^N`;
                   `moi_lgb1_th (tt:(real^N->bool)->bool) kk`] MOI_LGB1_L3_SC) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (Rx':real^2->bool) Rx` ASSUME_TAC THENL
   [ASM_MESON_TAC[DISJOINT_SYM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `Rx:real^2->bool`; `x:real^2`] MOI_LGB1_RELINT_A) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `Rx':real^2->bool`; `x':real^2`] MOI_LGB1_RELINT_A) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `d0:real`; `b:(real^2->bool)->real^2`;
                 `rho':real^2->bool`; `x':real^2`; `Rx':real^2->bool`] MOI_LGB1_PIECE_TYPE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `d0:real`; `b:(real^2->bool)->real^2`;
                 `rho:real^2->bool`; `x:real^2`; `Rx:real^2->bool`] MOI_LGB1_PIECE_TYPE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (LABEL_TAC "T1") (LABEL_TAC "K1")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (LABEL_TAC "T2") (LABEL_TAC "K2")) THENL
   [(* T T *)
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                   `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                   `a:real^2->real^3`; `Rx:real^2->bool`; `Rx':real^2->bool`;
                   `Fz:real^3->bool`; `z:real^3`] MOI_LGB1_INV_FULL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `affine hull ((IMAGE (a:real^2->real^3) Rx INTER Fz) UNION
                             (IMAGE a Rx' INTER Fz))` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[SUBSET_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[AFFINE_AFFINE_HULL; UNION_SUBSET] THEN
    CONJ_TAC THEN MATCH_MP_TAC SUBSET_TRANS THENL
     [EXISTS_TAC `affine hull (IMAGE (a:real^2->real^3) rho)` THEN CONJ_TAC THENL
       [USE_THEN "T1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC HULL_MONO THEN SET_TAC[]];
      EXISTS_TAC `affine hull (IMAGE (a:real^2->real^3) rho')` THEN CONJ_TAC THENL
       [USE_THEN "T2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC HULL_MONO THEN SET_TAC[]]];
    (* T K *)
    REMOVE_THEN "K2" (moi_lgb1_kdata_tac `P':real^2->bool` `S':real^3->bool` `w':real^2`) THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                     `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                     `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                     `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                     `a:real^2->real^3`; `b:(real^2->bool)->real^2`; `P':real^2->bool`;
                     `S':real^3->bool`; `Rx':real^2->bool`; `Rx:real^2->bool`; `x:real^2`]
        MOI_LGB1_CONE_POINT_F) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      SUBGOAL_THEN `IMAGE (a:real^2->real^3) Rx INTER S' SUBSET affine hull (IMAGE a rho)`
      ASSUME_TAC THENL
       [USE_THEN "T1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(SET_RULE `!s t (y:real^3). s = t /\ y IN t ==> y IN s`) THEN
        EXISTS_TAC `interior S':real^3->bool` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC RELATIVE_INTERIOR_INTERIOR THEN
        REWRITE_TAC[GSYM AFF_DIM_EQ_FULL; DIMINDEX_3] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                     `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                     `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                     `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                     `a:real^2->real^3`; `d0:real`; `b:(real^2->bool)->real^2`;
                     `P':real^2->bool`; `S':real^3->bool`; `Rx':real^2->bool`;
                     `Rx:real^2->bool`; `x':real^2`; `x:real^2`; `w':real^2`;
                     `rho:real^2->bool`] MOI_LGB1_CONE_EDGE_T) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[ONCE_REWRITE_RULE[UNION_COMM] th; SUBSET_UNIV])];
    (* K T *)
    REMOVE_THEN "K1" (moi_lgb1_kdata_tac `P:real^2->bool` `S:real^3->bool` `w:real^2`) THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                     `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                     `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                     `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                     `a:real^2->real^3`; `b:(real^2->bool)->real^2`; `P:real^2->bool`;
                     `S:real^3->bool`; `Rx:real^2->bool`; `Rx':real^2->bool`; `x':real^2`]
        MOI_LGB1_CONE_POINT_F) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      SUBGOAL_THEN `IMAGE (a:real^2->real^3) Rx' INTER S SUBSET affine hull (IMAGE a rho')`
      ASSUME_TAC THENL
       [USE_THEN "T2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(SET_RULE `!s t (y:real^3). s = t /\ y IN t ==> y IN s`) THEN
        EXISTS_TAC `interior S:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC RELATIVE_INTERIOR_INTERIOR THEN
        REWRITE_TAC[GSYM AFF_DIM_EQ_FULL; DIMINDEX_3] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                     `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                     `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                     `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                     `a:real^2->real^3`; `d0:real`; `b:(real^2->bool)->real^2`;
                     `P:real^2->bool`; `S:real^3->bool`; `Rx:real^2->bool`;
                     `Rx':real^2->bool`; `x:real^2`; `x':real^2`; `w:real^2`;
                     `rho':real^2->bool`] MOI_LGB1_CONE_EDGE_T) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[SUBSET_UNIV]];
    (* K K *)
    REMOVE_THEN "K1" (moi_lgb1_kdata_tac `P:real^2->bool` `S:real^3->bool` `w:real^2`) THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                     `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                     `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                     `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                     `a:real^2->real^3`; `b:(real^2->bool)->real^2`; `P:real^2->bool`;
                     `S:real^3->bool`; `Rx:real^2->bool`; `Rx':real^2->bool`; `x':real^2`]
        MOI_LGB1_CONE_POINT_F) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      ALL_TAC] THEN
    REMOVE_THEN "K2" (moi_lgb1_kdata_tac `P':real^2->bool` `S':real^3->bool` `w':real^2`) THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                     `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                     `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                     `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                     `a:real^2->real^3`; `b:(real^2->bool)->real^2`; `P':real^2->bool`;
                     `S':real^3->bool`; `Rx':real^2->bool`; `Rx:real^2->bool`; `x:real^2`]
        MOI_LGB1_CONE_POINT_F) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                     `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                     `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                     `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                     `a:real^2->real^3`; `b:(real^2->bool)->real^2`; `P:real^2->bool`;
                     `P':real^2->bool`; `S:real^3->bool`; `Rx:real^2->bool`;
                     `Rx':real^2->bool`; `x:real^2`; `x':real^2`; `w:real^2`; `w':real^2`]
        MOI_LGB1_EDGE_EDGE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]]]);;

let MOI_LGB1_C4_FROM_SPAN = prove
 (`!(G:real^N->bool) G' s y.
     y IN G /\ y IN G' /\ affine hull (G UNION G') = affine hull s
     ==> aff_dim s <= aff_dim G + aff_dim G' /\
         aff_dim (affine hull G INTER affine hull G') =
         aff_dim G + aff_dim G' - aff_dim s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:real^N->bool`; `G':real^N->bool`] MOI_FGP_AFF_DIM_HULLS_UNION) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `y:real^N` THEN
    ASM_SIMP_TAC[HULL_INC];
    DISCH_TAC] THEN
  SUBGOAL_THEN `aff_dim (G UNION G':real^N->bool) = aff_dim (s:real^N->bool)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= aff_dim (affine hull G INTER affine hull (G':real^N->bool))` MP_TAC THENL
   [REWRITE_TAC[AFF_DIM_POS_LE; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `y:real^N` THEN ASM_SIMP_TAC[HULL_INC];
    ALL_TAC] THEN
  UNDISCH_TAC `aff_dim (G UNION G':real^N->bool) = aff_dim (s:real^N->bool)` THEN
  UNDISCH_TAC `aff_dim (G UNION G':real^N->bool) =
               (aff_dim G + aff_dim G') - aff_dim (affine hull G INTER affine hull G')` THEN
  INT_ARITH_TAC);;

let MOI_LGB1_FACE_HULL_INTER = prove
 (`!(s:real^N->bool) t. convex s /\ t face_of s ==> s INTER affine hull t = t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `p:real^N` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`; `{p:real^N}`]
      SUBSET_OF_FACE_OF_AFFINE_HULL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[SING_SUBSET; RELATIVE_INTERIOR_SING] THEN
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_SING; NOT_IN_EMPTY] THEN
      ASM_MESON_TAC[];
      REWRITE_TAC[SING_SUBSET]];
    ASM_SIMP_TAC[SUBSET_INTER; HULL_SUBSET; FACE_OF_IMP_SUBSET]]);;

let MOI_LGB1_CORE4 = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a d0 b
    r r' x x' R1 R2 S z.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     moi_lgb1_sml tt u h h' kk L g a d0 /\ moi_lgb1_sm2 tt h kk L g Q a d0 /\
     moi_lgb1_cones tt h kk L g phi a b /\
     r IN moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                       (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) b /\
     r' IN moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                        (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) b /\
     x IN r /\ x' IN r' /\ ~(x = x') /\
     R1 IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\ r SUBSET R1 /\
     R2 IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\ r' SUBSET R2 /\
     a x = z /\ a x' = z /\
     moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a x = h' z /\
     moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a x' = h' z /\
     h' z IN Q UNION kk /\
     S IN IMAGE (IMAGE h) (moi_lgb1_th tt kk) /\ IMAGE a r UNION IMAGE a r' SUBSET S /\
     (!S'. S' IN IMAGE (IMAGE h) (moi_lgb1_th tt kk) /\ IMAGE a r UNION IMAGE a r' SUBSET S'
           ==> S SUBSET S')
     ==> affine hull (IMAGE a r UNION IMAGE a r') = affine hull S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `g:real^2->real^N`;
                 `moi_lgb1_th (tt:(real^N->bool)->bool) kk`] MOI_LGB1_L3_SC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`] MOI_LGB1_H_SC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `d0:real`; `b:(real^2->bool)->real^2`]
    MOI_LGB1_CUT_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_lgb1_cones tt (h:real^N->real^3) kk L (g:real^2->real^N) phi a b` THEN
    REWRITE_TAC[moi_lgb1_cones] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "un") (K ALL_TAC))) THEN
  SUBGOAL_THEN `(R1:real^2->bool) IN L /\ (R2:real^2->bool) IN L` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^2) IN std_triangle /\ (x':real^2) IN std_triangle` STRIP_ASSUME_TAC THENL
   [USE_THEN "un" (SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_UNIONS] THEN CONJ_TAC THENL
     [EXISTS_TAC `r:real^2->bool`; EXISTS_TAC `r':real^2->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `x:real^2`] MOI_LGB1_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Rx:real^2->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rxm")))) THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `x':real^2`] MOI_LGB1_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Rx':real^2->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rxm'")))) THEN
  SUBGOAL_THEN `Rx IN moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk) /\
                Rx' IN moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_complex (moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk))` THEN
    REWRITE_TAC[simplicial_complex] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN DISCH_TAC THEN
    CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THENL
     [EXISTS_TAC `R1:real^2->bool` THEN ASM_REWRITE_TAC[] THEN USE_THEN "rxm" MATCH_MP_TAC;
      EXISTS_TAC `R2:real^2->bool` THEN ASM_REWRITE_TAC[] THEN USE_THEN "rxm'" MATCH_MP_TAC] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^2) IN Rx /\ (x':real^2) IN Rx'` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `Rx:real^2->bool` RELATIVE_INTERIOR_SUBSET) THEN
    MP_TAC(ISPEC `Rx':real^2->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(x:real^2) IN relative_interior Rx` THEN
    UNDISCH_TAC `(x':real^2) IN relative_interior Rx'` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (Rx:real^2->bool) Rx'` ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT] THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    UNDISCH_TAC `~(x:real^2 = x')` THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                   `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                   `a:real^2->real^3`; `d0:real`; `Rx:real^2->bool`; `Rx':real^2->bool`;
                   `x:real^2`; `x':real^2`] MOI_LGB1_PW1) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)) a
                    (IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)) b`; `x:real^2`]
    MOI_LGB1_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real^2->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `r:real^2->bool`)))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)) a
                    (IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)) b`; `x':real^2`]
    MOI_LGB1_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho':real^2->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `r':real^2->bool`)))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:real^3) IN S` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (a:real^2->real^3) r UNION IMAGE a r' SUBSET S` THEN
    REWRITE_TAC[UNION_SUBSET; SUBSET; FORALL_IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^2` o CONJUNCT1) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)`; `z:real^3`]
    MOI_LGB1_CARRIER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `S:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Fz:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `S:real^3->bool`)))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `affine hull (Fz:real^3->bool) SUBSET
                affine hull (IMAGE (a:real^2->real^3) r UNION IMAGE a r')` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `affine hull (IMAGE (a:real^2->real^3) rho UNION IMAGE a rho')` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_LGB1_KEY4 THEN
      MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                            `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                            `kk:real^N->bool`; `L:(real^2->bool)->bool`;
                            `g:real^2->real^N`; `Q:real^N->bool`; `hs:real^3->bool`;
                            `phi:real^2->real^3`; `rk:real^2->num`; `d0:real`;
                            `b:(real^2->bool)->real^2`; `x:real^2`; `x':real^2`;
                            `Rx:real^2->bool`; `Rx':real^2->bool`; `z:real^3`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC HULL_MONO THEN
      MP_TAC(ISPECL [`r:real^2->bool`; `rho:real^2->bool`] FACE_OF_IMP_SUBSET) THEN
      MP_TAC(ISPECL [`r':real^2->bool`; `rho':real^2->bool`] FACE_OF_IMP_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 <= aff_dim (Fz:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC(INT_ARITH `~(x:int <= &1) ==> &2 <= x`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `Fz:real^3->bool`] MOI_LGB1_H_INV) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `f0:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "feq" o SYM) (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 (LABEL_TAC "finv") (K ALL_TAC)))))) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `f0:real^N->bool`] MOI_LGB1_TH_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `lh:real^N->real^3` (X_CHOOSE_THEN `yh:real^3`
         STRIP_ASSUME_TAC)) ASSUME_TAC))) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                   `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                   `a:real^2->real^3`; `d0:real`; `x:real^2`; `x':real^2`; `f0:real^N->bool`]
      MOI_LGB1_PW5) THEN
    REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `aff_dim (f0:real^N->bool) = aff_dim (IMAGE (h:real^N->real^3) f0)`
      SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_LGB1_AFF_DIM_INJ THEN
        MAP_EVERY EXISTS_TAC [`lh:real^N->real^3`; `yh:real^3`] THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
        USE_THEN "feq" SUBST1_TAC THEN ASM_REWRITE_TAC[]];
      USE_THEN "finv" (MP_TAC o SPEC `z:real^3`) THEN
      ANTS_TAC THENL
       [MP_TAC(ISPEC `Fz:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
        UNDISCH_TAC `(z:real^3) IN relative_interior Fz` THEN SET_TAC[];
        SIMP_TAC[]]];
    ALL_TAC] THEN
  ASM_CASES_TAC `Fz:real^3->bool = S` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_MONO THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex (S:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (Fz:real^3->bool) < aff_dim (S:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(IMAGE (a:real^2->real^3) r UNION IMAGE a r' SUBSET affine hull Fz)`
  ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(Fz:real^3->bool = S)` THEN REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[FACE_OF_IMP_SUBSET]; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!S'. P S' ==> (S:real^3->bool) SUBSET S'`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`S:real^3->bool`; `Fz:real^3->bool`] MOI_LGB1_FACE_HULL_INTER) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (a:real^2->real^3) r UNION IMAGE a r' SUBSET affine hull Fz` THEN
    UNDISCH_TAC `IMAGE (a:real^2->real^3) r UNION IMAGE a r' SUBSET S` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (Fz:real^3->bool) <
                aff_dim (IMAGE (a:real^2->real^3) r UNION IMAGE a r')` ASSUME_TAC THENL
   [MATCH_MP_TAC AFF_DIM_PSUBSET THEN ASM_REWRITE_TAC[PSUBSET] THEN
    DISCH_TAC THEN UNDISCH_TAC
      `~(IMAGE (a:real^2->real^3) r UNION IMAGE a r' SUBSET affine hull Fz)` THEN
    ASM_REWRITE_TAC[HULL_SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC AFF_DIM_EQ_AFFINE_HULL THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `S:real^3->bool` AFF_DIM_LE_UNIV) THEN REWRITE_TAC[DIMINDEX_3] THEN
  UNDISCH_TAC `&2 <= aff_dim (Fz:real^3->bool)` THEN
  UNDISCH_TAC `aff_dim (Fz:real^3->bool) < aff_dim (S:real^3->bool)` THEN
  UNDISCH_TAC `aff_dim (Fz:real^3->bool) <
               aff_dim (IMAGE (a:real^2->real^3) r UNION IMAGE a r')` THEN
  INT_ARITH_TAC);;

let MOI_LGB1_PIECE_L3 = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a d0 b t s.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     moi_lgb1_sml tt u h h' kk L g a d0 /\ moi_lgb1_cones tt h kk L g phi a b /\
     t IN moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                       (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) b /\
     s IN moi_lgb1_th tt kk /\
     IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a) t SUBSET s
     ==> ?R. R IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\ t SUBSET R`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `d0:real`; `b:(real^2->bool)->real^2`]
    MOI_LGB1_CUT_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_lgb1_cones tt (h:real^N->real^3) kk L (g:real^2->real^N) phi a b` THEN
    REWRITE_TAC[moi_lgb1_cones] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real^2->bool` o last o CONJUNCTS) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  STRIP_TAC THENL
   [EXISTS_TAC `t:real^2->bool` THEN REWRITE_TAC[SUBSET_REFL] THEN
    SUBGOAL_THEN `t INTER moi_lgb1_kv L (g:real^2->real^N) kk = {}` ASSUME_TAC THENL
     [UNDISCH_TAC `~(t IN moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk))` THEN
      REWRITE_TAC[moi_lgb1_lm; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[moi_lgb1_l3; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk))
                   g h' a) t SUBSET s` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_TAC THEN X_GEN_TAC `p:real^2` THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `p:real^2`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `!(y:real^N) z s. y = z ==> y IN s ==> z IN s`) THEN
    MATCH_MP_TAC MOI_LGB1_GP_UNMOVED THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                          `u:real^N->bool`; `h:real^N->real^3`; `Q:real^N->bool`;
                          `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                          `t:real^2->bool`] THEN
    ASM_REWRITE_TAC[];
    EXISTS_TAC `r:real^2->bool` THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_LGB1_LM_L3 THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`a:real^2->real^3`; `r:real^2->bool`; `s':real^3->bool`]
        MOI_LGB1_CELL_SUBSET) THEN
      UNDISCH_TAC `t SUBSET moi_lgb1_cell (a:real^2->real^3) r s'` THEN SET_TAC[]]]);;

let MOI_LGB1_CLAUSE4_CHART = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a d0 b
    r r' s x x' p R0.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     moi_lgb1_sml tt u h h' kk L g a d0 /\ moi_lgb1_sm2 tt h kk L g Q a d0 /\
     moi_lgb1_cones tt h kk L g phi a b /\
     r IN moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                       (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) b /\
     r' IN moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                        (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) b /\
     s IN tt /\
     IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a) r UNION
     IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a) r' SUBSET s /\
     (!s'. s' IN tt /\
           IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a) r UNION
           IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a) r' SUBSET s'
           ==> s SUBSET s') /\
     x IN r /\ x' IN r' /\ ~(x = x') /\
     moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a x =
     moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a x' /\
     moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a x IN Q UNION kk /\
     R0 IN moi_lgb1_lm L (moi_lgb1_kv L g kk) /\ p IN R0 /\ p IN r UNION r'
     ==> affine hull
           (IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a) r UNION
            IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a) r') =
         affine hull s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  ABBREV_TAC `gp = moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)) g h' a` THEN
  SUBGOAL_THEN `p IN UNIONS (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk))`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `R0:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `d0:real`; `p:real^2`] MOI_LGB1_GP_MOVED_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))))) THEN
  SUBGOAL_THEN `(h':real^3->real^N) (a (p:real^2)) IN s` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `(gp:real^2->real^N) p = h' ((a:real^2->real^3) p)`)) THEN
    UNDISCH_TAC `IMAGE (gp:real^2->real^N) r UNION IMAGE gp r' SUBSET s` THEN
    UNDISCH_TAC `(p:real^2) IN r UNION r'` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `s IN moi_lgb1_th (tt:(real^N->bool)->bool) kk` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:real^N->bool`] MOI_LGB1_TH_SUBSET) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    UNDISCH_TAC `moi_lgb1_sml tt u (h:real^N->real^3) h' kk L (g:real^2->real^N) a d0` THEN
    REWRITE_TAC[moi_lgb1_sml] THEN
    DISCH_THEN(MP_TAC o SPECL [`R0:real^2->bool`; `p:real^2`;
      `(h':real^3->real^N) (a (p:real^2))`; `s:real^N->bool`] o CONJUNCT2) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `s:real^N->bool`] MOI_LGB1_TH_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  SUBGOAL_THEN `IMAGE (h':real^3->real^N) (IMAGE h s) = s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o] THEN
    MATCH_MP_TAC(SET_RULE `!(f:real^N->real^N) s. (!x. x IN s ==> f x = x) ==> IMAGE f s = s`) THEN
    REWRITE_TAC[o_THM] THEN X_GEN_TAC `q:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(q:real^N) IN u` ASSUME_TAC THENL
     [UNDISCH_TAC `(s:real^N->bool) SUBSET u` THEN UNDISCH_TAC `(q:real^N) IN s` THEN
      SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(MATCH_MP (SPEC `q:real^N`
      (ASSUME `!x. x IN u ==> (h':real^3->real^N) ((h:real^N->real^3) x) = x /\
                              h x IN IMAGE h u`))
      (ASSUME `(q:real^N) IN u` )) THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `IMAGE (h:real^N->real^3) s`] MOI_LGB1_H_INV) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real^N->bool` (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
      (X_CHOOSE_THEN `l2:real^3->real^N` (X_CHOOSE_THEN `y2:real^N`
        STRIP_ASSUME_TAC))))))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `d0:real`; `b:(real^2->bool)->real^2`;
                 `r:real^2->bool`; `s:real^N->bool`] MOI_LGB1_PIECE_L3) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (gp:real^2->real^N) r UNION IMAGE gp r' SUBSET s` THEN SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `R1:real^2->bool` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `d0:real`; `b:(real^2->bool)->real^2`;
                 `r':real^2->bool`; `s:real^N->bool`] MOI_LGB1_PIECE_L3) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (gp:real^2->real^N) r UNION IMAGE gp r' SUBSET s` THEN SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `R2:real^2->bool` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `!q. q IN r UNION r'
                    ==> (gp:real^2->real^N) q = h' ((a:real^2->real^3) q) /\
                        a q IN IMAGE h u /\ a q IN IMAGE (h:real^N->real^3) s`
  (LABEL_TAC "pt") THENL
   [X_GEN_TAC `q:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?R. R IN moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk) /\ q IN R`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(q:real^2) IN r UNION r'` THEN REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
       [EXISTS_TAC `R1:real^2->bool`; EXISTS_TAC `R2:real^2->bool`] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(gp:real^2->real^N) q = h' ((a:real^2->real^3) q)` ASSUME_TAC THENL
     [EXPAND_TAC "gp" THEN MATCH_MP_TAC MOI_LGB1_GP_L3 THEN
      MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                            `u:real^N->bool`; `h:real^N->real^3`; `Q:real^N->bool`;
                            `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                            `R:real^2->bool`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(a:real^2->real^3) q IN IMAGE (h:real^N->real^3) u` ASSUME_TAC THENL
     [UNDISCH_TAC `moi_lgb1_sml tt u (h:real^N->real^3) h' kk L (g:real^2->real^N) a d0` THEN
      REWRITE_TAC[moi_lgb1_sml] THEN
      DISCH_THEN(MP_TAC o SPECL [`R:real^2->bool`; `q:real^2`] o CONJUNCT1) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(MATCH_MP (SPEC `(a:real^2->real^3) q`
      (ASSUME `!z. z IN IMAGE (h:real^N->real^3) u ==> h ((h':real^3->real^N) z) = z /\
                                                       h' z IN u`))
      (ASSUME `(a:real^2->real^3) q IN IMAGE (h:real^N->real^3) u`)) THEN
    DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `(gp:real^2->real^N) q = h' ((a:real^2->real^3) q)`)) THEN
    UNDISCH_TAC `IMAGE (gp:real^2->real^N) r UNION IMAGE gp r' SUBSET s` THEN
    UNDISCH_TAC `(q:real^2) IN r UNION r'` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (gp:real^2->real^N) r UNION IMAGE gp r' =
                IMAGE (h':real^3->real^N) (IMAGE (a:real^2->real^3) r UNION IMAGE a r')`
  SUBST1_TAC THENL
   [REWRITE_TAC[IMAGE_UNION; GSYM IMAGE_o] THEN
    MATCH_MP_TAC(SET_RULE `!(f:real^2->real^N) g s t. (!x. x IN s UNION t ==> f x = g x)
                             ==> IMAGE f s UNION IMAGE f t = IMAGE g s UNION IMAGE g t`) THEN
    REWRITE_TAC[o_THM] THEN X_GEN_TAC `q:real^2` THEN DISCH_TAC THEN
    USE_THEN "pt" (MP_TAC o C MATCH_MP (ASSUME `(q:real^2) IN r UNION r'`)) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (a:real^2->real^3) r UNION IMAGE a r' SUBSET IMAGE (h:real^N->real^3) s`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_UNION; SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `q:real^2` THEN
    DISCH_TAC THEN USE_THEN "pt" (MP_TAC o C MATCH_MP (ASSUME `(q:real^2) IN r UNION r'`)) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^2) IN r UNION r' /\ (x':real^2) IN r UNION r'` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_UNION]; ALL_TAC] THEN
  USE_THEN "pt" (MP_TAC o C MATCH_MP (ASSUME `(x:real^2) IN r UNION r'`)) THEN
  USE_THEN "pt" (MP_TAC o C MATCH_MP (ASSUME `(x':real^2) IN r UNION r'`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "gx'") (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "gx") (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  SUBGOAL_THEN `(a:real^2->real^3) x' = a x` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP (SPEC `(a:real^2->real^3) x`
      (ASSUME `!z. z IN IMAGE (h:real^N->real^3) u ==> h ((h':real^3->real^N) z) = z /\
                                                       h' z IN u`))
      (ASSUME `(a:real^2->real^3) x IN IMAGE (h:real^N->real^3) u`)) THEN
    MP_TAC(MATCH_MP (SPEC `(a:real^2->real^3) x'`
      (ASSUME `!z. z IN IMAGE (h:real^N->real^3) u ==> h ((h':real^3->real^N) z) = z /\
                                                       h' z IN u`))
      (ASSUME `(a:real^2->real^3) x' IN IMAGE (h:real^N->real^3) u`)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (K ALL_TAC)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (K ALL_TAC)) THEN
    AP_TERM_TAC THEN USE_THEN "gx" (SUBST1_TAC o SYM) THEN
    USE_THEN "gx'" (SUBST1_TAC o SYM) THEN
    CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h':real^3->real^N`; `l2:real^3->real^N`; `y2:real^N`;
                 `IMAGE (h:real^N->real^3) s`;
                 `IMAGE (a:real^2->real^3) r UNION IMAGE a r'`] MOI_LGB1_AFF_TRANSFER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC MOI_LGB1_CORE4 THEN
  MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                        `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`;
                        `kk:real^N->bool`; `L:(real^2->bool)->bool`; `g:real^2->real^N`;
                        `Q:real^N->bool`; `hs:real^3->bool`; `phi:real^2->real^3`;
                        `rk:real^2->num`; `d0:real`; `b:(real^2->bool)->real^2`;
                        `x:real^2`; `x':real^2`; `R1:real^2->bool`; `R2:real^2->bool`;
                        `(a:real^2->real^3) x`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `(gp:real^2->real^N) x IN Q UNION kk` THEN
    USE_THEN "gx" SUBST1_TAC THEN REWRITE_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `S':real^3->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `S':real^3->bool`] MOI_LGB1_H_INV) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s2:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "seq") (CONJUNCTS_THEN2 (LABEL_TAC "sinv") (K ALL_TAC))))) THEN
    USE_THEN "seq" SUBST1_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    UNDISCH_TAC `!s'. s' IN tt /\ IMAGE (gp:real^2->real^N) r UNION IMAGE gp r' SUBSET s'
                      ==> s SUBSET s'` THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                     `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                     `s2:real^N->bool`] MOI_LGB1_TH_FACTS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM IMAGE_UNION; SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `q:real^2` THEN
    DISCH_TAC THEN USE_THEN "pt" (MP_TAC o C MATCH_MP (ASSUME `(q:real^2) IN r UNION r'`)) THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN USE_THEN "sinv" (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN
    UNDISCH_TAC `IMAGE (a:real^2->real^3) r UNION IMAGE a r' SUBSET S'` THEN
    UNDISCH_TAC `(q:real^2) IN r UNION r'` THEN SET_TAC[]]);;

let MOI_LGB1_GP_CLAUSE4 = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a d0 b.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     moi_lgb1_sml tt u h h' kk L g a d0 /\ moi_lgb1_sm2 tt h kk L g Q a d0 /\
     moi_lgb1_cones tt h kk L g phi a b
     ==> !r r' s.
           r IN moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                             (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) b /\
           r' IN moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                              (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) b /\
           DISJOINT r r' /\ s IN tt /\
           IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a) r UNION
           IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a) r' SUBSET s /\
           (!s'. s' IN tt /\
                 IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a) r UNION
                 IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a) r' SUBSET s'
                 ==> s SUBSET s') /\
           ~(IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a) r INTER
             IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a) r' INTER
             (Q UNION kk) = {})
           ==> aff_dim s <=
               aff_dim (IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a) r) +
               aff_dim (IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a) r') /\
               aff_dim (affine hull
                          (IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a) r)
                        INTER affine hull
                          (IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a) r')) =
               aff_dim (IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a) r) +
               aff_dim (IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a) r') -
               aff_dim s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `d0:real`; `b:(real^2->bool)->real^2`]
    MOI_LGB1_CUT_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_lgb1_cones tt (h:real^N->real^3) kk L (g:real^2->real^N) phi a b` THEN
    REWRITE_TAC[moi_lgb1_cones] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "inL") (LABEL_TAC "cases")))) THEN
  ABBREV_TAC `gp = moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)) g h' a` THEN
  MAP_EVERY X_GEN_TAC [`r:real^2->bool`; `r':real^2->bool`; `s:real^N->bool`] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `~(IMAGE (gp:real^2->real^N) r INTER IMAGE gp r' INTER (Q UNION kk) = {})` THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC)
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `x':real^2` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
  SUBGOAL_THEN `(gp:real^2->real^N) x = gp x' /\ gp x IN Q UNION kk` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^N) IN Q UNION kk` THEN UNDISCH_TAC `(y:real^N) = gp (x':real^2)` THEN
    UNDISCH_TAC `(y:real^N) = gp (x:real^2)` THEN DISCH_THEN SUBST1_TAC THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(x:real^2 = x')` ASSUME_TAC THENL
   [UNDISCH_TAC `DISJOINT (r:real^2->bool) r'` THEN UNDISCH_TAC `(x:real^2) IN r` THEN
    UNDISCH_TAC `(x':real^2) IN r'` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gp:real^2->real^N) x IN IMAGE gp r /\ gp x IN IMAGE gp r'` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  ASM_CASES_TAC `?R0. R0 IN moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk) /\
                      ((x:real^2) IN R0 \/ (x':real^2) IN R0)` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `R0:real^2->bool` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
    MATCH_MP_TAC MOI_LGB1_C4_FROM_SPAN THEN EXISTS_TAC `(gp:real^2->real^N) x` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `?p:real^2. p IN R0 /\ p IN r UNION r'` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^2) IN R0 \/ (x':real^2) IN R0` THEN STRIP_TAC THENL
       [EXISTS_TAC `x:real^2`; EXISTS_TAC `x':real^2`] THEN ASM_REWRITE_TAC[IN_UNION];
      ALL_TAC] THEN
    EXPAND_TAC "gp" THEN MATCH_MP_TAC MOI_LGB1_CLAUSE4_CHART THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                          `u:real^N->bool`; `h:real^N->real^3`; `Q:real^N->bool`;
                          `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                          `d0:real`; `b:(real^2->bool)->real^2`; `x:real^2`; `x':real^2`;
                          `p:real^2`; `R0:real^2->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(gp:real^2->real^N) x IN Q UNION kk` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!R0. R0 IN moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)
                      ==> ~((x:real^2) IN R0)) /\
                (!R0. R0 IN moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)
                      ==> ~((x':real^2) IN R0))` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!t z. t IN moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)) a
                         (IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)) b /\
                      z IN t /\
                      (!R0. R0 IN moi_lgb1_lm L (moi_lgb1_kv L g kk) ==> ~(z IN R0))
                      ==> t IN L /\ t INTER moi_lgb1_kv L g kk = {}` (LABEL_TAC "unm") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "cases" (MP_TAC o SPEC `t:real^2->bool`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN2 STRIP_ASSUME_TAC
      (X_CHOOSE_THEN `R9:real^2->bool` (X_CHOOSE_THEN `S9:real^3->bool` STRIP_ASSUME_TAC))) THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(t IN moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk))` THEN
      REWRITE_TAC[moi_lgb1_lm; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `R9:real^2->bool` o check (fun th ->
        can (term_match [] `!R0. R0 IN mv ==> ~((z:real^2) IN R0)`) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`a:real^2->real^3`; `R9:real^2->bool`; `S9:real^3->bool`]
        MOI_LGB1_CELL_SUBSET) THEN
      UNDISCH_TAC `t SUBSET moi_lgb1_cell (a:real^2->real^3) R9 S9` THEN
      UNDISCH_TAC `(z:real^2) IN t` THEN SET_TAC[]];
    ALL_TAC] THEN
  USE_THEN "unm" (MP_TAC o SPECL [`r:real^2->bool`; `x:real^2`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "unm" (MP_TAC o SPECL [`r':real^2->bool`; `x':real^2`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `IMAGE (gp:real^2->real^N) r = IMAGE g r /\ IMAGE gp r' = IMAGE g r'`
  (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [CONJ_TAC THEN
    MATCH_MP_TAC(SET_RULE `!s (f:real^2->real^N) g. (!x. x IN s ==> f x = g x)
                             ==> IMAGE f s = IMAGE g s`) THEN
    REPEAT STRIP_TAC THEN EXPAND_TAC "gp" THEN MATCH_MP_TAC MOI_LGB1_GP_UNMOVED THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                          `u:real^N->bool`; `h:real^N->real^3`; `Q:real^N->bool`;
                          `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`] THENL
     [EXISTS_TAC `r:real^2->bool`; EXISTS_TAC `r':real^2->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gp:real^2->real^N) x = g x /\ (gp:real^2->real^N) x' = g x'`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN EXPAND_TAC "gp" THEN MATCH_MP_TAC MOI_LGB1_GP_UNMOVED THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                          `u:real^N->bool`; `h:real^N->real^3`; `Q:real^N->bool`;
                          `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`] THENL
     [EXISTS_TAC `r:real^2->bool`; EXISTS_TAC `r':real^2->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^2->real^N) x IN Q` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `g:real^2->real^N`; `kk:real^N->bool`;
                   `r:real^2->bool`; `(g:real^2->real^N) x`] MOI_LGB1_NO_KK) THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
    UNDISCH_TAC `(gp:real^2->real^N) x IN Q UNION kk` THEN
    FIRST_X_ASSUM(fun th -> if concl th = `(gp:real^2->real^N) x = g x`
                            then REWRITE_TAC[th] else NO_TAC) THEN
    REWRITE_TAC[IN_UNION] THEN CONV_TAC TAUT;
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^2->real^N) x = g x'` ASSUME_TAC THENL
   [TRANS_TAC EQ_TRANS `(gp:real^2->real^N) x` THEN CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      TRANS_TAC EQ_TRANS `(gp:real^2->real^N) x'` THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `L:(real^2->bool)->bool`; `g:real^2->real^N`;
                 `Q:real^N->bool`] MOI_LGB1_TGEN_CLAUSES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`r:real^2->bool`; `r':real^2->bool`; `s:real^N->bool`] o
    CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  EXISTS_TAC `(g:real^2->real^N) x` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x':real^2` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* C18. Clause 3 of tgeneric for the moved map (no fold along a wall).      *)
(* Planar tools: two 2-dimensional convex sets in a closed half-plane that  *)
(* contain a common segment of the boundary line have meeting interiors;   *)
(* an edge of a triangle is cut out by a supporting line.                   *)
(* ------------------------------------------------------------------------- *)

let MOI_LGB1_SAME_SIDE_2D = prove
 (`!T1 T2 (e1:real^2) e2 (n:real^2) b.
     convex T1 /\ convex T2 /\ aff_dim T1 = &2 /\ aff_dim T2 = &2 /\
     e1 IN T1 /\ e2 IN T1 /\ e1 IN T2 /\ e2 IN T2 /\ ~(e1 = e2) /\ ~(n = vec 0) /\
     n dot e1 = b /\ n dot e2 = b /\
     (!x. x IN T1 ==> n dot x <= b) /\ (!x. x IN T2 ==> n dot x <= b)
     ==> ~(interior T1 INTER interior T2 = {})`,
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  SUBGOAL_THEN `!Tq:real^2->bool. aff_dim Tq = &2 /\ (!x. x IN Tq ==> n dot x <= b)
                                  ==> ?p. p IN Tq /\ n dot p < b` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `~((Tq:real^2->bool) SUBSET {x | n dot x = b})` MP_TAC THENL
     [DISCH_TAC THEN
      MP_TAC(ISPECL [`Tq:real^2->bool`; `{x:real^2 | n dot x = b}`] AFF_DIM_SUBSET) THEN
      ASM_SIMP_TAC[AFF_DIM_HYPERPLANE; DIMINDEX_2] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; NOT_FORALL_THM; NOT_IMP] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p:real^2` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[REAL_LT_LE] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `T1:real^2->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:real^2` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `T2:real^2->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p2:real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!p:real^2. n dot p < b ==> ~collinear {e1,e2,p}` ASSUME_TAC THENL
   [X_GEN_TAC `p:real^2` THEN DISCH_TAC THEN ASM_SIMP_TAC[COLLINEAR_3_AFFINE_HULL] THEN
    REWRITE_TAC[AFFINE_HULL_2; IN_ELIM_THM; NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:real`; `v:real`] THEN STRIP_TAC THEN
    UNDISCH_TAC `n dot (p:real^2) < b` THEN ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN
    REWRITE_TAC[GSYM REAL_ADD_RDISTRIB] THEN ASM_REWRITE_TAC[REAL_MUL_LID; REAL_LT_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `~collinear {e1:real^2,e2,p1} /\ ~collinear {e1:real^2,e2,p2}`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `interior(convex hull {e1:real^2,e2,p1}) SUBSET interior T1 /\
                interior(convex hull {e1:real^2,e2,p2}) SUBSET interior T2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_INTERIOR THEN MATCH_MP_TAC HULL_MINIMAL THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p2:real^2) IN affine hull {e1,e2,p1}` MP_TAC THENL
   [SUBGOAL_THEN `affine hull {e1:real^2,e2,p1} = (:real^2)` SUBST1_TAC THENL
     [ALL_TAC; REWRITE_TAC[IN_UNIV]] THEN
    REWRITE_TAC[GSYM AFF_DIM_EQ_FULL; DIMINDEX_2] THEN
    UNDISCH_TAC `~collinear {e1:real^2,e2,p1}` THEN
    REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT; DE_MORGAN_THM] THEN STRIP_TAC THEN
    MP_TAC(ISPEC `{e1:real^2,e2,p1}` AFF_DIM_AFFINE_INDEPENDENT) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `CARD {e1:real^2,e2,p1} = 3` SUBST1_TAC THENL
     [SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
      UNDISCH_TAC `~(e1:real^2 = e2)` THEN UNDISCH_TAC `~(e1:real^2 = p1)` THEN
      UNDISCH_TAC `~(e2:real^2 = p1)` THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
      SIMP_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
      CONV_TAC INT_REDUCE_CONV];
    ALL_TAC] THEN
  REWRITE_TAC[AFFINE_HULL_3; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `al:real` (X_CHOOSE_THEN `be:real` (X_CHOOSE_THEN `ga:real`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)))) THEN
  SUBGOAL_THEN `&0 < ga` ASSUME_TAC THENL
   [UNDISCH_TAC `n dot (al % e1 + be % e2 + ga % p1:real^2) < b` THEN
    ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN DISCH_TAC THEN
    SUBGOAL_THEN `al * b + be * b + ga * b = b` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_ADD_RDISTRIB] THEN ASM_REWRITE_TAC[REAL_MUL_LID]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < ga * (b - n dot (p1:real^2))` MP_TAC THENL
     [REWRITE_TAC[REAL_SUB_LDISTRIB] THEN
      UNDISCH_TAC `al * b + be * b + ga * (n dot (p1:real^2)) < b` THEN
      UNDISCH_TAC `al * b + be * b + ga * b = b` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `(~p ==> ~q) ==> q ==> p`) THEN REWRITE_TAC[REAL_NOT_LT] THEN
    DISCH_TAC THEN
    MP_TAC(SPECL [`--ga`; `b - n dot (p1:real^2)`] REAL_LE_MUL) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `ga <= &0` THEN UNDISCH_TAC `n dot (p1:real^2) < b` THEN REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `lam = &1 + abs al + abs be` THEN
  SUBGOAL_THEN `&0 < &2 * lam + &1` ASSUME_TAC THENL
   [EXPAND_TAC "lam" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  EXISTS_TAC `(lam / (&2 * lam + &1)) % e1 + (lam / (&2 * lam + &1)) % e2 +
              (&1 / (&2 * lam + &1)) % (al % e1 + be % e2 + ga % p1:real^2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!s t (y:real^2). s SUBSET t /\ y IN s ==> y IN t`) THEN
    EXISTS_TAC `interior(convex hull {e1:real^2,e2,p1})` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[INTERIOR_CONVEX_HULL_3_MINIMAL; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`(lam + al) / (&2 * lam + &1)`; `(lam + be) / (&2 * lam + &1)`;
                          `ga / (&2 * lam + &1)`] THEN
    ASM_SIMP_TAC[REAL_LT_DIV] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "lam" THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "lam" THEN
      REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_FIELD `&0 < d ==> x / d + y / d + z / d = (x + y + z) / d`] THEN
      ASM_SIMP_TAC[REAL_DIV_EQ_1; REAL_LT_IMP_NZ] THEN
      UNDISCH_TAC `&0 < &2 * lam + &1` THEN UNDISCH_TAC `al + be + ga = &1` THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[real_div; VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN VECTOR_ARITH_TAC];
    MATCH_MP_TAC(SET_RULE `!s t (y:real^2). s SUBSET t /\ y IN s ==> y IN t`) THEN
    EXISTS_TAC `interior(convex hull {e1:real^2,e2,al % e1 + be % e2 + ga % p1})` THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[INTERIOR_CONVEX_HULL_3_MINIMAL; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`lam / (&2 * lam + &1)`; `lam / (&2 * lam + &1)`;
                          `&1 / (&2 * lam + &1)`] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "lam" THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "lam" THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[REAL_LT_01];
      ASM_SIMP_TAC[REAL_FIELD `&0 < d ==> x / d + y / d + z / d = (x + y + z) / d`] THEN
      ASM_SIMP_TAC[REAL_DIV_EQ_1; REAL_LT_IMP_NZ] THEN
      UNDISCH_TAC `&0 < &2 * lam + &1` THEN REAL_ARITH_TAC;
      REFL_TAC]]);;

let MOI_LGB1_EDGE_HALFPLANE = prove
 (`!(R:real^2->bool) E.
     polytope R /\ E face_of R /\ ~(E = R) /\ ~(E = {})
     ==> ?n b. ~(n = vec 0) /\ (!x. x IN R ==> n dot x <= b) /\
               (!x. x IN E ==> n dot x = b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`R:real^2->bool`; `E:real^2->bool`] EXPOSED_FACE_OF_POLYHEDRON) THEN
  ASM_SIMP_TAC[POLYTOPE_IMP_POLYHEDRON] THEN REWRITE_TAC[exposed_face_of] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:real^2` (X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC) o
    CONJUNCT2) THEN
  MAP_EVERY EXISTS_TAC [`n:real^2`; `b:real`] THEN REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `E = (R:real^2->bool) INTER {x | n dot x = b}` THEN
    ASM_REWRITE_TAC[DOT_LZERO] THEN ASM_CASES_TAC `&0 = b` THEN
    ASM_REWRITE_TAC[EMPTY_GSPEC; UNIV_GSPEC; INTER_UNIV; INTER_EMPTY];
    UNDISCH_TAC `(R:real^2->bool) SUBSET {x | n dot x <= b}` THEN SET_TAC[];
    UNDISCH_TAC `E = (R:real^2->bool) INTER {x | n dot x = b}` THEN SET_TAC[]]);;

let MOI_LGB1_FOLD_FRONTIER = prove
 (`!(K:(real^2->bool)->bool) e r1 r2.
     simplicial_complex K /\ UNIONS K = std_triangle /\
     e IN K /\ aff_dim e = &1 /\ r1 IN K /\ aff_dim r1 = &2 /\ e SUBSET r1 /\
     r2 IN K /\ aff_dim r2 = &2 /\ e SUBSET r2 /\ ~(r1 = r2)
     ==> ~(e SUBSET relative_frontier std_triangle)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`K:(real^2->bool)->bool`; `std_triangle`; `\x:real^2. x`; `\x:real^2. x`;
                 `e:real^2->bool`; `r1:real^2->bool`; `r2:real^2->bool`] MOI_FM3_DISK_EDGE2) THEN
  ASM_REWRITE_TAC[MOI_LTD_STD_TRIANGLE_SIMPLEX; HOMEOMORPHISM_ID; IMAGE_ID] THEN
  SUBGOAL_THEN `~(relative_interior (e:real^2->bool) = {})` MP_TAC THENL
   [SUBGOAL_THEN `convex (e:real^2->bool) /\ ~(e = {})` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
        DISCH_TAC THEN UNDISCH_TAC `aff_dim (e:real^2->bool) = &1` THEN
        ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC];
      ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `e:real^2->bool` RELATIVE_INTERIOR_SUBSET) THEN
  UNDISCH_TAC `(e:real^2->bool) SUBSET relative_frontier std_triangle` THEN
  REWRITE_TAC[relative_frontier] THEN SET_TAC[]);;

let MOI_LGB1_INT_MEET = prove
 (`!(K:(real^3->bool)->bool) S S'.
     simplicial_complex K /\ S IN K /\ S' IN K /\ aff_dim S = &3 /\
     ~(S' INTER interior S = {})
     ==> S = S'`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_complex]) THEN
  SUBGOAL_THEN `interior S = relative_interior (S:real^3->bool)` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RELATIVE_INTERIOR_INTERIOR THEN
    REWRITE_TAC[GSYM AFF_DIM_EQ_FULL; DIMINDEX_3] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(S INTER S':real^3->bool) face_of S /\ (S INTER S') face_of S'`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(S:real^3->bool) SUBSET S'` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!s t:real^3->bool. s SUBSET s INTER t ==> s SUBSET t`) THEN
    MATCH_MP_TAC SUBSET_OF_FACE_OF THEN EXISTS_TAC `S:real^3->bool` THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN
    UNDISCH_TAC `~(S' INTER interior S:real^3->bool = {})` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `S:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `S':real^3->bool`] FACE_OF_AFF_DIM_LT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
      SUBGOAL_THEN `S INTER S':real^3->bool = S` (fun th -> ASM_MESON_TAC[th]) THEN
      UNDISCH_TAC `(S:real^3->bool) SUBSET S'` THEN SET_TAC[];
      FIRST_ASSUM ACCEPT_TAC];
    MP_TAC(ISPEC `S':real^3->bool` AFF_DIM_LE_UNIV) THEN REWRITE_TAC[DIMINDEX_3] THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC]);;

let MOI_LGB1_MOVED_PT = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a d0 R q s.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     moi_lgb1_sml tt u h h' kk L g a d0 /\
     R IN moi_lgb1_lm L (moi_lgb1_kv L g kk) /\ q IN R /\ s IN tt /\
     moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a q IN s
     ==> s IN moi_lgb1_t3 tt kk /\ s IN moi_lgb1_th tt kk /\ a q IN IMAGE h s /\
         moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a q = h' (a q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `q IN UNIONS (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk))`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `R:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `d0:real`; `q:real^2`] MOI_LGB1_GP_MOVED_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "gq") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))))) THEN
  SUBGOAL_THEN `(h':real^3->real^N) (a (q:real^2)) IN s` ASSUME_TAC THENL
   [USE_THEN "gq" (SUBST1_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s IN moi_lgb1_t3 (tt:(real^N->bool)->bool) kk` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lgb1_sml tt u (h:real^N->real^3) h' kk L (g:real^2->real^N) a d0` THEN
    REWRITE_TAC[moi_lgb1_sml] THEN
    DISCH_THEN(MP_TAC o SPECL [`R:real^2->bool`; `q:real^2`;
      `(h':real^3->real^N) (a (q:real^2))`; `s:real^N->bool`] o CONJUNCT2) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:real^N->bool`] MOI_LGB1_TH_SUBSET) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `(h:real^N->real^3) ((h':real^3->real^N) ((a:real^2->real^3) q)) = a q`)) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC]);;

(* Fold case A, second half: the triangles are cone triangles over cells   *)
(* of the moved triangle E in the 3-cell of s'; their bases contain e.     *)

let MOI_LGB1_FOLD_A2 = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a d0 b
    e r1 r2 s s' E p.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     moi_lgb1_sml tt u h h' kk L g a d0 /\ moi_lgb1_cones tt h kk L g phi a b /\
     e IN moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                       (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) b /\
     r1 IN moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                        (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) b /\
     r2 IN moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                        (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) b /\
     ~(r1 = r2) /\ aff_dim e = &1 /\ aff_dim r1 = &2 /\ aff_dim r2 = &2 /\
     e SUBSET r1 /\ e SUBSET r2 /\
     s IN tt /\ aff_dim s = &2 /\
     IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a) e SUBSET s /\
     s' IN tt /\ aff_dim s' = &3 /\
     IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a) r1 UNION
     IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a) r2 SUBSET s' /\
     E IN moi_lgb1_lm L (moi_lgb1_kv L g kk) /\ aff_dim E = &2 /\ p IN e /\
     r1 SUBSET E /\ r2 SUBSET E
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`] MOI_LGB1_H_SC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ABBREV_TAC `gp = moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)) g h' a` THEN
  SUBGOAL_THEN `(E:real^2->bool) IN L` ASSUME_TAC THENL
   [UNDISCH_TAC `E IN moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)` THEN
    REWRITE_TAC[moi_lgb1_lm; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* chart images *)
  SUBGOAL_THEN `!q t. q IN E /\ t IN tt /\ (gp:real^2->real^N) q IN t
                      ==> t IN moi_lgb1_th tt kk /\ (a:real^2->real^3) q IN IMAGE h t`
  (LABEL_TAC "img") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                   `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                   `a:real^2->real^3`; `d0:real`; `E:real^2->bool`; `q:real^2`;
                   `t:real^N->bool`] MOI_LGB1_MOVED_PT) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^2) IN E /\ (gp:real^2->real^N) p IN s /\ gp p IN s'`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      UNDISCH_TAC `IMAGE (gp:real^2->real^N) e SUBSET s` THEN
      UNDISCH_TAC `(p:real^2) IN e` THEN SET_TAC[];
      UNDISCH_TAC `IMAGE (gp:real^2->real^N) r1 UNION IMAGE gp r2 SUBSET s'` THEN
      UNDISCH_TAC `(p:real^2) IN e` THEN UNDISCH_TAC `(e:real^2->bool) SUBSET r1` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  USE_THEN "img" (MP_TAC o SPECL [`p:real^2`; `s:real^N->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "img" (MP_TAC o SPECL [`p:real^2`; `s':real^N->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `IMAGE (h:real^N->real^3) s IN IMAGE (IMAGE h) (moi_lgb1_th tt kk) /\
                IMAGE (h:real^N->real^3) s' IN IMAGE (IMAGE h) (moi_lgb1_th tt kk)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (IMAGE (h:real^N->real^3) s) = &2` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `s:real^N->bool`] MOI_LGB1_TH_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `lh:real^N->real^3` (X_CHOOSE_THEN `yh:real^3`
         STRIP_ASSUME_TAC)) ASSUME_TAC))) THEN
    SUBGOAL_THEN `aff_dim (IMAGE (h:real^N->real^3) s) = aff_dim s` SUBST1_TAC THENL
     [MATCH_MP_TAC MOI_LGB1_AFF_DIM_INJ THEN
      MAP_EVERY EXISTS_TAC [`lh:real^N->real^3`; `yh:real^3`] THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (IMAGE (h:real^N->real^3) s') = &3` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `s':real^N->bool`] MOI_LGB1_TH_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `lh:real^N->real^3` (X_CHOOSE_THEN `yh:real^3`
         STRIP_ASSUME_TAC)) ASSUME_TAC))) THEN
    SUBGOAL_THEN `aff_dim (IMAGE (h:real^N->real^3) s') = aff_dim s'` SUBST1_TAC THENL
     [MATCH_MP_TAC MOI_LGB1_AFF_DIM_INJ THEN
      MAP_EVERY EXISTS_TAC [`lh:real^N->real^3`; `yh:real^3`] THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(r1:real^2->bool) SUBSET r1 UNION r2 /\ (r2:real^2->bool) SUBSET r1 UNION r2`
  STRIP_ASSUME_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!q. q IN e ==> (a:real^2->real^3) q IN IMAGE (h:real^N->real^3) s`
  (LABEL_TAC "ae") THENL
   [X_GEN_TAC `q:real^2` THEN DISCH_TAC THEN
    USE_THEN "img" (MP_TAC o SPECL [`q:real^2`; `s:real^N->bool`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `IMAGE (gp:real^2->real^N) e SUBSET s` THEN
      UNDISCH_TAC `(q:real^2) IN e` THEN SET_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!q. q IN r1 UNION r2 ==> (a:real^2->real^3) q IN IMAGE (h:real^N->real^3) s'`
  (LABEL_TAC "ar") THENL
   [X_GEN_TAC `q:real^2` THEN DISCH_TAC THEN
    USE_THEN "img" (MP_TAC o SPECL [`q:real^2`; `s':real^N->bool`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `IMAGE (gp:real^2->real^N) r1 UNION IMAGE gp r2 SUBSET s'` THEN
      UNDISCH_TAC `(q:real^2) IN r1 UNION r2` THEN SET_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. r IN moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)) a
                       (IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)) b /\
                    aff_dim r = &2 /\ r SUBSET E
                    ==> ?P f. P IN moi_lgb1_c2 (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                                               (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) /\
                              f face_of P /\ ~(f = P) /\ r = convex hull (b P INSERT f)`
  (LABEL_TAC "cone") THENL
   [X_GEN_TAC `r:real^2->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`L:(real^2->bool)->bool`;
                   `moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)`;
                   `a:real^2->real^3`; `IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)`;
                   `b:(real^2->bool)->real^2`; `r:real^2->bool`] MOI_LGB1_CUT_PIECES) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN2 STRIP_ASSUME_TAC (DISJ_CASES_THEN2
      (X_CHOOSE_THEN `R9:real^2->bool` (X_CHOOSE_THEN `S9:real^3->bool` STRIP_ASSUME_TAC))
      ACCEPT_TAC)) THENL
     [SUBGOAL_THEN `(r:real^2->bool) face_of E` ASSUME_TAC THENL
       [SUBGOAL_THEN `r INTER E:real^2->bool = r` (SUBST1_TAC o SYM) THENL
         [UNDISCH_TAC `(r:real^2->bool) SUBSET E` THEN SET_TAC[]; ALL_TAC] THEN
        ASM_MESON_TAC[simplicial_complex];
        ALL_TAC] THEN
      SUBGOAL_THEN `r:real^2->bool = E` SUBST_ALL_TAC THENL
       [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`r:real^2->bool`; `E:real^2->bool`] FACE_OF_AFF_DIM_LT) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
          ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
        ASM_MESON_TAC[]];
      UNDISCH_TAC `aff_dim (r:real^2->bool) = &2` THEN
      FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq (concl th) &&
        lhs (concl th) = `r:real^2->bool`)) THEN
      UNDISCH_TAC `aff_dim (moi_lgb1_cell (a:real^2->real^3) R9 S9) <= &1` THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!P f. P IN moi_lgb1_c2 (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)) a
                           (IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)) /\
          f face_of P /\ ~(f = P) /\
          convex hull ((b:(real^2->bool)->real^2) P INSERT f) SUBSET E /\
          aff_dim (convex hull (b P INSERT f)) = &2 /\
          e SUBSET convex hull (b P INSERT f) /\
          convex hull (b P INSERT f) SUBSET r1 UNION r2
          ==> P = moi_lgb1_cell a E (IMAGE h s') /\ e SUBSET f /\ aff_dim f = &1`
  (LABEL_TAC "pc") THENL
   [MAP_EVERY X_GEN_TAC [`P:real^2->bool`; `f:real^2->bool`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `h:real^N->real^3`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `phi:real^2->real^3`;
                   `a:real^2->real^3`; `b:(real^2->bool)->real^2`; `P:real^2->bool`]
      MOI_LGB1_CONES_GOOD) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                   `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                   `a:real^2->real^3`; `d0:real`; `P:real^2->bool`] MOI_LGB1_C2_CELL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `lp:real^2->real^3` (X_CHOOSE_THEN `yp:real^3`
         STRIP_ASSUME_TAC)) (K ALL_TAC)))))) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                   `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                   `a:real^2->real^3`; `d0:real`; `P:real^2->bool`] MOI_LGB1_C2_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `R:real^2->bool` (X_CHOOSE_THEN `S:real^3->bool`
      (fun th -> let cs = CONJUNCTS th in
                 let iseq t = is_eq (concl t) && is_var (lhs (concl t)) in
                 MAP_EVERY ASSUME_TAC (filter (not o iseq) cs) THEN
                 SUBST_ALL_TAC (find iseq cs)))) THEN
    ABBREV_TAC `P0 = moi_lgb1_cell (a:real^2->real^3) R S` THEN
    SUBGOAL_THEN `relative_interior (convex hull ((b:(real^2->bool)->real^2) P0 INSERT f))
                  SUBSET relative_interior P0` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_LGB1_CONE_RELINT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(relative_interior (convex hull ((b:(real^2->bool)->real^2) P0 INSERT f))
                    = {})` ASSUME_TAC THENL
     [SIMP_TAC[CONVEX_CONVEX_HULL; RELATIVE_INTERIOR_EQ_EMPTY] THEN
      REWRITE_TAC[CONVEX_HULL_EQ_EMPTY; NOT_INSERT_EMPTY];
      ALL_TAC] THEN
    SUBGOAL_THEN `R:real^2->bool = E` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC MOI_LGB1_CARRIER_UNIQUE THEN EXISTS_TAC `L:(real^2->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `R IN moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)` THEN
        REWRITE_TAC[moi_lgb1_lm; IN_ELIM_THM] THEN SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `relative_interior (convex hull ((b:(real^2->bool)->real^2) P0 INSERT f))
                    SUBSET relative_interior E` MP_TAC THENL
       [MATCH_MP_TAC SUBSET_RELATIVE_INTERIOR THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC AFF_DIM_EQ_AFFINE_HULL THEN ASM_REWRITE_TAC[INT_LE_REFL];
        ALL_TAC] THEN
      UNDISCH_TAC `relative_interior P0 SUBSET relative_interior (R:real^2->bool)` THEN
      UNDISCH_TAC `relative_interior (convex hull ((b:(real^2->bool)->real^2) P0 INSERT f))
                   SUBSET relative_interior P0` THEN
      UNDISCH_TAC `~(relative_interior (convex hull ((b:(real^2->bool)->real^2) P0 INSERT f))
                    = {})` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(b:(real^2->bool)->real^2) P0 IN convex hull (b P0 INSERT f)` ASSUME_TAC THENL
     [MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
    SUBGOAL_THEN `(a:real^2->real^3) ((b:(real^2->bool)->real^2) P0) IN interior S`
    ASSUME_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!s t (z:real^3). s SUBSET t /\ z IN s ==> z IN t`) THEN
      EXISTS_TAC `relative_interior (IMAGE (a:real^2->real^3) P0)` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`a:real^2->real^3`; `lp:real^2->real^3`; `yp:real^3`; `P0:real^2->bool`]
        MOI_LGB1_RELINT_AFFINE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `S = IMAGE (h:real^N->real^3) s'` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC MOI_LGB1_INT_MEET THEN
      EXISTS_TAC `IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)` THEN
      ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `(a:real^2->real^3) ((b:(real^2->bool)->real^2) P0)` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "ar" MATCH_MP_TAC THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `!q. q IN e ==> ~((q:real^2) IN relative_interior P0)` ASSUME_TAC THENL
     [X_GEN_TAC `q:real^2` THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `(a:real^2->real^3) q IN interior (IMAGE (h:real^N->real^3) s')`
      ASSUME_TAC THENL
       [MATCH_MP_TAC(SET_RULE `!s t (z:real^3). s SUBSET t /\ z IN s ==> z IN t`) THEN
        EXISTS_TAC `relative_interior (IMAGE (a:real^2->real^3) P0)` THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`a:real^2->real^3`; `lp:real^2->real^3`; `yp:real^3`; `P0:real^2->bool`]
          MOI_LGB1_RELINT_AFFINE) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)`;
                     `IMAGE (h:real^N->real^3) s'`; `IMAGE (h:real^N->real^3) s`]
        MOI_LGB1_INT_MEET) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
        EXISTS_TAC `(a:real^2->real^3) q` THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "ae" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        DISCH_TAC THEN
        SUBGOAL_THEN `aff_dim (IMAGE (h:real^N->real^3) s) = &3` MP_TAC THENL
         [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
            concl th = `IMAGE (h:real^N->real^3) s' = IMAGE h s`)) THEN
          ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[] THEN INT_ARITH_TAC]];
      ALL_TAC] THEN
    SUBGOAL_THEN `convex hull ((b:(real^2->bool)->real^2) P0 INSERT f) SUBSET P0`
    ASSUME_TAC THENL
     [MATCH_MP_TAC HULL_MINIMAL THEN ASM_REWRITE_TAC[INSERT_SUBSET] THEN
      ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET; FACE_OF_IMP_SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN `(e:real^2->bool) SUBSET f` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`P0:real^2->bool`; `(b:(real^2->bool)->real^2) P0`; `f:real^2->bool`;
                     `relative_frontier P0:real^2->bool`] MOI_CON_CONE_INTER_OUTSIDE) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[POLYTOPE_IMP_CLOSED; FACE_OF_SUBSET_RELATIVE_FRONTIER] THEN
        CONJ_TAC THENL [ASM_MESON_TAC[FACE_OF_IMP_CONVEX]; ALL_TAC] THEN
        REWRITE_TAC[relative_frontier] THEN SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(e:real^2->bool) SUBSET relative_frontier P0` MP_TAC THENL
       [ASM_SIMP_TAC[relative_frontier; POLYTOPE_IMP_CLOSED; CLOSURE_CLOSED] THEN
        REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `q:real^2` THEN DISCH_TAC THEN
        ASM_SIMP_TAC[] THEN ASM SET_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `(e:real^2->bool) SUBSET convex hull ((b:(real^2->bool)->real^2) P0 INSERT f)` THEN
      SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `aff_dim (convex hull ((b:(real^2->bool)->real^2) P0 INSERT f)) = &2` THEN
    REWRITE_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_INSERT] THEN
    SUBGOAL_THEN `~((b:(real^2->bool)->real^2) P0 IN affine hull f)` (fun th -> REWRITE_TAC[th]) THENL
     [MP_TAC(ISPECL [`P0:real^2->bool`; `f:real^2->bool`]
        AFFINE_HULL_FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(b:(real^2->bool)->real^2) P0 IN relative_interior P0` THEN SET_TAC[];
      INT_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "cone" (MP_TAC o SPEC `r1:real^2->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `P1:real^2->bool` (X_CHOOSE_THEN `f1:real^2->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "r1eq")))))) THEN
  USE_THEN "cone" (MP_TAC o SPEC `r2:real^2->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `P2:real^2->bool` (X_CHOOSE_THEN `f2:real^2->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "r2eq")))))) THEN
  USE_THEN "pc" (MP_TAC o SPECL [`P1:real^2->bool`; `f1:real^2->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "r1eq" (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
    SET_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC)] THEN
  USE_THEN "pc" (MP_TAC o SPECL [`P2:real^2->bool`; `f2:real^2->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "r2eq" (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
    SET_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `!f f'. f face_of moi_lgb1_cell (a:real^2->real^3) E (IMAGE (h:real^N->real^3) s') /\
                       f' face_of moi_lgb1_cell a E (IMAGE h s') /\ aff_dim f = &1 /\
                       e SUBSET f /\ e SUBSET f' ==> f SUBSET f'` (LABEL_TAC "fsub") THENL
   [MAP_EVERY X_GEN_TAC [`f:real^2->bool`; `f':real^2->bool`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(f INTER f':real^2->bool) face_of f` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`f INTER f':real^2->bool`;
                     `moi_lgb1_cell (a:real^2->real^3) E (IMAGE (h:real^N->real^3) s')`;
                     `f:real^2->bool`] FACE_OF_FACE) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      REWRITE_TAC[INTER_SUBSET] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC FACE_OF_INTER THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `!s t:real^2->bool. s INTER t = s ==> s SUBSET t`) THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`f INTER f':real^2->bool`; `f:real^2->bool`] FACE_OF_AFF_DIM_LT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[FACE_OF_IMP_CONVEX];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`e:real^2->bool`; `f INTER f':real^2->bool`] AFF_DIM_SUBSET) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[SUBSET_INTER]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `f2:real^2->bool = f1` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN CONJ_TAC THEN
    USE_THEN "fsub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `~(r1:real^2->bool = r2)` THEN REWRITE_TAC[] THEN
  USE_THEN "r1eq" SUBST1_TAC THEN USE_THEN "r2eq" SUBST1_TAC THEN
  ASM_REWRITE_TAC[]);;

(* Fold case A: the L-carrier of the edge is a (moved) triangle; the two    *)
(* L'-triangles would be cone triangles over the same 2-cell.               *)

let MOI_LGB1_FOLD_A = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a d0 b
    e r1 r2 s s' E p.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     moi_lgb1_sml tt u h h' kk L g a d0 /\ moi_lgb1_cones tt h kk L g phi a b /\
     e IN moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                       (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) b /\
     r1 IN moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                        (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) b /\
     r2 IN moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                        (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) b /\
     ~(r1 = r2) /\ aff_dim e = &1 /\ aff_dim r1 = &2 /\ aff_dim r2 = &2 /\
     e SUBSET r1 /\ e SUBSET r2 /\
     s IN tt /\ aff_dim s = &2 /\
     IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a) e SUBSET s /\
     s' IN tt /\ aff_dim s' = &3 /\
     IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a) r1 UNION
     IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a) r2 SUBSET s' /\
     E IN L /\ aff_dim E = &2 /\ p IN relative_interior e /\ p IN relative_interior E /\
     (!S. S IN L /\ p IN S ==> E face_of S) /\ e SUBSET E
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `d0:real`; `b:(real^2->bool)->real^2`]
    MOI_LGB1_CUT_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_lgb1_cones tt (h:real^N->real^3) kk L (g:real^2->real^N) phi a b` THEN
    REWRITE_TAC[moi_lgb1_cones] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "inL") (LABEL_TAC "cases")))) THEN
  ABBREV_TAC `gp = moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)) g h' a` THEN
  SUBGOAL_THEN `(p:real^2) IN e` ASSUME_TAC THENL
   [MP_TAC(ISPEC `e:real^2->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(p:real^2) IN relative_interior e` THEN SET_TAC[];
    ALL_TAC] THEN
  (* E is moved *)
  SUBGOAL_THEN `E IN moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)` ASSUME_TAC THENL
   [USE_THEN "cases" (MP_TAC o SPEC `e:real^2->bool`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN2 STRIP_ASSUME_TAC
      (X_CHOOSE_THEN `R0:real^2->bool` (X_CHOOSE_THEN `S0:real^3->bool` STRIP_ASSUME_TAC))) THENL
     [SUBGOAL_THEN `(e:real^2->bool) face_of E` ASSUME_TAC THENL
       [SUBGOAL_THEN `e INTER E:real^2->bool = e` (SUBST1_TAC o SYM) THENL
         [UNDISCH_TAC `(e:real^2->bool) SUBSET E` THEN SET_TAC[]; ALL_TAC] THEN
        ASM_MESON_TAC[simplicial_complex];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`E:real^2->bool`; `e:real^2->bool`; `E:real^2->bool`] SUBSET_OF_FACE_OF) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[SUBSET_REFL; DISJOINT; GSYM MEMBER_NOT_EMPTY] THEN
        EXISTS_TAC `p:real^2` THEN ASM_REWRITE_TAC[IN_INTER];
        DISCH_TAC THEN MP_TAC(ISPECL [`E:real^2->bool`; `e:real^2->bool`] AFF_DIM_SUBSET) THEN
        ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
      SUBGOAL_THEN `(p:real^2) IN R0` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`a:real^2->real^3`; `R0:real^2->bool`; `S0:real^3->bool`]
          MOI_LGB1_CELL_SUBSET) THEN
        UNDISCH_TAC `e SUBSET moi_lgb1_cell (a:real^2->real^3) R0 S0` THEN
        UNDISCH_TAC `(p:real^2) IN e` THEN SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(R0:real^2->bool) IN L` ASSUME_TAC THENL
       [UNDISCH_TAC `R0 IN moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)` THEN
        REWRITE_TAC[moi_lgb1_lm; IN_ELIM_THM] THEN SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `E:real^2->bool = R0` (fun th -> ASM_REWRITE_TAC[th]) THEN
      MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`E:real^2->bool`; `R0:real^2->bool`] FACE_OF_AFF_DIM_LT) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[] THEN ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
        MP_TAC(ISPEC `R0:real^2->bool` AFF_DIM_LE_UNIV) THEN REWRITE_TAC[DIMINDEX_2] THEN
        ASM_REWRITE_TAC[] THEN INT_ARITH_TAC]];
    ALL_TAC] THEN
  (* the triangles lie in E *)
  SUBGOAL_THEN `!r. r IN moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)) a
                       (IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)) b /\
                    e SUBSET r ==> r SUBSET E` (LABEL_TAC "inE") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "inL" (MP_TAC o SPEC `r:real^2->bool`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `R:real^2->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `E:real^2->bool = R` (fun th -> ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`E:real^2->bool`; `R:real^2->bool`] FACE_OF_AFF_DIM_LT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (term_match [] `!S. S IN L /\ (p:real^2) IN S ==> E face_of S`) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
      MP_TAC(ISPEC `R:real^2->bool` AFF_DIM_LE_UNIV) THEN REWRITE_TAC[DIMINDEX_2] THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(r1:real^2->bool) SUBSET E /\ (r2:real^2->bool) SUBSET E` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "inE" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `d0:real`; `b:(real^2->bool)->real^2`;
                 `e:real^2->bool`; `r1:real^2->bool`; `r2:real^2->bool`; `s:real^N->bool`;
                 `s':real^N->bool`; `E:real^2->bool`; `p:real^2`] MOI_LGB1_FOLD_A2) THEN
  ASM_REWRITE_TAC[]);;

(* Fold case B1: the L-carrier of the edge is a moved L-edge; it would lie *)
(* in a wall plane, hence in the frontier, where an edge has one triangle. *)

let MOI_LGB1_FOLD_B1 = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a d0 b
    e r1 r2 s E p.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     moi_lgb1_sml tt u h h' kk L g a d0 /\ moi_lgb1_cones tt h kk L g phi a b /\
     e IN moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                       (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) b /\
     r1 IN moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                        (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) b /\
     r2 IN moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                        (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) b /\
     ~(r1 = r2) /\ aff_dim e = &1 /\ aff_dim r1 = &2 /\ aff_dim r2 = &2 /\
     e SUBSET r1 /\ e SUBSET r2 /\
     s IN tt /\ aff_dim s = &2 /\
     IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a) e SUBSET s /\
     E IN L /\ aff_dim E = &1 /\ p IN relative_interior e /\ e SUBSET E /\
     ~(E INTER moi_lgb1_kv L g kk = {})
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `d0:real`; `b:(real^2->bool)->real^2`]
    MOI_LGB1_CUT_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_lgb1_cones tt (h:real^N->real^3) kk L (g:real^2->real^N) phi a b` THEN
    REWRITE_TAC[moi_lgb1_cones] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  MP_TAC(ISPECL [`moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)) a
                    (IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)) b`;
                 `e:real^2->bool`; `r1:real^2->bool`; `r2:real^2->bool`]
    MOI_LGB1_FOLD_FRONTIER) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `E IN moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[moi_lgb1_lm; IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `E IN moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LGB1_LM_L3 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^2) IN e` ASSUME_TAC THENL
   [MP_TAC(ISPEC `e:real^2->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(p:real^2) IN relative_interior e` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!q. q IN e ==> (a:real^2->real^3) q IN IMAGE (h:real^N->real^3) s /\
                               s IN moi_lgb1_th tt kk` ASSUME_TAC THENL
   [X_GEN_TAC `q:real^2` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                   `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                   `a:real^2->real^3`; `d0:real`; `E:real^2->bool`; `q:real^2`;
                   `s:real^N->bool`] MOI_LGB1_MOVED_PT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk))
                     g h' a) e SUBSET s` THEN
      UNDISCH_TAC `(q:real^2) IN e` THEN SET_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `s IN moi_lgb1_th (tt:(real^N->bool)->bool) kk` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `s:real^N->bool`] MOI_LGB1_TH_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `lh:real^N->real^3` (X_CHOOSE_THEN `yh:real^3`
       STRIP_ASSUME_TAC)) ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)`;
                 `a:real^2->real^3`; `IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)`;
                 `E:real^2->bool`] MOI_LGB1_SETUP_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_LGB1_CUTSETUP THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `u:real^N->bool`; `h':real^3->real^N`;
                          `Q:real^N->bool`; `hs:real^3->bool`; `phi:real^2->real^3`;
                          `rk:real^2->num`; `d0:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_THEN `l:real^2->real^3`
      (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) ASSUME_TAC)))) THEN
  SUBGOAL_THEN `aff_dim (IMAGE (a:real^2->real^3) e) = &1 /\ aff_dim (IMAGE a E) = &1`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [TRANS_TAC EQ_TRANS `aff_dim (e:real^2->bool)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_LGB1_AFF_DIM_INJ THEN
        MAP_EVERY EXISTS_TAC [`l:real^2->real^3`; `y:real^3`] THEN ASM_REWRITE_TAC[] THEN
        REPEAT CONJ_TAC THENL
         [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
          UNDISCH_TAC `(e:real^2->bool) SUBSET E` THEN ASM SET_TAC[];
          UNDISCH_TAC `(e:real^2->bool) SUBSET E` THEN ASM SET_TAC[]];
        ASM_REWRITE_TAC[]];
      TRANS_TAC EQ_TRANS `aff_dim (E:real^2->bool)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_LGB1_AFF_DIM_INJ THEN
        MAP_EVERY EXISTS_TAC [`l:real^2->real^3`; `y:real^3`] THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `E:real^2->bool`; `IMAGE (h:real^N->real^3) s`]
    MOI_LGB1_IN_WALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[FUN_IN_IMAGE];
      SUBGOAL_THEN `aff_dim (IMAGE (h:real^N->real^3) s) = aff_dim s` SUBST1_TAC THENL
       [MATCH_MP_TAC MOI_LGB1_AFF_DIM_INJ THEN
        MAP_EVERY EXISTS_TAC [`lh:real^N->real^3`; `yh:real^3`] THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
        ASM_REWRITE_TAC[INT_LE_REFL]];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `affine hull (IMAGE (a:real^2->real^3) E)` THEN REWRITE_TAC[HULL_SUBSET] THEN
      SUBGOAL_THEN `affine hull (IMAGE (a:real^2->real^3) e) = affine hull (IMAGE a E)`
      (SUBST1_TAC o SYM) THENL
       [MATCH_MP_TAC AFF_DIM_EQ_AFFINE_HULL THEN
        ASM_SIMP_TAC[IMAGE_SUBSET; INT_LE_REFL];
        MATCH_MP_TAC HULL_MONO THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
        ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  STRIP_TAC THEN UNDISCH_TAC `(e:real^2->bool) SUBSET E` THEN
  UNDISCH_TAC `(E:real^2->bool) SUBSET relative_frontier std_triangle` THEN SET_TAC[]);;

(* Fold case B2 tools.  The chart image of an L3 simplex has its relative  *)
(* interior in the relative interior of the chart image of the smallest    *)
(* tt-simplex containing its g-image.                                       *)

let MOI_LGB1_MIN_RELINT = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs R sg.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\
     R IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\
     sg IN moi_lgb1_th tt kk /\ IMAGE g R SUBSET sg /\
     (!s'. s' IN tt /\ IMAGE g R SUBSET s' ==> sg SUBSET s')
     ==> relative_interior (IMAGE (h o g) R) SUBSET relative_interior (IMAGE h sg)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`] MOI_LGB1_H_SC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `R:real^2->bool`]
    MOI_LGB1_L3_A0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `IMAGE (h:real^N->real^3) sg IN IMAGE (IMAGE h) (moi_lgb1_th tt kk)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `convex (IMAGE (h:real^N->real^3) sg)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE ((h:real^N->real^3) o (g:real^2->real^N)) R SUBSET IMAGE h sg`
  ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z0:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z0:real^3) IN IMAGE (h:real^N->real^3) sg` ASSUME_TAC THENL
   [MP_TAC(ISPEC `IMAGE ((h:real^N->real^3) o (g:real^2->real^N)) R`
      RELATIVE_INTERIOR_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (h:real^N->real^3) sg`; `z0:real^3`] IN_RELATIVE_INTERIOR_OF_FACE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Fy:real^3->bool` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `Fy = IMAGE (h:real^N->real^3) sg` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN
  SUBGOAL_THEN `IMAGE ((h:real^N->real^3) o (g:real^2->real^N)) R SUBSET Fy` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_OF_FACE_OF THEN EXISTS_TAC `IMAGE (h:real^N->real^3) sg` THEN
    ASM_REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `z0:real^3` THEN
    ASM_REWRITE_TAC[IN_INTER] THEN ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Fy:real^3->bool) IN IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_complex (IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk))` THEN
    REWRITE_TAC[simplicial_complex] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `Fy:real^3->bool`] MOI_LGB1_H_INV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f0:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "feq") (CONJUNCTS_THEN2 (LABEL_TAC "finv") (K ALL_TAC))))) THEN
  SUBGOAL_THEN `IMAGE (g:real^2->real^N) R SUBSET f0` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    USE_THEN "finv" (SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `(g:real^2->real^N) x IN u` ASSUME_TAC THENL
     [UNDISCH_TAC `IMAGE (g:real^2->real^N) R SUBSET u` THEN
      UNDISCH_TAC `(x:real^2) IN R` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(h:real^N->real^3) ((g:real^2->real^N) x)` THEN
    CONJ_TAC THENL
     [MP_TAC(MATCH_MP (SPEC `(g:real^2->real^N) x`
        (ASSUME `!x. x IN u ==> (h':real^3->real^N) ((h:real^N->real^3) x) = x /\
                                h x IN IMAGE h u`))
        (ASSUME `(g:real^2->real^N) x IN u`)) THEN SIMP_TAC[];
      UNDISCH_TAC `IMAGE ((h:real^N->real^3) o (g:real^2->real^N)) R SUBSET Fy` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(sg:real^N->bool) SUBSET f0` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!s'. s' IN tt /\ IMAGE (g:real^2->real^N) R SUBSET s'
                               ==> (sg:real^N->bool) SUBSET s'`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `f0:real^N->bool`] MOI_LGB1_TH_FACTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `~(Fy = IMAGE (h:real^N->real^3) sg)` THEN REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[FACE_OF_IMP_SUBSET];
    USE_THEN "feq" SUBST1_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]]);;

let MOI_LGB1_TWO_POINTS = prove
 (`!s:real^N->bool. &1 <= aff_dim s ==> ?x y. x IN s /\ y IN s /\ ~(x = y)`,
  GEN_TAC THEN MATCH_MP_TAC(TAUT `(~q ==> ~p) ==> p ==> q`) THEN
  REWRITE_TAC[NOT_EXISTS_THM; DE_MORGAN_THM] THEN DISCH_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN ASM_REWRITE_TAC[AFF_DIM_EMPTY] THENL
   [INT_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN DISCH_THEN(X_CHOOSE_TAC `x:real^N`) THEN
  SUBGOAL_THEN `s = {x:real^N}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_SING] THEN ASM_MESON_TAC[];
    REWRITE_TAC[AFF_DIM_SING] THEN INT_ARITH_TAC]);;

let MOI_LGB1_NONCOLL_DIM2 = prove
 (`!a b c:real^N. ~collinear {a,b,c} ==> aff_dim {a,b,c} = &2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT; DE_MORGAN_THM] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `{a:real^N,b,c}` AFF_DIM_AFFINE_INDEPENDENT) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `CARD {a:real^N,b,c} = 3` SUBST1_TAC THENL
   [SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    UNDISCH_TAC `~(a:real^N = b)` THEN UNDISCH_TAC `~(a:real^N = c)` THEN
    UNDISCH_TAC `~(b:real^N = c)` THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    SIMP_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    CONV_TAC INT_REDUCE_CONV]);;

(* Fold case B2, one side: an L'-triangle at the unmoved edge E inside the  *)
(* L-triangle R lies with R in the same 3-cell (the cell of the cone point  *)
(* is the 3-cell of the original image, by the side smallness and the      *)
(* planar same-side lemma).                                                 *)

let MOI_LGB1_FOLD_B2_TRI = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a d0 b
    e r R E s'.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     moi_lgb1_sml tt u h h' kk L g a d0 /\ moi_lgb1_sm2 tt h kk L g Q a d0 /\
     moi_lgb1_cones tt h kk L g phi a b /\
     r IN moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                       (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) b /\
     aff_dim r = &2 /\ e SUBSET r /\ aff_dim e = &1 /\
     R IN L /\ r SUBSET R /\
     E IN L /\ aff_dim E = &1 /\ e SUBSET E /\ E face_of R /\
     E INTER moi_lgb1_kv L g kk = {} /\
     s' IN tt /\ aff_dim s' = &3 /\
     IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a) r SUBSET s' /\
     ~(IMAGE g E INTER Q = {})
     ==> IMAGE g R SUBSET s'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`] MOI_LGB1_H_SC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `aff_dim (R:real^2->bool) = &2` ASSUME_TAC THENL
   [MP_TAC(ISPEC `R:real^2->bool` AFF_DIM_LE_UNIV) THEN
    MP_TAC(ISPECL [`r:real^2->bool`; `R:real^2->bool`] AFF_DIM_SUBSET) THEN
    ASM_REWRITE_TAC[DIMINDEX_2] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `convex (R:real^2->bool) /\ polytope R` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_POLYTOPE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`;
                 `moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)`;
                 `a:real^2->real^3`; `IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)`;
                 `b:(real^2->bool)->real^2`; `r:real^2->bool`] MOI_LGB1_CUT_PIECES) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN2 STRIP_ASSUME_TAC (DISJ_CASES_THEN2
    (X_CHOOSE_THEN `R9:real^2->bool` (X_CHOOSE_THEN `S9:real^3->bool` STRIP_ASSUME_TAC))
    (X_CHOOSE_THEN `P:real^2->bool` (X_CHOOSE_THEN `f:real^2->bool` STRIP_ASSUME_TAC)))) THENL
   [SUBGOAL_THEN `r:real^2->bool = R` SUBST_ALL_TAC THENL
     [SUBGOAL_THEN `(r:real^2->bool) face_of R` ASSUME_TAC THENL
       [SUBGOAL_THEN `r INTER R:real^2->bool = r` (SUBST1_TAC o SYM) THENL
         [UNDISCH_TAC `(r:real^2->bool) SUBSET R` THEN SET_TAC[]; ALL_TAC] THEN
        ASM_MESON_TAC[simplicial_complex];
        ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`r:real^2->bool`; `R:real^2->bool`] FACE_OF_AFF_DIM_LT) THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk))
                   g h' a) R SUBSET s'` THEN
    MATCH_MP_TAC(SET_RULE `!(f:real^2->real^N) g s t. (!x. x IN s ==> f x = g x)
                             ==> IMAGE f s SUBSET t ==> IMAGE g s SUBSET t`) THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_LGB1_GP_UNMOVED THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                          `u:real^N->bool`; `h:real^N->real^3`; `Q:real^N->bool`;
                          `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                          `R:real^2->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(R IN moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk))` THEN
    REWRITE_TAC[moi_lgb1_lm; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `aff_dim (r:real^2->bool) = &2` THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq (concl th) &&
      lhs (concl th) = `r:real^2->bool`)) THEN
    UNDISCH_TAC `aff_dim (moi_lgb1_cell (a:real^2->real^3) R9 S9) <= &1` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
    lhs (concl th) = `r:real^2->bool`)) THEN
  ABBREV_TAC `Kc = convex hull ((b:(real^2->bool)->real^2) P INSERT f)` THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `h:real^N->real^3`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `phi:real^2->real^3`;
                 `a:real^2->real^3`; `b:(real^2->bool)->real^2`; `P:real^2->bool`]
    MOI_LGB1_CONES_GOOD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `d0:real`; `P:real^2->bool`] MOI_LGB1_C2_CELL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `lp:real^2->real^3` (X_CHOOSE_THEN `yp:real^3`
       STRIP_ASSUME_TAC)) (K ALL_TAC)))))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `d0:real`; `P:real^2->bool`] MOI_LGB1_C2_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `RP:real^2->bool` (X_CHOOSE_THEN `SP:real^3->bool`
    (MAP_EVERY ASSUME_TAC o
     filter (fun th -> not (is_eq (concl th) && is_var (lhs (concl th)))) o CONJUNCTS))) THEN
  SUBGOAL_THEN `relative_interior Kc SUBSET relative_interior (P:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Kc" THEN MATCH_MP_TAC MOI_LGB1_CONE_RELINT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(b:(real^2->bool)->real^2) P IN Kc` ASSUME_TAC THENL
   [EXPAND_TAC "Kc" THEN MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
  SUBGOAL_THEN `~(relative_interior (Kc:real^2->bool) = {})` ASSUME_TAC THENL
   [EXPAND_TAC "Kc" THEN SIMP_TAC[CONVEX_CONVEX_HULL; RELATIVE_INTERIOR_EQ_EMPTY] THEN
    REWRITE_TAC[CONVEX_HULL_EQ_EMPTY; NOT_INSERT_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `(RP:real^2->bool) IN L` ASSUME_TAC THENL
   [UNDISCH_TAC `RP IN moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)` THEN
    REWRITE_TAC[moi_lgb1_lm; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `RP:real^2->bool = R` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC MOI_LGB1_CARRIER_UNIQUE THEN EXISTS_TAC `L:(real^2->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `relative_interior (Kc:real^2->bool) SUBSET relative_interior R` MP_TAC THENL
     [MATCH_MP_TAC SUBSET_RELATIVE_INTERIOR THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC AFF_DIM_EQ_AFFINE_HULL THEN ASM_REWRITE_TAC[INT_LE_REFL];
      ALL_TAC] THEN
    UNDISCH_TAC `relative_interior P SUBSET relative_interior (RP:real^2->bool)` THEN
    UNDISCH_TAC `relative_interior Kc SUBSET relative_interior (P:real^2->bool)` THEN
    UNDISCH_TAC `~(relative_interior (Kc:real^2->bool) = {})` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!q. q IN Kc ==> s' IN moi_lgb1_th (tt:(real^N->bool)->bool) kk /\
                                (a:real^2->real^3) q IN IMAGE (h:real^N->real^3) s'`
  (LABEL_TAC "kimg") THENL
   [X_GEN_TAC `q:real^2` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                   `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                   `a:real^2->real^3`; `d0:real`; `R:real^2->bool`; `q:real^2`;
                   `s':real^N->bool`] MOI_LGB1_MOVED_PT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk))
                     g h' a) Kc SUBSET s'` THEN
      UNDISCH_TAC `(q:real^2) IN Kc` THEN SET_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  USE_THEN "kimg" (MP_TAC o C MATCH_MP
    (ASSUME `(b:(real^2->bool)->real^2) P IN Kc`)) THEN STRIP_TAC THEN
  SUBGOAL_THEN `(a:real^2->real^3) ((b:(real^2->bool)->real^2) P) IN interior SP`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!s t (z:real^3). s SUBSET t /\ z IN s ==> z IN t`) THEN
    EXISTS_TAC `relative_interior (IMAGE (a:real^2->real^3) P)` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`a:real^2->real^3`; `lp:real^2->real^3`; `yp:real^3`; `P:real^2->bool`]
      MOI_LGB1_RELINT_AFFINE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `SP = IMAGE (h:real^N->real^3) s'` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC MOI_LGB1_INT_MEET THEN
    EXISTS_TAC `IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)` THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `(a:real^2->real^3) ((b:(real^2->bool)->real^2) P)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the smallest tt-simplex of g(R) and its chart image *)
  MP_TAC(ASSUME `moi_lgb_tlinear tt L (g:real^2->real^N)`) THEN REWRITE_TAC[moi_lgb_tlinear] THEN
  DISCH_THEN(MP_TAC o SPEC `R:real^2->bool` o last o CONJUNCTS) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:real^N->bool` STRIP_ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `IMAGE (g:real^2->real^N) R`; `s0:real^N->bool`]
    MOI_LGB_MIN_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `sg:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sgmin")))) THEN
  SUBGOAL_THEN `sg IN moi_lgb1_th (tt:(real^N->bool)->bool) kk` ASSUME_TAC THENL
   [UNDISCH_TAC `R IN moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)` THEN
    REWRITE_TAC[moi_lgb1_l3; moi_lgb1_th; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `s1:real^N->bool` STRIP_ASSUME_TAC o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `s3:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s1:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "sgmin" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `sg:real^N->bool`] MOI_LGB1_TH_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `lg:real^N->real^3` (X_CHOOSE_THEN `yg:real^3`
       STRIP_ASSUME_TAC)) ASSUME_TAC))) THEN
  SUBGOAL_THEN `aff_dim (sg:real^N->bool) = &3` ASSUME_TAC THENL
   [MATCH_MP_TAC(INT_ARITH `~(x:int <= &2) /\ x <= &3 ==> x = &3`) THEN CONJ_TAC THENL
     [DISCH_TAC THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `L:(real^2->bool)->bool`;
                     `g:real^2->real^N`; `Q:real^N->bool`] MOI_LGB1_TGEN_CLAUSES) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPECL [`R:real^2->bool`; `sg:real^N->bool`] o
        CONJUNCT1 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(IMAGE (g:real^2->real^N) E INTER Q = {})` THEN
      MP_TAC(ISPECL [`R:real^2->bool`; `E:real^2->bool`] FACE_OF_IMP_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      SUBGOAL_THEN `aff_dim (IMAGE (h:real^N->real^3) sg) = aff_dim sg` (SUBST1_TAC o SYM) THENL
       [MATCH_MP_TAC MOI_LGB1_AFF_DIM_INJ THEN
        MAP_EVERY EXISTS_TAC [`lg:real^N->real^3`; `yg:real^3`] THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
        MP_TAC(ISPEC `IMAGE (h:real^N->real^3) sg` AFF_DIM_LE_UNIV) THEN
        REWRITE_TAC[DIMINDEX_3]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h:real^N->real^3) sg IN IMAGE (IMAGE h) (moi_lgb1_th tt kk) /\
                aff_dim (IMAGE (h:real^N->real^3) sg) = &3 /\ convex (IMAGE h sg)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[FUN_IN_IMAGE];
      SUBGOAL_THEN `aff_dim (IMAGE (h:real^N->real^3) sg) = aff_dim sg` SUBST1_TAC THENL
       [MATCH_MP_TAC MOI_LGB1_AFF_DIM_INJ THEN
        MAP_EVERY EXISTS_TAC [`lg:real^N->real^3`; `yg:real^3`] THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
        ASM_REWRITE_TAC[]];
      MP_TAC(ISPEC `IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)` simplicial_complex) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; FUN_IN_IMAGE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior (IMAGE (h:real^N->real^3) sg) = relative_interior (IMAGE h sg)`
  ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RELATIVE_INTERIOR_INTERIOR THEN
    REWRITE_TAC[GSYM AFF_DIM_EQ_FULL; DIMINDEX_3] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `R:real^2->bool`; `sg:real^N->bool`] MOI_LGB1_MIN_RELINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `~(R:real^2->bool = {})` ASSUME_TAC THENL
   [UNDISCH_TAC `(b:(real^2->bool)->real^2) P IN Kc` THEN
    UNDISCH_TAC `(Kc:real^2->bool) SUBSET R` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `R:real^2->bool` MOI_LGB1_CEN) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `R:real^2->bool`]
    MOI_LGB1_L3_A0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `l0:real^2->real^3` (X_CHOOSE_THEN `y0:real^3`
       STRIP_ASSUME_TAC)) (K ALL_TAC)))) THEN
  SUBGOAL_THEN `(h:real^N->real^3) ((g:real^2->real^N) (moi_lgb1_cen R)) IN
                interior (IMAGE h sg)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `!s t (z:real^3). s SUBSET t /\ z IN s ==> z IN t`) THEN
    EXISTS_TAC `relative_interior (IMAGE ((h:real^N->real^3) o (g:real^2->real^N)) R)` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`(h:real^N->real^3) o (g:real^2->real^N)`; `l0:real^2->real^3`;
                   `y0:real^3`; `R:real^2->bool`] MOI_LGB1_RELINT_AFFINE) THEN
    ASM_REWRITE_TAC[o_THM] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[IN_IMAGE; o_THM] THEN EXISTS_TAC `moi_lgb1_cen R` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^2->real^3) (moi_lgb1_cen R) IN interior (IMAGE (h:real^N->real^3) sg)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lgb1_sm2 tt (h:real^N->real^3) kk L (g:real^2->real^N) Q a d0` THEN
    REWRITE_TAC[moi_lgb1_sm2] THEN
    DISCH_THEN(MP_TAC o SPECL [`R:real^2->bool`; `IMAGE (h:real^N->real^3) sg`] o
      CONJUNCT1 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`R:real^2->bool`; `E:real^2->bool`] MOI_LGB1_EDGE_HALFPLANE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN DISCH_TAC THENL
     [UNDISCH_TAC `aff_dim (E:real^2->bool) = &1` THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      UNDISCH_TAC `aff_dim (E:real^2->bool) = &1` THEN ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN
      INT_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `nv:real^2` (X_CHOOSE_THEN `be:real` STRIP_ASSUME_TAC))] THEN
  MP_TAC(ISPEC `e:real^2->bool` MOI_LGB1_TWO_POINTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[INT_LE_REFL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real^2` (X_CHOOSE_THEN `e2:real^2` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(e1:real^2) IN E /\ (e2:real^2) IN E /\ e1 IN P /\ e2 IN P`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(Kc:real^2->bool) SUBSET P` MP_TAC THENL
     [EXPAND_TAC "Kc" THEN MATCH_MP_TAC HULL_MINIMAL THEN
      ASM_REWRITE_TAC[INSERT_SUBSET] THEN
      ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET; FACE_OF_IMP_SUBSET];
      ALL_TAC] THEN
    UNDISCH_TAC `(e:real^2->bool) SUBSET E` THEN UNDISCH_TAC `(e:real^2->bool) SUBSET Kc` THEN
    UNDISCH_TAC `(e1:real^2) IN e` THEN UNDISCH_TAC `(e2:real^2) IN e` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~collinear {e1:real^2,e2,moi_lgb1_cen R}` ASSUME_TAC THENL
   [ASM_SIMP_TAC[COLLINEAR_3_AFFINE_HULL] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`R:real^2->bool`; `E:real^2->bool`]
      AFFINE_HULL_FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `aff_dim (E:real^2->bool) = &1` THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `moi_lgb1_cen R`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `!s t (z:real^2). s SUBSET t /\ z IN s ==> z IN t`) THEN
    EXISTS_TAC `affine hull {e1:real^2,e2}` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HULL_MONO THEN ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET];
    ALL_TAC] THEN
  ABBREV_TAC `T0 = convex hull {e1:real^2,e2,moi_lgb1_cen R}` THEN
  SUBGOAL_THEN `aff_dim (T0:real^2->bool) = &2 /\ convex T0 /\ T0 SUBSET R /\
                e1 IN T0 /\ e2 IN T0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "T0" THEN REWRITE_TAC[CONVEX_CONVEX_HULL; AFF_DIM_CONVEX_HULL] THEN
    ASM_SIMP_TAC[MOI_LGB1_NONCOLL_DIM2] THEN REPEAT CONJ_TAC THEN EXPAND_TAC "T0" THENL
     [MATCH_MP_TAC HULL_MINIMAL THEN ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
      MP_TAC(ISPECL [`R:real^2->bool`; `E:real^2->bool`] FACE_OF_IMP_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
      MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`P:real^2->bool`; `T0:real^2->bool`; `e1:real^2`; `e2:real^2`;
                 `nv:real^2`; `be:real`] MOI_LGB1_SAME_SIDE_2D) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (term_match [] `!x:real^2. x IN R ==> nv dot x <= be`) (concl th))) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `y1:real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)`;
                 `a:real^2->real^3`; `IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)`;
                 `R:real^2->bool`] MOI_LGB1_SETUP_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_LGB1_CUTSETUP THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `u:real^N->bool`; `h':real^3->real^N`;
                          `Q:real^N->bool`; `hs:real^3->bool`; `phi:real^2->real^3`;
                          `rk:real^2->num`; `d0:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (X_CHOOSE_THEN `la:real^2->real^3`
      (X_CHOOSE_THEN `ya:real^3` STRIP_ASSUME_TAC)) (K ALL_TAC))))) THEN
  SUBGOAL_THEN `E IN moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `g:real^2->real^N`;
                   `moi_lgb1_th (tt:(real^N->bool)->bool) kk`] MOI_LGB1_L3_SC) THEN
    ASM_REWRITE_TAC[simplicial_complex] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `E:real^2->bool`] MOI_LGB1_UNMOVED_A0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "ea0")] THEN
  SUBGOAL_THEN `IMAGE (a:real^2->real^3) T0 SUBSET IMAGE (h:real^N->real^3) sg` ASSUME_TAC THENL
   [EXPAND_TAC "T0" THEN
    MP_TAC(ISPECL [`a:real^2->real^3`; `la:real^2->real^3`; `ya:real^3`;
                   `{e1:real^2,e2,moi_lgb1_cen R}`] MOI_LGA_HULL_IMAGE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (term_match [] `!x. x IN (R:real^2->bool) ==> (a:real^2->real^3) x = la x + ya`)
          (concl th))) THEN
      UNDISCH_TAC `(T0:real^2->bool) SUBSET R` THEN
      UNDISCH_TAC `(x:real^2) IN T0` THEN SET_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC HULL_MINIMAL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IMAGE_CLAUSES; INSERT_SUBSET; EMPTY_SUBSET] THEN
    SUBGOAL_THEN `(E:real^2->bool) SUBSET R` ASSUME_TAC THENL
     [ASM_MESON_TAC[FACE_OF_IMP_SUBSET]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `(a:real^2->real^3) e1 = h ((g:real^2->real^N) e1)` SUBST1_TAC THENL
       [USE_THEN "ea0" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN
      UNDISCH_TAC `IMAGE (g:real^2->real^N) R SUBSET sg` THEN
      UNDISCH_TAC `(e1:real^2) IN E` THEN UNDISCH_TAC `(E:real^2->bool) SUBSET R` THEN SET_TAC[];
      SUBGOAL_THEN `(a:real^2->real^3) e2 = h ((g:real^2->real^N) e2)` SUBST1_TAC THENL
       [USE_THEN "ea0" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN
      UNDISCH_TAC `IMAGE (g:real^2->real^N) R SUBSET sg` THEN
      UNDISCH_TAC `(e2:real^2) IN E` THEN UNDISCH_TAC `(E:real^2->bool) SUBSET R` THEN SET_TAC[];
      MP_TAC(ISPEC `IMAGE (h:real^N->real^3) sg` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(a:real^2->real^3) (moi_lgb1_cen R) IN interior (IMAGE (h:real^N->real^3) sg)` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^2->real^3) y1 IN interior (IMAGE (h:real^N->real^3) s')`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!s t (z:real^3). s SUBSET t /\ z IN s ==> z IN t`) THEN
    EXISTS_TAC `relative_interior (IMAGE (a:real^2->real^3) P)` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`a:real^2->real^3`; `lp:real^2->real^3`; `yp:real^3`; `P:real^2->bool`]
      MOI_LGB1_RELINT_AFFINE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN
    MP_TAC(ISPEC `P:real^2->bool` INTERIOR_SUBSET_RELATIVE_INTERIOR) THEN
    UNDISCH_TAC `(y1:real^2) IN interior P` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h:real^N->real^3) s' = IMAGE h sg` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LGB1_INT_MEET THEN
    EXISTS_TAC `IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)` THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `(a:real^2->real^3) y1` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (a:real^2->real^3) T0 SUBSET IMAGE (h:real^N->real^3) sg` THEN
    MP_TAC(ISPEC `T0:real^2->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(y1:real^2) IN interior T0` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!X. X SUBSET u ==> IMAGE (h':real^3->real^N) (IMAGE (h:real^N->real^3) X) = X`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM IMAGE_o] THEN
    MATCH_MP_TAC(SET_RULE `!(f:real^N->real^N) s. (!x. x IN s ==> f x = x) ==> IMAGE f s = s`) THEN
    REWRITE_TAC[o_THM] THEN X_GEN_TAC `q:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(q:real^N) IN u` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(MATCH_MP (SPEC `q:real^N`
      (ASSUME `!x. x IN u ==> (h':real^3->real^N) ((h:real^N->real^3) x) = x /\
                              h x IN IMAGE h u`))
      (ASSUME `(q:real^N) IN u`)) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sg:real^N->bool = s'` (fun th -> ASM_REWRITE_TAC[SYM th]) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `s':real^N->bool`] MOI_LGB1_TH_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_X_ASSUM(fun th -> if is_forall (concl th) &&
      can (term_match [] `!X. X SUBSET u ==> IMAGE (h':real^3->real^N) (IMAGE (h:real^N->real^3) X) = X`)
        (concl th) then
      MP_TAC(SPEC `sg:real^N->bool` th) THEN MP_TAC(SPEC `s':real^N->bool` th) else NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN SIMP_TAC[]);;

(* Fold case B2: the L-carrier of the edge is an unmoved L-edge E; the two *)
(* L'-triangles lie in the two L-triangles at E, with their original      *)
(* 3-cells, so the input fold clause applies.                              *)

let MOI_LGB1_FOLD_B2 = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a d0 b
    e r1 r2 s s' E p.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     moi_lgb1_sml tt u h h' kk L g a d0 /\ moi_lgb1_sm2 tt h kk L g Q a d0 /\
     moi_lgb1_cones tt h kk L g phi a b /\
     e IN moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                       (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) b /\
     r1 IN moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                        (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) b /\
     r2 IN moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                        (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) b /\
     ~(r1 = r2) /\ aff_dim e = &1 /\ aff_dim r1 = &2 /\ aff_dim r2 = &2 /\
     e SUBSET r1 /\ e SUBSET r2 /\
     s IN tt /\ aff_dim s = &2 /\
     IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a) e SUBSET s /\
     ~(IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a) e INTER
       (Q UNION kk) = {}) /\
     s' IN tt /\ aff_dim s' = &3 /\
     IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a) r1 UNION
     IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a) r2 SUBSET s' /\
     E IN L /\ aff_dim E = &1 /\ p IN relative_interior e /\ p IN relative_interior E /\
     (!S. S IN L /\ p IN S ==> E face_of S) /\ e SUBSET E /\
     E INTER moi_lgb1_kv L g kk = {}
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `d0:real`; `b:(real^2->bool)->real^2`]
    MOI_LGB1_CUT_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_lgb1_cones tt (h:real^N->real^3) kk L (g:real^2->real^N) phi a b` THEN
    REWRITE_TAC[moi_lgb1_cones] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "inL") (K ALL_TAC)))) THEN
  SUBGOAL_THEN `(p:real^2) IN e /\ (p:real^2) IN E` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `e:real^2->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(p:real^2) IN relative_interior e` THEN
    UNDISCH_TAC `(e:real^2->bool) SUBSET E` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!q. q IN E ==> moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk))
                                 g h' a q = g q` (LABEL_TAC "ge") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_LGB1_GP_UNMOVED THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                          `u:real^N->bool`; `h:real^N->real^3`; `Q:real^N->bool`;
                          `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                          `E:real^2->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!X. X SUBSET E
                    ==> IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk))
                                g h' a) X = IMAGE g X` (LABEL_TAC "gim") THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(SET_RULE `!s (f:real^2->real^N) g. (!x. x IN s ==> f x = g x)
                             ==> IMAGE f s = IMAGE g s`) THEN
    X_GEN_TAC `q:real^2` THEN DISCH_TAC THEN USE_THEN "ge" MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g:real^2->real^N) e SUBSET s` ASSUME_TAC THENL
   [USE_THEN "gim" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th
      (ASSUME `(e:real^2->bool) SUBSET E`))]) THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g:real^2->real^N) E SUBSET s` ASSUME_TAC THENL
   [MP_TAC(ASSUME `moi_lgb_tlinear tt L (g:real^2->real^N)`) THEN
    REWRITE_TAC[moi_lgb_tlinear] THEN
    DISCH_THEN(MP_TAC o SPEC `E:real^2->bool` o last o CONJUNCTS) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `sE:real^N->bool` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `lE:real^2->real^N` (X_CHOOSE_THEN `yE:real^N` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `(s INTER sE:real^N->bool) face_of sE` ASSUME_TAC THENL
     [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
    SUBGOAL_THEN `(g:real^2->real^N) p IN relative_interior (IMAGE g E)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`g:real^2->real^N`; `lE:real^2->real^N`; `yE:real^N`; `E:real^2->bool`]
        MOI_LGB1_RELINT_AFFINE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
        DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s INTER sE:real^N->bool` THEN
    REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC SUBSET_OF_FACE_OF THEN
    EXISTS_TAC `sE:real^N->bool` THEN ASM_REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `(g:real^2->real^N) p` THEN ASM_REWRITE_TAC[IN_INTER] THEN
    UNDISCH_TAC `IMAGE (g:real^2->real^N) e SUBSET s` THEN
    UNDISCH_TAC `IMAGE (g:real^2->real^N) E SUBSET sE` THEN
    UNDISCH_TAC `(p:real^2) IN e` THEN UNDISCH_TAC `(p:real^2) IN E` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(IMAGE (g:real^2->real^N) E INTER Q = {})` ASSUME_TAC THENL
   [UNDISCH_TAC `~(IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk))
                   g h' a) e INTER (Q UNION kk) = {})` THEN
    USE_THEN "gim" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `(e:real^2->bool) SUBSET E`)]) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_UNION] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "qk"))) THEN
    EXISTS_TAC `y:real^N` THEN
    SUBGOAL_THEN `(y:real^N) IN IMAGE (g:real^2->real^N) E` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^N) IN IMAGE (g:real^2->real^N) e` THEN UNDISCH_TAC `(e:real^2->bool) SUBSET E` THEN
      SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `g:real^2->real^N`; `kk:real^N->bool`;
                   `E:real^2->bool`; `y:real^N`] MOI_LGB1_NO_KK) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "qk" MP_TAC THEN CONV_TAC TAUT;
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. r IN moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)) a
                       (IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)) b /\
                    aff_dim r = &2 /\ e SUBSET r
                    ==> ?R. R IN L /\ r SUBSET R /\ E face_of R /\ aff_dim R = &2`
  (LABEL_TAC "rR") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "inL" (MP_TAC o SPEC `r:real^2->bool`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `R:real^2->bool` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!S. S IN L /\ (p:real^2) IN S ==> E face_of S`) (concl th))) THEN
      ASM SET_TAC[];
      MP_TAC(ISPEC `R:real^2->bool` AFF_DIM_LE_UNIV) THEN
      MP_TAC(ISPECL [`r:real^2->bool`; `R:real^2->bool`] AFF_DIM_SUBSET) THEN
      ASM_REWRITE_TAC[DIMINDEX_2] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "rR" (MP_TAC o SPEC `r1:real^2->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `R1:real^2->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "rR" (MP_TAC o SPEC `r2:real^2->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `R2:real^2->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(R1:real^2->bool = R2)` ASSUME_TAC THENL
   [DISCH_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      concl th = `R1:real^2->bool = R2`)) THEN
    MP_TAC(ISPECL [`R2:real^2->bool`; `E:real^2->bool`] MOI_LGB1_EDGE_HALFPLANE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_POLYTOPE];
        DISCH_TAC THEN UNDISCH_TAC `aff_dim (E:real^2->bool) = &1` THEN ASM_REWRITE_TAC[] THEN
        INT_ARITH_TAC;
        DISCH_TAC THEN UNDISCH_TAC `aff_dim (E:real^2->bool) = &1` THEN
        ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC];
      DISCH_THEN(X_CHOOSE_THEN `nv:real^2` (X_CHOOSE_THEN `be:real` STRIP_ASSUME_TAC))] THEN
    MP_TAC(ISPEC `e:real^2->bool` MOI_LGB1_TWO_POINTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[INT_LE_REFL]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e1:real^2` (X_CHOOSE_THEN `e2:real^2` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`r1:real^2->bool`; `r2:real^2->bool`; `e1:real^2`; `e2:real^2`;
                   `nv:real^2`; `be:real`] MOI_LGB1_SAME_SIDE_2D) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
        ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
        ASM SET_TAC[]; ASM SET_TAC[]; ASM SET_TAC[]; ASM SET_TAC[];
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
          can (term_match [] `!x:real^2. x IN E ==> nv dot x = be`) (concl th))) THEN
        ASM SET_TAC[];
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
          can (term_match [] `!x:real^2. x IN E ==> nv dot x = be`) (concl th))) THEN
        ASM SET_TAC[];
        X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
          can (term_match [] `!x:real^2. x IN R2 ==> nv dot x <= be`) (concl th))) THEN
        ASM SET_TAC[];
        X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
          can (term_match [] `!x:real^2. x IN R2 ==> nv dot x <= be`) (concl th))) THEN
        ASM SET_TAC[]];
      ALL_TAC] THEN
    DISCH_TAC THEN UNDISCH_TAC `~(r1:real^2->bool = r2)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_LGB1_CARRIER_UNIQUE THEN
    EXISTS_TAC `moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)) a
                  (IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)) b` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `r1:real^2->bool` INTERIOR_SUBSET_RELATIVE_INTERIOR) THEN
    MP_TAC(ISPEC `r2:real^2->bool` INTERIOR_SUBSET_RELATIVE_INTERIOR) THEN
    UNDISCH_TAC `~(interior r1 INTER interior r2:real^2->bool = {})` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g:real^2->real^N) R1 SUBSET s' /\ IMAGE g R2 SUBSET s'`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_LGB1_FOLD_B2_TRI THENL
     [MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
        `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
        `L:(real^2->bool)->bool`;
        `Q:real^N->bool`; `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
        `a:real^2->real^3`; `d0:real`; `b:(real^2->bool)->real^2`; `e:real^2->bool`;
        `r1:real^2->bool`; `E:real^2->bool`];
      MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
        `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
        `L:(real^2->bool)->bool`;
        `Q:real^N->bool`; `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
        `a:real^2->real^3`; `d0:real`; `b:(real^2->bool)->real^2`; `e:real^2->bool`;
        `r2:real^2->bool`; `E:real^2->bool`]] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `L:(real^2->bool)->bool`; `g:real^2->real^N`;
                 `Q:real^N->bool`] MOI_LGB1_TGEN_CLAUSES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`E:real^2->bool`; `R1:real^2->bool`; `R2:real^2->bool`;
    `s:real^N->bool`] o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[FACE_OF_IMP_SUBSET];
    DISCH_THEN(MP_TAC o SPEC `s':real^N->bool`) THEN ASM_REWRITE_TAC[UNION_SUBSET]]);;

let MOI_LGB1_GP_CLAUSE3 = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a d0 b.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     moi_lgb1_sml tt u h h' kk L g a d0 /\ moi_lgb1_sm2 tt h kk L g Q a d0 /\
     moi_lgb1_cones tt h kk L g phi a b
     ==> !e r1 r2 s.
           e IN moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                             (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) b /\
           r1 IN moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                              (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) b /\
           r2 IN moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L g kk)) a
                              (IMAGE (IMAGE h) (moi_lgb1_th tt kk)) b /\
           ~(r1 = r2) /\ aff_dim e = &1 /\ aff_dim r1 = &2 /\ aff_dim r2 = &2 /\
           e SUBSET r1 /\ e SUBSET r2 /\ s IN tt /\ aff_dim s = &2 /\
           IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a) e SUBSET s /\
           ~(IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a) e INTER
             (Q UNION kk) = {})
           ==> !s'. s' IN tt /\ aff_dim s' = &3
                    ==> ~(IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a) r1
                          UNION
                          IMAGE (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a) r2
                          SUBSET s')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:real^2->bool`; `r1:real^2->bool`; `r2:real^2->bool`;
                       `s:real^N->bool`] THEN STRIP_TAC THEN
  X_GEN_TAC `s':real^N->bool` THEN STRIP_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `d0:real`; `b:(real^2->bool)->real^2`]
    MOI_LGB1_CUT_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_lgb1_cones tt (h:real^N->real^3) kk L (g:real^2->real^N) phi a b` THEN
    REWRITE_TAC[moi_lgb1_cones] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "un")
    (CONJUNCTS_THEN2 (LABEL_TAC "inL") (K ALL_TAC)))) THEN
  SUBGOAL_THEN `?p:real^2. p IN relative_interior e` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN
    SUBGOAL_THEN `convex (e:real^2->bool) /\ ~(e = {})` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
        DISCH_TAC THEN UNDISCH_TAC `aff_dim (e:real^2->bool) = &1` THEN
        ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC];
      ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^2) IN e` ASSUME_TAC THENL
   [MP_TAC(ISPEC `e:real^2->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(p:real^2) IN relative_interior e` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `p:real^2`] MOI_LGB1_CARRIER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "un" (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `e:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `E:real^2->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "emin")))) THEN
  USE_THEN "inL" (MP_TAC o SPEC `e:real^2->bool`) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real^2->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(E:real^2->bool) face_of R` ASSUME_TAC THENL
   [USE_THEN "emin" MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^2->bool) SUBSET E` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_OF_FACE_OF THEN EXISTS_TAC `R:real^2->bool` THEN
    ASM_REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `p:real^2` THEN
    ASM_REWRITE_TAC[IN_INTER] THEN
    MP_TAC(ISPEC `E:real^2->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(p:real^2) IN relative_interior E` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (E:real^2->bool) = &1 \/ aff_dim E = &2` MP_TAC THENL
   [MP_TAC(ISPEC `E:real^2->bool` AFF_DIM_LE_UNIV) THEN
    MP_TAC(ISPECL [`e:real^2->bool`; `E:real^2->bool`] AFF_DIM_SUBSET) THEN
    ASM_REWRITE_TAC[DIMINDEX_2] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THENL
   [ASM_CASES_TAC `E INTER moi_lgb1_kv L (g:real^2->real^N) kk = {}` THENL
     [MATCH_MP_TAC MOI_LGB1_FOLD_B2 THEN
      MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
        `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
        `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`; `hs:real^3->bool`;
        `phi:real^2->real^3`; `rk:real^2->num`; `a:real^2->real^3`; `d0:real`;
        `b:(real^2->bool)->real^2`; `e:real^2->bool`; `r1:real^2->bool`; `r2:real^2->bool`;
        `s:real^N->bool`; `s':real^N->bool`; `E:real^2->bool`; `p:real^2`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_LGB1_FOLD_B1 THEN
      MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
        `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
        `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`; `hs:real^3->bool`;
        `phi:real^2->real^3`; `rk:real^2->num`; `a:real^2->real^3`; `d0:real`;
        `b:(real^2->bool)->real^2`; `e:real^2->bool`; `r1:real^2->bool`; `r2:real^2->bool`;
        `s:real^N->bool`; `E:real^2->bool`; `p:real^2`] THEN
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC MOI_LGB1_FOLD_A THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
      `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
      `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`; `hs:real^3->bool`;
      `phi:real^2->real^3`; `rk:real^2->num`; `a:real^2->real^3`; `d0:real`;
      `b:(real^2->bool)->real^2`; `e:real^2->bool`; `r1:real^2->bool`; `r2:real^2->bool`;
      `s:real^N->bool`; `s':real^N->bool`; `E:real^2->bool`; `p:real^2`] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* C19. Assembly of the chart step.  The straight-line path in chart        *)
(* coordinates from h o g to the moved map stays, on the frontier, in the   *)
(* boundary near g, hence in w; the chart step itself.                      *)
(* ------------------------------------------------------------------------- *)

let MOI_LGB1_PATH_W = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a eta d0 w.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     moi_lgb1_near (moi_lgb1_l3 L g (moi_lgb1_th tt kk)) (\v. h (g v)) phi hs
                   (relative_frontier std_triangle) eta /\
     (!phi' a'. moi_lgb1_near (moi_lgb1_l3 L g (moi_lgb1_th tt kk)) (\v. h (g v)) phi' hs
                  (relative_frontier std_triangle) eta /\
                moi_lgb1_interp (moi_lgb1_l3 L g (moi_lgb1_th tt kk)) phi' a'
                ==> !R x. R IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\ x IN R
                          ==> a' x IN IMAGE h u /\ dist(h' (a' x),g x) < d0) /\
     (!x y. x IN relative_frontier std_triangle /\ y IN complex_boundary c /\
            dist(y,g x) < d0 ==> y IN w)
     ==> !t x. t IN interval[vec 0,vec 1] /\
               x IN UNIONS (moi_lgb1_lm L (moi_lgb1_kv L g kk)) /\
               x IN relative_frontier std_triangle
               ==> h' ((&1 - drop t) % h (g x) + drop t % a x) IN w`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "near") (CONJUNCTS_THEN2 (LABEL_TAC "small")
      (LABEL_TAC "wsm"))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  SUBGOAL_THEN `!x. x IN u ==> (x IN complex_boundary c <=>
                     hs = {z:real^3 | &0 <= z$3} /\ ((h:real^N->real^3) x)$3 = &0)`
  (LABEL_TAC "bd") THENL
   [UNDISCH_TAC `moi_lgb1_fix (c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs` THEN
    REWRITE_TAC[moi_lgb1_fix] THEN DISCH_THEN(ACCEPT_TAC o last o CONJUNCTS);
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real^1`; `x:real^2`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= drop t /\ drop t <= &1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(t:real^1) IN interval[vec 0,vec 1]` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC];
    ALL_TAC] THEN
  ABBREV_TAC `s = drop t` THEN
  UNDISCH_TAC `x IN UNIONS (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk))` THEN
  REWRITE_TAC[IN_UNIONS] THEN DISCH_THEN(X_CHOOSE_THEN `R:real^2->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `R IN moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LGB1_LM_L3 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_lgb1_interp (moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)) phi a`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lgb1_mvd tt (h:real^N->real^3) kk L (g:real^2->real^N) hs phi rk a` THEN
    REWRITE_TAC[moi_lgb1_mvd] THEN STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  USE_THEN "small" (MP_TAC o SPECL
    [`\v. (&1 - s) % (h:real^N->real^3) ((g:real^2->real^N) v) + s % (phi:real^2->real^3) v`;
     `\y. (&1 - s) % (h:real^N->real^3) ((g:real^2->real^N) y) + s % (a:real^2->real^3) y`]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[moi_lgb1_near] THEN X_GEN_TAC `v:real^2` THEN DISCH_TAC THEN
      USE_THEN "near" (MP_TAC o SPEC `v:real^2` o REWRITE_RULE[moi_lgb1_near]) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
      SUBGOAL_THEN `(g:real^2->real^N) v IN u` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                       `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                       `L:(real^2->bool)->bool`; `g:real^2->real^N`; `{v:real^2}`]
          MOI_LGB1_L3_A0) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[IMAGE_CLAUSES; INSERT_SUBSET] THEN SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(h:real^N->real^3) ((g:real^2->real^N) v) IN hs` ASSUME_TAC THENL
       [MP_TAC(MATCH_MP (SPEC `(g:real^2->real^N) v`
          (ASSUME `!x. x IN u ==> (h':real^3->real^N) ((h:real^N->real^3) x) = x /\
                                  h x IN IMAGE h u`))
          (ASSUME `(g:real^2->real^N) v IN u`)) THEN
        UNDISCH_TAC `IMAGE (h:real^N->real^3) u SUBSET hs` THEN SET_TAC[];
        ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[VECTOR_ARITH `((&1 - s) % a + s % b) - a:real^3 = s % (b - a)`] THEN
        REWRITE_TAC[NORM_MUL] THEN
        MATCH_MP_TAC REAL_LET_TRANS THEN
        EXISTS_TAC `norm((phi:real^2->real^3) v - h ((g:real^2->real^N) v))` THEN
        ASM_REWRITE_TAC[] THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
        UNDISCH_TAC `&0 <= s` THEN UNDISCH_TAC `s <= &1` THEN REAL_ARITH_TAC;
        MATCH_MP_TAC IN_CONVEX_SET THEN ASM_REWRITE_TAC[];
        STRIP_TAC THEN
        REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
        FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th))) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                       `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                       `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                       `hs:real^3->bool`; `v:real^2`] MOI_LGB1_BD_CHAR) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN
          MP_TAC MOI_LTD_STD_TRIANGLE_BASIC THEN
          SIMP_TAC[relative_frontier; CLOSURE_CLOSED] THEN
          UNDISCH_TAC `(v:real^2) IN relative_frontier std_triangle` THEN
          SIMP_TAC[relative_frontier; CLOSURE_CLOSED; MOI_LTD_STD_TRIANGLE_BASIC] THEN SET_TAC[];
          ASM_REWRITE_TAC[] THEN SIMP_TAC[] THEN REAL_ARITH_TAC]];
      ALL_TAC] THEN
    REWRITE_TAC[moi_lgb1_interp] THEN CONJ_TAC THENL
     [X_GEN_TAC `r:real^2->bool` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                     `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                     `L:(real^2->bool)->bool`; `g:real^2->real^N`; `r:real^2->bool`]
        MOI_LGB1_L3_A0) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `l1:real^2->real^3` (X_CHOOSE_THEN `y1:real^3`
        STRIP_ASSUME_TAC) o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
      UNDISCH_TAC `moi_lgb1_interp (moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)) phi a` THEN
      REWRITE_TAC[moi_lgb1_interp] THEN
      DISCH_THEN(MP_TAC o SPEC `r:real^2->bool` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `l2:real^2->real^3` (X_CHOOSE_THEN `y2:real^3`
        STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`\x:real^2. (&1 - s) % (l1:real^2->real^3) x + s % (l2:real^2->real^3) x`;
                            `(&1 - s) % (y1:real^3) + s % (y2:real^3)`] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC LINEAR_COMPOSE_ADD THEN CONJ_TAC THEN
        MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN VECTOR_ARITH_TAC];
      X_GEN_TAC `v:real^2` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      UNDISCH_TAC `moi_lgb1_interp (moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)) phi a` THEN
      REWRITE_TAC[moi_lgb1_interp] THEN
      DISCH_THEN(MP_TAC o SPEC `v:real^2` o CONJUNCT2) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`R:real^2->bool`; `x:real^2`]) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  USE_THEN "wsm" MATCH_MP_TAC THEN EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `z = (&1 - s) % (h:real^N->real^3) ((g:real^2->real^N) x) +
                  s % (a:real^2->real^3) x` THEN
  MP_TAC(MATCH_MP (SPEC `z:real^3`
    (ASSUME `!z. z IN IMAGE (h:real^N->real^3) u ==> h ((h':real^3->real^N) z) = z /\
                                                     h' z IN u`))
    (ASSUME `(z:real^3) IN IMAGE (h:real^N->real^3) u`)) THEN
  STRIP_TAC THEN
  USE_THEN "bd" (fun th -> REWRITE_TAC[MATCH_MP th
    (ASSUME `(h':real^3->real^N) z IN u`)]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(g:real^2->real^N) x IN u` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `R:real^2->bool`]
      MOI_LGB1_L3_A0) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(x:real^2) IN R` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^2->real^N) x IN complex_boundary c` MP_TAC THENL
   [UNDISCH_TAC `moi_lt_singular_disk (c:(real^N->bool)->bool) g` THEN
    REWRITE_TAC[moi_lt_singular_disk] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "bd" (fun th -> REWRITE_TAC[MATCH_MP th
    (ASSUME `(g:real^2->real^N) x IN u`)]) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `R:real^2->bool`; `x:real^2`] MOI_LGB1_ZERO_PATTERN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_eq (concl th) &&
      lhs (concl th) = `(h:real^N->real^3) ((h':real^3->real^N) z)` then SUBST1_TAC th
      else NO_TAC) THEN
  EXPAND_TAC "z" THEN REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let MOI_LGB1_GP_HTPY = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a d0 w.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\ moi_lgb1_mvd tt h kk L g hs phi rk a /\
     moi_lgb1_sml tt u h h' kk L g a d0 /\
     IMAGE g (relative_frontier std_triangle) SUBSET w /\
     (!t x. t IN interval[vec 0,vec 1] /\
            x IN UNIONS (moi_lgb1_lm L (moi_lgb1_kv L g kk)) /\
            x IN relative_frontier std_triangle
            ==> h' ((&1 - drop t) % h (g x) + drop t % a x) IN w)
     ==> homotopic_loops w (g o std_triangle_loop)
           (moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L g kk)) g h' a o std_triangle_loop)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `d0:real`] MOI_LGB1_CUTSETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[moi_lgb1_cutsetup] THEN STRIP_TAC] THEN
  SUBGOAL_THEN `moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)) g h' a =
                (\x. if x IN UNIONS (moi_lgb1_lm L (moi_lgb1_kv L g kk)) then h' (a x)
                     else g x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; moi_lgb1_gp]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_LGB1H_HTPY THEN
  MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `u:real^N->bool`;
    `UNIONS {r | r IN L /\ ~(r IN moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk))}`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FINITE (L:(real^2->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    SUBGOAL_THEN `IMAGE (h:real^N->real^3) u = ball(vec 0,&1) INTER hs` SUBST1_TAC THENL
     [UNDISCH_TAC `moi_lgb1_fix (c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs` THEN
      REWRITE_TAC[moi_lgb1_fix] THEN DISCH_THEN(ACCEPT_TAC o el 5 o CONJUNCTS);
      MATCH_MP_TAC CONVEX_INTER THEN ASM_REWRITE_TAC[CONVEX_BALL]];
    MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `L:(real^2->bool)->bool` THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CLOSED; SUBSET]];
    MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `L:(real^2->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CLOSED]];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `UNIONS L = std_triangle`)) THEN
    UNDISCH_TAC `moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk) SUBSET L` THEN SET_TAC[];
    MP_TAC(ISPECL [`a:real^2->real^3`; `moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)`]
      MOI_REAL_PIECEWISE_AFFINE_UNIONS) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `L:(real^2->bool)->bool` THEN
        ASM_REWRITE_TAC[];
        X_GEN_TAC `r:real^2->bool` THEN DISCH_TAC THEN CONJ_TAC THENL
         [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_POLYTOPE; SUBSET];
          FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
            can (term_match [] `!r. r IN L /\ (?r'. r' IN mv /\ r SUBSET r')
                                   ==> ?l y. linear l /\ !x. x IN r ==> (a:real^2->real^3) x = l x + y`)
              (concl th))) THEN
          CONJ_TAC THENL [ASM SET_TAC[]; EXISTS_TAC `r:real^2->bool` THEN
                          ASM_REWRITE_TAC[SUBSET_REFL]]]];
      SIMP_TAC[]];
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                   `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                   `a:real^2->real^3`; `d0:real`; `x:real^2`] MOI_LGB1_GP_MOVED_FACTS) THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[IN_INTER] THEN X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                   `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                   `a:real^2->real^3`; `d0:real`; `x:real^2`] MOI_LGB1_GP_MOVED_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "gpx") (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "hh") (K ALL_TAC))))) THEN
    UNDISCH_TAC `x IN UNIONS {r | r IN L /\
                   ~(r IN moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk))}` THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^2->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)) g h' a x =
                  g x` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_LGB1_GP_UNMOVED THEN
      MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                            `u:real^N->bool`; `h:real^N->real^3`; `Q:real^N->bool`;
                            `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                            `r:real^2->bool`] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(r IN moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk))` THEN
      REWRITE_TAC[moi_lgb1_lm; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "hh" (SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
    USE_THEN "gpx" (SUBST1_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC]);;

(* The records of the moved configuration from the smallness facts.        *)

let MOI_LGB1_RECORDS = prove
 (`!(c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs phi rk a eta d0.
     moi_lgb1_fix c tt u h h' kk L g Q hs /\
     moi_lgb1_gen tt h kk L g phi rk /\
     moi_lgb1_near (moi_lgb1_l3 L g (moi_lgb1_th tt kk)) (\v. h (g v)) phi hs
                   (relative_frontier std_triangle) eta /\
     moi_lgb1_interp (moi_lgb1_l3 L g (moi_lgb1_th tt kk)) phi a /\
     (!R x. R IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\ x IN R
            ==> a x IN IMAGE h u /\ dist(h' (a x),g x) < d0) /\
     (!v. {v} IN L /\
          (!r. r IN L /\ v IN r ==> r IN moi_lgb1_l3 L g (moi_lgb1_th tt kk))
          ==> !x y. x IN UNIONS {r | r IN L /\ v IN r} /\
                    y IN UNIONS {r | r IN L /\ v IN r} /\ a x = a y ==> x = y) /\
     (!R S. R IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\
            S IN IMAGE (IMAGE h) (moi_lgb1_th tt kk) /\ ~(R = {}) /\
            h (g (moi_lgb1_cen R)) IN interior S
            ==> a (moi_lgb1_cen R) IN interior S) /\
     (!v. {v} IN moi_lgb1_l3 L g (moi_lgb1_th tt kk) /\ hs = {z:real^3 | &0 <= z$3}
          ==> ((phi v)$3 = &0 <=> v IN relative_frontier std_triangle)) /\
     (!R x y s. R IN moi_lgb1_lm L (moi_lgb1_kv L g kk) /\ x IN R /\
                dist(y,g x) < d0 /\ s IN tt /\ y IN s ==> s IN moi_lgb1_t3 tt kk) /\
     (!R R' x y. R IN L /\ R' IN L /\ DISJOINT R R' /\ x IN R /\
                 y IN IMAGE g R' /\ y IN Q /\
                 (?s. s IN tt /\ aff_dim s <= &1 /\ y IN s)
                 ==> d0 <= dist(g x,y))
     ==> moi_lgb1_mvd tt h kk L g hs phi rk a /\
         moi_lgb1_sml tt u h h' kk L g a d0 /\
         moi_lgb1_sm2 tt h kk L g Q a d0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[moi_lgb1_mvd; moi_lgb1_sml; moi_lgb1_sm2] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `R:real^2->bool` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                   `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                   `a:real^2->real^3`] MOI_LGB1_INJ_PAIR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`R:real^2->bool`; `R:real^2->bool`; `x:real^2`; `y:real^2`]) THEN
    ASM_REWRITE_TAC[UNION_IDEMPOT; INTER_IDEMPOT] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
    X_GEN_TAC `v:real^2` THEN DISCH_TAC THEN
    UNDISCH_TAC `moi_lgb1_near (moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk))
                   (\v. (h:real^N->real^3) (g v)) phi hs (relative_frontier std_triangle) eta` THEN
    REWRITE_TAC[moi_lgb1_near] THEN DISCH_THEN(MP_TAC o SPEC `v:real^2`) THEN
    ASM_SIMP_TAC[]]);;

(* The chart step.                                                          *)

let MOI_LGB1_CHART_STEP = prove
 (MOI_LGB_CHART_STEP,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                 `A:((real^N->bool)#(real^N->real^3)#(real^3->real^N)#(real^N->bool))->bool`;
                 `u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`]
    MOI_LGB1_ATLAS_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `?hs. moi_lgb1_fix (c:(real^N->bool)->bool) tt u h h' kk L (g:real^2->real^N) Q hs`
  (X_CHOOSE_TAC `hs:real^3->bool`) THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`] MOI_LGB1_CHART_HS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `hs:real^3->bool` THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[moi_lgb1_fix];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_LGB1_FIX_FACTS) THEN
  MP_TAC(ISPEC `L:(real^2->bool)->bool` MOI_LGB1_STAR_LEBESGUE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "leb"))) THEN
  MP_TAC(ISPECL [`g:real^2->real^N`; `std_triangle`; `rho:real`] MOI_LGB1_TWO_TO_ONE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MOI_LTD_STD_TRIANGLE_BASIC] THEN
    UNDISCH_TAC `moi_lt_singular_disk (c:(real^N->bool)->bool) g` THEN
    REWRITE_TAC[moi_lt_singular_disk] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `mu:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "two"))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`] MOI_LGB1_MARGIN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dm:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "marg"))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:real^2->real^N`; `w:real^N->bool`]
    MOI_LGB1_WSMALL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dw:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "wsm"))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`] MOI_LGB1_SKEL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ds:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "skel"))) THEN
  ABBREV_TAC `d0 = min e (min mu (min dm (min dw ds)))` THEN
  SUBGOAL_THEN `&0 < d0 /\ d0 <= e /\ d0 <= mu /\ d0 <= dm /\ d0 <= dw /\ d0 <= ds`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d0" THEN
    UNDISCH_TAC `&0 < e` THEN UNDISCH_TAC `&0 < mu` THEN UNDISCH_TAC `&0 < dm` THEN
    UNDISCH_TAC `&0 < dw` THEN UNDISCH_TAC `&0 < ds` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `d0:real`] MOI_LGB1_SMALL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sm"))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `eta:real`] MOI_LGB1_GEN_MOVES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:real^2->real^3` (X_CHOOSE_THEN `rk:real^2->num`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`L:(real^2->bool)->bool`; `g:real^2->real^N`;
                 `moi_lgb1_th (tt:(real^N->bool)->bool) kk`] MOI_LGB1_L3_SC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`moi_lgb1_l3 L (g:real^2->real^N) (moi_lgb1_th tt kk)`; `phi:real^2->real^3`]
    MOI_LGB1_INTERP_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `a:real^2->real^3`) THEN
  USE_THEN "sm" (MP_TAC o SPECL [`phi:real^2->real^3`; `a:real^2->real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `eta:real`; `d0:real`] MOI_LGB1_RECORDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN USE_THEN "marg" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`R:real^2->bool`; `x:real^2`; `y:real^N`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `ds:real` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "skel" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`R:real^2->bool`; `R':real^2->bool`] THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                 `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                 `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                 `a:real^2->real^3`; `d0:real`] MOI_LGB1_CONES_FROM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `b:(real^2->bool)->real^2`) THEN
  MAP_EVERY EXISTS_TAC
   [`moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)) g h' a`;
    `moi_lgb1_cut L (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)) a
                  (IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk)) b`] THEN
  SUBGOAL_THEN `!P. P IN moi_lgb1_c2 (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk)) a
                         (IMAGE (IMAGE (h:real^N->real^3)) (moi_lgb1_th tt kk))
                    ==> (b:(real^2->bool)->real^2) P IN relative_interior P` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lgb1_cones tt (h:real^N->real^3) kk L (g:real^2->real^N) phi a b` THEN
    REWRITE_TAC[moi_lgb1_cones] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN std_triangle
                    ==> dist(moi_lgb1_gp (moi_lgb1_lm L (moi_lgb1_kv L (g:real^2->real^N) kk))
                               g h' a x,g x) < d0` (LABEL_TAC "close") THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                   `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                   `a:real^2->real^3`; `d0:real`] MOI_LGB1_GP_CLOSE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                   `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                   `a:real^2->real^3`; `d0:real`; `b:(real^2->bool)->real^2`; `rho:real`]
      MOI_LGB1_GP_DISK) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `g':real^2->real^N` THEN STRIP_TAC THEN USE_THEN "two" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `d0:real` THEN ASM_SIMP_TAC[];
    REWRITE_TAC[moi_lgb_tgeneric] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                     `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                     `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                     `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                     `a:real^2->real^3`; `d0:real`; `b:(real^2->bool)->real^2`]
        MOI_LGB1_GP_TLINEAR) THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                     `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                     `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                     `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                     `a:real^2->real^3`; `d0:real`; `b:(real^2->bool)->real^2`]
        MOI_LGB1_GP_CLAUSE1) THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                     `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                     `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                     `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                     `a:real^2->real^3`; `d0:real`; `b:(real^2->bool)->real^2`]
        MOI_LGB1_GP_CLAUSE2) THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                     `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                     `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                     `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                     `a:real^2->real^3`; `d0:real`; `b:(real^2->bool)->real^2`]
        MOI_LGB1_GP_CLAUSE3) THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                     `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                     `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                     `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                     `a:real^2->real^3`; `d0:real`; `b:(real^2->bool)->real^2`]
        MOI_LGB1_GP_CLAUSE4) THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                     `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                     `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                     `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                     `a:real^2->real^3`; `d0:real`; `b:(real^2->bool)->real^2`]
        MOI_LGB1_GP_CLAUSE5) THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `d0:real` THEN ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                   `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                   `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                   `a:real^2->real^3`; `d0:real`] MOI_LGB1_GP_OFF_U) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    USE_THEN "wsm" MATCH_MP_TAC THEN EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x:real^2) IN std_triangle` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^2) IN relative_frontier std_triangle` THEN
      SIMP_TAC[relative_frontier; CLOSURE_CLOSED; MOI_LTD_STD_TRIANGLE_BASIC] THEN SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`; `u:real^N->bool`;
                     `h:real^N->real^3`; `h':real^3->real^N`; `kk:real^N->bool`;
                     `L:(real^2->bool)->bool`; `g:real^2->real^N`; `Q:real^N->bool`;
                     `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                     `a:real^2->real^3`; `d0:real`] MOI_LGB1_GP_BOUNDARY) THEN
      ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `d0:real` THEN ASM_SIMP_TAC[]];
    MATCH_MP_TAC MOI_LGB1_GP_HTPY THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                          `u:real^N->bool`; `h:real^N->real^3`; `Q:real^N->bool`;
                          `hs:real^3->bool`; `phi:real^2->real^3`; `rk:real^2->num`;
                          `d0:real`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_LGB1_PATH_W THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tt:(real^N->bool)->bool`;
                          `u:real^N->bool`; `Q:real^N->bool`; `hs:real^3->bool`;
                          `phi:real^2->real^3`; `rk:real^2->num`; `eta:real`; `d0:real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT GEN_TAC THEN DISCH_TAC THEN
      USE_THEN "sm" (MP_TAC o SPECL [`phi':real^2->real^3`; `a':real^2->real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ACCEPT_TAC o CONJUNCT1)];
      REPEAT STRIP_TAC THEN USE_THEN "wsm" MATCH_MP_TAC THEN EXISTS_TAC `x:real^2` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `d0:real` THEN
      ASM_REWRITE_TAC[]]]);;

let CHART_STEP = MOI_LGB1_CHART_STEP;;

