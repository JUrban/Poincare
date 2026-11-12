(* ========================================================================= *)
(* Unit pc_p2c_flconv (Part 2C, flowlim route): local limits of sequences of *)
(* local Ricci flows.  Sequences of local flows on an open set V over [a,b], *)
(* smooth past both ends, with uniform bounds of all space-time jets on the  *)
(* boxes [a,b] x K, have a subsequence converging to a local Ricci flow on   *)
(* (a,b), with metric fields at all times of [a,b] and lck convergence       *)
(* uniform over [a,b] x K.  Tools: the Arzela-Ascoli diagonal argument on    *)
(* compact convex boxes, the C-infinity near calculus of pc_p2c_cgcinf with  *)
(* a moving base metric, and the jet polynomials of pc_p2c_flham.            *)
(* ========================================================================= *)

needs "src/pc_p2c_flham.ml";;
needs "src/pc_p2c_cgsub.ml";;
needs "src/pc_p2c_cgcinf.ml";;

prioritize_real();;
type_invention_error := true;;


(* ------------------------------------------------------------------------- *)
(* Arzela-Ascoli with all partials on compact convex sets, for              *)
(* functions smooth on open supersets that may depend on n.                 *)
(* ------------------------------------------------------------------------- *)

let P2CM_PARTIAL_LIPSCHITZ_ON = prove
 (`!(g:real^M->real^N) V s l B.
     open V /\ convex s /\ s SUBSET V /\ smooth_map_on V g /\
     ALL (\j. 1 <= j /\ j <= dimindex(:M)) l /\
     (!j y. 1 <= j /\ j <= dimindex(:M) /\ y IN s
            ==> norm(iterated_partial (CONS j l) g y) <= B)
     ==> !x y. x IN s /\ y IN s
               ==> norm(iterated_partial l g x - iterated_partial l g y) <=
                   (&(dimindex(:M)) * B) * norm(x - y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC DIFFERENTIABLE_BOUND THEN
  EXISTS_TAC `\(y:real^M) (v:real^M). vsum(1..dimindex(:M))
                     (\j. v$j % iterated_partial (CONS j l) (g:real^M->real^N) y)` THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
    REWRITE_TAC[iterated_partial; ETA_AX] THEN MATCH_MP_TAC TEXT_HAS_DERIVATIVE_PARTIALS THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `V:real^M->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
  MP_TAC(ISPEC `\v:real^M. vsum(1..dimindex(:M))
                     (\j. v$j % iterated_partial (CONS j l) (g:real^M->real^N) y)` ONORM) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`\j (v:real^M). v$j % iterated_partial (CONS j l) (g:real^M->real^N) y`;
                   `1..dimindex(:M)`] LINEAR_COMPOSE_VSUM) THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN BETA_TAC THEN
    DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\v:real^M. v`; `iterated_partial (CONS j l) (g:real^M->real^N) y`;
                   `j:num`] LINEAR_VMUL_COMPONENT) THEN
    ASM_REWRITE_TAC[LINEAR_ID];
    ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN X_GEN_TAC `v:real^M` THEN BETA_TAC THEN
  TRANS_TAC REAL_LE_TRANS
   `sum(1..dimindex(:M)) (\j:num. norm(v:real^M) * B)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[NORM_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE] THEN
    ASM_SIMP_TAC[COMPONENT_LE_NORM];
    REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB] THEN REAL_ARITH_TAC]);;

let P2CM_BOX_SUBSEQ = prove
 (`!(Fs:I->num->real^M->real^N) S Vs.
     COUNTABLE(:I) /\
     (!i. compact (S i) /\ convex (S i)) /\
     (!i n. open (Vs i n) /\ S i SUBSET Vs i n /\ smooth_map_on (Vs i n) (Fs i n)) /\
     (!i l. ALL (\j. 1 <= j /\ j <= dimindex(:M)) l
            ==> ?B. !n y. y IN S i ==> norm(iterated_partial l (Fs i n) y) <= B)
     ==> ?sub H. (!m n:num. m < n ==> sub m < sub n) /\
                 !i l. ALL (\j. 1 <= j /\ j <= dimindex(:M)) l
                       ==> H i l continuous_on S i /\
                           !e. &0 < e
                               ==> ?K. !n y. K <= n /\ y IN S i
                                             ==> norm(iterated_partial l (Fs i (sub n)) y -
                                                      H i l y) < e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "S")
    (CONJUNCTS_THEN2 (LABEL_TAC "V")
       (MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM])))) THEN
  DISCH_THEN(X_CHOOSE_THEN `Bf:I->(num)list->real` (LABEL_TAC "B")) THEN
  ABBREV_TAC `ok = \l:num list. ALL (\j. 1 <= j /\ j <= dimindex(:M)) l` THEN
  MP_TAC(ISPECL
   [`\(il:I#(num)list) n. if (ok:num list->bool) (SND il)
                          then iterated_partial (SND il) ((Fs:I->num->real^M->real^N) (FST il) n)
                          else (\y:real^M. vec 0:real^N)`;
    `\il:I#(num)list. (S:I->real^M->bool) (FST il)`;
    `\il:I#(num)list. abs((Bf:I->(num)list->real) (FST il) (SND il))`;
    `\il:I#(num)list. 0`] P2CS_AA_DIAG_GEN) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM] THEN BETA_TAC THEN REWRITE_TAC[FST; SND; LE_0] THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[P2CS_COUNTABLE_LISTS];
      ASM_MESON_TAC[];
      MAP_EVERY X_GEN_TAC [`i:I`; `l:num list`; `n:num`; `x:real^M`] THEN DISCH_TAC THEN
      COND_CASES_TAC THENL [ALL_TAC; BETA_TAC THEN REWRITE_TAC[NORM_0; REAL_ABS_POS]] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= b ==> x <= abs b`) THEN
      USE_THEN "B" (MP_TAC o SPECL [`i:I`; `l:num list`]) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `(ok:num list->bool) l` THEN EXPAND_TAC "ok" THEN REWRITE_TAC[];
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      MAP_EVERY X_GEN_TAC [`i:I`; `l:num list`; `x:real^M`; `e:real`] THEN STRIP_TAC THEN
      ASM_CASES_TAC `(ok:num list->bool) l` THEN ASM_REWRITE_TAC[] THENL
       [ALL_TAC;
        EXISTS_TAC `&1` THEN BETA_TAC THEN REWRITE_TAC[REAL_LT_01; VECTOR_SUB_REFL; NORM_0] THEN
        ASM_REWRITE_TAC[]] THEN
      ABBREV_TAC `Bs = sum(0..dimindex(:M)) (\j. abs((Bf:I->(num)list->real) i (CONS j l)))` THEN
      SUBGOAL_THEN `!j. 1 <= j /\ j <= dimindex(:M)
                        ==> abs((Bf:I->(num)list->real) i (CONS j l)) <= Bs`
      ASSUME_TAC THENL
       [REPEAT STRIP_TAC THEN EXPAND_TAC "Bs" THEN
        MP_TAC(ISPECL [`\j. abs((Bf:I->(num)list->real) i (CONS j l))`; `dimindex(:M)`;
                       `j:num`] P2CI_SUM_TERM_LE) THEN
        ASM_REWRITE_TAC[REAL_ABS_POS];
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= Bs` ASSUME_TAC THENL
       [EXPAND_TAC "Bs" THEN MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[REAL_ABS_POS];
        ALL_TAC] THEN
      ABBREV_TAC `L = &(dimindex(:M)) * Bs` THEN
      SUBGOAL_THEN `&0 <= L` ASSUME_TAC THENL
       [EXPAND_TAC "L" THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS];
        ALL_TAC] THEN
      EXISTS_TAC `e / (L + &1)` THEN
      ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 <= L ==> &0 < L + &1`] THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `y:real^M`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`(Fs:I->num->real^M->real^N) i n`; `(Vs:I->num->real^M->bool) i n`;
                     `(S:I->real^M->bool) i`; `l:num list`; `Bs:real`]
                    P2CM_PARTIAL_LIPSCHITZ_ON) THEN
      ANTS_TAC THENL
       [USE_THEN "V" (STRIP_ASSUME_TAC o SPECL [`i:I`; `n:num`]) THEN
        USE_THEN "S" (STRIP_ASSUME_TAC o SPEC `i:I`) THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [UNDISCH_TAC `(ok:num list->bool) l` THEN EXPAND_TAC "ok" THEN REWRITE_TAC[];
          MAP_EVERY X_GEN_TAC [`j:num`; `z:real^M`] THEN STRIP_TAC THEN
          TRANS_TAC REAL_LE_TRANS `abs((Bf:I->(num)list->real) i (CONS j l))` THEN
          ASM_SIMP_TAC[] THEN
          MATCH_MP_TAC(REAL_ARITH `x <= b ==> x <= abs b`) THEN
          USE_THEN "B" (MP_TAC o SPECL [`i:I`; `CONS (j:num) l`]) THEN
          ANTS_TAC THENL
           [REWRITE_TAC[ALL] THEN ASM_REWRITE_TAC[] THEN
            UNDISCH_TAC `(ok:num list->bool) l` THEN EXPAND_TAC "ok" THEN REWRITE_TAC[];
            DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPECL [`x:real^M`; `y:real^M`]) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `L * d < e ==> a <= L * d ==> a < e`) THEN
      TRANS_TAC REAL_LET_TRANS `L * e / (L + &1)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 <= L ==> &0 < L + &1`; REAL_LT_LDIV_EQ;
                   REAL_ARITH `L * e / (L + &1) = (L * e) / (L + &1)`] THEN
      ASM_SIMP_TAC[REAL_LT_LMUL_EQ; REAL_ARITH `L * e < e * (L + &1) <=> &0 < e`]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN BETA_TAC THEN REWRITE_TAC[FST; SND] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:I->(num)list->real^M->real^N` (LABEL_TAC "g")) THEN
  MAP_EVERY EXISTS_TAC [`sub:num->num`; `g:I->(num)list->real^M->real^N`] THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`i:I`; `l:num list`] THEN DISCH_TAC THEN
  USE_THEN "g" (MP_TAC o SPECL [`i:I`; `l:num list`]) THEN
  SUBGOAL_THEN `(ok:num list->bool) l` (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "ok" THEN ASM_REWRITE_TAC[]; MESON_TAC[]]);;

(* A countable cover of an open set by balls whose closures lie inside.    *)

let P2CM_BALL_COVER = prove
 (`!V:real^N->bool.
     open V
     ==> ?c r. (!i:num. cball(c i,r i) SUBSET V) /\
               (!y. y IN V ==> ?i. &0 < r i /\ y IN ball(c i,r i))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `D = {(v:real^N,q) | (!i. 1 <= i /\ i <= dimindex(:N) ==> rational(v$i)) /\
                                  rational q /\ &0 < q /\ cball(v,q) SUBSET V}` THEN
  SUBGOAL_THEN `!p:real^N#real. p IN D <=>
                      (!i. 1 <= i /\ i <= dimindex(:N) ==> rational(FST p$i)) /\
                      rational(SND p) /\ &0 < SND p /\ cball(FST p,SND p) SUBSET V`
  ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `!p:real^N#real. p IN D ==> &0 < SND p /\ cball(FST p,SND p) SUBSET V`
  (LABEL_TAC "Dprop") THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `COUNTABLE (D:real^N#real->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COUNTABLE_SUBSET THEN
    EXISTS_TAC `{v:real^N | !i. 1 <= i /\ i <= dimindex(:N) ==> rational(v$i)} CROSS
                rational` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC COUNTABLE_CROSS THEN
      REWRITE_TAC[COUNTABLE_RATIONAL; COUNTABLE_RATIONAL_COORDINATES];
      ASM_REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_CROSS; IN_ELIM_THM] THEN
      REWRITE_TAC[IN] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^N. y IN V ==> ?v q. (v,q) IN D /\ y IN ball(v,q)` (LABEL_TAC "cov") THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    UNDISCH_TAC `open(V:real^N->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM; SUBSET; IN_BALL] THEN
    X_GEN_TAC `e:real` THEN STRIP_TAC THEN
    MP_TAC(REWRITE_RULE[EXTENSION; IN_UNIV] CLOSURE_RATIONAL_COORDINATES) THEN
    REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
    DISCH_THEN(MP_TAC o SPECL [`x:real^N`; `e / &4`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[IN_ELIM_THM]] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?q. rational q /\ e / &3 < q /\ q < e / &2`
     (X_CHOOSE_THEN `q:real` STRIP_ASSUME_TAC) THENL
     [MP_TAC(ISPECL [`&5 / &12 * e`; `e / &12`] RATIONAL_APPROXIMATION) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC MONO_EXISTS] THEN
      SIMP_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`v:real^N`; `q:real`] THEN
    ASM_REWRITE_TAC[IN_BALL; SUBSET; IN_CBALL] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REPEAT(POP_ASSUM MP_TAC) THEN NORM_ARITH_TAC;
      REPEAT(POP_ASSUM MP_TAC) THEN NORM_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `D:real^N#real->bool = {}` THENL
   [MAP_EVERY EXISTS_TAC [`(\i. vec 0):num->real^N`; `(\i. -- &1):num->real`] THEN
    CONJ_TAC THENL
     [GEN_TAC THEN SIMP_TAC[CBALL_EMPTY; REAL_ARITH `-- &1 < &0`; EMPTY_SUBSET];
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      USE_THEN "cov" (MP_TAC o C MP (ASSUME `(y:real^N) IN V`) o SPEC `y:real^N`) THEN
      ASM_MESON_TAC[NOT_IN_EMPTY]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `D:real^N#real->bool` COUNTABLE_AS_IMAGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->real^N#real` (LABEL_TAC "f")) THEN
  SUBGOAL_THEN `!i. ((f:num->real^N#real) i) IN D` (LABEL_TAC "inD") THENL
   [GEN_TAC THEN USE_THEN "f" SUBST1_TAC THEN
    REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`\i. FST((f:num->real^N#real) i)`; `\i. SND((f:num->real^N#real) i)`] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN
    USE_THEN "inD" (fun th -> USE_THEN "Dprop" (fun dp ->
      MP_TAC(MP (SPEC `(f:num->real^N#real) i` dp) (SPEC `i:num` th)))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  USE_THEN "cov" (MP_TAC o C MP (ASSUME `(y:real^N) IN V`) o SPEC `y:real^N`) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`v:real^N`; `q:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(v:real^N,q) IN IMAGE (f:num->real^N#real) (:num)` MP_TAC THENL
   [USE_THEN "f" (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN DISCH_THEN(X_CHOOSE_TAC `i:num`) THEN
  EXISTS_TAC `i:num` THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    is_pair(lhs(concl th)))) THEN
  REWRITE_TAC[FST; SND] THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "Dprop" (MP_TAC o C MP (ASSUME `(v:real^N,q:real) IN (D:real^N#real->bool)`) o
                    SPEC `(v:real^N,q:real)`) THEN
  SIMP_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* Boxes.  Bounds of the space-time partials of the entries on              *)
(* the open-time box (a,b) x K pass to the closed box through the smooth    *)
(* extension FF; uniform limits of all partials on a closed box give smooth *)
(* limits on the open box and on every time slice, with C-infinity          *)
(* convergence near every point of the slices.                              *)
(* ------------------------------------------------------------------------- *)

let P2CM_BOX_BOUND = prove
 (`!V a b K (Gs:real->real^N->real^N^N) e (FF:real^(1,N)finite_sum->real^(N,N)finite_prod)
    l p q B.
     open V /\ a < b /\ compact K /\ K SUBSET V /\ &0 < e /\
     smooth_map_on (interval(lift(a - e),lift(b + e)) PCROSS V) FF /\
     (!t y. a <= t /\ t <= b /\ y IN V ==> FF(pastecart (lift t) y) = vectorize(Gs t y)) /\
     (!w. w IN interval(lift a,lift b) PCROSS K
          ==> norm(iterated_partial l
                     (\w. lift(Gs (drop(fstcart w)) (sndcart w)$p$q)) w) <= B)
     ==> !w. w IN interval[lift a,lift b] PCROSS K
             ==> norm(iterated_partial l (\w. lift((matrify(FF w):real^N^N)$p$q)) w) <= B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `D = interval(lift(a - e),lift(b + e)) PCROSS (V:real^N->bool)` THEN
  SUBGOAL_THEN `open(D:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on D (\w. lift((matrify((FF:real^(1,N)finite_sum->real^(N,N)finite_prod) w)
                               :real^N^N)$p$q))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\w. lift((matrify((FF:real^(1,N)finite_sum->real^(N,N)finite_prod) w):real^N^N)$p$q)) =
      (\m:real^(N,N)finite_prod. lift((matrify m:real^N^N)$p$q)) o FF`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[linear; MATRIFY_ADD; MATRIFY_CMUL; MATRIX_ADD_COMPONENT;
                MATRIX_CMUL_COMPONENT; LIFT_ADD; LIFT_CMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. w IN interval(lift a,lift b) PCROSS (V:real^N->bool)
        ==> iterated_partial l
              (\w. lift((matrify((FF:real^(1,N)finite_sum->real^(N,N)finite_prod) w)
                         :real^N^N)$p$q)) w =
            iterated_partial l
              (\w. lift((Gs:real->real^N->real^N^N) (drop(fstcart w)) (sndcart w)$p$q)) w`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`l:num list`; `interval(lift a,lift b) PCROSS (V:real^N->bool)`;
                   `\w. lift((matrify((FF:real^(1,N)finite_sum->real^(N,N)finite_prod) w)
                               :real^N^N)$p$q)`;
                   `\w. lift((Gs:real->real^N->real^N^N) (drop(fstcart w)) (sndcart w)$p$q)`]
                  TEXT_ITERATED_PARTIAL_LOCAL_OPEN) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN
    REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP;
                FSTCART_PASTECART; SNDCART_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`tt:real^1`; `y:real^N`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`drop tt`; `y:real^N`] o check (fun th ->
      can (find_term ((=) `vectorize:real^N^N->real^(N,N)finite_prod`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[MATRIFY_VECTORIZE];
    ALL_TAC] THEN
  SUBGOAL_THEN `closure(interval(lift a,lift b) PCROSS (K:real^N->bool)) =
                interval[lift a,lift b] PCROSS K`
  ASSUME_TAC THENL
   [REWRITE_TAC[CLOSURE_PCROSS] THEN BINOP_TAC THENL
     [MATCH_MP_TAC CLOSURE_OPEN_INTERVAL THEN
      REWRITE_TAC[INTERVAL_NE_EMPTY_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED]];
    ALL_TAC] THEN
  X_GEN_TAC `w:real^(1,N)finite_sum` THEN DISCH_TAC THEN
  MATCH_MP_TAC CONTINUOUS_ON_CLOSURE_NORM_LE THEN
  EXISTS_TAC `interval(lift a,lift b) PCROSS (K:real^N->bool)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `D:real^(1,N)finite_sum->bool` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_ITERATED_PARTIAL THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "D" THEN MATCH_MP_TAC PCROSS_MONO THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[]]];
    X_GEN_TAC `z:real^(1,N)finite_sum` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^(1,N)finite_sum) IN interval(lift a,lift b) PCROSS V`
    ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^(1,N)finite_sum) IN interval(lift a,lift b) PCROSS K` THEN
      SPEC_TAC(`z:real^(1,N)finite_sum`,`z:real^(1,N)finite_sum`) THEN
      REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS] THEN ASM SET_TAC[];
      ASM_SIMP_TAC[]]]);;

let P2CM_SLICE_LIMIT = prove
 (`!(Es:num->real^(1,N)finite_sum->real^1) H (D:num->real^(1,N)finite_sum->bool)
    a b c r t.
     a <= t /\ t <= b /\
     (!n. open (D n) /\ interval[lift a,lift b] PCROSS cball(c,r) SUBSET D n /\
          smooth_map_on (D n) (Es n)) /\
     (!l. ALL (\j. 1 <= j /\ j <= dimindex(:(1,N)finite_sum)) l
          ==> !e. &0 < e
                  ==> ?K. !n w. K <= n /\ w IN interval[lift a,lift b] PCROSS cball(c,r)
                                ==> norm(iterated_partial l (Es n) w - H l w) < e)
     ==> smooth_map_on (ball(c,r)) (\y. H [] (pastecart (lift t) y)) /\
         (!l y. ALL (\j. 1 <= j /\ j <= dimindex(:N)) l /\ y IN ball(c,r)
                ==> iterated_partial l (\y. H [] (pastecart (lift t) y)) y =
                    H (MAP (\k. 1 + k) l) (pastecart (lift t) y)) /\
         (!y0. y0 IN ball(c,r)
               ==> p2ci_near y0 (\n y. Es n (pastecart (lift t) y))
                                (\y. H [] (pastecart (lift t) y)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "D") (LABEL_TAC "conv")))) THEN
  SUBGOAL_THEN `!y:real^N. y IN cball(c,r)
                           ==> pastecart (lift t) y IN interval[lift a,lift b] PCROSS cball(c,r)`
  (LABEL_TAC "inS") THENL
   [REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n y. y IN cball(c:real^N,r)
                      ==> pastecart (lift t) y IN (D:num->real^(1,N)finite_sum->bool) n`
  (LABEL_TAC "inD") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "D" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    USE_THEN "inS" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. smooth_map_on (ball(c:real^N,r))
                      (\y. (Es:num->real^(1,N)finite_sum->real^1) n (pastecart (lift t) y))`
  (LABEL_TAC "sm") THENL
   [GEN_TAC THEN MATCH_MP_TAC RFA_W_SLICE_SMOOTH THEN
    EXISTS_TAC `(D:num->real^(1,N)finite_sum->bool) n` THEN
    USE_THEN "D" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[OPEN_BALL] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN USE_THEN "inD" MATCH_MP_TAC THEN
    ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n l y. ALL (\j. 1 <= j /\ j <= dimindex(:N)) l /\ y IN cball(c:real^N,r)
            ==> iterated_partial l
                  (\y. (Es:num->real^(1,N)finite_sum->real^1) n (pastecart (lift t) y)) y =
                iterated_partial (MAP (\k. 1 + k) l) (Es n) (pastecart (lift t) y)`
  (LABEL_TAC "ip") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_ST_SLICE_ITERATED THEN
    EXISTS_TAC `(D:num->real^(1,N)finite_sum->bool) n` THEN
    USE_THEN "D" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "inD" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!l. ALL (\j. 1 <= j /\ j <= dimindex(:N)) l
        ==> ALL (\j. 1 <= j /\ j <= dimindex(:(1,N)finite_sum)) (MAP (\k. 1 + k) l)`
  (LABEL_TAC "sh") THENL
   [GEN_TAC THEN REWRITE_TAC[ALL_MAP; o_DEF; DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN
    MATCH_MP_TAC MONO_ALL THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!l. ALL (\j. 1 <= j /\ j <= dimindex(:N)) l
        ==> !e. &0 < e
                ==> ?K. !n y. K <= n /\ y IN cball(c:real^N,r)
                              ==> norm(iterated_partial l
                                         (\y. (Es:num->real^(1,N)finite_sum->real^1) n
                                                (pastecart (lift t) y)) y -
                                       H (MAP (\k. 1 + k) l) (pastecart (lift t) y)) < e`
  (LABEL_TAC "uc") THENL
   [X_GEN_TAC `l:num list` THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "conv" (MP_TAC o SPEC `MAP (\k. 1 + k) (l:num list)`) THEN
    ANTS_TAC THENL [USE_THEN "sh" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `K:num` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `y:real^N`] THEN STRIP_TAC THEN
    USE_THEN "ip" (MP_TAC o C MP
      (CONJ (ASSUME `ALL (\j. 1 <= j /\ j <= dimindex(:N)) l`)
            (ASSUME `(y:real^N) IN cball(c,r)`)) o
      SPECL [`n:num`; `l:num list`; `y:real^N`]) THEN
    DISCH_THEN SUBST1_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "inS" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\n y. (Es:num->real^(1,N)finite_sum->real^1) n (pastecart (lift t) y)`;
                 `\l y. (H:(num)list->real^(1,N)finite_sum->real^1) (MAP (\k. 1 + k) l)
                          (pastecart (lift t) y)`;
                 `ball(c:real^N,r)`] P2CS_CINF_LIMIT) THEN
  REWRITE_TAC[OPEN_BALL; CONVEX_BALL; MAP] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [USE_THEN "sm" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
    X_GEN_TAC `l:num list` THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "uc" (MP_TAC o C MP (ASSUME `ALL (\j. 1 <= j /\ j <= dimindex(:N)) l`) o
                   SPEC `l:num list`) THEN
    DISCH_THEN(MP_TAC o C MP (ASSUME `&0 < e`) o SPEC `e:real`) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `K:num` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `y:real^N`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pl")) THEN
  ASM_REWRITE_TAC[] THEN
  TRY(CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "pl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  X_GEN_TAC `y0:real^N` THEN DISCH_TAC THEN
  MATCH_MP_TAC P2CI_NEAR_OF_PARTIALS THEN EXISTS_TAC `r - dist(c:real^N,y0)` THEN
  BETA_TAC THEN
  SUBGOAL_THEN `ball(y0:real^N,r - dist(c,y0)) SUBSET ball(c,r)` ASSUME_TAC THENL
   [UNDISCH_TAC `(y0:real^N) IN ball(c,r)` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
    CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `(y0:real^N) IN ball(c,r)` THEN REWRITE_TAC[IN_BALL] THEN REAL_ARITH_TAC;
    EXISTS_TAC `0` THEN GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `ball(c:real^N,r)` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "sm" (fun th -> REWRITE_TAC[th]);
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(c:real^N,r)` THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `l:num list` THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "uc" (MP_TAC o C MP (ASSUME `ALL (\j. 1 <= j /\ j <= dimindex(:N)) l`) o
                   SPEC `l:num list`) THEN
    DISCH_THEN(MP_TAC o C MP (ASSUME `&0 < e`) o SPEC `e:real`) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `K:num` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `y:real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN ball(c,r)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "pl" (MP_TAC o C MP
      (CONJ (ASSUME `ALL (\j. 1 <= j /\ j <= dimindex(:N)) l`)
            (ASSUME `(y:real^N) IN ball(c,r)`)) o SPECL [`l:num list`; `y:real^N`]) THEN
    DISCH_THEN SUBST1_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET]]);;

let P2CM_OPEN_BOX_LIMIT = prove
 (`!(Es:num->real^(1,N)finite_sum->real^1) H (D:num->real^(1,N)finite_sum->bool) a b c r.
     (!n. open (D n) /\ interval[lift a,lift b] PCROSS cball(c,r) SUBSET D n /\
          smooth_map_on (D n) (Es n)) /\
     (!l. ALL (\j. 1 <= j /\ j <= dimindex(:(1,N)finite_sum)) l
          ==> !e. &0 < e
                  ==> ?K. !n w. K <= n /\ w IN interval[lift a,lift b] PCROSS cball(c,r)
                                ==> norm(iterated_partial l (Es n) w - H l w) < e)
     ==> smooth_map_on (interval(lift a,lift b) PCROSS ball(c,r)) (H []) /\
         (!l w. ALL (\j. 1 <= j /\ j <= dimindex(:(1,N)finite_sum)) l /\
                w IN interval(lift a,lift b) PCROSS ball(c,r)
                ==> iterated_partial l (H []) w = H l w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `interval(lift a,lift b) PCROSS ball(c:real^N,r) SUBSET
                interval[lift a,lift b] PCROSS cball(c,r)` ASSUME_TAC THENL
   [MATCH_MP_TAC PCROSS_MONO THEN
    REWRITE_TAC[INTERVAL_OPEN_SUBSET_CLOSED; BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Es:num->real^(1,N)finite_sum->real^1`;
                 `H:(num)list->real^(1,N)finite_sum->real^1`;
                 `interval(lift a,lift b) PCROSS ball(c:real^N,r)`] P2CS_CINF_LIMIT) THEN
  SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_BALL; CONVEX_PCROSS; CONVEX_INTERVAL;
           CONVEX_BALL] THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `(D:num->real^(1,N)finite_sum->bool) n` THEN ASM_MESON_TAC[SUBSET_TRANS];
    X_GEN_TAC `l:num list` THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `l:num list`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `K:num` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `w:real^(1,N)finite_sum`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* The C-infinity near calculus of pc_p2c_cgcinf for inverse               *)
(* matrices and for the jet polynomials of pc_p2c_flham: if metric fields   *)
(* As n tend to A0 near z0 with all derivatives, so do the values of every  *)
(* jet polynomial (in particular Christoffel symbols and Ricci tensors).    *)
(* ------------------------------------------------------------------------- *)

let P2CM_NEAR_INV = prove
 (`!(As:num->real^N->real^N^N) A0 (z0:real^N).
     invertible(A0 z0) /\ p2ci_near z0 (\n. vectorize o As n) (vectorize o A0)
     ==> p2ci_near z0 (\n. vectorize o (\z. matrix_inv(As n z)))
                      (vectorize o (\z. matrix_inv(A0 z)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `O = {v:real^(N,N)finite_prod | v IN (:real^(N,N)finite_prod) /\
                                              invertible(matrify v:real^N^N)}` THEN
  SUBGOAL_THEN `open(O:real^(N,N)finite_prod->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN MATCH_MP_TAC PDE_OPEN_INVERTIBLE_SET THEN
    REWRITE_TAC[OPEN_UNIV; CONTINUOUS_ON_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(vectorize((A0:real^N->real^N^N) z0)) IN O` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN ASM_REWRITE_TAC[IN_ELIM_THM; IN_UNIV; MATRIFY_VECTORIZE];
    ALL_TAC] THEN
  SUBGOAL_THEN `?r. &0 < r /\ ball(vectorize((A0:real^N->real^N^N) z0),r) SUBSET O`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[OPEN_CONTAINS_BALL]; ALL_TAC] THEN
  ABBREV_TAC `Tl = \v:real^(N,N)finite_prod.
                     (vectorize:real^N^N->real^(N,N)finite_prod)(matrix_inv(matrify v))` THEN
  SUBGOAL_THEN `smooth_map_on (ball(vectorize((A0:real^N->real^N^N) z0),r))
                  (Tl:real^(N,N)finite_prod->real^(N,N)finite_prod)`
  ASSUME_TAC THENL
   [EXPAND_TAC "Tl" THEN
    MP_TAC(ISPECL [`ball(vectorize((A0:real^N->real^N^N) z0),r)`;
                   `matrify:real^(N,N)finite_prod->real^N^N`] LRG_SMOOTH_MATRIX_INV) THEN
    REWRITE_TAC[OPEN_BALL; o_DEF; VECTORIZE_MATRIFY] THEN
    REWRITE_TAC[ETA_AX; SMOOTH_MAP_ON_ID] THEN DISCH_THEN MATCH_MP_TAC THEN
    X_GEN_TAC `v:real^(N,N)finite_prod` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM INVERTIBLE_DET_NZ] THEN
    SUBGOAL_THEN `(v:real^(N,N)finite_prod) IN O` MP_TAC THENL
     [ASM SET_TAC[]; EXPAND_TAC "O" THEN REWRITE_TAC[IN_ELIM_THM; IN_UNIV]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`z0:real^N`;
                 `\n:num. (vectorize:real^N^N->real^(N,N)finite_prod) o
                          (As:num->real^N->real^N^N) n`;
                 `(vectorize:real^N^N->real^(N,N)finite_prod) o (A0:real^N->real^N^N)`;
                 `\n:num. (Tl:real^(N,N)finite_prod->real^(N,N)finite_prod)`;
                 `Tl:real^(N,N)finite_prod->real^(N,N)finite_prod`] P2CI_NEAR_COMPOSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[o_THM] THEN MATCH_MP_TAC P2CI_NEAR_CONST THEN
    EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXPAND_TAC "Tl" THEN REWRITE_TAC[o_DEF; MATRIFY_VECTORIZE] THEN REWRITE_TAC[ETA_AX]);;

(* The values of jet polynomials. *)

let P2CM_NEAR_EVAL = prove
 (`!(As:num->real^N->real^N^N) A0 (z0:real^N).
     invertible(A0 z0) /\ p2ci_near z0 (\n. vectorize o As n) (vectorize o A0)
     ==> !e. p2ch_ok (dimindex(:N)) e
             ==> p2ci_near z0 (\n z. lift(p2ch_eval (\s:real. As n) e (&0) z))
                              (\z. lift(p2ch_eval (\s:real. A0) e (&0) z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> ASSUME_TAC(REWRITE_RULE[P2CI_NEAR_MATRIX] th)) THEN
  MP_TAC(ISPECL [`As:num->real^N->real^N^N`; `A0:real^N->real^N^N`; `z0:real^N`]
                P2CM_NEAR_INV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o REWRITE_RULE[P2CI_NEAR_MATRIX]) THEN
  MATCH_MP_TAC p2ch_expr_INDUCT THEN REWRITE_TAC[p2ch_ok; p2ch_eval] THEN
  REPEAT CONJ_TAC THENL
   [(* PHE_G *)
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`a0:num`; `a1:num`] o
      check (fun th -> not(can (find_term ((=) `matrix_inv:real^N^N->real^N^N`)) (concl th)))) THEN
    ASM_REWRITE_TAC[];
    (* PHE_I *)
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`a0:num`; `a1:num`] o
      check (fun th -> can (find_term ((=) `matrix_inv:real^N^N->real^N^N`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    (* PHE_C *)
    GEN_TAC THEN MATCH_MP_TAC P2CI_NEAR_CONST THEN EXISTS_TAC `&1` THEN
    REWRITE_TAC[REAL_LT_01; SMOOTH_MAP_ON_CONST];
    (* PHE_ADD *)
    REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC P2CI_NEAR_ADD THEN
    ASM_SIMP_TAC[];
    (* PHE_MUL *)
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\x (y:real^1). drop x % y`; `z0:real^N`;
                   `\n z. lift(p2ch_eval (\s:real. (As:num->real^N->real^N^N) n) a0 (&0) z)`;
                   `\z. lift(p2ch_eval (\s:real. (A0:real^N->real^N^N)) a0 (&0) z)`;
                   `\n z. lift(p2ch_eval (\s:real. (As:num->real^N->real^N^N) n) a1 (&0) z)`;
                   `\z. lift(p2ch_eval (\s:real. (A0:real^N->real^N^N)) a1 (&0) z)`]
                  P2CI_NEAR_BILINEAR2) THEN
    REWRITE_TAC[BILINEAR_DROP_MUL; LIFT_DROP; GSYM LIFT_CMUL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    (* PHE_D *)
    REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_pd; LIFT_DROP] THEN
    MP_TAC(ISPECL [`z0:real^N`;
                   `\n z. lift(p2ch_eval (\s:real. (As:num->real^N->real^N^N) n) a1 (&0) z)`;
                   `\z. lift(p2ch_eval (\s:real. (A0:real^N->real^N^N)) a1 (&0) z)`;
                   `a0:num`] P2CI_NEAR_PARTIAL) THEN
    ASM_SIMP_TAC[ETA_AX]]);;


(* ------------------------------------------------------------------------- *)
(* The tensor near calculus with a moving base metric.  If the              *)
(* metric fields As n tend to A0 near z0 with all derivatives (p2cm_mnear), *)
(* so do their Christoffel symbols; covariant derivatives and squared norms *)
(* with respect to As n of tensors tending to 0 tend to 0; and             *)
(* lck_dist2 m (As n) (Bs n) tends to 0 when Bs n tends to A0 as well.      *)
(* ------------------------------------------------------------------------- *)

let p2cm_mnear = new_definition
 `p2cm_mnear (z0:real^N) (As:num->real^N->real^N^N) A0 <=>
    (?r N. &0 < r /\ metric_field (ball(z0,r)) A0 /\
           !n. N <= n ==> metric_field (ball(z0,r)) (As n)) /\
    p2ci_near z0 (\n. vectorize o As n) (vectorize o A0)`;;

let P2CM_MNEAR_INVERTIBLE = prove
 (`!(z0:real^N) As A0. p2cm_mnear z0 As A0 ==> invertible(A0 z0)`,
  REWRITE_TAC[p2cm_mnear] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ball(z0:real^N,r)`; `A0:real^N->real^N^N`; `z0:real^N`]
                LRG_METRIC_INVERTIBLE) THEN
  ASM_SIMP_TAC[CENTRE_IN_BALL]);;

let P2CM_MNEAR_CHRIST_BASIS = prove
 (`!(z0:real^N) As A0 m p q.
     p2cm_mnear z0 As A0 /\
     1 <= m /\ m <= dimindex(:N) /\ 1 <= p /\ p <= dimindex(:N) /\
     1 <= q /\ q <= dimindex(:N)
     ==> p2ci_near z0 (\n z. lift(christoffel (As n) z (basis p) (basis q)$m))
                      (\z. lift(christoffel A0 z (basis p) (basis q)$m))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "mn") STRIP_ASSUME_TAC) THEN
  USE_THEN "mn" (ASSUME_TAC o MATCH_MP P2CM_MNEAR_INVERTIBLE) THEN
  USE_THEN "mn" (STRIP_ASSUME_TAC o REWRITE_RULE[p2cm_mnear]) THEN
  MP_TAC(ISPECL [`As:num->real^N->real^N^N`; `A0:real^N->real^N^N`; `z0:real^N`]
                P2CM_NEAR_EVAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `p2ch_xchr (dimindex(:N)) m p q`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[p2ch_xchr; p2ch_xsub; p2ch_xd1] THEN P2CH_OK_TAC; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC P2CI_NEAR_EQ THEN
  MAP_EVERY EXISTS_TAC
   [`\n z. lift(p2ch_eval (\s:real. (As:num->real^N->real^N^N) n)
                          (p2ch_xchr (dimindex(:N)) m p q) (&0) z)`;
    `\z. lift(p2ch_eval (\s:real. (A0:real^N->real^N^N))
                        (p2ch_xchr (dimindex(:N)) m p q) (&0) z)`;
    `r:real`; `N:num`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `z:real^N`] THEN STRIP_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`ball(z0:real^N,r)`; `\s:real. (As:num->real^N->real^N^N) n`; `&0`;
                   `z:real^N`; `m:num`; `p:num`; `q:num`] P2CH_EVAL_XCHR) THEN
    ASM_SIMP_TAC[PDE_CHR_JET];
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`ball(z0:real^N,r)`; `\s:real. (A0:real^N->real^N^N)`; `&0`;
                   `z:real^N`; `m:num`; `p:num`; `q:num`] P2CH_EVAL_XCHR) THEN
    ASM_SIMP_TAC[PDE_CHR_JET]]);;

let P2CM_MNEAR_CHRIST = prove
 (`!(z0:real^N) As A0 m u v.
     p2cm_mnear z0 As A0 /\ 1 <= m /\ m <= dimindex(:N)
     ==> p2ci_near z0 (\n z. lift(christoffel (As n) z u v$m))
                      (\z. lift(christoffel A0 z u v$m))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "mn") STRIP_ASSUME_TAC) THEN
  USE_THEN "mn" (STRIP_ASSUME_TAC o REWRITE_RULE[p2cm_mnear]) THEN
  MATCH_MP_TAC P2CI_NEAR_EQ THEN
  MAP_EVERY EXISTS_TAC
   [`\n z. vsum(1..dimindex(:N)) (\p. vsum(1..dimindex(:N)) (\q.
             drop(lift((u:real^N)$p * (v:real^N)$q)) %
             lift(christoffel ((As:num->real^N->real^N^N) n) z (basis p) (basis q)$m)))`;
    `\z. vsum(1..dimindex(:N)) (\p. vsum(1..dimindex(:N)) (\q.
             drop(lift((u:real^N)$p * (v:real^N)$q)) %
             lift(christoffel (A0:real^N->real^N^N) z (basis p) (basis q)$m)))`;
    `r:real`; `N:num`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2CI_NEAR_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC P2CI_NEAR_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `q:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC P2CI_NEAR_SMUL THEN EXISTS_TAC `r:real` THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
    MATCH_MP_TAC P2CM_MNEAR_CHRIST_BASIS THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`n:num`; `z:real^N`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`ball(z0:real^N,r)`; `(As:num->real^N->real^N^N) n`; `z:real^N`;
                   `u:real^N`; `v:real^N`; `m:num`] PDE_CHR_EXPAND) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[LIFT_SUM; LIFT_DROP; o_DEF; GSYM LIFT_CMUL; REAL_MUL_ASSOC];
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`ball(z0:real^N,r)`; `A0:real^N->real^N^N`; `z:real^N`;
                   `u:real^N`; `v:real^N`; `m:num`] PDE_CHR_EXPAND) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[LIFT_SUM; LIFT_DROP; o_DEF; GSYM LIFT_CMUL; REAL_MUL_ASSOC]]);;

let P2CM_TNEAR_LNABLA2 = prove
 (`!(z0:real^N) As A0 k tfs.
     p2cm_mnear z0 As A0 /\ p2ci_tnear k z0 tfs
     ==> p2ci_tnear (k + 1) z0 (\n. lnabla k (As n) (tfs n))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "mn") MP_TAC) THEN
  USE_THEN "mn" (X_CHOOSE_THEN `r1:real` (X_CHOOSE_THEN `N1:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "mf")))) o
    CONJUNCT1 o REWRITE_RULE[p2cm_mnear]) THEN
  REWRITE_TAC[p2ci_tnear] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `N0:num`
       (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tf"))))
    (LABEL_TAC "near")) THEN
  ABBREV_TAC `s = min r r1` THEN
  SUBGOAL_THEN `&0 < s /\ ball(z0:real^N,s) SUBSET ball(z0,r) /\
                ball(z0:real^N,s) SUBSET ball(z0,r1)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n:num. N0 + N1 <= n
        ==> metric_field (ball(z0:real^N,s)) ((As:num->real^N->real^N^N) n) /\
            ltensor_field k (ball(z0:real^N,s))
              ((tfs:num->real^N->(num->real^N)->real) n) /\
            !u. smooth_map_on (ball(z0,s)) (\y. lift(tfs n y u))`
  (LABEL_TAC "fld") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "tf" (MP_TAC o SPEC `n:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `ball(z0:real^N,r1)` THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN USE_THEN "mf" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      UNDISCH_TAC `ltensor_field k (ball(z0:real^N,r))
                     ((tfs:num->real^N->(num->real^N)->real) n)` THEN
      REWRITE_TAC[ltensor_field] THEN ASM_MESON_TAC[SUBSET];
      GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `ball(z0:real^N,r)` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`s:real`; `N0 + N1:num`] THEN ASM_REWRITE_TAC[] THEN
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
            (\q. (christoffel ((As:num->real^N->real^N^N) n) y (u(k + 1)) (u i))$q %
                 lift(tfs n y (\j. if j = i then basis q else u j))))` THEN
  EXISTS_TAC `\y:real^N. vec 0:real^1` THEN
  MAP_EVERY EXISTS_TAC [`s:real`; `N0 + N1:num`] THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    MAP_EVERY X_GEN_TAC [`n:num`; `z:real^N`] THEN STRIP_TAC THEN
    USE_THEN "fld" (MP_TAC o C MP (ASSUME `N0 + N1 <= (n:num)`) o SPEC `n:num`) THEN
    STRIP_TAC THEN
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
    DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC P2CI_ZERO_PARTIAL THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2CI_ZERO_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC P2CI_ZERO_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `q:num` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM LIFT_CMUL] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    MATCH_MP_TAC P2CI_ZERO_MUL THEN
    EXISTS_TAC `\y. lift((christoffel (A0:real^N->real^N^N) y
                           ((u:num->real^N)(k + 1)) (u i))$q)` THEN
    CONJ_TAC THENL
     [USE_THEN "near" (MP_TAC o SPEC `\j. if j = i then basis q else (u:num->real^N) j`) THEN
      REWRITE_TAC[];
      MATCH_MP_TAC P2CM_MNEAR_CHRIST THEN ASM_REWRITE_TAC[]]]);;

let P2CM_TNEAR_ITER2 = prove
 (`!(z0:real^N) As A0 k tfs.
     p2cm_mnear z0 As A0 /\ p2ci_tnear k z0 tfs
     ==> !l. p2ci_tnear (k + l) z0 (\n. lnabla_iter k l (As n) (tfs n))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [ASM_REWRITE_TAC[lnabla_iter; ADD_CLAUSES; ETA_AX];
    REWRITE_TAC[lnabla_iter; ADD_CLAUSES; ADD1] THEN
    MP_TAC(ISPECL [`z0:real^N`; `As:num->real^N->real^N^N`; `A0:real^N->real^N^N`;
                   `k + l:num`;
                   `\n:num. lnabla_iter k l ((As:num->real^N->real^N^N) n)
                              ((tfs:num->real^N->(num->real^N)->real) n)`]
                  P2CM_TNEAR_LNABLA2) THEN
    ASM_REWRITE_TAC[]]);;

(* Products, squared norms and differences of metric tensors. *)

let P2CM_NEAR_PRODUCT = prove
 (`!(z0:real^M) (f:num->num->real^M->real) g k.
     (!m. 1 <= m /\ m <= k ==> p2ci_near z0 (\n y. lift(f m n y)) (\y. lift(g m y)))
     ==> p2ci_near z0 (\n y. lift(product(1..k) (\m. f m n y)))
                      (\y. lift(product(1..k) (\m. g m y)))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[PRODUCT_CLAUSES_NUMSEG; ARITH_RULE `~(1 = 0)`] THEN
    DISCH_TAC THEN MATCH_MP_TAC P2CI_NEAR_CONST THEN EXISTS_TAC `&1` THEN
    REWRITE_TAC[REAL_LT_01; SMOOTH_MAP_ON_CONST];
    DISCH_TAC THEN REWRITE_TAC[PRODUCT_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC k`] THEN
    MP_TAC(ISPECL [`\x (y:real^1). drop x % y`; `z0:real^M`;
                   `\n y. lift(product(1..k) (\m. (f:num->num->real^M->real) m n y))`;
                   `\y. lift(product(1..k) (\m. (g:num->real^M->real) m y))`;
                   `\n y. lift((f:num->num->real^M->real) (SUC k) n y)`;
                   `\y. lift((g:num->real^M->real) (SUC k) y)`] P2CI_NEAR_BILINEAR2) THEN
    REWRITE_TAC[BILINEAR_DROP_MUL; LIFT_DROP; GSYM LIFT_CMUL] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC]]);;

let P2CM_LTNORM2_NEAR2 = prove
 (`!(z0:real^N) As A0 k tfs.
     p2cm_mnear z0 As A0 /\ p2ci_tnear k z0 tfs
     ==> p2ci_near z0 (\n y. lift(ltnorm2 k (As n) (tfs n) y)) (\y. vec 0)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "mn") MP_TAC) THEN
  REWRITE_TAC[p2ci_tnear] THEN STRIP_TAC THEN
  USE_THEN "mn" (ASSUME_TAC o MATCH_MP P2CM_MNEAR_INVERTIBLE) THEN
  USE_THEN "mn" (ASSUME_TAC o CONJUNCT2 o REWRITE_RULE[p2cm_mnear]) THEN
  MP_TAC(ISPECL [`As:num->real^N->real^N^N`; `A0:real^N->real^N^N`; `z0:real^N`]
                P2CM_NEAR_INV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "inv" o REWRITE_RULE[P2CI_NEAR_MATRIX]) THEN
  REWRITE_TAC[ltnorm2; LIFT_SUM; o_DEF] THEN
  MATCH_MP_TAC P2CI_ZERO_VSUM THEN REWRITE_TAC[LRG_INDEX_TUPLES_FINITE] THEN
  X_GEN_TAC `i:num->num` THEN DISCH_TAC THEN
  MATCH_MP_TAC P2CI_ZERO_VSUM THEN REWRITE_TAC[LRG_INDEX_TUPLES_FINITE] THEN
  X_GEN_TAC `j:num->num` THEN DISCH_TAC THEN
  MATCH_MP_TAC P2CI_ZERO_MUL THEN EXISTS_TAC `\y:real^N. vec 0:real^1` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC P2CI_ZERO_MUL THEN
  EXISTS_TAC `\y:real^N. lift(product(1..k)
                    (\m. matrix_inv((A0:real^N->real^N^N) y)$((i:num->num) m)$
                            ((j:num->num) m)))` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`z0:real^N`;
                 `\(m:num) (n:num) (y:real^N).
                     matrix_inv((As:num->real^N->real^N^N) n y)$((i:num->num) m)$
                       ((j:num->num) m)`;
                 `\(m:num) (y:real^N).
                     matrix_inv((A0:real^N->real^N^N) y)$((i:num->num) m)$((j:num->num) m)`;
                 `k:num`]
                P2CM_NEAR_PRODUCT) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  USE_THEN "inv" MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`i:num->num`; `k:num`; `m:num`] LRG_INDEX_TUPLES_RANGE) THEN
  MP_TAC(ISPECL [`j:num->num`; `k:num`; `m:num`] LRG_INDEX_TUPLES_RANGE) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let P2CM_TENSOR_FIELD_SUBSET = prove
 (`!k s t (tf:real^N->(num->real^N)->real).
     ltensor_field k s tf /\ t SUBSET s ==> ltensor_field k t tf`,
  REWRITE_TAC[ltensor_field] THEN SET_TAC[]);;

let P2CM_TNEAR_SUB = prove
 (`!k (z0:real^N) f g.
     p2ci_tnear k z0 f /\ p2ci_tnear k z0 g
     ==> p2ci_tnear k z0 (\n z u. f n z u - g n z u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2ci_tnear] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `r1:real` (X_CHOOSE_THEN `N1:num`
       (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "f")))) (LABEL_TAC "fn"))
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `r2:real` (X_CHOOSE_THEN `N2:num`
       (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "g")))) (LABEL_TAC "gn"))) THEN
  CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`min r1 r2`; `N1 + N2:num`] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "f" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
    USE_THEN "g" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `ball(z0:real^N,min r1 r2) SUBSET ball(z0,r1) /\
                  ball(z0:real^N,min r1 r2) SUBSET ball(z0,r2)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRG_TENSOR_FIELD_SUB THEN REWRITE_TAC[ETA_AX] THEN CONJ_TAC THEN
      MATCH_MP_TAC P2CM_TENSOR_FIELD_SUBSET THEN ASM_MESON_TAC[];
      GEN_TAC THEN REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
      REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      ASM_MESON_TAC[]];
    GEN_TAC THEN REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC P2CI_ZERO_SUB THEN
    ASM_REWRITE_TAC[]]);;

let P2CM_TNEAR_METRIC2 = prove
 (`!(z0:real^N) As Bs A0.
     p2ci_near z0 (\n. vectorize o As n) (vectorize o A0) /\
     p2ci_near z0 (\n. vectorize o Bs n) (vectorize o A0)
     ==> p2ci_tnear 2 z0 (\n z u. lmetric2 (Bs n) z u - lmetric2 (As n) z u)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `z0:real^N`;
                 `\n z u. lmetric2 ((Bs:num->real^N->real^N^N) n) z u -
                          lmetric2 (A0:real^N->real^N^N) z u`;
                 `\n z u. lmetric2 ((As:num->real^N->real^N^N) n) z u -
                          lmetric2 (A0:real^N->real^N^N) z u`] P2CM_TNEAR_SUB) THEN
  ASM_SIMP_TAC[P2CI_TNEAR_METRIC] THEN
  REWRITE_TAC[REAL_ARITH `(b - c) - (a - c):real = b - a`]);;

let P2CM_LCK_NEAR2 = prove
 (`!(z0:real^N) As Bs A0 m.
     p2cm_mnear z0 As A0 /\ p2ci_near z0 (\n. vectorize o Bs n) (vectorize o A0)
     ==> p2ci_near z0 (\n y. lift(lck_dist2 m (As n) (Bs n) y)) (\y. vec 0)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT2 o REWRITE_RULE[p2cm_mnear] o
              check (fun th -> can (find_term ((=) `p2cm_mnear:real^N->(num->real^N->real^N^N)->(real^N->real^N^N)->bool`)) (concl th))) THEN
  REWRITE_TAC[lck_dist2; LIFT_SUM; o_DEF] THEN
  MATCH_MP_TAC P2CI_ZERO_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `l:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`z0:real^N`; `As:num->real^N->real^N^N`; `A0:real^N->real^N^N`; `2 + l`;
                 `\n:num. lnabla_iter 2 l ((As:num->real^N->real^N^N) n)
                            (\z u. lmetric2 ((Bs:num->real^N->real^N^N) n) z u -
                                   lmetric2 (As n) z u)`]
                P2CM_LTNORM2_NEAR2) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`z0:real^N`; `As:num->real^N->real^N^N`; `A0:real^N->real^N^N`; `2`;
                 `\n:num z:real^N u:num->real^N.
                    lmetric2 ((Bs:num->real^N->real^N^N) n) z u - lmetric2 (As n) z u`]
                P2CM_TNEAR_ITER2) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2CM_TNEAR_METRIC2 THEN
    EXISTS_TAC `A0:real^N->real^N^N` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(ACCEPT_TAC o SPEC `l:num`)]);;


(* ------------------------------------------------------------------------- *)
(* The context of the local limit.  Entries p2cm_ent of the                 *)
(* smooth extensions FF n, closed boxes p2cm_box over a countable ball cover *)
(* (c i,r i) of V, a subsequence sub along which all space-time partials of *)
(* the entries converge uniformly on the boxes to H (i,p,q) l, and the      *)
(* pointwise limit p2cm_lim of the metrics.                                  *)
(* ------------------------------------------------------------------------- *)

let p2cm_ent = new_definition
 `p2cm_ent (FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod) n (p:num) (q:num) =
    \w. lift((matrify(FF n w):real^N^N)$p$q)`;;

let p2cm_box = new_definition
 `p2cm_box a b (c:num->real^N) r (i:num) =
    interval[lift a,lift b] PCROSS cball(c i,r i)`;;

let p2cm_ctx = new_definition
 `p2cm_ctx V a b (Gs:num->real->real^N->real^N^N)
           (FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod) ee c r (sub:num->num)
           (H:num#num#num->(num)list->real^(1,N)finite_sum->real^1) <=>
    open V /\ a < b /\
    (!n t. a <= t /\ t <= b ==> metric_field V (Gs n t)) /\
    (!n. lricci_flow V a b (Gs n)) /\
    (!n. &0 < ee n /\
         smooth_map_on (interval(lift(a - ee n),lift(b + ee n)) PCROSS V) (FF n) /\
         !t y. a <= t /\ t <= b /\ y IN V
               ==> FF n (pastecart (lift t) y) = vectorize(Gs n t y)) /\
    (!K. compact K /\ K SUBSET V
         ==> ?Lm. !n t y v. a <= t /\ t <= b /\ y IN K
                            ==> norm v pow 2 <= Lm * (v dot (Gs n t y ** v))) /\
    (!i. cball(c i,r i) SUBSET V) /\
    (!y. y IN V ==> ?i. &0 < r i /\ y IN ball(c i,r i)) /\
    (!m n. m < n ==> sub m < sub n) /\
    (!i p q l. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N) /\
               ALL (\j. 1 <= j /\ j <= dimindex(:(1,N)finite_sum)) l
               ==> H (i,p,q) l continuous_on p2cm_box a b c r i /\
                   !e. &0 < e
                       ==> ?K. !n w. K <= n /\ w IN p2cm_box a b c r i
                                     ==> norm(iterated_partial l (p2cm_ent FF (sub n) p q) w -
                                              H (i,p,q) l w) < e)`;;

let p2cm_lim = new_definition
 `p2cm_lim (Gs:num->real->real^N->real^N^N) (sub:num->num) t y =
    (lambda p q. drop(lim sequentially (\n. lift(Gs (sub n) t y$p$q)))):real^N^N`;;

(* The entries agree with the metrics on [a,b] x V; their extension domain. *)

let P2CM_CTX_ENT = prove
 (`!V a b (Gs:num->real->real^N->real^N^N) FF ee c r sub H n p q t y.
     p2cm_ctx V a b Gs FF ee c r sub H /\ a <= t /\ t <= b /\ y IN V
     ==> p2cm_ent FF n p q (pastecart (lift t) y) = lift(Gs n t y$p$q)`,
  REWRITE_TAC[p2cm_ctx; p2cm_ent] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MATRIFY_VECTORIZE]);;

let P2CM_CTX_DOMAIN = prove
 (`!V a b (Gs:num->real->real^N->real^N^N) FF ee c r sub H n i p q.
     p2cm_ctx V a b Gs FF ee c r sub H
     ==> open (interval(lift(a - ee n),lift(b + ee n)) PCROSS V) /\
         p2cm_box a b c r i SUBSET interval(lift(a - ee n),lift(b + ee n)) PCROSS V /\
         smooth_map_on (interval(lift(a - ee n),lift(b + ee n)) PCROSS V)
                       (p2cm_ent FF n p q)`,
  REWRITE_TAC[p2cm_ctx] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `n:num` o check (fun th ->
    can (find_term ((=) `vectorize:real^N^N->real^(N,N)finite_prod`)) (concl th) &&
    is_forall(concl th))) THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL];
    REWRITE_TAC[p2cm_box] THEN MATCH_MP_TAC PCROSS_MONO THEN
    ASM_REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN
    DISJ2_TAC THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[p2cm_ent] THEN
    SUBGOAL_THEN
     `(\w. lift((matrify((FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod) n w)
                 :real^N^N)$p$q)) =
      (\m:real^(N,N)finite_prod. lift((matrify m:real^N^N)$p$q)) o FF n`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN
    REWRITE_TAC[linear; MATRIFY_ADD; MATRIFY_CMUL; MATRIX_ADD_COMPONENT;
                MATRIX_CMUL_COMPONENT; LIFT_ADD; LIFT_CMUL]]);;

(* Pointwise limits on the boxes. *)

let P2CM_CTX_LIM = prove
 (`!V a b (Gs:num->real->real^N->real^N^N) FF ee c r sub H i p q t y.
     p2cm_ctx V a b Gs FF ee c r sub H /\
     1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N) /\
     a <= t /\ t <= b /\ y IN cball(c i,r i)
     ==> ((\n. lift(Gs (sub n) t y$p$q)) --> H (i,p,q) [] (pastecart (lift t) y))
         sequentially /\
         lift(p2cm_lim Gs sub t y$p$q) = H (i,p,q) [] (pastecart (lift t) y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN V` ASSUME_TAC THENL
   [UNDISCH_TAC `p2cm_ctx V a b (Gs:num->real->real^N->real^N^N) FF ee c r sub H` THEN
    REWRITE_TAC[p2cm_ctx] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\n. lift((Gs:num->real->real^N->real^N^N) (sub n) t y$p$q)) -->
     (H:num#num#num->(num)list->real^(1,N)finite_sum->real^1) (i,p,q) []
       (pastecart (lift t) y)) sequentially`
  ASSUME_TAC THENL
   [REWRITE_TAC[LIM_SEQUENTIALLY; dist] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`i:num`; `p:num`; `q:num`; `[]:num list`] o
      el 9 o CONJUNCTS o REWRITE_RULE[p2cm_ctx]) THEN
    ASM_REWRITE_TAC[ALL] THEN DISCH_THEN(MP_TAC o SPEC `e:real` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[iterated_partial] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `K:num` THEN DISCH_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `pastecart (lift t) (y:real^N)`]) THEN
    ASM_REWRITE_TAC[p2cm_box; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    MP_TAC(ISPECL [`V:real^N->bool`; `a:real`; `b:real`; `Gs:num->real->real^N->real^N^N`;
                   `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`;
                   `ee:num->real`; `c:num->real^N`; `r:num->real`; `sub:num->num`;
                   `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`;
                   `(sub:num->num) n`; `p:num`; `q:num`; `t:real`; `y:real^N`]
                  P2CM_CTX_ENT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[p2cm_lim; LAMBDA_BETA; LIFT_DROP] THEN
  MATCH_MP_TAC TENDSTO_LIM THEN ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY]);;

(* The time slices of the limit: smooth, with their partials given by H and *)
(* C-infinity convergence of the slices of the sequence near every point.    *)

let P2CM_CTX_SLICE = prove
 (`!V a b (Gs:num->real->real^N->real^N^N) FF ee c r sub H i p q t.
     p2cm_ctx V a b Gs FF ee c r sub H /\
     1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N) /\ a <= t /\ t <= b
     ==> smooth_map_on (ball(c i,r i)) (\y. lift(p2cm_lim Gs sub t y$p$q)) /\
         (!l y. ALL (\j. 1 <= j /\ j <= dimindex(:N)) l /\ y IN ball(c i,r i)
                ==> iterated_partial l (\y. lift(p2cm_lim Gs sub t y$p$q)) y =
                    H (i,p,q) (MAP (\k. 1 + k) l) (pastecart (lift t) y)) /\
         (!y0. y0 IN ball(c i,r i)
               ==> p2ci_near y0 (\n y. lift(Gs (sub n) t y$p$q))
                                (\y. lift(p2cm_lim Gs sub t y$p$q)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\n:num. p2cm_ent (FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod) ((sub:num->num) n) p q`;
    `(H:num#num#num->(num)list->real^(1,N)finite_sum->real^1) (i,p,q)`;
    `\n:num. interval(lift(a - (ee:num->real) ((sub:num->num) n)),lift(b + ee ((sub:num->num) n))) PCROSS
             (V:real^N->bool)`;
    `a:real`; `b:real`; `(c:num->real^N) i`; `(r:num->real) i`; `t:real`]
   P2CM_SLICE_LIMIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [GEN_TAC THEN
      MP_TAC(ISPECL [`V:real^N->bool`; `a:real`; `b:real`;
                     `Gs:num->real->real^N->real^N^N`;
                     `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`;
                     `ee:num->real`; `c:num->real^N`; `r:num->real`; `sub:num->num`;
                     `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`;
                     `(sub:num->num) n`; `i:num`; `p:num`; `q:num`] P2CM_CTX_DOMAIN) THEN
      ASM_REWRITE_TAC[p2cm_box];
      FIRST_ASSUM(MP_TAC o SPECL [`i:num`; `p:num`; `q:num`] o
        el 9 o CONJUNCTS o REWRITE_RULE[p2cm_ctx]) THEN
      ASM_REWRITE_TAC[p2cm_box] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN cball((c:num->real^N) i,(r:num->real) i) ==> y IN V`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p2cm_ctx V a b (Gs:num->real->real^N->real^N^N) FF ee c r sub H` THEN
    REWRITE_TAC[p2cm_ctx] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN ball((c:num->real^N) i,(r:num->real) i)
        ==> (H:num#num#num->(num)list->real^(1,N)finite_sum->real^1) (i,p,q) []
              (pastecart (lift t) y) =
            lift(p2cm_lim (Gs:num->real->real^N->real^N^N) (sub:num->num) t y$p$q) /\
            !n. p2cm_ent (FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod) ((sub:num->num) n) p q
                  (pastecart (lift t) y) =
                lift((Gs:num->real->real^N->real^N^N) ((sub:num->num) n) t y$p$q)`
  (LABEL_TAC "eq") THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN cball((c:num->real^N) i,(r:num->real) i)` ASSUME_TAC THENL
     [ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET]; ALL_TAC] THEN
    CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN
      MP_TAC(ISPECL [`V:real^N->bool`; `a:real`; `b:real`;
                     `Gs:num->real->real^N->real^N^N`;
                     `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`;
                     `ee:num->real`; `c:num->real^N`; `r:num->real`; `sub:num->num`;
                     `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`;
                     `i:num`; `p:num`; `q:num`; `t:real`; `y:real^N`] P2CM_CTX_LIM) THEN
      ASM_SIMP_TAC[];
      GEN_TAC THEN MATCH_MP_TAC P2CM_CTX_ENT THEN
      MAP_EVERY EXISTS_TAC [`V:real^N->bool`; `a:real`; `b:real`; `ee:num->real`;
                            `c:num->real^N`; `r:num->real`; `sub:num->num`;
                            `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`] THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "ip") (LABEL_TAC "nr"))) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `\y. (H:num#num#num->(num)list->real^(1,N)finite_sum->real^1) (i,p,q) []
                      (pastecart (lift t) y)` THEN
    ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`l:num list`; `y:real^N`] THEN STRIP_TAC THEN
    USE_THEN "ip" (MP_TAC o C MP
      (CONJ (ASSUME `ALL (\j. 1 <= j /\ j <= dimindex(:N)) l`)
            (ASSUME `(y:real^N) IN ball((c:num->real^N) i,(r:num->real) i)`)) o
      SPECL [`l:num list`; `y:real^N`]) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`l:num list`; `ball((c:num->real^N) i,(r:num->real) i)`;
                   `\y. lift(p2cm_lim (Gs:num->real->real^N->real^N^N) (sub:num->num) t y$p$q)`;
                   `\y. (H:num#num#num->(num)list->real^(1,N)finite_sum->real^1) (i,p,q) []
                          (pastecart (lift t) y)`] TEXT_ITERATED_PARTIAL_LOCAL_OPEN) THEN
    REWRITE_TAC[OPEN_BALL] THEN ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `y0:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC P2CI_NEAR_EQ THEN
    MAP_EVERY EXISTS_TAC
     [`\n y. p2cm_ent (FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod) ((sub:num->num) n) p q
               (pastecart (lift t) y)`;
      `\y. (H:num#num#num->(num)list->real^(1,N)finite_sum->real^1) (i,p,q) []
             (pastecart (lift t) y)`;
      `r i - dist((c:num->real^N) i,y0)`; `0`] THEN
    USE_THEN "nr" (MP_TAC o BETA_RULE o C MP
      (ASSUME `(y0:real^N) IN ball((c:num->real^N) i,(r:num->real) i)`) o
      SPEC `y0:real^N`) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `ball(y0:real^N,r i - dist((c:num->real^N) i,y0)) SUBSET ball(c i,r i)`
    ASSUME_TAC THENL
     [UNDISCH_TAC `(y0:real^N) IN ball((c:num->real^N) i,(r:num->real) i)` THEN
      REWRITE_TAC[SUBSET; IN_BALL] THEN CONV_TAC NORM_ARITH;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `(y0:real^N) IN ball((c:num->real^N) i,(r:num->real) i)` THEN
      REWRITE_TAC[IN_BALL] THEN REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
      USE_THEN "eq" (MP_TAC o SPEC `z:real^N`) THEN ANTS_TAC THENL
       [ASM SET_TAC[]; SIMP_TAC[]];
      REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
      USE_THEN "eq" (MP_TAC o SPEC `z:real^N`) THEN ANTS_TAC THENL
       [ASM SET_TAC[]; SIMP_TAC[]]]]);;


(* ------------------------------------------------------------------------- *)
(* The limit is a metric field at every time of [a,b] and a                  *)
(* local Ricci flow on (a,b).                                                *)
(* ------------------------------------------------------------------------- *)

let P2CM_CTX_LABELS th =
  EVERY (map2 LABEL_TAC ["oV"; "ab"; "mf"; "lf"; "ext"; "eqv"; "cb"; "cov"; "sub"; "H"]
              (CONJUNCTS (REWRITE_RULE[p2cm_ctx] th)));;

(* Entrywise convergence to the limit at every point of V. *)

let P2CM_CTX_ENTRY_LIM = prove
 (`!V a b (Gs:num->real->real^N->real^N^N) FF ee c r sub H t y p q.
     p2cm_ctx V a b Gs FF ee c r sub H /\ a <= t /\ t <= b /\ y IN V /\
     1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
     ==> ((\n. lift(Gs (sub n) t y$p$q)) --> lift(p2cm_lim Gs sub t y$p$q)) sequentially`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (fun th ->
    LABEL_TAC "ctx" th THEN P2CM_CTX_LABELS th) STRIP_ASSUME_TAC) THEN
  USE_THEN "cov" (MP_TAC o C MP (ASSUME `(y:real^N) IN V`) o SPEC `y:real^N`) THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `a:real`; `b:real`; `Gs:num->real->real^N->real^N^N`;
                 `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`;
                 `ee:num->real`; `c:num->real^N`; `r:num->real`; `sub:num->num`;
                 `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`;
                 `i:num`; `p:num`; `q:num`; `t:real`; `y:real^N`] P2CM_CTX_LIM) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET]; SIMP_TAC[]]);;

let P2CM_CTX_METRIC = prove
 (`!V a b (Gs:num->real->real^N->real^N^N) FF ee c r sub H t.
     p2cm_ctx V a b Gs FF ee c r sub H /\ a <= t /\ t <= b
     ==> metric_field V (p2cm_lim Gs sub t)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (fun th ->
    LABEL_TAC "ctx" th THEN P2CM_CTX_LABELS th) STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[metric_field] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`V:real^N->bool`; `p2cm_lim (Gs:num->real->real^N->real^N^N) (sub:num->num) t`]
                  LRG_SMOOTH_VECTORIZE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN STRIP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    USE_THEN "cov" (MP_TAC o C MP (ASSUME `(y:real^N) IN V`) o SPEC `y:real^N`) THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `ball((c:num->real^N) i,(r:num->real) i)` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN
    MP_TAC(ISPECL [`V:real^N->bool`; `a:real`; `b:real`; `Gs:num->real->real^N->real^N^N`;
                   `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`;
                   `ee:num->real`; `c:num->real^N`; `r:num->real`; `sub:num->num`;
                   `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`;
                   `i:num`; `p:num`; `q:num`; `t:real`] P2CM_CTX_SLICE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN CONJ_TAC THENL
   [SIMP_TAC[CART_EQ; TRANSP_COMPONENT; p2cm_lim; LAMBDA_BETA] THEN
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    X_GEN_TAC `n:num` THEN AP_TERM_TAC THEN
    USE_THEN "mf" (MP_TAC o REWRITE_RULE[metric_field] o
      C MP (CONJ (ASSUME `a <= t`) (ASSUME `t <= b`)) o
      SPECL [`(sub:num->num) n`; `t:real`]) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o C MP (ASSUME `(y:real^N) IN V`) o SPEC `y:real^N` o
               CONJUNCT2 o CONJUNCT2) THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o LAND_CONV) [GSYM th]) THEN
    REWRITE_TAC[TRANSP_COMPONENT];
    ALL_TAC] THEN
  X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
  USE_THEN "eqv" (MP_TAC o SPEC `{y:real^N}`) THEN
  ANTS_TAC THENL [REWRITE_TAC[COMPACT_SING] THEN ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_SING] THEN DISCH_THEN(X_CHOOSE_TAC `Lm:real`) THEN
  SUBGOAL_THEN
   `((\n. lift(v dot ((Gs:num->real->real^N->real^N^N) ((sub:num->num) n) t y ** v))) -->
     lift(v dot (p2cm_lim Gs (sub:num->num) t y ** v))) sequentially`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `((\n. vectorize((Gs:num->real->real^N->real^N^N) ((sub:num->num) n) t y)) -->
       vectorize(p2cm_lim Gs (sub:num->num) t y)) sequentially`
    MP_TAC THENL
     [REWRITE_TAC[LIM_VECTORIZE_COMPONENTWISE] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC P2CM_CTX_ENTRY_LIM THEN
      MAP_EVERY EXISTS_TAC [`V:real^N->bool`; `a:real`; `b:real`;
                            `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`;
                            `ee:num->real`; `c:num->real^N`; `r:num->real`;
                            `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o ISPEC `\m:real^(N,N)finite_prod. lift(v dot (matrify m ** v))` o
               MATCH_MP (REWRITE_RULE[IMP_CONJ] LIM_LINEAR)) THEN
    REWRITE_TAC[MATRIFY_VECTORIZE] THEN DISCH_THEN MATCH_MP_TAC THEN
    SUBGOAL_THEN `linear (\x:real^(N,N)finite_prod. matrify x ** (v:real^N))` ASSUME_TAC THENL
     [MP_TAC(INST_TYPE [] (LRG_BILINEAR_MATRIFY_MUL:thm)) THEN
      REWRITE_TAC[bilinear] THEN DISCH_THEN(MP_TAC o SPEC `v:real^N` o CONJUNCT2) THEN
      REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\m:real^(N,N)finite_prod. lift((v:real^N) dot (matrify m ** v))) =
      (\x. (\y. lift(v dot y)) ((\x. matrify x ** v) x))`
    SUBST1_TAC THENL [REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC LRG_LINEAR_COMPOSE_LAMBDA THEN ASM_REWRITE_TAC[LINEAR_LIFT_DOT];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(v:real^N) pow 2 <=
                drop(lift(Lm * (v dot (p2cm_lim (Gs:num->real->real^N->real^N^N)
                                         (sub:num->num) t y ** v))))`
  (ASSUME_TAC o REWRITE_RULE[LIFT_DROP]) THENL
   [MATCH_MP_TAC(ISPEC `sequentially` LIM_DROP_LBOUND) THEN
    EXISTS_TAC `\n. lift(Lm * (v dot ((Gs:num->real->real^N->real^N^N) ((sub:num->num) n)
                                        t y ** v)))` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; LIFT_DROP] THEN CONJ_TAC THENL
     [REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC LIM_CMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN BETA_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `Lm:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < Lm` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`(sub:num->num) 0`; `t:real`; `y:real^N`; `v:real^N`] o
      check (fun th -> is_forall(concl th) &&
                       can (find_term ((=) `Lm:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "mf" (MP_TAC o REWRITE_RULE[metric_field] o
      C MP (CONJ (ASSUME `a <= t`) (ASSUME `t <= b`)) o
      SPECL [`(sub:num->num) 0`; `t:real`]) THEN
    DISCH_THEN(MP_TAC o C MP (ASSUME `~(v:real^N = vec 0)`) o SPEC `v:real^N` o
               CONJUNCT2 o C MP (ASSUME `(y:real^N) IN V`) o SPEC `y:real^N` o
               CONJUNCT2 o CONJUNCT2) THEN
    SUBGOAL_THEN `&0 < norm(v:real^N) pow 2` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LT; NORM_POS_LT]; ALL_TAC] THEN
    SPEC_TAC(`v dot ((Gs:num->real->real^N->real^N^N) ((sub:num->num) 0) t y ** v)`,`x:real`) THEN
    SPEC_TAC(`norm(v:real^N) pow 2`,`w:real`) THEN
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    ASM_CASES_TAC `&0 < Lm` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `Lm * x <= &0` MP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= --Lm * x ==> Lm * x <= &0`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < Lm * (v dot (p2cm_lim (Gs:num->real->real^N->real^N^N) (sub:num->num) t y ** v))`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `norm(v:real^N) pow 2` THEN
    ASM_SIMP_TAC[REAL_POW_LT; NORM_POS_LT];
    ASM_SIMP_TAC[REAL_LT_MUL_EQ]]);;

(* Convergence at the base point of a near sequence. *)

let P2CM_NEAR_POINT = prove
 (`!(z0:real^M) (Fs:num->real^M->real^N) f.
     p2ci_near z0 Fs f ==> ((\n. Fs n z0) --> f z0) sequentially`,
  REWRITE_TAC[p2ci_near; LIM_SEQUENTIALLY; dist] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `M:num` THEN DISCH_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[CENTRE_IN_BALL]);;

(* The limit on the open boxes over the balls of the cover. *)

let P2CM_CTX_REP = prove
 (`!V a b (Gs:num->real->real^N->real^N^N) FF ee c r sub H i p q.
     p2cm_ctx V a b Gs FF ee c r sub H /\
     1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
     ==> (!w. w IN interval(lift a,lift b) PCROSS ball(c i,r i)
              ==> lift(p2cm_lim Gs sub (drop(fstcart w)) (sndcart w)$p$q) = H (i,p,q) [] w) /\
         smooth_map_on (interval(lift a,lift b) PCROSS ball(c i,r i)) (H (i,p,q) []) /\
         (!l w. ALL (\j. 1 <= j /\ j <= dimindex(:(1,N)finite_sum)) l /\
                w IN interval(lift a,lift b) PCROSS ball(c i,r i)
                ==> iterated_partial l (H (i,p,q) []) w = H (i,p,q) l w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                FSTCART_PASTECART; SNDCART_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`tt:real^1`; `y:real^N`] THEN
    REWRITE_TAC[LIFT_DROP] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:real^N->bool`; `a:real`; `b:real`; `Gs:num->real->real^N->real^N^N`;
                   `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`;
                   `ee:num->real`; `c:num->real^N`; `r:num->real`; `sub:num->num`;
                   `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`;
                   `i:num`; `p:num`; `q:num`; `drop tt`; `y:real^N`] P2CM_CTX_LIM) THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET]];
      SIMP_TAC[]];
    MATCH_MP_TAC P2CM_OPEN_BOX_LIMIT THEN
    EXISTS_TAC `\n:num. p2cm_ent (FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod)
                          ((sub:num->num) n) p q` THEN
    EXISTS_TAC `\n:num. interval(lift(a - (ee:num->real) ((sub:num->num) n)),
                                 lift(b + ee ((sub:num->num) n))) PCROSS (V:real^N->bool)` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [GEN_TAC THEN
      MP_TAC(ISPECL [`V:real^N->bool`; `a:real`; `b:real`;
                     `Gs:num->real->real^N->real^N^N`;
                     `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`;
                     `ee:num->real`; `c:num->real^N`; `r:num->real`; `sub:num->num`;
                     `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`;
                     `(sub:num->num) n`; `i:num`; `p:num`; `q:num`] P2CM_CTX_DOMAIN) THEN
      ASM_REWRITE_TAC[p2cm_box];
      FIRST_ASSUM(MP_TAC o SPECL [`i:num`; `p:num`; `q:num`] o
        el 9 o CONJUNCTS o REWRITE_RULE[p2cm_ctx]) THEN
      ASM_REWRITE_TAC[p2cm_box] THEN MESON_TAC[]]]);;

(* Convergence of the Ricci tensors at every point. *)

let P2CM_CTX_RICCI_LIM = prove
 (`!V a b (Gs:num->real->real^N->real^N^N) FF ee c r sub H t y p q.
     p2cm_ctx V a b Gs FF ee c r sub H /\ a <= t /\ t <= b /\ y IN V /\
     1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
     ==> ((\n. lift(lricci (Gs (sub n) t) y (basis p) (basis q))) -->
          lift(lricci (p2cm_lim Gs sub t) y (basis p) (basis q))) sequentially`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (fun th ->
    LABEL_TAC "ctx" th THEN P2CM_CTX_LABELS th) STRIP_ASSUME_TAC) THEN
  USE_THEN "cov" (MP_TAC o C MP (ASSUME `(y:real^N) IN V`) o SPEC `y:real^N`) THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `a:real`; `b:real`; `Gs:num->real->real^N->real^N^N`;
                 `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`;
                 `ee:num->real`; `c:num->real^N`; `r:num->real`; `sub:num->num`;
                 `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`; `t:real`]
                P2CM_CTX_METRIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `p2ci_near y (\n. vectorize o (Gs:num->real->real^N->real^N^N) ((sub:num->num) n) t)
                (vectorize o p2cm_lim Gs sub t)`
  ASSUME_TAC THENL
   [REWRITE_TAC[P2CI_NEAR_MATRIX] THEN MAP_EVERY X_GEN_TAC [`p':num`; `q':num`] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`V:real^N->bool`; `a:real`; `b:real`; `Gs:num->real->real^N->real^N^N`;
                   `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`;
                   `ee:num->real`; `c:num->real^N`; `r:num->real`; `sub:num->num`;
                   `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`;
                   `i:num`; `p':num`; `q':num`; `t:real`] P2CM_CTX_SLICE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\n:num. (Gs:num->real->real^N->real^N^N) ((sub:num->num) n) t`;
                 `p2cm_lim (Gs:num->real->real^N->real^N^N) (sub:num->num) t`; `y:real^N`]
                P2CM_NEAR_EVAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`V:real^N->bool`; `p2cm_lim (Gs:num->real->real^N->real^N^N)
                     (sub:num->num) t`; `y:real^N`] LRG_METRIC_INVERTIBLE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `p2ch_xric (dimindex(:N)) p q`) THEN
  ANTS_TAC THENL [MATCH_MP_TAC P2CH_OK_XRIC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP P2CM_NEAR_POINT) THEN BETA_TAC THEN
  SUBGOAL_THEN
   `(!n. p2ch_eval (\s:real. (Gs:num->real->real^N->real^N^N) ((sub:num->num) n) t)
                   (p2ch_xric (dimindex(:N)) p q) (&0) y =
         lricci (Gs (sub n) t) y (basis p) (basis q)) /\
    p2ch_eval (\s:real. p2cm_lim (Gs:num->real->real^N->real^N^N) (sub:num->num) t)
              (p2ch_xric (dimindex(:N)) p q) (&0) y =
    lricci (p2cm_lim Gs sub t) y (basis p) (basis q)`
  (fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC P2CH_EVAL_XRIC THEN EXISTS_TAC `V:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "mf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2CH_EVAL_XRIC THEN EXISTS_TAC `V:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

(* The time partial of the limit entries is -2 times its Ricci tensor. *)

let P2CM_CTX_TIME_PARTIAL = prove
 (`!V a b (Gs:num->real->real^N->real^N^N) FF ee c r sub H i t y p q.
     p2cm_ctx V a b Gs FF ee c r sub H /\ a < t /\ t < b /\ y IN ball(c i,r i) /\
     1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
     ==> H (i,p,q) [1] (pastecart (lift t) y) =
         lift(--(&2) * lricci (p2cm_lim Gs sub t) y (basis p) (basis q))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (fun th ->
    LABEL_TAC "ctx" th THEN P2CM_CTX_LABELS th) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:real^N) IN V` ASSUME_TAC THENL
   [USE_THEN "cb" (MP_TAC o SPEC `i:num`) THEN
    MP_TAC(ISPECL [`(c:num->real^N) i`; `(r:num->real) i`] BALL_SUBSET_CBALL) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
  EXISTS_TAC `\n. iterated_partial [1]
                    (p2cm_ent (FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod)
                       ((sub:num->num) n) p q) (pastecart (lift t) (y:real^N))` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [REWRITE_TAC[LIM_SEQUENTIALLY; dist] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "H" (MP_TAC o SPECL [`i:num`; `p:num`; `q:num`; `[1]`]) THEN
    REWRITE_TAC[ALL; DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o C MP (ASSUME `&0 < e`) o SPEC `e:real` o CONJUNCT2) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `K:num` THEN DISCH_TAC THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[p2cm_box; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. iterated_partial [1]
          (p2cm_ent (FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod)
             ((sub:num->num) n) p q) (pastecart (lift t) (y:real^N)) =
        lift(--(&2) * lricci ((Gs:num->real->real^N->real^N^N) (sub n) t) y
                             (basis p) (basis q))`
  (fun th -> REWRITE_TAC[th]) THENL
   [X_GEN_TAC `n:num` THEN
    SUBGOAL_THEN `pastecart (lift t) (y:real^N) IN interval(lift a,lift b) PCROSS V`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP]; ALL_TAC] THEN
    MP_TAC(ISPECL [`[1]`; `interval(lift a,lift b) PCROSS (V:real^N->bool)`;
                   `p2cm_ent (FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod)
                      ((sub:num->num) n) p q`;
                   `\w. lift((Gs:num->real->real^N->real^N^N) ((sub:num->num) n)
                                (drop(fstcart w)) (sndcart w)$p$q)`]
                  TEXT_ITERATED_PARTIAL_LOCAL_OPEN) THEN
    ANTS_TAC THENL
     [USE_THEN "oV" (fun th -> SIMP_TAC[th; OPEN_PCROSS; OPEN_INTERVAL]) THEN
      REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                  FSTCART_PASTECART; SNDCART_PASTECART] THEN
      MAP_EVERY X_GEN_TAC [`tt:real^1`; `z:real^N`] THEN REWRITE_TAC[LIFT_DROP] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `tt = lift(drop tt)` (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o
                                                    LAND_CONV) [th]) THENL
       [REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
      MATCH_MP_TAC P2CM_CTX_ENT THEN
      MAP_EVERY EXISTS_TAC [`V:real^N->bool`; `a:real`; `b:real`; `ee:num->real`;
                            `c:num->real^N`; `r:num->real`; `sub:num->num`;
                            `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `pastecart (lift t) (y:real^N) IN interval(lift a,lift b) PCROSS V`)]) THEN
    MP_TAC(ISPECL [`V:real^N->bool`; `a:real`; `b:real`;
                   `(Gs:num->real->real^N->real^N^N) ((sub:num->num) n)`] P2CH_ST_PARTIAL) THEN
    USE_THEN "lf" (fun th -> REWRITE_TAC[th]) THEN
    DISCH_THEN(MP_TAC o SPECL [`[1]`; `PHE_G p q`]) THEN
    REWRITE_TAC[ALL; p2ch_ok; DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o C MP
      (ASSUME `pastecart (lift t) (y:real^N) IN interval(lift a,lift b) PCROSS V`) o
      SPEC `pastecart (lift t) (y:real^N)`) THEN
    REWRITE_TAC[p2ch_eval; p2ch_stx; p2ch_dt; FSTCART_PASTECART; SNDCART_PASTECART;
                LIFT_DROP] THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC P2CH_EVAL_XRIC THEN EXISTS_TAC `V:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "mf" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC LIM_CMUL THEN
  MATCH_MP_TAC P2CM_CTX_RICCI_LIM THEN
  MAP_EVERY EXISTS_TAC [`V:real^N->bool`; `a:real`; `b:real`;
                        `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`;
                        `ee:num->real`; `c:num->real^N`; `r:num->real`;
                        `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* The limit is a local Ricci flow on (a,b). *)

let P2CM_CTX_FLOW = prove
 (`!V a b (Gs:num->real->real^N->real^N^N) FF ee c r sub H.
     p2cm_ctx V a b Gs FF ee c r sub H ==> lricci_flow V a b (p2cm_lim Gs sub)`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> LABEL_TAC "ctx" th THEN P2CM_CTX_LABELS th) THEN
  REWRITE_TAC[lricci_flow] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!t. a < t /\ t < b
                    ==> metric_field V (p2cm_lim (Gs:num->real->real^N->real^N^N)
                                          (sub:num->num) t)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CM_CTX_METRIC THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`;
                          `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`;
                          `ee:num->real`; `c:num->real^N`; `r:num->real`;
                          `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!z. z IN interval(lift a,lift b) PCROSS V
        ==> ?i. &0 < (r:num->real) i /\ (sndcart z) IN ball((c:num->real^N) i,r i) /\
                z IN interval(lift a,lift b) PCROSS ball(c i,r i)`
  (LABEL_TAC "loc") THENL
   [REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; SNDCART_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`tt:real^1`; `y:real^N`] THEN STRIP_TAC THEN
    USE_THEN "cov" (MP_TAC o C MP (ASSUME `(y:real^N) IN V`) o SPEC `y:real^N`) THEN
    MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `(\z. (vectorize:real^N^N->real^(N,N)finite_prod)
           (p2cm_lim (Gs:num->real->real^N->real^N^N) (sub:num->num)
                     (drop(fstcart z)) (sndcart z))) =
      vectorize o (\z. p2cm_lim Gs sub (drop(fstcart z)) (sndcart z))`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MP_TAC(ISPECL [`interval(lift a,lift b) PCROSS (V:real^N->bool)`;
                   `\z:real^(1,N)finite_sum. p2cm_lim (Gs:num->real->real^N->real^N^N)
                       (sub:num->num) (drop(fstcart z)) (sndcart z)`]
                  LRG_SMOOTH_VECTORIZE) THEN
    USE_THEN "oV" (fun th -> SIMP_TAC[th; OPEN_PCROSS; OPEN_INTERVAL]) THEN
    DISCH_THEN(K ALL_TAC) THEN
    MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN STRIP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN
    USE_THEN "oV" (fun th -> SIMP_TAC[th; OPEN_PCROSS; OPEN_INTERVAL]) THEN
    X_GEN_TAC `z:real^(1,N)finite_sum` THEN DISCH_TAC THEN
    USE_THEN "loc" (MP_TAC o C MP (ASSUME `z IN interval(lift a,lift b) PCROSS
                                              (V:real^N->bool)`) o SPEC `z:real^(1,N)finite_sum`) THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `interval(lift a,lift b) PCROSS ball((c:num->real^N) i,(r:num->real) i)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_BALL] THEN
    MP_TAC(ISPECL [`V:real^N->bool`; `a:real`; `b:real`; `Gs:num->real->real^N->real^N^N`;
                   `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`;
                   `ee:num->real`; `c:num->real^N`; `r:num->real`; `sub:num->num`;
                   `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`;
                   `i:num`; `p:num`; `q:num`] P2CM_CTX_REP) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `(H:num#num#num->(num)list->real^(1,N)finite_sum->real^1) (i,p,q) []` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`; `p:num`; `q:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pastecart (lift t) (y:real^N) IN interval(lift a,lift b) PCROSS V`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP]; ALL_TAC] THEN
  USE_THEN "loc" (MP_TAC o C MP
    (ASSUME `pastecart (lift t) (y:real^N) IN interval(lift a,lift b) PCROSS V`) o
    SPEC `pastecart (lift t) (y:real^N)`) THEN
  REWRITE_TAC[SNDCART_PASTECART] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `a:real`; `b:real`; `Gs:num->real->real^N->real^N^N`;
                 `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`;
                 `ee:num->real`; `c:num->real^N`; `r:num->real`; `sub:num->num`;
                 `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`;
                 `i:num`; `p:num`; `q:num`] P2CM_CTX_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rep") (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pl"))) THEN
  ABBREV_TAC `U = interval(lift a,lift b) PCROSS ball((c:num->real^N) i,(r:num->real) i)` THEN
  SUBGOAL_THEN `open(U:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_BALL]; ALL_TAC] THEN
  SUBGOAL_THEN `pastecart (lift t) (y:real^N) IN U` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP];
    ALL_TAC] THEN
  ABBREV_TAC `Fp = \w. lift(p2cm_lim (Gs:num->real->real^N->real^N^N) (sub:num->num)
                                 (drop(fstcart w)) (sndcart w)$p$q)` THEN
  SUBGOAL_THEN `!w. w IN U ==> (Fp:real^(1,N)finite_sum->real^1) w =
                               (H:num#num#num->(num)list->real^(1,N)finite_sum->real^1)
                                 (i,p,q) [] w`
  ASSUME_TAC THENL
   [EXPAND_TAC "Fp" THEN X_GEN_TAC `w:real^(1,N)finite_sum` THEN DISCH_TAC THEN
    USE_THEN "rep" MATCH_MP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U (Fp:real^(1,N)finite_sum->real^1)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `(H:num#num#num->(num)list->real^(1,N)finite_sum->real^1) (i,p,q) []` THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Fp:real^(1,N)finite_sum->real^1`; `t:real`; `y:real^N`]
                PDE_ST_TIME_REAL_DERIV) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^(1,N)finite_sum->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXPAND_TAC "Fp" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  MATCH_MP_TAC(MESON[]
   `(x:real) = y ==> (f has_real_derivative x) net ==> (f has_real_derivative y) net`) THEN
  SUBGOAL_THEN
   `partial_derivative 1
      (\w. lift(p2cm_lim (Gs:num->real->real^N->real^N^N) (sub:num->num)
                  (drop(fstcart w)) (sndcart w)$p$q)) (pastecart (lift t) y) =
    (H:num#num#num->(num)list->real^(1,N)finite_sum->real^1) (i,p,q) [1]
      (pastecart (lift t) y)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`[1]`; `U:real^(1,N)finite_sum->bool`;
                   `Fp:real^(1,N)finite_sum->real^1`;
                   `(H:num#num#num->(num)list->real^(1,N)finite_sum->real^1) (i,p,q) []`]
                  TEXT_ITERATED_PARTIAL_LOCAL_OPEN) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o C MP (ASSUME `pastecart (lift t) (y:real^N) IN U`) o
               SPEC `pastecart (lift t) (y:real^N)`) THEN
    REWRITE_TAC[iterated_partial] THEN EXPAND_TAC "Fp" THEN REWRITE_TAC[ETA_AX] THEN
    DISCH_THEN SUBST1_TAC THEN
    USE_THEN "pl" (MP_TAC o SPECL [`[1]`; `pastecart (lift t) (y:real^N)`]) THEN
    REWRITE_TAC[ALL; DIMINDEX_FINITE_SUM; DIMINDEX_1; iterated_partial] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `pastecart (lift t) (y:real^N) IN U` THEN EXPAND_TAC "U" THEN
      REWRITE_TAC[];
      REWRITE_TAC[ETA_AX]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `a:real`; `b:real`; `Gs:num->real->real^N->real^N^N`;
                 `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`;
                 `ee:num->real`; `c:num->real^N`; `r:num->real`; `sub:num->num`;
                 `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`;
                 `i:num`; `t:real`; `y:real^N`; `p:num`; `q:num`] P2CM_CTX_TIME_PARTIAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN USE_THEN "ctx" ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LIFT_DROP]);;


(* ------------------------------------------------------------------------- *)
(* The lck convergence is uniform over [a,b] x K.  Along converging times the *)
(* slices of the limit, and the slices of the sequence along any indices     *)
(* tending to infinity, converge near every point with all spatial           *)
(* derivatives to the slice of the limit time (with a moving base metric, as *)
(* above); a compactness argument on [a,b] x K concludes.                    *)
(* ------------------------------------------------------------------------- *)

(* Uniform continuity in time of the limit partials on a box. *)

let P2CM_CTX_SLICE_UNIF = prove
 (`!V a b (Gs:num->real->real^N->real^N^N) FF ee c r sub H i p q l ts t0.
     p2cm_ctx V a b Gs FF ee c r sub H /\
     1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N) /\
     ALL (\j. 1 <= j /\ j <= dimindex(:N)) l /\
     (!j. a <= ts j /\ ts j <= b) /\ a <= t0 /\ t0 <= b /\
     ((\j. lift(ts j)) --> lift t0) sequentially
     ==> !e. &0 < e
             ==> ?J. !j z. J <= j /\ z IN cball(c i,r i)
                           ==> norm(H (i,p,q) (MAP (\k. 1 + k) l) (pastecart (lift(ts j)) z) -
                                    H (i,p,q) (MAP (\k. 1 + k) l) (pastecart (lift t0) z))
                               < e`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (fun th ->
    LABEL_TAC "ctx" th THEN P2CM_CTX_LABELS th) STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(H:num#num#num->(num)list->real^(1,N)finite_sum->real^1) (i,p,q) (MAP (\k. 1 + k) l)
      uniformly_continuous_on p2cm_box a b (c:num->real^N) r i`
  MP_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIFORMLY_CONTINUOUS THEN CONJ_TAC THENL
     [USE_THEN "H" (MP_TAC o SPECL [`i:num`; `p:num`; `q:num`;
                                    `MAP (\k. 1 + k) (l:num list)`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `ALL (\j. 1 <= j /\ j <= dimindex(:N)) l` THEN
        REWRITE_TAC[ALL_MAP; o_DEF; DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN
        MATCH_MP_TAC MONO_ALL THEN ARITH_TAC;
        SIMP_TAC[]];
      REWRITE_TAC[p2cm_box] THEN
      SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL; COMPACT_CBALL]];
    ALL_TAC] THEN
  REWRITE_TAC[uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `((\j. lift((ts:num->real) j)) --> lift t0) sequentially` THEN
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN DISCH_THEN(MP_TAC o SPEC `d:real`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `J:num` THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`j:num`; `z:real^N`] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM dist] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[p2cm_box; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
  REWRITE_TAC[dist; PDE_ST_PASTECART_DIST] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[dist; GSYM LIFT_SUB; NORM_LIFT]);;

(* Near sequences of slices along converging times. *)

let P2CM_CTX_NEAR_SEQ = prove
 (`!V a b (Gs:num->real->real^N->real^N^N) FF ee c r sub H i ts t0 ns y0.
     p2cm_ctx V a b Gs FF ee c r sub H /\
     (!j. a <= ts j /\ ts j <= b) /\ a <= t0 /\ t0 <= b /\
     ((\j. lift(ts j)) --> lift t0) sequentially /\
     (!j. j <= ns j) /\ y0 IN ball(c i,r i)
     ==> p2cm_mnear y0 (\j. p2cm_lim Gs sub (ts j)) (p2cm_lim Gs sub t0) /\
         p2ci_near y0 (\j. vectorize o Gs (sub (ns j)) (ts j))
                      (vectorize o p2cm_lim Gs sub t0)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (fun th ->
    LABEL_TAC "ctx" th THEN P2CM_CTX_LABELS th) STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `rho = (r:num->real) i - dist((c:num->real^N) i,y0)` THEN
  SUBGOAL_THEN `&0 < rho /\ ball(y0:real^N,rho) SUBSET ball((c:num->real^N) i,(r:num->real) i)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN
    UNDISCH_TAC `(y0:real^N) IN ball((c:num->real^N) i,(r:num->real) i)` THEN
    REWRITE_TAC[SUBSET; IN_BALL] THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN `ball((c:num->real^N) i,(r:num->real) i) SUBSET V /\
                ball((c:num->real^N) i,(r:num->real) i) SUBSET cball(c i,r i)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[BALL_SUBSET_CBALL] THEN USE_THEN "cb" (MP_TAC o SPEC `i:num`) THEN
    MP_TAC(ISPECL [`(c:num->real^N) i`; `(r:num->real) i`] BALL_SUBSET_CBALL) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. a <= t /\ t <= b
                    ==> metric_field V (p2cm_lim (Gs:num->real->real^N->real^N^N)
                                          (sub:num->num) t)`
  (LABEL_TAC "lmf") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CM_CTX_METRIC THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`;
                          `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`;
                          `ee:num->real`; `c:num->real^N`; `r:num->real`;
                          `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the slices of the limit and their partials on the ball of the cover *)
  SUBGOAL_THEN
   `!t p q. a <= t /\ t <= b /\
            1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
            ==> smooth_map_on (ball((c:num->real^N) i,(r:num->real) i))
                  (\y. lift(p2cm_lim (Gs:num->real->real^N->real^N^N) (sub:num->num)
                              t y$p$q)) /\
                (!l y. ALL (\j. 1 <= j /\ j <= dimindex(:N)) l /\ y IN ball(c i,r i)
                       ==> iterated_partial l (\y. lift(p2cm_lim Gs sub t y$p$q)) y =
                           (H:num#num#num->(num)list->real^(1,N)finite_sum->real^1)
                             (i,p,q) (MAP (\k. 1 + k) l) (pastecart (lift t) y))`
  (LABEL_TAC "sl") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:real^N->bool`; `a:real`; `b:real`; `Gs:num->real->real^N->real^N^N`;
                   `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`;
                   `ee:num->real`; `c:num->real^N`; `r:num->real`; `sub:num->num`;
                   `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`;
                   `i:num`; `p:num`; `q:num`; `t:real`] P2CM_CTX_SLICE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN USE_THEN "ctx" ACCEPT_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[p2cm_mnear] THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`rho:real`; `0`] THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ALL_TAC; GEN_TAC THEN REWRITE_TAC[LE_0] THEN BETA_TAC] THEN
      MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `V:real^N->bool` THEN
      REWRITE_TAC[OPEN_BALL] THEN
      (CONJ_TAC THENL [USE_THEN "lmf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM SET_TAC[]]);
      ALL_TAC] THEN
    REWRITE_TAC[P2CI_NEAR_MATRIX] THEN MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN
    STRIP_TAC THEN MATCH_MP_TAC P2CI_NEAR_OF_PARTIALS THEN EXISTS_TAC `rho:real` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXISTS_TAC `0` THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `ball((c:num->real^N) i,(r:num->real) i)` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "sl" (MP_TAC o SPECL [`(ts:num->real) j`; `p:num`; `q:num`]) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `ball((c:num->real^N) i,(r:num->real) i)` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "sl" (MP_TAC o SPECL [`t0:real`; `p:num`; `q:num`]) THEN
      ASM_SIMP_TAC[];
      X_GEN_TAC `l:num list` THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`V:real^N->bool`; `a:real`; `b:real`; `Gs:num->real->real^N->real^N^N`;
                     `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`;
                     `ee:num->real`; `c:num->real^N`; `r:num->real`; `sub:num->num`;
                     `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`;
                     `i:num`; `p:num`; `q:num`; `l:num list`; `ts:num->real`; `t0:real`]
                    P2CM_CTX_SLICE_UNIF) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN USE_THEN "ctx" ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o C MP (ASSUME `&0 < e`) o SPEC `e:real`) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `J:num` THEN DISCH_TAC THEN
      MAP_EVERY X_GEN_TAC [`j:num`; `z:real^N`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(z:real^N) IN ball((c:num->real^N) i,(r:num->real) i)` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      USE_THEN "sl" (MP_TAC o SPECL [`(ts:num->real) j`; `p:num`; `q:num`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPECL [`l:num list`; `z:real^N`] o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      USE_THEN "sl" (MP_TAC o SPECL [`t0:real`; `p:num`; `q:num`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPECL [`l:num list`; `z:real^N`] o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[P2CI_NEAR_MATRIX] THEN MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN
  STRIP_TAC THEN MATCH_MP_TAC P2CI_NEAR_OF_PARTIALS THEN EXISTS_TAC `rho:real` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!j. smooth_map_on V
          (\y. lift((Gs:num->real->real^N->real^N^N) ((sub:num->num) ((ns:num->num) j))
                      ((ts:num->real) j) y$p$q))`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC PDE_SMOOTH_G_ENTRY THEN REWRITE_TAC[ETA_AX] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "mf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [EXISTS_TAC `0` THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `V:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `ball((c:num->real^N) i,(r:num->real) i)` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "sl" (MP_TAC o SPECL [`t0:real`; `p:num`; `q:num`]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `a:real`; `b:real`; `Gs:num->real->real^N->real^N^N`;
                 `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`;
                 `ee:num->real`; `c:num->real^N`; `r:num->real`; `sub:num->num`;
                 `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`;
                 `i:num`; `p:num`; `q:num`; `l:num list`; `ts:num->real`; `t0:real`]
                P2CM_CTX_SLICE_UNIF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN USE_THEN "ctx" ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `J1:num`) THEN
  USE_THEN "H" (MP_TAC o SPECL [`i:num`; `p:num`; `q:num`; `MAP (\k. 1 + k) (l:num list)`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ALL (\j. 1 <= j /\ j <= dimindex(:N)) l` THEN
    REWRITE_TAC[ALL_MAP; o_DEF; DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN
    MATCH_MP_TAC MONO_ALL THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2` o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `K1:num`) THEN EXISTS_TAC `J1 + K1:num` THEN
  MAP_EVERY X_GEN_TAC [`j:num`; `z:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^N) IN ball((c:num->real^N) i,(r:num->real) i) /\ z IN V /\
                z IN cball(c i,r i)`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  USE_THEN "sl" (MP_TAC o SPECL [`t0:real`; `p:num`; `q:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`l:num list`; `z:real^N`] o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `iterated_partial l
      (\y. lift((Gs:num->real->real^N->real^N^N) ((sub:num->num) ((ns:num->num) j))
                  ((ts:num->real) j) y$p$q)) z =
    iterated_partial (MAP (\k. 1 + k) l)
      (p2cm_ent (FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod) (sub (ns j)) p q)
      (pastecart (lift(ts j)) z)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`l:num list`; `V:real^N->bool`;
                   `\y. lift((Gs:num->real->real^N->real^N^N) ((sub:num->num) ((ns:num->num) j))
                               ((ts:num->real) j) y$p$q)`;
                   `\y. p2cm_ent (FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod)
                          ((sub:num->num) ((ns:num->num) j)) p q (pastecart (lift((ts:num->real) j)) y)`]
                  TEXT_ITERATED_PARTIAL_LOCAL_OPEN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2CM_CTX_ENT THEN
      MAP_EVERY EXISTS_TAC [`V:real^N->bool`; `a:real`; `b:real`; `ee:num->real`;
                            `c:num->real^N`; `r:num->real`; `sub:num->num`;
                            `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`] THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "ctx" ACCEPT_TAC;
      ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(z:real^N) IN V`)]) THEN
    MP_TAC(ISPECL [`V:real^N->bool`; `a:real`; `b:real`; `Gs:num->real->real^N->real^N^N`;
                   `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`;
                   `ee:num->real`; `c:num->real^N`; `r:num->real`; `sub:num->num`;
                   `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`;
                   `(sub:num->num) ((ns:num->num) j)`; `i:num`; `p:num`; `q:num`]
                  P2CM_CTX_DOMAIN) THEN
    ANTS_TAC THENL [USE_THEN "ctx" ACCEPT_TAC; STRIP_TAC] THEN
    MATCH_MP_TAC PDE_ST_SLICE_ITERATED THEN
    EXISTS_TAC `interval(lift(a - (ee:num->real) ((sub:num->num) ((ns:num->num) j))),
                         lift(b + ee (sub (ns j)))) PCROSS (V:real^N->bool)` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (find_term ((=) `p2cm_box:real->real->(num->real^N)->(num->real)->num->real^(1,N)finite_sum->bool`)) (concl th))) THEN
    REWRITE_TAC[p2cm_box; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(NORM_ARITH
   `!x y z:real^1 e. norm(x - y) < e / &2 /\ norm(y - z) < e / &2 ==> norm(x - z) < e`) THEN
  EXISTS_TAC `(H:num#num#num->(num)list->real^(1,N)finite_sum->real^1) (i,p,q)
                (MAP (\k. 1 + k) l) (pastecart (lift((ts:num->real) j)) z)` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `K1:num`)) (concl th))) THEN
    ASM_REWRITE_TAC[p2cm_box; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    MP_TAC(SPEC `j:num` (ASSUME `!j:num. j <= (ns:num->num) j`)) THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `J1:num`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* The uniform lck convergence. *)

let P2CM_CTX_LCK = prove
 (`!V a b (Gs:num->real->real^N->real^N^N) FF ee c r sub H K m e.
     p2cm_ctx V a b Gs FF ee c r sub H /\ compact K /\ K SUBSET V /\ &0 < e
     ==> ?N. !n t y. N <= n /\ a <= t /\ t <= b /\ y IN K
                     ==> lck_dist2 m (p2cm_lim Gs sub t) (Gs (sub n) t) y < e`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (fun th ->
    LABEL_TAC "ctx" th THEN P2CM_CTX_LABELS th) STRIP_ASSUME_TAC) THEN
  REFUTE_THEN(MP_TAC o REWRITE_RULE[NOT_EXISTS_THM; NOT_FORALL_THM; NOT_IMP; REAL_NOT_LT;
                                     SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `nn:num->num` (X_CHOOSE_THEN `tt:num->real`
    (X_CHOOSE_THEN `yy:num->real^N` (LABEL_TAC "bad")))) THEN
  SUBGOAL_THEN `compact(interval[lift a,lift b] PCROSS (K:real^N->bool))` MP_TAC THENL
   [ASM_SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [compact] THEN
  DISCH_THEN(MP_TAC o SPEC `\N. pastecart (lift((tt:num->real) N)) ((yy:num->real^N) N)`) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `N:num` THEN REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    USE_THEN "bad" (MP_TAC o SPEC `N:num`) THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[o_DEF] THEN
  DISCH_THEN(X_CHOOSE_THEN `w0:real^(1,N)finite_sum` (X_CHOOSE_THEN `phi:num->num`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `t0 = drop(fstcart(w0:real^(1,N)finite_sum))` THEN
  ABBREV_TAC `y0 = sndcart(w0:real^(1,N)finite_sum)` THEN
  SUBGOAL_THEN `w0 = pastecart (lift t0) (y0:real^N)` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["t0"; "y0"] THEN REWRITE_TAC[LIFT_DROP; PASTECART_FST_SND];
    ALL_TAC] THEN
  UNDISCH_TAC `pastecart (lift t0) (y0:real^N) IN interval[lift a,lift b] PCROSS K` THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN STRIP_TAC THEN
  UNDISCH_TAC `((\n. pastecart (lift((tt:num->real) ((phi:num->num) n))) ((yy:num->real^N) (phi n)))
                --> pastecart (lift t0) (y0:real^N)) sequentially` THEN
  REWRITE_TAC[LIM_PASTECART_EQ] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y0:real^N) IN V` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  USE_THEN "cov" (MP_TAC o C MP (ASSUME `(y0:real^N) IN V`) o SPEC `y0:real^N`) THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!j. j <= (nn:num->num) ((phi:num->num) j)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(phi:num->num) j` THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `phi:num->num` MONOTONE_BIGGER) THEN ASM_SIMP_TAC[];
      USE_THEN "bad" (MP_TAC o SPEC `(phi:num->num) j`) THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `a:real`; `b:real`; `Gs:num->real->real^N->real^N^N`;
                 `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`;
                 `ee:num->real`; `c:num->real^N`; `r:num->real`; `sub:num->num`;
                 `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`; `i:num`;
                 `\j. (tt:num->real) ((phi:num->num) j)`; `t0:real`;
                 `\j. (nn:num->num) ((phi:num->num) j)`; `y0:real^N`] P2CM_CTX_NEAR_SEQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [USE_THEN "ctx" ACCEPT_TAC; ALL_TAC] THEN
    X_GEN_TAC `j:num` THEN USE_THEN "bad" (MP_TAC o SPEC `(phi:num->num) j`) THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP P2CM_LCK_NEAR2 th)) THEN
  DISCH_THEN(MP_TAC o SPEC `m:num`) THEN
  REWRITE_TAC[p2ci_near] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPEC `e:real` o last o CONJUNCTS))) THEN
  ASM_REWRITE_TAC[VECTOR_SUB_RZERO; NORM_LIFT] THEN
  DISCH_THEN(X_CHOOSE_TAC `J1:num`) THEN
  UNDISCH_TAC `((\n. (yy:num->real^N) ((phi:num->num) n)) --> y0) sequentially` THEN
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN DISCH_THEN(MP_TAC o SPEC `rho:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `J2:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`J1 + J2:num`; `(yy:num->real^N) ((phi:num->num) (J1 + J2))`] o
    check (fun th -> can (find_term ((=) `J1:num`)) (concl th) && is_forall(concl th))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LE_ADD; IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "bad" (MP_TAC o SPEC `(phi:num->num) (J1 + J2)`) THEN REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* The local limit theorem.                                                  *)
(* ------------------------------------------------------------------------- *)

let P2CM_COUNTABLE_NUM3 = prove
 (`COUNTABLE(:num#num#num)`,
  REWRITE_TAC[GSYM CROSS_UNIV] THEN
  REPEAT(MATCH_MP_TAC COUNTABLE_CROSS THEN CONJ_TAC) THEN REWRITE_TAC[NUM_COUNTABLE]);;

let P2CM_LOCAL_LIMIT = prove
 (`!V a b (Gs:num->real->real^N->real^N^N).
     open V /\ a < b /\
     (!n t. a <= t /\ t <= b ==> metric_field V (Gs n t)) /\
     (!n. lricci_flow V a b (Gs n)) /\
     (!n. ?e (FF:real^(1,N)finite_sum->real^(N,N)finite_prod).
            &0 < e /\ smooth_map_on (interval(lift(a - e),lift(b + e)) PCROSS V) FF /\
            (!t y. a <= t /\ t <= b /\ y IN V
                   ==> FF(pastecart (lift t) y) = vectorize(Gs n t y))) /\
     (!K. compact K /\ K SUBSET V
          ==> ?Lm. !n t y v. a <= t /\ t <= b /\ y IN K
                             ==> norm v pow 2 <= Lm * (v dot (Gs n t y ** v))) /\
     (!K l p q. compact K /\ K SUBSET V /\
                ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l /\
                1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
                ==> ?B. !n w. w IN interval(lift a,lift b) PCROSS K
                             ==> norm(iterated_partial l
                                        (\w. lift(Gs n (drop(fstcart w)) (sndcart w)$p$q)) w)
                                 <= B)
     ==> ?sub G. (!m n. m < n ==> sub m < sub n) /\
                 lricci_flow V a b G /\
                 (!t. a <= t /\ t <= b ==> metric_field V (G t)) /\
                 (!t y p q. a <= t /\ t <= b /\ y IN V /\
                            1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
                            ==> ((\n. Gs (sub n) t y$p$q) ---> G t y$p$q) sequentially) /\
                 (!K m e. compact K /\ K SUBSET V /\ &0 < e
                          ==> ?N. !n t y. N <= n /\ a <= t /\ t <= b /\ y IN K
                                          ==> lck_dist2 m (G t) (Gs (sub n) t) y < e)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "mf") (CONJUNCTS_THEN2 (LABEL_TAC "lf")
    (CONJUNCTS_THEN2 (MP_TAC o REWRITE_RULE[SKOLEM_THM])
    (CONJUNCTS_THEN2 (LABEL_TAC "eqv") (LABEL_TAC "bd"))))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `ee:num->real` (X_CHOOSE_THEN
    `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod` (LABEL_TAC "ext"))) THEN
  MP_TAC(ISPEC `V:real^N->bool` P2CM_BALL_COVER) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num->real^N` (X_CHOOSE_THEN `r:num->real`
    (CONJUNCTS_THEN2 (LABEL_TAC "cb") (LABEL_TAC "cov")))) THEN
  SUBGOAL_THEN
   `!i n. open (interval(lift(a - (ee:num->real) n),lift(b + ee n)) PCROSS (V:real^N->bool)) /\
          p2cm_box a b (c:num->real^N) r i SUBSET
          interval(lift(a - ee n),lift(b + ee n)) PCROSS V`
  (LABEL_TAC "dom") THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `n:num`] THEN
    USE_THEN "ext" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL];
      REWRITE_TAC[p2cm_box] THEN MATCH_MP_TAC PCROSS_MONO THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN DISJ2_TAC THEN ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n p q. smooth_map_on (interval(lift(a - (ee:num->real) n),lift(b + ee n)) PCROSS
                           (V:real^N->bool))
              (p2cm_ent (FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod) n p q)`
  (LABEL_TAC "smE") THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `p:num`; `q:num`] THEN
    USE_THEN "ext" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    REWRITE_TAC[p2cm_ent] THEN
    SUBGOAL_THEN
     `(\w. lift((matrify((FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod) n w)
                 :real^N^N)$p$q)) =
      (\m:real^(N,N)finite_prod. lift((matrify m:real^N^N)$p$q)) o FF n`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN
    REWRITE_TAC[linear; MATRIFY_ADD; MATRIFY_CMUL; MATRIX_ADD_COMPONENT;
                MATRIX_CMUL_COMPONENT; LIFT_ADD; LIFT_CMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i p q l. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N) /\
              ALL (\j. 1 <= j /\ j <= dimindex(:(1,N)finite_sum)) l
              ==> ?B. !n w. w IN p2cm_box a b (c:num->real^N) r i
                            ==> norm(iterated_partial l
                                       (p2cm_ent (FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod)
                                          n p q) w) <= B`
  (LABEL_TAC "bnd") THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `p:num`; `q:num`; `l:num list`] THEN STRIP_TAC THEN
    USE_THEN "bd" (MP_TAC o SPECL [`cball((c:num->real^N) i,(r:num->real) i)`;
                                   `l:num list`; `p:num`; `q:num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[COMPACT_CBALL]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN EXISTS_TAC `B:real` THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[p2cm_box; p2cm_ent] THEN
    USE_THEN "ext" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    MATCH_MP_TAC P2CM_BOX_BOUND THEN
    MAP_EVERY EXISTS_TAC [`V:real^N->bool`; `(Gs:num->real->real^N->real^N^N) n`;
                          `(ee:num->real) n`] THEN
    ASM_REWRITE_TAC[COMPACT_CBALL; ETA_AX];
    ALL_TAC] THEN
  ABBREV_TAC `ok = \p:num. 1 <= p /\ p <= dimindex(:N)` THEN
  MP_TAC(ISPECL
   [`\(ipq:num#num#num) n. if (ok:num->bool) (FST(SND ipq)) /\ ok (SND(SND ipq))
                           then p2cm_ent (FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod)
                                  n (FST(SND ipq)) (SND(SND ipq))
                           else (\w:real^(1,N)finite_sum. vec 0:real^1)`;
    `\ipq:num#num#num. p2cm_box a b (c:num->real^N) r (FST ipq)`;
    `\(ipq:num#num#num) n. interval(lift(a - (ee:num->real) n),lift(b + ee n)) PCROSS
                           (V:real^N->bool)`] P2CM_BOX_SUBSEQ) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND; P2CM_COUNTABLE_NUM3] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REPEAT GEN_TAC THEN REWRITE_TAC[p2cm_box] THEN
      SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL; COMPACT_CBALL; CONVEX_PCROSS;
               CONVEX_INTERVAL; CONVEX_CBALL];
      MAP_EVERY X_GEN_TAC [`i:num`; `p:num`; `q:num`; `n:num`] THEN
      ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST];
      MAP_EVERY X_GEN_TAC [`i:num`; `p:num`; `q:num`; `l:num list`] THEN DISCH_TAC THEN
      ASM_CASES_TAC `(ok:num->bool) p /\ ok q` THEN ASM_REWRITE_TAC[] THENL
       [USE_THEN "bnd" MATCH_MP_TAC THEN
        UNDISCH_TAC `(ok:num->bool) p /\ ok q` THEN EXPAND_TAC "ok" THEN SIMP_TAC[] THEN
        ASM_REWRITE_TAC[];
        EXISTS_TAC `&0` THEN
        REWRITE_TAC[RFA_ITERATED_PARTIAL_CONST; COND_ID; NORM_0; REAL_LE_REFL]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN
    `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "HH")))) THEN
  SUBGOAL_THEN `p2cm_ctx V a b (Gs:num->real->real^N->real^N^N) FF ee c r sub H`
  (LABEL_TAC "ctx") THENL
   [REWRITE_TAC[p2cm_ctx] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `p:num`; `q:num`; `l:num list`] THEN STRIP_TAC THEN
    USE_THEN "HH" (MP_TAC o C MP (ASSUME
      `ALL (\j. 1 <= j /\ j <= dimindex(:(1,N)finite_sum)) l`) o
      SPECL [`i:num`; `p:num`; `q:num`; `l:num list`]) THEN
    EXPAND_TAC "ok" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`sub:num->num`; `p2cm_lim (Gs:num->real->real^N->real^N^N) sub`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2CM_CTX_FLOW THEN
    MAP_EVERY EXISTS_TAC [`FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`;
                          `ee:num->real`; `c:num->real^N`; `r:num->real`;
                          `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`] THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CM_CTX_METRIC THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`;
                          `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`;
                          `ee:num->real`; `c:num->real^N`; `r:num->real`;
                          `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`] THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN REWRITE_TAC[TENDSTO_REAL; o_DEF] THEN
    MATCH_MP_TAC P2CM_CTX_ENTRY_LIM THEN
    MAP_EVERY EXISTS_TAC [`V:real^N->bool`; `a:real`; `b:real`;
                          `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`;
                          `ee:num->real`; `c:num->real^N`; `r:num->real`;
                          `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`] THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CM_CTX_LCK THEN
    MAP_EVERY EXISTS_TAC [`V:real^N->bool`; `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`;
                          `ee:num->real`; `c:num->real^N`; `r:num->real`;
                          `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`] THEN
    ASM_REWRITE_TAC[]]);;

