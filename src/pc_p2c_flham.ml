(* ========================================================================= *)
(* Unit pc_p2c_flham (Part 2C, flowlim route): Hamilton's lemma uniformly    *)
(* over families of local Ricci flows.  For local flows G n on an open set V *)
(* over [a,b] (a <= 0 <= b) with uniformly bounded metric entries, uniform   *)
(* equivalence to the Euclidean metric, uniform bounds on every |nabla^j     *)
(* Rm|^2 and uniform coordinate jets at time 0, all coordinate jets of all   *)
(* orders are bounded on a compact K uniformly in n and t.  The family is    *)
(* encoded as one time family on disjoint time windows (p2ch_win), so that   *)
(* the calculus of uniformly jet-bounded families rfa_jb of pc_rfa_r1        *)
(* applies verbatim; the time integration and the Christoffel induction of   *)
(* pc_rfa_r1 are generalized to windows and to both time directions from the *)
(* base time 0.                                                              *)
(* ========================================================================= *)

needs "src/pc_rfa_r1.ml";;
needs "src/pc_pde_rdt_symbol.ml";;
needs "src/pc_pde_st.ml";;
needs "src/pc_rfa_slmfd.ml";;  (* RFA_LRICCI_FLOW_EQ *)

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Time integration of jet bounds from base times (the                      *)
(* generalization of RFA_JB_TIME): every t in Js is joined to a base time   *)
(* t0 in Js0 within distance D by a segment on which f has a jointly smooth *)
(* representative and the time derivative f' (bounded on Js1).             *)
(* ------------------------------------------------------------------------- *)

let P2CH_JB_TIME = prove
 (`!Js Js0 Js1 V K m (f:real->real^N->real) f' D.
     open V /\ K SUBSET V /\ &0 <= D /\
     (!t. t IN Js ==> smooth_map_on V (\z. lift(f t z))) /\
     (!t. t IN Js
          ==> ?t0 W (Fx:real^(1,N)finite_sum->real).
                t0 IN Js0 /\ abs(t - t0) <= D /\ open W /\
                smooth_map_on W (\w. lift(Fx w)) /\
                (!s z. min t0 t <= s /\ s <= max t0 t /\ z IN V
                       ==> pastecart (lift s) z IN W /\ Fx(pastecart (lift s) z) = f s z) /\
                (!s y. min t0 t < s /\ s < max t0 t /\ y IN V
                       ==> s IN Js1 /\ ((\r. f r y) has_real_derivative f' s y) (atreal s))) /\
     rfa_jb Js1 V K m f' /\ rfa_jb Js0 V K m f
     ==> rfa_jb Js V K m f`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "loc") (CONJUNCTS_THEN2 MP_TAC MP_TAC)))))) THEN
  REWRITE_TAC[rfa_jb] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sm0") (X_CHOOSE_TAC `C0:real`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_TAC `C1:real`)) THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `C0 + D * abs C1` THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `l:num list`; `y:real^N`] THEN STRIP_TAC THEN
  USE_THEN "loc" (MP_TAC o C MP (ASSUME `(t:real) IN Js`) o SPEC `t:real`) THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real` (X_CHOOSE_THEN `W:real^(1,N)finite_sum->bool`
    (X_CHOOSE_THEN `Fx:real^(1,N)finite_sum->real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "seg") (LABEL_TAC "dr"))))))))) THEN
  SUBGOAL_THEN `(y:real^N) IN V` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= D * abs C1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(rfa_jet l (f:real->real^N->real) t0 y) <= C0` ASSUME_TAC THENL
   [REWRITE_TAC[rfa_jet] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `drop(iterated_partial l (\z. lift((f:real->real^N->real) t z)) y) =
                rfa_jet l f t y` SUBST1_TAC THENL [REWRITE_TAC[rfa_jet]; ALL_TAC] THEN
  ASM_CASES_TAC `t:real = t0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `u = min t0 t` THEN ABBREV_TAC `v = max t0 t` THEN
  SUBGOAL_THEN `u < v /\ v - u <= D /\ ((u = t0 /\ v = t) \/ (u = t /\ v = t0))`
  (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THENL
   [EXPAND_TAC "u" THEN EXPAND_TAC "v" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!s z. u <= s /\ s <= v /\ (z:real^N) IN V ==> pastecart (lift s) z IN W) /\
    (!s z. u <= s /\ s <= v /\ (z:real^N) IN V
           ==> (Fx:real^(1,N)finite_sum->real) (pastecart (lift s) z) = f s z) /\
    (!s. u < s /\ s < v ==> s IN Js1) /\
    (!s z. u < s /\ s < v /\ (z:real^N) IN V
           ==> ((\r. f r z) has_real_derivative f' s z) (atreal s))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "seg" MP_TAC THEN MESON_TAC[];
      USE_THEN "seg" MP_TAC THEN MESON_TAC[];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      USE_THEN "dr" (MP_TAC o SPECL [`s:real`; `y:real^N`]) THEN ASM_SIMP_TAC[];
      USE_THEN "dr" MP_TAC THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (interval(lift u,lift v) PCROSS V)
      (\w. lift((f:real->real^N->real) (drop(fstcart w)) (sndcart w)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `\w:real^(1,N)finite_sum. lift((Fx:real^(1,N)finite_sum->real) w)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1; FORALL_LIFT;
                  LIFT_DROP; FSTCART_PASTECART; SNDCART_PASTECART] THEN
      REPEAT STRIP_TAC THEN AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `W:real^(1,N)finite_sum->bool` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1; FORALL_LIFT;
                  LIFT_DROP] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. u <= s /\ s <= v
        ==> rfa_jet l (f:real->real^N->real) s y =
            rfa_jet l (\s z. (Fx:real^(1,N)finite_sum->real) (pastecart (lift s) z)) s y`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN REWRITE_TAC[rfa_jet] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`l:num list`; `V:real^N->bool`; `\z. lift((f:real->real^N->real) s z)`;
                   `\z:real^N. lift((Fx:real^(1,N)finite_sum->real) (pastecart (lift s) z))`]
           TEXT_ITERATED_PARTIAL_LOCAL_OPEN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN AP_TERM_TAC THEN
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\r. rfa_jet l (f:real->real^N->real) r y`;
                 `\r. rfa_jet l (f':real->real^N->real) r y`; `u:real`; `v:real`]
         REAL_MVT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_EQ THEN
      EXISTS_TAC `\r. rfa_jet l (\s z. (Fx:real^(1,N)finite_sum->real)
                                        (pastecart (lift s) z)) r (y:real^N)` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; IN_REAL_INTERVAL] THEN
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      MATCH_MP_TAC RFA_JET_SLICE_CONTINUOUS THEN
      EXISTS_TAC `W:real^(1,N)finite_sum->bool` THEN
      ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; PASTECART_FST_SND;
                      ETA_AX] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      MATCH_MP_TAC RFA_JET_DT THEN
      MAP_EVERY EXISTS_TAC [`V:real^N->bool`; `u:real`; `v:real`] THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `xi:real` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs(rfa_jet l (f':real->real^N->real) xi y) <= C1` ASSUME_TAC THENL
   [REWRITE_TAC[rfa_jet] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(rfa_jet l (f':real->real^N->real) xi y * (v - u)) <= D * abs C1`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (is_disj o concl)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The Christoffel induction of pc_rfa_r1 for families of                    *)
(* times Js with base times Js0 and flow times Js1: two-sided extensions     *)
(* (RFA_EXT_DET_OPEN for [a,b]), the time derivative of the Christoffel      *)
(* symbols at flow times (RFA_R1_DGAMMA_JB with a local flow around each    *)
(* time), the induction step and the induction.                              *)
(* ------------------------------------------------------------------------- *)

let P2CH_EXT_DET_OPEN = prove
 (`!V a b e (Gc:real->real^N->real^N^N)
    (FF:real^(1,N)finite_sum->real^(N,N)finite_prod).
     open V /\ &0 < e /\
     (!t. a <= t /\ t <= b ==> metric_field V (Gc t)) /\
     smooth_map_on (interval(lift(a - e),lift(b + e)) PCROSS V) FF /\
     (!t y. a <= t /\ t <= b /\ y IN V ==> FF(pastecart (lift t) y) = vectorize(Gc t y))
     ==> ?W. open W /\
             (!t y. a <= t /\ t <= b /\ y IN V ==> pastecart (lift t) y IN W) /\
             smooth_map_on W FF /\
             (!w. w IN W ==> ~(det(matrify(FF w):real^N^N) = &0))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `O = interval(lift(a - e),lift(b + e)) PCROSS (V:real^N->bool)` THEN
  SUBGOAL_THEN `open(O:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL]; ALL_TAC] THEN
  EXISTS_TAC `{w | w IN O /\
                   lift(det(matrify((FF:real^(1,N)finite_sum->real^(N,N)finite_prod) w)
                            :real^N^N)) IN (:real^1) DIFF {vec 0}}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_SIMP_TAC[OPEN_DIFF; OPEN_UNIV; CLOSED_SING] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_DET THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `(\w. lift(matrify((FF:real^(1,N)finite_sum->real^(N,N)finite_prod) w)
                :real^N^N$i$j)) =
      (\m:real^(N,N)finite_prod. lift(basis i dot ((matrify m:real^N^N) ** basis j))) o FF`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC RFB_BASIS_DOT_MATRIX THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; LINEAR_CONTINUOUS_ON;
                 LRG_LINEAR_MATRIFY_DOT];
    REPEAT STRIP_TAC THEN REWRITE_TAC[IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_SING] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "O" THEN REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[MATRIFY_VECTORIZE; LIFT_EQ; GSYM LIFT_NUM] THEN
      MP_TAC(ISPECL [`V:real^N->bool`; `(Gc:real->real^N->real^N^N) t`; `y:real^N`]
             LRG_METRIC_INVERTIBLE) THEN
      ASM_SIMP_TAC[]];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `O:real^(1,N)finite_sum->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    REWRITE_TAC[IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_SING; GSYM LIFT_NUM; LIFT_EQ] THEN
    SIMP_TAC[]]);;

(* The time derivative of the Christoffel symbols at times with a local flow. *)

let P2CH_DGAMMA_JB = prove
 (`!m Js1 V K (Gc:real->real^N->real^N^N).
     open V /\ K SUBSET V /\
     (!t. t IN Js1 ==> ?a b. a < t /\ t < b /\ lricci_flow V a b Gc) /\
     (!t. t IN Js1 ==> metric_field V (Gc t)) /\
     (!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
            ==> rfa_jb Js1 V K m (\t z. matrix_inv(Gc t z)$p$q)) /\
     (!al. al IN index_tuples 5 (:N)
           ==> rfa_jb Js1 V K m
                 (\t z. lnabla 4 (Gc t) (lrm4 (Gc t)) z (\r. basis(al r))))
     ==> !i j s. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
                 1 <= s /\ s <= dimindex(:N)
                 ==> rfa_jb Js1 V K m
                       (\t z. (ldgamma Gc t z (basis i) (basis j))$s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "lf") (CONJUNCTS_THEN2 (LABEL_TAC "mf")
    (CONJUNCTS_THEN2 (LABEL_TAC "gi") (LABEL_TAC "r5")))))) THEN
  SUBGOAL_THEN
   `!x1 x2 x3. 1 <= x1 /\ x1 <= dimindex(:N) /\ 1 <= x2 /\ x2 <= dimindex(:N) /\
               1 <= x3 /\ x3 <= dimindex(:N)
               ==> rfa_jb Js1 V K m
                     (\t y. lnabla 2 ((Gc:real->real^N->real^N^N) t) (lric2 (Gc t)) y
                              (\r. basis(rfa_tup3 x1 x2 x3 r)))`
  (LABEL_TAC "n3") THENL
   [MATCH_MP_TAC RFA_R1_N3_JB THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN USE_THEN "mf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_JB_EQ THEN
  EXISTS_TAC
   `\t y. --(sum(1..dimindex(:N)) (\k. matrix_inv((Gc:real->real^N->real^N^N) t y)$s$k *
             (lnabla 2 (Gc t) (lric2 (Gc t)) y (\r. basis(rfa_tup3 j k i r)) +
              lnabla 2 (Gc t) (lric2 (Gc t)) y (\r. basis(rfa_tup3 i k j r)) -
              lnabla 2 (Gc t) (lric2 (Gc t)) y (\r. basis(rfa_tup3 i j k r)))))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
    USE_THEN "lf" (MP_TAC o C MP (ASSUME `(t:real) IN Js1`) o SPEC `t:real`) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real` (X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC)) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC RFA_LDGAMMA_N3 THEN
    MAP_EVERY EXISTS_TAC [`V:real^N->bool`; `a:real`; `b:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC RFA_JB_NEG THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC RFA_JB_SUM THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC RFA_JB_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [USE_THEN "gi" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC RFA_JB_ADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC RFA_JB_SUB THEN ASM_REWRITE_TAC[] THEN CONJ_TAC] THEN
  USE_THEN "n3" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* The induction step on the order of the Christoffel jets. *)

let P2CH_GAMMA_STEP = prove
 (`!m Js Js0 Js1 V K (Gc:real->real^N->real^N^N) Lm D.
     open V /\ compact K /\ K SUBSET V /\ &0 <= Lm /\ &0 <= D /\
     Js0 SUBSET Js /\ Js1 SUBSET Js /\
     (!t. t IN Js ==> metric_field V (Gc t)) /\
     (!t y p. t IN Js /\ y IN K /\ 1 <= p /\ p <= dimindex(:N) ==> Gc t y$p$p <= Lm) /\
     (!t y v. t IN Js /\ y IN K ==> norm v pow 2 <= Lm * (v dot (Gc t y ** v))) /\
     (!j. ?C. !t y. t IN Js /\ y IN K ==> lrm_deriv_norm2 j (Gc t) y <= C) /\
     (!t. t IN Js
          ==> ?t0 a b e (FF:real^(1,N)finite_sum->real^(N,N)finite_prod).
                t0 IN Js0 /\ abs(t - t0) <= D /\ a <= min t0 t /\ max t0 t <= b /\
                &0 < e /\ lricci_flow V a b Gc /\
                (!s. a <= s /\ s <= b ==> metric_field V (Gc s)) /\
                smooth_map_on (interval(lift(a - e),lift(b + e)) PCROSS V) FF /\
                (!s y. a <= s /\ s <= b /\ y IN V
                       ==> FF(pastecart (lift s) y) = vectorize(Gc s y)) /\
                (!s. min t0 t < s /\ s < max t0 t ==> s IN Js1)) /\
     (!t. t IN Js1 ==> ?a b. a < t /\ t < b /\ lricci_flow V a b Gc) /\
     (!i j s. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
              1 <= s /\ s <= dimindex(:N)
              ==> rfa_jb Js0 V K m (\t z. (christoffel (Gc t) z (basis i) (basis j))$s)) /\
     (1 <= m
      ==> !i j s. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
                  1 <= s /\ s <= dimindex(:N)
                  ==> rfa_jb Js V K (m - 1)
                        (\t z. (christoffel (Gc t) z (basis i) (basis j))$s))
     ==> !i j s. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
                 1 <= s /\ s <= dimindex(:N)
                 ==> rfa_jb Js V K m (\t z. (christoffel (Gc t) z (basis i) (basis j))$s)`,
  INTRO_TAC "!m Js Js0 Js1 V K Gc Lm D; oV cK KV L0 D0 J0 J1 mf diag pos rmb loc lf ini ih" THEN
  SUBGOAL_THEN
   `!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
          ==> rfa_jb Js V K 0 (\t z. matrix_inv((Gc:real->real^N->real^N^N) t z)$p$q)`
  (LABEL_TAC "gi00") THENL
   [MATCH_MP_TAC RFA_R1_GINV0 THEN EXISTS_TAC `Lm:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
          ==> rfa_jb Js V K m (\t z. matrix_inv((Gc:real->real^N->real^N^N) t z)$p$q)`
  (LABEL_TAC "gi") THENL
   [ASM_CASES_TAC `m = 0` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`m - 1`; `Js:real->bool`; `V:real^N->bool`; `K:real^N->bool`;
                   `Gc:real->real^N->real^N^N`] RFA_JB_GINV) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "ih" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!al. al IN index_tuples 5 (:N)
         ==> rfa_jb Js V K m
               (\t z. lnabla 4 ((Gc:real->real^N->real^N^N) t) (lrm4 (Gc t)) z
                        (\r. basis(al r)))`
  (LABEL_TAC "r5") THENL
   [MATCH_MP_TAC RFA_R5_JB THEN EXISTS_TAC `Lm:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j s. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
            1 <= s /\ s <= dimindex(:N)
            ==> rfa_jb Js1 V K m
                  (\t z. (ldgamma (Gc:real->real^N->real^N^N) t z (basis i) (basis j))$s)`
  (LABEL_TAC "dg") THENL
   [MATCH_MP_TAC P2CH_DGAMMA_JB THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_JB_TSUBSET THEN EXISTS_TAC `Js:real->bool` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "gi" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_JB_TSUBSET THEN EXISTS_TAC `Js:real->bool` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "r5" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`; `s:num`] THEN STRIP_TAC THEN
  MATCH_MP_TAC P2CH_JB_TIME THEN
  MAP_EVERY EXISTS_TAC
   [`Js0:real->bool`; `Js1:real->bool`;
    `\t z. (ldgamma (Gc:real->real^N->real^N^N) t z (basis i) (basis j))$s`; `D:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LRG_CHRISTOFFEL_SMOOTH THEN ASM_SIMP_TAC[];
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    USE_THEN "loc" (MP_TAC o C MP (ASSUME `(t:real) IN Js`) o SPEC `t:real`) THEN
    DISCH_THEN(X_CHOOSE_THEN `t0:real` (X_CHOOSE_THEN `a:real` (X_CHOOSE_THEN `b:real`
      (X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `FF:real^(1,N)finite_sum->real^(N,N)finite_prod`
       STRIP_ASSUME_TAC))))) THEN
    MP_TAC(ISPECL [`V:real^N->bool`; `a:real`; `b:real`; `e:real`;
                   `Gc:real->real^N->real^N^N`;
                   `FF:real^(1,N)finite_sum->real^(N,N)finite_prod`] P2CH_EXT_DET_OPEN) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `W:real^(1,N)finite_sum->bool` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC
     [`t0:real`; `W:real^(1,N)finite_sum->bool`;
      `\w. (christoffel (\z. matrify((FF:real^(1,N)finite_sum->real^(N,N)finite_prod)
                                       (pastecart (fstcart w) z)):real^N^N)
                         (sndcart w) (basis i) (basis j))$s`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`W:real^(1,N)finite_sum->bool`;
                     `FF:real^(1,N)finite_sum->real^(N,N)finite_prod`;
                     `basis i:real^N`; `basis j:real^N`]
                    RFA_W_CHRISTOFFEL_SMOOTH) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`r:real`; `z:real^N`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `a <= r /\ r <= b` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC CHRISTOFFEL_LOCAL THEN EXISTS_TAC `V:real^N->bool` THEN
      ASM_SIMP_TAC[MATRIFY_VECTORIZE];
      MAP_EVERY X_GEN_TAC [`r:real`; `y:real^N`] THEN STRIP_TAC THEN
      CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`V:real^N->bool`; `a:real`; `b:real`; `Gc:real->real^N->real^N^N`;
                     `r:real`; `y:real^N`; `basis i:real^N`; `basis j:real^N`]
             LRG_FLOW_GAMMA_VDERIV) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[GSYM ldgamma] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`\r. christoffel ((Gc:real->real^N->real^N^N) r) y (basis i) (basis j)`;
                     `ldgamma (Gc:real->real^N->real^N^N) r y (basis i) (basis j)`;
                     `r:real`; `s:num`] LRG_VDERIV_COMPONENT_REAL) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    USE_THEN "dg" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "ini" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let P2CH_GAMMA = prove
 (`!Js Js0 Js1 V K (Gc:real->real^N->real^N^N) Lm D.
     open V /\ compact K /\ K SUBSET V /\ &0 <= Lm /\ &0 <= D /\
     Js0 SUBSET Js /\ Js1 SUBSET Js /\
     (!t. t IN Js ==> metric_field V (Gc t)) /\
     (!t y p. t IN Js /\ y IN K /\ 1 <= p /\ p <= dimindex(:N) ==> Gc t y$p$p <= Lm) /\
     (!t y v. t IN Js /\ y IN K ==> norm v pow 2 <= Lm * (v dot (Gc t y ** v))) /\
     (!j. ?C. !t y. t IN Js /\ y IN K ==> lrm_deriv_norm2 j (Gc t) y <= C) /\
     (!t. t IN Js
          ==> ?t0 a b e (FF:real^(1,N)finite_sum->real^(N,N)finite_prod).
                t0 IN Js0 /\ abs(t - t0) <= D /\ a <= min t0 t /\ max t0 t <= b /\
                &0 < e /\ lricci_flow V a b Gc /\
                (!s. a <= s /\ s <= b ==> metric_field V (Gc s)) /\
                smooth_map_on (interval(lift(a - e),lift(b + e)) PCROSS V) FF /\
                (!s y. a <= s /\ s <= b /\ y IN V
                       ==> FF(pastecart (lift s) y) = vectorize(Gc s y)) /\
                (!s. min t0 t < s /\ s < max t0 t ==> s IN Js1)) /\
     (!t. t IN Js1 ==> ?a b. a < t /\ t < b /\ lricci_flow V a b Gc) /\
     (!m i j s. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
                1 <= s /\ s <= dimindex(:N)
                ==> rfa_jb Js0 V K m (\t z. (christoffel (Gc t) z (basis i) (basis j))$s))
     ==> !m i j s. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
                   1 <= s /\ s <= dimindex(:N)
                   ==> rfa_jb Js V K m
                         (\t z. (christoffel (Gc t) z (basis i) (basis j))$s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN
  MATCH_MP_TAC P2CH_GAMMA_STEP THEN
  MAP_EVERY EXISTS_TAC [`Js0:real->bool`; `Js1:real->bool`; `Lm:real`; `D:real`] THEN
  ASM_SIMP_TAC[ARITH; SUC_SUB1]);;

(* ------------------------------------------------------------------------- *)
(* Jets of the Christoffel symbols from jets of the metric                   *)
(* (PDE_CHR_JET, PDE_JG_PARTIAL), and the generalized local Hamilton lemma:  *)
(* metric jets of every order on Js from those on the base times Js0.        *)
(* ------------------------------------------------------------------------- *)

let P2CH_CHRIST_JB = prove
 (`!Js V K (G:real->real^N->real^N^N) Lm.
     open V /\ K SUBSET V /\ &0 <= Lm /\ (!t. t IN Js ==> metric_field V (G t)) /\
     (!t y v. t IN Js /\ y IN K ==> norm v pow 2 <= Lm * (v dot (G t y ** v))) /\
     (!m p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
              ==> rfa_jb Js V K m (\t z. G t z$p$q))
     ==> !m i j s. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
                   1 <= s /\ s <= dimindex(:N)
                   ==> rfa_jb Js V K m (\t z. (christoffel (G t) z (basis i) (basis j))$s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!m c p q. 1 <= c /\ c <= dimindex(:N) /\ 1 <= p /\ p <= dimindex(:N) /\
              1 <= q /\ q <= dimindex(:N)
              ==> rfa_jb Js V K m (\t z. (mderiv ((G:real->real^N->real^N^N) t) z
                                                 (basis c))$p$q)`
  (LABEL_TAC "d1") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_JB_EQ THEN
    EXISTS_TAC `rfa_pd c (\t z. (G:real->real^N->real^N^N) t z$p$q)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN STRIP_TAC THEN
      REWRITE_TAC[rfa_pd] THEN
      MP_TAC(ISPECL [`V:real^N->bool`; `(G:real->real^N->real^N^N) t`; `z:real^N`;
                     `c:num`; `p:num`; `q:num`] PDE_JG_PARTIAL) THEN
      ASM_SIMP_TAC[pde_jd1; LIFT_DROP];
      MP_TAC(ISPECL [`Js:real->bool`; `V:real^N->bool`; `K:real^N->bool`; `m:num`;
                     `\t z. (G:real->real^N->real^N^N) t z$p$q`] RFA_JB_SUC) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `c:num` o CONJUNCT2) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. (!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
               ==> rfa_jb Js V K m (\t z. matrix_inv((G:real->real^N->real^N^N) t z)$p$q))
        ==> !i j s. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
                    1 <= s /\ s <= dimindex(:N)
                    ==> rfa_jb Js V K m
                          (\t z. (christoffel (G t) z (basis i) (basis j))$s)`
  (LABEL_TAC "step") THENL
   [GEN_TAC THEN DISCH_TAC THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_JB_EQ THEN
    EXISTS_TAC
     `\t z. sum(1..dimindex(:N))
              (\k. matrix_inv((G:real->real^N->real^N^N) t z)$s$k * inv(&2) *
                   ((mderiv (G t) z (basis i))$k$j + (mderiv (G t) z (basis j))$k$i -
                    (mderiv (G t) z (basis k))$i$j))` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[PDE_CHR_JET; pde_jchr; pde_jgi; pde_jd1];
      ALL_TAC] THEN
    MATCH_MP_TAC RFA_JB_SUM THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC RFA_JB_MUL THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC RFA_JB_CMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RFA_JB_ADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "d1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFA_JB_SUB THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
      USE_THEN "d1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
            ==> rfa_jb Js V K m (\t z. matrix_inv((G:real->real^N->real^N^N) t z)$p$q)`
  ASSUME_TAC THENL
   [INDUCT_TAC THENL
     [MATCH_MP_TAC RFA_R1_GINV0 THEN EXISTS_TAC `Lm:real` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`m:num`; `Js:real->bool`; `V:real^N->bool`; `K:real^N->bool`;
                   `G:real->real^N->real^N^N`] RFA_JB_GINV) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC RFA_R1_GINV0 THEN EXISTS_TAC `Lm:real` THEN ASM_REWRITE_TAC[];
        USE_THEN "step" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      DISCH_THEN(MP_TAC o SPECL [`SUC m`; `p:num`; `q:num`]) THEN
      ASM_REWRITE_TAC[ARITH_RULE `SUC m <= m + 1`]];
    ALL_TAC] THEN
  GEN_TAC THEN USE_THEN "step" MATCH_MP_TAC THEN ASM_SIMP_TAC[]);;

(* The local Hamilton lemma on generalized time sets. *)

let P2CH_LOCAL = prove
 (`!Js Js0 Js1 V K (Gc:real->real^N->real^N^N) Lm D.
     open V /\ compact K /\ K SUBSET V /\ &0 <= Lm /\ &0 <= D /\
     Js0 SUBSET Js /\ Js1 SUBSET Js /\
     (!t. t IN Js ==> metric_field V (Gc t)) /\
     (!t y p q. t IN Js /\ y IN K /\ 1 <= p /\ p <= dimindex(:N) /\
                1 <= q /\ q <= dimindex(:N) ==> abs(Gc t y$p$q) <= Lm) /\
     (!t y v. t IN Js /\ y IN K ==> norm v pow 2 <= Lm * (v dot (Gc t y ** v))) /\
     (!j. ?C. !t y. t IN Js /\ y IN K ==> lrm_deriv_norm2 j (Gc t) y <= C) /\
     (!t. t IN Js
          ==> ?t0 a b e (FF:real^(1,N)finite_sum->real^(N,N)finite_prod).
                t0 IN Js0 /\ abs(t - t0) <= D /\ a <= min t0 t /\ max t0 t <= b /\
                &0 < e /\ lricci_flow V a b Gc /\
                (!s. a <= s /\ s <= b ==> metric_field V (Gc s)) /\
                smooth_map_on (interval(lift(a - e),lift(b + e)) PCROSS V) FF /\
                (!s y. a <= s /\ s <= b /\ y IN V
                       ==> FF(pastecart (lift s) y) = vectorize(Gc s y)) /\
                (!s. min t0 t < s /\ s < max t0 t ==> s IN Js1)) /\
     (!t. t IN Js1 ==> ?a b. a < t /\ t < b /\ lricci_flow V a b Gc) /\
     (!m p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
              ==> rfa_jb Js0 V K m (\t z. Gc t z$p$q))
     ==> !m p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
                 ==> rfa_jb Js V K m (\t z. Gc t z$p$q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!m i j s. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
              1 <= s /\ s <= dimindex(:N)
              ==> rfa_jb Js V K m
                    (\t z. (christoffel ((Gc:real->real^N->real^N^N) t) z
                                        (basis i) (basis j))$s)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2CH_GAMMA THEN
    MAP_EVERY EXISTS_TAC [`Js0:real->bool`; `Js1:real->bool`; `Lm:real`; `D:real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `abs x <= l ==> x <= l`) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2CH_CHRIST_JB THEN EXISTS_TAC `Lm:real` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  GEN_TAC THEN MATCH_MP_TAC RFA_R1_METRIC_JB THEN EXISTS_TAC `Lm:real` THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Time windows and the uniform Hamilton lemma.  A sequence                 *)
(* of families Gs n over [a,b] (a <= 0 <= b) is the time family             *)
(* p2ch_win Gs L on the windows t + n L (t in [a,b]), L = 2 (|a| + |b| + 1); *)
(* the window of tt is the n with abs(tt - n L) < L / 2.                     *)
(* ------------------------------------------------------------------------- *)

let p2ch_idx = new_definition
 `p2ch_idx L tt = @n:num. abs(tt - &n * L) < L / &2`;;

let p2ch_win = new_definition
 `p2ch_win (Gs:num->real->real^N->real^N^N) L tt =
    Gs (p2ch_idx L tt) (tt - &(p2ch_idx L tt) * L)`;;

let P2CH_IDX = prove
 (`!L t n. &0 < L /\ abs t < L / &2 ==> p2ch_idx L (t + &n * L) = n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2ch_idx] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC `k:num` THEN REWRITE_TAC[] THEN EQ_TAC THENL
   [ALL_TAC;
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[REAL_ARITH `(x + y) - y:real = x`]] THEN
  DISCH_TAC THEN MATCH_MP_TAC(ARITH_RULE `~(k < n) /\ ~(n < k) ==> k = n:num`) THEN
  CONJ_TAC THEN DISCH_TAC THENL
   [SUBGOAL_THEN `&1 <= &n - &k` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LE_SUB_LADD; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `L <= (&n - &k) * L` MP_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      UNDISCH_TAC `abs((t + &n * L) - &k * L) < L / &2` THEN
      UNDISCH_TAC `abs t < L / &2` THEN REAL_ARITH_TAC];
    SUBGOAL_THEN `&1 <= &k - &n` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LE_SUB_LADD; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `L <= (&k - &n) * L` MP_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      UNDISCH_TAC `abs((t + &n * L) - &k * L) < L / &2` THEN
      UNDISCH_TAC `abs t < L / &2` THEN REAL_ARITH_TAC]]);;

let P2CH_WIN = prove
 (`!(Gs:num->real->real^N->real^N^N) L t n.
     &0 < L /\ abs t < L / &2 ==> p2ch_win Gs L (t + &n * L) = Gs n t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2ch_win] THEN
  ASM_SIMP_TAC[P2CH_IDX] THEN REWRITE_TAC[REAL_ARITH `(x + y) - y:real = x`]);;

(* Time translation of local Ricci flows. *)

let P2CH_LRICCI_FLOW_SHIFT = prove
 (`!U a b (G:real->real^N->real^N^N) c.
     lricci_flow U a b G ==> lricci_flow U (a + c) (b + c) (\t. G (t - c))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lricci_flow] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[REAL_LT_RADD] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL
     [`\z:real^(1,N)finite_sum.
         (vectorize:real^N^N->real^(N,N)finite_prod)
         ((G:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z))`;
      `U:real^N->bool`; `a:real`; `b:real`; `a + c:real`; `b + c:real`; `&1`; `--c:real`]
     RFB_SMOOTH_TIME_AFFINE) THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP;
                REAL_MUL_LID; GSYM real_sub] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`; `i:num`; `j:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`t - c:real`; `y:real^N`; `i:num`; `j:num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`\u:real. u - c`; `\u:real. (G:real->real^N->real^N^N) u y$i$j`;
                   `&1 - &0`;
                   `--(&2) * lricci ((G:real->real^N->real^N^N) (t - c)) y
                                    (basis i) (basis j)`;
                   `t:real`] REAL_DIFF_CHAIN_ATREAL) THEN
    ASM_REWRITE_TAC[o_DEF] THEN ANTS_TAC THENL
     [REWRITE_TAC[REAL_DIFF_CONV `((\u. u - c) has_real_derivative f') (atreal t)`];
      REWRITE_TAC[REAL_SUB_RZERO; REAL_MUL_RID]]]);;

(* The uniform Hamilton lemma. *)

let P2CH_UNIFORM = prove
 (`!V K a b (Gs:num->real->real^N->real^N^N) Lm.
     open V /\ compact K /\ K SUBSET V /\ a <= &0 /\ &0 <= b /\ a < b /\ &0 <= Lm /\
     (!n. lricci_flow V a b (Gs n)) /\
     (!n t. a <= t /\ t <= b ==> metric_field V (Gs n t)) /\
     (!n. ?e (FF:real^(1,N)finite_sum->real^(N,N)finite_prod).
            &0 < e /\ smooth_map_on (interval(lift(a - e),lift(b + e)) PCROSS V) FF /\
            (!t y. a <= t /\ t <= b /\ y IN V
                   ==> FF(pastecart (lift t) y) = vectorize(Gs n t y))) /\
     (!n t y p q. a <= t /\ t <= b /\ y IN K /\ 1 <= p /\ p <= dimindex(:N) /\
                  1 <= q /\ q <= dimindex(:N) ==> abs(Gs n t y$p$q) <= Lm) /\
     (!n t y v. a <= t /\ t <= b /\ y IN K
                ==> norm v pow 2 <= Lm * (v dot (Gs n t y ** v))) /\
     (!j. ?C. !n t y. a <= t /\ t <= b /\ y IN K ==> lrm_deriv_norm2 j (Gs n t) y <= C) /\
     (!m p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
              ==> ?B. !n l y. l IN pde_index_lists m (:N) /\ y IN K
                              ==> abs(drop(iterated_partial l (\z. lift(Gs n (&0) z$p$q)) y))
                                  <= B)
     ==> !m p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
                 ==> ?B. !n t l y. a <= t /\ t <= b /\ l IN pde_index_lists m (:N) /\ y IN K
                                   ==> abs(drop(iterated_partial l
                                                 (\z. lift(Gs n t z$p$q)) y)) <= B`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "lf")
    (CONJUNCTS_THEN2 (LABEL_TAC "mf") (CONJUNCTS_THEN2 (LABEL_TAC "ext")
    (CONJUNCTS_THEN2 (LABEL_TAC "ent") (CONJUNCTS_THEN2 (LABEL_TAC "eqv")
    (CONJUNCTS_THEN2 (LABEL_TAC "rmd") (LABEL_TAC "ini")))))))))))))) THEN
  ABBREV_TAC `L = &2 * (abs a + abs b + &1)` THEN
  SUBGOAL_THEN `&0 < L /\ !t. a <= t /\ t <= b ==> abs t < L / &2 /\ abs t <= abs a + abs b`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Gc = p2ch_win (Gs:num->real->real^N->real^N^N) L` THEN
  SUBGOAL_THEN `!n t. a <= t /\ t <= b ==> (Gc:real->real^N->real^N^N) (t + &n * L) = Gs n t`
  (LABEL_TAC "win") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "Gc" THEN MATCH_MP_TAC P2CH_WIN THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`{t + &n * L | n,t | a <= t /\ t <= b}`; `{&n * L | n IN (:num)}`;
    `{t + &n * L | n,t | a < t /\ t < b}`; `V:real^N->bool`; `K:real^N->bool`;
    `Gc:real->real^N->real^N^N`; `Lm:real`; `abs a + abs b`] P2CH_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [(* 5 *) REAL_ARITH_TAC;
      (* 6 *) REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_UNIV; IN_ELIM_THM] THEN
      X_GEN_TAC `n:num` THEN MAP_EVERY EXISTS_TAC [`n:num`; `&0`] THEN
      ASM_REWRITE_TAC[REAL_ADD_LID];
      (* 7 *) REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `t:real`] THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [`n:num`; `t:real`] THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      (* 8 *) REWRITE_TAC[FORALL_IN_GSPEC] THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `t:real`] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
      (* 9 *) REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `t:real`] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
      (* 10 *) REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `t:real`] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
      (* 11 *) X_GEN_TAC `j:num` THEN
      USE_THEN "rmd" (X_CHOOSE_TAC `C:real` o SPEC `j:num`) THEN
      EXISTS_TAC `C:real` THEN
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `t:real`] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
      (* 12 *) REWRITE_TAC[FORALL_IN_GSPEC] THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `t:real`] THEN STRIP_TAC THEN
      USE_THEN "ext" (X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN
        `FF:real^(1,N)finite_sum->real^(N,N)finite_prod` STRIP_ASSUME_TAC) o SPEC `n:num`) THEN
      MAP_EVERY EXISTS_TAC
       [`&n * L`; `a + &n * L`; `b + &n * L`; `e:real`;
        `\w:real^(1,N)finite_sum. (FF:real^(1,N)finite_sum->real^(N,N)finite_prod)
                                  (pastecart (lift(&1 * drop(fstcart w) + --(&n * L)))
                                             (sndcart w))`] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN EXISTS_TAC `n:num` THEN REWRITE_TAC[];
        REWRITE_TAC[REAL_ARITH `(t + n) - n:real = t`] THEN ASM_SIMP_TAC[];
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC RFA_LRICCI_FLOW_EQ THEN
        EXISTS_TAC `\s. (Gs:num->real->real^N->real^N^N) n (s - &n * L)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC P2CH_LRICCI_FLOW_SHIFT THEN ASM_REWRITE_TAC[ETA_AX];
          MAP_EVERY X_GEN_TAC [`s:real`; `y:real^N`] THEN STRIP_TAC THEN
          REWRITE_TAC[] THEN
          USE_THEN "win" (MP_TAC o SPECL [`n:num`; `s - &n * L`]) THEN
          ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          REWRITE_TAC[REAL_SUB_ADD] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]];
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN
        USE_THEN "win" (MP_TAC o SPECL [`n:num`; `s - &n * L`]) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[REAL_SUB_ADD] THEN DISCH_THEN SUBST1_TAC THEN
        USE_THEN "mf" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        MP_TAC(ISPECL [`FF:real^(1,N)finite_sum->real^(N,N)finite_prod`; `V:real^N->bool`;
                       `a - e:real`; `b + e:real`;
                       `(a + &n * L) - e:real`; `(b + &n * L) + e:real`; `&1`;
                       `--(&n * L):real`] RFB_SMOOTH_TIME_AFFINE) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; SIMP_TAC[]];
        MAP_EVERY X_GEN_TAC [`s:real`; `y:real^N`] THEN STRIP_TAC THEN
        REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
        REWRITE_TAC[REAL_MUL_LID; GSYM real_sub] THEN
        USE_THEN "win" (MP_TAC o SPECL [`n:num`; `s - &n * L`]) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[REAL_SUB_ADD] THEN DISCH_THEN SUBST1_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
        MAP_EVERY EXISTS_TAC [`n:num`; `s - &n * L`] THEN
        REWRITE_TAC[REAL_SUB_ADD] THEN ASM_REAL_ARITH_TAC];
      (* 13 *) REWRITE_TAC[FORALL_IN_GSPEC] THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `t:real`] THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [`a + &n * L`; `b + &n * L`] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC RFA_LRICCI_FLOW_EQ THEN
      EXISTS_TAC `\s. (Gs:num->real->real^N->real^N^N) n (s - &n * L)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC P2CH_LRICCI_FLOW_SHIFT THEN ASM_REWRITE_TAC[ETA_AX];
        MAP_EVERY X_GEN_TAC [`s:real`; `y:real^N`] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
        USE_THEN "win" (MP_TAC o SPECL [`n:num`; `s - &n * L`]) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[REAL_SUB_ADD] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]];
      (* 14 *) MAP_EVERY X_GEN_TAC [`m:num`; `p:num`; `q:num`] THEN STRIP_TAC THEN
      REWRITE_TAC[rfa_jb; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC; IN_UNIV] THEN
      SUBGOAL_THEN `!n. (Gc:real->real^N->real^N^N) (&n * L) = Gs n (&0)` ASSUME_TAC THENL
       [GEN_TAC THEN USE_THEN "win" (MP_TAC o SPECL [`n:num`; `&0`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[REAL_ADD_LID]];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [GEN_TAC THEN MATCH_MP_TAC PDE_SMOOTH_G_ENTRY THEN REWRITE_TAC[ETA_AX] THEN
        USE_THEN "mf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL];
        USE_THEN "ini" (MP_TAC o SPECL [`m:num`; `p:num`; `q:num`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> MAP_EVERY X_GEN_TAC [`m:num`; `p:num`; `q:num`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`m:num`; `p:num`; `q:num`] th)) THEN
  ASM_REWRITE_TAC[rfa_jb; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
  DISCH_THEN(K ALL_TAC) THEN DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN EXISTS_TAC `B:real` THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `t:real`] THEN REPEAT DISCH_TAC THEN
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  USE_THEN "win" (MP_TAC o SPECL [`n:num`; `t:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `t:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> ASM_SIMP_TAC[th]));;

(* ------------------------------------------------------------------------- *)
(* Jet polynomials.  Expressions built from the metric entries               *)
(* (PHE_G p q), the inverse metric entries (PHE_I p q), constants, sums,    *)
(* products and space partials (PHE_D i), evaluated on a time family of      *)
(* metrics G.  The evaluation at time t only reads G t (P2CH_EVAL_SLICE),   *)
(* and jet bounds of the entries and inverse entries give jet bounds of      *)
(* every expression (P2CH_EVAL_JB).                                          *)
(* ------------------------------------------------------------------------- *)

let p2ch_expr_INDUCT,p2ch_expr_RECURSION = define_type
 "p2ch_expr = PHE_G num num | PHE_I num num | PHE_C real |
              PHE_ADD p2ch_expr p2ch_expr | PHE_MUL p2ch_expr p2ch_expr |
              PHE_D num p2ch_expr";;

let p2ch_eval = new_recursive_definition p2ch_expr_RECURSION
 `(p2ch_eval (G:real->real^N->real^N^N) (PHE_G p q) = \t z. G t z$p$q) /\
  (p2ch_eval G (PHE_I p q) = \t z. matrix_inv(G t z)$p$q) /\
  (p2ch_eval G (PHE_C c) = \t z. c) /\
  (p2ch_eval G (PHE_ADD e1 e2) = \t z. p2ch_eval G e1 t z + p2ch_eval G e2 t z) /\
  (p2ch_eval G (PHE_MUL e1 e2) = \t z. p2ch_eval G e1 t z * p2ch_eval G e2 t z) /\
  (p2ch_eval G (PHE_D i e) = rfa_pd i (p2ch_eval G e))`;;

let p2ch_ok = new_recursive_definition p2ch_expr_RECURSION
 `(p2ch_ok n (PHE_G p q) <=> 1 <= p /\ p <= n /\ 1 <= q /\ q <= n) /\
  (p2ch_ok n (PHE_I p q) <=> 1 <= p /\ p <= n /\ 1 <= q /\ q <= n) /\
  (p2ch_ok n (PHE_C c) <=> T) /\
  (p2ch_ok n (PHE_ADD e1 e2) <=> p2ch_ok n e1 /\ p2ch_ok n e2) /\
  (p2ch_ok n (PHE_MUL e1 e2) <=> p2ch_ok n e1 /\ p2ch_ok n e2) /\
  (p2ch_ok n (PHE_D i e) <=> 1 <= i /\ i <= n /\ p2ch_ok n e)`;;

let p2ch_sumn = new_recursive_definition num_RECURSION
 `(p2ch_sumn 0 (f:num->p2ch_expr) = PHE_C(&0)) /\
  (p2ch_sumn (SUC n) f = PHE_ADD (p2ch_sumn n f) (f (SUC n)))`;;

let P2CH_EVAL_SUMN = prove
 (`!(G:real->real^N->real^N^N) f n t z.
     p2ch_eval G (p2ch_sumn n f) t z = sum(1..n) (\k. p2ch_eval G (f k) t z)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[p2ch_sumn; p2ch_eval; SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
  REWRITE_TAC[ARITH_RULE `~(1 = 0)`]);;

let P2CH_OK_SUMN = prove
 (`!m f n. (!k. 1 <= k /\ k <= n ==> p2ch_ok m (f k)) ==> p2ch_ok m (p2ch_sumn n f)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[p2ch_sumn; p2ch_ok] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC]);;

(* The value at time t only depends on the slice G t. *)

let P2CH_EVAL_SLICE = prove
 (`!(G:real->real^N->real^N^N) G' t t'.
     G t = G' t' ==> !e. p2ch_eval G e t = p2ch_eval G' e t'`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC p2ch_expr_INDUCT THEN
  REWRITE_TAC[p2ch_eval; rfa_pd; FUN_EQ_THM] THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM FUN_EQ_THM] THEN FIRST_X_ASSUM(SUBST1_TAC o check (is_eq o concl)) THEN
  REWRITE_TAC[]);;

(* Jet bounds of every expression. *)

let P2CH_EVAL_JB = prove
 (`!Js V K (G:real->real^N->real^N^N).
     open V /\ K SUBSET V /\
     (!m p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
              ==> rfa_jb Js V K m (\t z. G t z$p$q)) /\
     (!m p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
              ==> rfa_jb Js V K m (\t z. matrix_inv(G t z)$p$q))
     ==> !e. p2ch_ok (dimindex(:N)) e ==> !m. rfa_jb Js V K m (p2ch_eval G e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC p2ch_expr_INDUCT THEN
  REWRITE_TAC[p2ch_ok; p2ch_eval] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[];
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[RFA_JB_CONST];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_JB_ADD THEN ASM_SIMP_TAC[ETA_AX];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_JB_MUL THEN ASM_SIMP_TAC[ETA_AX];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`Js:real->bool`; `V:real^N->bool`; `K:real^N->bool`; `m:num`;
                   `p2ch_eval (G:real->real^N->real^N^N) a1`] RFA_JB_SUC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `a0:num` o CONJUNCT2) THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The Ricci tensor as a jet polynomial (the syntactic copies                *)
(* of pde_jchr, pde_jdgi, pde_jdchr and pde_jric of pc_pde_rdt_symbol) and   *)
(* its evaluation: on a metric field it is lricci (PDE_RIC_JET).             *)
(* ------------------------------------------------------------------------- *)

let p2ch_xsub = new_definition
 `p2ch_xsub e1 e2 = PHE_ADD e1 (PHE_MUL (PHE_C (--(&1))) e2)`;;

let p2ch_xd1 = new_definition
 `p2ch_xd1 c a b = PHE_D c (PHE_G a b)`;;

let p2ch_xd2 = new_definition
 `p2ch_xd2 c e a b = PHE_D c (PHE_D e (PHE_G a b))`;;

let p2ch_xchr = new_definition
 `p2ch_xchr n m a b =
    p2ch_sumn n (\k. PHE_MUL (PHE_I m k)
                       (PHE_MUL (PHE_C (inv(&2)))
                          (p2ch_xsub (PHE_ADD (p2ch_xd1 a k b) (p2ch_xd1 b k a))
                                     (p2ch_xd1 k a b))))`;;

let p2ch_xdgi = new_definition
 `p2ch_xdgi n c i j =
    PHE_MUL (PHE_C (--(&1)))
      (p2ch_sumn n (\p. p2ch_sumn n (\q.
         PHE_MUL (PHE_I i p) (PHE_MUL (p2ch_xd1 c p q) (PHE_I q j)))))`;;

let p2ch_xdchr = new_definition
 `p2ch_xdchr n c m a b =
    p2ch_sumn n (\k. PHE_ADD
      (PHE_MUL (p2ch_xdgi n c m k)
         (PHE_MUL (PHE_C (inv(&2)))
            (p2ch_xsub (PHE_ADD (p2ch_xd1 a k b) (p2ch_xd1 b k a)) (p2ch_xd1 k a b))))
      (PHE_MUL (PHE_I m k)
         (PHE_MUL (PHE_C (inv(&2)))
            (p2ch_xsub (PHE_ADD (p2ch_xd2 c a k b) (p2ch_xd2 c b k a))
                       (p2ch_xd2 c k a b)))))`;;

let p2ch_xric = new_definition
 `p2ch_xric n a b =
    p2ch_sumn n (\c. PHE_ADD (p2ch_xsub (p2ch_xdchr n c c a b) (p2ch_xdchr n a c c b))
      (p2ch_sumn n (\p. p2ch_xsub (PHE_MUL (p2ch_xchr n p a b) (p2ch_xchr n c c p))
                                  (PHE_MUL (p2ch_xchr n p c b) (p2ch_xchr n c a p)))))`;;

(* Index validity. *)

let P2CH_OK_TAC =
  REPEAT((MATCH_MP_TAC P2CH_OK_SUMN THEN GEN_TAC THEN DISCH_TAC) ORELSE CONJ_TAC ORELSE
         CHANGED_TAC(REWRITE_TAC[p2ch_ok])) THEN
  ASM_ARITH_TAC;;

let P2CH_OK_XRIC = prove
 (`!n a b. 1 <= a /\ a <= n /\ 1 <= b /\ b <= n ==> p2ch_ok n (p2ch_xric n a b)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[p2ch_xric; p2ch_xdchr; p2ch_xchr; p2ch_xdgi; p2ch_xsub; p2ch_xd1; p2ch_xd2] THEN
  P2CH_OK_TAC);;

(* Evaluation of the first and second space partials of the entries. *)

let P2CH_EVAL_D1 = prove
 (`!V (G:real->real^N->real^N^N) t z c a b.
     metric_field V (G t) /\ z IN V /\ 1 <= c /\ c <= dimindex(:N)
     ==> p2ch_eval G (p2ch_xd1 c a b) t z = pde_jd1 (G t) z c a b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2ch_xd1; p2ch_eval; rfa_pd] THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `(G:real->real^N->real^N^N) t`; `z:real^N`;
                 `c:num`; `a:num`; `b:num`] PDE_JG_PARTIAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LIFT_DROP]);;

let P2CH_EVAL_D2 = prove
 (`!V (G:real->real^N->real^N^N) t z c e a b.
     metric_field V (G t) /\ z IN V /\ 1 <= c /\ c <= dimindex(:N) /\
     1 <= e /\ e <= dimindex(:N)
     ==> p2ch_eval G (p2ch_xd2 c e a b) t z = pde_jd2 (G t) z c e a b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(V:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  REWRITE_TAC[p2ch_xd2; p2ch_eval; rfa_pd] THEN
  MP_TAC(ISPECL [`c:num`;
                 `\z. lift(drop(partial_derivative e
                        (\z. lift((G:real->real^N->real^N^N) t z$a$b)) z))`;
                 `\z. lift((mderiv ((G:real->real^N->real^N^N) t) z (basis e))$a$b)`;
                 `V:real^N->bool`; `z:real^N`] PARTIAL_DERIVATIVE_LOCAL_OPEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`V:real^N->bool`; `(G:real->real^N->real^N^N) t`; `y:real^N`;
                   `e:num`; `a:num`; `b:num`] PDE_JG_PARTIAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LIFT_DROP; pde_jd1];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `(G:real->real^N->real^N^N) t`; `z:real^N`;
                 `c:num`; `e:num`; `a:num`; `b:num`] PDE_JD1_PARTIAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LIFT_DROP]);;

(* The clauses of p2ch_eval without the partials. *)

let P2CH_EVAL_NOD =
  end_itlist CONJ (List.filter (fun th -> not(can (find_term (fun t -> try fst(dest_const t) = "PHE_D"
                                                           with Failure _ -> false))
                                          (lhs(snd(strip_forall(concl th))))))
                        (CONJUNCTS p2ch_eval));;

let P2CH_EVAL_XCHR = prove
 (`!V (G:real->real^N->real^N^N) t z m a b.
     metric_field V (G t) /\ z IN V /\ 1 <= a /\ a <= dimindex(:N) /\
     1 <= b /\ b <= dimindex(:N)
     ==> p2ch_eval G (p2ch_xchr (dimindex(:N)) m a b) t z =
         pde_jchr (dimindex(:N)) (pde_jgi (G t) z) (pde_jd1 (G t) z) m a b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2ch_xchr; P2CH_EVAL_SUMN; pde_jchr] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[p2ch_xsub; P2CH_EVAL_NOD; pde_jgi] THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `G:real->real^N->real^N^N`; `t:real`; `z:real^N`]
                P2CH_EVAL_D1) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN REAL_ARITH_TAC);;

let P2CH_EVAL_XDGI = prove
 (`!V (G:real->real^N->real^N^N) t z c i j.
     metric_field V (G t) /\ z IN V /\ 1 <= c /\ c <= dimindex(:N)
     ==> p2ch_eval G (p2ch_xdgi (dimindex(:N)) c i j) t z =
         pde_jdgi (dimindex(:N)) (pde_jgi (G t) z) (pde_jd1 (G t) z) c i j`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2ch_xdgi; P2CH_EVAL_NOD; P2CH_EVAL_SUMN; pde_jdgi] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y ==> -- &1 * x = --y`) THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
  REWRITE_TAC[P2CH_EVAL_SUMN] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
  REWRITE_TAC[P2CH_EVAL_NOD; pde_jgi] THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `G:real->real^N->real^N^N`; `t:real`; `z:real^N`;
                 `c:num`; `p:num`; `q:num`] P2CH_EVAL_D1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

let P2CH_EVAL_XDCHR = prove
 (`!V (G:real->real^N->real^N^N) t z c m a b.
     metric_field V (G t) /\ z IN V /\ 1 <= c /\ c <= dimindex(:N) /\
     1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
     ==> p2ch_eval G (p2ch_xdchr (dimindex(:N)) c m a b) t z =
         pde_jdchr (dimindex(:N)) (pde_jgi (G t) z) (pde_jd1 (G t) z) (pde_jd2 (G t) z)
                   c m a b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2ch_xdchr; P2CH_EVAL_SUMN; pde_jdchr] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[p2ch_xsub; P2CH_EVAL_NOD; pde_jgi] THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `G:real->real^N->real^N^N`; `t:real`; `z:real^N`;
                 `c:num`; `m:num`; `k:num`] P2CH_EVAL_XDGI) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `G:real->real^N->real^N^N`; `t:real`; `z:real^N`]
                P2CH_EVAL_D1) THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `G:real->real^N->real^N^N`; `t:real`; `z:real^N`]
                P2CH_EVAL_D2) THEN
  ASM_SIMP_TAC[] THEN REPEAT(DISCH_THEN(K ALL_TAC)) THEN REWRITE_TAC[pde_jgi] THEN
  REAL_ARITH_TAC);;

let P2CH_EVAL_XRIC = prove
 (`!V (G:real->real^N->real^N^N) t z a b.
     metric_field V (G t) /\ z IN V /\ 1 <= a /\ a <= dimindex(:N) /\
     1 <= b /\ b <= dimindex(:N)
     ==> p2ch_eval G (p2ch_xric (dimindex(:N)) a b) t z = lricci (G t) z (basis a) (basis b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `(G:real->real^N->real^N^N) t`; `z:real^N`;
                 `a:num`; `b:num`] PDE_RIC_JET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[p2ch_xric; P2CH_EVAL_SUMN; pde_jric] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN
  REWRITE_TAC[p2ch_xsub; P2CH_EVAL_NOD; P2CH_EVAL_SUMN] THEN
  MATCH_MP_TAC(REAL_ARITH `e1 = f1 /\ e2 = f2 /\ s = s'
                           ==> (e1 + -- &1 * e2) + s = f1 - f2 + s'`) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2CH_EVAL_XDCHR THEN EXISTS_TAC `V:real^N->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2CH_EVAL_XDCHR THEN EXISTS_TAC `V:real^N->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    REWRITE_TAC[P2CH_EVAL_NOD] THEN
    MATCH_MP_TAC(prove
     (`!a a' b b' c c' d d':real.
         a = a' /\ b = b' /\ c = c' /\ d = d'
         ==> a * b + -- &1 * (c * d) = a' * b' - c' * d'`,
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC)) THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC P2CH_EVAL_XCHR THEN EXISTS_TAC `V:real^N->bool` THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The syntactic time derivative of jet polynomials under the                *)
(* Ricci flow: d/dt G = -2 Ric, d/dt G^-1 = 2 G^-1 Ric G^-1, and the time    *)
(* derivative commutes with space partials.  Every jet polynomial of a local *)
(* Ricci flow is jointly smooth on the flow box with the time derivative     *)
(* given by p2ch_dt (P2CH_EVAL_DT).                                          *)
(* ------------------------------------------------------------------------- *)

let p2ch_dt = new_recursive_definition p2ch_expr_RECURSION
 `(p2ch_dt n (PHE_G p q) = PHE_MUL (PHE_C (--(&2))) (p2ch_xric n p q)) /\
  (p2ch_dt n (PHE_I p q) =
     p2ch_sumn n (\k. p2ch_sumn n (\l.
       PHE_MUL (PHE_I p k) (PHE_MUL (PHE_MUL (PHE_C (&2)) (p2ch_xric n k l)) (PHE_I l q))))) /\
  (p2ch_dt n (PHE_C c) = PHE_C (&0)) /\
  (p2ch_dt n (PHE_ADD e1 e2) = PHE_ADD (p2ch_dt n e1) (p2ch_dt n e2)) /\
  (p2ch_dt n (PHE_MUL e1 e2) =
     PHE_ADD (PHE_MUL (p2ch_dt n e1) e2) (PHE_MUL e1 (p2ch_dt n e2))) /\
  (p2ch_dt n (PHE_D i e) = PHE_D i (p2ch_dt n e))`;;

let P2CH_OK_DT = prove
 (`!n e. p2ch_ok n e ==> p2ch_ok n (p2ch_dt n e)`,
  GEN_TAC THEN MATCH_MP_TAC p2ch_expr_INDUCT THEN
  REWRITE_TAC[p2ch_dt; p2ch_ok] THEN SIMP_TAC[] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CH_OK_XRIC THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CH_OK_SUMN THEN X_GEN_TAC `k:num` THEN
    DISCH_TAC THEN BETA_TAC THEN MATCH_MP_TAC P2CH_OK_SUMN THEN X_GEN_TAC `l:num` THEN
    DISCH_TAC THEN BETA_TAC THEN
    REWRITE_TAC[p2ch_ok] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2CH_OK_XRIC THEN ASM_REWRITE_TAC[]]);;

(* The time derivative of the inverse metric entries (the text of           *)
(* RFA_GINV_DT of pc_rfa_hcalc, which is not in this load closure).         *)

let P2CH_GINV_DT = prove
 (`!U a b (G:real->real^N->real^N^N) t y p q.
     lricci_flow U a b G /\ a < t /\ t < b /\ y IN U /\
     1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
     ==> ((\s. matrix_inv(G s y)$p$q) has_real_derivative
          &2 * sum(1..dimindex(:N)) (\c. sum(1..dimindex(:N)) (\d.
                 matrix_inv(G t y)$p$c * lricci (G t) y (basis c) (basis d) *
                 matrix_inv(G t y)$d$q))) (atreal t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `t:real`; `y:real^N`] LRG_FLOW_DGINV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`p:num`; `q:num`] o
    MATCH_MP (REWRITE_RULE[IMP_CONJ] (ISPECL
      [`\s. matrix_inv((G:real->real^N->real^N^N) s y)`] LRG_VDERIV_MATRIX_ENTRY_REAL))) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[]
   `(x:real) = y ==> (f has_real_derivative x) net ==> (f has_real_derivative y) net`) THEN
  ASM_SIMP_TAC[MATRIX_NEG_COMPONENT; matrix_mul; LAMBDA_BETA] THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_NEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[LAMBDA_BETA] THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_NEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC);;

(* Joint smoothness and time derivative of every jet polynomial. *)

let P2CH_EVAL_DT = prove
 (`!V a b (G:real->real^N->real^N^N).
     lricci_flow V a b G
     ==> !e. p2ch_ok (dimindex(:N)) e
             ==> smooth_map_on (interval(lift a,lift b) PCROSS V)
                   (\w. lift(p2ch_eval G e (drop(fstcart w)) (sndcart w))) /\
                 !t z. a < t /\ t < b /\ z IN V
                       ==> ((\s. p2ch_eval G e s z) has_real_derivative
                            p2ch_eval G (p2ch_dt (dimindex(:N)) e) t z) (atreal t)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RFA_LRICCI_FLOW_LSMOOTH) THEN
  MATCH_MP_TAC p2ch_expr_INDUCT THEN REWRITE_TAC[p2ch_ok; p2ch_dt] THEN
  REPEAT CONJ_TAC THENL
   [(* PHE_G *)
    MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN STRIP_TAC THEN
    REWRITE_TAC[p2ch_eval] THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `(\w. lift((G:real->real^N->real^N^N) (drop(fstcart w)) (sndcart w)$p$q)) =
        (\m:real^(N,N)finite_prod. lift((matrify m:real^N^N)$p$q)) o
        (\w. vectorize(G (drop(fstcart w)) (sndcart w)))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; MATRIFY_VECTORIZE]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[linear; MATRIFY_ADD; MATRIFY_CMUL; MATRIX_ADD_COMPONENT;
                  MATRIX_CMUL_COMPONENT; LIFT_ADD; LIFT_CMUL];
      MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN STRIP_TAC THEN
      UNDISCH_TAC `lricci_flow V a b (G:real->real^N->real^N^N)` THEN
      REWRITE_TAC[lricci_flow] THEN
      DISCH_THEN(MP_TAC o SPECL [`t:real`; `z:real^N`; `p:num`; `q:num`] o
                 last o CONJUNCTS) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(MESON[]
       `(x:real) = y ==> (f has_real_derivative x) net ==> (f has_real_derivative y) net`) THEN
      REWRITE_TAC[P2CH_EVAL_NOD] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC P2CH_EVAL_XRIC THEN EXISTS_TAC `V:real^N->bool` THEN ASM_SIMP_TAC[]];
    (* PHE_I *)
    MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN STRIP_TAC THEN
    REWRITE_TAC[p2ch_eval] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LRG_LSMOOTH_GINV_ENTRY THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`V:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                     `t:real`; `z:real^N`; `p:num`; `q:num`] P2CH_GINV_DT) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(MESON[]
       `(x:real) = y ==> (f has_real_derivative x) net ==> (f has_real_derivative y) net`) THEN
      REWRITE_TAC[P2CH_EVAL_SUMN; GSYM SUM_LMUL] THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN
      REWRITE_TAC[P2CH_EVAL_SUMN; GSYM SUM_LMUL] THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
      REWRITE_TAC[P2CH_EVAL_NOD] THEN
      MP_TAC(ISPECL [`V:real^N->bool`; `G:real->real^N->real^N^N`; `t:real`; `z:real^N`;
                     `c:num`; `d:num`] P2CH_EVAL_XRIC) THEN
      ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN REAL_ARITH_TAC];
    (* PHE_C *)
    GEN_TAC THEN REWRITE_TAC[p2ch_eval; SMOOTH_MAP_ON_CONST; HAS_REAL_DERIVATIVE_CONST];
    (* PHE_ADD *)
    MAP_EVERY X_GEN_TAC [`e1:p2ch_expr`; `e2:p2ch_expr`] THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN REWRITE_TAC[p2ch_eval] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PDE_SMOOTH_LIFT_ADD_REAL THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN ASM_SIMP_TAC[]];
    (* PHE_MUL *)
    MAP_EVERY X_GEN_TAC [`e1:p2ch_expr`; `e2:p2ch_expr`] THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN REWRITE_TAC[p2ch_eval] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`\s. p2ch_eval (G:real->real^N->real^N^N) e1 s z`;
                     `p2ch_eval (G:real->real^N->real^N^N) (p2ch_dt (dimindex(:N)) e1) t z`;
                     `\s. p2ch_eval (G:real->real^N->real^N^N) e2 s z`;
                     `p2ch_eval (G:real->real^N->real^N^N) (p2ch_dt (dimindex(:N)) e2) t z`;
                     `t:real`] HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
      ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC(MESON[]
       `(x:real) = y ==> (f has_real_derivative x) net ==> (f has_real_derivative y) net`) THEN
      REAL_ARITH_TAC];
    (* PHE_D *)
    MAP_EVERY X_GEN_TAC [`i:num`; `e:p2ch_expr`] THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN REWRITE_TAC[p2ch_eval] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`interval(lift a,lift b) PCROSS (V:real^N->bool)`;
                     `\w. lift(p2ch_eval (G:real->real^N->real^N^N) e (drop(fstcart w))
                                         (sndcart w))`;
                     `basis i:real^N`] LRG_JOINT_PARTIAL) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(MESON[] `(f:real^(1,N)finite_sum->real^1) = g
                            ==> smooth_map_on s f ==> smooth_map_on s g`) THEN
      REWRITE_TAC[FUN_EQ_THM; rfa_pd; LIFT_DROP; partial_derivative] THEN
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART];
      REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`V:real^N->bool`; `a:real`; `b:real`;
                     `p2ch_eval (G:real->real^N->real^N^N) e`;
                     `p2ch_eval (G:real->real^N->real^N^N) (p2ch_dt (dimindex(:N)) e)`;
                     `[i:num]`; `t:real`; `z:real^N`] RFA_JET_DT) THEN
      ASM_SIMP_TAC[] THEN REWRITE_TAC[RFA_JET_CONS] THEN
      REWRITE_TAC[rfa_jet; iterated_partial; LIFT_DROP; ETA_AX]]]);;

(* ------------------------------------------------------------------------- *)
(* Space-time partials.  Coordinate 1 of real^(1,N)finite_sum is              *)
(* time and 1 + k is the space coordinate k; along a space-time index list l *)
(* the iterated partial of a jet polynomial of a local Ricci flow is the     *)
(* jet polynomial p2ch_stx l e (time partials by p2ch_dt, space partials by  *)
(* PHE_D).  With the uniform Hamilton lemma this bounds every space-time     *)
(* jet of a family of local flows uniformly (P2CH_ST_JETS).                  *)
(* ------------------------------------------------------------------------- *)

let p2ch_stx = define
 `(p2ch_stx n [] e = e) /\
  (p2ch_stx n (CONS h l) e =
     if h = 1 then p2ch_dt n (p2ch_stx n l e) else PHE_D (h - 1) (p2ch_stx n l e))`;;

let P2CH_OK_STX = prove
 (`!n l e. ALL (\i. 1 <= i /\ i <= n + 1) l /\ p2ch_ok n e ==> p2ch_ok n (p2ch_stx n l e)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[p2ch_stx; ALL] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[P2CH_OK_DT; p2ch_ok] THEN
  ASM_ARITH_TAC);;

let P2CH_ST_PARTIAL = prove
 (`!V a b (G:real->real^N->real^N^N).
     lricci_flow V a b G
     ==> !l e. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l /\
               p2ch_ok (dimindex(:N)) e
               ==> !w. w IN interval(lift a,lift b) PCROSS V
                       ==> iterated_partial l
                             (\w. lift(p2ch_eval G e (drop(fstcart w)) (sndcart w))) w =
                           lift(p2ch_eval G (p2ch_stx (dimindex(:N)) l e)
                                          (drop(fstcart w)) (sndcart w))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
  ABBREV_TAC `B = interval(lift a,lift b) PCROSS (V:real^N->bool)` THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[iterated_partial; p2ch_stx]; ALL_TAC] THEN
  REWRITE_TAC[ALL; DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN
  X_GEN_TAC `e:p2ch_expr` THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2ch_ok (dimindex(:N)) (p2ch_stx (dimindex(:N)) t e)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2CH_OK_STX THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ALL (\i. 1 <= i /\ i <= 1 + dimindex(:N)) t` THEN
    MATCH_MP_TAC MONO_ALL THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`]
                P2CH_EVAL_DT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `p2ch_stx (dimindex(:N)) t e`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  X_GEN_TAC `w:real^(1,N)finite_sum` THEN DISCH_TAC THEN
  REWRITE_TAC[iterated_partial] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `partial_derivative h
                (\w. lift(p2ch_eval (G:real->real^N->real^N^N) (p2ch_stx (dimindex(:N)) t e)
                                    (drop(fstcart w)) (sndcart w))) w` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN EXISTS_TAC `B:real^(1,N)finite_sum->bool` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ALL (\i. 1 <= i /\ i <= 1 + dimindex(:N)) t` THEN
    REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1];
    ALL_TAC] THEN
  SUBGOAL_THEN `?s y. w = pastecart (lift s) (y:real^N)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXISTS_TAC [`drop(fstcart(w:real^(1,N)finite_sum))`;
                          `sndcart(w:real^(1,N)finite_sum)`] THEN
    REWRITE_TAC[LIFT_DROP; PASTECART_FST_SND];
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  UNDISCH_TAC `pastecart (lift s) (y:real^N) IN B` THEN EXPAND_TAC "B" THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN STRIP_TAC THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; p2ch_stx] THEN
  SUBGOAL_THEN
   `(\w. lift(p2ch_eval (G:real->real^N->real^N^N) (p2ch_stx (dimindex(:N)) t e)
                        (drop(fstcart w)) (sndcart w)))
    differentiable at (pastecart (lift s) y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `B:real^(1,N)finite_sum->bool` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "B" THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL
     [`\w. lift(p2ch_eval (G:real->real^N->real^N^N) (p2ch_stx (dimindex(:N)) t e)
                          (drop(fstcart w)) (sndcart w))`; `s:real`; `y:real^N`]
     PDE_ST_TIME_REAL_DERIV) THEN
    ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    DISCH_TAC THEN
    MATCH_MP_TAC(MESON[LIFT_DROP] `drop x = y ==> x = lift y`) THEN
    MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
    EXISTS_TAC `\s. p2ch_eval (G:real->real^N->real^N^N) (p2ch_stx (dimindex(:N)) t e) s y` THEN
    EXISTS_TAC `s:real` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `h = 1 + (h - 1) /\ 1 <= h - 1 /\ h - 1 <= dimindex(:N)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RATOR_CONV o RAND_CONV)
                                          [th]) THEN
  MP_TAC(ISPECL
   [`\w. lift(p2ch_eval (G:real->real^N->real^N^N) (p2ch_stx (dimindex(:N)) t e)
                        (drop(fstcart w)) (sndcart w))`; `lift s`; `y:real^N`; `h - 1`]
   PDE_ST_SLICE_PARTIAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; p2ch_eval; rfa_pd] THEN
  REWRITE_TAC[ETA_AX]);;

(* Uniform bounds of all space-time jets of a family of local flows. *)

let P2CH_ST_JETS = prove
 (`!V K a b (Gs:num->real->real^N->real^N^N) Lm.
     open V /\ compact K /\ K SUBSET V /\ a <= &0 /\ &0 <= b /\ a < b /\ &0 <= Lm /\
     (!n. lricci_flow V a b (Gs n)) /\
     (!n t. a <= t /\ t <= b ==> metric_field V (Gs n t)) /\
     (!n. ?e (FF:real^(1,N)finite_sum->real^(N,N)finite_prod).
            &0 < e /\ smooth_map_on (interval(lift(a - e),lift(b + e)) PCROSS V) FF /\
            (!t y. a <= t /\ t <= b /\ y IN V
                   ==> FF(pastecart (lift t) y) = vectorize(Gs n t y))) /\
     (!n t y p q. a <= t /\ t <= b /\ y IN K /\ 1 <= p /\ p <= dimindex(:N) /\
                  1 <= q /\ q <= dimindex(:N) ==> abs(Gs n t y$p$q) <= Lm) /\
     (!n t y v. a <= t /\ t <= b /\ y IN K
                ==> norm v pow 2 <= Lm * (v dot (Gs n t y ** v))) /\
     (!j. ?C. !n t y. a <= t /\ t <= b /\ y IN K ==> lrm_deriv_norm2 j (Gs n t) y <= C) /\
     (!m p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
              ==> ?B. !n l y. l IN pde_index_lists m (:N) /\ y IN K
                              ==> abs(drop(iterated_partial l (\z. lift(Gs n (&0) z$p$q)) y))
                                  <= B)
     ==> !l p q. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l /\
                 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
                 ==> ?B. !n w. w IN interval(lift a,lift b) PCROSS K
                              ==> norm(iterated_partial l
                                        (\w. lift(Gs n (drop(fstcart w)) (sndcart w)$p$q)) w)
                                  <= B`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(LABEL_TAC "uj" o MATCH_MP P2CH_UNIFORM) THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "lf")
    (CONJUNCTS_THEN2 (LABEL_TAC "mf") (CONJUNCTS_THEN2 (LABEL_TAC "ext")
    (CONJUNCTS_THEN2 (LABEL_TAC "ent") (CONJUNCTS_THEN2 (LABEL_TAC "eqv")
    (CONJUNCTS_THEN2 (LABEL_TAC "rmd") (LABEL_TAC "ini")))))))))))))) THEN
  DISCH_THEN(LABEL_TAC "uj") THEN
  ABBREV_TAC `L = &2 * (abs a + abs b + &1)` THEN
  SUBGOAL_THEN `&0 < L /\ !t. a <= t /\ t <= b ==> abs t < L / &2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Gc = p2ch_win (Gs:num->real->real^N->real^N^N) L` THEN
  SUBGOAL_THEN `!n t. a <= t /\ t <= b ==> (Gc:real->real^N->real^N^N) (t + &n * L) = Gs n t`
  (LABEL_TAC "win") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "Gc" THEN MATCH_MP_TAC P2CH_WIN THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Js = {t + &n * L | n,t | a <= t /\ t <= b}` THEN
  SUBGOAL_THEN `!tt. tt IN Js ==> ?n t. a <= t /\ t <= b /\ tt = t + &n * L /\
                                         (Gc:real->real^N->real^N^N) tt = Gs n t`
  (LABEL_TAC "js") THENL
   [EXPAND_TAC "Js" THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `t:real`] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `t:real`] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!tt. tt IN Js ==> metric_field V ((Gc:real->real^N->real^N^N) tt)`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN USE_THEN "js" (MP_TAC o C MP (ASSUME `(tt:real) IN Js`) o
      SPEC `tt:real`) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "mf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!m p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
                        ==> rfa_jb Js V K m (\tt z. (Gc:real->real^N->real^N^N) tt z$p$q)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_jb] THEN CONJ_TAC THENL
     [X_GEN_TAC `tt:real` THEN DISCH_TAC THEN
      MATCH_MP_TAC PDE_SMOOTH_G_ENTRY THEN REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[];
      USE_THEN "uj" (MP_TAC o SPECL [`m:num`; `p:num`; `q:num`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `B:real` THEN DISCH_TAC THEN
      MAP_EVERY X_GEN_TAC [`tt:real`; `l:num list`; `y:real^N`] THEN STRIP_TAC THEN
      USE_THEN "js" (MP_TAC o C MP (ASSUME `(tt:real) IN Js`) o SPEC `tt:real`) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!tt y v. tt IN Js /\ y IN K
                         ==> norm v pow 2 <= Lm * (v dot ((Gc:real->real^N->real^N^N) tt y ** v))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "js" (MP_TAC o C MP (ASSUME `(tt:real) IN Js`) o
      SPEC `tt:real`) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "eqv" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!m p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
                        ==> rfa_jb Js V K m
                              (\tt z. matrix_inv((Gc:real->real^N->real^N^N) tt z)$p$q)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`Js:real->bool`; `V:real^N->bool`; `K:real^N->bool`;
                   `Gc:real->real^N->real^N^N`; `Lm:real`] P2CH_CHRIST_JB) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`m:num`; `Js:real->bool`; `V:real^N->bool`; `K:real^N->bool`;
                   `Gc:real->real^N->real^N^N`] RFA_JB_GINV) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN MATCH_MP_TAC RFA_R1_GINV0 THEN EXISTS_TAC `Lm:real` THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o SPECL [`m:num`; `p:num`; `q:num`]) THEN
      ASM_REWRITE_TAC[ARITH_RULE `m <= m + 1`]];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `e' = p2ch_stx (dimindex(:N)) l (PHE_G p q)` THEN
  SUBGOAL_THEN `p2ch_ok (dimindex(:N)) e'` ASSUME_TAC THENL
   [EXPAND_TAC "e'" THEN MATCH_MP_TAC P2CH_OK_STX THEN
    ASM_REWRITE_TAC[p2ch_ok] THEN
    UNDISCH_TAC `ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l` THEN
    REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN
    MATCH_MP_TAC MONO_ALL THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Js:real->bool`; `V:real^N->bool`; `K:real^N->bool`;
                 `Gc:real->real^N->real^N^N`] P2CH_EVAL_JB) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `0` o C MP (ASSUME `p2ch_ok (dimindex(:N)) e'`) o
             SPEC `e':p2ch_expr`) THEN
  REWRITE_TAC[rfa_jb] THEN
  DISCH_THEN(X_CHOOSE_TAC `C:real` o CONJUNCT2) THEN EXISTS_TAC `C:real` THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `w:real^(1,N)finite_sum`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?s y. w = pastecart (lift s) (y:real^N)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXISTS_TAC [`drop(fstcart(w:real^(1,N)finite_sum))`;
                          `sndcart(w:real^(1,N)finite_sum)`] THEN
    REWRITE_TAC[LIFT_DROP; PASTECART_FST_SND];
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  UNDISCH_TAC `pastecart (lift s) (y:real^N) IN interval(lift a,lift b) PCROSS K` THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `a:real`; `b:real`;
                 `(Gs:num->real->real^N->real^N^N) n`] P2CH_ST_PARTIAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`l:num list`; `PHE_G p q`]) THEN
  ASM_REWRITE_TAC[p2ch_ok] THEN
  DISCH_THEN(MP_TAC o SPEC `pastecart (lift s) (y:real^N)`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2ch_eval; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[NORM_LIFT] THEN
  MP_TAC(ISPECL [`(Gs:num->real->real^N->real^N^N) n`; `Gc:real->real^N->real^N^N`;
                 `s:real`; `s + &n * L`] P2CH_EVAL_SLICE) THEN
  ANTS_TAC THENL
   [CONV_TAC SYM_CONV THEN USE_THEN "win" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s + &n * L`; `[]:num list`; `y:real^N`]) THEN
  REWRITE_TAC[iterated_partial; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [EXPAND_TAC "Js" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `s:real`] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[pde_index_lists; IN_ELIM_THM; LENGTH; ALL; LE_0]]);;

