(* ========================================================================= *)
(* Unit pc_p2c_flfrom (Part 2C, flowlim route): smoothness from the initial *)
(* time of local limits.  A map smooth on an open time slab (a,b) x U whose *)
(* values and iterated partials extend continuously, near every point of U, *)
(* to the half-open slab [a,b) x O, extends smoothly past a (PDE_SEELEY via *)
(* a patching of the local extensions, P2CB_UPTO).  For the local limits of *)
(* pc_p2c_flconv the extensions are the uniform limits H on the closed      *)
(* boxes of the Arzela-Ascoli context p2cm_ctx (P2CB_CTX_EXISTS,            *)
(* P2CB_CTX_DATA), and a metric that is the lck limit of the same sequence  *)
(* is the local limit (P2CB_LCK_LIM_UNIQUE).                                 *)
(* ========================================================================= *)

needs "src/pc_p2c_flasm.ml";;
needs "src/pc_pde_seeley.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Patching of local continuous extensions from the open time               *)
(* slab to the half-open slab, and the Seeley extension from local data.    *)
(* ------------------------------------------------------------------------- *)

let P2CB_SLAB = prove
 (`!a b (O:real^N->bool).
     {pastecart (lift t) y | a <= t /\ t < b /\ y IN O} =
     {x | a <= drop x /\ drop x < b} PCROSS O`,
  REWRITE_TAC[EXTENSION; PCROSS; IN_ELIM_THM] THEN REPEAT GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[LIFT_DROP]; MESON_TAC[LIFT_DROP]]);;

let P2CB_OPEN_SLAB = prove
 (`!a b (O:real^N->bool) (P:real^(1,N)finite_sum->bool).
     (!t y. a < t /\ t < b /\ y IN O ==> P(pastecart (lift t) y)) <=>
     (!w. w IN interval(lift a,lift b) PCROSS O ==> P w)`,
  REWRITE_TAC[FORALL_IN_PCROSS; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP; GSYM CONJ_ASSOC]);;

let P2CB_AGREE = prove
 (`!a b (O1:real^N->bool) O2 (h1:real^(1,N)finite_sum->real^K) h2 f y t.
     a < b /\ open O1 /\ open O2 /\ y IN O1 /\ y IN O2 /\
     h1 continuous_on ({x | a <= drop x /\ drop x < b} PCROSS O1) /\
     h2 continuous_on ({x | a <= drop x /\ drop x < b} PCROSS O2) /\
     (!w. w IN interval(lift a,lift b) PCROSS O1 ==> h1 w = f w) /\
     (!w. w IN interval(lift a,lift b) PCROSS O2 ==> h2 w = f w) /\
     a <= t /\ t < b
     ==> h1 (pastecart (lift t) y) = h2 (pastecart (lift t) y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(ISPECL [`h1:real^(1,N)finite_sum->real^K`; `h2:real^(1,N)finite_sum->real^K`;
                 `interval(lift a,lift b) PCROSS ((O1:real^N->bool) INTER O2)`;
                 `{x | a <= drop x /\ drop x < b} PCROSS ((O1:real^N->bool) INTER O2)`]
                CONTINUOUS_AGREE_ON_INTERMEDIATE_CLOSURE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `{x | a <= drop x /\ drop x < b} PCROSS (O1:real^N->bool)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL] THEN
      SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `{x | a <= drop x /\ drop x < b} PCROSS (O2:real^N->bool)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL] THEN
      SET_TAC[];
      MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL] THEN
      REWRITE_TAC[SUBSET; IN_INTERVAL_1; IN_ELIM_THM; LIFT_DROP] THEN REAL_ARITH_TAC;
      REWRITE_TAC[CLOSURE_PCROSS] THEN
      SUBGOAL_THEN `closure(interval(lift a,lift b)) = interval[lift a,lift b]`
      SUBST1_TAC THENL
       [MATCH_MP_TAC CLOSURE_OPEN_INTERVAL THEN
        ASM_REWRITE_TAC[INTERVAL_NE_EMPTY_1; LIFT_DROP];
        ALL_TAC] THEN
      MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[CLOSURE_SUBSET] THEN
      REWRITE_TAC[SUBSET; IN_INTERVAL_1; IN_ELIM_THM; LIFT_DROP] THEN REAL_ARITH_TAC;
      REWRITE_TAC[FORALL_IN_PCROSS] THEN
      MAP_EVERY X_GEN_TAC [`u:real^1`; `z:real^N`] THEN REWRITE_TAC[IN_INTER] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `h1(pastecart (u:real^1) (z:real^N)):real^K = f(pastecart u z) /\
                    h2(pastecart u z):real^K = f(pastecart u z)`
      (fun th -> REWRITE_TAC[th]) THEN
      CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[PASTECART_IN_PCROSS]];
    ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_ELIM_THM; LIFT_DROP; IN_INTER]);;

let P2CB_PATCH = prove
 (`!a b (U:real^N->bool) (f:real^(1,N)finite_sum->real^K).
     a < b /\
     (!y0. y0 IN U
           ==> ?O h. open O /\ y0 IN O /\ O SUBSET U /\
                     h continuous_on ({x | a <= drop x /\ drop x < b} PCROSS O) /\
                     !w. w IN interval(lift a,lift b) PCROSS O ==> h w = f w)
     ==> ?h. h continuous_on ({x | a <= drop x /\ drop x < b} PCROSS U) /\
             !w. w IN interval(lift a,lift b) PCROSS U ==> h w = f w`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM])) THEN
  DISCH_THEN(X_CHOOSE_THEN `O:real^N->real^N->bool`
    (X_CHOOSE_THEN `h:real^N->real^(1,N)finite_sum->real^K` (LABEL_TAC "loc"))) THEN
  SUBGOAL_THEN
   `!y0 w. y0 IN U /\ w IN {x | a <= drop x /\ drop x < b} PCROSS ((O:real^N->real^N->bool) y0)
           ==> (h:real^N->real^(1,N)finite_sum->real^K) (sndcart w) w = h y0 w`
  (LABEL_TAC "agree") THENL
   [MAP_EVERY X_GEN_TAC [`y0:real^N`; `w:real^(1,N)finite_sum`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `sndcart(w:real^(1,N)finite_sum) IN (O:real^N->real^N->bool) y0 /\
                  a <= drop(fstcart w) /\ drop(fstcart w) < b`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(w:real^(1,N)finite_sum) IN
                   {x | a <= drop x /\ drop x < b} PCROSS (O:real^N->real^N->bool) y0` THEN
      ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN
      REWRITE_TAC[PASTECART_IN_PCROSS; IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
      CONV_TAC TAUT;
      ALL_TAC] THEN
    USE_THEN "loc" (MP_TAC o C MP (ASSUME `(y0:real^N) IN U`) o SPEC `y0:real^N`) THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    SUBGOAL_THEN `sndcart(w:real^(1,N)finite_sum) IN U` ASSUME_TAC THENL
     [UNDISCH_TAC `(O:real^N->real^N->bool) y0 SUBSET U` THEN
      UNDISCH_TAC `sndcart(w:real^(1,N)finite_sum) IN (O:real^N->real^N->bool) y0` THEN
      SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "loc" (MP_TAC o C MP (ASSUME `sndcart(w:real^(1,N)finite_sum) IN U`) o
                    SPEC `sndcart(w:real^(1,N)finite_sum)`) THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    SUBGOAL_THEN `w = pastecart (lift(drop(fstcart(w:real^(1,N)finite_sum)))) (sndcart w)`
    SUBST1_TAC THENL [REWRITE_TAC[LIFT_DROP; PASTECART_FST_SND]; ALL_TAC] THEN
    REWRITE_TAC[SNDCART_PASTECART] THEN MATCH_MP_TAC P2CB_AGREE THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`;
                          `(O:real^N->real^N->bool) (sndcart(w:real^(1,N)finite_sum))`;
                          `(O:real^N->real^N->bool) y0`;
                          `f:real^(1,N)finite_sum->real^K`] THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  EXISTS_TAC `\w:real^(1,N)finite_sum. (h:real^N->real^(1,N)finite_sum->real^K) (sndcart w) w` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    X_GEN_TAC `w0:real^(1,N)finite_sum` THEN DISCH_TAC THEN
    ABBREV_TAC `y0 = sndcart(w0:real^(1,N)finite_sum)` THEN
    SUBGOAL_THEN `(y0:real^N) IN U` ASSUME_TAC THENL
     [UNDISCH_TAC `(w0:real^(1,N)finite_sum) IN {x | a <= drop x /\ drop x < b} PCROSS U` THEN
      ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS] THEN SIMP_TAC[];
      ALL_TAC] THEN
    USE_THEN "loc" (MP_TAC o C MP (ASSUME `(y0:real^N) IN U`) o SPEC `y0:real^N`) THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    ABBREV_TAC `Tb = {x | a <= drop x /\ drop x < b} PCROSS (O:real^N->real^N->bool) y0` THEN
    SUBGOAL_THEN `(w0:real^(1,N)finite_sum) IN Tb` ASSUME_TAC THENL
     [EXPAND_TAC "Tb" THEN
      UNDISCH_TAC `(w0:real^(1,N)finite_sum) IN {x | a <= drop x /\ drop x < b} PCROSS U` THEN
      ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `open_in (subtopology euclidean ({x | a <= drop x /\ drop x < b} PCROSS U))
                          (Tb:real^(1,N)finite_sum->bool)`
    ASSUME_TAC THENL
     [REWRITE_TAC[OPEN_IN_OPEN] THEN
      EXISTS_TAC `(:real^1) PCROSS (O:real^N->real^N->bool) y0` THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV] THEN EXPAND_TAC "Tb" THEN
      REWRITE_TAC[EXTENSION; IN_INTER] THEN
      REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_UNIV] THEN
      UNDISCH_TAC `(O:real^N->real^N->bool) y0 SUBSET U` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\w:real^(1,N)finite_sum. (h:real^N->real^(1,N)finite_sum->real^K) (sndcart w) w`;
                   `w0:real^(1,N)finite_sum`;
                   `{x | a <= drop x /\ drop x < b} PCROSS (U:real^N->bool)`;
                   `Tb:real^(1,N)finite_sum->bool`] CONTINUOUS_WITHIN_OPEN_IN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `(\w:real^(1,N)finite_sum. (h:real^N->real^(1,N)finite_sum->real^K) (sndcart w) w)
                  continuous_on Tb`
    MP_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
      EXISTS_TAC `(h:real^N->real^(1,N)finite_sum->real^K) y0` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `v:real^(1,N)finite_sum` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      CONV_TAC SYM_CONV THEN USE_THEN "agree" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(v:real^(1,N)finite_sum) IN Tb` THEN EXPAND_TAC "Tb" THEN SIMP_TAC[];
      REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN ASM_SIMP_TAC[]];
    X_GEN_TAC `w:real^(1,N)finite_sum` THEN DISCH_TAC THEN
    SUBGOAL_THEN `sndcart(w:real^(1,N)finite_sum) IN U /\ fstcart w IN interval(lift a,lift b)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(w:real^(1,N)finite_sum) IN interval(lift a,lift b) PCROSS U` THEN
      ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN
      REWRITE_TAC[PASTECART_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART] THEN SIMP_TAC[];
      ALL_TAC] THEN
    USE_THEN "loc" (MP_TAC o C MP (ASSUME `sndcart(w:real^(1,N)finite_sum) IN U`) o
                    SPEC `sndcart(w:real^(1,N)finite_sum)`) THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; SNDCART_PASTECART]]);;

let P2CB_SLAB_OPEN_IN = prove
 (`!a b (O:real^N->bool) U.
     open O /\ O SUBSET U
     ==> open_in (subtopology euclidean ({x | a <= drop x /\ drop x < b} PCROSS U))
                 ({x | a <= drop x /\ drop x < b} PCROSS O)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[OPEN_IN_OPEN] THEN
  EXISTS_TAC `(:real^1) PCROSS (O:real^N->bool)` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_UNIV] THEN
  ASM SET_TAC[]);;

let P2CB_CONT_LOCAL = prove
 (`!(f:real^(1,N)finite_sum->real^K) a b U.
     (!y0. y0 IN U
           ==> ?O. open O /\ y0 IN O /\ O SUBSET U /\
                   f continuous_on ({x | a <= drop x /\ drop x < b} PCROSS O))
     ==> f continuous_on ({x | a <= drop x /\ drop x < b} PCROSS U)`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "loc") THEN
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  X_GEN_TAC `w0:real^(1,N)finite_sum` THEN DISCH_TAC THEN
  SUBGOAL_THEN `sndcart(w0:real^(1,N)finite_sum) IN U /\
                fstcart w0 IN {x | a <= drop x /\ drop x < b}`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(w0:real^(1,N)finite_sum) IN {x | a <= drop x /\ drop x < b} PCROSS U` THEN
    ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    CONV_TAC TAUT;
    ALL_TAC] THEN
  USE_THEN "loc" (MP_TAC o C MP (ASSUME `sndcart(w0:real^(1,N)finite_sum) IN U`) o
                  SPEC `sndcart(w0:real^(1,N)finite_sum)`) THEN
  DISCH_THEN(X_CHOOSE_THEN `O:real^N->bool` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  SUBGOAL_THEN `(w0:real^(1,N)finite_sum) IN {x | a <= drop x /\ drop x < b} PCROSS O`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^K`; `w0:real^(1,N)finite_sum`;
                 `{x | a <= drop x /\ drop x < b} PCROSS (U:real^N->bool)`;
                 `{x | a <= drop x /\ drop x < b} PCROSS (O:real^N->bool)`]
                CONTINUOUS_WITHIN_OPEN_IN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2CB_SLAB_OPEN_IN THEN ASM_REWRITE_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  UNDISCH_TAC `(f:real^(1,N)finite_sum->real^K) continuous_on
               ({x | a <= drop x /\ drop x < b} PCROSS (O:real^N->bool))` THEN
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let P2CB_UPTO = prove
 (`!a b (U:real^N->bool) (u:real->real^N->real^K).
     open U /\ a < b /\
     smooth_map_on (interval(lift a,lift b) PCROSS U) (\z. u (drop(fstcart z)) (sndcart z)) /\
     (!y0. y0 IN U
           ==> ?O. open O /\ y0 IN O /\ O SUBSET U /\
                   (\z. u (drop(fstcart z)) (sndcart z)) continuous_on
                     ({x | a <= drop x /\ drop x < b} PCROSS O) /\
                   !l. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l
                       ==> ?h. h continuous_on ({x | a <= drop x /\ drop x < b} PCROSS O) /\
                               !w. w IN interval(lift a,lift b) PCROSS O
                                   ==> h w = iterated_partial l
                                               (\z. u (drop(fstcart z)) (sndcart z)) w)
     ==> pde_upto a b U u`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "loc")))) THEN
  MATCH_MP_TAC PDE_SEELEY THEN ASM_REWRITE_TAC[pde_upto_classical; P2CB_SLAB] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2CB_CONT_LOCAL THEN X_GEN_TAC `y0:real^N` THEN DISCH_TAC THEN
    USE_THEN "loc" (MP_TAC o C MP (ASSUME `(y0:real^N) IN U`) o SPEC `y0:real^N`) THEN
    MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `l:(num)list` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`a:real`; `b:real`; `U:real^N->bool`;
                 `iterated_partial l (\z:real^(1,N)finite_sum.
                                        (u:real->real^N->real^K) (drop(fstcart z)) (sndcart z))`]
                P2CB_PATCH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y0:real^N` THEN DISCH_TAC THEN
    USE_THEN "loc" (MP_TAC o C MP (ASSUME `(y0:real^N) IN U`) o SPEC `y0:real^N`) THEN
    DISCH_THEN(X_CHOOSE_THEN `O:real^N->bool` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o C MP (ASSUME
      `ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l`) o SPEC `l:(num)list`) THEN
    DISCH_THEN(X_CHOOSE_THEN `h:real^(1,N)finite_sum->real^K` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`O:real^N->bool`; `h:real^(1,N)finite_sum->real^K`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h:real^(1,N)finite_sum->real^K` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP]);;

(* ------------------------------------------------------------------------- *)
(* The Arzela-Ascoli context p2cm_ctx of pc_p2c_flconv exists               *)
(* under the hypotheses of P2CM_LOCAL_LIMIT (its proof up to the context,   *)
(* P2CB_CTX_EXISTS), in particular under p2ca_seqhyp (P2CB_CTX_SEQHYP).      *)
(* ------------------------------------------------------------------------- *)

let P2CB_CTX_EXISTS = prove
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
     ==> ?(FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod) ee c r (sub:num->num)
           (H:num#num#num->(num)list->real^(1,N)finite_sum->real^1).
           p2cm_ctx V a b Gs FF ee c r sub H`,
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
  MAP_EVERY EXISTS_TAC [`FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`; `ee:num->real`;
                        `c:num->real^N`; `r:num->real`; `sub:num->num`;
                        `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`] THEN
  REWRITE_TAC[p2cm_ctx] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `p:num`; `q:num`; `l:num list`] THEN STRIP_TAC THEN
    USE_THEN "HH" (MP_TAC o C MP (ASSUME
      `ALL (\j. 1 <= j /\ j <= dimindex(:(1,N)finite_sum)) l`) o
      SPECL [`i:num`; `p:num`; `q:num`; `l:num list`]) THEN
    EXPAND_TAC "ok" THEN ASM_REWRITE_TAC[]);;

let P2CB_CTX_SEQHYP = prove
 (`!V a b (Gs:num->real->real^N->real^N^N).
     open V /\ a < b /\ p2ca_seqhyp V a b Gs
     ==> ?(FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod) ee c r (sub:num->num)
           (H:num#num#num->(num)list->real^(1,N)finite_sum->real^1).
           p2cm_ctx V a b Gs FF ee c r sub H`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2ca_seqhyp] THEN STRIP_TAC THEN
  MATCH_MP_TAC P2CB_CTX_EXISTS THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Uniqueness of lck limits at a point (P2CB_LCK_LIM_UNIQUE),                *)
(* entries of vectorized maps, the local extension data of a local limit    *)
(* from its context (P2CB_CTX_DATA), and the smooth extension past the      *)
(* initial time of a map that is near every point a local limit           *)
(* (P2CB_UPTO_CTX).                                                          *)
(* ------------------------------------------------------------------------- *)

let P2CB_QF_LIM = prove
 (`!S (G:real^N->real^N^N) (As:num->real^N->real^N^N) y N w.
     metric_field S G /\ y IN S /\ (!n. N <= n ==> metric_field S (As n)) /\
     (!e. &0 < e ==> ?M. !n. M <= n ==> lck_dist2 0 G (As n) y < e)
     ==> ((\n. w dot (As n y ** w)) ---> w dot (G y ** w)) sequentially`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CA_C0_LIM THEN
  MAP_EVERY EXISTS_TAC [`\n. lck_dist2 0 (G:real^N->real^N^N) ((As:num->real^N->real^N^N) n) y`;
                        `w dot ((G:real^N->real^N^N) y ** w)`; `N:num`] THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2CA_LCK_DIST2_POS THEN EXISTS_TAC `S:real^N->bool` THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC LCK_DIST_C0 THEN EXISTS_TAC `S:real^N->bool` THEN ASM_SIMP_TAC[]];
    UNDISCH_TAC `metric_field S (G:real^N->real^N^N)` THEN REWRITE_TAC[metric_field] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N` o CONJUNCT2 o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `w:real^N = vec 0` THEN ASM_REWRITE_TAC[DOT_LZERO; REAL_LE_REFL] THEN
    ASM_MESON_TAC[REAL_LT_IMP_LE]]);;

let P2CB_LCK_LIM_UNIQUE = prove
 (`!S (G1:real^N->real^N^N) G2 (As:num->real^N->real^N^N) y N.
     metric_field S G1 /\ metric_field S G2 /\ y IN S /\
     (!n. N <= n ==> metric_field S (As n)) /\
     (!e. &0 < e ==> ?M. !n. M <= n ==> lck_dist2 0 G1 (As n) y < e) /\
     (!e. &0 < e ==> ?M. !n. M <= n ==> lck_dist2 0 G2 (As n) y < e)
     ==> G1 y = G2 y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CMPH_SYM_QUAD_EQ THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `metric_field S (G1:real^N->real^N^N)` THEN REWRITE_TAC[metric_field] THEN
    ASM_SIMP_TAC[];
    UNDISCH_TAC `metric_field S (G2:real^N->real^N^N)` THEN REWRITE_TAC[metric_field] THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `w:real^N` THEN MATCH_MP_TAC(ISPEC `sequentially:(num)net` REALLIM_UNIQUE) THEN
    EXISTS_TAC `\n. w dot ((As:num->real^N->real^N^N) n y ** w)` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THEN
    MATCH_MP_TAC P2CB_QF_LIM THEN
    MAP_EVERY EXISTS_TAC [`S:real^N->bool`; `N:num`] THEN ASM_REWRITE_TAC[]]);;

let P2CB_VECTORIZE_CONTINUOUS = prove
 (`!(A:real^M->real^N^N) s.
     (!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
            ==> (\w. lift(A w$p$q)) continuous_on s)
     ==> (\w. vectorize(A w)) continuous_on s`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[CONTINUOUS_ON_COMPONENTWISE_LIFT] THEN
  X_GEN_TAC `k:num` THEN REWRITE_TAC[DIMINDEX_FINITE_PROD] THEN STRIP_TAC THEN
  MP_TAC(SPEC `k:num` (INST_TYPE [`:N`,`:N`] LRG_VECTORIZE_INDEX)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[VECTORIZE_COMPONENT; DIMINDEX_FINITE_PROD]);;

let P2CB_VEC_ENTRY_EQ = prove
 (`!(X:real^(N,N)finite_prod) Y.
     (!p q. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
            ==> (matrify X:real^N^N)$p$q = (matrify Y:real^N^N)$p$q)
     ==> X = Y`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM MATRIFY_EQ] THEN
  REWRITE_TAC[CART_EQ] THEN ASM_SIMP_TAC[]);;

let P2CB_ITERATED_PARTIAL_ENTRY = prove
 (`!l s (u:real^M->real^(N,N)finite_prod) w p q.
     open s /\ smooth_map_on s u /\ w IN s
     ==> (matrify(iterated_partial l u w):real^N^N)$p$q =
         drop(iterated_partial l (\z. lift((matrify(u z):real^N^N)$p$q)) w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:(num)list`;
                 `\x:real^(N,N)finite_prod. lift((matrify x:real^N^N)$p$q)`;
                 `u:real^M->real^(N,N)finite_prod`; `s:real^M->bool`; `w:real^M`]
                PDE_ITERATED_PARTIAL_LINEAR_COMPOSE) THEN
  ASM_REWRITE_TAC[LRG_LINEAR_MATRIFY_ENTRY] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[LIFT_DROP]);;

let P2CB_CTX_DATA = prove
 (`!V a b (Gs:num->real->real^N->real^N^N) FF ee c r sub H G y0.
     p2cm_ctx V a b Gs FF ee c r sub H /\
     (!t y. a <= t /\ t <= b /\ y IN V ==> G t y = p2cm_lim Gs sub t y) /\
     y0 IN V
     ==> ?O. open O /\ y0 IN O /\ O SUBSET V /\
             (\z. vectorize(G (drop(fstcart z)) (sndcart z))) continuous_on
               ({x | a <= drop x /\ drop x < b} PCROSS O) /\
             !l. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l
                 ==> ?h. h continuous_on ({x | a <= drop x /\ drop x < b} PCROSS O) /\
                         !w. w IN interval(lift a,lift b) PCROSS O
                             ==> h w = iterated_partial l
                                         (\z. vectorize(G (drop(fstcart z)) (sndcart z))) w`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ctx") (CONJUNCTS_THEN2 (LABEL_TAC "id") ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `open (V:real^N->bool) /\ a < b /\
    (!i. cball((c:num->real^N) i,(r:num->real) i) SUBSET V) /\
    (!y. y IN V ==> ?i. &0 < r i /\ y IN ball(c i,r i)) /\
    (!i p q l. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N) /\
               ALL (\j. 1 <= j /\ j <= dimindex(:(1,N)finite_sum)) l
               ==> (H:num#num#num->(num)list->real^(1,N)finite_sum->real^1) (i,p,q) l
                     continuous_on p2cm_box a b c r i)`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "ctx" (MP_TAC o REWRITE_RULE[p2cm_ctx]) THEN SIMP_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `(y0:real^N) IN V`) o SPEC `y0:real^N` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `ball:real^N#real->real^N->bool`)) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `ball((c:num->real^N) i,(r:num->real) i) SUBSET V` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball((c:num->real^N) i,(r:num->real) i)` THEN
    ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x | a <= drop x /\ drop x < b} PCROSS ball((c:num->real^N) i,(r:num->real) i) SUBSET
    p2cm_box a b c r i`
  ASSUME_TAC THENL
   [REWRITE_TAC[p2cm_box] THEN MATCH_MP_TAC PCROSS_MONO THEN
    REWRITE_TAC[BALL_SUBSET_CBALL; SUBSET; IN_INTERVAL_1; IN_ELIM_THM; LIFT_DROP] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p q w. 1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N) /\
            w IN {x | a <= drop x /\ drop x < b} PCROSS ball((c:num->real^N) i,(r:num->real) i)
            ==> lift((G:real->real^N->real^N^N) (drop(fstcart w)) (sndcart w)$p$q) =
                (H:num#num#num->(num)list->real^(1,N)finite_sum->real^1) (i,p,q) [] w`
  (LABEL_TAC "ent0") THENL
   [MAP_EVERY X_GEN_TAC [`p:num`; `q:num`; `w:real^(1,N)finite_sum`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `a <= drop(fstcart(w:real^(1,N)finite_sum)) /\ drop(fstcart w) < b /\
                  sndcart w IN ball((c:num->real^N) i,(r:num->real) i)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(w:real^(1,N)finite_sum) IN
                   {x | a <= drop x /\ drop x < b} PCROSS ball((c:num->real^N) i,(r:num->real) i)` THEN
      ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN
      REWRITE_TAC[PASTECART_IN_PCROSS; IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
      CONV_TAC TAUT;
      ALL_TAC] THEN
    SUBGOAL_THEN `sndcart(w:real^(1,N)finite_sum) IN V /\
                  sndcart w IN cball((c:num->real^N) i,(r:num->real) i)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[SUBSET; BALL_SUBSET_CBALL]];
      ALL_TAC] THEN
    USE_THEN "id" (MP_TAC o SPECL [`drop(fstcart(w:real^(1,N)finite_sum))`;
                                   `sndcart(w:real^(1,N)finite_sum)`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`V:real^N->bool`; `a:real`; `b:real`; `Gs:num->real->real^N->real^N^N`;
                   `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`; `ee:num->real`;
                   `c:num->real^N`; `r:num->real`; `sub:num->num`;
                   `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`;
                   `i:num`; `p:num`; `q:num`; `drop(fstcart(w:real^(1,N)finite_sum))`;
                   `sndcart(w:real^(1,N)finite_sum)`] P2CM_CTX_LIM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN REWRITE_TAC[LIFT_DROP; PASTECART_FST_SND];
    ALL_TAC] THEN
  EXISTS_TAC `ball((c:num->real^N) i,(r:num->real) i)` THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2CB_VECTORIZE_CONTINUOUS THEN REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN STRIP_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `(H:num#num#num->(num)list->real^(1,N)finite_sum->real^1) (i,p,q) []` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `w:real^(1,N)finite_sum` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      CONV_TAC SYM_CONV THEN USE_THEN "ent0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `p2cm_box a b (c:num->real^N) r i` THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ALL]];
    ALL_TAC] THEN
  X_GEN_TAC `l:(num)list` THEN DISCH_TAC THEN
  EXISTS_TAC `\w. (vectorize:real^N^N->real^(N,N)finite_prod)
                    (lambda p q. drop((H:num#num#num->(num)list->real^(1,N)finite_sum->real^1)
                                        (i,p,q) l w))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2CB_VECTORIZE_CONTINUOUS THEN
    MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[LAMBDA_BETA; LIFT_DROP; ETA_AX] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `p2cm_box a b (c:num->real^N) r i` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `w:real^(1,N)finite_sum` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `a:real`; `b:real`; `Gs:num->real->real^N->real^N^N`;
                 `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`; `ee:num->real`;
                 `c:num->real^N`; `r:num->real`; `sub:num->num`;
                 `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`] P2CM_CTX_FLOW) THEN
  USE_THEN "ctx" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[lricci_flow] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `open(interval(lift a,lift b) PCROSS ball((c:num->real^N) i,(r:num->real) i)) /\
    interval(lift a,lift b) PCROSS ball(c i,r i) SUBSET interval(lift a,lift b) PCROSS V`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_BALL] THEN MATCH_MP_TAC PCROSS_MONO THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `iterated_partial l (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                              ((G:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z))) w =
    iterated_partial l (\z. vectorize(p2cm_lim (Gs:num->real->real^N->real^N^N) sub
                                        (drop(fstcart z)) (sndcart z))) w`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`l:(num)list`;
                   `interval(lift a,lift b) PCROSS ball((c:num->real^N) i,(r:num->real) i)`;
                   `\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                          ((G:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z))`;
                   `\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                          (p2cm_lim (Gs:num->real->real^N->real^N^N) sub
                             (drop(fstcart z)) (sndcart z))`]
                  TEXT_ITERATED_PARTIAL_LOCAL_OPEN) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[FORALL_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN REPEAT STRIP_TAC THEN
    AP_TERM_TAC THEN USE_THEN "id" MATCH_MP_TAC THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `ball((c:num->real^N) i,(r:num->real) i) SUBSET V` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC P2CB_VEC_ENTRY_EQ THEN MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN STRIP_TAC THEN
  REWRITE_TAC[MATRIFY_VECTORIZE] THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN
  MP_TAC(ISPECL [`l:(num)list`;
                 `interval(lift a,lift b) PCROSS ball((c:num->real^N) i,(r:num->real) i)`;
                 `\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                        (p2cm_lim (Gs:num->real->real^N->real^N^N) sub
                           (drop(fstcart z)) (sndcart z))`;
                 `w:real^(1,N)finite_sum`; `p:num`; `q:num`] P2CB_ITERATED_PARTIAL_ENTRY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `interval(lift a,lift b) PCROSS (V:real^N->bool)` THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[MATRIFY_VECTORIZE] THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `a:real`; `b:real`; `Gs:num->real->real^N->real^N^N`;
                 `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`; `ee:num->real`;
                 `c:num->real^N`; `r:num->real`; `sub:num->num`;
                 `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`;
                 `i:num`; `p:num`; `q:num`] P2CM_CTX_REP) THEN
  USE_THEN "ctx" (fun th -> ASM_REWRITE_TAC[th]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Hl"))) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `iterated_partial l
                ((H:num#num#num->(num)list->real^(1,N)finite_sum->real^1) (i,p,q) []) w` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN USE_THEN "Hl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`l:(num)list`;
                   `interval(lift a,lift b) PCROSS ball((c:num->real^N) i,(r:num->real) i)`;
                   `\z. lift(p2cm_lim (Gs:num->real->real^N->real^N^N) sub
                               (drop(fstcart z)) (sndcart z)$p$q)`;
                   `(H:num#num#num->(num)list->real^(1,N)finite_sum->real^1) (i,p,q) []`]
                  TEXT_ITERATED_PARTIAL_LOCAL_OPEN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `w:real^(1,N)finite_sum`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o SYM)]);;

let P2CB_UPTO_CTX = prove
 (`!a b (U:real^N->bool) (G:real->real^N->real^N^N).
     open U /\ a < b /\
     smooth_map_on (interval(lift a,lift b) PCROSS U)
                   (\z. vectorize(G (drop(fstcart z)) (sndcart z))) /\
     (!y0. y0 IN U
           ==> ?V (Gs:num->real->real^N->real^N^N)
                 (FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod) ee c r (sub:num->num)
                 (H:num#num#num->(num)list->real^(1,N)finite_sum->real^1).
                 y0 IN V /\ V SUBSET U /\ p2cm_ctx V a b Gs FF ee c r sub H /\
                 (!t y. a <= t /\ t <= b /\ y IN V ==> G t y = p2cm_lim Gs sub t y))
     ==> pde_upto a b U (\t y. vectorize(G t y))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "loc")))) THEN
  MATCH_MP_TAC P2CB_UPTO THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y0:real^N` THEN DISCH_TAC THEN
  USE_THEN "loc" (MP_TAC o C MP (ASSUME `(y0:real^N) IN U`) o SPEC `y0:real^N`) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`V:real^N->bool`; `Gs:num->real->real^N->real^N^N`;
                       `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`; `ee:num->real`;
                       `c:num->real^N`; `r:num->real`; `sub:num->num`;
                       `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `a:real`; `b:real`; `Gs:num->real->real^N->real^N^N`;
                 `FF:num->real^(1,N)finite_sum->real^(N,N)finite_prod`; `ee:num->real`;
                 `c:num->real^N`; `r:num->real`; `sub:num->num`;
                 `H:num#num#num->(num)list->real^(1,N)finite_sum->real^1`;
                 `G:real->real^N->real^N^N`; `y0:real^N`] P2CB_CTX_DATA) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `O:real^N->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

