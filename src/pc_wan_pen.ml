(* ========================================================================= *)
(* pc_wan_pen: the classical linear parabolic equation on space-time         *)
(* real^(N,1)finite_sum (spatial directions basis 1..N, time basis (N + 1))  *)
(* in divergence form,                                                       *)
(*   d_t v = sum_i d_i (sum_j a_ij d_j v + g_i) + sum_i b_i d_i v + c v + f, *)
(* and its level-0 energy estimate for smooth v with compact support.        *)
(*   - definitions, supports, integration by parts;                          *)
(*   - the energy identity and WAN_ENERGY0;                                  *)
(*   - the differentiated equation and linearity;                            *)
(*   - the weak form on the whole space and the weak identity of classical   *)
(*     solutions.                                                            *)
(* ========================================================================= *)

needs "src/pc_wan_moll.ml";;

prioritize_real();;
type_invention_error := true;;

let wan_ceq = new_definition
 `wan_ceq (a:real^(N,1)finite_sum->real^N^N) (b:real^(N,1)finite_sum->real^N)
          (c:real^(N,1)finite_sum->real) (f:real^(N,1)finite_sum->real^1)
          (g:num->real^(N,1)finite_sum->real^1) (v:real^(N,1)finite_sum->real^1) <=>
    !z. partial_derivative (dimindex(:N) + 1) v z =
        vsum(1..dimindex(:N))
          (\i. partial_derivative i
                 (\w. vsum(1..dimindex(:N)) (\j. a w$i$j % partial_derivative j v w) +
                      g i w) z) +
        vsum(1..dimindex(:N)) (\i. b z$i % partial_derivative i v z) +
        c z % v z + f z`;;

(* ------------------------------------------------------------------------- *)
(* Supports and integrals of derivatives of compactly supported smooth maps. *)
(* ------------------------------------------------------------------------- *)

let WAN_PEN_DSUPPORT = prove
 (`!(v:real^M->real^K) k l z.
     compact k /\ smooth_map_on (:real^M) v /\ (!z. ~(z IN k) ==> v z = vec 0) /\
     ~(z IN k)
     ==> iterated_partial l v z = vec 0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TEXT_ITERATED_PARTIAL_ZERO_OPEN THEN
  EXISTS_TAC `(:real^M) DIFF k` THEN
  ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED; IN_DIFF; IN_UNIV]);;

let WAN_PEN_PSUPPORT = prove
 (`!(v:real^M->real^K) k i z.
     compact k /\ smooth_map_on (:real^M) v /\ (!z. ~(z IN k) ==> v z = vec 0) /\
     ~(z IN k)
     ==> partial_derivative i v z = vec 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`v:real^M->real^K`; `k:real^M->bool`; `[i:num]`; `z:real^M`]
                WAN_PEN_DSUPPORT) THEN
  ASM_REWRITE_TAC[iterated_partial]);;

let WAN_PEN_INTEGRAL_PARTIAL = prove
 (`!(hh:real^M->real^K) k i.
     compact k /\ smooth_map_on (:real^M) hh /\ (!z. ~(z IN k) ==> hh z = vec 0)
     ==> integral (:real^M) (\z. partial_derivative i hh z) = vec 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[partial_derivative] THEN
  MATCH_MP_TAC INTEGRAL_UNIQUE THEN MATCH_MP_TAC WAN_INTEGRAL_DIRDERIV_ZERO THEN
  EXISTS_TAC `k:real^M->bool` THEN ASM_REWRITE_TAC[]);;

let WAN_PEN_SMOOTH_PARTIAL = prove
 (`!(v:real^M->real^K) i.
     smooth_map_on (:real^M) v ==> smooth_map_on (:real^M) (partial_derivative i v)`,
  SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; OPEN_UNIV]);;

let WAN_PEN_SMOOTH_DROPMUL = prove
 (`!(u:real^M->real^1) (h:real^M->real^K).
     smooth_map_on (:real^M) u /\ smooth_map_on (:real^M) h
     ==> smooth_map_on (:real^M) (\z. drop(u z) % h z)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN
  ASM_REWRITE_TAC[OPEN_UNIV]);;

let WAN_PEN_IBP = prove
 (`!(v:real^M->real^1) (h:real^M->real^1) k i.
     compact k /\ smooth_map_on (:real^M) v /\ (!z. ~(z IN k) ==> v z = vec 0) /\
     smooth_map_on (:real^M) h
     ==> integral (:real^M) (\z. drop(v z) % partial_derivative i h z) =
         --(integral (:real^M) (\z. drop(h z) % partial_derivative i v z))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z:real^M. drop((v:real^M->real^1) z) % (h:real^M->real^1) z`;
                 `k:real^M->bool`; `i:num`] WAN_PEN_INTEGRAL_PARTIAL) THEN
  ASM_SIMP_TAC[WAN_PEN_SMOOTH_DROPMUL; DROP_VEC; VECTOR_MUL_LZERO] THEN
  SUBGOAL_THEN
   `!z. partial_derivative i (\z:real^M. drop((v:real^M->real^1) z) % (h:real^M->real^1) z) z =
        drop(v z) % partial_derivative i h z + drop(h z) % partial_derivative i v z`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) PARTIAL_DERIVATIVE_MUL o lhand o snd) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `(:real^M)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[GSYM DROP_EQ; DROP_ADD; DROP_CMUL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. ~(z IN k) ==> partial_derivative i (v:real^M->real^1) z = vec 0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_PEN_PSUPPORT THEN
    EXISTS_TAC `k:real^M->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. drop((v:real^M->real^1) z) % partial_derivative i (h:real^M->real^1) z)
      integrable_on (:real^M) /\
    (\z. drop((h:real^M->real^1) z) % partial_derivative i (v:real^M->real^1) z)
      integrable_on (:real^M)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC WAN_CONT_SUPPORT_INTEGRABLE THEN
    EXISTS_TAC `k:real^M->bool` THEN
    ASM_SIMP_TAC[DROP_VEC; VECTOR_MUL_LZERO; VECTOR_MUL_RZERO] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN MATCH_MP_TAC WAN_PEN_SMOOTH_DROPMUL THEN
    ASM_SIMP_TAC[WAN_PEN_SMOOTH_PARTIAL; ETA_AX];
    ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGRAL_ADD] THEN VECTOR_ARITH_TAC);;

let WAN_PEN_INT_SELF = prove
 (`!(v:real^M->real^1) k i.
     compact k /\ smooth_map_on (:real^M) v /\ (!z. ~(z IN k) ==> v z = vec 0)
     ==> integral (:real^M) (\z. drop(v z) % partial_derivative i v z) = vec 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`v:real^M->real^1`; `v:real^M->real^1`; `k:real^M->bool`; `i:num`]
                WAN_PEN_IBP) THEN
  ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC);;

(* ========================================================================= *)
(* The energy identity and the level-0 energy estimate.                     *)
(* ========================================================================= *)

let WAN_PEN_CCS_INTEGRABLE = prove
 (`!(ff:real^M->real) k.
     (\z. lift(ff z)) continuous_on (:real^M) /\ compact k /\
     (!z. ~(z IN k) ==> ff z = &0)
     ==> (\z. lift(ff z)) integrable_on (:real^M)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_CONT_SUPPORT_INTEGRABLE THEN
  EXISTS_TAC `k:real^M->bool` THEN ASM_SIMP_TAC[LIFT_NUM]);;

let WAN_PEN_RINT_SUM = prove
 (`!(ff:num->real^M->real) s.
     FINITE s /\ (!i. i IN s ==> (\z. lift(ff i z)) integrable_on (:real^M))
     ==> drop(integral (:real^M) (\z. lift(sum s (\i. ff i z)))) =
         sum s (\i. drop(integral (:real^M) (\z. lift(ff i z))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_SUM; o_DEF] THEN
  ASM_SIMP_TAC[INTEGRAL_VSUM; DROP_VSUM; o_DEF]);;

let WAN_PEN_RINT_ADD = prove
 (`!(ff:real^M->real) gg.
     (\z. lift(ff z)) integrable_on (:real^M) /\ (\z. lift(gg z)) integrable_on (:real^M)
     ==> drop(integral (:real^M) (\z. lift(ff z + gg z))) =
         drop(integral (:real^M) (\z. lift(ff z))) + drop(integral (:real^M) (\z. lift(gg z)))`,
  SIMP_TAC[LIFT_ADD; INTEGRAL_ADD; DROP_ADD]);;

let WAN_PEN_RINT_SUB = prove
 (`!(ff:real^M->real) gg.
     (\z. lift(ff z)) integrable_on (:real^M) /\ (\z. lift(gg z)) integrable_on (:real^M)
     ==> drop(integral (:real^M) (\z. lift(ff z - gg z))) =
         drop(integral (:real^M) (\z. lift(ff z))) - drop(integral (:real^M) (\z. lift(gg z)))`,
  SIMP_TAC[LIFT_SUB; INTEGRAL_SUB; DROP_SUB]);;

let WAN_PEN_CONT_DROP = prove
 (`!(u:real^M->real^1). u continuous_on (:real^M)
                        ==> (\z. lift(drop(u z))) continuous_on (:real^M)`,
  REWRITE_TAC[LIFT_DROP; ETA_AX]);;

let WAN_PEN_CONT_SUM = prove
 (`!(ff:num->real^M->real) s.
     FINITE s /\ (!i. i IN s ==> (\z. lift(ff i z)) continuous_on (:real^M))
     ==> (\z. lift(sum s (\i. ff i z))) continuous_on (:real^M)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_SUM; o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN ASM_REWRITE_TAC[]);;

let WAN_PEN_CONT_ADD = prove
 (`!(ff:real^M->real) gg.
     (\z. lift(ff z)) continuous_on (:real^M) /\ (\z. lift(gg z)) continuous_on (:real^M)
     ==> (\z. lift(ff z + gg z)) continuous_on (:real^M)`,
  SIMP_TAC[LIFT_ADD; CONTINUOUS_ON_ADD]);;

let WAN_PEN_CONT_SUB = prove
 (`!(ff:real^M->real) gg.
     (\z. lift(ff z)) continuous_on (:real^M) /\ (\z. lift(gg z)) continuous_on (:real^M)
     ==> (\z. lift(ff z - gg z)) continuous_on (:real^M)`,
  SIMP_TAC[LIFT_SUB; CONTINUOUS_ON_SUB]);;

let WAN_PEN_IDENTITY = prove
 (`!(a:real^(N,1)finite_sum->real^N^N) b c f g (v:real^(N,1)finite_sum->real^1) k.
     compact k /\ smooth_map_on (:real^(N,1)finite_sum) v /\
     (!z. ~(z IN k) ==> v z = vec 0) /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> smooth_map_on (:real^(N,1)finite_sum) (\w. lift(a w$i$j))) /\
     (!i. 1 <= i /\ i <= dimindex(:N)
          ==> (\w. lift(b w$i)) continuous_on (:real^(N,1)finite_sum)) /\
     (\w. lift(c w)) continuous_on (:real^(N,1)finite_sum) /\
     f continuous_on (:real^(N,1)finite_sum) /\
     (!i. 1 <= i /\ i <= dimindex(:N) ==> smooth_map_on (:real^(N,1)finite_sum) (g i)) /\
     wan_ceq a b c f g v
     ==> drop(integral (:real^(N,1)finite_sum)
               (\z. lift(sum(1..dimindex(:N))
                      (\i. sum(1..dimindex(:N))
                             (\j. a z$i$j * drop(partial_derivative i v z) *
                                  drop(partial_derivative j v z)))))) =
         drop(integral (:real^(N,1)finite_sum)
               (\z. lift(sum(1..dimindex(:N))
                           (\i. b z$i * drop(v z) * drop(partial_derivative i v z) -
                                drop(g i z) * drop(partial_derivative i v z)) +
                         c z * drop(v z) pow 2 + drop(v z) * drop(f z))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC
   `H = \i (w:real^(N,1)finite_sum).
          vsum(1..dimindex(:N))
            (\j. (a:real^(N,1)finite_sum->real^N^N) w$i$j %
                 partial_derivative j (v:real^(N,1)finite_sum->real^1) w) +
          (g:num->real^(N,1)finite_sum->real^1) i w` THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> smooth_map_on (:real^(N,1)finite_sum) ((H:num->real^(N,1)finite_sum->real^1) i)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "H" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_SIMP_TAC[OPEN_UNIV; ETA_AX] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN REWRITE_TAC[OPEN_UNIV; FINITE_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN REWRITE_TAC[IN_NUMSEG] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(\w. (a:real^(N,1)finite_sum->real^N^N) w$i$j %
           partial_derivative j (v:real^(N,1)finite_sum->real^1) w) =
      (\w. drop(lift(a w$i$j)) % partial_derivative j v w)`
    SUBST1_TAC THENL [REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC WAN_PEN_SMOOTH_DROPMUL THEN
    ASM_SIMP_TAC[WAN_PEN_SMOOTH_PARTIAL; ETA_AX];
    ALL_TAC] THEN
  ABBREV_TAC `u = \z. drop((v:real^(N,1)finite_sum->real^1) z)` THEN
  ABBREV_TAC `p = \i z. drop(partial_derivative i (v:real^(N,1)finite_sum->real^1) z)` THEN
  SUBGOAL_THEN
   `(\z. lift((u:real^(N,1)finite_sum->real) z)) continuous_on (:real^(N,1)finite_sum) /\
    (!i. (\z. lift((p:num->real^(N,1)finite_sum->real) i z)) continuous_on
         (:real^(N,1)finite_sum)) /\
    (!z. ~(z IN k) ==> u z = &0) /\ (!i z. ~(z IN k) ==> p i z = &0)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["u"; "p"] THEN REWRITE_TAC[LIFT_DROP; ETA_AX] THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
      GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      ASM_SIMP_TAC[WAN_PEN_SMOOTH_PARTIAL];
      ASM_SIMP_TAC[DROP_VEC];
      REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`v:real^(N,1)finite_sum->real^1`; `k:real^(N,1)finite_sum->bool`;
                     `i:num`; `z:real^(N,1)finite_sum`] WAN_PEN_PSUPPORT) THEN
      ASM_SIMP_TAC[DROP_VEC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!z. drop((v:real^(N,1)finite_sum->real^1) z) = (u:real^(N,1)finite_sum->real) z) /\
    (!i z. drop(partial_derivative i (v:real^(N,1)finite_sum->real^1) z) =
           (p:num->real^(N,1)finite_sum->real) i z)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["u"; "p"] THEN REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!z. (p:num->real^(N,1)finite_sum->real) (dimindex(:N) + 1) z =
        sum(1..dimindex(:N)) (\i. drop(partial_derivative i ((H:num->real^(N,1)finite_sum->real^1) i) z)) +
        sum(1..dimindex(:N)) (\i. (b:real^(N,1)finite_sum->real^N) z$i * p i z) +
        (c:real^(N,1)finite_sum->real) z * (u:real^(N,1)finite_sum->real) z +
        drop((f:real^(N,1)finite_sum->real^1) z)`
  (LABEL_TAC "eq") THENL
   [GEN_TAC THEN MAP_EVERY EXPAND_TAC ["u"; "p"] THEN
    UNDISCH_TAC `wan_ceq (a:real^(N,1)finite_sum->real^N^N) b c f g v` THEN
    REWRITE_TAC[wan_ceq] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    EXPAND_TAC "H" THEN
    REWRITE_TAC[DROP_ADD; DROP_VSUM; o_DEF; DROP_CMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> (\z. lift(drop((H:num->real^(N,1)finite_sum->real^1) i z))) continuous_on
              (:real^(N,1)finite_sum) /\
            (\z. lift(drop(partial_derivative i (H i) z))) continuous_on
              (:real^(N,1)finite_sum) /\
            (\z. lift(drop((g:num->real^(N,1)finite_sum->real^1) i z))) continuous_on
              (:real^(N,1)finite_sum) /\
            (\z. lift((b:real^(N,1)finite_sum->real^N) z$i)) continuous_on
              (:real^(N,1)finite_sum)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_DROP; ETA_AX] THEN ASM_SIMP_TAC[] THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    ASM_SIMP_TAC[WAN_PEN_SMOOTH_PARTIAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
          ==> (\z. lift((a:real^(N,1)finite_sum->real^N^N) z$i$j)) continuous_on
                (:real^(N,1)finite_sum)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. lift(drop((f:real^(N,1)finite_sum->real^1) z))) continuous_on
      (:real^(N,1)finite_sum)`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[LIFT_DROP; ETA_AX]; ALL_TAC] THEN
  SUBGOAL_THEN
   `drop(integral (:real^(N,1)finite_sum)
           (\z. lift((u:real^(N,1)finite_sum->real) z *
                     (p:num->real^(N,1)finite_sum->real) (dimindex(:N) + 1) z))) = &0`
  (LABEL_TAC "a0") THENL
   [SUBGOAL_THEN
     `(\z. lift((u:real^(N,1)finite_sum->real) z *
                (p:num->real^(N,1)finite_sum->real) (dimindex(:N) + 1) z)) =
      (\z. drop((v:real^(N,1)finite_sum->real^1) z) %
           partial_derivative (dimindex(:N) + 1) v z)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; GSYM DROP_EQ; DROP_CMUL; LIFT_DROP] THEN
      MAP_EVERY EXPAND_TAC ["u"; "p"] THEN REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`v:real^(N,1)finite_sum->real^1`; `k:real^(N,1)finite_sum->bool`;
                   `dimindex(:N) + 1`] WAN_PEN_INT_SELF) THEN
    ASM_SIMP_TAC[DROP_VEC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> drop(integral (:real^(N,1)finite_sum)
                   (\z. lift((u:real^(N,1)finite_sum->real) z *
                             drop(partial_derivative i
                                    ((H:num->real^(N,1)finite_sum->real^1) i) z)))) =
            --drop(integral (:real^(N,1)finite_sum)
                     (\z. lift(drop(H i z) * (p:num->real^(N,1)finite_sum->real) i z)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `(\z. lift((u:real^(N,1)finite_sum->real) z *
                drop(partial_derivative i ((H:num->real^(N,1)finite_sum->real^1) i) z))) =
      (\z. drop((v:real^(N,1)finite_sum->real^1) z) % partial_derivative i (H i) z) /\
      (\z. lift(drop(H i z) * (p:num->real^(N,1)finite_sum->real) i z)) =
      (\z. drop(H i z) % partial_derivative i v z)`
    (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[FUN_EQ_THM; GSYM DROP_EQ; DROP_CMUL; LIFT_DROP] THEN
      MAP_EVERY EXPAND_TAC ["u"; "p"] THEN REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`v:real^(N,1)finite_sum->real^1`;
                   `(H:num->real^(N,1)finite_sum->real^1) i`;
                   `k:real^(N,1)finite_sum->bool`; `i:num`] WAN_PEN_IBP) THEN
    ASM_SIMP_TAC[DROP_NEG];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. (u:real^(N,1)finite_sum->real) z * (p:num->real^(N,1)finite_sum->real) (dimindex(:N) + 1) z =
        sum(1..dimindex(:N))
          (\i. u z * drop(partial_derivative i ((H:num->real^(N,1)finite_sum->real^1) i) z)) +
        (sum(1..dimindex(:N)) (\i. (b:real^(N,1)finite_sum->real^N) z$i * u z * p i z) +
         (c:real^(N,1)finite_sum->real) z * u z pow 2 +
         u z * drop((f:real^(N,1)finite_sum->real^1) z))`
  ASSUME_TAC THENL
   [GEN_TAC THEN USE_THEN "eq" (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN
     `sum(1..dimindex(:N)) (\i. (b:real^(N,1)finite_sum->real^N) z$i *
                                (u:real^(N,1)finite_sum->real) z *
                                (p:num->real^(N,1)finite_sum->real) i z) =
      u z * sum(1..dimindex(:N)) (\i. b z$i * p i z)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[SUM_LMUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. sum(1..dimindex(:N))
          (\i. drop((H:num->real^(N,1)finite_sum->real^1) i z) *
               (p:num->real^(N,1)finite_sum->real) i z) =
        sum(1..dimindex(:N))
          (\i. sum(1..dimindex(:N))
                 (\j. (a:real^(N,1)finite_sum->real^N^N) z$i$j * p i z * p j z)) +
        sum(1..dimindex(:N)) (\i. drop((g:num->real^(N,1)finite_sum->real^1) i z) * p i z)`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN EXPAND_TAC "H" THEN
    REWRITE_TAC[DROP_ADD; DROP_VSUM; o_DEF; DROP_CMUL] THEN
    MAP_EVERY EXPAND_TAC ["p"] THEN
    REWRITE_TAC[REAL_ADD_RDISTRIB; GSYM SUM_RMUL] THEN
    MATCH_MP_TAC(REAL_ARITH `x = y ==> x + z = y + z`) THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!ff:real^(N,1)finite_sum->real.
      (\z. lift(ff z)) continuous_on (:real^(N,1)finite_sum) /\
      (!z. ~(z IN k) ==> ff z = &0)
      ==> (\z. lift(ff z)) integrable_on (:real^(N,1)finite_sum)`
  (LABEL_TAC "ccs") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_PEN_CCS_INTEGRABLE THEN
    EXISTS_TAC `k:real^(N,1)finite_sum->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!i. 1 <= i /\ i <= dimindex(:N)
         ==> (\z. lift((u:real^(N,1)finite_sum->real) z *
                       drop(partial_derivative i ((H:num->real^(N,1)finite_sum->real^1) i) z)))
               integrable_on (:real^(N,1)finite_sum) /\
             (\z. lift(drop(H i z) * (p:num->real^(N,1)finite_sum->real) i z))
               integrable_on (:real^(N,1)finite_sum)) /\
    (\z. lift(sum(1..dimindex(:N)) (\i. u z * drop(partial_derivative i (H i) z))))
      integrable_on (:real^(N,1)finite_sum) /\
    (\z. lift(sum(1..dimindex(:N)) (\i. (b:real^(N,1)finite_sum->real^N) z$i * u z * p i z) +
              (c:real^(N,1)finite_sum->real) z * u z pow 2 +
              u z * drop((f:real^(N,1)finite_sum->real^1) z)))
      integrable_on (:real^(N,1)finite_sum) /\
    (\z. lift(sum(1..dimindex(:N))
               (\i. sum(1..dimindex(:N))
                      (\j. (a:real^(N,1)finite_sum->real^N^N) z$i$j * p i z * p j z))))
      integrable_on (:real^(N,1)finite_sum) /\
    (\z. lift(sum(1..dimindex(:N)) (\i. drop((g:num->real^(N,1)finite_sum->real^1) i z) * p i z)))
      integrable_on (:real^(N,1)finite_sum)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(GEN_TAC THEN DISCH_TAC THEN CONJ_TAC) THEN
    USE_THEN "ccs" MATCH_MP_TAC THEN CONJ_TAC THEN
    TRY(REPEAT STRIP_TAC THEN
        ASM_SIMP_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; SUM_0; REAL_ADD_LID; REAL_POW_2;
                     REAL_SUB_REFL] THEN NO_TAC) THEN
    REPEAT(FIRST
     [MATCH_MP_TAC WAN_PEN_CONT_ADD THEN CONJ_TAC;
      MATCH_MP_TAC WAN_PEN_CONT_SUB THEN CONJ_TAC;
      MATCH_MP_TAC WAN_PEN_CONT_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
        GEN_TAC THEN DISCH_TAC;
      MATCH_MP_TAC WAN_CONT_LIFT_MUL THEN CONJ_TAC;
      REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC WAN_CONT_LIFT_MUL THEN CONJ_TAC]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `drop(integral (:real^(N,1)finite_sum)
           (\z. lift(sum(1..dimindex(:N))
                   (\i. drop((H:num->real^(N,1)finite_sum->real^1) i z) *
                        (p:num->real^(N,1)finite_sum->real) i z)))) =
    drop(integral (:real^(N,1)finite_sum)
           (\z. lift(sum(1..dimindex(:N))
                   (\i. sum(1..dimindex(:N))
                          (\j. (a:real^(N,1)finite_sum->real^N^N) z$i$j * p i z * p j z))))) +
    drop(integral (:real^(N,1)finite_sum)
           (\z. lift(sum(1..dimindex(:N))
                       (\i. drop((g:num->real^(N,1)finite_sum->real^1) i z) * p i z))))`
  (LABEL_TAC "a3") THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC WAN_PEN_RINT_ADD THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `drop(integral (:real^(N,1)finite_sum)
           (\z. lift(sum(1..dimindex(:N))
                       (\i. (b:real^(N,1)finite_sum->real^N) z$i *
                            (u:real^(N,1)finite_sum->real) z *
                            (p:num->real^(N,1)finite_sum->real) i z -
                            drop((g:num->real^(N,1)finite_sum->real^1) i z) * p i z) +
                     (c:real^(N,1)finite_sum->real) z * u z pow 2 +
                     u z * drop((f:real^(N,1)finite_sum->real^1) z)))) =
    drop(integral (:real^(N,1)finite_sum)
           (\z. lift(sum(1..dimindex(:N)) (\i. b z$i * u z * p i z) +
                     c z * u z pow 2 + u z * drop(f z)))) -
    drop(integral (:real^(N,1)finite_sum)
           (\z. lift(sum(1..dimindex(:N)) (\i. drop(g i z) * p i z))))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM WAN_PEN_RINT_SUB] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[SUM_SUB_NUMSEG] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. lift((u:real^(N,1)finite_sum->real) z *
              (p:num->real^(N,1)finite_sum->real) (dimindex(:N) + 1) z)) =
    (\z. lift(sum(1..dimindex(:N))
               (\i. u z * drop(partial_derivative i
                              ((H:num->real^(N,1)finite_sum->real^1) i) z)) +
              (sum(1..dimindex(:N)) (\i. (b:real^(N,1)finite_sum->real^N) z$i * u z * p i z) +
               (c:real^(N,1)finite_sum->real) z * u z pow 2 +
               u z * drop((f:real^(N,1)finite_sum->real^1) z))))`
  (LABEL_TAC "sp") THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `drop(integral (:real^(N,1)finite_sum)
           (\z. lift(sum(1..dimindex(:N))
                       (\i. (u:real^(N,1)finite_sum->real) z *
                            drop(partial_derivative i
                                   ((H:num->real^(N,1)finite_sum->real^1) i) z)) +
                     (sum(1..dimindex(:N))
                        (\i. (b:real^(N,1)finite_sum->real^N) z$i * u z *
                             (p:num->real^(N,1)finite_sum->real) i z) +
                      (c:real^(N,1)finite_sum->real) z * u z pow 2 +
                      u z * drop((f:real^(N,1)finite_sum->real^1) z))))) =
    drop(integral (:real^(N,1)finite_sum)
           (\z. lift(sum(1..dimindex(:N))
                       (\i. u z * drop(partial_derivative i (H i) z))))) +
    drop(integral (:real^(N,1)finite_sum)
           (\z. lift(sum(1..dimindex(:N)) (\i. b z$i * u z * p i z) +
                     c z * u z pow 2 + u z * drop(f z))))`
  (LABEL_TAC "s1") THENL
   [MATCH_MP_TAC WAN_PEN_RINT_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `drop(integral (:real^(N,1)finite_sum)
           (\z. lift(sum(1..dimindex(:N))
                       (\i. (u:real^(N,1)finite_sum->real) z *
                            drop(partial_derivative i
                                   ((H:num->real^(N,1)finite_sum->real^1) i) z))))) =
    sum(1..dimindex(:N))
      (\i. drop(integral (:real^(N,1)finite_sum)
                  (\z. lift(u z * drop(partial_derivative i (H i) z)))))`
  (LABEL_TAC "s2") THENL
   [MATCH_MP_TAC WAN_PEN_RINT_SUM THEN ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N))
      (\i. drop(integral (:real^(N,1)finite_sum)
                  (\z. lift((u:real^(N,1)finite_sum->real) z *
                            drop(partial_derivative i
                                   ((H:num->real^(N,1)finite_sum->real^1) i) z))))) =
    --drop(integral (:real^(N,1)finite_sum)
             (\z. lift(sum(1..dimindex(:N))
                     (\i. drop(H i z) * (p:num->real^(N,1)finite_sum->real) i z))))`
  (LABEL_TAC "s3") THENL
   [MP_TAC(ISPECL [`\i z. drop((H:num->real^(N,1)finite_sum->real^1) i z) *
                         (p:num->real^(N,1)finite_sum->real) i z`;
                   `1..dimindex(:N)`] WAN_PEN_RINT_SUM) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o BETA_RULE) THEN
    REWRITE_TAC[GSYM SUM_NEG] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "a0" MP_TAC THEN
  USE_THEN "sp" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "s1" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "s2" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "s3" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "a3" (fun th -> REWRITE_TAC[th]) THEN
  REAL_ARITH_TAC);;

let WAN_AMGM = prove
 (`!e x y. &0 < e ==> x * y <= e / &4 * x pow 2 + inv(e) * y pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`e / &4`; `(x - &2 * y / e) pow 2`] REAL_LE_MUL) THEN
  ANTS_TAC THENL [REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `e / &4 * x pow 2 + inv(e) * y pow 2 - x * y =
                e / &4 * (x - &2 * y / e) pow 2` MP_TAC THENL
   [UNDISCH_TAC `&0 < e` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let WAN_PEN_ELLIPTIC_POINT = prove
 (`!lam (A:real^N^N) (p:num->real).
     (!xi. lam * norm xi pow 2 <= xi dot (A ** xi))
     ==> lam * sum(1..dimindex(:N)) (\i. p i pow 2) <=
         sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j. A$i$j * p i * p j))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(lambda i. p i):real^N`) THEN
  MATCH_MP_TAC(REAL_ARITH `a = a' /\ b = b' ==> a <= b ==> a' <= b'`) THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[NORM_POW_2; dot] THEN
    SIMP_TAC[LAMBDA_BETA; REAL_POW_2] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    SIMP_TAC[LAMBDA_BETA];
    REWRITE_TAC[dot] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN
    STRIP_TAC THEN
    ASM_SIMP_TAC[LAMBDA_BETA; MATRIX_VECTOR_MUL_COMPONENT; dot; GSYM SUM_LMUL] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC]);;

let WAN_PEN_RBOUND = prove
 (`!lam Kb Kc (bz:real^N) cz u (p:num->real) (q:num->real) phi.
     &0 < lam /\ (!i. 1 <= i /\ i <= dimindex(:N) ==> abs(bz$i) <= Kb) /\ abs(cz) <= Kc
     ==> sum(1..dimindex(:N)) (\i. bz$i * u * p i - q i * p i) + cz * u pow 2 + u * phi
         <= lam / &2 * sum(1..dimindex(:N)) (\i. p i pow 2) +
            (&(dimindex(:N)) * Kb pow 2 / lam + Kc + &1 / &2) * u pow 2 +
            &1 / &2 * phi pow 2 + inv lam * sum(1..dimindex(:N)) (\i. q i pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> (bz:real^N)$i * u * p i - q i * p i <=
            lam / &2 * p i pow 2 + Kb pow 2 / lam * u pow 2 + inv lam * q i pow 2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`lam:real`; `(p:num->real) i`; `(bz:real^N)$i * u`] WAN_AMGM) THEN
    MP_TAC(ISPECL [`lam:real`; `(p:num->real) i`; `--((q:num->real) i)`] WAN_AMGM) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `((bz:real^N)$i * u) pow 2 <= Kb pow 2 * u pow 2` MP_TAC THENL
     [REWRITE_TAC[REAL_POW_MUL] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      REWRITE_TAC[REAL_LE_POW_2] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW2_ABS] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_ABS_POS];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < inv lam` MP_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_NEG; ARITH; real_div] THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `inv lam * ((bz:real^N)$i * u) pow 2 <= inv lam * (Kb pow 2 * u pow 2)`
    MP_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N)) (\i. (bz:real^N)$i * u * p i - q i * p i) <=
    lam / &2 * sum(1..dimindex(:N)) (\i. p i pow 2) +
    &(dimindex(:N)) * Kb pow 2 / lam * u pow 2 +
    inv lam * sum(1..dimindex(:N)) (\i. q i pow 2)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:N))
                  (\i. lam / &2 * p i pow 2 + Kb pow 2 / lam * u pow 2 +
                       inv lam * (q:num->real) i pow 2)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC SUM_LE_NUMSEG THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUM_ADD_NUMSEG; SUM_LMUL; SUM_CONST_NUMSEG; ADD_SUB] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`&2`; `u:real`; `phi:real`] WAN_AMGM) THEN
  SUBGOAL_THEN `cz * u pow 2 <= Kc * u pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

let WAN_INTEGRAL_ADD4 = prove
 (`!(h1:real^M->real^K) h2 h3 h4 s.
     h1 integrable_on s /\ h2 integrable_on s /\ h3 integrable_on s /\ h4 integrable_on s
     ==> (\z. h1 z + h2 z + h3 z + h4 z) integrable_on s /\
         integral s (\z. h1 z + h2 z + h3 z + h4 z) =
         integral s h1 + integral s h2 + integral s h3 + integral s h4`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\z. (h3:real^M->real^K) z + h4 z) integrable_on s` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(\z. (h2:real^M->real^K) z + h3 z + h4 z) integrable_on s` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGRAL_ADD]);;

let WAN_RCONT_TAC =
  REPEAT(FIRST
   [MATCH_MP_TAC WAN_PEN_CONT_ADD THEN CONJ_TAC;
    MATCH_MP_TAC WAN_PEN_CONT_SUB THEN CONJ_TAC;
    MATCH_MP_TAC WAN_PEN_CONT_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      GEN_TAC THEN DISCH_TAC;
    MATCH_MP_TAC WAN_CONT_LIFT_MUL THEN CONJ_TAC;
    REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC WAN_CONT_LIFT_MUL THEN CONJ_TAC]) THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_CONST];;

let WAN_ENERGY0 = prove
 (`!lam Kb Kc (a:real^(N,1)finite_sum->real^N^N) b c.
     &0 < lam /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> smooth_map_on (:real^(N,1)finite_sum) (\w. lift(a w$i$j))) /\
     (!i. 1 <= i /\ i <= dimindex(:N)
          ==> (\w. lift(b w$i)) continuous_on (:real^(N,1)finite_sum)) /\
     (\w. lift(c w)) continuous_on (:real^(N,1)finite_sum) /\
     (!z xi. lam * norm xi pow 2 <= xi dot (a z ** xi)) /\
     (!z i. 1 <= i /\ i <= dimindex(:N) ==> abs(b z$i) <= Kb) /\
     (!z. abs(c z) <= Kc)
     ==> ?C. &0 < C /\
             !(v:real^(N,1)finite_sum->real^1) f g k.
               compact k /\ smooth_map_on (:real^(N,1)finite_sum) v /\
               (!z. ~(z IN k) ==> v z = vec 0) /\
               f continuous_on (:real^(N,1)finite_sum) /\ (!z. ~(z IN k) ==> f z = vec 0) /\
               (!i. 1 <= i /\ i <= dimindex(:N)
                    ==> smooth_map_on (:real^(N,1)finite_sum) (g i) /\
                        (!z. ~(z IN k) ==> g i z = vec 0)) /\
               wan_ceq a b c f g v
               ==> sum(1..dimindex(:N))
                     (\i. drop(integral (:real^(N,1)finite_sum)
                                (\z. lift(norm(partial_derivative i v z) pow 2)))) <=
                   C * (drop(integral (:real^(N,1)finite_sum) (\z. lift(norm(v z) pow 2))) +
                        drop(integral (:real^(N,1)finite_sum) (\z. lift(norm(f z) pow 2))) +
                        sum(1..dimindex(:N))
                          (\i. drop(integral (:real^(N,1)finite_sum)
                                     (\z. lift(norm(g i z) pow 2)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= Kb /\ &0 <= Kc` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPECL [`vec 0:real^(N,1)finite_sum`; `1`]
        (ASSUME `!z i. 1 <= i /\ i <= dimindex(:N)
                       ==> abs((b:real^(N,1)finite_sum->real^N) z$i) <= Kb`)) THEN
      REWRITE_TAC[LE_REFL; DIMINDEX_GE_1] THEN REAL_ARITH_TAC;
      MP_TAC(SPEC `vec 0:real^(N,1)finite_sum`
        (ASSUME `!z. abs((c:real^(N,1)finite_sum->real) z) <= Kc`)) THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `&2 / lam * (&(dimindex(:N)) * Kb pow 2 / lam + Kc + &1 + inv lam)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH];
      MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ &0 <= y /\ &0 < z ==> &0 < x + y + &1 + z`) THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_MUL; REAL_POS; REAL_LE_POW_2; REAL_LT_IMP_LE;
                   REAL_LT_INV]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`v:real^(N,1)finite_sum->real^1`; `f:real^(N,1)finite_sum->real^1`;
                       `g:num->real^(N,1)finite_sum->real^1`; `k:real^(N,1)finite_sum->bool`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^(N,1)finite_sum->real^N^N`; `b:real^(N,1)finite_sum->real^N`;
                 `c:real^(N,1)finite_sum->real`; `f:real^(N,1)finite_sum->real^1`;
                 `g:num->real^(N,1)finite_sum->real^1`; `v:real^(N,1)finite_sum->real^1`;
                 `k:real^(N,1)finite_sum->bool`] WAN_PEN_IDENTITY) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "id") THEN
  SUBGOAL_THEN
   `(\z. lift(drop((v:real^(N,1)finite_sum->real^1) z))) continuous_on (:real^(N,1)finite_sum) /\
    (!i. (\z. lift(drop(partial_derivative i v z))) continuous_on (:real^(N,1)finite_sum)) /\
    (\z. lift(drop((f:real^(N,1)finite_sum->real^1) z))) continuous_on (:real^(N,1)finite_sum) /\
    (!i. 1 <= i /\ i <= dimindex(:N)
         ==> (\z. lift(drop((g:num->real^(N,1)finite_sum->real^1) i z))) continuous_on
               (:real^(N,1)finite_sum)) /\
    (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
           ==> (\z. lift((a:real^(N,1)finite_sum->real^N^N) z$i$j)) continuous_on
                 (:real^(N,1)finite_sum)) /\
    (!z. ~(z IN k) ==> drop(v z) = &0) /\
    (!i z. ~(z IN k) ==> drop(partial_derivative i v z) = &0) /\
    (!z. ~(z IN k) ==> drop(f z) = &0) /\
    (!i z. 1 <= i /\ i <= dimindex(:N) /\ ~(z IN k) ==> drop(g i z) = &0)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_DROP; ETA_AX] THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
      GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      ASM_SIMP_TAC[WAN_PEN_SMOOTH_PARTIAL];
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_SIMP_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_SIMP_TAC[];
      ASM_SIMP_TAC[DROP_VEC];
      REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`v:real^(N,1)finite_sum->real^1`; `k:real^(N,1)finite_sum->bool`;
                     `i:num`; `z:real^(N,1)finite_sum`] WAN_PEN_PSUPPORT) THEN
      ASM_SIMP_TAC[DROP_VEC];
      ASM_SIMP_TAC[DROP_VEC];
      ASM_SIMP_TAC[DROP_VEC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!ff:real^(N,1)finite_sum->real.
      (\z. lift(ff z)) continuous_on (:real^(N,1)finite_sum) /\
      (!z. ~(z IN k) ==> ff z = &0)
      ==> (\z. lift(ff z)) integrable_on (:real^(N,1)finite_sum)`
  (LABEL_TAC "ccs") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_PEN_CCS_INTEGRABLE THEN
    EXISTS_TAC `k:real^(N,1)finite_sum->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^1. norm x pow 2 = drop x pow 2`
  ASSUME_TAC THENL [REWRITE_TAC[NORM_1; REAL_POW2_ABS]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N))
      (\i. drop(integral (:real^(N,1)finite_sum)
                  (\z. lift(drop(partial_derivative i (v:real^(N,1)finite_sum->real^1) z)
                            pow 2)))) =
    drop(integral (:real^(N,1)finite_sum)
           (\z. lift(sum(1..dimindex(:N)) (\i. drop(partial_derivative i v z) pow 2)))) /\
    sum(1..dimindex(:N))
      (\i. drop(integral (:real^(N,1)finite_sum)
                  (\z. lift(drop((g:num->real^(N,1)finite_sum->real^1) i z) pow 2)))) =
    drop(integral (:real^(N,1)finite_sum)
           (\z. lift(sum(1..dimindex(:N)) (\i. drop(g i z) pow 2))))`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC WAN_PEN_RINT_SUM THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "ccs" MATCH_MP_TAC THEN CONJ_TAC THEN
    TRY(REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_POW_2; REAL_MUL_LZERO] THEN NO_TAC) THEN
    WAN_RCONT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. lift(sum(1..dimindex(:N))
               (\i. drop(partial_derivative i (v:real^(N,1)finite_sum->real^1) z) pow 2)))
      integrable_on (:real^(N,1)finite_sum) /\
    (\z. lift(drop((v:real^(N,1)finite_sum->real^1) z) pow 2))
      integrable_on (:real^(N,1)finite_sum) /\
    (\z. lift(drop((f:real^(N,1)finite_sum->real^1) z) pow 2))
      integrable_on (:real^(N,1)finite_sum) /\
    (\z. lift(sum(1..dimindex(:N))
               (\i. drop((g:num->real^(N,1)finite_sum->real^1) i z) pow 2)))
      integrable_on (:real^(N,1)finite_sum) /\
    (\z. lift(sum(1..dimindex(:N))
               (\i. sum(1..dimindex(:N))
                      (\j. (a:real^(N,1)finite_sum->real^N^N) z$i$j *
                           drop(partial_derivative i v z) * drop(partial_derivative j v z)))))
      integrable_on (:real^(N,1)finite_sum) /\
    (\z. lift(sum(1..dimindex(:N))
                 (\i. (b:real^(N,1)finite_sum->real^N) z$i * drop(v z) *
                      drop(partial_derivative i v z) -
                      drop(g i z) * drop(partial_derivative i v z)) +
               (c:real^(N,1)finite_sum->real) z * drop(v z) pow 2 + drop(v z) * drop(f z)))
      integrable_on (:real^(N,1)finite_sum)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN USE_THEN "ccs" MATCH_MP_TAC THEN CONJ_TAC THEN
    TRY(REPEAT STRIP_TAC THEN
        ASM_SIMP_TAC[REAL_POW_2; REAL_MUL_LZERO; REAL_MUL_RZERO; SUM_0; REAL_SUB_REFL;
                     REAL_ADD_LID] THEN NO_TAC) THEN
    TRY(REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
        ASM_SIMP_TAC[REAL_POW_2; REAL_MUL_LZERO] THEN NO_TAC) THEN
    WAN_RCONT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lam * drop(integral (:real^(N,1)finite_sum)
                 (\z. lift(sum(1..dimindex(:N))
                         (\i. drop(partial_derivative i (v:real^(N,1)finite_sum->real^1) z)
                              pow 2)))) <=
    drop(integral (:real^(N,1)finite_sum)
           (\z. lift(sum(1..dimindex(:N))
                   (\i. sum(1..dimindex(:N))
                          (\j. (a:real^(N,1)finite_sum->real^N^N) z$i$j *
                               drop(partial_derivative i v z) *
                               drop(partial_derivative j v z))))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `drop(integral (:real^(N,1)finite_sum)
             (\z. lam % lift(sum(1..dimindex(:N))
                       (\i. drop(partial_derivative i (v:real^(N,1)finite_sum->real^1) z)
                            pow 2))))` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL; REAL_LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_SIMP_TAC[INTEGRABLE_CMUL] THEN
    X_GEN_TAC `z:real^(N,1)finite_sum` THEN DISCH_TAC THEN
    REWRITE_TAC[DROP_CMUL; LIFT_DROP] THEN
    MP_TAC(ISPECL [`lam:real`; `(a:real^(N,1)finite_sum->real^N^N) z`;
                   `\i. drop(partial_derivative i (v:real^(N,1)finite_sum->real^1) z)`]
                  WAN_PEN_ELLIPTIC_POINT) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `C1 = &(dimindex(:N)) * Kb pow 2 / lam + Kc + &1 / &2` THEN
  SUBGOAL_THEN
   `drop(integral (:real^(N,1)finite_sum)
           (\z. lift(sum(1..dimindex(:N))
                       (\i. (b:real^(N,1)finite_sum->real^N) z$i *
                            drop((v:real^(N,1)finite_sum->real^1) z) *
                            drop(partial_derivative i v z) -
                            drop((g:num->real^(N,1)finite_sum->real^1) i z) *
                            drop(partial_derivative i v z)) +
                     (c:real^(N,1)finite_sum->real) z * drop(v z) pow 2 +
                     drop(v z) * drop((f:real^(N,1)finite_sum->real^1) z)))) <=
    lam / &2 * drop(integral (:real^(N,1)finite_sum)
                      (\z. lift(sum(1..dimindex(:N))
                                  (\i. drop(partial_derivative i v z) pow 2)))) +
    C1 * drop(integral (:real^(N,1)finite_sum) (\z. lift(drop(v z) pow 2))) +
    &1 / &2 * drop(integral (:real^(N,1)finite_sum) (\z. lift(drop(f z) pow 2))) +
    inv lam * drop(integral (:real^(N,1)finite_sum)
                     (\z. lift(sum(1..dimindex(:N)) (\i. drop(g i z) pow 2))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `drop(integral (:real^(N,1)finite_sum)
             (\z. (lam / &2) % lift(sum(1..dimindex(:N))
                                     (\i. drop(partial_derivative i
                                                (v:real^(N,1)finite_sum->real^1) z) pow 2)) +
                  C1 % lift(drop(v z) pow 2) +
                  (&1 / &2) % lift(drop((f:real^(N,1)finite_sum->real^1) z) pow 2) +
                  inv lam % lift(sum(1..dimindex(:N))
                                  (\i. drop((g:num->real^(N,1)finite_sum->real^1) i z)
                                       pow 2))))` THEN
    MP_TAC(ISPECL
     [`\z. (lam / &2) % lift(sum(1..dimindex(:N))
                          (\i. drop(partial_derivative i (v:real^(N,1)finite_sum->real^1) z)
                               pow 2))`;
      `\z. C1 % lift(drop((v:real^(N,1)finite_sum->real^1) z) pow 2)`;
      `\z. (&1 / &2) % lift(drop((f:real^(N,1)finite_sum->real^1) z) pow 2)`;
      `\z. inv lam % lift(sum(1..dimindex(:N))
                          (\i. drop((g:num->real^(N,1)finite_sum->real^1) i z) pow 2))`;
      `(:real^(N,1)finite_sum)`] WAN_INTEGRAL_ADD4) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `z:real^(N,1)finite_sum` THEN DISCH_TAC THEN
      REWRITE_TAC[DROP_ADD; DROP_CMUL; LIFT_DROP] THEN EXPAND_TAC "C1" THEN
      MATCH_MP_TAC WAN_PEN_RBOUND THEN ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_ADD; DROP_CMUL; REAL_LE_REFL]];
    ALL_TAC] THEN
  ABBREV_TAC `P = drop(integral (:real^(N,1)finite_sum)
                     (\z. lift(sum(1..dimindex(:N))
                             (\i. drop(partial_derivative i (v:real^(N,1)finite_sum->real^1) z)
                                  pow 2))))` THEN
  ABBREV_TAC `U = drop(integral (:real^(N,1)finite_sum)
                     (\z. lift(drop((v:real^(N,1)finite_sum->real^1) z) pow 2)))` THEN
  ABBREV_TAC `Ph = drop(integral (:real^(N,1)finite_sum)
                      (\z. lift(drop((f:real^(N,1)finite_sum->real^1) z) pow 2)))` THEN
  ABBREV_TAC `G = drop(integral (:real^(N,1)finite_sum)
                     (\z. lift(sum(1..dimindex(:N))
                             (\i. drop((g:num->real^(N,1)finite_sum->real^1) i z) pow 2))))` THEN
  SUBGOAL_THEN `&0 <= U /\ &0 <= Ph /\ &0 <= G` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["U"; "Ph"; "G"] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN
    GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  ABBREV_TAC `D = &(dimindex(:N)) * Kb pow 2 / lam + Kc + &1 + inv lam` THEN
  SUBGOAL_THEN `C1 <= D /\ &1 / &2 <= D /\ inv lam <= D` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["C1"; "D"] THEN
    SUBGOAL_THEN `&0 <= &(dimindex(:N)) * Kb pow 2 / lam /\ &0 < inv lam`
    MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_MUL; REAL_POS; REAL_LE_POW_2; REAL_LT_IMP_LE;
                   REAL_LT_INV];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `C1 * U <= D * U /\ &1 / &2 * Ph <= D * Ph /\ inv lam * G <= D * G`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `lam / &2 * P <= D * (U + Ph + G)` MP_TAC THENL
   [USE_THEN "id" (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `P = &2 / lam * (lam / &2 * P)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE]);;

(* ========================================================================= *)
(* The differentiated equation (a derivative d_k v, in any                   *)
(* space or time direction, solves the same equation with differentiated    *)
(* data) and linearity of the classical equation.                            *)
(* ========================================================================= *)

let WAN_PD_SYM = prove
 (`!(u:real^M->real^K) i j z.
     smooth_map_on (:real^M) u /\ 1 <= i /\ i <= dimindex(:M) /\ 1 <= j /\ j <= dimindex(:M)
     ==> partial_derivative i (partial_derivative j u) z =
         partial_derivative j (partial_derivative i u) z`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PARTIAL_DERIVATIVE_SYM THEN
  EXISTS_TAC `(:real^M)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
  ASM_MESON_TAC[smooth_map_on]);;

let WAN_PD_DROPMUL = prove
 (`!(s:real^M->real) (u:real^M->real^K) k z.
     smooth_map_on (:real^M) (\w. lift(s w)) /\ smooth_map_on (:real^M) u
     ==> partial_derivative k (\w. s w % u w) z =
         s z % partial_derivative k u z +
         drop(partial_derivative k (\w. lift(s w)) z) % u z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `\w:real^M. lift((s:real^M->real) w)`; `u:real^M->real^K`;
                 `z:real^M`] PARTIAL_DERIVATIVE_MUL) THEN
  REWRITE_TAC[LIFT_DROP; ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `(:real^M)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV]);;

let WAN_PD_ADD = prove
 (`!(u:real^M->real^K) w k z.
     smooth_map_on (:real^M) u /\ smooth_map_on (:real^M) w
     ==> partial_derivative k (\x. u x + w x) z =
         partial_derivative k u z + partial_derivative k w z`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PARTIAL_DERIVATIVE_ADD THEN
  CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `(:real^M)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV]);;

let WAN_PD_VSUM = prove
 (`!(u:num->real^M->real^K) n k z.
     (!i. 1 <= i /\ i <= n ==> smooth_map_on (:real^M) (u i))
     ==> partial_derivative k (\x. vsum(1..n) (\i. u i x)) z =
         vsum(1..n) (\i. partial_derivative k (u i) z)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PARTIAL_DERIVATIVE_VSUM THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `(:real^M)` THEN ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV]);;

let WAN_SMOOTH_VSUM = prove
 (`!(u:num->real^M->real^K) n.
     (!i. 1 <= i /\ i <= n ==> smooth_map_on (:real^M) (u i))
     ==> smooth_map_on (:real^M) (\x. vsum(1..n) (\i. u i x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN
  ASM_SIMP_TAC[OPEN_UNIV; FINITE_NUMSEG; IN_NUMSEG; ETA_AX]);;

let WAN_SMOOTH_SMUL = prove
 (`!(s:real^M->real) (u:real^M->real^K).
     smooth_map_on (:real^M) (\w. lift(s w)) /\ smooth_map_on (:real^M) u
     ==> smooth_map_on (:real^M) (\w. s w % u w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\w:real^M. lift((s:real^M->real) w)`; `u:real^M->real^K`]
                WAN_PEN_SMOOTH_DROPMUL) THEN
  ASM_REWRITE_TAC[LIFT_DROP; ETA_AX]);;

let WAN_PD_ADD4 = prove
 (`!(u1:real^M->real^K) u2 u3 u4 k z.
     smooth_map_on (:real^M) u1 /\ smooth_map_on (:real^M) u2 /\
     smooth_map_on (:real^M) u3 /\ smooth_map_on (:real^M) u4
     ==> partial_derivative k (\x. u1 x + u2 x + u3 x + u4 x) z =
         partial_derivative k u1 z + partial_derivative k u2 z +
         partial_derivative k u3 z + partial_derivative k u4 z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on (:real^M) (\x. (u3:real^M->real^K) x + u4 x) /\
                smooth_map_on (:real^M) (\x. (u2:real^M->real^K) x + u3 x + u4 x)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT(MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
                         ASM_REWRITE_TAC[OPEN_UNIV; ETA_AX]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u1:real^M->real^K`; `\x. (u2:real^M->real^K) x + u3 x + u4 x`;
                 `k:num`; `z:real^M`] WAN_PD_ADD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`u2:real^M->real^K`; `\x. (u3:real^M->real^K) x + u4 x`;
                 `k:num`; `z:real^M`] WAN_PD_ADD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC WAN_PD_ADD THEN ASM_REWRITE_TAC[]);;

let WAN_PD_FLUX = prove
 (`!(A:num->real^M->real) (v:real^M->real^1) (g:real^M->real^1) n k z.
     (!j. 1 <= j /\ j <= n ==> smooth_map_on (:real^M) (\w. lift(A j w))) /\
     smooth_map_on (:real^M) v /\ smooth_map_on (:real^M) g /\
     1 <= k /\ k <= dimindex(:M) /\ n <= dimindex(:M)
     ==> partial_derivative k
           (\w. vsum(1..n) (\j. A j w % partial_derivative j v w) + g w) z =
         vsum(1..n) (\j. A j z % partial_derivative j (partial_derivative k v) z) +
         (partial_derivative k g z +
          vsum(1..n) (\j. drop(partial_derivative k (\w. lift(A j w)) z) %
                          partial_derivative j v z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!j. smooth_map_on (:real^M) (partial_derivative j (v:real^M->real^1))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[WAN_PEN_SMOOTH_PARTIAL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= n
        ==> smooth_map_on (:real^M)
              (\w. (A:num->real^M->real) j w % partial_derivative j (v:real^M->real^1) w)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_SMOOTH_SMUL THEN ASM_SIMP_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `partial_derivative k
      (\w. vsum(1..n) (\j. (A:num->real^M->real) j w %
                           partial_derivative j (v:real^M->real^1) w) + g w) z =
    partial_derivative k (\w. vsum(1..n) (\j. A j w % partial_derivative j v w)) z +
    partial_derivative k g z`
  SUBST1_TAC THENL
   [MATCH_MP_TAC WAN_PD_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC WAN_SMOOTH_VSUM THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `partial_derivative k
      (\w. vsum(1..n) (\j. (A:num->real^M->real) j w %
                           partial_derivative j (v:real^M->real^1) w)) z =
    vsum(1..n) (\j. partial_derivative k (\w. A j w % partial_derivative j v w) z)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`\j w. (A:num->real^M->real) j w % partial_derivative j (v:real^M->real^1) w`;
                   `n:num`; `k:num`; `z:real^M`] WAN_PD_VSUM) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= n
        ==> partial_derivative k (\w. (A:num->real^M->real) j w %
                                      partial_derivative j (v:real^M->real^1) w) z =
            A j z % partial_derivative j (partial_derivative k v) z +
            drop(partial_derivative k (\w. lift(A j w)) z) % partial_derivative j v z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`(A:num->real^M->real) j`; `partial_derivative j (v:real^M->real^1)`;
                   `k:num`; `z:real^M`] WAN_PD_DROPMUL) THEN
    ASM_SIMP_TAC[ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC WAN_PD_SYM THEN ASM_SIMP_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[VSUM_ADD_NUMSEG] THEN VECTOR_ARITH_TAC);;

let WAN_CEQ_DIFF = prove
 (`!(a:real^(N,1)finite_sum->real^N^N) b c f g (v:real^(N,1)finite_sum->real^1) k.
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> smooth_map_on (:real^(N,1)finite_sum) (\w. lift(a w$i$j))) /\
     (!i. 1 <= i /\ i <= dimindex(:N)
          ==> smooth_map_on (:real^(N,1)finite_sum) (\w. lift(b w$i))) /\
     smooth_map_on (:real^(N,1)finite_sum) (\w. lift(c w)) /\
     smooth_map_on (:real^(N,1)finite_sum) f /\
     (!i. 1 <= i /\ i <= dimindex(:N) ==> smooth_map_on (:real^(N,1)finite_sum) (g i)) /\
     smooth_map_on (:real^(N,1)finite_sum) v /\
     1 <= k /\ k <= dimindex(:N) + 1 /\
     wan_ceq a b c f g v
     ==> wan_ceq a b c
           (\z. partial_derivative k f z +
                vsum(1..dimindex(:N))
                  (\i. drop(partial_derivative k (\w. lift(b w$i)) z) %
                       partial_derivative i v z) +
                drop(partial_derivative k (\w. lift(c w)) z) % v z)
           (\i z. partial_derivative k (g i) z +
                  vsum(1..dimindex(:N))
                    (\j. drop(partial_derivative k (\w. lift(a w$i$j)) z) %
                         partial_derivative j v z))
           (partial_derivative k v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `dimindex(:(N,1)finite_sum) = dimindex(:N) + 1` ASSUME_TAC THENL
   [REWRITE_TAC[TEXT_DIMINDEX_SPACETIME]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!i. smooth_map_on (:real^(N,1)finite_sum) (partial_derivative i v)) /\
    (!i j. smooth_map_on (:real^(N,1)finite_sum)
             (partial_derivative i (partial_derivative j (v:real^(N,1)finite_sum->real^1))))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_PEN_SMOOTH_PARTIAL]; ALL_TAC] THEN
  ABBREV_TAC
   `H = \i (w:real^(N,1)finite_sum).
          vsum(1..dimindex(:N))
            (\j. (a:real^(N,1)finite_sum->real^N^N) w$i$j %
                 partial_derivative j (v:real^(N,1)finite_sum->real^1) w) +
          (g:num->real^(N,1)finite_sum->real^1) i w` THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> smooth_map_on (:real^(N,1)finite_sum) ((H:num->real^(N,1)finite_sum->real^1) i)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "H" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_SIMP_TAC[OPEN_UNIV; ETA_AX] THEN
    MATCH_MP_TAC WAN_SMOOTH_VSUM THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC WAN_SMOOTH_SMUL THEN ASM_SIMP_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> partial_derivative k ((H:num->real^(N,1)finite_sum->real^1) i) =
            (\w. vsum(1..dimindex(:N))
                   (\j. (a:real^(N,1)finite_sum->real^N^N) w$i$j %
                        partial_derivative j (partial_derivative k v) w) +
                 (partial_derivative k ((g:num->real^(N,1)finite_sum->real^1) i) w +
                  vsum(1..dimindex(:N))
                    (\j. drop(partial_derivative k (\w. lift(a w$i$j)) w) %
                         partial_derivative j v w)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `w:real^(N,1)finite_sum` THEN
    EXPAND_TAC "H" THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\j (w:real^(N,1)finite_sum). (a:real^(N,1)finite_sum->real^N^N) w$i$j`;
                   `v:real^(N,1)finite_sum->real^1`;
                   `(g:num->real^(N,1)finite_sum->real^1) i`; `dimindex(:N)`; `k:num`;
                   `w:real^(N,1)finite_sum`] WAN_PD_FLUX) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `partial_derivative (dimindex(:N) + 1) (v:real^(N,1)finite_sum->real^1) =
    (\z. vsum(1..dimindex(:N))
           (\i. partial_derivative i ((H:num->real^(N,1)finite_sum->real^1) i) z) +
         vsum(1..dimindex(:N))
           (\i. (b:real^(N,1)finite_sum->real^N) z$i % partial_derivative i v z) +
         (c:real^(N,1)finite_sum->real) z % v z + (f:real^(N,1)finite_sum->real^1) z)`
  (LABEL_TAC "eqf") THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN EXPAND_TAC "H" THEN
    UNDISCH_TAC `wan_ceq (a:real^(N,1)finite_sum->real^N^N) b c f g v` THEN
    REWRITE_TAC[wan_ceq];
    ALL_TAC] THEN
  REWRITE_TAC[wan_ceq] THEN X_GEN_TAC `z:real^(N,1)finite_sum` THEN
  SUBGOAL_THEN
   `partial_derivative (dimindex(:N) + 1) (partial_derivative k v) z =
    partial_derivative k (partial_derivative (dimindex(:N) + 1)
                           (v:real^(N,1)finite_sum->real^1)) z`
  SUBST1_TAC THENL
   [MATCH_MP_TAC WAN_PD_SYM THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "eqf" SUBST1_TAC THEN
  MP_TAC(ISPECL
   [`\z. vsum(1..dimindex(:N))
           (\i. partial_derivative i ((H:num->real^(N,1)finite_sum->real^1) i) z)`;
    `\z. vsum(1..dimindex(:N))
           (\i. (b:real^(N,1)finite_sum->real^N) z$i %
                partial_derivative i (v:real^(N,1)finite_sum->real^1) z)`;
    `\z. (c:real^(N,1)finite_sum->real) z % (v:real^(N,1)finite_sum->real^1) z`;
    `f:real^(N,1)finite_sum->real^1`; `k:num`; `z:real^(N,1)finite_sum`] WAN_PD_ADD4) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC WAN_SMOOTH_VSUM THEN REPEAT STRIP_TAC THEN REWRITE_TAC[]) THEN
    TRY(MATCH_MP_TAC WAN_SMOOTH_SMUL THEN ASM_SIMP_TAC[ETA_AX] THEN NO_TAC) THEN
    REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[WAN_PEN_SMOOTH_PARTIAL];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `partial_derivative k
      (\z. vsum(1..dimindex(:N))
             (\i. partial_derivative i ((H:num->real^(N,1)finite_sum->real^1) i) z)) z =
    vsum(1..dimindex(:N))
      (\i. partial_derivative i (partial_derivative k (H i)) z)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`\i. partial_derivative i ((H:num->real^(N,1)finite_sum->real^1) i)`;
                   `dimindex(:N)`; `k:num`; `z:real^(N,1)finite_sum`] WAN_PD_VSUM) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[WAN_PEN_SMOOTH_PARTIAL]; ALL_TAC] THEN
    REWRITE_TAC[ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC WAN_PD_SYM THEN ASM_SIMP_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `vsum(1..dimindex(:N))
      (\i. partial_derivative i (partial_derivative k
                                  ((H:num->real^(N,1)finite_sum->real^1) i)) z) =
    vsum(1..dimindex(:N))
      (\i. partial_derivative i
             (\w. vsum(1..dimindex(:N))
                    (\j. (a:real^(N,1)finite_sum->real^N^N) w$i$j %
                         partial_derivative j (partial_derivative k v) w) +
                  partial_derivative k ((g:num->real^(N,1)finite_sum->real^1) i) w +
                  vsum(1..dimindex(:N))
                    (\j. drop(partial_derivative k (\w. lift(a w$i$j)) w) %
                         partial_derivative j v w)) z)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `partial_derivative k
      (\z. vsum(1..dimindex(:N))
             (\i. (b:real^(N,1)finite_sum->real^N) z$i %
                  partial_derivative i (v:real^(N,1)finite_sum->real^1) z)) z =
    vsum(1..dimindex(:N)) (\i. b z$i % partial_derivative i (partial_derivative k v) z) +
    vsum(1..dimindex(:N))
      (\i. drop(partial_derivative k (\w. lift(b w$i)) z) % partial_derivative i v z)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`\i (z:real^(N,1)finite_sum). (b:real^(N,1)finite_sum->real^N) z$i %
                                               partial_derivative i
                                                 (v:real^(N,1)finite_sum->real^1) z`;
                   `dimindex(:N)`; `k:num`; `z:real^(N,1)finite_sum`] WAN_PD_VSUM) THEN
    ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC WAN_SMOOTH_SMUL THEN
      ASM_SIMP_TAC[ETA_AX];
      ALL_TAC] THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[GSYM VSUM_ADD_NUMSEG] THEN
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\w:real^(N,1)finite_sum. (b:real^(N,1)finite_sum->real^N) w$i`;
                   `partial_derivative i (v:real^(N,1)finite_sum->real^1)`;
                   `k:num`; `z:real^(N,1)finite_sum`] WAN_PD_DROPMUL) THEN
    ASM_SIMP_TAC[ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC WAN_PD_SYM THEN ASM_SIMP_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:real^(N,1)finite_sum->real`; `v:real^(N,1)finite_sum->real^1`;
                 `k:num`; `z:real^(N,1)finite_sum`] WAN_PD_DROPMUL) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_ACCEPT_TAC(VECTOR_ARITH
   `!A B1 B2 C1 C2 Fk:real^1.
      A + (B1 + B2) + (C1 + C2) + Fk = A + B1 + C1 + Fk + B2 + C2`));;

let WAN_CEQ_SUB = prove
 (`!(a:real^(N,1)finite_sum->real^N^N) b c f1 g1 (v1:real^(N,1)finite_sum->real^1) f2 g2 v2.
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> smooth_map_on (:real^(N,1)finite_sum) (\w. lift(a w$i$j))) /\
     smooth_map_on (:real^(N,1)finite_sum) v1 /\ smooth_map_on (:real^(N,1)finite_sum) v2 /\
     (!i. 1 <= i /\ i <= dimindex(:N)
          ==> smooth_map_on (:real^(N,1)finite_sum) (g1 i) /\
              smooth_map_on (:real^(N,1)finite_sum) (g2 i)) /\
     wan_ceq a b c f1 g1 v1 /\ wan_ceq a b c f2 g2 v2
     ==> wan_ceq a b c (\z. f1 z - f2 z) (\i z. g1 i z - g2 i z) (\z. v1 z - v2 z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_ceq] THEN STRIP_TAC THEN
  X_GEN_TAC `z:real^(N,1)finite_sum` THEN
  SUBGOAL_THEN
   `!i w. partial_derivative i (\z. (v1:real^(N,1)finite_sum->real^1) z - v2 z) w =
          partial_derivative i v1 w - partial_derivative i v2 w`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC PARTIAL_DERIVATIVE_SUB THEN
    CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(:real^(N,1)finite_sum)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  ABBREV_TAC
   `H1 = \i (w:real^(N,1)finite_sum).
          vsum(1..dimindex(:N))
            (\j. (a:real^(N,1)finite_sum->real^N^N) w$i$j %
                 partial_derivative j (v1:real^(N,1)finite_sum->real^1) w) +
          (g1:num->real^(N,1)finite_sum->real^1) i w` THEN
  ABBREV_TAC
   `H2 = \i (w:real^(N,1)finite_sum).
          vsum(1..dimindex(:N))
            (\j. (a:real^(N,1)finite_sum->real^N^N) w$i$j %
                 partial_derivative j (v2:real^(N,1)finite_sum->real^1) w) +
          (g2:num->real^(N,1)finite_sum->real^1) i w` THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> smooth_map_on (:real^(N,1)finite_sum) ((H1:num->real^(N,1)finite_sum->real^1) i) /\
            smooth_map_on (:real^(N,1)finite_sum) ((H2:num->real^(N,1)finite_sum->real^1) i)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MAP_EVERY EXPAND_TAC ["H1"; "H2"] THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_SIMP_TAC[OPEN_UNIV; ETA_AX] THEN
    MATCH_MP_TAC WAN_SMOOTH_VSUM THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC WAN_SMOOTH_SMUL THEN ASM_SIMP_TAC[ETA_AX; WAN_PEN_SMOOTH_PARTIAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. (\w. vsum(1..dimindex(:N))
               (\j. (a:real^(N,1)finite_sum->real^N^N) w$i$j %
                    (partial_derivative j (v1:real^(N,1)finite_sum->real^1) w -
                     partial_derivative j (v2:real^(N,1)finite_sum->real^1) w)) +
             ((g1:num->real^(N,1)finite_sum->real^1) i w - g2 i w)) =
        (\w. (H1:num->real^(N,1)finite_sum->real^1) i w - (H2:num->real^(N,1)finite_sum->real^1) i w)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MAP_EVERY EXPAND_TAC ["H1"; "H2"] THEN
    REWRITE_TAC[FUN_EQ_THM; VECTOR_SUB_LDISTRIB; VSUM_SUB_NUMSEG] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `vsum(1..dimindex(:N))
      (\i. partial_derivative i
             (\w. (H1:num->real^(N,1)finite_sum->real^1) i w -
                  (H2:num->real^(N,1)finite_sum->real^1) i w) z) =
    vsum(1..dimindex(:N)) (\i. partial_derivative i (H1 i) z) -
    vsum(1..dimindex(:N)) (\i. partial_derivative i (H2 i) z)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM VSUM_SUB_NUMSEG] THEN MATCH_MP_TAC VSUM_EQ_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC PARTIAL_DERIVATIVE_SUB THEN
    CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(:real^(N,1)finite_sum)` THEN ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; ETA_AX];
    ALL_TAC] THEN
  MAP_EVERY EXPAND_TAC ["H1"; "H2"] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VECTOR_SUB_LDISTRIB; VSUM_SUB_NUMSEG] THEN VECTOR_ARITH_TAC);;

(* ========================================================================= *)
(* The weak form on the whole space (wan_gweak, with weak                   *)
(* spatial gradient K and data f, g), and the weak identity of classical    *)
(* solutions.                                                                *)
(* ========================================================================= *)

let wan_gweak = new_definition
 `wan_gweak (a:real^(N,1)finite_sum->real^N^N) (b:real^(N,1)finite_sum->real^N)
            (c:real^(N,1)finite_sum->real) (f:real^(N,1)finite_sum->real^1)
            (g:num->real^(N,1)finite_sum->real^1) (v:real^(N,1)finite_sum->real^1)
            (K:num->real^(N,1)finite_sum->real^1) <=>
    !phi. wan_test (:real^(N,1)finite_sum) phi
          ==> integral (:real^(N,1)finite_sum)
                (\z. wan_dpart (dimindex(:N) + 1) phi z % v z -
                     vsum(1..dimindex(:N))
                       (\i. wan_dpart i phi z %
                            (vsum(1..dimindex(:N)) (\j. a z$i$j % K j z) + g i z)) +
                     phi z % (vsum(1..dimindex(:N)) (\i. b z$i % K i z) + c z % v z + f z)) =
              vec 0`;;

let WAN_TEST_LIFT = prove
 (`!(phi:real^M->real) i z.
     wan_test (:real^M) phi
     ==> smooth_map_on (:real^M) (\z. lift(phi z)) /\
         ?k. compact k /\ (!z. ~(z IN k) ==> lift(phi z) = vec 0) /\
         wan_dpart i phi z = drop(partial_derivative i (\z. lift(phi z)) z)`,
  REWRITE_TAC[wan_test; wan_dpart; partial_derivative; SUBSET_UNIV] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `k:real^M->bool` THEN
  ASM_SIMP_TAC[LIFT_NUM]);;

let WAN_TEST_IBP_SMOOTH = prove
 (`!(phi:real^M->real) (h:real^M->real^1) i.
     wan_test (:real^M) phi /\ smooth_map_on (:real^M) h
     ==> integral (:real^M) (\z. wan_dpart i phi z % h z) =
         --(integral (:real^M) (\z. phi z % partial_derivative i h z))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[wan_test] (ASSUME `wan_test (:real^M) (phi:real^M->real)`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:real^M->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`\z:real^M. lift((phi:real^M->real) z)`; `h:real^M->real^1`;
                 `k:real^M->bool`; `i:num`] WAN_PEN_IBP) THEN
  ASM_SIMP_TAC[LIFT_NUM; LIFT_DROP] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(\z. wan_dpart i (phi:real^M->real) z % (h:real^M->real^1) z) =
    (\z. drop(h z) % partial_derivative i (\z. lift(phi z)) z)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; wan_dpart; partial_derivative] THEN GEN_TAC THEN
    REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL] THEN MATCH_ACCEPT_TAC REAL_MUL_SYM;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[VECTOR_NEG_NEG]);;

let WAN_PEN_HAS_INTEGRAL_PARTIAL = prove
 (`!(hh:real^M->real^K) k i.
     compact k /\ smooth_map_on (:real^M) hh /\ (!z. ~(z IN k) ==> hh z = vec 0)
     ==> ((\z. partial_derivative i hh z) has_integral vec 0) (:real^M)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[partial_derivative] THEN
  MATCH_MP_TAC WAN_INTEGRAL_DIRDERIV_ZERO THEN EXISTS_TAC `k:real^M->bool` THEN
  ASM_REWRITE_TAC[]);;

let WAN_CEQ_WEAK = prove
 (`!(a:real^(N,1)finite_sum->real^N^N) b c f g (v:real^(N,1)finite_sum->real^1).
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> smooth_map_on (:real^(N,1)finite_sum) (\w. lift(a w$i$j))) /\
     (!i. 1 <= i /\ i <= dimindex(:N) ==> smooth_map_on (:real^(N,1)finite_sum) (g i)) /\
     smooth_map_on (:real^(N,1)finite_sum) v /\
     wan_ceq a b c f g v
     ==> wan_gweak a b c f g v (\j. partial_derivative j v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[wan_gweak] THEN
  X_GEN_TAC `phi:real^(N,1)finite_sum->real` THEN DISCH_TAC THEN
  MP_TAC(REWRITE_RULE[wan_test]
    (ASSUME `wan_test (:real^(N,1)finite_sum) (phi:real^(N,1)finite_sum->real)`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:real^(N,1)finite_sum->bool`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC
   `H = \i (w:real^(N,1)finite_sum).
          vsum(1..dimindex(:N))
            (\j. (a:real^(N,1)finite_sum->real^N^N) w$i$j %
                 partial_derivative j (v:real^(N,1)finite_sum->real^1) w) +
          (g:num->real^(N,1)finite_sum->real^1) i w` THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> smooth_map_on (:real^(N,1)finite_sum) ((H:num->real^(N,1)finite_sum->real^1) i)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "H" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_SIMP_TAC[OPEN_UNIV; ETA_AX] THEN
    MATCH_MP_TAC WAN_SMOOTH_VSUM THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC WAN_SMOOTH_SMUL THEN ASM_SIMP_TAC[ETA_AX; WAN_PEN_SMOOTH_PARTIAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!(ff:real^(N,1)finite_sum->real^1) w.
      smooth_map_on (:real^(N,1)finite_sum) ff
      ==> !i. partial_derivative i (\w. (phi:real^(N,1)finite_sum->real) w % ff w) w =
              phi w % partial_derivative i ff w + wan_dpart i phi w % ff w`
  (LABEL_TAC "pr") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`phi:real^(N,1)finite_sum->real`; `ff:real^(N,1)finite_sum->real^1`;
                   `i:num`; `w:real^(N,1)finite_sum`] WAN_PD_DROPMUL) THEN
    ASM_REWRITE_TAC[wan_dpart; partial_derivative];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. wan_dpart (dimindex(:N) + 1) phi z % (v:real^(N,1)finite_sum->real^1) z -
        vsum(1..dimindex(:N))
          (\i. wan_dpart i phi z %
               (vsum(1..dimindex(:N))
                  (\j. (a:real^(N,1)finite_sum->real^N^N) z$i$j % partial_derivative j v z) +
                (g:num->real^(N,1)finite_sum->real^1) i z)) +
        phi z % (vsum(1..dimindex(:N))
                   (\i. (b:real^(N,1)finite_sum->real^N) z$i % partial_derivative i v z) +
                 (c:real^(N,1)finite_sum->real) z % v z + (f:real^(N,1)finite_sum->real^1) z) =
        partial_derivative (dimindex(:N) + 1) (\w. phi w % v w) z -
        vsum(1..dimindex(:N))
          (\i. partial_derivative i
                 (\w. phi w % (H:num->real^(N,1)finite_sum->real^1) i w) z)`
  (fun th -> REWRITE_TAC[th]) THENL
   [X_GEN_TAC `z:real^(N,1)finite_sum` THEN
    USE_THEN "pr" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
      `smooth_map_on (:real^(N,1)finite_sum) (v:real^(N,1)finite_sum->real^1)`)]) THEN
    SUBGOAL_THEN
     `vsum(1..dimindex(:N))
        (\i. partial_derivative i
               (\w. (phi:real^(N,1)finite_sum->real) w %
                    (H:num->real^(N,1)finite_sum->real^1) i w) z) =
      phi z % vsum(1..dimindex(:N)) (\i. partial_derivative i (H i) z) +
      vsum(1..dimindex(:N)) (\i. wan_dpart i phi z % H i z)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM VSUM_LMUL; GSYM VSUM_ADD_NUMSEG] THEN
      MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN
      USE_THEN "pr" (fun th -> MP_TAC(SPECL
        [`(H:num->real^(N,1)finite_sum->real^1) i`; `z:real^(N,1)finite_sum`] th)) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(MATCH_ACCEPT_TAC o SPEC `i:num`)];
      ALL_TAC] THEN
    UNDISCH_TAC `wan_ceq (a:real^(N,1)finite_sum->real^N^N) b c f g v` THEN
    REWRITE_TAC[wan_ceq] THEN DISCH_THEN(MP_TAC o SPEC `z:real^(N,1)finite_sum`) THEN
    EXPAND_TAC "H" THEN REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[VECTOR_ADD_LDISTRIB] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  GEN_REWRITE_TAC LAND_CONV [VECTOR_ARITH `vec 0:real^1 = vec 0 - vec 0`] THEN
  MATCH_MP_TAC HAS_INTEGRAL_SUB THEN CONJ_TAC THENL
   [MATCH_MP_TAC WAN_PEN_HAS_INTEGRAL_PARTIAL THEN EXISTS_TAC `k:real^(N,1)finite_sum->bool` THEN
    ASM_SIMP_TAC[VECTOR_MUL_LZERO] THEN MATCH_MP_TAC WAN_SMOOTH_SMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `vec 0:real^1 = vsum(1..dimindex(:N)) (\i. vec 0)` SUBST1_TAC THENL
   [REWRITE_TAC[VSUM_0]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_INTEGRAL_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC WAN_PEN_HAS_INTEGRAL_PARTIAL THEN EXISTS_TAC `k:real^(N,1)finite_sum->bool` THEN
  ASM_SIMP_TAC[VECTOR_MUL_LZERO] THEN MATCH_MP_TAC WAN_SMOOTH_SMUL THEN
  ASM_SIMP_TAC[ETA_AX]);;

