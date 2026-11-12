(* ========================================================================= *)
(* pc_p2a_usc: upper semicontinuity of Lx (L7 FIX, P2A_LX_USC_FIX).  An      *)
(* admissible curve is cut at s1 < sqrt b and joined in a region chart to a  *)
(* nearby end point by an affine chart curve; finite L-length bounds the     *)
(* energy near the end, so the junction costs little (Cauchy-Schwarz). The   *)
(* result is smoothed by L12 FIX.                                            *)
(*                                                                           *)
(* First: the displacement bound for a C^1 chart curve.                      *)
(* ========================================================================= *)

needs "src/pc_p2a_smth.ml";;

prioritize_real();;
type_invention_error := true;;

let P2A_NORM_LE_INTEGRAL = prove
 (`!(Y:real^1->real^N) s1 s2.
     s1 <= s2 /\
     (!r. s1 <= r /\ r <= s2 ==> Y differentiable (at (lift r))) /\
     (\x. vector_derivative Y (at x)) continuous_on interval[lift s1,lift s2]
     ==> norm(Y(lift s2) - Y(lift s1)) <=
         real_integral (real_interval[s1,s2]) (\r. norm(vector_derivative Y (at (lift r))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Y:real^1->real^N`; `\x. vector_derivative (Y:real^1->real^N) (at x)`;
                 `lift s1`; `lift s2`] FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LIFT_DROP; FORALL_LIFT; IN_INTERVAL_1] THEN
    X_GEN_TAC `r:real` THEN STRIP_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
    REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP INTEGRAL_UNIQUE)] THEN
  SUBGOAL_THEN
   `(\r. norm(vector_derivative (Y:real^1->real^N) (at (lift r)))) real_integrable_on
    real_interval[s1,s2]`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_INTEGRABLE_ON; IMAGE_LIFT_REAL_INTERVAL] THEN
    MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN REWRITE_TAC[o_DEF; LIFT_DROP] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_INTEGRAL; IMAGE_LIFT_REAL_INTERVAL] THEN
  MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
  REWRITE_TAC[o_DEF; LIFT_DROP; REAL_LE_REFL] THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `(\r. norm(vector_derivative (Y:real^1->real^N) (at (lift r))))
                  real_integrable_on real_interval[s1,s2]` THEN
    REWRITE_TAC[REAL_INTEGRABLE_ON; IMAGE_LIFT_REAL_INTERVAL; o_DEF; LIFT_DROP]]);;

let P2A_CS_DISPLACEMENT = prove
 (`!(Y:real^1->real^N) s1 s2.
     s1 < s2 /\
     (!r. s1 <= r /\ r <= s2 ==> Y differentiable (at (lift r))) /\
     (\x. vector_derivative Y (at x)) continuous_on interval[lift s1,lift s2]
     ==> norm(Y(lift s2) - Y(lift s1)) pow 2 <=
         (s2 - s1) * real_integral (real_interval[s1,s2])
                       (\r. norm(vector_derivative Y (at (lift r))) pow 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Y:real^1->real^N`; `s1:real`; `s2:real`] P2A_NORM_LE_INTEGRAL) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN
   `(\r. norm(vector_derivative (Y:real^1->real^N) (at (lift r)))) real_continuous_on
    real_interval[s1,s2]`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_CONTINUOUS_ON; IMAGE_LIFT_REAL_INTERVAL; o_DEF; LIFT_DROP] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\r. norm(vector_derivative (Y:real^1->real^N) (at (lift r))) pow 2) real_continuous_on
    real_interval[s1,s2]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `Dd = norm((Y:real^1->real^N)(lift s2) - Y(lift s1))` THEN
  ABBREV_TAC `Jn = real_integral (real_interval[s1,s2])
                    (\r. norm(vector_derivative (Y:real^1->real^N) (at (lift r))))` THEN
  ABBREV_TAC `En = real_integral (real_interval[s1,s2])
                    (\r. norm(vector_derivative (Y:real^1->real^N) (at (lift r))) pow 2)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `!lam. &0 < lam ==> &2 * Jn <= lam * En + (s2 - s1) / lam` ASSUME_TAC THENL
   [X_GEN_TAC `lam:real` THEN DISCH_TAC THEN EXPAND_TAC "Jn" THEN EXPAND_TAC "En" THEN
    SUBGOAL_THEN `(s2 - s1) / lam = real_integral (real_interval[s1,s2]) (\r. inv lam)`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[REAL_INTEGRAL_CONST; REAL_LT_IMP_LE] THEN REWRITE_TAC[real_div] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM REAL_INTEGRAL_LMUL; REAL_INTEGRABLE_CONTINUOUS] THEN
    W(MP_TAC o PART_MATCH (rand o rand) REAL_INTEGRAL_ADD o rand o snd) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN ASM_SIMP_TAC[REAL_INTEGRABLE_CONTINUOUS];
        REWRITE_TAC[REAL_INTEGRABLE_CONST]];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC REAL_INTEGRAL_LE THEN
    ASM_SIMP_TAC[REAL_INTEGRABLE_LMUL; REAL_INTEGRABLE_CONTINUOUS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_ADD THEN
      ASM_SIMP_TAC[REAL_INTEGRABLE_LMUL; REAL_INTEGRABLE_CONTINUOUS; REAL_INTEGRABLE_CONST];
      ALL_TAC] THEN
    X_GEN_TAC `r:real` THEN DISCH_TAC THEN
    ABBREV_TAC `n = norm(vector_derivative (Y:real^1->real^N) (at (lift r)))` THEN
    SUBGOAL_THEN `&0 <= (lam * n - &1) pow 2` MP_TAC THENL
     [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
    SUBGOAL_THEN `lam * n pow 2 + inv lam - &2 * n = inv lam * (lam * n - &1) pow 2`
    ASSUME_TAC THENL
     [UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= inv lam * (lam * n - &1) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= En` ASSUME_TAC THENL
   [EXPAND_TAC "En" THEN MATCH_MP_TAC REAL_INTEGRAL_POS THEN
    ASM_SIMP_TAC[REAL_INTEGRABLE_CONTINUOUS; REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Dd` ASSUME_TAC THENL [EXPAND_TAC "Dd" THEN REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  ASM_CASES_TAC `En = &0` THENL
   [ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
    ASM_CASES_TAC `Dd = &0` THENL
     [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(s2 - s1) / Dd`) THEN
    SUBGOAL_THEN `&0 < Dd` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_SUB_LT; REAL_MUL_RZERO; REAL_ADD_LID] THEN
    SUBGOAL_THEN `(s2 - s1) / ((s2 - s1) / Dd) = Dd` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < Dd` THEN UNDISCH_TAC `s1 < s2` THEN CONV_TAC REAL_FIELD;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < En` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `t = sqrt((s2 - s1) / En)` THEN
  SUBGOAL_THEN `&0 < t /\ t pow 2 * En = s2 - s1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN
    SUBGOAL_THEN `&0 < (s2 - s1) / En` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE] THEN
    UNDISCH_TAC `&0 < En` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(s2 - s1) / t = t * En` SUBST1_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `t pow 2 * En = s2 - s1`)) THEN
    UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `Dd <= t * En` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(t * En) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `t pow 2 * En = s2 - s1`)) THEN
    REWRITE_TAC[REAL_POW_MUL; REAL_POW_2] THEN REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Uniform two-sided bounds for a smooth family of metrics in s on compact   *)
(* sets, and the kinetic part of the s-Lagrangian.                           *)
(* ========================================================================= *)

let P2A_LSMOOTH_QUAD_BOUNDS = prove
 (`!Uo sa sb (Gt:real->real^N->real^N^N) tt K s1 s2.
     p2a_lsmooth Uo sa sb (\s. Gt(tt - s pow 2)) /\ sa < s1 /\ s1 <= s2 /\ s2 < sb /\
     compact K /\ K SUBSET Uo
     ==> ?c Cg. &0 < c /\ c <= Cg /\
                !s y v. s1 <= s /\ s <= s2 /\ y IN K
                        ==> c * norm v pow 2 <= v dot (Gt(tt - s pow 2) y ** v) /\
                            v dot (Gt(tt - s pow 2) y ** v) <= Cg * norm v pow 2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_lsmooth] THEN STRIP_TAC THEN
  ASM_CASES_TAC `K:real^N->bool = {}` THENL
   [MAP_EVERY EXISTS_TAC [`&1`; `&1`] THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY; REAL_LE_REFL; REAL_LT_01];
    ALL_TAC] THEN
  ABBREV_TAC `Kc = interval[lift s1,lift s2] PCROSS (K:real^N->bool)` THEN
  SUBGOAL_THEN `compact(Kc:real^(1,N)finite_sum->bool) /\
                Kc SUBSET interval(lift sa,lift sb) PCROSS (Uo:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Kc" THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_PCROSS THEN ASM_REWRITE_TAC[COMPACT_INTERVAL];
      REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; FORALL_LIFT;
                  IN_INTERVAL_1; LIFT_DROP] THEN
      REPEAT STRIP_TAC THEN (ASM_REAL_ARITH_TAC ORELSE ASM SET_TAC[])];
    ALL_TAC] THEN
  ABBREV_TAC `G = \z:real^(1,N)finite_sum. (Gt:real->real^N->real^N^N)
                     (tt - drop(fstcart z) pow 2) (sndcart z)` THEN
  SUBGOAL_THEN `((vectorize:real^N^N->real^(N,N)finite_prod) o
                 (G:real^(1,N)finite_sum->real^N^N)) continuous_on Kc` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `interval(lift sa,lift sb) PCROSS (Uo:real^N->bool)` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "G" THEN REWRITE_TAC[o_DEF] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?B. &0 < B /\
                    !z. z IN Kc ==> norm((vectorize:real^N^N->real^(N,N)finite_prod)
                                           ((G:real^(1,N)finite_sum->real^N^N) z)) <= B`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `IMAGE ((vectorize:real^N^N->real^(N,N)finite_prod) o
                         (G:real^(1,N)finite_sum->real^N^N)) Kc` COMPACT_IMP_BOUNDED) THEN
    ASM_SIMP_TAC[COMPACT_CONTINUOUS_IMAGE] THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; o_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\p:real^((1,N)finite_sum,N)finite_sum.
       sndcart p dot ((G:real^(1,N)finite_sum->real^N^N) (fstcart p) ** sndcart p)`;
    `(Kc:real^(1,N)finite_sum->bool) PCROSS sphere(vec 0:real^N,&1)`]
   CONTINUOUS_ATTAINS_INF) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_PCROSS THEN ASM_REWRITE_TAC[COMPACT_SPHERE];
      REWRITE_TAC[PCROSS_EQ_EMPTY; SPHERE_EQ_EMPTY; DE_MORGAN_THM] THEN
      CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
      EXPAND_TAC "Kc" THEN
      REWRITE_TAC[PCROSS_EQ_EMPTY; INTERVAL_EQ_EMPTY_1; LIFT_DROP; DE_MORGAN_THM] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_SNDCART];
        ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_MATRIX_VECTOR_MUL THEN CONJ_TAC THENL
       [ALL_TAC;
        MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_SNDCART]] THEN
      SUBGOAL_THEN
       `(vectorize:real^N^N->real^(N,N)finite_prod) o
        (\p:real^((1,N)finite_sum,N)finite_sum. (G:real^(1,N)finite_sum->real^N^N) (fstcart p)) =
        (vectorize o G) o fstcart`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_FSTCART];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `Kc:real^(1,N)finite_sum->bool` THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; FSTCART_PASTECART] THEN
        SIMP_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_IN_PCROSS; FORALL_IN_PCROSS; FSTCART_PASTECART;
              SNDCART_PASTECART; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `z0:real^(1,N)finite_sum` (X_CHOOSE_THEN `u0:real^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `&0 < u0 dot ((G:real^(1,N)finite_sum->real^N^N) z0 ** u0)` ASSUME_TAC THENL
   [SUBGOAL_THEN `~(u0:real^N = vec 0)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `norm(u0:real^N) = &1` THEN
      ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `(z0:real^(1,N)finite_sum) IN Kc` THEN EXPAND_TAC "Kc" THEN
    REWRITE_TAC[FORALL_PASTECART] THEN
    SUBST1_TAC(SYM(ISPEC `z0:real^(1,N)finite_sum` PASTECART_FST_SND)) THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN STRIP_TAC THEN
    EXPAND_TAC "G" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `drop(fstcart(z0:real^(1,N)finite_sum))` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "metric_field")) (concl th))) THEN
    ANTS_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[GSYM drop; LIFT_DROP]) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[metric_field] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `sndcart(z0:real^(1,N)finite_sum)` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "transp")) (concl th))) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `c0 = u0 dot ((G:real^(1,N)finite_sum->real^N^N) z0 ** u0)` THEN
  MAP_EVERY EXISTS_TAC [`c0:real`; `max B c0`] THEN
  ASM_REWRITE_TAC[REAL_LE_MAX; REAL_LE_REFL] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `y:real^N`; `v:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pastecart (lift s) (y:real^N) IN Kc` ASSUME_TAC THENL
   [EXPAND_TAC "Kc" THEN ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN `(G:real^(1,N)finite_sum->real^N^N) (pastecart (lift s) y) =
                (Gt:real->real^N->real^N^N)(tt - s pow 2) y` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `v:real^N = vec 0` THENL
     [ASM_REWRITE_TAC[NORM_0; DOT_LZERO] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`pastecart (lift s) (y:real^N)`; `inv(norm v) % v:real^N`] o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `c0:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0; GRGD_QUAD_HOMOG] THEN
    SUBGOAL_THEN `&0 < norm(v:real^N)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
    ABBREV_TAC `qq = v dot ((Gt:real->real^N->real^N^N)(tt - s pow 2) y ** v)` THEN
    ABBREV_TAC `n = norm(v:real^N)` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `qq = (inv n * inv n * qq) * n pow 2` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < n` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    ASM_REWRITE_TAC[REAL_MUL_ASSOC];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B * norm(v:real^N) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm(vectorize((Gt:real->real^N->real^N^N)(tt - s pow 2) y)) *
                  norm(v:real^N) pow 2` THEN
      REWRITE_TAC[P2A_QUAD_VECTORIZE_BOUND] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      REWRITE_TAC[REAL_LE_POW_2] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (lift s) (y:real^N)` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `B:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC]]);;

let P2A_LLAG_SPLIT = prove
 (`!(Gt:real->real^N->real^N^N) tt s y A.
     p2a_llag Gt tt s y A =
     inv(&2) * (A dot (Gt(tt - s pow 2) y ** A)) + p2a_llag Gt tt s y (vec 0)`,
  REWRITE_TAC[p2a_llag; DOT_LZERO] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* On a compact subinterval where the region-chart curve is C^1, its         *)
(* displacement is bounded by its L-length (energy).                         *)
(* ========================================================================= *)

let P2A_END_ENERGY = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) W a' b'' (U:A->bool) (phi:A->real^N) sa sb' s1 s c Kb.
     p2a_svs V /\ p2a_adm V tt x b gamma /\
     p2a_region V W a' b'' /\ (U,phi) IN p2a_vatlas V b'' /\
     &0 < s1 /\ s1 < s /\ s pow 2 <= b /\ sa < s1 /\ s < sb' /\
     (!r. sa < r /\ r < sb' ==> a' < tt - r pow 2 /\ tt - r pow 2 <= b'') /\
     (!r. s1 <= r /\ r <= s ==> gamma(r pow 2) IN U INTER W) /\
     (!r. s1 <= r /\ r <= s
          ==> (\v. phi(gamma(drop v pow 2))) differentiable (at (lift r)) /\
              (\v. vector_derivative (\v. phi(gamma(drop v pow 2))) (at v))
                continuous (at (lift r))) /\
     &0 < c /\
     (!r A. s1 <= r /\ r <= s
            ==> c * norm A pow 2 <=
                A dot (p2a_rlocal V W b'' (U INTER W,phi) (tt - r pow 2)
                         (phi(gamma(r pow 2))) ** A)) /\
     (!r. s1 <= r /\ r <= s
          ==> abs(p2a_llag (p2a_rlocal V W b'' (U INTER W,phi)) tt r
                           (phi(gamma(r pow 2))) (vec 0)) <= Kb)
     ==> norm(phi(gamma(s pow 2)) - phi(gamma(s1 pow 2))) pow 2 <=
         (&2 / c) * (s - s1) *
         (real_integral (real_interval[s1 pow 2,s pow 2]) (p2a_L_integrand V tt gamma b) +
          Kb * (s - s1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Gt = p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                 (real->A->real^N^N)) W b'' (U INTER W,phi:A->real^N)` THEN
  SUBGOAL_THEN `(\x. vector_derivative (\v:real^1. (phi:A->real^N)((gamma:real->A)(drop v pow 2)))
                       (at x)) continuous_on interval[lift s1,lift s]` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
    X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "differentiable")) (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?M. !r. s1 <= r /\ r <= s
            ==> norm(vector_derivative (\v:real^1. (phi:A->real^N)((gamma:real->A)(drop v pow 2)))
                                       (at (lift r))) <= M`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `IMAGE (\x. vector_derivative
                               (\v:real^1. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) (at x))
                        (interval[lift s1,lift s])` COMPACT_IMP_BOUNDED) THEN
    ASM_SIMP_TAC[COMPACT_CONTINUOUS_IMAGE; COMPACT_INTERVAL] THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`;
                 `s1:real`; `s:real`; `W:A->bool`; `a':real`; `b'':real`;
                 `U:A->bool`; `phi:A->real^N`; `{}:real->bool`; `sa:real`; `sb':real`;
                 `M:real`] P2A_LINT_PIECE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_EMPTY; NOT_IN_EMPTY] THEN REPEAT CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`r:real`; `O:A->bool`] THEN STRIP_TAC THEN
      MP_TAC(SPECL [`r:real`; `O:A->bool`] (MATCH_MP P2A_ADM_SCONT (ASSUME
        `p2a_adm (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)) tt x b gamma`))) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `s pow 2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
      REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "differentiable")) (concl th))) THEN
      ASM_SIMP_TAC[];
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "differentiable")) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `M:real`)) (concl th))) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
  REWRITE_TAC[p2a_cL; LIFT_DROP] THEN
  ABBREV_TAC `En = real_integral (real_interval[s1,s])
                     (\r. norm(vector_derivative
                                (\v:real^1. (phi:A->real^N)((gamma:real->A)(drop v pow 2)))
                                (at (lift r))) pow 2)` THEN
  SUBGOAL_THEN `p2a_lsmooth (IMAGE (phi:A->real^N) (U INTER W)) sa sb'
                  (\r. (Gt:real->real^N->real^N^N)(tt - r pow 2))` ASSUME_TAC THENL
   [EXPAND_TAC "Gt" THEN MATCH_MP_TAC P2A_REGION_SFAMILY THEN EXISTS_TAC `a':real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\r. p2a_llag (Gt:real->real^N->real^N^N) tt r ((phi:A->real^N)((gamma:real->A)(r pow 2)))
                  (vector_derivative (\v:real^1. phi(gamma(drop v pow 2))) (at (lift r))))
      real_integrable_on real_interval[s1,s] /\
    (\r. norm(vector_derivative (\v:real^1. (phi:A->real^N)((gamma:real->A)(drop v pow 2)))
                                (at (lift r))) pow 2) real_integrable_on real_interval[s1,s]`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THENL
     [MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER W)`; `sa:real`; `sb':real`;
                     `Gt:real->real^N->real^N^N`; `tt:real`;
                     `\v:real^1. (phi:A->real^N)((gamma:real->A)(drop v pow 2))`; `r:real`]
                    P2A_LLAG_CONT_AT) THEN
      REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "differentiable")) (concl th))) THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS_ATREAL; o_DEF] THEN
      MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_LIFT_POW) THEN
      MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_LIFT_NORM_COMPOSE) THEN
      REWRITE_TAC[LIFT_DROP; ETA_AX] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "differentiable")) (concl th))) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(c / &2) * En - Kb * (s - s1) <=
    real_integral (real_interval[s1,s])
      (\r. p2a_llag (Gt:real->real^N->real^N^N) tt r ((phi:A->real^N)((gamma:real->A)(r pow 2)))
                    (vector_derivative (\v:real^1. phi(gamma(drop v pow 2))) (at (lift r))))`
  ASSUME_TAC THENL
   [EXPAND_TAC "En" THEN
    SUBGOAL_THEN `Kb * (s - s1) = real_integral (real_interval[s1,s]) (\r:real. Kb)`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[REAL_INTEGRAL_CONST; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM REAL_INTEGRAL_LMUL] THEN
    W(MP_TAC o PART_MATCH (rand o rand) REAL_INTEGRAL_SUB o lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_INTEGRABLE_LMUL; REAL_INTEGRABLE_CONST]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC REAL_INTEGRAL_LE THEN
    ASM_SIMP_TAC[REAL_INTEGRABLE_SUB; REAL_INTEGRABLE_LMUL; REAL_INTEGRABLE_CONST] THEN
    X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[P2A_LLAG_SPLIT] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`r:real`; `vector_derivative (\v:real^1. (phi:A->real^N)((gamma:real->A)(drop v pow 2)))
                                   (at (lift r))`] o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `c:real`)) (concl th))) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `Kb:real`)) (concl th))) THEN
    EXPAND_TAC "Gt" THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\v:real^1. (phi:A->real^N)((gamma:real->A)(drop v pow 2))`; `s1:real`; `s:real`]
                P2A_CS_DISPLACEMENT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "differentiable")) (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(s - s1) * En` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `En <= (&2 / c) *
                (real_integral (real_interval[s1,s])
                   (\r. p2a_llag (Gt:real->real^N->real^N^N) tt r
                          ((phi:A->real^N)((gamma:real->A)(r pow 2)))
                          (vector_derivative (\v:real^1. phi(gamma(drop v pow 2))) (at (lift r)))) +
                 Kb * (s - s1))`
  MP_TAC THENL
   [SUBGOAL_THEN `&0 < c / &2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `!X. &2 / c * X = X / (c / &2)` (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= s - s1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The curve cut at s1^2 and joined to a chart point p by an affine chart    *)
(* curve on [s1, sqrt b].                                                    *)
(* ========================================================================= *)

let P2A_AFFINE_VD = prove
 (`!(A:real^N) d c s1 x.
     ((\v:real^1. A + (c * (drop v - s1)) % d) has_vector_derivative (c % d)) (at x)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `(\v:real^1. (A:real^N) + (c * (drop v - s1)) % d) =
                (\v. (A - (c * s1) % d) + drop v % (c % d))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC; REAL_SUB_LDISTRIB; VECTOR_SUB_RDISTRIB] THEN
    REWRITE_TAC[REAL_MUL_SYM] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM VECTOR_ADD_LID] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST] THEN
  REWRITE_TAC[has_vector_derivative] THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
  REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN CONJ_TAC THEN VECTOR_ARITH_TAC);;

let p2a_jcurve = new_definition
 `p2a_jcurve (gamma:real->A) (U:A->bool) (W:A->bool) (phi:A->real^N) (s1:real) (sb:real)
             (p:real^N) =
    \tau. if tau <= s1 pow 2 then gamma tau
          else chart_inv (U INTER W,phi)
                 (phi(gamma(s1 pow 2)) +
                  (inv(sb - s1) * (sqrt tau - s1)) % (p - phi(gamma(s1 pow 2))))`;;

let P2A_JCURVE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) W a' b'' (U:A->bool) (phi:A->real^N) s1 sa sb' p.
     p2a_svs V /\ p2a_adm V tt x b gamma /\
     p2a_region V W a' b'' /\ (U,phi) IN p2a_vatlas V b'' /\
     &0 < s1 /\ s1 < sqrt b /\ sa < s1 /\ sqrt b < sb' /\
     (!s. sa < s /\ s < sb' ==> a' < tt - s pow 2 /\ tt - s pow 2 < b'') /\
     gamma(s1 pow 2) IN U INTER W /\
     (!s. s1 <= s /\ s <= sqrt b
          ==> phi(gamma(s1 pow 2)) + (inv(sqrt b - s1) * (s - s1)) % (p - phi(gamma(s1 pow 2)))
              IN IMAGE phi (U INTER W))
     ==> p2a_adm V tt x b (p2a_jcurve gamma U W phi s1 (sqrt b) p) /\
         p2a_jcurve gamma U W phi s1 (sqrt b) p b = chart_inv (U INTER W,phi) p /\
         p2a_L_length V tt (p2a_jcurve gamma U W phi s1 (sqrt b) p) b =
         p2a_L_length V tt gamma (s1 pow 2) +
         p2a_cL (p2a_rlocal V W b'' (U INTER W,phi)) tt
                (\v. phi(gamma(s1 pow 2)) +
                     (inv(sqrt b - s1) * (drop v - s1)) % (p - phi(gamma(s1 pow 2))))
                s1 (sqrt b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_adm]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt b pow 2 = b /\ &0 < sqrt b` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POW_2; SQRT_POS_LT; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `s1 pow 2 < b` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `sqrt b pow 2 = b`)) THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `W:A->bool`; `a':real`; `b'':real`;
                 `U:A->bool`; `phi:A->real^N`;
                 `\v:real^1. (phi:A->real^N)((gamma:real->A)(s1 pow 2)) +
                             (inv(sqrt b - s1) * (drop v - s1)) % (p - phi(gamma(s1 pow 2)))`;
                 `s1:real`; `sqrt b`; `sa:real`; `sb':real`] P2A_CHART_CURVE_SEG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LIFT_DROP] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN
      EXISTS_TAC `inv(sqrt b - s1) % ((p:real^N) - phi((gamma:real->A)(s1 pow 2)))` THEN
      REWRITE_TAC[P2A_AFFINE_VD];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\v. vector_derivative
             (\v:real^1. (phi:A->real^N)((gamma:real->A)(s1 pow 2)) +
                         (inv(sqrt b - s1) * (drop v - s1)) % (p - phi(gamma(s1 pow 2))))
             (at v)) =
      (\v. inv(sqrt b - s1) % ((p:real^N) - phi(gamma(s1 pow 2))))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
      REWRITE_TAC[P2A_AFFINE_VD];
      REWRITE_TAC[CONTINUOUS_CONST]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`;
                 `\tau. chart_inv (U INTER W,phi:A->real^N)
                          ((phi:A->real^N)((gamma:real->A)(s1 pow 2)) +
                           (inv(sqrt b - s1) * (sqrt tau - s1)) % (p - phi(gamma(s1 pow 2))))`;
                 `gamma:real->A`; `p2a_jcurve (gamma:real->A) U W (phi:A->real^N) s1 (sqrt b) p`;
                 `b:real`; `s1 pow 2`] P2A_SEG_GLUE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2A_ADM_RESTRICT THEN EXISTS_TAC `b:real` THEN
      ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_IMP_LE];
      ASM_REWRITE_TAC[];
      REWRITE_TAC[] THEN ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE] THEN
      REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2A_REGION_CHART_INV THEN
      MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                               (real->A->real^N^N)`; `a':real`; `b'':real`] THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s1:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `a':real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      X_GEN_TAC `tau:real` THEN DISCH_TAC THEN ASM_REWRITE_TAC[p2a_jcurve];
      X_GEN_TAC `tau:real` THEN DISCH_TAC THEN REWRITE_TAC[p2a_jcurve] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `tau = s1 pow 2` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE] THEN
      REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2A_REGION_CHART_INV THEN
      MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                               (real->A->real^N^N)`; `a':real`; `b'':real`] THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s1:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `a':real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[p2a_jcurve] THEN
    SUBGOAL_THEN `~(b <= s1 pow 2)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN `inv(sqrt b - s1) * (sqrt b - s1) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC];
    AP_TERM_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "has_real_integral")) (concl th))) THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The L-length of the affine piece, and the displacement of the curve near  *)
(* its end point.                                                            *)
(* ========================================================================= *)

let P2A_ZPIECE_LENGTH = prove
 (`!Uo sa sb' (Gt:real->real^N->real^N^N) tt (A0:real^N) d c0 s1 s2 K Cg Kp.
     p2a_lsmooth Uo sa sb' (\s. Gt(tt - s pow 2)) /\ sa < s1 /\ s1 <= s2 /\ s2 < sb' /\
     K SUBSET Uo /\
     (!s. s1 <= s /\ s <= s2 ==> A0 + (c0 * (s - s1)) % d IN K) /\
     (!s y v. s1 <= s /\ s <= s2 /\ y IN K
              ==> v dot (Gt(tt - s pow 2) y ** v) <= Cg * norm v pow 2) /\
     (!s y. s1 <= s /\ s <= s2 /\ y IN K ==> abs(p2a_llag Gt tt s y (vec 0)) <= Kp)
     ==> p2a_cL Gt tt (\v. A0 + (c0 * (drop v - s1)) % d) s1 s2 <=
         (s2 - s1) * (inv(&2) * Cg * norm(c0 % d) pow 2 + Kp)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2a_cL] THEN
  SUBGOAL_THEN `!x. vector_derivative (\v:real^1. (A0:real^N) + (c0 * (drop v - s1)) % d) (at x) =
                    c0 % d` (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN REWRITE_TAC[P2A_AFFINE_VD]; ALL_TAC] THEN
  REWRITE_TAC[LIFT_DROP] THEN
  SUBGOAL_THEN `(s2 - s1) * (inv(&2) * Cg * norm(c0 % d:real^N) pow 2 + Kp) =
                real_integral (real_interval[s1,s2])
                  (\s:real. inv(&2) * Cg * norm(c0 % d:real^N) pow 2 + Kp)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[REAL_INTEGRAL_CONST] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_INTEGRAL_LE THEN REWRITE_TAC[REAL_INTEGRABLE_CONST; IN_REAL_INTERVAL] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
    MP_TAC(ISPECL [`Uo:real^N->bool`; `sa:real`; `sb':real`; `Gt:real->real^N->real^N^N`;
                   `tt:real`; `\v:real^1. (A0:real^N) + (c0 * (drop v - s1)) % d`; `s:real`]
                  P2A_LLAG_CONT_AT) THEN
    SUBGOAL_THEN `!x. vector_derivative (\v:real^1. (A0:real^N) + (c0 * (drop v - s1)) % d) (at x) =
                      c0 % d` (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN REWRITE_TAC[P2A_AFFINE_VD];
      ALL_TAC] THEN
    REWRITE_TAC[LIFT_DROP; CONTINUOUS_CONST] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term ((=) `Uo:real^N->bool`)) (concl th) &&
        not(can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lsmooth")) (concl th)))) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MESON_TAC[P2A_AFFINE_VD; HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE]];
    ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN ONCE_REWRITE_TAC[P2A_LLAG_SPLIT] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= Cg * n /\ abs y <= Kp ==> inv(&2) * x + y <= inv(&2) * Cg * n + Kp`) THEN
  SUBGOAL_THEN `(A0:real^N) + (c0 * (s - s1)) % d IN K` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[]);;

(* The displacement of the region-chart curve near the end point.           *)

let P2A_END_DISP = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) W a' b'' (U:A->bool) (phi:A->real^N) sa sb' s1 c Kp eps.
     p2a_svs V /\ p2a_adm V tt x b gamma /\
     p2a_region V W a' b'' /\ (U,phi) IN p2a_vatlas V b'' /\
     &0 < s1 /\ s1 < sqrt b /\ sa < s1 /\ sqrt b < sb' /\
     (!r. sa < r /\ r < sb' ==> a' < tt - r pow 2 /\ tt - r pow 2 <= b'') /\
     (!r. s1 <= r /\ r <= sqrt b ==> gamma(r pow 2) IN U INTER W) /\
     (!r. s1 <= r /\ r < sqrt b
          ==> (\v. phi(gamma(drop v pow 2))) differentiable (at (lift r)) /\
              (\v. vector_derivative (\v. phi(gamma(drop v pow 2))) (at v))
                continuous (at (lift r))) /\
     &0 < c /\
     (!r A. s1 <= r /\ r <= sqrt b
            ==> c * norm A pow 2 <=
                A dot (p2a_rlocal V W b'' (U INTER W,phi) (tt - r pow 2)
                         (phi(gamma(r pow 2))) ** A)) /\
     (!r. s1 <= r /\ r <= sqrt b
          ==> abs(p2a_llag (p2a_rlocal V W b'' (U INTER W,phi)) tt r
                           (phi(gamma(r pow 2))) (vec 0)) <= Kp) /\
     (!s. s1 <= s /\ s <= sqrt b
          ==> real_integral (real_interval[s1 pow 2,s pow 2]) (p2a_L_integrand V tt gamma b)
              <= c * eps / &4) /\
     Kp * (sqrt b - s1) <= c * eps / &4 /\ &0 < eps
     ==> norm(phi(gamma b) - phi(gamma(s1 pow 2))) pow 2 <= &4 * eps * (sqrt b - s1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_adm]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt b pow 2 = b` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Kp` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `s1:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `Kp:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the bound strictly before the end point *)
  SUBGOAL_THEN
   `!s. s1 < s /\ s < sqrt b
        ==> norm((phi:A->real^N)((gamma:real->A)(s pow 2)) - phi(gamma(s1 pow 2))) pow 2 <=
            eps * (sqrt b - s1)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                   `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                   `sa:real`; `sb':real`; `s1:real`; `s:real`; `c:real`; `Kp:real`]
                  P2A_END_ENERGY) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `sqrt b pow 2 = b`)) THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&2 / c) * (s - s1) * (c * eps / &4 + c * eps / &4)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Kp * (sqrt b - s1)` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `(&2 / c) * (s - s1) * (c * eps / &4 + c * eps / &4) = eps * (s - s1)`
      SUBST1_TAC THENL [UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* continuity of the chart curve at the end point *)
  SUBGOAL_THEN `(\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) continuous_on
                interval[lift s1,lift(sqrt b)]` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`;
                   `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                   `s1:real`; `sqrt b`] P2A_ADM_CHART_CONT) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[MATCH_MP P2A_ADM_SCONT (ASSUME
      `p2a_adm (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) tt x b gamma`); REAL_LE_REFL; REAL_LT_IMP_LE] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `a':real`)) (concl th))) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `zeta = sqrt(eps * (sqrt b - s1))` THEN
  SUBGOAL_THEN `&0 < zeta /\ zeta pow 2 = eps * (sqrt b - s1)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "zeta" THEN
    SUBGOAL_THEN `&0 < eps * (sqrt b - s1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  UNDISCH_TAC `(\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) continuous_on
               interval[lift s1,lift(sqrt b)]` THEN
  REWRITE_TAC[continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `lift(sqrt b)`) THEN
  REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; REAL_LE_REFL] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `zeta:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `s = sqrt b - min dl (sqrt b - s1) / &2` THEN
  SUBGOAL_THEN `s1 < s /\ s < sqrt b /\ dist(lift s,lift(sqrt b)) < dl` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[DIST_LIFT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `lift s` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `dl:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[LIFT_DROP; IN_INTERVAL_1] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[dist] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `eps:real`)) (concl th) &&
    not(can (find_term ((=) `c:real`)) (concl th)))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
  SUBGOAL_THEN `norm((phi:A->real^N)((gamma:real->A)(s pow 2)) - phi(gamma(s1 pow 2))) <= zeta`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
    ASM_REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2 * zeta) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC(NORM_ARITH
     `!z:real^N. norm(y - z) < e /\ norm(z - w) <= e ==> norm(y - w) <= &2 * e`) THEN
    EXISTS_TAC `(phi:A->real^N)((gamma:real->A)(s pow 2))` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[REAL_POW_MUL] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* L7 FIX (P2A_LX_USC_FIX).                                                  *)
(* ========================================================================= *)

let P2A_LX_USC_GEN = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b (gamma:real->A) e.
     p2a_svs V /\ p2a_atlas_lc V /\ p2a_bsmooth V x tt /\ p2a_adm V tt x b gamma /\ &0 < e
     ==> ?O. open_in (p2a_vtop V (tt - b)) O /\ gamma b IN O /\
             !q. q IN O
                 ==> ?gamma'. p2a_adm1 V tt x b gamma' /\ gamma' b = q /\
                              p2a_L_length V tt gamma' b <= p2a_L_length V tt gamma b + e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_adm]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt b /\ sqrt b pow 2 = b` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  (* the region chart at the end point *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `sqrt b`] P2A_MIN_REGION_AT) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:A->bool` (X_CHOOSE_THEN `a':real` (X_CHOOSE_THEN `b'':real`
    (X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))))))))) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN DISCH_TAC THEN
  (* the punctured window at the end point *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`; `sqrt b`]
                P2A_MIN_PUNCT_C1) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "H1") (CONJUNCTS_THEN2 (LABEL_TAC "H2") (LABEL_TAC "H3"))))) THEN
  SUBGOAL_THEN `?h1. &0 < h1 /\ h1 < h /\ h1 < sqrt b` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min h (sqrt b) / &2` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!s. sqrt b - h1 < s /\ s < sqrt b + h1
                    ==> a' < tt - s pow 2 /\ tt - s pow 2 < b''`
  (LABEL_TAC "WIN") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN USE_THEN "H1" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(s = &0)` (fun th -> SIMP_TAC[th]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. sqrt b - h1 < s /\ s < sqrt b + h1
                    ==> a' < tt - s pow 2 /\ tt - s pow 2 <= b''`
  (LABEL_TAC "WINLE") THENL
   [GEN_TAC THEN DISCH_TAC THEN USE_THEN "WIN" (MP_TAC o SPEC `s:real`) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2a_lsmooth (IMAGE (phi:A->real^N) (U INTER W)) (sqrt b - h1) (sqrt b + h1)
                  (\s. p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                     (real->A->real^N^N)) W b'' (U INTER W,phi) (tt - s pow 2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_REGION_SFAMILY THEN EXISTS_TAC `a':real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* a closed ball in the chart image *)
  SUBGOAL_THEN `?rho0. &0 < rho0 /\
                       cball((phi:A->real^N)((gamma:real->A) b),rho0) SUBSET
                       IMAGE phi (U INTER W)` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[p2a_lsmooth] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_lsmooth")) (concl th))) THEN
    REWRITE_TAC[OPEN_CONTAINS_CBALL] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* metric and curvature bounds near the end point *)
  MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER W)`; `sqrt b - h1`; `sqrt b + h1`;
                 `p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) W b'' (U INTER W,phi:A->real^N)`;
                 `tt:real`; `cball((phi:A->real^N)((gamma:real->A) b),rho0)`;
                 `sqrt b - h1 / &2`; `sqrt b + h1 / &2`] P2A_LSMOOTH_QUAD_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[COMPACT_CBALL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `Cg:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "QB"))))) THEN
  SUBGOAL_THEN `&0 <= Cg` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER W)`; `sqrt b - h1`; `sqrt b + h1`;
                 `p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) W b'' (U INTER W,phi:A->real^N)`;
                 `tt:real`; `cball((phi:A->real^N)((gamma:real->A) b),rho0)`;
                 `sqrt b - h1 / &2`; `sqrt b + h1 / &2`; `&0`] P2A_LLAG_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[COMPACT_CBALL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Kb:real` (LABEL_TAC "KB")) THEN
  ABBREV_TAC `Kp = abs Kb` THEN
  SUBGOAL_THEN `&0 <= Kp` ASSUME_TAC THENL [EXPAND_TAC "Kp" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s y. sqrt b - h1 / &2 <= s /\ s <= sqrt b + h1 / &2 /\
          y IN cball((phi:A->real^N)((gamma:real->A) b),rho0)
          ==> abs(p2a_llag (p2a_rlocal (V:(real->A topology)#
                 (real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N)) W b''
                 (U INTER W,phi)) tt s y (vec 0)) <= Kp`
  (LABEL_TAC "KP") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "Kp" THEN
    MATCH_MP_TAC(REAL_ARITH `x <= k ==> x <= abs k`) THEN USE_THEN "KB" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[NORM_0; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `?eps. &0 < eps /\ eps * (&16 * (Cg + &1)) = e`
  (X_CHOOSE_THEN `eps:real` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `e / (&16 * (Cg + &1))` THEN
    SUBGOAL_THEN `&0 < &16 * (Cg + &1)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV] THEN UNDISCH_TAC `&0 < &16 * (Cg + &1)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `Cg * eps <= e / &16` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `eta = min (e / &8) (c * eps / &4)` THEN
  SUBGOAL_THEN `&0 < eta /\ eta <= e / &8 /\ eta <= c * eps / &4` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN
    SUBGOAL_THEN `&0 < c * eps` MP_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the L-length near the end point is small *)
  SUBGOAL_THEN `p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                   (real->A->real^N^N)) tt gamma b
                real_integrable_on real_interval[&0,b]` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2a_adm]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                     (real->A->real^N^N)) tt gamma b`;
                 `&0`; `b:real`; `b:real`; `b:real`; `eta:real`]
                REAL_INDEFINITE_INTEGRAL_CONTINUOUS) THEN
  ASM_SIMP_TAC[IN_REAL_INTERVAL; REAL_LE_REFL; REAL_LT_IMP_LE; REAL_INTEGRAL_REFL;
               REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `kap:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "KAP"))) THEN
  MP_TAC(SPECL [`sqrt b`; `kap:real`] P2A_SQ_NEAR) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `hk:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "HK"))) THEN
  (* continuity of the chart curve at the end point *)
  SUBGOAL_THEN `(\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) continuous_on
                interval[lift(sqrt b - h1 / &2),lift(sqrt b)]` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`;
                   `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                   `sqrt b - h1 / &2`; `sqrt b`] P2A_ADM_CHART_CONT) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[MATCH_MP P2A_ADM_SCONT (ASSUME
      `p2a_adm (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) tt x b gamma`); REAL_LE_REFL] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN CONJ_TAC THENL
     [USE_THEN "H2" MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `sqrt b pow 2 = b`)) THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      USE_THEN "WINLE" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `(\v. (phi:A->real^N)((gamma:real->A)(drop v pow 2))) continuous_on
               interval[lift(sqrt b - h1 / &2),lift(sqrt b)]` THEN
  REWRITE_TAC[continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `lift(sqrt b)`) THEN
  REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; REAL_LE_REFL] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `rho0 / &4`) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dy:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DY"))) THEN
  (* the cut point s1 = sqrt b - d1 *)
  MP_TAC(SPECL [`c * eps / &4`; `Kp:real`] P2A_SMALL_K) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_DIV; REAL_ARITH `&0 < &4`];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ka:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "KA"))) THEN
  MP_TAC(SPECL [`e / &8`; `Kp:real`] P2A_SMALL_K) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `kb:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "KBB"))) THEN
  SUBGOAL_THEN
   `?d1. &0 < d1 /\ d1 <= h1 / &2 /\ d1 < hk /\ d1 < dy /\
         Kp * d1 <= c * eps / &4 /\ Kp * d1 <= e / &8`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min (min (h1 / &2) (min hk dy / &2)) (min ka kb)` THEN
    SUBGOAL_THEN `&0 < min (min (h1 / &2) (min hk dy / &2)) (min ka kb)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THEN GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THENL
     [USE_THEN "KA" MATCH_MP_TAC; USE_THEN "KBB" MATCH_MP_TAC] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `s1 = sqrt b - d1` THEN
  SUBGOAL_THEN `&0 < s1 /\ s1 < sqrt b /\ sqrt b - h1 < s1 /\ sqrt b - h1 / &2 <= s1`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "s1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* facts on [s1, sqrt b] *)
  SUBGOAL_THEN
   `!r. s1 <= r /\ r <= sqrt b
        ==> (phi:A->real^N)((gamma:real->A)(r pow 2)) IN cball(phi(gamma b),rho0) /\
            norm(phi(gamma(r pow 2)) - phi(gamma b)) < rho0 / &4`
  (LABEL_TAC "INB") THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    USE_THEN "DY" (MP_TAC o SPEC `lift r`) THEN
    REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DIST_LIFT] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[dist; IN_CBALL] THEN
    MP_TAC(ISPECL [`(phi:A->real^N)((gamma:real->A)(r pow 2))`; `(phi:A->real^N)((gamma:real->A) b)`]
                  NORM_SUB) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. s1 pow 2 <= u /\ u <= b
        ==> abs(real_integral (real_interval[s1 pow 2,u])
                  (p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                      (real->A->real^N^N)) tt gamma b)) < eta`
  (LABEL_TAC "SMALL") THENL
   [X_GEN_TAC `u:real` THEN STRIP_TAC THEN USE_THEN "KAP" MATCH_MP_TAC THEN
    SUBGOAL_THEN `abs(s1 pow 2 - b) < kap` ASSUME_TAC THENL
     [USE_THEN "HK" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= s1 pow 2` ASSUME_TAC THENL [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the displacement of the curve near the end *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                 `sqrt b - h1`; `sqrt b + h1`; `s1:real`; `c:real`; `Kp:real`; `eps:real`]
                P2A_END_DISP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN USE_THEN "H2" MATCH_MP_TAC THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `sqrt b pow 2 = b`)) THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN USE_THEN "H3" MATCH_MP_TAC THEN
      REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `sqrt b pow 2 = b`)) THEN
      MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`r:real`; `A:real^N`] THEN STRIP_TAC THEN
      USE_THEN "QB" (MP_TAC o SPECL [`r:real`; `(phi:A->real^N)((gamma:real->A)(r pow 2))`;
                                     `A:real^N`]) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "INB" (MP_TAC o SPEC `r:real`) THEN ASM_SIMP_TAC[];
      X_GEN_TAC `r:real` THEN STRIP_TAC THEN USE_THEN "KP" MATCH_MP_TAC THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "INB" (MP_TAC o SPEC `r:real`) THEN ASM_SIMP_TAC[];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      USE_THEN "SMALL" (MP_TAC o SPEC `s pow 2`) THEN ANTS_TAC THENL
       [CONJ_TAC THEN TRY(FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          concl th = `sqrt b pow 2 = b`))) THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      EXPAND_TAC "s1" THEN ASM_REWRITE_TAC[REAL_ARITH `s - (s - d) = d:real`]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  ABBREV_TAC `zeta = sqrt(eps * d1)` THEN
  SUBGOAL_THEN `&0 < zeta /\ zeta pow 2 = eps * d1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "zeta" THEN
    SUBGOAL_THEN `&0 < eps * d1` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm((phi:A->real^N)((gamma:real->A) b) - phi(gamma(s1 pow 2))) <= &2 * zeta`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN REWRITE_TAC[ARITH_EQ] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_MUL] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `norm((phi:A->real^N)((gamma:real->A) b) - phi(gamma(s1 pow 2))) pow 2 <=
                 &4 * eps * (sqrt b - s1)` THEN
    EXPAND_TAC "s1" THEN REWRITE_TAC[REAL_ARITH `s - (s - d) = d:real`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the open set of end points *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`;
                 `phi:A->real^N`; `tt - b`; `(gamma:real->A) b`; `min (rho0 / &4) zeta`]
                P2A_CHART_PREIMAGE_OPEN) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `O:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "OP")))) THEN
  EXISTS_TAC `O:A->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `q:A` THEN DISCH_TAC THEN
  USE_THEN "OP" (MP_TAC o SPEC `q:A`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REAL_LT_MIN; dist] THEN STRIP_TAC THEN
  (* the joined curve *)
  ABBREV_TAC `P1 = (phi:A->real^N)((gamma:real->A)(s1 pow 2))` THEN
  ABBREV_TAC `Pb = (phi:A->real^N)((gamma:real->A) b)` THEN
  ABBREV_TAC `pq = (phi:A->real^N) q` THEN
  SUBGOAL_THEN `norm((P1:real^N) - Pb) < rho0 / &4` ASSUME_TAC THENL
   [USE_THEN "INB" (MP_TAC o SPEC `s1:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s1 <= s /\ s <= sqrt b
        ==> (P1:real^N) + (inv(sqrt b - s1) * (s - s1)) % (pq - P1) IN cball(Pb,rho0)`
  (LABEL_TAC "ZIN") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN REWRITE_TAC[IN_CBALL; dist] THEN
    ABBREV_TAC `t = inv(sqrt b - s1) * (s - s1)` THEN
    SUBGOAL_THEN `&0 <= t /\ t <= &1` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "t" THEN
      SUBGOAL_THEN `&0 < sqrt b - s1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(Pb:real^N) - (P1 + t % (pq - P1)) = (&1 - t) % (Pb - P1) + t % (Pb - pq)`
    SUBST1_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs(&1 - t) * norm((Pb:real^N) - P1) + abs t * norm(Pb - pq)` THEN
    CONJ_TAC THENL [REWRITE_TAC[GSYM NORM_MUL; NORM_TRIANGLE]; ALL_TAC] THEN
    SUBGOAL_THEN `norm((Pb:real^N) - P1) <= rho0 /\ norm((Pb:real^N) - pq) <= rho0`
    STRIP_ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs(&1 - t) * rho0 + abs t * rho0` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[REAL_ABS_POS];
      ASM_SIMP_TAC[REAL_ARITH `&0 <= t /\ t <= &1 ==> abs(&1 - t) = &1 - t /\ abs t = t`] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `gamma:real->A`;
                 `W:A->bool`; `a':real`; `b'':real`; `U:A->bool`; `phi:A->real^N`;
                 `s1:real`; `sqrt b - h1`; `sqrt b + h1`; `pq:real^N`] P2A_JCURVE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      USE_THEN "H2" MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `sqrt b pow 2 = b`)) THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "cball")) (concl th) &&
        not(is_forall(concl th)))) THEN
      USE_THEN "ZIN" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2a_jcurve (gamma:real->A) U W (phi:A->real^N) s1 (sqrt b) pq b = q`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "pq" THEN MATCH_MP_TAC P2A_REGION_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                             (real->A->real^N^N)`; `a':real`; `b'':real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the length of the affine piece *)
  MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER W)`; `sqrt b - h1`; `sqrt b + h1`;
                 `p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) W b'' (U INTER W,phi:A->real^N)`;
                 `tt:real`; `P1:real^N`; `(pq:real^N) - P1`; `inv(sqrt b - s1)`;
                 `s1:real`; `sqrt b`; `cball(Pb:real^N,rho0)`; `Cg:real`; `Kp:real`]
                P2A_ZPIECE_LENGTH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THENL
     [MAP_EVERY X_GEN_TAC [`s:real`; `y:real^N`; `v:real^N`] THEN STRIP_TAC THEN
      USE_THEN "QB" (MP_TAC o SPECL [`s:real`; `y:real^N`; `v:real^N`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      MAP_EVERY X_GEN_TAC [`s:real`; `y:real^N`] THEN STRIP_TAC THEN
      USE_THEN "KP" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN
  (* the final estimate for the joined curve *)
  SUBGOAL_THEN
   `p2a_L_length (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)) tt
       (p2a_jcurve (gamma:real->A) U W (phi:A->real^N) s1 (sqrt b) (pq:real^N)) b <=
    p2a_L_length V tt gamma b + &3 * e / &4`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)`; `tt:real`; `x:A`; `gamma:real->A`; `b:real`;
                   `s1 pow 2`] P2A_LENGTH_SPLIT) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LT] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `sqrt b pow 2 = b`)) THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "SMALL" (MP_TAC o SPEC `b:real`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[REAL_LE_REFL] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `sqrt b pow 2 = b`)) THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      DISCH_TAC] THEN
    SUBGOAL_THEN `norm((pq:real^N) - P1) pow 2 <= &9 * eps * d1` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&3 * zeta) pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
        MATCH_MP_TAC(NORM_ARITH
         `!z:real^N. norm(y - z) < e /\ norm(z - w) <= &2 * e ==> norm(y - w) <= &3 * e`) THEN
        EXISTS_TAC `Pb:real^N` THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL [ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
        REWRITE_TAC[REAL_POW_MUL] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `sqrt b - s1 = d1` SUBST_ALL_TAC THENL
     [EXPAND_TAC "s1" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `d1 * (inv(&2) * Cg * norm(inv d1 % ((pq:real^N) - P1)) pow 2 + Kp) <=
      &9 * (Cg * eps) / &2 + Kp * d1`
    ASSUME_TAC THENL
     [REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < d ==> abs d = d`] THEN
      ABBREV_TAC `nn = norm((pq:real^N) - P1)` THEN
      SUBGOAL_THEN `d1 * (inv(&2) * Cg * (inv d1 * nn) pow 2 + Kp) =
                    inv(&2) * Cg * (nn pow 2 / d1) + Kp * d1` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < d1` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      SUBGOAL_THEN `nn pow 2 / d1 <= &9 * eps` ASSUME_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `Cg * (nn pow 2 / d1) <= Cg * (&9 * eps)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* smoothing *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`;
                 `p2a_jcurve (gamma:real->A) U W (phi:A->real^N) s1 (sqrt b) pq`; `e / &4`]
                P2A_SMOOTHING_GEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma':real->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `gamma':real->A` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC]);;

let P2A_LX_USC_FIX = prove
 (`!u:A->bool. P2A_LX_USC_FIX_STATEMENT u`,
  REWRITE_TAC[P2A_LX_USC_FIX_STATEMENT; GSYM P2A_VIEW_PROJ_3] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2A_LX_USC_GEN THEN ASM_REWRITE_TAC[]);;

let P2A_ROUTE_LX_USC_FIX = prove
 (`!u:A->bool. P2A_ROUTE_LX_USC_FIX_STATEMENT u`,
  REWRITE_TAC[P2A_ROUTE_LX_USC_FIX_STATEMENT; P2A_LX_USC_FIX]);;

