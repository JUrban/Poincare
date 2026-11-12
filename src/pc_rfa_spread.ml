(* ========================================================================= *)
(* Unit pc_rfa_spread: for the strong maximum principle, the local           *)
(* spreading of positivity for scalar supersolutions                         *)
(* dv/dt >= Lap v - B v, v >= 0, on a coordinate cylinder                    *)
(* [t1,t2] x cball(y,R) of a jointly smooth metric family: if v(t1) >= dl > 0 *)
(* on ball(y,rho) then v(t2) > 0 on ball(y,R) (RFA_SPREAD).  Comparison with *)
(* the expanding bump dl e^(-lam (t - t1)) max(0, 1 - |z - y|^2 / m(t))^k,   *)
(* m(t) = rho^2 + V (t - t1), a subsolution where it is positive, by the     *)
(* weak minimum principle on the compact cylinder.                           *)
(* ========================================================================= *)

needs "src/pc_rfa_slcalc.ml";;

prioritize_real();;
type_invention_error := true;;


(* ========================================================================= *)
(* The real inequality behind the subsolution property.                      *)
(* ========================================================================= *)

let RFA_BUMP_ALG = prove
 (`!sg m rho2 R2 V L C1 Gr L0 B lam k.
     &0 <= sg /\ sg < &1 /\ &0 < rho2 /\ rho2 <= m /\ m <= R2 /\ &0 <= V /\
     abs L <= C1 /\ &4 * sg * m <= L0 * Gr /\ &0 < L0 /\ &2 <= k /\
     ((V + C1) / rho2) * L0 * R2 <= &4 * (k - &1) /\
     B + &2 * k * ((V + C1) / rho2) <= lam
     ==> --lam * (&1 - sg) pow 2 + k * sg * (&1 - sg) * V / m <=
         --(k * (&1 - sg) * L / m) + k * (k - &1) * Gr / m pow 2 -
         B * (&1 - sg) pow 2`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `tau = &1 - sg` THEN ABBREV_TAC `P = (V + C1) / rho2` THEN
  SUBGOAL_THEN `&0 < tau /\ tau <= &1 /\ &0 < m /\ &0 < R2 /\ &0 <= C1 /\ &0 <= P`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    EXPAND_TAC "P" THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= k * tau` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `inv m <= inv rho2 /\ inv R2 <= inv m /\ &0 <= inv m` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `k * sg * tau * V / m <= k * tau * V / rho2` ASSUME_TAC THENL
   [SUBGOAL_THEN `k * sg * tau * V / m = ((k * tau) * V) * (sg * inv m) /\
                  k * tau * V / rho2 = ((k * tau) * V) * inv rho2`
    (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv m` THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `--(k * tau * C1 / rho2) <= --(k * tau * L / m)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_NEG2] THEN
    SUBGOAL_THEN `k * tau * L / m = (k * tau) * (L * inv m) /\
                  k * tau * C1 / rho2 = (k * tau) * (C1 * inv rho2)`
    (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs L * inv m` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= k * (k - &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&4 * sg * inv(L0 * R2) <= Gr / m pow 2` ASSUME_TAC THENL
   [SUBGOAL_THEN `Gr / m pow 2 = (L0 * Gr) * inv(L0 * m pow 2) /\
                  &4 * sg * inv(L0 * m) = (&4 * sg * m) * inv(L0 * m pow 2)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN UNDISCH_TAC `&0 < m` THEN UNDISCH_TAC `&0 < L0` THEN
      CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&4 * sg * inv(L0 * m)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `(k * (k - &1)) * (&4 * sg * inv(L0 * R2)) <=
                (k * (k - &1)) * (Gr / m pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `Q = (k * (k - &1)) * (&4 * sg * inv(L0 * R2))` THEN
  SUBGOAL_THEN `k * tau * P <= (lam - B) * tau pow 2 + Q` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= (lam - B) * tau pow 2 /\ &0 <= Q` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
        SUBGOAL_THEN `&0 <= &2 * k * P` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC];
        EXPAND_TAC "Q" THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[REAL_LE_INV_EQ] THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_CASES_TAC `tau <= inv(&2)` THENL
     [MATCH_MP_TAC(REAL_ARITH `x <= z /\ &0 <= y ==> x <= y + z`) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `k * inv(&2) * P` THEN CONJ_TAC THENL
       [SUBGOAL_THEN `k * tau * P = k * (tau * P) /\ k * inv(&2) * P = k * (inv(&2) * P)`
        (fun th -> REWRITE_TAC[th]) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      EXPAND_TAC "Q" THEN
      SUBGOAL_THEN `&0 < L0 * R2` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `inv(&2) <= sg` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `P <= &4 * (k - &1) * inv(L0 * R2)` ASSUME_TAC THENL
       [SUBGOAL_THEN `P = (P * L0 * R2) * inv(L0 * R2)` SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < L0 * R2` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
        SUBGOAL_THEN `&4 * (k - &1) * inv(L0 * R2) = (&4 * (k - &1)) * inv(L0 * R2)`
        SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
        ALL_TAC] THEN
      SUBGOAL_THEN `(k - &1) * inv(&2) <= (k - &1) * sg` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= inv(L0 * R2)` ASSUME_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]; ALL_TAC] THEN
      SUBGOAL_THEN `((k - &1) * inv(&2)) * inv(L0 * R2) <= ((k - &1) * sg) * inv(L0 * R2)`
      ASSUME_TAC THENL [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `k * inv(&2) * P <= k * (inv(&2) * &4 * (k - &1) * inv(L0 * R2))`
      ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `k * (inv(&2) * &4 * (k - &1) * inv(L0 * R2))` THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `k * (inv(&2) * &4 * (k - &1) * inv(L0 * R2)) =
                    k * (&4 * (((k - &1) * inv(&2)) * inv(L0 * R2))) /\
                    (k * (k - &1)) * &4 * sg * inv(L0 * R2) =
                    k * (&4 * (((k - &1) * sg) * inv(L0 * R2)))`
      (fun th -> REWRITE_TAC[th]) THENL [CONJ_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `x <= y /\ &0 <= z ==> x <= y + z`) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2 * k * P) * tau pow 2` THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN `(&2 * k * P) * tau pow 2 = (k * tau * P) * (&2 * tau)` SUBST1_TAC THENL
         [REAL_ARITH_TAC; ALL_TAC] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [SUBGOAL_THEN `k * tau * P = (k * tau) * P` SUBST1_TAC THENL
           [REAL_ARITH_TAC; ALL_TAC] THEN
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
          ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `k * tau * V / rho2 + k * tau * C1 / rho2 = k * tau * P` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `k * (k - &1) * Gr / m pow 2 = (k * (k - &1)) * (Gr / m pow 2)`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let RFA_SBUMP_INEQ = prove
 (`!c0 sg m rho2 R2 V L C1 Gr L0 B lam k.
     &0 < c0 /\ 2 <= k /\ &0 <= sg /\ sg < &1 /\ &0 < rho2 /\ rho2 <= m /\ m <= R2 /\
     &0 <= V /\ abs L <= C1 /\ &4 * sg * m <= L0 * Gr /\ &0 < L0 /\
     ((V + C1) / rho2) * L0 * R2 <= &4 * (&k - &1) /\
     B + &2 * &k * ((V + C1) / rho2) <= lam
     ==> c0 * (&1 - sg) pow (k - 1) * (--lam * (&1 - sg) + &k * sg * V / m) <=
         (--(c0 * &k * (&1 - sg) pow (k - 1) / m) * L +
          (c0 * &k * &(k - 1) * (&1 - sg) pow (k - 2) / m pow 2) * Gr) -
         B * (c0 * (&1 - sg) pow k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`sg:real`; `m:real`; `rho2:real`; `R2:real`; `V:real`; `L:real`;
                `C1:real`; `Gr:real`; `L0:real`; `B:real`; `lam:real`; `&k`]
         RFA_BUMP_ALG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `?j. k = SUC(SUC j)` (CHOOSE_THEN SUBST_ALL_TAC) THENL
   [EXISTS_TAC `k - 2` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `SUC(SUC j) - 1 = SUC j /\ SUC(SUC j) - 2 = j`] THEN
  REWRITE_TAC[real_pow; GSYM REAL_OF_NUM_SUC] THEN
  ABBREV_TAC `X = (&1 - sg) pow j` THEN
  SUBGOAL_THEN `&0 <= c0 * X` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "X" THEN MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_LMUL o CONJ (ASSUME `&0 <= c0 * X`)) THEN
  MATCH_MP_TAC(REAL_ARITH `a = c /\ b = d ==> a <= b ==> c <= d`) THEN
  CONJ_TAC THEN REAL_ARITH_TAC);;


(* ========================================================================= *)
(* Joint smoothness of the Laplacian of a fixed function, the                *)
(* squared distance, uniform bounds on compact sets, smooth powers.          *)
(* ========================================================================= *)

(* A time-independent smooth function composed with the space projection.  *)

let RFA_SMOOTH_SNDCART = prove
 (`!a b Om (f:real^N->real^P).
     open Om /\ smooth_map_on Om f
     ==> smooth_map_on (interval(lift a,lift b) PCROSS Om) (\w. f(sndcart w))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\w. (f:real^N->real^P) (sndcart w)) =
                f o (sndcart:real^(1,N)finite_sum->real^N)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `Om:real^N->bool` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; LRG_SMOOTH_LINEAR; LINEAR_SNDCART] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; SNDCART_PASTECART] THEN
  SIMP_TAC[]);;

(* The Laplacian of a fixed smooth function is jointly smooth in (t,z).    *)

let RFA_LLAP_JOINT_SMOOTH = prove
 (`!Om a b (G:real->real^N->real^N^N) (f:real^N->real).
     lrg_lsmooth Om a b G /\ smooth_map_on Om (\z. lift(f z))
     ==> smooth_map_on (interval(lift a,lift b) PCROSS Om)
           (\w. lift(llap (G (drop(fstcart w))) f (sndcart w)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
  REWRITE_TAC[RFA_LLAP_D2] THEN
  MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL THEN ASM_SIMP_TAC[LRG_LSMOOTH_GINV_ENTRY] THEN
  REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`a:real`; `b:real`; `Om:real^N->bool`;
                   `\z. lift(rfa_d2 (f:real^N->real) z (basis i) (basis j))`]
           RFA_SMOOTH_SNDCART) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[RFA_D2_AS_D1] THEN
    MATCH_MP_TAC RFA_D1_SMOOTH THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RFA_D1_SMOOTH THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`interval(lift a,lift b) PCROSS (Om:real^N->bool)`;
                   `\w. christoffel ((G:real->real^N->real^N^N) (drop(fstcart w)))
                                    (sndcart w) (basis i) (basis j)`; `k:num`]
                  SMOOTH_MAP_ON_LIFT_COMPONENT) THEN
    ASM_SIMP_TAC[LRG_LSMOOTH_CHRISTOFFEL];
    MP_TAC(ISPECL [`a:real`; `b:real`; `Om:real^N->bool`;
                   `\z. lift(rfa_d1 (f:real^N->real) z (basis k))`]
           RFA_SMOOTH_SNDCART) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RFA_D1_SMOOTH THEN ASM_REWRITE_TAC[]]);;

(* The squared distance |z - y|^2: derivative, smoothness, gradient bound. *)

let RFA_SQDIST_DERIV = prove
 (`!(y:real^N) z.
     ((\w. lift(norm(w - y) pow 2)) has_derivative
      (\h. &2 % lift((z - y) dot h))) (at z)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `(\w. lift(norm(w - y:real^N) pow 2)) = (\x. lift(norm x pow 2)) o (\w. w - y) /\
    (\h. &2 % lift((z - y:real^N) dot h)) = (\x. &2 % lift((z - y) dot x)) o (\h. h)`
  (fun th -> ONCE_REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN REWRITE_TAC[HAS_DERIVATIVE_SQNORM_AT] THEN
  SUBGOAL_THEN `(\h:real^N. h) = (\h. h - vec 0)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; VECTOR_SUB_RZERO]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
  REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST]);;

let RFA_SQDIST_D1 = prove
 (`!(y:real^N) z h. rfa_d1 (\w. norm(w - y) pow 2) z h = &2 * ((z - y) dot h)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfa_d1] THEN
  MP_TAC(ISPECL [`y:real^N`; `z:real^N`] RFA_SQDIST_DERIV) THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[DROP_CMUL; LIFT_DROP]);;

let RFA_SQDIST_SMOOTH = prove
 (`!U (y:real^N). open U ==> smooth_map_on U (\w. lift(norm(w - y) pow 2))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `\w:real^N. w - y`] SMOOTH_MAP_ON_NORM_POW2_OPEN) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST]);;

let RFA_METRIC_FIELD_ID = prove
 (`!U. open U ==> metric_field U (\z:real^N. mat 1)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[metric_field] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(vectorize:real^N^N->real^(N,N)finite_prod) o (\z:real^N. mat 1) =
                  (\z. vectorize(mat 1:real^N^N))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    REWRITE_TAC[SMOOTH_MAP_ON_CONST];
    REWRITE_TAC[TRANSP_MAT; MATRIX_VECTOR_MUL_LID] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[DOT_POS_LT]]);;

let RFA_LGRAD2_SQDIST_LOW = prove
 (`!U (G:real^N->real^N^N) y z L0.
     metric_field U G /\ z IN U /\ &0 < L0 /\
     (!x. x dot (G z ** x) <= L0 * (x dot x))
     ==> &4 * norm(z - y) pow 2 <= L0 * lgrad2 G (\w. norm(w - y) pow 2) z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `lgrad2 G (\w. norm(w - y) pow 2) (z:real^N) =
    (&2 % (z - y)) dot (matrix_inv(G z) ** (&2 % (z - y)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[lgrad2] THEN
    REWRITE_TAC[REWRITE_RULE[rfa_d1] RFA_SQDIST_D1] THEN
    MP_TAC(ISPECL [`matrix_inv((G:real^N->real^N^N) z)`;
                   `\i. &2 * ((z - y:real^N) dot basis i)`] LRG_QUADFORM_SUM) THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `(lambda i. &2 * ((z - y:real^N) dot basis i)):real^N = &2 % (z - y)`
    SUBST1_TAC THENL
     [SIMP_TAC[CART_EQ; LAMBDA_BETA; VECTOR_MUL_COMPONENT; DOT_BASIS];
      REFL_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `\z:real^N. mat 1:real^N^N`; `G:real^N->real^N^N`;
                 `z:real^N`; `L0:real`] LRG_METRIC_DUAL_COMPARE) THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `metric_field U (G:real^N->real^N^N)` THEN
    REWRITE_TAC[metric_field] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RFA_METRIC_FIELD_ID; MATRIX_VECTOR_MUL_LID; MATRIX_INV_I] THEN
  DISCH_THEN(MP_TAC o SPEC `&2 % (z - y:real^N)`) THEN
  REWRITE_TAC[DOT_LMUL; DOT_RMUL; GSYM NORM_POW_2] THEN REAL_ARITH_TAC);;

(* Bounds on compact sets, and smoothness of powers.                        *)

let RFA_CONT_COMPACT_BOUND = prove
 (`!(f:real^M->real^P) s.
     compact s /\ f continuous_on s ==> ?B. &0 < B /\ !x. x IN s ==> norm(f x) <= B`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `bounded(IMAGE (f:real^M->real^P) s)` MP_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE]]);;

let RFA_SMOOTH_LIFT_POW = prove
 (`!s (f:real^N->real) k.
     open s /\ smooth_map_on s (\x. lift(f x))
     ==> smooth_map_on s (\x. lift(f x pow k))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[real_pow; SMOOTH_MAP_ON_CONST] THEN
  MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL THEN ASM_SIMP_TAC[]);;

(* Uniform bounds over a compact subset of the space-time domain of a      *)
(* jointly smooth metric family: G <= L0 I, and |llap(G t) f| <= C1 for a  *)
(* fixed smooth f.                                                          *)

let RFA_LSMOOTH_QFORM_BOUND = prove
 (`!Om a b (G:real->real^N->real^N^N) K.
     lrg_lsmooth Om a b G /\ compact K /\
     K SUBSET interval(lift a,lift b) PCROSS Om
     ==> ?L0. &0 < L0 /\
              !t z x. pastecart (lift t) z IN K
                      ==> x dot (G t z ** x) <= L0 * (x dot x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
  MP_TAC(ISPECL
   [`\w:real^(1,N)finite_sum. (vectorize:real^N^N->real^(N,N)finite_prod)
        ((G:real->real^N->real^N^N) (drop(fstcart w)) (sndcart w))`;
    `K:real^(1,N)finite_sum->bool`] RFA_CONT_COMPACT_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `interval(lift a,lift b) PCROSS (Om:real^N->bool)` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `M:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`; `x:real^N`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (lift t) (z:real^N)`) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(x:real^N) * norm((G:real->real^N->real^N^N) t z ** x)` THEN
  REWRITE_TAC[NORM_CAUCHY_SCHWARZ] THEN
  REWRITE_TAC[DOT_SQUARE_NORM; REAL_POW_2] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_ARITH `M * (n * n) = n * (M * n)`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(vectorize((G:real->real^N->real^N^N) t z)) * norm(x:real^N)` THEN
  REWRITE_TAC[COMPATIBLE_NORM_VECTORIZE] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE]);;

let RFA_LSMOOTH_LLAP_BOUND = prove
 (`!Om a b (G:real->real^N->real^N^N) (f:real^N->real) K.
     lrg_lsmooth Om a b G /\ smooth_map_on Om (\z. lift(f z)) /\ compact K /\
     K SUBSET interval(lift a,lift b) PCROSS Om
     ==> ?C1. !t z. pastecart (lift t) z IN K ==> abs(llap (G t) f z) <= C1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\w:real^(1,N)finite_sum.
                    lift(llap ((G:real->real^N->real^N^N) (drop(fstcart w))) f (sndcart w))`;
                 `K:real^(1,N)finite_sum->bool`] RFA_CONT_COMPACT_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `interval(lift a,lift b) PCROSS (Om:real^N->bool)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MATCH_MP_TAC RFA_LLAP_JOINT_SMOOTH THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `M:real` THEN MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (lift t) (z:real^N)`) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; NORM_LIFT]);;


(* ========================================================================= *)
(* The expanding bump: continuity, time derivative, Laplacian,               *)
(* support and positivity, and the subsolution inequality.                  *)
(* ========================================================================= *)

(* The expanding bump: dl e^(-lam (t - t1)) max(0, 1 - |z - y|^2 / m(t))^k  *)
(* with m(t) = rho2 + V (t - t1), whose support grows with t.             *)

let rfa_sbump = new_definition
 `rfa_sbump (dl:real) (lam:real) (t1:real) (rho2:real) (V:real) (k:num)
            (y:real^N) (t:real) (z:real^N) =
    dl * exp(--(lam * (t - t1))) *
    max (&0) (&1 - norm(z - y) pow 2 / (rho2 + V * (t - t1))) pow k`;;

let RFA_REAL_CONT_DROP_FSTCART = prove
 (`!w0 (s:real^(1,N)finite_sum->bool).
     (\w. drop(fstcart w)) real_continuous (at w0 within s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS1] THEN
  SUBGOAL_THEN `lift o (\w:real^(1,N)finite_sum. drop(fstcart w)) = fstcart`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC LINEAR_CONTINUOUS_WITHIN THEN REWRITE_TAC[LINEAR_FSTCART]);;

let RFA_REAL_CONT_SQDIST_SNDCART = prove
 (`!w0 (s:real^(1,N)finite_sum->bool) (y:real^N).
     (\w. norm(sndcart w - y) pow 2) real_continuous (at w0 within s)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_POW THEN
  SUBGOAL_THEN `(\w:real^(1,N)finite_sum. norm(sndcart w - y:real^N)) =
                norm o (\w. sndcart w - y)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_CONTINUOUS_WITHIN_COMPOSE THEN
  REWRITE_TAC[REAL_CONTINUOUS_NORM_WITHIN] THEN
  MATCH_MP_TAC CONTINUOUS_SUB THEN REWRITE_TAC[CONTINUOUS_CONST] THEN
  MATCH_MP_TAC LINEAR_CONTINUOUS_WITHIN THEN REWRITE_TAC[LINEAR_SNDCART]);;

let RFA_SBUMP_CONT = prove
 (`!dl lam t1 rho2 V k (y:real^N).
     &0 < rho2 /\ &0 <= V
     ==> (\w. lift(rfa_sbump dl lam t1 rho2 V k y (drop(fstcart w)) (sndcart w)))
         continuous_on {w:real^(1,N)finite_sum | t1 <= drop(fstcart w)}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  X_GEN_TAC `w0:real^(1,N)finite_sum` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  ABBREV_TAC `S = {w:real^(1,N)finite_sum | t1 <= drop(fstcart w)}` THEN
  SUBGOAL_THEN
   `(\w. lift(rfa_sbump dl lam t1 rho2 V k (y:real^N) (drop(fstcart w)) (sndcart w))) =
    lift o (\w:real^(1,N)finite_sum.
              rfa_sbump dl lam t1 rho2 V k y (drop(fstcart w)) (sndcart w))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_CONTINUOUS_CONTINUOUS1; rfa_sbump] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_MUL THEN REWRITE_TAC[REAL_CONTINUOUS_CONST] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_MUL THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `(\w:real^(1,N)finite_sum. exp(--(lam * (drop(fstcart w) - t1)))) =
      exp o (\w. --(lam * (drop(fstcart w) - t1)))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_WITHIN_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_NEG THEN MATCH_MP_TAC REAL_CONTINUOUS_LMUL THEN
      MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN
      REWRITE_TAC[REAL_CONTINUOUS_CONST; RFA_REAL_CONT_DROP_FSTCART];
      MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      REWRITE_TAC[REAL_CONTINUOUS_AT_EXP]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_POW THEN MATCH_MP_TAC REAL_CONTINUOUS_MAX THEN
  REWRITE_TAC[REAL_CONTINUOUS_CONST] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN REWRITE_TAC[REAL_CONTINUOUS_CONST] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_DIV_WITHIN THEN
  REWRITE_TAC[RFA_REAL_CONT_SQDIST_SNDCART] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ADD THEN REWRITE_TAC[REAL_CONTINUOUS_CONST] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_LMUL THEN MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN
    REWRITE_TAC[REAL_CONTINUOUS_CONST; RFA_REAL_CONT_DROP_FSTCART];
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x = &0)`) THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < r /\ &0 <= v ==> &0 < r + v`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]);;

let RFA_SBUMP_POLY_DERIV = prove
 (`!dl lam t1 rho2 V k q t.
     ~(rho2 + V * (t - t1) = &0) /\ 1 <= k
     ==> ((\s. dl * exp(--(lam * (s - t1))) * (&1 - q / (rho2 + V * (s - t1))) pow k)
          has_real_derivative
          (dl * exp(--(lam * (t - t1))) *
           (&1 - q / (rho2 + V * (t - t1))) pow (k - 1) *
           (--lam * (&1 - q / (rho2 + V * (t - t1))) +
            &k * (q / (rho2 + V * (t - t1))) * V / (rho2 + V * (t - t1)))))
         (atreal t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(DISCH_ALL(REAL_DIFF_CONV
   `((\s. dl * exp(--(lam * (s - t1))) * (&1 - q / (rho2 + V * (s - t1))) pow k)
     has_real_derivative f') (atreal t)`)) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `?j. k = SUC j` (CHOOSE_THEN SUBST_ALL_TAC) THENL
   [EXISTS_TAC `k - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUC_SUB1; real_pow] THEN
  ABBREV_TAC `m = rho2 + V * (t - t1)` THEN
  ABBREV_TAC `E = exp(--(lam * (t - t1)))` THEN
  ABBREV_TAC `X = (&1 - q / m) pow j` THEN
  UNDISCH_TAC `~(m = &0)` THEN CONV_TAC REAL_FIELD);;

let RFA_SBUMP_TDERIV = prove
 (`!dl lam t1 rho2 V k (y:real^N) t z.
     1 <= k /\ &0 <= V /\ &0 < rho2 + V * (t - t1) /\
     norm(z - y) pow 2 < rho2 + V * (t - t1)
     ==> ((\s. rfa_sbump dl lam t1 rho2 V k y s z) has_real_derivative
          (dl * exp(--(lam * (t - t1))) *
           (&1 - norm(z - y) pow 2 / (rho2 + V * (t - t1))) pow (k - 1) *
           (--lam * (&1 - norm(z - y) pow 2 / (rho2 + V * (t - t1))) +
            &k * (norm(z - y) pow 2 / (rho2 + V * (t - t1))) * V /
            (rho2 + V * (t - t1)))))
         (atreal t)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `q = norm(z - y:real^N) pow 2` THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC `\s. dl * exp(--(lam * (s - t1))) * (&1 - q / (rho2 + V * (s - t1))) pow k` THEN
  EXISTS_TAC `(rho2 + V * (t - t1) - q) / (V + &1)` THEN
  SUBGOAL_THEN `&0 <= q` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN REWRITE_TAC[rfa_sbump] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `q < rho2 + V * (s - t1)` ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 < V + &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `V * abs(s - t) <= V * ((rho2 + V * (t - t1) - q) / (V + &1))`
      MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `V * ((rho2 + V * (t - t1) - q) / (V + &1)) < rho2 + V * (t - t1) - q`
      MP_TAC THENL
       [REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
        ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `V * (t - s) <= V * abs(s - t)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < rho2 + V * (s - t1)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= &1 - q / (rho2 + V * (s - t1))` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_SUB_LE; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> max (&0) x = x`];
    MATCH_MP_TAC RFA_SBUMP_POLY_DERIV THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let RFA_POW_PROFILE_DERIVS = prove
 (`!c0 m k. ~(m = &0) /\ 2 <= k
     ==> !x. ((\x. c0 * (&1 - x / m) pow k) has_real_derivative
              (--(c0 * &k * (&1 - x / m) pow (k - 1) / m))) (atreal x) /\
             ((\x. --(c0 * &k * (&1 - x / m) pow (k - 1) / m)) has_real_derivative
              (c0 * &k * &(k - 1) * (&1 - x / m) pow (k - 2) / m pow 2)) (atreal x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real` THEN CONJ_TAC THENL
   [MP_TAC(DISCH_ALL(REAL_DIFF_CONV
     `((\x. c0 * (&1 - x / m) pow k) has_real_derivative f') (atreal x)`)) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ABBREV_TAC `X = (&1 - x / m) pow (k - 1)` THEN
    UNDISCH_TAC `~(m = &0)` THEN CONV_TAC REAL_FIELD;
    MP_TAC(DISCH_ALL(REAL_DIFF_CONV
     `((\x. --(c0 * &k * (&1 - x / m) pow (k - 1) / m)) has_real_derivative f')
      (atreal x)`)) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `k - 1 - 1 = k - 2` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `X = (&1 - x / m) pow (k - 2)` THEN
    UNDISCH_TAC `~(m = &0)` THEN CONV_TAC REAL_FIELD]);;

let RFA_SBUMP_LLAP = prove
 (`!dl lam t1 rho2 V k (y:real^N) t z (G:real^N->real^N^N).
     2 <= k /\ &0 < rho2 + V * (t - t1) /\
     norm(z - y) pow 2 < rho2 + V * (t - t1)
     ==> llap G (rfa_sbump dl lam t1 rho2 V k y t) z =
         --(dl * exp(--(lam * (t - t1))) * &k *
            (&1 - norm(z - y) pow 2 / (rho2 + V * (t - t1))) pow (k - 1) /
            (rho2 + V * (t - t1))) * llap G (\w. norm(w - y) pow 2) z +
         (dl * exp(--(lam * (t - t1))) * &k * &(k - 1) *
          (&1 - norm(z - y) pow 2 / (rho2 + V * (t - t1))) pow (k - 2) /
          (rho2 + V * (t - t1)) pow 2) * lgrad2 G (\w. norm(w - y) pow 2) z`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `m = rho2 + V * (t - t1)` THEN
  ABBREV_TAC `c0 = dl * exp(--(lam * (t - t1)))` THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `llap G (\w. (\x. c0 * (&1 - x / m) pow k) (norm(w - y:real^N) pow 2)) z` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LLAP_LOCAL THEN EXISTS_TAC `ball(y:real^N,sqrt m)` THEN
    REWRITE_TAC[OPEN_BALL; IN_BALL] THEN
    SUBGOAL_THEN `!w:real^N. dist(y,w) < sqrt m <=> norm(w - y) pow 2 < m`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN REWRITE_TAC[dist; NORM_SUB] THEN
      MATCH_MP_TAC(MESON[] `(a <=> b) ==> (a <=> b)`) THEN
      EQ_TAC THEN DISCH_TAC THENL
       [SUBGOAL_THEN `norm(w - y:real^N) pow 2 < sqrt m pow 2` MP_TAC THENL
         [MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[NORM_POS_LE; ARITH_EQ];
          ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]];
        MATCH_MP_TAC REAL_LT_RSQRT THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[rfa_sbump] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= &1 - norm(w - y:real^N) pow 2 / m` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_SUB_LE; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> max (&0) x = x`] THEN
    EXPAND_TAC "c0" THEN REWRITE_TAC[REAL_MUL_ASSOC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^N)`; `(:real)`; `G:real^N->real^N^N`;
                 `\w:real^N. norm(w - y) pow 2`;
                 `\x. c0 * (&1 - x / m) pow k`;
                 `\x. --(c0 * &k * (&1 - x / m) pow (k - 1) / m)`;
                 `\x. c0 * &k * &(k - 1) * (&1 - x / m) pow (k - 2) / m pow 2`;
                 `z:real^N`] RFA_LLAP_COMPOSE) THEN
  REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [SIMP_TAC[RFA_SQDIST_SMOOTH; OPEN_UNIV]; ALL_TAC] THEN
    MP_TAC(ISPECL [`c0:real`; `m:real`; `k:num`] RFA_POW_PROFILE_DERIVS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "c0" THEN REWRITE_TAC[REAL_MUL_ASSOC]);;

let RFA_BALL_SQRT_IFF = prove
 (`!(y:real^N) z m. &0 < m ==> (z IN ball(y,sqrt m) <=> norm(z - y) pow 2 < m)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
  REWRITE_TAC[dist] THEN EQ_TAC THEN DISCH_TAC THENL
   [SUBGOAL_THEN `norm(z - y:real^N) pow 2 < sqrt m pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[NORM_POS_LE; ARITH_EQ];
      ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]];
    MATCH_MP_TAC REAL_LT_RSQRT THEN ASM_REWRITE_TAC[]]);;

let RFA_SBUMP_POS_LE = prove
 (`!dl lam t1 rho2 V k (y:real^N) t z.
     &0 <= dl ==> &0 <= rfa_sbump dl lam t1 rho2 V k y t z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_sbump] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
  MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC);;

let RFA_SBUMP_ZERO = prove
 (`!dl lam t1 rho2 V k (y:real^N) t z.
     1 <= k /\ &0 < rho2 + V * (t - t1) /\ rho2 + V * (t - t1) <= norm(z - y) pow 2
     ==> rfa_sbump dl lam t1 rho2 V k y t z = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_sbump] THEN
  SUBGOAL_THEN `max (&0) (&1 - norm(z - y:real^N) pow 2 / (rho2 + V * (t - t1))) = &0`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= &0 ==> max (&0) x = &0`) THEN
    ASM_SIMP_TAC[REAL_SUB_LE; REAL_ARITH `&1 - x <= &0 <=> &1 <= x`; REAL_LE_RDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_POW_ZERO; LE_1; ARITH_RULE `1 <= k ==> ~(k = 0)`] THEN
  REAL_ARITH_TAC);;

let RFA_SBUMP_POS = prove
 (`!dl lam t1 rho2 V k (y:real^N) t z.
     &0 < dl /\ &0 < rho2 + V * (t - t1) /\ norm(z - y) pow 2 < rho2 + V * (t - t1)
     ==> &0 < rfa_sbump dl lam t1 rho2 V k y t z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_sbump] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
  MATCH_MP_TAC REAL_POW_LT THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < x ==> &0 < max (&0) x`) THEN
  ASM_SIMP_TAC[REAL_SUB_LT; REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

let RFA_SBUMP_INIT = prove
 (`!dl lam t1 rho2 V k (y:real^N) z.
     &0 <= dl /\ &0 < rho2 ==> rfa_sbump dl lam t1 rho2 V k y t1 z <= dl`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[rfa_sbump; REAL_SUB_REFL; REAL_MUL_RZERO; REAL_ADD_RID;
              REAL_NEG_0; REAL_EXP_0; REAL_MUL_LID] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_POW_1_LE THEN
  SUBGOAL_THEN `&0 <= norm(z - y:real^N) pow 2 / rho2` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LE_POW_2; REAL_LT_IMP_LE];
    REAL_ARITH_TAC]);;

let RFA_SBUMP_SMOOTH_BALL = prove
 (`!dl lam t1 rho2 V k (y:real^N) t.
     &0 < rho2 + V * (t - t1)
     ==> smooth_map_on (ball(y,sqrt(rho2 + V * (t - t1))))
                       (\z. lift(rfa_sbump dl lam t1 rho2 V k y t z))`,
  REPEAT STRIP_TAC THEN ABBREV_TAC `m = rho2 + V * (t - t1)` THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `\z:real^N. lift((dl * exp(--(lam * (t - t1)))) *
                              (&1 - norm(z - y) pow 2 / m) pow k)` THEN
  REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:real^N` THEN ASM_SIMP_TAC[RFA_BALL_SQRT_IFF] THEN DISCH_TAC THEN
    REWRITE_TAC[rfa_sbump] THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `&0 <= &1 - norm(z - y:real^N) pow 2 / m` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_SUB_LE; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> max (&0) x = x`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
  REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC RFA_SMOOTH_LIFT_POW THEN
  REWRITE_TAC[OPEN_BALL; LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
  REWRITE_TAC[OPEN_BALL; SMOOTH_MAP_ON_CONST; real_div] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[LIFT_CMUL] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
  SIMP_TAC[OPEN_BALL; RFA_SQDIST_SMOOTH]);;

let RFA_LEFT_MIN_DERIV = prove
 (`!(f:real->real) D t e.
     (f has_real_derivative D) (atreal t) /\ &0 < e /\
     (!s. t - e < s /\ s < t ==> f t <= f s)
     ==> D <= &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `D:real`; `t:real`; `(:real)`; `D / &2`]
         RFA_LEFT_DERIV_BOUND) THEN
  ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_ATREAL_WITHIN; REAL_HALF; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `min d e / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t - min d e / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `h = min d e / &2` THEN
  SUBGOAL_THEN `&0 < h` ASSUME_TAC THENL [EXPAND_TAC "h" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `D / &2 * h < h * D` MP_TAC THENL
   [SUBGOAL_THEN `D / &2 * h = (h * D) / &2` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> x / &2 < x`) THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    REAL_ARITH_TAC]);;

let RFA_SBUMP_SUBSOL = prove
 (`!(G:real^N->real^N^N) dl lam t1 rho2 V k (y:real^N) t z R2 L0 C1 B Dw.
     &0 < dl /\ 2 <= k /\ &0 < rho2 /\ &0 <= V /\ t1 <= t /\
     rho2 + V * (t - t1) <= R2 /\
     norm(z - y) pow 2 < rho2 + V * (t - t1) /\
     abs(llap G (\w. norm(w - y) pow 2) z) <= C1 /\
     &4 * norm(z - y) pow 2 <= L0 * lgrad2 G (\w. norm(w - y) pow 2) z /\ &0 < L0 /\
     ((V + C1) / rho2) * L0 * R2 <= &4 * (&k - &1) /\
     B + &2 * &k * ((V + C1) / rho2) <= lam /\
     ((\s. rfa_sbump dl lam t1 rho2 V k y s z) has_real_derivative Dw) (atreal t)
     ==> Dw <= llap G (rfa_sbump dl lam t1 rho2 V k y t) z -
               B * rfa_sbump dl lam t1 rho2 V k y t z`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `m = rho2 + V * (t - t1)` THEN
  SUBGOAL_THEN `rho2 <= m /\ &0 < m` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN
    SUBGOAL_THEN `&0 <= V * (t - t1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`dl:real`; `lam:real`; `t1:real`; `rho2:real`; `V:real`; `k:num`;
                 `y:real^N`; `t:real`; `z:real^N`] RFA_SBUMP_TDERIV) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `Dw = dl * exp(--(lam * (t - t1))) *
         (&1 - norm(z - y:real^N) pow 2 / m) pow (k - 1) *
         (--lam * (&1 - norm(z - y) pow 2 / m) +
          &k * (norm(z - y) pow 2 / m) * V / m)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
    EXISTS_TAC `\s. rfa_sbump dl lam t1 rho2 V k (y:real^N) s z` THEN
    EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`dl:real`; `lam:real`; `t1:real`; `rho2:real`; `V:real`; `k:num`;
                 `y:real^N`; `t:real`; `z:real^N`; `G:real^N->real^N^N`]
         RFA_SBUMP_LLAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `rfa_sbump dl lam t1 rho2 V k (y:real^N) t z =
    dl * exp(--(lam * (t - t1))) * (&1 - norm(z - y) pow 2 / m) pow k`
  SUBST1_TAC THENL
   [REWRITE_TAC[rfa_sbump] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= &1 - norm(z - y:real^N) pow 2 / m` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_SUB_LE; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> max (&0) x = x`];
    ALL_TAC] THEN
  MP_TAC(SPECL [`dl * exp(--(lam * (t - t1)))`; `norm(z - y:real^N) pow 2 / m`; `m:real`;
                `rho2:real`; `R2:real`; `V:real`;
                `llap G (\w. norm(w - y:real^N) pow 2) z`; `C1:real`;
                `lgrad2 G (\w. norm(w - y:real^N) pow 2) z`; `L0:real`; `B:real`;
                `lam:real`; `k:num`] RFA_SBUMP_INEQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT];
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LE_POW_2; REAL_LT_IMP_LE];
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `&4 * norm(z - y:real^N) pow 2 / m * m = &4 * norm(z - y) pow 2`
      SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < m` THEN CONV_TAC REAL_FIELD; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  REAL_ARITH_TAC);;


(* ========================================================================= *)
(* The comparison on the cylinder and the spreading lemma.                   *)
(* ========================================================================= *)

let RFA_EX_DERIV = prove
 (`!(f:real->real) d net. (f has_real_derivative d) net
                          ==> ?d'. (f has_real_derivative d') net`,
  MESON_TAC[]);;

let RFA_SPREAD_CORE = prove
 (`!Om a b (G:real->real^N->real^N^N) (v:real->real^N->real) B y R t1 t2
    dl lam rho2 V k L0 C1.
     lrg_lsmooth Om a b G /\
     smooth_map_on (interval(lift a,lift b) PCROSS Om)
       (\w. lift(v (drop(fstcart w)) (sndcart w))) /\
     a < t1 /\ t1 < t2 /\ t2 < b /\ cball(y,R) SUBSET Om /\ &0 < dl /\ &0 < B /\
     &0 < rho2 /\ &0 <= V /\ rho2 + V * (t2 - t1) = R pow 2 /\ &0 < R /\
     2 <= k /\ &0 < L0 /\
     ((V + C1) / rho2) * L0 * R pow 2 <= &4 * (&k - &1) /\
     B + &2 * &k * ((V + C1) / rho2) <= lam /\
     (!t z x. t1 <= t /\ t <= t2 /\ z IN cball(y,R)
              ==> x dot (G t z ** x) <= L0 * (x dot x)) /\
     (!t z. t1 <= t /\ t <= t2 /\ z IN cball(y,R)
            ==> abs(llap (G t) (\w. norm(w - y) pow 2) z) <= C1) /\
     (!t z. t1 <= t /\ t <= t2 /\ z IN cball(y,R) ==> &0 <= v t z) /\
     (!t z. t1 <= t /\ t <= t2 /\ z IN cball(y,R)
            ==> ?D. ((\s. v s z) has_real_derivative D) (atreal t) /\
                    llap (G t) (v t) z - B * v t z <= D) /\
     (!z. z IN cball(y,R) ==> rfa_sbump dl lam t1 rho2 V k y t1 z <= v t1 z)
     ==> !t z. t1 <= t /\ t <= t2 /\ z IN cball(y,R)
               ==> rfa_sbump dl lam t1 rho2 V k y t z <= v t z`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "lsm vsm at1 t12 t2b cb dlp Bp r2p Vp mR Rp k2 L0p kc lamc qf lb vpos sup init" THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
  ABBREV_TAC `K = interval[lift t1,lift t2] PCROSS cball(y:real^N,R)` THEN
  ABBREV_TAC `uf = \w:real^(1,N)finite_sum.
                     (v:real->real^N->real) (drop(fstcart w)) (sndcart w) -
                     rfa_sbump dl lam t1 rho2 V k (y:real^N) (drop(fstcart w)) (sndcart w)` THEN
  SUBGOAL_THEN `compact(K:real^(1,N)finite_sum->bool) /\ ~(K = {})` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL; COMPACT_CBALL] THEN
    REWRITE_TAC[PCROSS_EQ_EMPTY; INTERVAL_EQ_EMPTY_1; CBALL_EQ_EMPTY; LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(K:real^(1,N)finite_sum->bool) SUBSET interval(lift a,lift b) PCROSS Om`
  ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC PCROSS_MONO THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(lift o (uf:real^(1,N)finite_sum->real)) continuous_on K` ASSUME_TAC THENL
   [EXPAND_TAC "uf" THEN REWRITE_TAC[o_DEF; LIFT_SUB] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `interval(lift a,lift b) PCROSS (Om:real^N->bool)` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `{w:real^(1,N)finite_sum | t1 <= drop(fstcart w)}` THEN
      ASM_SIMP_TAC[RFA_SBUMP_CONT] THEN EXPAND_TAC "K" THEN
      REWRITE_TAC[SUBSET; FORALL_IN_PCROSS; IN_ELIM_THM; FSTCART_PASTECART] THEN
      REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`uf:real^(1,N)finite_sum->real`; `K:real^(1,N)finite_sum->bool`]
         CONTINUOUS_ATTAINS_INF) THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "K" THEN
  REWRITE_TAC[EXISTS_IN_PCROSS; FORALL_IN_PCROSS; EXISTS_LIFT; FORALL_LIFT;
              IN_INTERVAL_1; LIFT_DROP] THEN
  EXPAND_TAC "uf" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  DISCH_THEN(X_CHOOSE_THEN `ts:real` (X_CHOOSE_THEN `zs:real^N`
    (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "min"))))) THEN
  SUBGOAL_THEN `&0 <= (v:real->real^N->real) ts zs - rfa_sbump dl lam t1 rho2 V k y ts zs`
  ASSUME_TAC THENL
   [ALL_TAC;
    MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN STRIP_TAC THEN
    USE_THEN "min" (MP_TAC o SPECL [`t:real`; `z:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `ms = rho2 + V * (ts - t1)` THEN
  SUBGOAL_THEN `rho2 <= ms /\ ms <= R pow 2 /\ &0 < ms` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ms" THEN
    SUBGOAL_THEN `&0 <= V * (ts - t1) /\ V * (ts - t1) <= V * (t2 - t1)` MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (v:real->real^N->real) ts zs` ASSUME_TAC THENL
   [USE_THEN "vpos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(zs - y:real^N) pow 2 < ms` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`dl:real`; `lam:real`; `t1:real`; `rho2:real`; `V:real`; `k:num`;
                   `y:real^N`; `ts:real`; `zs:real^N`] RFA_SBUMP_ZERO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `t1 < ts` ASSUME_TAC THENL
   [ASM_CASES_TAC `ts:real = t1` THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    USE_THEN "init" (MP_TAC o SPEC `zs:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `a < ts /\ ts < b` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field Om ((G:real->real^N->real^N^N) ts) /\ (zs:real^N) IN Om`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(zs:real^N) IN ball(y,sqrt ms) /\ ball(y,sqrt ms) SUBSET cball(y,R)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RFA_BALL_SQRT_IFF] THEN
    REWRITE_TAC[SUBSET; IN_CBALL] THEN X_GEN_TAC `z:real^N` THEN
    ASM_SIMP_TAC[RFA_BALL_SQRT_IFF] THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN
    MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `2` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on Om (\z. lift((v:real->real^N->real) ts z))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\w:real^(1,N)finite_sum.
                      lift((v:real->real^N->real) (drop(fstcart w)) (sndcart w))`;
                   `a:real`; `b:real`; `Om:real^N->bool`; `ts:real`]
           RFA_SMOOTH_MAP_ON_SLICE) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (ball(y:real^N,sqrt ms)) (\z. lift((v:real->real^N->real) ts z)) /\
    smooth_map_on (ball(y:real^N,sqrt ms))
      (\z. lift(rfa_sbump dl lam t1 rho2 V k y ts z))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `Om:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      EXPAND_TAC "ms" THEN MATCH_MP_TAC RFA_SBUMP_SMOOTH_BALL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= llap ((G:real->real^N->real^N^N) ts)
            (\z. (v:real->real^N->real) ts z - rfa_sbump dl lam t1 rho2 V k y ts z) zs`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_LLAP_LOCAL_MIN THEN
    MAP_EVERY EXISTS_TAC [`Om:real^N->bool`; `ball(y:real^N,sqrt ms)`] THEN
    BETA_TAC THEN ASM_REWRITE_TAC[OPEN_BALL; LIFT_SUB] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[OPEN_BALL]; ALL_TAC] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    USE_THEN "min" (MP_TAC o SPECL [`ts:real`; `z:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(y:real^N,sqrt ms)`; `(G:real->real^N->real^N^N) ts`;
                 `(v:real->real^N->real) ts`;
                 `rfa_sbump dl lam t1 rho2 V k (y:real^N) ts`; `zs:real^N`] RFA_LLAP_SUB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[OPEN_BALL]; DISCH_THEN SUBST_ALL_TAC] THEN
  USE_THEN "sup" (MP_TAC o SPECL [`ts:real`; `zs:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Dv:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`dl:real`; `lam:real`; `t1:real`; `rho2:real`; `V:real`; `k:num`;
                 `y:real^N`; `ts:real`; `zs:real^N`] RFA_SBUMP_TDERIV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Dw:real` ASSUME_TAC o MATCH_MP RFA_EX_DERIV) THEN
  SUBGOAL_THEN `Dv - Dw <= &0` ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_LEFT_MIN_DERIV THEN
    EXISTS_TAC `\s. (v:real->real^N->real) s zs - rfa_sbump dl lam t1 rho2 V k y s zs` THEN
    EXISTS_TAC `ts:real` THEN EXISTS_TAC `ts - t1` THEN
    ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_SUB; REAL_SUB_LT] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "min" (MP_TAC o SPECL [`s:real`; `zs:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(G:real->real^N->real^N^N) ts`; `dl:real`; `lam:real`; `t1:real`;
                 `rho2:real`; `V:real`; `k:num`; `y:real^N`; `ts:real`; `zs:real^N`;
                 `R pow 2`; `L0:real`; `C1:real`; `B:real`; `Dw:real`] RFA_SBUMP_SUBSOL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "lb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC RFA_LGRAD2_SQDIST_LOW THEN EXISTS_TAC `Om:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^N` THEN
    USE_THEN "qf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `&0 < B * (rfa_sbump dl lam t1 rho2 V k (y:real^N) ts zs - (v:real->real^N->real) ts zs)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let RFA_SPREAD = prove
 (`!Om a b (G:real->real^N->real^N^N) (v:real->real^N->real) B y rho R t1 t2 dl.
     lrg_lsmooth Om a b G /\
     smooth_map_on (interval(lift a,lift b) PCROSS Om)
       (\w. lift(v (drop(fstcart w)) (sndcart w))) /\
     a < t1 /\ t1 < t2 /\ t2 < b /\ &0 < rho /\ rho < R /\ cball(y,R) SUBSET Om /\
     &0 < dl /\
     (!t z. t1 <= t /\ t <= t2 /\ z IN cball(y,R) ==> &0 <= v t z) /\
     (!t z. t1 <= t /\ t <= t2 /\ z IN cball(y,R)
            ==> ?D. ((\s. v s z) has_real_derivative D) (atreal t) /\
                    llap (G t) (v t) z - B * v t z <= D) /\
     (!z. z IN ball(y,rho) ==> dl <= v t1 z)
     ==> !z. z IN ball(y,R) ==> &0 < v t2 z`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "lsm vsm at1 t12 t2b rhop rhoR cb dlp vpos sup init" THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
  ABBREV_TAC `B1 = max B (&1)` THEN
  SUBGOAL_THEN `&0 < B1 /\ B <= B1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "B1" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t z. t1 <= t /\ t <= t2 /\ z IN cball(y,R)
          ==> ?D. ((\s. (v:real->real^N->real) s z) has_real_derivative D) (atreal t) /\
                  llap ((G:real->real^N->real^N^N) t) (v t) z - B1 * v t z <= D`
  (LABEL_TAC "sup1") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "sup" (MP_TAC o SPECL [`t:real`; `z:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `D:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `D:real` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `B * (v:real->real^N->real) t z <= B1 * v t z` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "vpos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `K = interval[lift t1,lift t2] PCROSS cball(y:real^N,R)` THEN
  SUBGOAL_THEN
   `compact(K:real^(1,N)finite_sum->bool) /\
    K SUBSET interval(lift a,lift b) PCROSS Om /\
    (!t z. pastecart (lift t) z IN K <=> (t1 <= t /\ t <= t2) /\ z IN cball(y,R))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL; COMPACT_CBALL] THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    MATCH_MP_TAC PCROSS_MONO THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Om:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `K:real^(1,N)finite_sum->bool`] RFA_LSMOOTH_QFORM_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `L0:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`Om:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `\w:real^N. norm(w - y) pow 2`;
                 `K:real^(1,N)finite_sum->bool`] RFA_LSMOOTH_LLAP_BOUND) THEN
  ASM_SIMP_TAC[RFA_SQDIST_SMOOTH] THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real` ASSUME_TAC) THEN
  ABBREV_TAC `V = (R pow 2 - rho pow 2) / (t2 - t1)` THEN
  SUBGOAL_THEN `&0 <= V /\ rho pow 2 + V * (t2 - t1) = R pow 2 /\ &0 < rho pow 2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      REWRITE_TAC[REAL_SUB_LE] THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `~(t2 - t1 = &0)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  X_CHOOSE_TAC `n:num`
    (SPEC `((V + C1) / rho pow 2) * L0 * R pow 2 / &4` REAL_ARCH_SIMPLE) THEN
  ABBREV_TAC `k = n + 2` THEN
  SUBGOAL_THEN `2 <= k /\ ((V + C1) / rho pow 2) * L0 * R pow 2 <= &4 * (&k - &1)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    CONJ_TAC THENL [ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `lam = B1 + &2 * &k * ((V + C1) / rho pow 2)` THEN
  MP_TAC(ISPECL [`Om:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `v:real->real^N->real`; `B1:real`; `y:real^N`; `R:real`; `t1:real`;
                 `t2:real`; `dl:real`; `lam:real`; `rho pow 2`; `V:real`; `k:num`;
                 `L0:real`; `C1:real`] RFA_SPREAD_CORE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      ASM_CASES_TAC `(z:real^N) IN ball(y,rho)` THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `dl:real` THEN
        ASM_SIMP_TAC[RFA_SBUMP_INIT; REAL_LT_IMP_LE];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`dl:real`; `lam:real`; `t1:real`; `rho pow 2`; `V:real`; `k:num`;
                     `y:real^N`; `t1:real`; `z:real^N`] RFA_SBUMP_ZERO) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_ADD_RID] THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `~((z:real^N) IN ball(y,rho))` THEN
        REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
        REWRITE_TAC[dist] THEN REAL_ARITH_TAC;
        DISCH_THEN SUBST1_TAC THEN USE_THEN "vpos" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "cmp") THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `rfa_sbump dl lam t1 (rho pow 2) V k (y:real^N) t2 z` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RFA_SBUMP_POS THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[NORM_POS_LE; ARITH_EQ] THEN
    UNDISCH_TAC `(z:real^N) IN ball(y,R)` THEN
    REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist];
    USE_THEN "cmp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_CBALL] THEN UNDISCH_TAC `(z:real^N) IN ball(y,R)` THEN
    REWRITE_TAC[IN_BALL] THEN REAL_ARITH_TAC]);;

