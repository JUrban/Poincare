(* ========================================================================= *)
(* pc_p3e_theta: a smooth radial diffeomorphism p3e_theta g0 A0 of the model *)
(* region of the standard initial metric, the set of x with                  *)
(* -c < A0 + 4 - p3_std_dist g0 x (c = sqrt 2 log 2), onto ball(vec 0,2).    *)
(* On the collar -c < s1 < 0 (s1 = A0 + 4 - d(0,x)) it is the inversion      *)
(* z/|z|^2 of z = p3_std_nc g0 A0 x, and it maps the cap s1 >= 0 onto        *)
(* cball(vec 0,1).  Used by step S4 of the proof of MT Lemma 15.11: the      *)
(* model parametrization of a new cap is the cap chart composed with         *)
(* p3e_theta.                                                                *)
(* Radial profile: theta(r) = chi(r) k r + (1 - chi(r)) f(r), with          *)
(* f(r) = exp((rho(r) - A0 - 4)/sqrt 2) (rho = p3s_rad_rho g0, so that      *)
(* f(|x|) x/|x| is the inversion of p3_std_nc g0 A0 x), chi = p2c_std_chi   *)
(* (r0/4) (1 near 0, 0 beyond r0/2, r0 = rho^-1(A0 + 4)) and k = f(0)/rc    *)
(* (rc = rho^-1(A0 + 4 + c)), so that k r <= f(r) on [0,rc] and theta' > 0. *)
(* ========================================================================= *)

needs "src/pc_p3_s13met.ml";;
needs "src/pc_smt_radial.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The profile f = p3e_tf, the radii r0 < rc (s1 = 0 and                     *)
(* s1 = -c) and the slope k = p3e_tk; f(r0) = 1, f(rc) = 2, f strictly     *)
(* increasing, k r <= f(r) on [0,rc], and the derivative of f.             *)
(* ------------------------------------------------------------------------- *)

let p3e_tf = new_definition
 `p3e_tf (g0:real^3->real^3^3) (A0:real) (r:real) =
    exp((p3s_rad_rho g0 r - (A0 + &4)) / sqrt(&2))`;;

let p3e_tr0 = new_definition
 `p3e_tr0 (g0:real^3->real^3^3) (A0:real) = p3s_rad_rinv g0 (A0 + &4)`;;

let p3e_trc = new_definition
 `p3e_trc (g0:real^3->real^3^3) (A0:real) =
    p3s_rad_rinv g0 (A0 + &4 + sqrt(&2) * log(&2))`;;

let p3e_tk = new_definition
 `p3e_tk (g0:real^3->real^3^3) (A0:real) = p3e_tf g0 A0 (&0) / p3e_trc g0 A0`;;

let P3E_SQRT2_LOG2 = prove
 (`&0 < sqrt(&2) /\ &0 < log(&2) /\ &0 < sqrt(&2) * log(&2)`,
  SUBGOAL_THEN `&0 < sqrt(&2) /\ &0 < log(&2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC SQRT_POS_LT; MATCH_MP_TAC LOG_POS_LT] THEN
    REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LT_MUL]]);;

let P3E_TF_POS = prove
 (`!g0 A0 r. &0 < p3e_tf g0 A0 r`,
  REWRITE_TAC[p3e_tf; REAL_EXP_POS_LT]);;

let P3E_TF_STRICT = prove
 (`!g0 A0 r1 r2. p3_std_initial g0 A0 /\ &0 <= r1 /\ r1 < r2
                 ==> p3e_tf g0 A0 r1 < p3e_tf g0 A0 r2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3e_tf; REAL_EXP_MONO_LT] THEN
  SIMP_TAC[REAL_LT_DIV2_EQ; P3E_SQRT2_LOG2] THEN
  MATCH_MP_TAC(REAL_ARITH `a < b ==> a - c < b - c`) THEN
  MATCH_MP_TAC P3S_RHO_STRICT THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[]);;

let P3E_TF_MONO = prove
 (`!g0 A0 r1 r2. p3_std_initial g0 A0 /\ &0 <= r1 /\ r1 <= r2
                 ==> p3e_tf g0 A0 r1 <= p3e_tf g0 A0 r2`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `r1:real = r2` THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
  MATCH_MP_TAC P3E_TF_STRICT THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P3E_TR_FACTS = prove
 (`!g0 A0. p3_std_initial g0 A0
           ==> &0 < A0 /\ &0 < p3e_tr0 g0 A0 /\ p3e_tr0 g0 A0 < p3e_trc g0 A0 /\
               p3s_rad_rho g0 (p3e_tr0 g0 A0) = A0 + &4 /\
               p3s_rad_rho g0 (p3e_trc g0 A0) = A0 + &4 + sqrt(&2) * log(&2) /\
               p3e_tf g0 A0 (p3e_tr0 g0 A0) = &1 /\
               p3e_tf g0 A0 (p3e_trc g0 A0) = &2 /\
               p3e_tf g0 A0 (&0) = exp(--((A0 + &4) / sqrt(&2)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < A0` ASSUME_TAC THENL
   [ASM_MESON_TAC[p3_std_initial]; ALL_TAC] THEN
  MP_TAC P3E_SQRT2_LOG2 THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `A0 + &4`] P3S_RINV_FACTS) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `A0 + &4 + sqrt(&2) * log(&2)`]
    P3S_RINV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[p3e_tr0; p3e_trc; p3e_tf] THEN
  SUBGOAL_THEN
   `p3s_rad_rinv g0 (A0 + &4) < p3s_rad_rinv g0 (A0 + &4 + sqrt(&2) * log(&2))`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `p3s_rad_rinv g0 (A0 + &4)`;
                  `p3s_rad_rinv g0 (A0 + &4 + sqrt(&2) * log(&2))`] P3S_RHO_LT_EQ) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL; real_div; REAL_MUL_LZERO; REAL_EXP_0] THEN
  REWRITE_TAC[P3S_RHO_0; REAL_SUB_LZERO; REAL_MUL_LNEG] THEN
  REWRITE_TAC[REAL_ARITH `(a + b + s * l) - (a + b) = l * s`] THEN
  ASM_SIMP_TAC[GSYM REAL_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_MUL_RID] THEN
  MATCH_MP_TAC EXP_LOG THEN REAL_ARITH_TAC);;

let P3E_TK_FACTS = prove
 (`!g0 A0. p3_std_initial g0 A0
           ==> &0 < p3e_tk g0 A0 /\
               !r. &0 <= r /\ r <= p3e_trc g0 A0 ==> p3e_tk g0 A0 * r <= p3e_tf g0 A0 r`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_TR_FACTS) THEN
  SUBGOAL_THEN `&0 < p3e_trc g0 A0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[p3e_tk] THEN ASM_SIMP_TAC[REAL_LT_DIV; P3E_TF_POS]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `p3e_tf g0 A0 (&0)` THEN CONJ_TAC THENL
   [REWRITE_TAC[p3e_tk; real_div; GSYM REAL_MUL_ASSOC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    SIMP_TAC[P3E_TF_POS; REAL_LT_IMP_LE] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC P3E_TF_MONO THEN ASM_REWRITE_TAC[REAL_LE_REFL]]);;

let P3E_TF_DERIV = prove
 (`!g0 A0 r. p3_std_initial g0 A0 /\ &0 < r
             ==> (p3e_tf g0 A0 has_real_derivative
                  p3e_tf g0 A0 r * sqrt(p3s_rad_a g0 r) / sqrt(&2)) (atreal r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r:real`] P3S_RHO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `((\u. (p3s_rad_rho g0 u - (A0 + &4)) / sqrt(&2)) has_real_derivative
     sqrt(p3s_rad_a g0 r) / sqrt(&2)) (atreal r)`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_CDIV_ATREAL THEN
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM REAL_SUB_RZERO] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN
    ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST; ETA_AX];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (CONJUNCT2(SPEC_ALL(MATCH_MP
    HAS_REAL_DERIVATIVE_CHAIN_UNIV
    (GEN `x:real` (SPEC `x:real` HAS_REAL_DERIVATIVE_EXP)))))) THEN
  REWRITE_TAC[GSYM p3e_tf; ETA_AX] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[p3e_tf] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The blended profile theta = p3e_tth: theta(r) = k r for                   *)
(* r <= r0/4, theta = f for r >= r0/2, theta(0) = 0, theta(r0) = 1,          *)
(* theta(rc) = 2; theta is strictly increasing on [0,rc], smooth on r > 0,  *)
(* with a positive derivative on (0,rc].                                    *)
(* ------------------------------------------------------------------------- *)

let p3e_tth = new_definition
 `p3e_tth (g0:real^3->real^3^3) (A0:real) (r:real) =
    p2c_std_chi (p3e_tr0 g0 A0 / &4) r * p3e_tk g0 A0 * r +
    (&1 - p2c_std_chi (p3e_tr0 g0 A0 / &4) r) * p3e_tf g0 A0 r`;;

let P3E_TTH_SMALL = prove
 (`!g0 A0 r. p3_std_initial g0 A0 /\ r <= p3e_tr0 g0 A0 / &4
             ==> p3e_tth g0 A0 r = p3e_tk g0 A0 * r`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_TR_FACTS) THEN
  REWRITE_TAC[p3e_tth] THEN
  MP_TAC(SPECL [`p3e_tr0 g0 A0 / &4`; `r:real`] P2C_STD_CHI_1) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REAL_ARITH_TAC);;

let P3E_TTH_LARGE = prove
 (`!g0 A0 r. p3_std_initial g0 A0 /\ p3e_tr0 g0 A0 / &2 <= r
             ==> p3e_tth g0 A0 r = p3e_tf g0 A0 r`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_TR_FACTS) THEN
  REWRITE_TAC[p3e_tth] THEN
  MP_TAC(SPECL [`p3e_tr0 g0 A0 / &4`; `r:real`] P2C_STD_CHI_0) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REAL_ARITH_TAC);;

let P3E_TTH_VALUES = prove
 (`!g0 A0. p3_std_initial g0 A0
           ==> p3e_tth g0 A0 (&0) = &0 /\
               p3e_tth g0 A0 (p3e_tr0 g0 A0) = &1 /\
               p3e_tth g0 A0 (p3e_trc g0 A0) = &2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_TR_FACTS) THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `&0`] P3E_TTH_SMALL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `p3e_tr0 g0 A0`] P3E_TTH_LARGE);
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `p3e_trc g0 A0`] P3E_TTH_LARGE)] THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]));;

let P3E_TTH_STRICT = prove
 (`!g0 A0 r1 r2. p3_std_initial g0 A0 /\ &0 <= r1 /\ r1 < r2 /\ r2 <= p3e_trc g0 A0
                 ==> p3e_tth g0 A0 r1 < p3e_tth g0 A0 r2`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_TR_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_TK_FACTS) THEN
  REWRITE_TAC[p3e_tth] THEN
  ABBREV_TAC `c1 = p2c_std_chi (p3e_tr0 g0 A0 / &4) r1` THEN
  ABBREV_TAC `c2 = p2c_std_chi (p3e_tr0 g0 A0 / &4) r2` THEN
  ABBREV_TAC `k = p3e_tk g0 A0` THEN
  SUBGOAL_THEN `&0 <= c2 /\ c2 <= c1 /\ c1 <= &1` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["c1"; "c2"] THEN
    REWRITE_TAC[P2C_STD_CHI_BOUNDS] THEN MATCH_MP_TAC P2C_STD_CHI_MONO THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `k * r1 < k * r2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_LMUL_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `p3e_tf g0 A0 r1 < p3e_tf g0 A0 r2` ASSUME_TAC THENL
   [MATCH_MP_TAC P3E_TF_STRICT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `k * r1 <= p3e_tf g0 A0 r1` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `F1 = p3e_tf g0 A0 r1` THEN ABBREV_TAC `F2 = p3e_tf g0 A0 r2` THEN
  ABBREV_TAC `K1 = k * r1` THEN ABBREV_TAC `K2 = k * r2` THEN
  SUBGOAL_THEN `&0 <= (c1 - c2) * (F1 - K1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c2 * (K2 - K1) + (&1 - c2) * (F2 - F1)` ASSUME_TAC THENL
   [ASM_CASES_TAC `c2 = &0` THENL
     [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `c1 * k * r1 = c1 * K1 /\ c2 * k * r2 = c2 * K2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["K1"; "K2"] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P3E_TTH_MONO = prove
 (`!g0 A0 r1 r2. p3_std_initial g0 A0 /\ &0 <= r1 /\ r1 <= r2 /\ r2 <= p3e_trc g0 A0
                 ==> p3e_tth g0 A0 r1 <= p3e_tth g0 A0 r2`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `r1:real = r2` THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
  MATCH_MP_TAC P3E_TTH_STRICT THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P3E_TTH_RANGE = prove
 (`!g0 A0 r. p3_std_initial g0 A0 /\ &0 <= r /\ r < p3e_trc g0 A0
             ==> &0 <= p3e_tth g0 A0 r /\ p3e_tth g0 A0 r < &2 /\
                 (&0 < r ==> &0 < p3e_tth g0 A0 r) /\
                 (r <= p3e_tr0 g0 A0 <=> p3e_tth g0 A0 r <= &1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_TR_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_TTH_VALUES) THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `p3e_tth g0 A0 (&0) = &0` THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
    MATCH_MP_TAC P3E_TTH_MONO THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `p3e_tth g0 A0 (p3e_trc g0 A0) = &2` THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    MATCH_MP_TAC P3E_TTH_STRICT THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    DISCH_TAC THEN UNDISCH_TAC `p3e_tth g0 A0 (&0) = &0` THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
    MATCH_MP_TAC P3E_TTH_STRICT THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `p3e_tth g0 A0 (p3e_tr0 g0 A0) = &1` THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
    EQ_TAC THENL
     [DISCH_TAC THEN MATCH_MP_TAC P3E_TTH_MONO THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[REAL_NOT_LE] THEN
      DISCH_TAC THEN MATCH_MP_TAC P3E_TTH_STRICT THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Derivative, smoothness and continuity of theta.                           *)
(* theta'(r) = chi k + (1 - chi) f' - chi' (f - k r) > 0 on (0,rc], since    *)
(* chi' <= 0 and k r <= f(r); theta = k r on r < r0/4.                      *)
(* ------------------------------------------------------------------------- *)

let P3E_TTH_DERIV = prove
 (`!g0 A0 r. p3_std_initial g0 A0 /\ &0 < r
     ==> (p3e_tth g0 A0 has_real_derivative
          (p2c_std_chi (p3e_tr0 g0 A0 / &4) r * p3e_tk g0 A0 +
           (&1 - p2c_std_chi (p3e_tr0 g0 A0 / &4) r) *
             (p3e_tf g0 A0 r * sqrt(p3s_rad_a g0 r) / sqrt(&2)) +
           --(real_derivative (p2c_std_chi (p3e_tr0 g0 A0 / &4)) r) *
             (p3e_tf g0 A0 r - p3e_tk g0 A0 * r))) (atreal r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(DISCH_ALL(p3s_rdiffc
    [SPEC `p3e_tr0 g0 A0 / &4` P2C_STD_CHI_DERIV;
     GEN `r:real` (UNDISCH(SPEC_ALL(REWRITE_RULE[IMP_CONJ]
       (SPECL [`g0:real^3->real^3^3`; `A0:real`] P3E_TF_DERIV))))]
    `((\r. p2c_std_chi (p3e_tr0 g0 A0 / &4) r * p3e_tk g0 A0 * r +
           (&1 - p2c_std_chi (p3e_tr0 g0 A0 / &4) r) * p3e_tf (g0:real^3->real^3^3) A0 r)
      has_real_derivative f') (atreal r)`)) THEN
  ASM_REWRITE_TAC[GSYM p3e_tth; ETA_AX] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let P3E_TTH_DERIV_POS = prove
 (`!g0 A0 r. p3_std_initial g0 A0 /\ &0 < r /\ r <= p3e_trc g0 A0
     ==> &0 < p2c_std_chi (p3e_tr0 g0 A0 / &4) r * p3e_tk g0 A0 +
              (&1 - p2c_std_chi (p3e_tr0 g0 A0 / &4) r) *
                (p3e_tf g0 A0 r * sqrt(p3s_rad_a g0 r) / sqrt(&2)) +
              --(real_derivative (p2c_std_chi (p3e_tr0 g0 A0 / &4)) r) *
                (p3e_tf g0 A0 r - p3e_tk g0 A0 * r)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_TR_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_TK_FACTS) THEN
  MP_TAC(SPECL [`p3e_tr0 g0 A0 / &4`; `r:real`] P2C_STD_CHI_BOUNDS) THEN
  MP_TAC(SPECL [`p3e_tr0 g0 A0 / &4`; `r:real`] P2C_STD_CHI_DERIV_LE) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < p3e_tf g0 A0 r * sqrt(p3s_rad_a g0 r) / sqrt(&2)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[P3E_TF_POS] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[P3E_SQRT2_LOG2] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r:real`] P3S_RS_AB_SQRT) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= p3e_tf g0 A0 r - p3e_tk g0 A0 * r` MP_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `a <= b ==> &0 <= b - a`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `&0 < p3e_tk g0 A0` THEN
  ABBREV_TAC `c = p2c_std_chi (p3e_tr0 g0 A0 / &4) r` THEN
  ABBREV_TAC `c' = real_derivative (p2c_std_chi (p3e_tr0 g0 A0 / &4)) r` THEN
  ABBREV_TAC `fd = p3e_tf g0 A0 r * sqrt(p3s_rad_a g0 r) / sqrt(&2)` THEN
  ABBREV_TAC `h = p3e_tf g0 A0 r - p3e_tk g0 A0 * r` THEN
  ABBREV_TAC `k = p3e_tk g0 A0` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= --c' * h` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c * k + (&1 - c) * fd` ASSUME_TAC THENL
   [ASM_CASES_TAC `c = &0` THENL
     [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P3E_TF_SMOOTH = prove
 (`!g0 A0. p3_std_initial g0 A0
           ==> smooth_map_on {s | &0 < drop s} (lift o p3e_tf g0 A0 o drop)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `p3e_tf g0 A0 = (\t. exp((p3s_rad_rho g0 t - (A0 + &4)) * inv(sqrt(&2))))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; p3e_tf; real_div]; ALL_TAC] THEN
  MATCH_MP_TAC P2C_S1_EXP THEN REWRITE_TAC[P2C_OPEN_DROP_GT] THEN
  MATCH_MP_TAC P2C_S1_MUL THEN REWRITE_TAC[P2C_OPEN_DROP_GT; P2C_S1_CONST] THEN
  MATCH_MP_TAC P2C_S1_SUB THEN REWRITE_TAC[P2C_OPEN_DROP_GT; P2C_S1_CONST] THEN
  REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC P3S_RHO_SMOOTH THEN
  EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[]);;

let P3E_TTH_SMOOTH = prove
 (`!g0 A0. p3_std_initial g0 A0
           ==> smooth_map_on {s | &0 < drop s} (lift o p3e_tth g0 A0 o drop)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `p3e_tth g0 A0 =
    (\t. p2c_std_chi (p3e_tr0 g0 A0 / &4) t * p3e_tk g0 A0 * t +
         (&1 - p2c_std_chi (p3e_tr0 g0 A0 / &4) t) * p3e_tf g0 A0 t)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; p3e_tth]; ALL_TAC] THEN
  MATCH_MP_TAC P2C_S1_ADD THEN REWRITE_TAC[P2C_OPEN_DROP_GT] THEN CONJ_TAC THEN
  MATCH_MP_TAC P2C_S1_MUL THEN REWRITE_TAC[P2C_OPEN_DROP_GT] THEN CONJ_TAC THENL
   [REWRITE_TAC[ETA_AX] THEN SIMP_TAC[P2C_STD_CHI_SMOOTH; P2C_OPEN_DROP_GT];
    MATCH_MP_TAC P2C_S1_MUL THEN
    REWRITE_TAC[P2C_OPEN_DROP_GT; P2C_S1_CONST; P2C_S1_ID];
    MATCH_MP_TAC P2C_S1_SUB THEN
    REWRITE_TAC[P2C_OPEN_DROP_GT; P2C_S1_CONST; ETA_AX] THEN
    SIMP_TAC[P2C_STD_CHI_SMOOTH; P2C_OPEN_DROP_GT];
    REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC P3E_TF_SMOOTH THEN ASM_REWRITE_TAC[]]);;

let P3E_TTH_DERIV_SMALL = prove
 (`!g0 A0 r. p3_std_initial g0 A0 /\ r < p3e_tr0 g0 A0 / &4
             ==> (p3e_tth g0 A0 has_real_derivative p3e_tk g0 A0) (atreal r)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  MAP_EVERY EXISTS_TAC [`\u. p3e_tk g0 A0 * u`; `p3e_tr0 g0 A0 / &4 - r`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `u:real` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN BETA_TAC THEN
    MATCH_MP_TAC P3E_TTH_SMALL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_ID]]);;

let P3E_TTH_DIFF = prove
 (`!g0 A0 x. p3_std_initial g0 A0
             ==> ?d. (p3e_tth g0 A0 has_real_derivative d) (atreal x)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_TR_FACTS) THEN
  ASM_CASES_TAC `x < p3e_tr0 g0 A0 / &4` THENL
   [EXISTS_TAC `p3e_tk g0 A0` THEN MATCH_MP_TAC P3E_TTH_DERIV_SMALL THEN
    ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real`] P3E_TTH_DERIV) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; MESON_TAC[]]]);;

let P3E_TTH_CONT = prove
 (`!g0 A0 s. p3_std_initial g0 A0 ==> p3e_tth g0 A0 real_continuous_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
  REWRITE_TAC[real_differentiable_on] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real`] P3E_TTH_DIFF) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[HAS_REAL_DERIVATIVE_ATREAL_WITHIN]);;

(* ------------------------------------------------------------------------- *)
(* The inverse profile p3e_tthi of theta on [0,2): values,                   *)
(* uniqueness, tthi(s) = s/k near 0, and smoothness on (0,2) by the 1-D      *)
(* inverse function theorem (theta' > 0).                                   *)
(* ------------------------------------------------------------------------- *)

let p3e_tthi = new_definition
 `p3e_tthi (g0:real^3->real^3^3) (A0:real) (s:real) =
    @r. &0 <= r /\ r < p3e_trc g0 A0 /\ p3e_tth g0 A0 r = s`;;

let P3E_OPEN_DROP_INTERVAL = prove
 (`!a b. open {x:real^1 | a < drop x /\ drop x < b}`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SET_RULE `{x:real^1 | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
  MATCH_MP_TAC OPEN_INTER THEN REWRITE_TAC[P2C_OPEN_DROP_GT; P2C_OPEN_DROP_LT]);;

let P3E_TTHI = prove
 (`!g0 A0 s. p3_std_initial g0 A0 /\ &0 <= s /\ s < &2
             ==> &0 <= p3e_tthi g0 A0 s /\ p3e_tthi g0 A0 s < p3e_trc g0 A0 /\
                 p3e_tth g0 A0 (p3e_tthi g0 A0 s) = s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[p3e_tthi] THEN
  CONV_TAC SELECT_CONV THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_TR_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_TTH_VALUES) THEN
  MP_TAC(ISPECL [`p3e_tth g0 A0`; `&0`; `p3e_trc g0 A0`; `s:real`]
    REAL_IVT_INCREASING) THEN
  ASM_SIMP_TAC[P3E_TTH_CONT; IN_REAL_INTERVAL] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[REAL_LT_LE] THEN
  DISCH_TAC THEN UNDISCH_TAC `p3e_tth g0 A0 r = s` THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

let P3E_TTHI_UNIQUE = prove
 (`!g0 A0 r. p3_std_initial g0 A0 /\ &0 <= r /\ r < p3e_trc g0 A0
             ==> p3e_tthi g0 A0 (p3e_tth g0 A0 r) = r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r:real`] P3E_TTH_RANGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `p3e_tth g0 A0 r`] P3E_TTHI) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `r' = p3e_tthi g0 A0 (p3e_tth g0 A0 r)` THEN STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `~(a < b) /\ ~(b < a) ==> a = b`) THEN
  CONJ_TAC THEN DISCH_TAC THENL
   [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r':real`; `r:real`]
      P3E_TTH_STRICT);
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r:real`; `r':real`]
      P3E_TTH_STRICT)] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P3E_TTHI_RANGE = prove
 (`!g0 A0 s. p3_std_initial g0 A0 /\ &0 <= s /\ s < &2
             ==> &0 <= p3e_tthi g0 A0 s /\ p3e_tthi g0 A0 s < p3e_trc g0 A0 /\
                 p3e_tth g0 A0 (p3e_tthi g0 A0 s) = s /\
                 (&0 < s ==> &0 < p3e_tthi g0 A0 s) /\
                 (p3e_tthi g0 A0 s <= p3e_tr0 g0 A0 <=> s <= &1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `s:real`] P3E_TTHI) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `r = p3e_tthi g0 A0 s` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r:real`] P3E_TTH_RANGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[REAL_LT_LE] THEN DISCH_TAC THEN
  UNDISCH_TAC `p3e_tth g0 A0 r = s` THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP P3E_TTH_VALUES th]) THEN
  ASM_REAL_ARITH_TAC);;

let P3E_TTHI_SMALL = prove
 (`!g0 A0 s. p3_std_initial g0 A0 /\ &0 <= s /\
             s <= p3e_tk g0 A0 * (p3e_tr0 g0 A0 / &4)
             ==> p3e_tthi g0 A0 s = s / p3e_tk g0 A0`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_TR_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_TK_FACTS) THEN
  SUBGOAL_THEN `&0 <= s / p3e_tk g0 A0 /\ s / p3e_tk g0 A0 <= p3e_tr0 g0 A0 / &4`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `s = p3e_tth g0 A0 (s / p3e_tk g0 A0)`
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
   [ASM_SIMP_TAC[P3E_TTH_SMALL] THEN ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ];
    MATCH_MP_TAC P3E_TTHI_UNIQUE THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let P3E_TTHI_SMOOTH = prove
 (`!g0 A0. p3_std_initial g0 A0
           ==> smooth_map_on {s | &0 < drop s /\ drop s < &2}
                             (lift o p3e_tthi g0 A0 o drop)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_TR_FACTS) THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN REWRITE_TAC[P3E_OPEN_DROP_INTERVAL] THEN
  X_GEN_TAC `y:real^1` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `drop y`] P3E_TTHI_RANGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `r1 = p3e_tthi g0 A0 (drop y)` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o p3e_tth g0 A0 o drop`;
                 `{x:real^1 | &0 < drop x /\ drop x < p3e_trc g0 A0}`;
                 `lift r1`] SMOOTH_INVERSE_FUNCTION_THEOREM) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; LIFT_DROP; P3E_OPEN_DROP_INTERVAL] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `{x:real^1 | &0 < drop x}` THEN
      ASM_SIMP_TAC[P3E_TTH_SMOOTH] THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r1:real`] P3E_TTH_DERIV) THEN
    ASM_REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT] THEN
    DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    REWRITE_TAC[DET_1; matrix] THEN
    SIMP_TAC[LAMBDA_BETA; DIMINDEX_1; ARITH; VECTOR_MUL_COMPONENT; BASIS_COMPONENT] THEN
    REWRITE_TAC[REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
    MATCH_MP_TAC P3E_TTH_DERIV_POS THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[diffeomorphism_on; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t:real^1->bool`; `u:real^1->bool`; `g:real^1->real^1`] THEN
  STRIP_TAC THEN EXISTS_TAC `u:real^1->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `(lift o p3e_tth g0 A0 o drop) (lift r1) IN u` THEN
    ASM_REWRITE_TAC[o_THM; LIFT_DROP];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `g:real^1->real^1` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^1` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?z:real^1. z IN t /\ w = (lift o p3e_tth g0 A0 o drop) z`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < drop(z:real^1) /\ drop z < p3e_trc g0 A0` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[o_THM; LIFT_DROP] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `drop(z:real^1)`] P3E_TTHI_UNIQUE) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; LIFT_DROP]);;

(* ------------------------------------------------------------------------- *)
(* The radial maps p3e_theta (x -> theta(|x|) x/|x|) and                     *)
(* p3e_thinv (z -> tthi(|z|) z/|z|): norms, mutual inverses on ball(0,rc)    *)
(* and ball(0,2), and smoothness (linear near the origin, radial with a      *)
(* smooth profile away from it).                                            *)
(* ------------------------------------------------------------------------- *)

let p3e_theta = new_definition
 `p3e_theta (g0:real^3->real^3^3) (A0:real) (x:real^3) =
    (p3e_tth g0 A0 (norm x) / norm x) % x`;;

let p3e_thinv = new_definition
 `p3e_thinv (g0:real^3->real^3^3) (A0:real) (z:real^3) =
    (p3e_tthi g0 A0 (norm z) / norm z) % z`;;

let P3E_TTHI_0 = prove
 (`!g0 A0. p3_std_initial g0 A0 ==> p3e_tthi g0 A0 (&0) = &0`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_TR_FACTS) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `&0`] P3E_TTHI_UNIQUE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP P3E_TTH_VALUES th]));;

let P3E_THETA_NORM = prove
 (`!g0 A0 x. p3_std_initial g0 A0 /\ norm x < p3e_trc g0 A0
             ==> norm(p3e_theta g0 A0 x) = p3e_tth g0 A0 (norm x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3e_theta] THEN
  ASM_CASES_TAC `x:real^3 = vec 0` THENL
   [ASM_REWRITE_TAC[NORM_0; VECTOR_MUL_RZERO] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP P3E_TTH_VALUES th]);
    ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(x:real^3)`] P3E_TTH_RANGE) THEN
  ASM_REWRITE_TAC[NORM_POS_LE] THEN STRIP_TAC THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`; REAL_DIV_RMUL; NORM_EQ_0]);;

let P3E_THINV_NORM = prove
 (`!g0 A0 z. p3_std_initial g0 A0 /\ norm z < &2
             ==> norm(p3e_thinv g0 A0 z) = p3e_tthi g0 A0 (norm z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3e_thinv] THEN
  ASM_CASES_TAC `z:real^3 = vec 0` THENL
   [ASM_REWRITE_TAC[NORM_0; VECTOR_MUL_RZERO] THEN ASM_SIMP_TAC[P3E_TTHI_0];
    ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(z:real^3)`] P3E_TTHI_RANGE) THEN
  ASM_REWRITE_TAC[NORM_POS_LE] THEN STRIP_TAC THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`; REAL_DIV_RMUL; NORM_EQ_0]);;

let P3E_THETA_THINV = prove
 (`!g0 A0 x. p3_std_initial g0 A0 /\ norm x < p3e_trc g0 A0
             ==> p3e_thinv g0 A0 (p3e_theta g0 A0 x) = x`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `x:real^3 = vec 0` THENL
   [ASM_REWRITE_TAC[p3e_theta; p3e_thinv; VECTOR_MUL_RZERO]; ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P3E_THETA_NORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(x:real^3)`] P3E_TTH_RANGE) THEN
  ASM_REWRITE_TAC[NORM_POS_LE] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(x:real^3)`] P3E_TTHI_UNIQUE) THEN
  ASM_REWRITE_TAC[NORM_POS_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < norm(x:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < p3e_tth g0 A0 (norm(x:real^3))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[p3e_thinv] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[p3e_theta; VECTOR_MUL_ASSOC] THEN
  SUBGOAL_THEN
   `norm(x:real^3) / p3e_tth g0 A0 (norm x) * p3e_tth g0 A0 (norm x) / norm x = &1`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(REAL_FIELD `&0 < a /\ &0 < b ==> a / b * b / a = &1`) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[VECTOR_MUL_LID]]);;

let P3E_THINV_THETA = prove
 (`!g0 A0 z. p3_std_initial g0 A0 /\ norm z < &2
             ==> p3e_theta g0 A0 (p3e_thinv g0 A0 z) = z`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `z:real^3 = vec 0` THENL
   [ASM_REWRITE_TAC[p3e_theta; p3e_thinv; VECTOR_MUL_RZERO]; ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `z:real^3`] P3E_THINV_NORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(z:real^3)`] P3E_TTHI_RANGE) THEN
  ASM_REWRITE_TAC[NORM_POS_LE] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(z:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < p3e_tthi g0 A0 (norm(z:real^3))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[p3e_theta] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[p3e_thinv; VECTOR_MUL_ASSOC] THEN
  SUBGOAL_THEN
   `norm(z:real^3) / p3e_tthi g0 A0 (norm z) * p3e_tthi g0 A0 (norm z) / norm z = &1`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(REAL_FIELD `&0 < a /\ &0 < b ==> a / b * b / a = &1`) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[VECTOR_MUL_LID]]);;

let P3E_RADIAL_SMOOTH = prove
 (`!(h:real->real) a.
     smooth_map_on {s | &0 < drop s /\ drop s < a} (lift o h o drop)
     ==> smooth_map_on (ball(vec 0:real^3,a) DELETE vec 0)
                       (\x. (h(norm x) / norm x) % x)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `D = ball(vec 0:real^3,a) DELETE vec 0` THEN
  SUBGOAL_THEN `open(D:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN SIMP_TAC[OPEN_DELETE; OPEN_BALL]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN D ==> ~(x = vec 0) /\ &0 < norm x /\ norm x < a`
  ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[IN_DELETE; IN_BALL_0] THEN MESON_TAC[NORM_POS_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on D (\x:real^3. lift(norm x))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN
    REWRITE_TAC[SMOOTH_MAP_ON_LIFT_NORM_NONZERO] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on D (\x:real^3. lift(h(norm x)))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`D:real^3->bool`; `{s:real^1 | &0 < drop s /\ drop s < a}`;
                   `\x:real^3. lift(norm x)`; `h:real->real`]
      SMOOTH_MAP_ON_LIFT_COMPOSE_1D) THEN
    ASM_REWRITE_TAC[P3E_OPEN_DROP_INTERVAL; LIFT_DROP; IN_ELIM_THM] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on D (\x:real^3. lift(inv(norm x)))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`D:real^3->bool`; `\x:real^3. lift(norm x)`]
      SMOOTH_MAP_ON_LIFT_INV) THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC[REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on D (\x:real^3. drop(lift(h(norm x))) % lift(inv(norm x)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`D:real^3->bool`; `\x:real^3. lift(h(norm x))`;
                   `\x:real^3. lift(inv(norm x))`] SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`D:real^3->bool`;
                 `\x:real^3. drop(lift(h(norm x))) % lift(inv(norm x))`;
                 `\x:real^3. x`] SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; LIFT_DROP; DROP_CMUL; real_div]);;

let P3E_THETA_SMOOTH = prove
 (`!g0 A0. p3_std_initial g0 A0
           ==> smooth_map_on (ball(vec 0,p3e_trc g0 A0)) (p3e_theta g0 A0)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_TR_FACTS) THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN REWRITE_TAC[OPEN_BALL; IN_BALL_0] THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  ASM_CASES_TAC `norm(x:real^3) < p3e_tr0 g0 A0 / &4` THENL
   [EXISTS_TAC `ball(vec 0:real^3,p3e_tr0 g0 A0 / &4)` THEN
    ASM_REWRITE_TAC[OPEN_BALL; IN_BALL_0] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `\x:real^3. p3e_tk g0 A0 % x` THEN
    SIMP_TAC[SMOOTH_MAP_ON_CMUL_OPEN; OPEN_BALL; SMOOTH_MAP_ON_ID] THEN
    X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_BALL_0] THEN DISCH_TAC THEN
    REWRITE_TAC[p3e_theta] THEN
    ASM_CASES_TAC `y:real^3 = vec 0` THEN ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(y:real^3)`] P3E_TTH_SMALL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `~(y:real^3 = vec 0)` THEN REWRITE_TAC[GSYM NORM_EQ_0] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(norm(x:real^3) < p3e_tr0 g0 A0 / &4)` THEN
    ASM_REWRITE_TAC[NORM_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `ball(vec 0:real^3,p3e_trc g0 A0) DELETE vec 0` THEN
  ASM_SIMP_TAC[OPEN_DELETE; OPEN_BALL; IN_DELETE; IN_BALL_0] THEN
  SUBGOAL_THEN `p3e_theta g0 A0 = (\x. (p3e_tth g0 A0 (norm x) / norm x) % x)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; p3e_theta]; ALL_TAC] THEN
  MATCH_MP_TAC P3E_RADIAL_SMOOTH THEN REWRITE_TAC[ETA_AX] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `{s:real^1 | &0 < drop s}` THEN
  ASM_SIMP_TAC[P3E_TTH_SMOOTH] THEN SET_TAC[]);;

let P3E_THINV_SMOOTH = prove
 (`!g0 A0. p3_std_initial g0 A0
           ==> smooth_map_on (ball(vec 0,&2)) (p3e_thinv g0 A0)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_TR_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_TK_FACTS) THEN
  SUBGOAL_THEN `&0 < p3e_tk g0 A0 * (p3e_tr0 g0 A0 / &4)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN REWRITE_TAC[OPEN_BALL; IN_BALL_0] THEN
  X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  ASM_CASES_TAC `norm(z:real^3) < p3e_tk g0 A0 * (p3e_tr0 g0 A0 / &4)` THENL
   [EXISTS_TAC `ball(vec 0:real^3,p3e_tk g0 A0 * (p3e_tr0 g0 A0 / &4))` THEN
    ASM_REWRITE_TAC[OPEN_BALL; IN_BALL_0] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `\x:real^3. inv(p3e_tk g0 A0) % x` THEN
    SIMP_TAC[SMOOTH_MAP_ON_CMUL_OPEN; OPEN_BALL; SMOOTH_MAP_ON_ID] THEN
    X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_BALL_0] THEN DISCH_TAC THEN
    REWRITE_TAC[p3e_thinv] THEN
    ASM_CASES_TAC `y:real^3 = vec 0` THEN ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(y:real^3)`] P3E_TTHI_SMALL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `~(y:real^3 = vec 0)` THEN UNDISCH_TAC `&0 < p3e_tk g0 A0` THEN
    REWRITE_TAC[GSYM NORM_EQ_0] THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(z:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~(norm(z:real^3) < p3e_tk g0 A0 * (p3e_tr0 g0 A0 / &4))` THEN
    ASM_REWRITE_TAC[NORM_0];
    ALL_TAC] THEN
  EXISTS_TAC `ball(vec 0:real^3,&2) DELETE vec 0` THEN
  ASM_SIMP_TAC[OPEN_DELETE; OPEN_BALL; IN_DELETE; IN_BALL_0] THEN
  SUBGOAL_THEN `p3e_thinv g0 A0 = (\x. (p3e_tthi g0 A0 (norm x) / norm x) % x)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; p3e_thinv]; ALL_TAC] THEN
  MATCH_MP_TAC P3E_RADIAL_SMOOTH THEN REWRITE_TAC[ETA_AX] THEN
  ASM_SIMP_TAC[P3E_TTHI_SMOOTH]);;

(* ------------------------------------------------------------------------- *)
(* The model region s1 > -c is ball(0,rc) and the cap s1 >= 0                *)
(* is cball(0,r0); p3e_theta is a diffeomorphism of the model region onto   *)
(* ball(0,2), on the collar -c < s1 < 0 it is the inversion of p3_std_nc     *)
(* (and 1 < |theta x| < 2 there), and it maps the cap onto cball(0,1).      *)
(* ------------------------------------------------------------------------- *)

let P3E_MODEL_REGION = prove
 (`!g0 A0. p3_std_initial g0 A0
           ==> {x | --(sqrt(&2) * log(&2)) < A0 + &4 - p3_std_dist g0 x} =
               ball(vec 0,p3e_trc g0 A0)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_TR_FACTS) THEN
  SUBGOAL_THEN `&0 <= p3e_trc g0 A0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_BALL_0] THEN X_GEN_TAC `x:real^3` THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP P3S_ROT_DIST th]) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(x:real^3)`; `p3e_trc g0 A0`]
    P3S_RHO_LT_EQ) THEN
  ASM_REWRITE_TAC[NORM_POS_LE] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN REAL_ARITH_TAC);;

let P3E_CAP_REGION = prove
 (`!g0 A0. p3_std_initial g0 A0
           ==> {x | &0 <= A0 + &4 - p3_std_dist g0 x} = cball(vec 0,p3e_tr0 g0 A0)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_TR_FACTS) THEN
  SUBGOAL_THEN `&0 <= p3e_tr0 g0 A0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_CBALL_0] THEN X_GEN_TAC `x:real^3` THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP P3S_ROT_DIST th]) THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(x:real^3)`; `p3e_tr0 g0 A0`]
    P3S_RHO_LT_EQ) THEN
  ASM_REWRITE_TAC[NORM_POS_LE] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN REAL_ARITH_TAC);;

let P3E_THETA_DIFFEO_BALL = prove
 (`!g0 A0. p3_std_initial g0 A0
           ==> diffeomorphism_on (ball(vec 0,p3e_trc g0 A0)) (ball(vec 0,&2))
                                 (p3e_theta g0 A0) (p3e_thinv g0 A0)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMT_DIFFEOMORPHISM_ON_INVERSES THEN
  ASM_SIMP_TAC[OPEN_BALL; P3E_THETA_SMOOTH; P3E_THINV_SMOOTH; IN_BALL_0] THEN
  CONJ_TAC THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THENL
   [ASM_SIMP_TAC[P3E_THETA_NORM; P3E_THETA_THINV] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(x:real^3)`] P3E_TTH_RANGE) THEN
    ASM_SIMP_TAC[NORM_POS_LE];
    ASM_SIMP_TAC[P3E_THINV_NORM; P3E_THINV_THETA] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(x:real^3)`] P3E_TTHI_RANGE) THEN
    ASM_SIMP_TAC[NORM_POS_LE]]);;

let P3E_THETA_CAP_IMAGE = prove
 (`!g0 A0. p3_std_initial g0 A0
           ==> IMAGE (p3e_theta g0 A0) (cball(vec 0,p3e_tr0 g0 A0)) = cball(vec 0,&1)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_TR_FACTS) THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_CBALL_0] THEN X_GEN_TAC `z:real^3` THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `norm(x:real^3) < p3e_trc g0 A0` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[P3E_THETA_NORM] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(x:real^3)`] P3E_TTH_RANGE) THEN
    ASM_SIMP_TAC[NORM_POS_LE];
    DISCH_TAC THEN EXISTS_TAC `p3e_thinv g0 A0 z` THEN
    SUBGOAL_THEN `norm(z:real^3) < &2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[P3E_THINV_THETA; P3E_THINV_NORM] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `norm(z:real^3)`] P3E_TTHI_RANGE) THEN
    ASM_SIMP_TAC[NORM_POS_LE]]);;

let P3E_THETA_COLLAR = prove
 (`!g0 A0 x. p3_std_initial g0 A0 /\
             --(sqrt(&2) * log(&2)) < A0 + &4 - p3_std_dist g0 x /\
             A0 + &4 - p3_std_dist g0 x < &0
             ==> &1 < norm(p3e_theta g0 A0 x) /\ norm(p3e_theta g0 A0 x) < &2 /\
                 inv(norm(p3e_theta g0 A0 x) pow 2) % p3e_theta g0 A0 x =
                 p3_std_nc g0 A0 x /\
                 p3e_theta g0 A0 x =
                 inv(norm(p3_std_nc g0 A0 x) pow 2) % p3_std_nc g0 A0 x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3E_TR_FACTS) THEN
  SUBGOAL_THEN `&0 < p3e_trc g0 A0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `r = norm(x:real^3)` THEN
  SUBGOAL_THEN `p3_std_dist g0 x = p3s_rad_rho g0 r` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN MATCH_MP_TAC P3S_ROT_DIST THEN EXISTS_TAC `A0:real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= r` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `p3e_tr0 g0 A0 < r /\ r < p3e_trc g0 A0` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `p3e_tr0 g0 A0`; `r:real`]
      P3S_RHO_LT_EQ) THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r:real`; `p3e_trc g0 A0`]
      P3S_RHO_LT_EQ) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p3e_tth g0 A0 r = p3e_tf g0 A0 r` ASSUME_TAC THENL
   [MATCH_MP_TAC P3E_TTH_LARGE THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(p3e_theta g0 A0 x) = p3e_tf g0 A0 r` ASSUME_TAC THENL
   [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P3E_THETA_NORM) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 < p3e_tf g0 A0 r /\ p3e_tf g0 A0 r < &2` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p3e_tf g0 A0 (p3e_tr0 g0 A0) = &1` THEN
    UNDISCH_TAC `p3e_tf g0 A0 (p3e_trc g0 A0) = &2` THEN
    REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
    CONJ_TAC THEN MATCH_MP_TAC P3E_TF_STRICT THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `p3e_theta g0 A0 x = (p3e_tf g0 A0 r / r) % (x:real^3)` ASSUME_TAC THENL
   [REWRITE_TAC[p3e_theta] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `p3_std_nc g0 A0 x = (inv(p3e_tf g0 A0 r) * inv r) % (x:real^3)`
  ASSUME_TAC THENL
   [REWRITE_TAC[p3_std_nc; VECTOR_MUL_ASSOC] THEN ASM_REWRITE_TAC[] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[p3e_tf; GSYM REAL_EXP_NEG] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `inv(norm(p3e_theta g0 A0 x) pow 2) % p3e_theta g0 A0 x = p3_std_nc g0 A0 x`
  ASSUME_TAC THENL
   [REWRITE_TAC[ASSUME `norm(p3e_theta g0 A0 x) = p3e_tf g0 A0 r`] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r:real`] P3E_TF_POS) THEN
    UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(p3e_theta g0 A0 x = vec 0)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NORM_EQ_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    UNDISCH_TAC
     `inv(norm(p3e_theta g0 A0 x) pow 2) % p3e_theta g0 A0 x = p3_std_nc g0 A0 x` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SMT_INVERSION_INVOLUTION THEN ASM_REWRITE_TAC[]]);;

let P3E_THETA_FACTS = prove
 (`!g0 A0. p3_std_initial g0 A0
     ==> diffeomorphism_on {x | --(sqrt(&2) * log(&2)) < A0 + &4 - p3_std_dist g0 x}
                           (ball(vec 0,&2)) (p3e_theta g0 A0) (p3e_thinv g0 A0) /\
         (!x. --(sqrt(&2) * log(&2)) < A0 + &4 - p3_std_dist g0 x /\
              A0 + &4 - p3_std_dist g0 x < &0
              ==> &1 < norm(p3e_theta g0 A0 x) /\ norm(p3e_theta g0 A0 x) < &2 /\
                  inv(norm(p3e_theta g0 A0 x) pow 2) % p3e_theta g0 A0 x =
                  p3_std_nc g0 A0 x /\
                  p3e_theta g0 A0 x =
                  inv(norm(p3_std_nc g0 A0 x) pow 2) % p3_std_nc g0 A0 x) /\
         IMAGE (p3e_theta g0 A0) {x | &0 <= A0 + &4 - p3_std_dist g0 x} =
         cball(vec 0,&1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[P3E_MODEL_REGION; P3E_CAP_REGION; P3E_THETA_DIFFEO_BALL;
               P3E_THETA_CAP_IMAGE] THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P3E_THETA_COLLAR) THEN
  ASM_REWRITE_TAC[]);;

