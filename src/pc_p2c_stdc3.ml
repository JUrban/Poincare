(* ========================================================================= *)
(* Unit pc_p2c_stdc3 (Part 2C; MT Ch 12): MT Prop 12.31, R(p,t) >= c/(1-t)   *)
(* on the standard flow, with a repair of MT's proof: (a) the warp f_t = r   *)
(* sqrt(b_t) is nondecreasing with limit <= sqrt(2(1-t)) (cylinder           *)
(* asymptotics), so b_t(r) <= 2(1-t)/r^2 -> 0, while bounded R near a point  *)
(* (Lemma 11.2) would keep b_t bounded below: R -> inf everywhere as t -> 1; *)
(* (b) the last paragraph corrected: forward Lemma 11.2 from t1 >= 1 -       *)
(* r^2/(32 C) gives R >= 1/(32 C (1-t)); (c) inf R > 0 on [0,t0] by          *)
(* continuity, positivity (sec > 0 for t > 0, K_tan > 0 at t = 0) and the    *)
(* cylinder far out.                                                         *)
(* ========================================================================= *)

needs "src/pc_p2c_stdc2.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The tangential coefficient through the normalized map.                   *)
(* For an SO(3)-invariant metric G and a far point x, the pullback of G by  *)
(* stds_nmap g0 A0 x at basis 1 has e2-coefficient |x|^2 b_G(|x|): the       *)
(* derivative of nmap = ncinv o (mu Q) maps e2 to |x| Q e2, tangential at x  *)
(* (P3S_RADMAP_DERIV, the chain rule, LRG_MPULLBACK_DOT, STDS_RT_ROT_FORM).  *)
(* ------------------------------------------------------------------------- *)

let STDS_LINEAR_RANK1 = prove
 (`!k c (y0:real^N) m. linear (\h. k % h + (c * (y0 dot h) / m) % y0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linear; DOT_RADD; DOT_RMUL] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[real_div; REAL_ADD_LDISTRIB; REAL_ADD_RDISTRIB; VECTOR_ADD_RDISTRIB;
              VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
  REWRITE_TAC[REAL_ARITH `c * (a * x) * m = a * c * x * m`] THEN
  VECTOR_ARITH_TAC);;

let STDS_NMAP_TANG = prove
 (`!g0 A0 (x:real^3) G.
     p3_std_initial g0 A0 /\ A0 + sqrt(&2) * (&0 + &1) <= p3_std_dist g0 x /\ stds_rotm G
     ==> basis 2 dot (mpullback (stds_nmap g0 A0 x) G (basis 1) ** basis 2) =
         norm x pow 2 * p3s_rad_b G (norm x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `0`] STDS_FAR_MU) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `mu = norm(p3_std_nc g0 A0 x)` THEN
  SUBGOAL_THEN `&0 < mu` ASSUME_TAC THENL
   [EXPAND_TAC "mu" THEN ASM_SIMP_TAC[STDS_NC_MU_POS]; ALL_TAC] THEN
  MP_TAC(SPEC `x:real^3` STDS_ROT) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `Q = stds_rot x` THEN
  MP_TAC(SPECL [`mu:real`; `Q:real^3^3`] STDS_LIN_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `mu % ((Q:real^3^3) ** basis 1) = p3_std_nc g0 A0 x` ASSUME_TAC THENL
   [REWRITE_TAC[ASSUME `(Q:real^3^3) ** basis 1 = inv(norm(x:real^3)) % x`; p3_std_nc] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P3S_NC_NORM) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `y0 = p3_std_nc g0 A0 x` THEN
  SUBGOAL_THEN `~(y0:real^3 = vec 0) /\
                sqrt(&2) * log(norm(y0:real^3)) < A0 + &4 /\
                p3s_rad_rinv g0 (A0 + &4 - sqrt(&2) * log(norm y0)) = norm(x:real^3)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `a /\ (a ==> b) /\ (a /\ b ==> c) ==> a /\ b /\ c`) THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[GSYM NORM_POS_LT];
      DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P3S_NC_NORM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LOG_EXP] THEN
      SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ] THEN
      MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P3S_DIST_POS) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      STRIP_TAC THEN
      MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `y0:real^3`] P3S_NCINV_FACTS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
      MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`] P3S_NC_NCINV) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      DISCH_THEN(ACCEPT_TAC o SYM)];
    ALL_TAC] THEN
  (* the derivative of nmap at basis 1 *)
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `y0:real^3`] P3S_RADMAP_DERIV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM p3s_ncinv; ETA_AX] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?c2. (stds_nmap g0 A0 x has_derivative
          ((\h. (norm(x:real^3) * inv mu) % h + (c2 * ((y0:real^3) dot h) / mu) % y0) o
           (\y:real^3. mu % ((Q:real^3^3) ** y)))) (at (basis 1))`
  (X_CHOOSE_TAC `c2:real`) THENL
   [EXISTS_TAC `(inv(sqrt(p3s_rad_a g0 (norm(x:real^3)))) * --(sqrt(&2) * inv mu)) * inv mu +
                norm x * --inv(mu pow 2)` THEN
    REWRITE_TAC[STDS_NMAP_O] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  SUBGOAL_THEN `linear(frechet_derivative (stds_nmap g0 A0 x) (at (basis 1:real^3)))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LINEAR_COMPOSE THEN
    ASM_REWRITE_TAC[STDS_LINEAR_RANK1];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LRG_MPULLBACK_DOT; STDS_NMAP_E1] THEN
  ASM_REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN `(y0:real^3) dot (mu % ((Q:real^3^3) ** basis 2)) = &0` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM(ASSUME `mu % ((Q:real^3^3) ** basis 1) = y0`)] THEN
    REWRITE_TAC[DOT_LMUL; DOT_RMUL] THEN
    ASM_SIMP_TAC[STDS_ORTH_DOT; DOT_BASIS_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_MUL_RZERO; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
  SUBGOAL_THEN `(norm(x:real^3) * inv mu) % (mu % ((Q:real^3^3) ** basis 2)) =
                norm x % (Q ** basis 2)`
  SUBST1_TAC THENL
   [REWRITE_TAC[VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < mu` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^3->real^3^3`; `x:real^3`; `norm(x:real^3) % ((Q:real^3^3) ** basis 2)`]
                STDS_RT_ROT_FORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `((Q:real^3^3) ** basis 2) dot (x:real^3) = &0 /\
                ((Q:real^3^3) ** basis 2) dot ((Q:real^3^3) ** basis 2) = &1`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[STDS_ORTH_DOT; DOT_BASIS_BASIS; DIMINDEX_3; ARITH] THEN
    SUBGOAL_THEN `x:real^3 = norm x % ((Q:real^3^3) ** basis 1)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_RINV; NORM_EQ_0; VECTOR_MUL_LID];
      REWRITE_TAC[DOT_RMUL] THEN ASM_SIMP_TAC[STDS_ORTH_DOT; DOT_BASIS_BASIS; DIMINDEX_3; ARITH] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[DOT_LMUL; DOT_RMUL] THEN
  SUBGOAL_THEN `~(norm(x:real^3) = &0)` MP_TAC THENL [ASM_REWRITE_TAC[NORM_EQ_0]; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

let STDS_CYL_E2E2 = prove
 (`!t. basis 2 dot (cylinder_flow t (basis 1) ** basis 2) = &2 * (&1 - t)`,
  GEN_TAC THEN REWRITE_TAC[cylinder_flow] THEN
  SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN
  SIMP_TAC[DOT_BASIS; MATRIX_VECTOR_MUL_COMPONENT; DIMINDEX_3; ARITH] THEN
  SIMP_TAC[matrix_vector_mul; LAMBDA_BETA; DIMINDEX_3; ARITH; SUM_3; DOT_3;
           BASIS_COMPONENT; MATRIX_CMUL_COMPONENT; MATRIX_ADD_COMPONENT; MAT_COMPONENT] THEN
  REAL_ARITH_TAC);;

(* Repair (a): the warp of Gs t is at most sqrt(2(1-t)): it is               *)
(* nondecreasing (STDS_MFH_MONO) and far out its square is within eta of    *)
(* 2(1-t) for every eta > 0 (STDS_ASYM_CLOSE with LCK_DIST_C0 at basis 1).  *)

let STDS_WARP_LE = prove
 (`!d:real^4->bool.
     stds_tm_hyps d
     ==> !g0 A0 t r. p3_std_initial g0 A0 /\ &0 <= t /\ t < &1 /\ &0 < r
                     ==> r pow 2 * p3s_rad_b (stds_gs g0 t) r <= &2 * (&1 - t)`,
  GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[stds_tm_hyps] th)) THEN
  MAP_EVERY X_GEN_TAC [`g0:real^3->real^3^3`; `A0:real`; `t:real`; `r:real`] THEN
  STRIP_TAC THEN
  MP_TAC(SPEC `d:real^4->bool` STDS_TM_EQ_1) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] STDS_GS_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `d:real^4->bool` STDS_GS_SEC_NONNEG) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "sec") THEN
  SUBGOAL_THEN `stds_rgood (stds_gs g0 t)` ASSUME_TAC THENL
   [REWRITE_TAC[stds_rgood] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "stds_rotm")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]] THEN STRIP_TAC THEN
    REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `dd = r pow 2 * p3s_rad_b (stds_gs g0 t) r - &2 * (&1 - t)` THEN
  ABBREV_TAC `eta = dd / (&4 * (&1 - t))` THEN
  SUBGOAL_THEN `&0 < eta /\ eta * (&2 * (&1 - t)) = dd / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `~(&1 - t = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  UNDISCH_TAC `stds_gs_hyps` THEN REWRITE_TAC[stds_gs_hyps] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `stds_tm g0`; `stds_gs g0`; `t:real`;
                `{basis 1:real^3}`; `0`; `eta pow 2`] STDS_ASYM_CLOSE) THEN
  ASM_SIMP_TAC[COMPACT_SING; REAL_POW_LT; SING_SUBSET; IN_DELETE; IN_UNIV; STDS_BASIS1_NZ;
               IN_SING] THEN
  DISCH_THEN(X_CHOOSE_THEN `A2:real` (LABEL_TAC "CL")) THEN
  (* a far point x with |x| >= r *)
  SUBGOAL_THEN `&0 <= p3_std_dist g0 (r % basis 1:real^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC P3S_DIST_POS THEN
    EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; STDS_BASIS1_NZ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `c = max (max A2 (A0 + sqrt(&2) * (&0 + &1))) (p3_std_dist g0 (r % basis 1:real^3)) +
                  &1` THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `\n:num. (c:real)`] STDS_FAR_SEQ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN EXPAND_TAC "c" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs:num->real^3` (MP_TAC o SPEC `0`)) THEN BETA_TAC THEN
  ABBREV_TAC `x = (xs:num->real^3) 0` THEN DISCH_TAC THEN
  SUBGOAL_THEN `A2 < p3_std_dist g0 x /\ A0 + sqrt(&2) * (&0 + &1) <= p3_std_dist g0 x`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `max (max A2 (A0 + sqrt(&2) * (&0 + &1))) (p3_std_dist g0 (r % basis 1:real^3)) +
                  &1 = c` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `r <= norm(x:real^3)` ASSUME_TAC THENL
   [SUBGOAL_THEN `p3_std_dist g0 (r % basis 1:real^3) < p3_std_dist g0 x` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `max (max A2 (A0 + sqrt(&2) * (&0 + &1))) (p3_std_dist g0 (r % basis 1:real^3)) +
                  &1 = c` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] P3S_DIST_ALT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN BETA_TAC THEN
    SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `r:real`; `norm(x:real^3)`] STDS_RT_RHO_LT_EQ) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE] THEN MATCH_MP_TAC STDS_STD_ROTM THEN
      EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the closeness at basis 1 and the C0 comparison *)
  USE_THEN "CL" (MP_TAC o SPECL [`x:real^3`; `t:real`; `basis 1:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; DISCH_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `0`] STDS_FAR_MU) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `0`] STDS_NMAP_OPEN_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `exp(--(&0 + &1))`;
                `exp(&0 + &1)`] STDS_NMAP_DIFFEO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_EXP_POS_LT; REAL_EXP_MONO_LT] THEN REAL_ARITH_TAC;
    REWRITE_TAC[GSYM stds_aW] THEN STRIP_TAC] THEN
  SUBGOAL_THEN `metric_field (stds_aW 0) (mpullback (stds_nmap g0 A0 x) (stds_gs g0 t)) /\
                metric_field (stds_aW 0) (cylinder_flow t)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [`IMAGE (stds_nmap g0 A0 x) (stds_aW 0)`;
        `(\z. inv(norm(p3_std_nc g0 A0 x)) % (transp(stds_rot x) ** z)) o p3_std_nc g0 A0`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
      EXISTS_TAC `(:real^3)` THEN ASM_REWRITE_TAC[SUBSET_UNIV] THEN
      MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `t:real`] STDS_GS_RIEM) THEN
      ASM_REWRITE_TAC[stds_gs_hyps] THEN SIMP_TAC[];
      MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
      REWRITE_TAC[STDS_AW_SUBSET] THEN MATCH_MP_TAC RFB_CYL_METRIC_FIELD THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`0`; `stds_aW 0`; `cylinder_flow t`;
                 `mpullback (stds_nmap g0 A0 x) (stds_gs g0 t)`; `basis 1:real^3`;
                 `basis 2:real^3`] LCK_DIST_C0) THEN
  ASM_REWRITE_TAC[STDS_AW_BASIS; STDS_CYL_E2E2] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `stds_gs g0 t`]
               STDS_NMAP_TANG) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[stds_rgood]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `sqrt(lck_dist2 0 (cylinder_flow t)
                       (mpullback (stds_nmap g0 A0 x) (stds_gs g0 t)) (basis 1)) < eta`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_LSQRT THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* monotonicity of the warp *)
  MP_TAC(SPECL [`stds_gs g0 t`; `r:real`; `norm(x:real^3)`] STDS_MFH_MONO) THEN
  ASM_REWRITE_TAC[stds_mFh] THEN DISCH_TAC THEN
  SUBGOAL_THEN `r pow 2 * p3s_rad_b (stds_gs g0 t) r <=
                norm(x:real^3) pow 2 * p3s_rad_b (stds_gs g0 t) (norm x)`
  MP_TAC THENL
   [SUBGOAL_THEN `&0 < p3s_rad_b (stds_gs g0 t) r /\
                  &0 < p3s_rad_b (stds_gs g0 t) (norm(x:real^3))` STRIP_ASSUME_TAC THENL
     [MP_TAC(SPEC `stds_gs g0 t` STDS_RT_ROT_AB) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[stds_rgood]; SIMP_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`2`; `r * sqrt(p3s_rad_b (stds_gs g0 t) r)`;
                   `norm(x:real^3) * sqrt(p3s_rad_b (stds_gs g0 t) (norm x))`]
                  REAL_POW_LE2) THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; SQRT_POS_LE] THEN
    ASM_SIMP_TAC[REAL_POW_MUL; SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  UNDISCH_TAC `eta * (&2 * (&1 - t)) = dd / &2` THEN
  UNDISCH_TAC `r pow 2 * p3s_rad_b (stds_gs g0 t) r - &2 * (&1 - t) = dd` THEN
  SUBGOAL_THEN `sqrt(lck_dist2 0 (cylinder_flow t)
                       (mpullback (stds_nmap g0 A0 x) (stds_gs g0 t)) (basis 1)) *
                (&2 * (&1 - t)) <= eta * (&2 * (&1 - t))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `&2 * (&1 - t) < r pow 2 * p3s_rad_b (stds_gs g0 t) r` THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Repair (a) completed: R(p,t) -> inf as t -> 1 at every                    *)
(* point p.  If R(p,t1) <= M with 1 - t1 below the window of Lemma 11.2,    *)
(* then R stays bounded on a ball B around p over [t1,1), the metrics on B  *)
(* stay above exp(-c) g(t1) (SNGL_METRIC_EQUIV_LOCAL), so the tangential    *)
(* coefficient b_t at a nonzero point of B stays above a positive constant, *)
(* against b_t(|y|) <= 2(1-t)/|y|^2 (STDS_WARP_LE).                          *)
(* ------------------------------------------------------------------------- *)

let STDS_TANG_COEF = prove
 (`!G (y:real^3).
     stds_rotm G /\ ~(y = vec 0)
     ==> (stds_rot y ** basis 2) dot (G y ** (stds_rot y ** basis 2)) =
         p3s_rad_b G (norm y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `y:real^3` STDS_ROT) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `Q = stds_rot y` THEN
  ASM_SIMP_TAC[STDS_RT_ROT_FORM] THEN
  SUBGOAL_THEN `((Q:real^3^3) ** basis 2) dot (y:real^3) = &0 /\
                ((Q:real^3^3) ** basis 2) dot (Q ** basis 2) = &1`
  (fun th -> REWRITE_TAC[th]) THENL
   [ASM_SIMP_TAC[STDS_ORTH_DOT; DOT_BASIS_BASIS; DIMINDEX_3; ARITH] THEN
    SUBGOAL_THEN `y:real^3 = norm y % ((Q:real^3^3) ** basis 1)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_RINV; NORM_EQ_0; VECTOR_MUL_LID];
      REWRITE_TAC[DOT_RMUL] THEN ASM_SIMP_TAC[STDS_ORTH_DOT; DOT_BASIS_BASIS; DIMINDEX_3; ARITH] THEN
      REAL_ARITH_TAC];
    REAL_ARITH_TAC]);;

let STDS_NONZERO_IN_OPEN = prove
 (`!B (p:real^3). open B /\ p IN B ==> ?y. y IN B /\ ~(y = vec 0)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `p:real^3 = vec 0` THENL
   [ALL_TAC; EXISTS_TAC `p:real^3` THEN ASM_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `vec 0:real^3` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(e / &2) % basis 1:real^3` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    SIMP_TAC[IN_BALL_0; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[VECTOR_MUL_EQ_0; STDS_BASIS1_NZ] THEN ASM_REAL_ARITH_TAC]);;

let STDS_R_TO_INFTY = prove
 (`!d:real^4->bool.
     stds_tm_hyps d
     ==> !g0 A0 (p:real^3) M.
           p3_std_initial g0 A0
           ==> ?t1. t1 < &1 /\
                    !t. t1 <= t /\ t < &1
                        ==> M < mfd_scalar (open_set_atlas (:real^3)) (stds_gs g0 t) p`,
  GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[stds_tm_hyps] th)) THEN
  MAP_EVERY X_GEN_TAC [`g0:real^3->real^3^3`; `A0:real`; `p:real^3`; `M:real`] THEN
  DISCH_TAC THEN
  MP_TAC(SPEC `d:real^4->bool` STDS_TM_EQ_1) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] STDS_GS_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `d:real^4->bool` STDS_GS_SEC_NONNEG) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "sec") THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] STDS_GV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "per"))))))) THEN
  MP_TAC(SPEC `d:real^4->bool` STDS_DERIV_BOUNDS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps:real` (X_CHOOSE_THEN `C:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]))))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DB"))) THEN
  ABBREV_TAC `C' = max C (&2)` THEN
  ABBREV_TAC `Kd = max (&0) M + inv(r pow 2)` THEN
  SUBGOAL_THEN `&0 < C' /\ &0 < inv(r pow 2) /\ &0 < Kd` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `a /\ b /\ (b ==> c) ==> a /\ b /\ c`) THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "C'" THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_POW_LT];
      EXPAND_TAC "Kd" THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `dl = inv(&16 * C' * Kd)` THEN
  SUBGOAL_THEN `&0 < dl` ASSUME_TAC THENL
   [EXPAND_TAC "dl" THEN REWRITE_TAC[REAL_LT_INV_EQ] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(MP_TAC o SPEC `max (&1 / &2) (&1 - dl / &2)` o
    REWRITE_RULE[NOT_EXISTS_THM; TAUT `~(a /\ b) <=> a ==> ~b`; NOT_FORALL_THM; NOT_IMP;
                 REAL_NOT_LT]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ts:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < ts /\ &1 - ts <= dl` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the ball of Lemma 11.2 around p at time ts *)
  SUBGOAL_THEN `riemannian_metric (open_set_atlas (:real^3)) (stds_gs g0 ts)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `ts:real`] STDS_GS_RIEM) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `rr = inv(&2 * C' * sqrt(max (rfs_vscalar (stds_gv g0) ts p) (inv(r pow 2))))` THEN
  SUBGOAL_THEN `&0 < rr` ASSUME_TAC THENL
   [EXPAND_TAC "rr" THEN REWRITE_TAC[REAL_LT_INV_EQ] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SQRT_POS_LT THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `B = rfs_vball (stds_gv g0) ts p rr` THEN
  SUBGOAL_THEN `open (B:real^3->bool) /\ (p:real^3) IN B` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `ts:real`; `p:real^3`; `rr:real`] STDS_GV_BALL) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[GSYM OPEN_IN_EUCLIDEAN] THEN
    SIMP_TAC[MFD_BALL_OPEN; MFD_CENTRE_IN_BALL; P2C_EUCLID_FACTS; IN_UNIV;
             ASSUME `riemannian_metric (open_set_atlas (:real^3)) (stds_gs g0 ts)`;
             ASSUME `&0 < rr`];
    ALL_TAC] THEN
  (* R on B after ts *)
  SUBGOAL_THEN
   `!s y. ts < s /\ s < &1 /\ y IN B
          ==> mfd_scalar (open_set_atlas (:real^3)) (stds_gs g0 s) y <= &2 * Kd`
  (LABEL_TAC "Rafter") THENL
   [MAP_EVERY X_GEN_TAC [`s:real`; `y:real^3`] THEN STRIP_TAC THEN
    UNDISCH_TAC `P2C_LEMMA_11_2_DB_STATEMENT (:real^3)` THEN
    REWRITE_TAC[P2C_LEMMA_11_2_DB_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPECL [`stds_gv g0`; `C':real`; `r:real`; `p:real^3`; `ts:real`;
                               `s:real`; `rr:real`]) THEN
    SUBGOAL_THEN `min ts s = ts /\ max ts s = s` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MAP_EVERY X_GEN_TAC [`z:real^3`; `u:real`] THEN
        REWRITE_TAC[STDS_GV_TOPSPACE] THEN STRIP_TAC THEN
        USE_THEN "DB" (MP_TAC o SPECL [`z:real^3`; `u:real`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        REWRITE_TAC[STDS_GV_TOPSPACE] THEN ASM_REAL_ARITH_TAC;
        EXPAND_TAC "rr" THEN REWRITE_TAC[REAL_LE_REFL];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `dl:real` THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        EXPAND_TAC "dl" THEN MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
          MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          EXPAND_TAC "Kd" THEN REWRITE_TAC[STDS_GV_SCALAR] THEN ASM_REAL_ARITH_TAC];
        USE_THEN "per" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        TRY DISCH_TAC THEN REWRITE_TAC[STDS_GV_PARTS] THEN
        SUBGOAL_THEN `(&0 <= ts /\ ts < stds_tm g0) /\ (&0 <= s /\ s < stds_tm g0)`
        (fun th -> REWRITE_TAC[th]) THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC MFD_DIFFEO_ID THEN EXPAND_TAC "B" THEN
        ASM_REWRITE_TAC[P2C_EUCLID_FACTS; OPEN_IN_EUCLIDEAN]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`s:real`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    REWRITE_TAC[STDS_GV_SCALAR] THEN EXPAND_TAC "Kd" THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `ts:real`] STDS_GS_RBOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Kts:real` (LABEL_TAC "Kts")) THEN
  ABBREV_TAC `Kb = max (&0) (max Kts (&2 * Kd)) / &2` THEN
  SUBGOAL_THEN `&0 <= Kb` ASSUME_TAC THENL [EXPAND_TAC "Kb" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!u y. ts <= u /\ u < &1 /\ y IN B
          ==> mfd_rm_norm (open_set_atlas (:real^3)) (stds_gs g0 u) y <= Kb`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`u:real`; `y:real^3`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `u:real`; `y:real^3`]
                 STDS_GS_SEC_CONSEQ) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
    SUBGOAL_THEN `mfd_scalar (open_set_atlas (:real^3)) (stds_gs g0 u) y <=
                  max Kts (&2 * Kd)` MP_TAC THENL
     [ASM_CASES_TAC `u:real = ts` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN
        MATCH_MP_TAC(REAL_ARITH `a <= b ==> a <= max b c`) THEN
        USE_THEN "Kts" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `a <= c ==> a <= max b c`) THEN
        USE_THEN "Rafter" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      EXPAND_TAC "Kb" THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `stds_gs g0`;
                 `ts:real`; `&1`; `B:real^3->bool`; `Kb:real`] SNGL_METRIC_EQUIV_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_IN_EUCLIDEAN] THEN
    MATCH_MP_TAC PDE_RFF_RESTRICT THEN MAP_EVERY EXISTS_TAC [`&0`; `stds_tm g0`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[p3_partial_std]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(LABEL_TAC "EQ") THEN
  MP_TAC(SPECL [`B:real^3->bool`; `p:real^3`] STDS_NONZERO_IN_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y0:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!u. &0 <= u /\ u < &1
        ==> (stds_rot y0 ** basis 2) dot (stds_gs g0 u y0 ** (stds_rot y0 ** basis 2)) =
            p3s_rad_b (stds_gs g0 u) (norm(y0:real^3)) /\
            &0 < p3s_rad_b (stds_gs g0 u) (norm y0)`
  (LABEL_TAC "TC") THENL
   [GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `stds_rotm (stds_gs g0 u)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `u:real` o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "stds_rotm")) (concl th) &&
        is_forall (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC STDS_TANG_COEF THEN ASM_REWRITE_TAC[];
      MP_TAC(SPEC `stds_gs g0 u` STDS_RT_ROT_AB) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `bts = p3s_rad_b (stds_gs g0 ts) (norm(y0:real^3))` THEN
  SUBGOAL_THEN `&0 < bts` ASSUME_TAC THENL
   [EXPAND_TAC "bts" THEN USE_THEN "TC" (MP_TAC o SPEC `ts:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(y0:real^3) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `q = norm(y0:real^3) pow 2 * exp(--(&4 * Kb)) * bts / &4` THEN
  SUBGOAL_THEN `&0 < q` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `u = max ts (&1 - q)` THEN
  SUBGOAL_THEN `ts <= u /\ u < &1 /\ &1 - u <= q /\ u - ts <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "TC" (MP_TAC o SPEC `u:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  USE_THEN "TC" (MP_TAC o SPEC `ts:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  USE_THEN "EQ" (MP_TAC o SPECL [`u:real`; `y0:real^3`; `stds_rot y0 ** basis 2:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `exp(--(&4 * Kb)) * bts <= p3s_rad_b (stds_gs g0 u) (norm(y0:real^3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `exp(--(&2 * (&2 * Kb) * (u - ts))) * bts` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_EXP_MONO_LE] THEN
    REWRITE_TAC[REAL_LE_NEG2] THEN
    SUBGOAL_THEN `(&2 * Kb) * (u - ts) <= (&2 * Kb) * &1` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPEC `d:real^4->bool` STDS_WARP_LE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`; `u:real`; `norm(y0:real^3)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LT] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `norm(y0:real^3) pow 2 * (exp(--(&4 * Kb)) * bts) <=
                norm y0 pow 2 * p3s_rad_b (stds_gs g0 u) (norm y0)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  UNDISCH_TAC `norm(y0:real^3) pow 2 * exp(--(&4 * Kb)) * bts / &4 = q` THEN
  SUBGOAL_THEN `&0 < norm(y0:real^3) pow 2 * (exp(--(&4 * Kb)) * bts)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[REAL_EXP_POS_LT];
    ALL_TAC] THEN
  UNDISCH_TAC `&1 - u <= q` THEN
  UNDISCH_TAC `norm(y0:real^3) pow 2 * p3s_rad_b (stds_gs g0 u) (norm y0) <= &2 * (&1 - u)` THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Repair (c): inf R > 0 on R^3 x [0,t0], t0 < 1.  Far out                   *)
(* R >= 1/2 (cylinder asymptotics, RFB_CYL_SCALAR); at t = 0 R(g0) > 0      *)
(* (tangential curvature, the tip); for t > 0 R > 0 (sec > 0); the minimum  *)
(* over the compact rest exists by joint continuity of R                    *)
(* (RFA_MFD_SCALAR_CONTINUOUS_GEN).                                         *)
(* ------------------------------------------------------------------------- *)

let STDS_FAR_SCALAR_LOW = prove
 (`!g0 A0 T'.
     stds_gs_hyps /\ p3_std_initial g0 A0 /\ &0 <= T' /\ T' < stds_tm g0 /\ T' < &1
     ==> ?A1. !x s. A1 < p3_std_dist g0 x /\ &0 <= s /\ s <= T'
                    ==> &1 / &2 <= mfd_scalar (open_set_atlas (:real^3)) (stds_gs g0 s) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] STDS_GS_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  X_CHOOSE_THEN `C0:real` (X_CHOOSE_THEN `Cs:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cyl"))))
    STDS_CYL_UNIF THEN
  ABBREV_TAC `Kt = inv(&2 * (&1 - T'))` THEN
  MP_TAC(SPECL [`sqrt C0 * Kt`; `&1 / &2`]
    (INST_TYPE [`:3`,`:N`] LCK_CURVATURE_STABILITY)) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ST"))) THEN
  UNDISCH_TAC `stds_gs_hyps` THEN REWRITE_TAC[stds_gs_hyps] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `stds_tm g0`; `stds_gs g0`; `T':real`;
                `{basis 1:real^3}`; `2`; `eta pow 2`] STDS_ASYM_CLOSE) THEN
  ASM_SIMP_TAC[COMPACT_SING; REAL_POW_LT; SING_SUBSET; IN_DELETE; IN_UNIV; STDS_BASIS1_NZ;
               IN_SING] THEN
  DISCH_THEN(X_CHOOSE_THEN `A2:real` (LABEL_TAC "CL")) THEN
  EXISTS_TAC `max A2 (A0 + sqrt(&2) * (&0 + &1))` THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `s:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `s < stds_tm g0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `A0 + sqrt(&2) * (&0 + &1) <= p3_std_dist g0 x` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `0`] STDS_FAR_MU) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `0`] STDS_NMAP_OPEN_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `exp(--(&0 + &1))`;
                `exp(&0 + &1)`] STDS_NMAP_DIFFEO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_EXP_POS_LT; REAL_EXP_MONO_LT] THEN REAL_ARITH_TAC;
    REWRITE_TAC[GSYM stds_aW] THEN STRIP_TAC] THEN
  ABBREV_TAC `h = stds_nmap g0 A0 x` THEN
  ABBREV_TAC `U = IMAGE (h:real^3->real^3) (stds_aW 0)` THEN
  SUBGOAL_THEN `metric_field (U:real^3->bool) (stds_gs g0 s)` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `s:real`] STDS_GS_RIEM) THEN
    ASM_REWRITE_TAC[stds_gs_hyps] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (stds_aW 0) (mpullback (h:real^3->real^3) (stds_gs g0 s)) /\
                metric_field (stds_aW 0) (cylinder_flow s)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [`U:real^3->bool`;
        `(\z. inv(norm(p3_std_nc g0 A0 x)) % (transp(stds_rot x) ** z)) o p3_std_nc g0 A0`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
      REWRITE_TAC[STDS_AW_SUBSET] THEN MATCH_MP_TAC RFB_CYL_METRIC_FIELD THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "ST" (MP_TAC o SPECL [`stds_aW 0`; `cylinder_flow s`;
                                 `mpullback (h:real^3->real^3) (stds_gs g0 s)`;
                                 `basis 1:real^3`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[STDS_AW_BASIS] THEN CONJ_TAC THENL
     [USE_THEN "cyl" (MP_TAC o SPECL [`T':real`; `s:real`; `basis 1:real^3`]) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[STDS_BASIS1_NZ] THEN ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
      EXPAND_TAC "h" THEN USE_THEN "CL" MATCH_MP_TAC THEN
      EXISTS_TAC `basis 1:real^3` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `stds_aW 0`; `h:real^3->real^3`;
                 `(\z. inv(norm(p3_std_nc g0 A0 x)) % (transp(stds_rot x) ** z)) o
                  p3_std_nc g0 A0`;
                 `stds_gs g0 s`; `basis 1:real^3`] LSCALAR_PULLBACK) THEN
  ASM_REWRITE_TAC[STDS_AW_BASIS] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(h:real^3->real^3) (basis 1) = x` SUBST1_TAC THENL
   [EXPAND_TAC "h" THEN MATCH_MP_TAC STDS_NMAP_E1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[P2C_OPEN_SET_MFD_SCALAR] THEN
  SUBGOAL_THEN `s < &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[RFB_CYL_SCALAR; STDS_BASIS1_NZ] THEN
  SUBGOAL_THEN `&1 <= &1 / (&1 - s)` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_SUB_LT] THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;
let STDS_G0_SCALAR_POS = prove
 (`!g0 A0 (x:real^3). p3_std_initial g0 A0
                      ==> &0 < mfd_scalar (open_set_atlas (:real^3)) g0 x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p3_std_initial]) THEN
  (* every sectional curvature is at most R/2 *)
  SUBGOAL_THEN `!u v. ~collinear {vec 0,u,v}
                      ==> mfd_sectional (open_set_atlas (:real^3)) g0 x u v <=
                          mfd_scalar (open_set_atlas (:real^3)) g0 x / &2`
  (LABEL_TAC "half") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_rm_norm (open_set_atlas (:real^3)) g0 x` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `abs a <= b ==> a <= b`) THEN
      MATCH_MP_TAC RFA_MFD_SECTIONAL_LE_NORM THEN EXISTS_TAC `euclidean:(real^3)topology` THEN
      ASM_REWRITE_TAC[P2C_EUCLID_FACTS; IN_UNIV];
      MATCH_MP_TAC P2BX0_RM_NORM_LE_HALF_SCALAR THEN EXISTS_TAC `euclidean:(real^3)topology` THEN
      ASM_REWRITE_TAC[P2C_EUCLID_FACTS; IN_UNIV] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `p3_std_dist g0 x < r0` THENL
   [USE_THEN "half" (MP_TAC o SPECL [`basis 1:real^3`; `basis 2:real^3`]) THEN
    REWRITE_TAC[P3S_NONCOLL_BASIS] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^3`; `basis 1:real^3`; `basis 2:real^3`] o
      check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `&1 / &4`)) (concl th))) THEN
    ASM_REWRITE_TAC[P3S_NONCOLL_BASIS] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(p3_std_dist g0 x < r0)` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] P3S_DIST_0) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `x:real^3` STDS_ROT) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `Q = stds_rot x` THEN
  ABBREV_TAC `u = (Q:real^3^3) ** basis 2` THEN
  ABBREV_TAC `v = (Q:real^3^3) ** basis 3` THEN
  SUBGOAL_THEN `(u:real^3) dot u = &1 /\ (v:real^3) dot v = &1 /\ u dot v = &0`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["u"; "v"] THEN
    ASM_SIMP_TAC[STDS_ORTH_DOT; DOT_BASIS_BASIS; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^3) dot x = &0 /\ (v:real^3) dot x = &0` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["u"; "v"] THEN
    SUBGOAL_THEN `(x:real^3) = norm x % ((Q:real^3^3) ** basis 1)`
    (fun th -> ONCE_REWRITE_TAC[th]) THENL
     [ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_RINV; NORM_EQ_0; VECTOR_MUL_LID];
      ALL_TAC] THEN
    REWRITE_TAC[DOT_RMUL] THEN
    ASM_SIMP_TAC[STDS_ORTH_DOT; DOT_BASIS_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~collinear {vec 0,u:real^3,v}` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["u"; "v"] THEN
    MP_TAC(ISPECL [`\z:real^3. (Q:real^3^3) ** z`; `{vec 0:real^3,basis 2,basis 3}`]
                  COLLINEAR_LINEAR_IMAGE_EQ) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN REPEAT GEN_TAC THEN
      DISCH_THEN(MP_TAC o AP_TERM `\z:real^3. transp(Q:real^3^3) ** z`) THEN
      REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP ORTHOGONAL_MATRIX_TRANSP_LMUL th]) THEN
      REWRITE_TAC[MATRIX_VECTOR_MUL_LID];
      ALL_TAC] THEN
    REWRITE_TAC[IMAGE_CLAUSES; MATRIX_VECTOR_MUL_RZERO; P3S_NONCOLL_BASIS] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `u:real^3`; `u:real^3`]
                P3S_ROT_BIL) THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `v:real^3`; `v:real^3`]
                P3S_ROT_BIL) THEN
  MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `u:real^3`; `v:real^3`]
                P3S_ROT_BIL) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; real_div; REAL_SUB_RZERO; REAL_ADD_LID;
              REAL_MUL_RID] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 < p3s_rad_b g0 (norm(x:real^3))` ASSUME_TAC THENL
   [ASM_MESON_TAC[P3S_ROT_AB]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_sectional (open_set_atlas (:real^3)) g0 x u v =
                p3s_sec_tan g0 (p3_std_dist g0 x)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `u:real^3`; `v:real^3`]
                  P3S_ROT_SEC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; real_div; REAL_SUB_RZERO; REAL_ADD_LID;
                REAL_MUL_RID; REAL_POW_2] THEN
    SUBGOAL_THEN `~(p3s_rad_b g0 (norm(x:real^3)) = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `r0:real`] P3S_ROT_SEC_TAN_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p3_std_dist g0 x` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p3s_sec_tan")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  USE_THEN "half" (MP_TAC o SPECL [`u:real^3`; `v:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* R > 0 at every point of Gs on [0,1): sec > 0 for t > 0 (SMP), R(g0) > 0. *)

let STDS_GS_SCALAR_POS = prove
 (`!d:real^4->bool.
     stds_tm_hyps d /\ P2C_REQ_SMP_POS_STATEMENT (:real^3)
     ==> !g0 A0 t (x:real^3).
           p3_std_initial g0 A0 /\ &0 <= t /\ t < &1
           ==> &0 < mfd_scalar (open_set_atlas (:real^3)) (stds_gs g0 t) x`,
  GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[stds_tm_hyps] th))
    ASSUME_TAC) THEN
  MAP_EVERY X_GEN_TAC [`g0:real^3->real^3^3`; `A0:real`; `t:real`; `x:real^3`] THEN
  STRIP_TAC THEN
  MP_TAC(SPEC `d:real^4->bool` STDS_TM_EQ_1) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] STDS_GS_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `t = &0` THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC STDS_G0_SCALAR_POS THEN
    EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `d:real^4->bool` STDS_GS_SEC_POS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`t:real`; `x:real^3`; `basis 1:real^3`; `basis 2:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[P3S_NONCOLL_BASIS] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `t:real`; `x:real^3`] STDS_GS_SEC_CONSEQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `d:real^4->bool` STDS_GS_SEC_NONNEG) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `stds_gs g0 t`;
                 `x:real^3`; `basis 1:real^3`; `basis 2:real^3`] RFA_MFD_SECTIONAL_LE_NORM) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[P2C_EUCLID_FACTS; IN_UNIV; P3S_NONCOLL_BASIS] THEN
    MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `t:real`] STDS_GS_RIEM) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `&0 < mfd_sectional (open_set_atlas (:real^3)) (stds_gs g0 t) x
                    (basis 1) (basis 2)` THEN
  REAL_ARITH_TAC);;

let STDS_R_LOWER_EARLY = prove
 (`!d:real^4->bool.
     stds_tm_hyps d /\ P2C_REQ_SMP_POS_STATEMENT (:real^3)
     ==> !g0 A0 t0. p3_std_initial g0 A0 /\ t0 < &1
                    ==> ?m. &0 < m /\
                            !x t. &0 <= t /\ t <= t0
                                  ==> m <= mfd_scalar (open_set_atlas (:real^3))
                                                      (stds_gs g0 t) x`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[stds_tm_hyps] (CONJUNCT1 th))) THEN
  MAP_EVERY X_GEN_TAC [`g0:real^3->real^3^3`; `A0:real`; `t0:real`] THEN STRIP_TAC THEN
  MP_TAC(SPEC `d:real^4->bool` STDS_TM_EQ_1) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] STDS_GS_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `T' = max (&0) t0` THEN
  SUBGOAL_THEN `&0 <= T' /\ T' < &1 /\ t0 <= T'` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "T'" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `T':real`] STDS_FAR_SCALAR_LOW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `A1':real` (LABEL_TAC "far")) THEN
  ABBREV_TAC `A1 = max (&1) A1'` THEN
  SUBGOAL_THEN `&0 <= A1 /\ &0 < A1 /\ A1' <= A1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "A1" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  (* the continuous function on the compact set *)
  SUBGOAL_THEN
   `continuous_map
      (prod_topology (subtopology euclideanreal {t | &0 <= t /\ t < &1})
                     (subtopology euclidean (topspace (euclidean:(real^3)topology))),
       euclideanreal)
      (\z. mfd_scalar (open_set_atlas (:real^3)) (stds_gs g0 (FST z)) (SND z))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_MFD_SCALAR_CONTINUOUS_GEN THEN REWRITE_TAC[P2C_EUCLID_FACTS] THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `t:real`] STDS_GS_RIEM) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      UNDISCH_TAC `p3_partial_std g0 (&1) (stds_gs g0)` THEN
      REWRITE_TAC[p3_partial_std; ricci_flow_from] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `KK = real_interval[&0,T'] CROSS cball(vec 0:real^3,p3s_rad_rinv g0 A1)` THEN
  SUBGOAL_THEN
   `compact_in (prod_topology (subtopology euclideanreal {t | &0 <= t /\ t < &1})
                              (subtopology euclidean (topspace (euclidean:(real^3)topology))))
               KK`
  ASSUME_TAC THENL
   [EXPAND_TAC "KK" THEN REWRITE_TAC[COMPACT_IN_CROSS] THEN REPEAT DISJ2_TAC THEN
    REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN; SUBTOPOLOGY_UNIV] THEN
    REWRITE_TAC[COMPACT_IN_EUCLIDEAN; COMPACT_CBALL; GSYM real_compact_def;
                REAL_COMPACT_INTERVAL] THEN
    REWRITE_TAC[SUBSET_UNIV] THEN REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (\z. mfd_scalar (open_set_atlas (:real^3)) (stds_gs g0 (FST z)) (SND z))
                      (KK:real#real^3->bool)` REAL_COMPACT_ATTAINS_INF) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[real_compact_def] THEN MATCH_MP_TAC IMAGE_COMPACT_IN THEN
      EXISTS_TAC `prod_topology (subtopology euclideanreal {t | &0 <= t /\ t < &1})
                     (subtopology euclidean (topspace (euclidean:(real^3)topology)))` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[IMAGE_EQ_EMPTY] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `(&0,vec 0:real^3)` THEN EXPAND_TAC "KK" THEN
      REWRITE_TAC[IN_CROSS; IN_REAL_INTERVAL; CENTRE_IN_CBALL] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `A1:real`] P3S_RINV_POS) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `z0:real#real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < mfd_scalar (open_set_atlas (:real^3)) (stds_gs g0 (FST(z0:real#real^3)))
                                (SND z0)` ASSUME_TAC THENL
   [MP_TAC(SPEC `d:real^4->bool` STDS_GS_SCALAR_POS) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `A0:real` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z0:real#real^3) IN KK` THEN EXPAND_TAC "KK" THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    SPEC_TAC(`z0:real#real^3`,`z0:real#real^3`) THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    REWRITE_TAC[IN_CROSS; IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `min (&1 / &2) (mfd_scalar (open_set_atlas (:real^3))
                              (stds_gs g0 (FST(z0:real#real^3))) (SND z0))` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `t:real`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `A1 < p3_std_dist g0 x` THENL
   [MATCH_MP_TAC(REAL_ARITH `a <= b ==> min a c <= b`) THEN
    USE_THEN "far" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `c <= b ==> min a c <= b`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(t,x):real#real^3` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> t = `KK:real#real^3->bool`)) (concl th))) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN EXPAND_TAC "KK" THEN
  REWRITE_TAC[IN_CROSS; IN_REAL_INTERVAL; IN_CBALL_0] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `A1:real`; `x:real^3`] P2CN_DIST_COMPARE) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Repair (b), the corrected last paragraph of MT Prop                       *)
(* 12.31: with t0 = max 0 (1 - r^2/(32 C)), a point with R(x,t1) <          *)
(* 1/(32 C (1-t1)), t1 >= t0, would keep R bounded at x up to t = 1 by      *)
(* forward Lemma 11.2, against STDS_R_TO_INFTY; with STDS_R_LOWER_EARLY on  *)
(* [0,t0] this is Prop 12.31: R(x,t) >= c/(1-t).                            *)
(* ------------------------------------------------------------------------- *)

let STDS_R_LOWER_LATE = prove
 (`!d:real^4->bool.
     stds_tm_hyps d
     ==> !g0 A0. p3_std_initial g0 A0
                 ==> ?c1 t0. &0 < c1 /\ t0 < &1 /\
                             !x t. t0 <= t /\ t < &1
                                   ==> c1 / (&1 - t) <=
                                       mfd_scalar (open_set_atlas (:real^3)) (stds_gs g0 t) x`,
  GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[stds_tm_hyps] th)) THEN
  MAP_EVERY X_GEN_TAC [`g0:real^3->real^3^3`; `A0:real`] THEN DISCH_TAC THEN
  MP_TAC(SPEC `d:real^4->bool` STDS_TM_EQ_1) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] STDS_GS_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `d:real^4->bool` STDS_GS_SEC_NONNEG) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "sec") THEN
  MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`] STDS_GV_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "per"))))))) THEN
  MP_TAC(SPEC `d:real^4->bool` STDS_DERIV_BOUNDS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps:real` (X_CHOOSE_THEN `C:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]))))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DB"))) THEN
  ABBREV_TAC `C' = max C (&2)` THEN
  SUBGOAL_THEN `&0 < C' /\ &0 < inv(r pow 2) /\ &0 < r pow 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "C'" THEN REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_POW_LT]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`inv(&32 * C')`; `max (&0) (&1 - r pow 2 / (&32 * C'))`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `&0 < b ==> max (&0) (&1 - b) < &1`) THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `t1:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= t1 /\ &0 < &1 - t1 /\ &1 - t1 <= r pow 2 / (&32 * C')`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `R1 = mfd_scalar (open_set_atlas (:real^3)) (stds_gs g0 t1) x` THEN
  SUBGOAL_THEN `&0 < &16 * C' * (max (&0) R1 + inv(r pow 2)) /\
                (&1 - t1) * (&16 * C' * (max (&0) R1 + inv(r pow 2))) <= &1`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(&1 - t1) * max (&0) R1 <= inv(&32 * C')` ASSUME_TAC THENL
     [ASM_CASES_TAC `R1 <= &0` THENL
       [SUBGOAL_THEN `max (&0) R1 = &0` SUBST1_TAC THENL
         [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_MUL_RZERO; REAL_LE_INV_EQ] THEN
          ASM_REAL_ARITH_TAC];
        SUBGOAL_THEN `max (&0) R1 = R1` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `R1 < inv(&32 * C') / (&1 - t1)` THEN
        ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(&1 - t1) * inv(r pow 2) <= inv(&32 * C')` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `r pow 2 / (&32 * C') * inv(r pow 2)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN
        SUBGOAL_THEN `~(r pow 2 = &0) /\ ~(C' = &0)` MP_TAC THENL
         [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&16 * C' * inv(&32 * C') = &1 / &2` ASSUME_TAC THENL
     [UNDISCH_TAC `&0 < C'` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `(&1 - t1) * (&16 * C' * (max (&0) R1 + inv(r pow 2))) =
                  (&16 * C') * ((&1 - t1) * max (&0) R1) +
                  (&16 * C') * ((&1 - t1) * inv(r pow 2))` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `!c k. a <= c * k /\ b <= c * k /\ c * k = &1 / &2
                                   ==> a + b <= &1`) THEN
    EXISTS_TAC `&16 * C'` THEN EXISTS_TAC `inv(&32 * C')` THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&0 < C'` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  (* R stays below M := 2 (max 0 R1 + r^-2) at x up to time 1 *)
  ABBREV_TAC `M = &2 * (max (&0) R1 + inv(r pow 2))` THEN
  MP_TAC(SPEC `d:real^4->bool` STDS_R_TO_INFTY) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`; `x:real^3`; `M:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inf"))) THEN
  ABBREV_TAC `s = max t2 ((&1 + t1) / &2)` THEN
  SUBGOAL_THEN `t2 <= s /\ t1 < s /\ s < &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "inf" (MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REAL_NOT_LT] THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas (:real^3)) (stds_gs g0 t1)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`g0:real^3->real^3^3`; `A0:real`; `t1:real`] STDS_GS_RIEM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `rr = inv(&2 * C' * sqrt(max (rfs_vscalar (stds_gv g0) t1 x) (inv(r pow 2))))` THEN
  SUBGOAL_THEN `&0 < rr` ASSUME_TAC THENL
   [EXPAND_TAC "rr" THEN REWRITE_TAC[REAL_LT_INV_EQ] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SQRT_POS_LT THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open (rfs_vball (stds_gv g0) t1 x rr) /\
                (x:real^3) IN rfs_vball (stds_gv g0) t1 x rr` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`g0:real^3->real^3^3`; `t1:real`; `x:real^3`; `rr:real`] STDS_GV_BALL) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[GSYM OPEN_IN_EUCLIDEAN] THEN
    SIMP_TAC[MFD_BALL_OPEN; MFD_CENTRE_IN_BALL; P2C_EUCLID_FACTS; IN_UNIV;
             ASSUME `riemannian_metric (open_set_atlas (:real^3)) (stds_gs g0 t1)`;
             ASSUME `&0 < rr`];
    ALL_TAC] THEN
  UNDISCH_TAC `P2C_LEMMA_11_2_DB_STATEMENT (:real^3)` THEN
  REWRITE_TAC[P2C_LEMMA_11_2_DB_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`stds_gv g0`; `C':real`; `r:real`; `x:real^3`; `t1:real`;
                             `s:real`; `rr:real`]) THEN
  SUBGOAL_THEN `min t1 s = t1 /\ max t1 s = s` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`z:real^3`; `u:real`] THEN
      REWRITE_TAC[STDS_GV_TOPSPACE] THEN STRIP_TAC THEN
      USE_THEN "DB" (MP_TAC o SPECL [`z:real^3`; `u:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      REWRITE_TAC[STDS_GV_TOPSPACE] THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "rr" THEN REWRITE_TAC[REAL_LE_REFL];
      REWRITE_TAC[STDS_GV_SCALAR] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ a <= b ==> abs a <= b`) THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 - t1` THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `inv(&16 * C' * (max (&0) R1 + inv(r pow 2))) =
                    &1 / (&16 * C' * (max (&0) R1 + inv(r pow 2)))` SUBST1_TAC THENL
       [REWRITE_TAC[real_div; REAL_MUL_LID]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
      UNDISCH_TAC `(&1 - t1) * (&16 * C' * (max (&0) R1 + inv(r pow 2))) <= &1` THEN
      REAL_ARITH_TAC;
      USE_THEN "per" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      TRY DISCH_TAC THEN REWRITE_TAC[STDS_GV_PARTS] THEN
      SUBGOAL_THEN `(&0 <= t1 /\ t1 < stds_tm g0) /\ (&0 <= s /\ s < stds_tm g0)`
      (fun th -> REWRITE_TAC[th]) THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC MFD_DIFFEO_ID THEN
      ASM_REWRITE_TAC[P2C_EUCLID_FACTS; OPEN_IN_EUCLIDEAN]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`s:real`; `x:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  REWRITE_TAC[STDS_GV_SCALAR] THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "M" THEN
  REAL_ARITH_TAC);;

(* MT Prop 12.31 for the maximal standard flow.                               *)

let STDS_PROP_12_31 = prove
 (`!d:real^4->bool.
     stds_tm_hyps d /\ P2C_REQ_SMP_POS_STATEMENT (:real^3)
     ==> !g0 A0. p3_std_initial g0 A0
                 ==> ?c. &0 < c /\
                         !x t. &0 <= t /\ t < &1
                               ==> c / (&1 - t) <=
                                   mfd_scalar (open_set_atlas (:real^3)) (stds_gs g0 t) x`,
  GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`g0:real^3->real^3^3`; `A0:real`] THEN DISCH_TAC THEN
  MP_TAC(SPEC `d:real^4->bool` STDS_R_LOWER_LATE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:real` (X_CHOOSE_THEN `t0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "late"))))) THEN
  MP_TAC(SPEC `d:real^4->bool` STDS_R_LOWER_EARLY) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`; `t0:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "early"))) THEN
  EXISTS_TAC `min c1 (m * (&1 - t0))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < a /\ &0 < b ==> &0 < min a b`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `t:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 - t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `t0 <= t` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c1 / (&1 - t)` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN REAL_ARITH_TAC;
      USE_THEN "late" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `m:real` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= m * (&1 - t0) /\ m * (&1 - t0) <= m * (&1 - t)
                             ==> x <= m * (&1 - t)`) THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    USE_THEN "early" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

