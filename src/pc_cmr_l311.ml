(* ========================================================================= *)
(* Unit pc_cmr_l311 (a unit of the replacement chain of pc_cm_replacement):  *)
(* CM Lemma 3.11 in the G-weighted setting.                                  *)
(*                                                                           *)
(* The difference of the G-energies of a map and of the                      *)
(* minimizer with its boundary values, on any open subset of the disc.  The *)
(* weight term int |u - v| |dv|^2 is bounded with the Hardy inequality and  *)
(* the interior gradient bound for small-energy harmonic maps, as in the    *)
(* convexity proof (pc_hm_convexity).                                         *)
(* ========================================================================= *)

needs "src/pc_cmr_cont.ml";;
needs "src/pc_wan_sob2c.ml";;

prioritize_real();;
type_invention_error := true;;

let CMR_DENS_DIFF = prove
 (`!(G:real^K->real^K^K) S Lam1 C3 (p:real^K) q (a:real^K) b.
     (!z xi. z IN S ==> norm(G z ** xi) <= Lam1 * norm xi) /\
     (!y z xi. y IN S /\ z IN S ==> norm((G y - G z) ** xi) <= C3 * norm(y - z) * norm xi) /\
     (!z. transp(G z) = G z) /\ p IN S /\ q IN S
     ==> abs(a dot (G p ** a) - b dot (G q ** b))
         <= Lam1 * norm(a - b) * (norm a + norm b) + C3 * norm(p - q) * norm b pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `a dot ((G:real^K->real^K^K) p ** a) - b dot (G q ** b) =
    (a - b) dot (G p ** (a + b)) + b dot ((G p - G q) ** b)`
  SUBST1_TAC THENL
   [REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_SUB_RDISTRIB;
                DOT_LADD; DOT_RADD; DOT_LSUB; DOT_RSUB] THEN
    MP_TAC(ISPECL [`(G:real^K->real^K^K) p`; `a:real^K`; `b:real^K`] HMC_SYM_DOT) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `abs x <= a /\ abs y <= b ==> abs(x + y) <= a + b`) THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
   [EXISTS_TAC `norm(a - b:real^K) * norm((G:real^K->real^K^K) p ** (a + b))` THEN
    REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `l * x * y = x * (l * y)`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Lam1 * norm(a + b:real^K)` THEN
    ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `&0 <= Lam1` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`p:real^K`; `basis 1:real^K`] o
        check (fun th -> is_forall(concl th) &&
                         can (find_term (fun t -> t = `Lam1:real`)) (concl th))) THEN
      ASM_SIMP_TAC[NORM_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
      MP_TAC(ISPEC `(G:real^K->real^K^K) p ** basis 1` NORM_POS_LE) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[NORM_TRIANGLE];
    EXISTS_TAC `norm(b:real^K) * norm(((G:real^K->real^K^K) p - G q) ** b)` THEN
    REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN
    REWRITE_TAC[REAL_POW_2] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `c * d * b * b' = b * (c * d * b')`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[NORM_POS_LE]]);;

let CMR_CS2 = prove
 (`!A1 A2 B1 B2.
     &0 <= A1 /\ &0 <= A2 /\ &0 <= B1 /\ &0 <= B2
     ==> sqrt A1 * sqrt B1 + sqrt A2 * sqrt B2 <= sqrt(A1 + A2) * sqrt(B1 + B2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sqrt(A1 + A2) * sqrt(B1 + B2) = sqrt((A1 + A2) * (B1 + B2))`
  SUBST1_TAC THENL [ASM_SIMP_TAC[SQRT_MUL; REAL_LE_ADD]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RSQRT THEN
  SUBGOAL_THEN `(sqrt A1 * sqrt B1 + sqrt A2 * sqrt B2) pow 2 =
                A1 * B1 + A2 * B2 + &2 * (sqrt A1 * sqrt B2) * (sqrt A2 * sqrt B1)`
  SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ARITH `(a * b + c * d) pow 2 =
                            (a pow 2) * (b pow 2) + (c pow 2) * (d pow 2) + &2 * (a * d) * (c * b)`] THEN
    ASM_SIMP_TAC[SQRT_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * (sqrt A1 * sqrt B2) * (sqrt A2 * sqrt B1) <= A1 * B2 + A2 * B1`
  MP_TAC THENL
   [MP_TAC(SPEC `sqrt A1 * sqrt B2 - sqrt A2 * sqrt B1` REAL_LE_POW_2) THEN
    REWRITE_TAC[REAL_ARITH `(x - y) pow 2 = x pow 2 + y pow 2 - &2 * x * y`] THEN
    REWRITE_TAC[REAL_POW_MUL] THEN ASM_SIMP_TAC[SQRT_POW_2] THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let CMR_LNORM2_SQRT = prove
 (`!(g:real^N->real^M) s.
     g IN lspace s (&2) ==> lnorm s (&2) g = sqrt(drop(integral s (\x. lift(norm(g x) pow 2))))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM WAN_SOB_LNORM2_SQ] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC POW_2_SQRT THEN ASM_SIMP_TAC[LNORM_POS_LE]);;

let CMR_WEIGHT_TERM = prove
 (`!S (G:real^K->real^K^K) e0 (C:num->real) Lam.
     (!(a:real^2) r (u:real^2->real^K) l x.
        &0 < r /\ cm_harmonic S G (ball(a,r)) u /\ wan_w12 (ball(a,r)) u /\
        wan_gdir (ball(a,r)) G u <= e0 /\
        ALL (\i. 1 <= i /\ i <= 2) l /\ ~(l = []) /\ x IN ball(a,r / &2)
        ==> r pow (LENGTH l) * norm(iterated_partial l u x)
            <= C (LENGTH l) * sqrt(wan_gdir (ball(a,r)) G u)) /\
     (!k. &0 < C k) /\
     smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o G) /\
     (!z xi. &0 <= xi dot (G z ** xi) /\ xi dot (G z ** xi) <= Lam * norm xi pow 2)
     ==> ?CW. &0 < CW /\
              !(a:real^2) r (u:real^2->real^K) v M.
                &0 < r /\ cm_harmonic S G (ball(a,r)) v /\ wan_w12 (ball(a,r)) v /\
                wan_gdir (ball(a,r)) G v <= e0 /\ wan_w12 (ball(a,r)) u /\
                u continuous_on ball(a,r) /\
                wan_w120 (ball(a,r)) (\x. u x - v x) /\
                (!x. x IN ball(a,r) ==> norm(u x - v x) <= M)
                ==> (!i. 1 <= i /\ i <= 2
                         ==> (\x. lift(norm(u x - v x) * norm(partial_derivative i v x) pow 2))
                               integrable_on ball(a,r)) /\
                    sum(1..2) (\i. drop(integral (ball(a,r))
                       (\x. lift(norm(u x - v x) * norm(partial_derivative i v x) pow 2))))
                    <= CW * sqrt(wan_gdir (ball(a,r)) G v) *
                       sqrt(wan_dir (ball(a,r)) (\x. u x - v x)) *
                       sqrt(wan_dir (ball(a,r)) v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(:2)`; `(:K)`] WAN_HARDY_BALL) THEN
  REWRITE_TAC[WAN_HARDY_BALL_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `CH:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `sqrt(&2 * CH) * (C:num->real) 1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `continuously_differentiable 1 (ball(a:real^2,r)) (v:real^2->real^K)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `cm_harmonic S (G:real^K->real^K^K) (ball(a,r)) (v:real^2->real^K)` THEN
    SIMP_TAC[cm_harmonic; smooth_map_on];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> (\x. partial_derivative i (v:real^2->real^K) x) IN lspace (ball(a,r)) (&2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HMC_PD_LSPACE THEN
    ASM_REWRITE_TAC[OPEN_BALL; DIMINDEX_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. lift(norm((u:real^2->real^K) x - v x))) continuous_on ball(a,r)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
    EXISTS_TAC `1` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> (\x. lift(norm((u:real^2->real^K) x - v x) *
                      norm(partial_derivative i (v:real^2->real^K) x)))
              IN lspace (ball(a,r)) (&2) /\
            (\x. lift(norm(partial_derivative i (v:real^2->real^K) x))) IN lspace (ball(a,r)) (&2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(\x. lift(norm(partial_derivative i (v:real^2->real^K) x))) IN
                  lspace (ball(a,r)) (&2)` ASSUME_TAC THENL
     [MATCH_MP_TAC LSPACE_NORM THEN ASM_SIMP_TAC[]; ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[LIFT_CMUL] THEN
    MATCH_MP_TAC(BETA_RULE(ISPECL
      [`ball(a:real^2,r)`; `\x. norm((u:real^2->real^K) x - v x)`;
       `\x. lift(norm(partial_derivative i (v:real^2->real^K) x))`; `M:real`]
      WAN_LSPACE2_BOUNDED_MUL)) THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; OPEN_BALL; REAL_ABS_NORM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> (\x. lift(norm((u:real^2->real^K) x - v x) *
                      norm(partial_derivative i (v:real^2->real^K) x) pow 2))
              integrable_on ball(a,r) /\
            drop(integral (ball(a,r))
              (\x. lift(norm((u:real^2->real^K) x - v x) * norm(partial_derivative i v x) pow 2)))
            <= sqrt(drop(integral (ball(a,r))
                 (\x. lift(norm(u x - v x) pow 2 * norm(partial_derivative i v x) pow 2)))) *
               sqrt(drop(integral (ball(a,r)) (\x. lift(norm(partial_derivative i v x) pow 2))))`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`ball(a:real^2,r)`; `&2`; `&2`;
                   `\x. lift(norm((u:real^2->real^K) x - v x) *
                             norm(partial_derivative i (v:real^2->real^K) x))`;
                   `\x. lift(norm(partial_derivative i (v:real^2->real^K) x))`]
                  HOELDER_INEQUALITY_FULL) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[NORM_LIFT; REAL_ABS_MUL; REAL_ABS_NORM] THEN
    REWRITE_TAC[REAL_ARITH `(a * b) * b = a * b pow 2`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lnorm (ball(a:real^2,r)) (&2)
                  (\x. lift(norm((u:real^2->real^K) x - v x) *
                            norm(partial_derivative i (v:real^2->real^K) x))) *
                lnorm (ball(a,r)) (&2) (\x. lift(norm(partial_derivative i v x)))` THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[CMR_LNORM2_SQRT; NORM_LIFT; REAL_ABS_MUL; REAL_ABS_NORM; REAL_POW_MUL;
                 REAL_LE_REFL];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e0:real`; `C:num->real`;
                 `Lam:real`; `a:real^2`; `r:real`; `v:real^2->real^K`] HMC_GRAD_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^2`; `r:real`; `\x. (u:real^2->real^K) x - v x`] o
    check (fun th -> is_forall(concl th) &&
                     can (find_term (fun t -> t = `CH:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `v:real^2->real^K`; `\x. (u:real^2->real^K) x - v x`;
                 `(C:num->real) 1 * sqrt(wan_gdir (ball(a,r)) G (v:real^2->real^K))`]
                HMC_WEIGHTED_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o
      check (fun th -> is_forall(concl th) &&
                       can (find_term (fun t -> is_const t && fst(dest_const t) = "lnorm"))
                           (concl th) = false &&
                       can (find_term (fun t -> is_const t && fst(dest_const t) = "lift"))
                           (concl th) &&
                       can (find_term (fun t -> is_const t && fst(dest_const t) = "lspace"))
                           (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(MATCH_MP WAN_LSPACE2_SQNORM_INTEGRABLE (ASSUME
     `(\x. lift(norm((u:real^2->real^K) x - v x) *
                norm(partial_derivative i (v:real^2->real^K) x))) IN lspace (ball(a,r)) (&2)`)) THEN
    REWRITE_TAC[NORM_LIFT; REAL_ABS_MUL; REAL_ABS_NORM; REAL_POW_MUL];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `wan_dir (ball(a:real^2,r)) (v:real^2->real^K) =
    sum(1..2) (\i. drop(integral (ball(a,r)) (\x. lift(norm(partial_derivative i v x) pow 2))))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM WAN_GDIR_ID] THEN
    MP_TAC(ISPECL [`ball(a:real^2,r)`; `\y:real^K. mat 1:real^K^K`; `v:real^2->real^K`]
                  HMC_GDIR_CLASSICAL) THEN
    ASM_REWRITE_TAC[OPEN_BALL; DIMINDEX_2; MATRIX_VECTOR_MUL_LID; GSYM NORM_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> (\x. lift(norm((u:real^2->real^K) x - v x) pow 2 *
                      norm(partial_derivative i (v:real^2->real^K) x) pow 2))
              integrable_on ball(a,r) /\
            (\x. lift(norm(partial_derivative i (v:real^2->real^K) x) pow 2))
              integrable_on ball(a,r)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o
        check (fun th -> is_forall(concl th) &&
                         can (find_term (fun t -> is_const t && fst(dest_const t) = "lspace"))
                             (concl th) &&
                         can (find_term (fun t -> is_const t && fst(dest_const t) = "lift"))
                             (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o MATCH_MP WAN_LSPACE2_SQNORM_INTEGRABLE o CONJUNCT1) THEN
      REWRITE_TAC[NORM_LIFT; REAL_ABS_MUL; REAL_ABS_NORM; REAL_POW_MUL];
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o
        check (fun th -> is_forall(concl th) &&
                         can (find_term (fun t -> is_const t && fst(dest_const t) = "lspace"))
                             (concl th) &&
                         not (can (find_term (fun t -> is_const t && fst(dest_const t) = "lift"))
                                  (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o MATCH_MP WAN_LSPACE2_SQNORM_INTEGRABLE) THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sqrt(sum(1..2) (\i. drop(integral (ball(a:real^2,r))
             (\x. lift(norm((u:real^2->real^K) x - v x) pow 2 *
                       norm(partial_derivative i (v:real^2->real^K) x) pow 2))))) *
    sqrt(wan_dir (ball(a,r)) v)` THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUM_2] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `sqrt(drop(integral (ball(a:real^2,r))
             (\x. lift(norm((u:real^2->real^K) x - v x) pow 2 *
                       norm(partial_derivative 1 (v:real^2->real^K) x) pow 2)))) *
      sqrt(drop(integral (ball(a,r)) (\x. lift(norm(partial_derivative 1 v x) pow 2)))) +
      sqrt(drop(integral (ball(a:real^2,r))
             (\x. lift(norm((u:real^2->real^K) x - v x) pow 2 *
                       norm(partial_derivative 2 (v:real^2->real^K) x) pow 2)))) *
      sqrt(drop(integral (ball(a,r)) (\x. lift(norm(partial_derivative 2 v x) pow 2))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
       [FIRST_ASSUM(MP_TAC o SPEC `1` o
          check (fun th -> is_forall(concl th) &&
                           can (find_term (fun t -> is_const t && fst(dest_const t) = "sqrt"))
                               (concl th))) THEN
        REWRITE_TAC[ARITH] THEN SIMP_TAC[];
        FIRST_ASSUM(MP_TAC o SPEC `2` o
          check (fun th -> is_forall(concl th) &&
                           can (find_term (fun t -> is_const t && fst(dest_const t) = "sqrt"))
                               (concl th))) THEN
        REWRITE_TAC[ARITH] THEN SIMP_TAC[]];
      MATCH_MP_TAC CMR_CS2 THEN REPEAT CONJ_TAC THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
      REWRITE_TAC[LIFT_DROP] THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2; ARITH]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= wan_gdir (ball(a:real^2,r)) G (v:real^2->real^K) /\
    &0 <= wan_dir (ball(a:real^2,r)) (\x. (u:real^2->real^K) x - v x) /\
    &0 <= wan_dir (ball(a:real^2,r)) (v:real^2->real^K)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HMC_GDIR_POS THEN EXISTS_TAC `Lam:real` THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN ASM_MESON_TAC[cm_harmonic];
      MATCH_MP_TAC WAN_DIR_POS THEN ASM_MESON_TAC[wan_w120];
      MATCH_MP_TAC WAN_DIR_POS THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[SQRT_POS_LE] THEN
  MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_MUL] THEN
  ASM_SIMP_TAC[SQRT_POW_2; REAL_ARITH `&0 < CH ==> &0 <= &2 * CH`] THEN
  RULE_ASSUM_TAC(BETA_RULE) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `&2 * ((C:num->real) 1 * sqrt(wan_gdir (ball(a:real^2,r)) G (v:real^2->real^K))) pow 2 *
    drop(integral (ball(a,r))
           (\x. lift(norm((u:real^2->real^K) x - v x) pow 2 / (r - norm(x - a)) pow 2)))` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_POW_MUL] THEN ASM_SIMP_TAC[SQRT_POW_2] THEN
  SUBGOAL_THEN `&0 <= (C:num->real) 1 pow 2 * wan_gdir (ball(a:real^2,r)) G (v:real^2->real^K)`
  MP_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  UNDISCH_TAC
   `drop(integral (ball(a:real^2,r))
           (\x. lift(norm((u:real^2->real^K) x - v x) pow 2 / (r - norm(x - a)) pow 2)))
    <= CH * wan_dir (ball(a,r)) (\x. u x - v x)` THEN
  ABBREV_TAC
   `X = drop(integral (ball(a:real^2,r))
           (\x. lift(norm((u:real^2->real^K) x - v x) pow 2 / (r - norm(x - a)) pow 2)))` THEN
  ABBREV_TAC `k = (C:num->real) 1 pow 2 * wan_gdir (ball(a:real^2,r)) G (v:real^2->real^K)` THEN
  ABBREV_TAC `dd = wan_dir (ball(a:real^2,r)) (\x. (u:real^2->real^K) x - v x)` THEN
  REWRITE_TAC[REAL_ARITH `((&2 * CH) * c) * g = &2 * CH * (c * g)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `k * X <= k * (CH * dd) ==> &2 * k * X <= (&2 * CH * k) * dd`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]);;

(* G-energies on an open subset are integrals of the weak partials on the   *)
(* larger open set.                                                          *)

let CMR_GDIR_RESTRICT = prove
 (`!s t (G:real^K->real^K^K) (u:real^N->real^K).
     open s /\ open t /\ t SUBSET s /\ wan_w12 s u
     ==> wan_gdir t G u =
         sum(1..dimindex(:N))
            (\i. drop(integral t (\x. lift(wan_wd s i u x dot (G(u x) ** wan_wd s i u x)))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_gdir] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `i:num`; `u:real^N->real^K`] WAN_WD_WORKS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_wd s i (u:real^N->real^K) IN lspace t (&2) /\
                wan_wpd t i u (wan_wd s i u)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN];
      MATCH_MP_TAC WAN_WPD_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `i:num`; `u:real^N->real^K`;
                 `wan_wd s i (u:real^N->real^K)`] CMR_WD_WORKS_P) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `i:num`; `u:real^N->real^K`;
                 `wan_wd t i (u:real^N->real^K)`; `wan_wd s i (u:real^N->real^K)`]
                WAN_WPD_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC INTEGRAL_SPIKE THEN
  EXISTS_TAC `{x | x IN t /\ ~(wan_wd t i (u:real^N->real^K) x = wan_wd s i u x)}` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN MESON_TAC[]);;

(* Sum of two Hoelder products.                                              *)

let CMR_HOELDER_SUM2 = prove
 (`!s (F1:real^N->real^K) (F2:real^N->real^K) (W1:real^N->real^K) (W2:real^N->real^K).
     F1 IN lspace s (&2) /\ F2 IN lspace s (&2) /\ W1 IN lspace s (&2) /\ W2 IN lspace s (&2)
     ==> (\x. lift(norm(F1 x) * norm(W1 x))) integrable_on s /\
         (\x. lift(norm(F2 x) * norm(W2 x))) integrable_on s /\
         drop(integral s (\x. lift(norm(F1 x) * norm(W1 x)))) +
         drop(integral s (\x. lift(norm(F2 x) * norm(W2 x))))
         <= sqrt(drop(integral s (\x. lift(norm(F1 x) pow 2))) +
                 drop(integral s (\x. lift(norm(F2 x) pow 2)))) *
            sqrt(drop(integral s (\x. lift(norm(W1 x) pow 2))) +
                 drop(integral s (\x. lift(norm(W2 x) pow 2))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `&2`; `&2`; `F1:real^N->real^K`; `W1:real^N->real^K`]
                HOELDER_INEQUALITY_FULL) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `&2`; `&2`; `F2:real^N->real^K`; `W2:real^N->real^K`]
                HOELDER_INEQUALITY_FULL) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_SIMP_TAC[CMR_LNORM2_SQRT] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sqrt(drop(integral s (\x. lift(norm((F1:real^N->real^K) x) pow 2)))) *
    sqrt(drop(integral s (\x. lift(norm((W1:real^N->real^K) x) pow 2)))) +
    sqrt(drop(integral s (\x. lift(norm((F2:real^N->real^K) x) pow 2)))) *
    sqrt(drop(integral s (\x. lift(norm((W2:real^N->real^K) x) pow 2))))` THEN
  ASM_SIMP_TAC[REAL_LE_ADD2] THEN MATCH_MP_TAC CMR_CS2 THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
  ASM_SIMP_TAC[WAN_LSPACE2_SQNORM_INTEGRABLE; LIFT_DROP; REAL_LE_POW_2]);;

(* Difference of two G-quadratic integrals over a subset A of B.            *)

let CMR_QUAD_DIFF_BOUND = prove
 (`!(G:real^K->real^K^K) S Lam Lam1 C3 M (A:real^2->bool) B (X:real^2->real^K)
    (Y:real^2->real^K) (p:real^2->real^K) (q:real^2->real^K).
     lebesgue_measurable A /\ lebesgue_measurable B /\ A SUBSET B /\
     X IN lspace B (&2) /\ Y IN lspace B (&2) /\ p measurable_on B /\ q measurable_on B /\
     (!x. x IN B ==> p x IN S /\ q x IN S /\ norm(p x - q x) <= M) /\
     ((vectorize:real^K^K->real^(K,K)finite_prod) o G) continuous_on (:real^K) /\
     (!z v. &0 <= v dot (G z ** v) /\ v dot (G z ** v) <= Lam * norm v pow 2) /\
     (!z xi. z IN S ==> norm(G z ** xi) <= Lam1 * norm xi) /\
     (!y z xi. y IN S /\ z IN S ==> norm((G y - G z) ** xi) <= C3 * norm(y - z) * norm xi) /\
     (!z. transp(G z) = G z) /\ &0 <= Lam1 /\ &0 <= C3
     ==> (\x. lift(norm(p x - q x) * norm(Y x) pow 2)) integrable_on B /\
         (\x. lift(norm(X x - Y x) * norm(X x))) integrable_on B /\
         (\x. lift(norm(X x - Y x) * norm(Y x))) integrable_on B /\
         abs(drop(integral A (\x. lift(X x dot (G(p x) ** X x)))) -
             drop(integral A (\x. lift(Y x dot (G(q x) ** Y x)))))
         <= Lam1 * (drop(integral B (\x. lift(norm(X x - Y x) * norm(X x)))) +
                    drop(integral B (\x. lift(norm(X x - Y x) * norm(Y x))))) +
            C3 * drop(integral B (\x. lift(norm(p x - q x) * norm(Y x) pow 2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x. (X:real^2->real^K) x - Y x) IN lspace B (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(norm((p:real^2->real^K) x - q x) * norm((Y:real^2->real^K) x) pow 2))
      integrable_on B`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
    EXISTS_TAC `\x. lift(M * norm((Y:real^2->real^K) x) pow 2)` THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`\x. lift(norm((p:real^2->real^K) x - q x))`;
                     `\x. lift(norm((Y:real^2->real^K) x) pow 2)`; `B:real^2->bool`]
                    MEASURABLE_ON_DROP_MUL) THEN
      REWRITE_TAC[LIFT_DROP; GSYM LIFT_CMUL] THEN DISCH_THEN MATCH_MP_TAC THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MEASURABLE_ON_NORM THEN MATCH_MP_TAC MEASURABLE_ON_SUB THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC INTEGRABLE_IMP_MEASURABLE THEN
        ASM_SIMP_TAC[WAN_LSPACE2_SQNORM_INTEGRABLE]];
      REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
      ASM_SIMP_TAC[WAN_LSPACE2_SQNORM_INTEGRABLE];
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      REWRITE_TAC[NORM_LIFT; LIFT_DROP; REAL_ABS_MUL; REAL_ABS_NORM; REAL_ABS_POW] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(norm((X:real^2->real^K) x - Y x) * norm(X x))) integrable_on B /\
    (\x. lift(norm((X:real^2->real^K) x - Y x) * norm(Y x))) integrable_on B`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LSPACE_INTEGRABLE_PRODUCT THEN
    MAP_EVERY EXISTS_TAC [`&2`; `&2`] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `beta = \x. lift(Lam1 * (norm((X:real^2->real^K) x - Y x) * norm(X x) +
                            norm(X x - Y x) * norm(Y x)) +
                    C3 * (norm((p:real^2->real^K) x - q x) * norm(Y x) pow 2))` THEN
  SUBGOAL_THEN `(beta:real^2->real^1) integrable_on B` ASSUME_TAC THENL
   [EXPAND_TAC "beta" THEN
    REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN
    REPEAT((MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC) ORELSE MATCH_MP_TAC INTEGRABLE_CMUL) THEN
    ASM_REWRITE_TAC[GSYM LIFT_CMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN B ==> &0 <= drop((beta:real^2->real^1) x)` ASSUME_TAC THENL
   [EXPAND_TAC "beta" THEN REWRITE_TAC[LIFT_DROP] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LE_ADD; REAL_LE_MUL; NORM_POS_LE; REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `(beta:real^2->real^1) integrable_on A` ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `B:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_EQ_INTEGRABLE_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift((X:real^2->real^K) x dot ((G:real^K->real^K^K)((p:real^2->real^K) x) ** X x)))
      integrable_on A /\
    (\x. lift((Y:real^2->real^K) x dot ((G:real^K->real^K^K)((q:real^2->real^K) x) ** Y x)))
      integrable_on A`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC CMR_GQUAD_INTEGRABLE THEN EXISTS_TAC `Lam:real` THEN
    ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
       EXISTS_TAC `B:real^2->bool` THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `B:real^2->bool` THEN
       ASM_REWRITE_TAC[]]);
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `drop(integral B (beta:real^2->real^1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `drop(integral A (beta:real^2->real^1))` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[GSYM DROP_SUB; GSYM INTEGRAL_SUB] THEN REWRITE_TAC[GSYM NORM_1] THEN
      MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
      ASM_SIMP_TAC[INTEGRABLE_SUB] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(x:real^2) IN B` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "beta" THEN REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT; LIFT_DROP] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `Lam1 * norm((X:real^2->real^K) x - Y x) * (norm(X x) + norm(Y x)) +
                  C3 * norm((p:real^2->real^K) x - q x) * norm(Y x) pow 2` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CMR_DENS_DIFF THEN EXISTS_TAC `S:real^K->bool` THEN ASM_SIMP_TAC[];
        REAL_ARITH_TAC];
      MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN ASM_REWRITE_TAC[]];
    EXPAND_TAC "beta" THEN REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN
    ASM_SIMP_TAC[INTEGRAL_ADD; INTEGRAL_CMUL; INTEGRABLE_ADD; INTEGRABLE_CMUL;
                 GSYM LIFT_CMUL; DROP_ADD; DROP_CMUL] THEN
    REAL_ARITH_TAC]);;

let CMR_LGD_ARITH = prove
 (`!a1 a2 b1 b2 P1u P2u P1v P2v R1 R2 Lam1 C3 CW sf su sv sg.
     &0 <= Lam1 /\ &0 <= C3 /\ &0 <= CW /\ &0 <= sf /\ &0 <= su /\ &0 <= sv /\ &0 <= sg
     ==> abs(a1 - b1) <= Lam1 * (P1u + P1v) + C3 * R1
     ==> abs(a2 - b2) <= Lam1 * (P2u + P2v) + C3 * R2
     ==> P1u + P2u <= sf * su
     ==> P1v + P2v <= sf * sv
     ==> R1 + R2 <= CW * sg * sf * sv
     ==> abs((a1 + a2) - (b1 + b2)) <= (Lam1 + C3 * CW + &1) * sf * (su + sv + sg * sv)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `Lam1 * (P1u + P2u) <= Lam1 * (sf * su) /\
                Lam1 * (P1v + P2v) <= Lam1 * (sf * sv) /\
                C3 * (R1 + R2) <= C3 * (CW * sg * sf * sv)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Lam1 * sf * sg * sv /\ &0 <= C3 * CW * sf * su /\
                &0 <= C3 * CW * sf * sv /\ &0 <= sf * su /\ &0 <= sf * sv /\
                &0 <= sf * sg * sv` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The difference of G-energies on an open subset of the disc.              *)

let CMR_LOCAL_GDIR_DIFF = prove
 (`!S (G:real^K->real^K^K) d e0 (C:num->real).
     cm_target S G d /\
     (!(a:real^2) r (u:real^2->real^K) l x.
        &0 < r /\ cm_harmonic S G (ball(a,r)) u /\ wan_w12 (ball(a,r)) u /\
        wan_gdir (ball(a,r)) G u <= e0 /\
        ALL (\i. 1 <= i /\ i <= 2) l /\ ~(l = []) /\ x IN ball(a,r / &2)
        ==> r pow (LENGTH l) * norm(iterated_partial l u x)
            <= C (LENGTH l) * sqrt(wan_gdir (ball(a,r)) G u)) /\
     (!k. &0 < C k)
     ==> ?K1. &0 < K1 /\
           !(a:real^2) r (u:real^2->real^K) v A.
             &0 < r /\ cm_harmonic S G (ball(a,r)) v /\ wan_w12 (ball(a,r)) v /\
             wan_gdir (ball(a,r)) G v <= e0 /\ wan_w12 (ball(a,r)) u /\
             u continuous_on ball(a,r) /\ (!x. x IN ball(a,r) ==> u x IN S) /\
             wan_w120 (ball(a,r)) (\x. u x - v x) /\ open A /\ A SUBSET ball(a,r)
             ==> abs(wan_gdir A G u - wan_gdir A G v)
                 <= K1 * sqrt(wan_dir (ball(a,r)) (\x. u x - v x)) *
                    (sqrt(wan_dir (ball(a,r)) u) + sqrt(wan_dir (ball(a,r)) v) +
                     sqrt(wan_gdir (ball(a,r)) G v) * sqrt(wan_dir (ball(a,r)) v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_CONSTS) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC o MATCH_MP HMC_G_BOUNDS) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CMW_TARGET_FACTS) THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z. transp((G:real^K->real^K^K) z) = G z` ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_target]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e0:real`; `C:num->real`; `Lam:real`]
                CMR_WEIGHT_TERM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `CW:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?M. !p q. p IN S /\ q IN S ==> norm(p - q:real^K) <= M` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED o
      check (fun th -> concl th = `compact (S:real^K->bool)`)) THEN
    REWRITE_TAC[bounded] THEN DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
    EXISTS_TAC `&2 * B` THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(NORM_ARITH `norm(p:real^K) <= B /\ norm(q:real^K) <= B ==> norm(p - q) <= &2 * B`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `Lam1 + C3 * CW + &1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ &0 <= y ==> &0 < x + y + &1`) THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `continuously_differentiable 1 (ball(a:real^2,r)) (v:real^2->real^K) /\
                (!x. x IN ball(a,r) ==> v x IN S)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `cm_harmonic S (G:real^K->real^K^K) (ball(a,r)) (v:real^2->real^K)` THEN
    SIMP_TAC[cm_harmonic; smooth_map_on];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 (ball(a:real^2,r)) (\x. (u:real^2->real^K) x - v x)` ASSUME_TAC THENL
   [ASM_MESON_TAC[wan_w120]; ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^2->real^K) measurable_on ball(a,r) /\
                (v:real^2->real^K) measurable_on ball(a,r)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[wan_w12; lspace; IN_ELIM_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(a:real^2,r)`; `A:real^2->bool`; `G:real^K->real^K^K`;
                 `u:real^2->real^K`] CMR_GDIR_RESTRICT) THEN
  MP_TAC(ISPECL [`ball(a:real^2,r)`; `A:real^2->bool`; `G:real^K->real^K^K`;
                 `v:real^2->real^K`] CMR_GDIR_RESTRICT) THEN
  ASM_REWRITE_TAC[OPEN_BALL; DIMINDEX_2; SUM_2] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> wan_wd (ball(a,r)) i (u:real^2->real^K) IN lspace (ball(a,r)) (&2) /\
            wan_wd (ball(a,r)) i (v:real^2->real^K) IN lspace (ball(a,r)) (&2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WAN_WD_WORKS; DIMINDEX_2]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `S:real^K->bool`; `Lam:real`; `Lam1:real`; `C3:real`;
                 `M:real`; `A:real^2->bool`; `ball(a:real^2,r)`;
                 `wan_wd (ball(a,r)) 1 (u:real^2->real^K)`;
                 `wan_wd (ball(a,r)) 1 (v:real^2->real^K)`;
                 `u:real^2->real^K`; `v:real^2->real^K`] CMR_QUAD_DIFF_BOUND) THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `S:real^K->bool`; `Lam:real`; `Lam1:real`; `C3:real`;
                 `M:real`; `A:real^2->bool`; `ball(a:real^2,r)`;
                 `wan_wd (ball(a,r)) 2 (u:real^2->real^K)`;
                 `wan_wd (ball(a,r)) 2 (v:real^2->real^K)`;
                 `u:real^2->real^K`; `v:real^2->real^K`] CMR_QUAD_DIFF_BOUND) THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; OPEN_BALL; ARITH] THEN
  DISCH_THEN(STRIP_ASSUME_TAC) THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`ball(a:real^2,r)`;
                 `\x. wan_wd (ball(a,r)) 1 (u:real^2->real^K) x - wan_wd (ball(a,r)) 1 (v:real^2->real^K) x`;
                 `\x. wan_wd (ball(a,r)) 2 (u:real^2->real^K) x - wan_wd (ball(a,r)) 2 (v:real^2->real^K) x`;
                 `wan_wd (ball(a,r)) 1 (u:real^2->real^K)`;
                 `wan_wd (ball(a,r)) 2 (u:real^2->real^K)`] CMR_HOELDER_SUM2) THEN
  MP_TAC(ISPECL [`ball(a:real^2,r)`;
                 `\x. wan_wd (ball(a,r)) 1 (u:real^2->real^K) x - wan_wd (ball(a,r)) 1 (v:real^2->real^K) x`;
                 `\x. wan_wd (ball(a,r)) 2 (u:real^2->real^K) x - wan_wd (ball(a,r)) 2 (v:real^2->real^K) x`;
                 `wan_wd (ball(a,r)) 1 (v:real^2->real^K)`;
                 `wan_wd (ball(a,r)) 2 (v:real^2->real^K)`] CMR_HOELDER_SUM2) THEN
  ASM_SIMP_TAC[LSPACE_SUB; REAL_POS; ARITH; ETA_AX] THEN
  DISCH_THEN(STRIP_ASSUME_TAC) THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `drop(integral (ball(a,r)) (\x. lift(norm(wan_wd (ball(a,r)) 1 (u:real^2->real^K) x -
                                              wan_wd (ball(a,r)) 1 (v:real^2->real^K) x) pow 2))) +
    drop(integral (ball(a,r)) (\x. lift(norm(wan_wd (ball(a,r)) 2 u x -
                                              wan_wd (ball(a,r)) 2 v x) pow 2))) =
    wan_dir (ball(a:real^2,r)) (\x. u x - v x) /\
    drop(integral (ball(a,r)) (\x. lift(norm(wan_wd (ball(a,r)) 1 (u:real^2->real^K) x) pow 2))) +
    drop(integral (ball(a,r)) (\x. lift(norm(wan_wd (ball(a,r)) 2 u x) pow 2))) =
    wan_dir (ball(a:real^2,r)) u /\
    drop(integral (ball(a,r)) (\x. lift(norm(wan_wd (ball(a,r)) 1 (v:real^2->real^K) x) pow 2))) +
    drop(integral (ball(a,r)) (\x. lift(norm(wan_wd (ball(a,r)) 2 v x) pow 2))) =
    wan_dir (ball(a:real^2,r)) v`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN REWRITE_TAC[wan_dir; DIMINDEX_2; SUM_2] THEN
    MP_TAC(ISPECL [`ball(a:real^2,r)`; `\x. (u:real^2->real^K) x - v x`;
                   `\i x. wan_wd (ball(a,r)) i (u:real^2->real^K) x -
                          wan_wd (ball(a,r)) i (v:real^2->real^K) x`] WAN_DIR_EQ) THEN
    MP_TAC(ISPECL [`ball(a:real^2,r)`; `u:real^2->real^K`; `v:real^2->real^K`]
                  WAN_W12_SUB_WD) THEN
    ASM_SIMP_TAC[OPEN_BALL; DIMINDEX_2; SUM_2; wan_dir];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^2`; `r:real`; `u:real^2->real^K`; `v:real^2->real^K`;
                                `M:real`] o
    check (fun th -> is_forall(concl th) &&
                     can (find_term (fun t -> t = `CW:real`)) (concl th))) THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[SUM_2] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> drop(integral (ball(a,r))
              (\x. lift(norm((u:real^2->real^K) x - v x) *
                        norm(wan_wd (ball(a,r)) i (v:real^2->real^K) x) pow 2))) =
            drop(integral (ball(a,r))
              (\x. lift(norm(u x - v x) * norm(partial_derivative i v x) pow 2)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE THEN
    EXISTS_TAC `{x | x IN ball(a,r) /\
                     ~(wan_wd (ball(a,r)) i (v:real^2->real^K) x = partial_derivative i v x)}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HMC_WD_CLASSICAL THEN ASM_REWRITE_TAC[OPEN_BALL; DIMINDEX_2];
      REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(SIMP_RULE[ARITH; LE_REFL]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
   `drop(integral (ball(a,r)) (\x. lift(norm(wan_wd (ball(a,r)) 1 (u:real^2->real^K) x -
                                              wan_wd (ball(a,r)) 1 (v:real^2->real^K) x) pow 2))) +
    drop(integral (ball(a,r)) (\x. lift(norm(wan_wd (ball(a,r)) 2 u x -
                                              wan_wd (ball(a,r)) 2 v x) pow 2))) =
    wan_dir (ball(a:real^2,r)) (\x. u x - v x)`;
   ASSUME
   `drop(integral (ball(a,r)) (\x. lift(norm(wan_wd (ball(a,r)) 1 (u:real^2->real^K) x) pow 2))) +
    drop(integral (ball(a,r)) (\x. lift(norm(wan_wd (ball(a,r)) 2 u x) pow 2))) =
    wan_dir (ball(a:real^2,r)) u`;
   ASSUME
   `drop(integral (ball(a,r)) (\x. lift(norm(wan_wd (ball(a,r)) 1 (v:real^2->real^K) x) pow 2))) +
    drop(integral (ball(a,r)) (\x. lift(norm(wan_wd (ball(a,r)) 2 v x) pow 2))) =
    wan_dir (ball(a:real^2,r)) v`]) THEN
  SUBGOAL_THEN
   `&0 <= wan_dir (ball(a:real^2,r)) (\x. (u:real^2->real^K) x - v x) /\
    &0 <= wan_dir (ball(a:real^2,r)) (u:real^2->real^K) /\
    &0 <= wan_dir (ball(a:real^2,r)) (v:real^2->real^K) /\
    &0 <= wan_gdir (ball(a:real^2,r)) G (v:real^2->real^K)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_DIR_POS] THEN MATCH_MP_TAC HMC_GDIR_POS THEN
    EXISTS_TAC `Lam:real` THEN ASM_REWRITE_TAC[OPEN_BALL] THEN
    ASM_MESON_TAC[cm_harmonic];
    ALL_TAC] THEN
  ABBREV_TAC `sf = sqrt(wan_dir (ball(a:real^2,r)) (\x. (u:real^2->real^K) x - v x))` THEN
  ABBREV_TAC `su = sqrt(wan_dir (ball(a:real^2,r)) (u:real^2->real^K))` THEN
  ABBREV_TAC `sv = sqrt(wan_dir (ball(a:real^2,r)) (v:real^2->real^K))` THEN
  ABBREV_TAC `sg = sqrt(wan_gdir (ball(a:real^2,r)) G (v:real^2->real^K))` THEN
  SUBGOAL_THEN `&0 <= sf /\ &0 <= su /\ &0 <= sv /\ &0 <= sg` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["sf"; "su"; "sv"; "sg"] THEN ASM_SIMP_TAC[SQRT_POS_LE];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
   `sqrt(wan_dir (ball(a:real^2,r)) (\x. (u:real^2->real^K) x - v x)) = sf`;
   ASSUME `sqrt(wan_dir (ball(a:real^2,r)) (u:real^2->real^K)) = su`;
   ASSUME `sqrt(wan_dir (ball(a:real^2,r)) (v:real^2->real^K)) = sv`;
   ASSUME `sqrt(wan_gdir (ball(a:real^2,r)) G (v:real^2->real^K)) = sg`]) THEN
  FIRST_ASSUM(MP_TAC o SPEC `1` o
    check (fun th -> is_forall(concl th) &&
                     can (find_term (fun t -> is_const t && fst(dest_const t) = "partial_derivative"))
                         (concl th) &&
                     can (find_term (fun t -> is_const t && fst(dest_const t) = "wan_wd"))
                         (concl th))) THEN
  FIRST_ASSUM(MP_TAC o SPEC `2` o
    check (fun th -> is_forall(concl th) &&
                     can (find_term (fun t -> is_const t && fst(dest_const t) = "partial_derivative"))
                         (concl th) &&
                     can (find_term (fun t -> is_const t && fst(dest_const t) = "wan_wd"))
                         (concl th))) THEN
  REWRITE_TAC[ARITH] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o
    check (fun th -> can (find_term (fun t -> t = `CW:real`)) (concl th) &&
                     not (is_forall(concl th)) &&
                     can (find_term (fun t -> is_const t && fst(dest_const t) = "partial_derivative"))
                         (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> t = `CW:real`)) (concl th) &&
                                          not (is_forall(concl th)))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> t = `sf * sv`)) (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> t = `sf * su`)) (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_binary "real_le" (concl th) &&
                                          can (find_term (fun t -> t = `C3:real`)) (concl th) &&
                                          can (find_term (fun t -> t = `wan_wd (ball(a:real^2,r)) 2 (u:real^2->real^K)`)) (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_binary "real_le" (concl th) &&
                                          can (find_term (fun t -> t = `C3:real`)) (concl th) &&
                                          can (find_term (fun t -> t = `wan_wd (ball(a:real^2,r)) 1 (u:real^2->real^K)`)) (concl th))) THEN
  MATCH_MP_TAC CMR_LGD_ARITH THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;


(* ========================================================================= *)
(* Energies on S^2 only see the map where they are taken, cap                *)
(* boundary circles carry no energy, and the global stability of energies  *)
(* on open sets under replacement on disjoint small caps.                   *)
(* ========================================================================= *)

let CMR_WD_RESTRICT = prove
 (`!s t (u:real^N->real^K) i.
     open s /\ open t /\ t SUBSET s /\ wan_w12 s u /\ 1 <= i /\ i <= dimindex(:N)
     ==> negligible {x | x IN t /\ ~(wan_wd t i u x = wan_wd s i u x)}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `i:num`; `u:real^N->real^K`] WAN_WD_WORKS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_wd s i (u:real^N->real^K) IN lspace t (&2) /\
                wan_wpd t i u (wan_wd s i u)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN];
      MATCH_MP_TAC WAN_WPD_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `i:num`; `u:real^N->real^K`;
                 `wan_wd s i (u:real^N->real^K)`] CMR_WD_WORKS_P) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC WAN_WPD_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`i:num`; `u:real^N->real^K`] THEN ASM_REWRITE_TAC[ETA_AX]);;

let CMR_WD_LOCAL_EQ = prove
 (`!s t (u:real^N->real^K) v i.
     open s /\ open t /\ t SUBSET s /\ wan_w12 s u /\ wan_w12 s v /\
     (!x. x IN t ==> u x = v x) /\ 1 <= i /\ i <= dimindex(:N)
     ==> negligible {x | x IN t /\ ~(wan_wd s i u x = wan_wd s i v x)}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `{x | x IN t /\ ~(wan_wd t i (u:real^N->real^K) x = wan_wd s i u x)} UNION
              {x | x IN t /\ ~(wan_wd t i (v:real^N->real^K) x = wan_wd s i v x)}` THEN
  ASM_SIMP_TAC[NEGLIGIBLE_UNION; CMR_WD_RESTRICT] THEN
  SUBGOAL_THEN `wan_wd t i (u:real^N->real^K) = wan_wd t i v` ASSUME_TAC THENL
   [MATCH_MP_TAC CMT_WAN_WD_EQ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN MESON_TAC[]);;

let CMR_SEN_ON_EQ_OPEN = prove
 (`!(G:real^K->real^K^K) (u:real^3->real^K) v W E.
     wan_s2_w12 u /\ wan_s2_w12 v /\ open(cmr_cone W) /\
     (!y. y IN W ==> u y = v y) /\ E SUBSET W
     ==> cmr_sen_on G u E = cmr_sen_on G v E`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_s2_w12] THEN STRIP_TAC THEN
  REWRITE_TAC[cmr_sen_on] THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `cmr_cone W SUBSET wan_shell /\ cmr_cone E SUBSET cmr_cone W`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[cmr_cone; SUBSET; IN_ELIM_THM] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN cmr_cone W ==> wan_rext (u:real^3->real^K) z = wan_rext v z`
  ASSUME_TAC THENL
   [REWRITE_TAC[cmr_cone; IN_ELIM_THM; wan_rext] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC INTEGRAL_SPIKE THEN
  EXISTS_TAC
   `{z | z IN cmr_cone W /\ ~(wan_wd wan_shell 1 (wan_rext (u:real^3->real^K)) z =
                               wan_wd wan_shell 1 (wan_rext v) z)} UNION
    {z | z IN cmr_cone W /\ ~(wan_wd wan_shell 2 (wan_rext (u:real^3->real^K)) z =
                               wan_wd wan_shell 2 (wan_rext v) z)} UNION
    {z | z IN cmr_cone W /\ ~(wan_wd wan_shell 3 (wan_rext (u:real^3->real^K)) z =
                               wan_wd wan_shell 3 (wan_rext v) z)}` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC CMR_WD_LOCAL_EQ THEN
    ASM_REWRITE_TAC[DIMINDEX_3; ARITH; CMT_SHELL_OPEN];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_DIFF; IN_UNION; IN_ELIM_THM] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^3) IN cmr_cone W` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_wd wan_shell 1 (wan_rext (u:real^3->real^K)) z = wan_wd wan_shell 1 (wan_rext v) z /\
    wan_wd wan_shell 2 (wan_rext (u:real^3->real^K)) z = wan_wd wan_shell 2 (wan_rext v) z /\
    wan_wd wan_shell 3 (wan_rext (u:real^3->real^K)) z = wan_wd wan_shell 3 (wan_rext v) z`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[cmr_dens; SUM_3] THEN ASM_SIMP_TAC[]);;

(* The cone over the image of a planar circle under a cap chart is          *)
(* negligible (a differentiable image of the plane in R^3).                 *)

let CMR_CIRCLE_CONE_NEGLIGIBLE = prove
 (`!(Q:real^3^3) (c:real^2) r.
     negligible(cmr_cone (IMAGE (cm_capmap Q) (sphere(c,r))))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `IMAGE (\x:real^2. drop(lift(x$2)) %
                       cm_capmap Q (c + r % vector[cos(x$1); sin(x$1)])) (:real^2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_DIFFERENTIABLE_IMAGE_LOWDIM THEN
    REWRITE_TAC[DIMINDEX_2; DIMINDEX_3; ARITH] THEN
    MATCH_MP_TAC DIFFERENTIABLE_AT_IMP_DIFFERENTIABLE_ON THEN
    X_GEN_TAC `x0:real^2` THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN
    SIMP_TAC[OPEN_UNIV; SMOOTH_MAP_ON_LIFT_COORDINATE] THEN
    SUBGOAL_THEN
     `(\x:real^2. cm_capmap Q (c + r % vector[cos(x$1); sin(x$1)])) =
      cm_capmap Q o (\x:real^2. c + r % (lambda k. drop((\k x. if k = 1
                                                              then lift(cos(drop(lift(x$1))))
                                                              else lift(sin(drop(lift(x$1))))) k x)))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `x:real^2` THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      SIMP_TAC[CART_EQ; LAMBDA_BETA; DIMINDEX_2; FORALL_2; VECTOR_2; LIFT_DROP; ARITH];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; CMR_CAPMAP_SMOOTH] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN REWRITE_TAC[OPEN_UNIV] THEN CONJ_TAC THENL
     [SIMP_TAC[SMOOTH_MAP_ON_OPEN_UNIV; CONTINUOUSLY_DIFFERENTIABLE_CONST; OPEN_UNIV];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN REWRITE_TAC[OPEN_UNIV] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LAMBDA THEN REWRITE_TAC[OPEN_UNIV; DIMINDEX_2] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN ASM_CASES_TAC `k = 1` THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COS; MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_SIN] THEN
    SIMP_TAC[OPEN_UNIV; SMOOTH_MAP_ON_LIFT_COORDINATE];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; cmr_cone; IN_ELIM_THM; IN_IMAGE; IN_UNIV] THEN
  X_GEN_TAC `z:real^3` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`c:real^2`; `r:real`; `y:real^2`] WAN_SPHERE_CIRC) THEN
  ASM_REWRITE_TAC[wan_circ] THEN DISCH_THEN(X_CHOOSE_TAC `t:real`) THEN
  EXISTS_TAC `vector[t; norm(z:real^3)]:real^2` THEN
  REWRITE_TAC[VECTOR_2; LIFT_DROP] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o
    check (fun th -> concl th = `inv(norm(z:real^3)) % z = cm_capmap Q y`)) THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  SUBGOAL_THEN `~(norm(z:real^3) = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_EQ_0] THEN ASM_MESON_TAC[CMT_SHELL_NONZERO]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; VECTOR_MUL_LID]);;

let CMR_CONE_OPEN = prove
 (`!W. open_in (subtopology euclidean (sphere(vec 0:real^3,&1))) W ==> open(cmr_cone W)`,
  GEN_TAC THEN REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `cmr_cone W = {z:real^3 | z IN wan_shell /\ (\z. inv(norm z) % z) z IN t0}`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[cmr_cone; EXTENSION; IN_ELIM_THM; IN_INTER] THEN
    X_GEN_TAC `z:real^3` THEN ASM_CASES_TAC `(z:real^3) IN wan_shell` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    SUBGOAL_THEN `~(norm(z:real^3) = &0)` (fun th -> SIMP_TAC[th; REAL_MUL_LINV]) THEN
    REWRITE_TAC[NORM_EQ_0] THEN ASM_MESON_TAC[CMT_SHELL_NONZERO];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[CMT_SHELL_OPEN] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN
  SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SMOOTH_MAP_ON_NORMALIZE] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[CMT_SHELL_NONZERO]);;

let CMR_CHART_PREIMAGE_OPEN = prove
 (`!(Q:real^3^3) (c:real^2) r W.
     orthogonal_matrix Q /\ open_in (subtopology euclidean (sphere(vec 0:real^3,&1))) W
     ==> open {x | x IN ball(c,r) /\ cm_capmap Q x IN W} /\
         IMAGE (cm_capmap Q) {x | x IN ball(c,r) /\ cm_capmap Q x IN W} =
         W INTER IMAGE (cm_capmap Q) (ball(c,r))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t0:real^3->bool` STRIP_ASSUME_TAC)) THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `{x | x IN ball(c:real^2,r) /\ cm_capmap Q x IN W} =
                  {x | x IN ball(c,r) /\ cm_capmap Q x IN t0}` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN
      MP_TAC(SPEC `Q:real^3^3` CMR_CAPMAP_FACTS) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[OPEN_BALL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; CMR_CAPMAP_SMOOTH; SUBSET_UNIV; ETA_AX];
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN MESON_TAC[]]);;

(* Decomposition of an open subset of S^2 by a cap: the part in the open    *)
(* cap, the part off the closed cap, and the boundary circle.               *)

let CMR_CAP_SPLIT_SETS = prove
 (`!(Q:real^3^3) (c:real^2) r W.
     orthogonal_matrix Q /\ open_in (subtopology euclidean (sphere(vec 0:real^3,&1))) W
     ==> W = ((W INTER IMAGE (cm_capmap Q) (ball(c,r))) UNION
              (W INTER (sphere(vec 0,&1) DIFF IMAGE (cm_capmap Q) (cball(c,r))))) UNION
             (W INTER IMAGE (cm_capmap Q) (sphere(c,r))) /\
         DISJOINT (W INTER IMAGE (cm_capmap Q) (ball(c,r)))
                  (W INTER (sphere(vec 0,&1) DIFF IMAGE (cm_capmap Q) (cball(c,r)))) /\
         DISJOINT ((W INTER IMAGE (cm_capmap Q) (ball(c,r))) UNION
                   (W INTER (sphere(vec 0,&1) DIFF IMAGE (cm_capmap Q) (cball(c,r)))))
                  (W INTER IMAGE (cm_capmap Q) (sphere(c,r))) /\
         open_in (subtopology euclidean (sphere(vec 0,&1)))
                 (W INTER IMAGE (cm_capmap Q) (ball(c,r))) /\
         open_in (subtopology euclidean (sphere(vec 0,&1)))
                 (W INTER (sphere(vec 0,&1) DIFF IMAGE (cm_capmap Q) (cball(c,r)))) /\
         open_in (subtopology euclidean (sphere(vec 0,&1)))
                 (sphere(vec 0,&1) DIFF IMAGE (cm_capmap Q) (cball(c,r)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
  MP_TAC(SPEC `Q:real^3^3` CMR_CAPMAP_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean (sphere(vec 0:real^3,&1)))
      (sphere(vec 0,&1) DIFF IMAGE (cm_capmap Q) (cball(c:real^2,r)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_DIFF_CLOSED THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN REWRITE_TAC[COMPACT_CBALL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; CMR_CAPMAP_SMOOTH; SUBSET_UNIV];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM BALL_UNION_SPHERE; IMAGE_UNION] THEN
    SUBGOAL_THEN `!y. y IN W ==> y IN sphere(vec 0:real^3,&1)` MP_TAC THENL
     [ASM SET_TAC[]; SET_TAC[]];
    REWRITE_TAC[GSYM BALL_UNION_SPHERE; IMAGE_UNION] THEN SET_TAC[];
    REWRITE_TAC[GSYM BALL_UNION_SPHERE; IMAGE_UNION] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_UNION; IN_DIFF; IN_IMAGE; NOT_IN_EMPTY] THEN
    X_GEN_TAC `y:real^3` THEN
    SUBGOAL_THEN `!x x':real^2. cm_capmap Q x = cm_capmap Q x' ==> x = x'` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`c:real^2`; `r:real`] BALL_SUBSET_CBALL) THEN
    REWRITE_TAC[SUBSET; IN_BALL; IN_SPHERE; IN_CBALL] THEN
    MESON_TAC[REAL_LT_REFL];
    MATCH_MP_TAC OPEN_IN_INTER THEN ASM_SIMP_TAC[CMR_CAP_OPEN_IN; OPEN_BALL];
    MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[]]);;

(* Energy additivity over the cap split.                                    *)

let CMR_SEN_ON_CAP_SPLIT = prove
 (`!(G:real^K->real^K^K) Lam (Q:real^3^3) (c:real^2) r (f:real^3->real^K) W.
     CMR_GCOND G Lam /\ wan_s2_w12 f /\ orthogonal_matrix Q /\
     open_in (subtopology euclidean (sphere(vec 0:real^3,&1))) W
     ==> cmr_sen_on G f W =
         cmr_sen_on G f (W INTER IMAGE (cm_capmap Q) (ball(c,r))) +
         cmr_sen_on G f (W INTER (sphere(vec 0,&1) DIFF IMAGE (cm_capmap Q) (cball(c,r))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Q:real^3^3`; `c:real^2`; `r:real`; `W:real^3->bool`] CMR_CAP_SPLIT_SETS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
  SUBGOAL_THEN
   `negligible(cmr_cone (W INTER IMAGE (cm_capmap Q) (sphere(c:real^2,r))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `cmr_cone (IMAGE (cm_capmap Q) (sphere(c:real^2,r)))` THEN
    REWRITE_TAC[CMR_CIRCLE_CONE_NEGLIGIBLE] THEN
    REWRITE_TAC[cmr_cone; SUBSET; IN_ELIM_THM; IN_INTER] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `f:real^3->real^K`; `Lam:real`;
                 `(W INTER IMAGE (cm_capmap Q) (ball(c:real^2,r))) UNION
                  (W INTER (sphere(vec 0,&1) DIFF IMAGE (cm_capmap Q) (cball(c,r))))`;
                 `W INTER IMAGE (cm_capmap Q) (sphere(c:real^2,r))`] CMR_SEN_ON_UNION) THEN
  ASM_SIMP_TAC[NEGLIGIBLE_IMP_LEBESGUE_MEASURABLE; CMR_CONE_UNION] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC LEBESGUE_MEASURABLE_UNION THEN CONJ_TAC THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_OPEN THEN MATCH_MP_TAC CMR_CONE_OPEN THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `f:real^3->real^K`; `Lam:real`;
                 `W INTER IMAGE (cm_capmap Q) (ball(c:real^2,r))`;
                 `W INTER (sphere(vec 0,&1) DIFF IMAGE (cm_capmap Q) (cball(c:real^2,r)))`]
                CMR_SEN_ON_UNION) THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; CMR_CONE_OPEN] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `cmr_sen_on (G:real^K->real^K^K) (f:real^3->real^K)
      (W INTER IMAGE (cm_capmap Q) (sphere(c:real^2,r))) = &0`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[cmr_sen_on; INTEGRAL_ON_NEGLIGIBLE; DROP_VEC] THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* One-cap stability of energies on open subsets of S^2.                    *)

let CMR_REP1_STAB = prove
 (`!S (G:real^K->real^K^K) d e0 (C:num->real) e.
     cm_target S G d /\
     (!(a:real^2) r (u:real^2->real^K) l x.
        &0 < r /\ cm_harmonic S G (ball(a,r)) u /\ wan_w12 (ball(a,r)) u /\
        wan_gdir (ball(a,r)) G u <= e0 /\
        ALL (\i. 1 <= i /\ i <= 2) l /\ ~(l = []) /\ x IN ball(a,r / &2)
        ==> r pow (LENGTH l) * norm(iterated_partial l u x)
            <= C (LENGTH l) * sqrt(wan_gdir (ball(a,r)) G u)) /\
     (!k. &0 < C k) /\ cmw_repex S G e /\ e <= e0
     ==> ?K2. &0 < K2 /\
           !(Q:real^3^3) (c:real^2) r (v:real^3->real^K) W.
             cm_smap S v /\ orthogonal_matrix Q /\ &0 < r /\
             wan_gdir (ball(c,r)) G (\x. v(cm_capmap Q x)) <= e /\
             open_in (subtopology euclidean (sphere(vec 0,&1))) W
             ==> abs(cmr_sen_on G (cmr_rep1 S G Q c r v) W - cmr_sen_on G v W)
                 <= K2 * sqrt(wan_dir (ball(c,r))
                                (\x. v(cm_capmap Q x) -
                                     cmr_minw S G c r (\x. v(cm_capmap Q x)) x)) *
                    (sqrt(wan_dir (ball(c,r)) (\x. v(cm_capmap Q x))) +
                     sqrt(wan_dir (ball(c,r)) (cmr_minw S G c r (\x. v(cm_capmap Q x)))) +
                     sqrt(wan_gdir (ball(c,r)) G (cmr_minw S G c r (\x. v(cm_capmap Q x)))) *
                     sqrt(wan_dir (ball(c,r)) (cmr_minw S G c r (\x. v(cm_capmap Q x)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC o MATCH_MP CMR_TARGET_GCOND) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e0:real`; `C:num->real`]
                CMR_LOCAL_GDIR_DIFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `K1:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `K1:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `V = \x. (v:real^3->real^K)(cm_capmap Q x)` THEN
  ABBREV_TAC `M = cmr_minw S (G:real^K->real^K^K) (c:real^2) r (V:real^2->real^K)` THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Q:real^3^3`; `c:real^2`;
                 `r:real`; `v:real^3->real^K`] CMR_REP1_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `c:real^2`; `r:real`;
                 `V:real^2->real^K`] CMR_MINW_WORKS) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [EXPAND_TAC "V" THEN ASM_SIMP_TAC[CMR_CHART_CMAP]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `Lam:real`; `Q:real^3^3`; `c:real^2`; `r:real`;
                 `cmr_rep1 S (G:real^K->real^K^K) Q (c:real^2) r (v:real^3->real^K)`;
                 `W:real^3->bool`] CMR_SEN_ON_CAP_SPLIT) THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `Lam:real`; `Q:real^3^3`; `c:real^2`; `r:real`;
                 `v:real^3->real^K`; `W:real^3->bool`] CMR_SEN_ON_CAP_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[cm_smap]; DISCH_THEN SUBST1_TAC] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[cm_smap]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`Q:real^3^3`; `c:real^2`; `r:real`; `W:real^3->bool`] CMR_CAP_SPLIT_SETS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `cmr_sen_on (G:real^K->real^K^K) (cmr_rep1 S G Q (c:real^2) r (v:real^3->real^K))
      (W INTER (sphere(vec 0,&1) DIFF IMAGE (cm_capmap Q) (cball(c,r)))) =
    cmr_sen_on G v (W INTER (sphere(vec 0,&1) DIFF IMAGE (cm_capmap Q) (cball(c,r))))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CMR_SEN_ON_EQ_OPEN THEN
    EXISTS_TAC `sphere(vec 0:real^3,&1) DIFF IMAGE (cm_capmap Q) (cball(c:real^2,r))` THEN
    ASM_SIMP_TAC[CMR_CONE_OPEN] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[cm_smap];
      ASM_MESON_TAC[cm_smap];
      X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `~((y:real^3) IN IMAGE (cm_capmap Q) (cball(c:real^2,r)))` THEN
      MP_TAC(ISPECL [`c:real^2`; `r:real`] BALL_SUBSET_CBALL) THEN SET_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Q:real^3^3`; `c:real^2`; `r:real`; `W:real^3->bool`]
                CMR_CHART_PREIMAGE_OPEN) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `A = {x | x IN ball(c:real^2,r) /\ cm_capmap Q x IN W}` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `v:real^3->real^K`; `Q:real^3^3`; `Lam:real`;
                 `A:real^2->bool`] CMR_CAP_EN) THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`;
                 `cmr_rep1 S (G:real^K->real^K^K) Q (c:real^2) r (v:real^3->real^K)`;
                 `Q:real^3^3`; `Lam:real`; `A:real^2->bool`] CMR_CAP_EN) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[cm_smap]; DISCH_THEN SUBST1_TAC] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[cm_smap]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `(A:real^2->bool) SUBSET ball(c,r)` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_gdir A G (\x. cmr_rep1 S (G:real^K->real^K^K) Q (c:real^2) r (v:real^3->real^K)
                        (cm_capmap Q x)) =
    wan_gdir A G (M:real^2->real^K) /\
    wan_gdir A G (\x. (v:real^3->real^K)(cm_capmap Q x)) = wan_gdir A G (V:real^2->real^K)`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CMT_WAN_GDIR_EQ THEN EXPAND_TAC "M" THEN EXPAND_TAC "V" THEN
      ASM_MESON_TAC[SUBSET];
      EXPAND_TAC "V" THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(a + b) - (c + b) = a - c`] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`c:real^2`; `r:real`; `V:real^2->real^K`; `M:real^2->real^K`;
                                `A:real^2->bool`] o
    check (fun th -> is_forall(concl th) &&
                     can (find_term (fun t -> t = `K1:real`)) (concl th))) THEN
  SUBGOAL_THEN `cm_cmap S (ball(c:real^2,r)) (V:real^2->real^K)` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN ASM_SIMP_TAC[CMR_CHART_CMAP]; ALL_TAC] THEN
  SUBGOAL_THEN `wan_w120 (ball(c:real^2,r)) (\x. (V:real^2->real^K) x - M x)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(\x. (V:real^2->real^K) x - M x) = (\x. --((\x. M x - V x) x))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC WAN_W120_NEG THEN ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_gdir (ball(c:real^2,r)) G (M:real^2->real^K) <=
                wan_gdir (ball(c,r)) G (V:real^2->real^K)` ASSUME_TAC THENL
   [UNDISCH_TAC `cm_minimizer S (G:real^K->real^K^K) (ball(c,r)) (M:real^2->real^K)` THEN
    REWRITE_TAC[cm_minimizer; cm_gen] THEN
    DISCH_THEN(MP_TAC o SPEC `V:real^2->real^K` o CONJUNCT2) THEN
    ASM_SIMP_TAC[CMR_CMAP_WMAP] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. (v:real^3->real^K)(cm_capmap Q x) - M x) = (\x. (V:real^2->real^K) x - M x)`
  SUBST1_TAC THENL [EXPAND_TAC "V" THEN REWRITE_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[cm_cmap];
      ASM_REAL_ARITH_TAC;
      ASM_MESON_TAC[cm_cmap];
      UNDISCH_TAC `cm_cmap S (ball(c:real^2,r)) (V:real^2->real^K)` THEN
      ASM_SIMP_TAC[cm_cmap; CLOSURE_BALL] THEN STRIP_TAC THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(c:real^2,r)` THEN
      ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN EXPAND_TAC "V" THEN REWRITE_TAC[] THEN
      UNDISCH_TAC `cm_smap S (v:real^3->real^K)` THEN REWRITE_TAC[cm_smap] THEN
      STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[CMR_CAPMAP_FACTS]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= b ==> abs(x - y) <= b ==> abs(y / &2 - x / &2) <= b`) THEN
  SUBGOAL_THEN
   `&0 <= wan_dir (ball(c:real^2,r)) (\x. (V:real^2->real^K) x - M x) /\
    &0 <= wan_dir (ball(c:real^2,r)) (V:real^2->real^K) /\
    &0 <= wan_dir (ball(c:real^2,r)) (M:real^2->real^K) /\
    &0 <= wan_gdir (ball(c:real^2,r)) G (M:real^2->real^K)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC WAN_DIR_POS THEN ASM_MESON_TAC[wan_w120];
      MATCH_MP_TAC WAN_DIR_POS THEN ASM_MESON_TAC[cm_cmap];
      MATCH_MP_TAC WAN_DIR_POS THEN ASM_MESON_TAC[cm_cmap];
      FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMW_TARGET_FACTS) THEN
      MATCH_MP_TAC HMC_GDIR_POS THEN EXISTS_TAC `Lam':real` THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[cm_harmonic]; ASM_MESON_TAC[cm_cmap]]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
  TRY(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
  MATCH_MP_TAC SQRT_POS_LE THEN ASM_REWRITE_TAC[]);;

let CMR_SUM_SQRT_CS = prove
 (`!(a:num->real) b n.
     (!k. 1 <= k /\ k <= n ==> &0 <= a k /\ &0 <= b k)
     ==> sum(1..n) (\k. sqrt(a k) * sqrt(b k)) <= sqrt(sum(1..n) a) * sqrt(sum(1..n) b)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`; ARITH; SQRT_0; REAL_MUL_LZERO;
              REAL_LE_REFL] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[ARITH_RULE `k <= n ==> k <= SUC n`]; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= sum(1..n) (a:num->real) /\ &0 <= sum(1..n) (b:num->real) /\
                &0 <= a(SUC n) /\ &0 <= b(SUC n)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC SUM_POS_LE_NUMSEG) THEN
    ASM_MESON_TAC[ARITH_RULE `k <= n ==> k <= SUC n`; ARITH_RULE `1 <= SUC n`; LE_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(sum(1..n) a) * sqrt(sum(1..n) b) + sqrt((a:num->real)(SUC n)) * sqrt(b(SUC n))` THEN
  ASM_SIMP_TAC[REAL_LE_RADD] THEN
  MP_TAC(SPECL [`sum(1..n) (a:num->real)`; `(a:num->real)(SUC n)`;
                `sum(1..n) (b:num->real)`; `(b:num->real)(SUC n)`] CMR_CS2) THEN
  ASM_REWRITE_TAC[]);;

(* Abbreviations for the one-cap stability bound.                           *)

let cmr_stab_df = new_definition
 `cmr_stab_df S (G:real^K->real^K^K) (Q:real^3^3) (c:real^2) r (u:real^3->real^K) =
    wan_dir (ball(c,r)) (\x. u(cm_capmap Q x) - cmr_minw S G c r (\x. u(cm_capmap Q x)) x)`;;

let cmr_stab_x = new_definition
 `cmr_stab_x S (G:real^K->real^K^K) (Q:real^3^3) (c:real^2) r (u:real^3->real^K) =
    sqrt(wan_dir (ball(c,r)) (\x. u(cm_capmap Q x))) +
    sqrt(wan_dir (ball(c,r)) (cmr_minw S G c r (\x. u(cm_capmap Q x)))) +
    sqrt(wan_gdir (ball(c,r)) G (cmr_minw S G c r (\x. u(cm_capmap Q x)))) *
    sqrt(wan_dir (ball(c,r)) (cmr_minw S G c r (\x. u(cm_capmap Q x))))`;;

let CMR_STAB_CONG = prove
 (`!S (G:real^K->real^K^K) (Q:real^3^3) (c:real^2) r (u:real^3->real^K) u'.
     (!y. y IN IMAGE (cm_capmap Q) (cball(c,r)) ==> u y = u' y)
     ==> cmr_stab_df S G Q c r u = cmr_stab_df S G Q c r u' /\
         cmr_stab_x S G Q c r u = cmr_stab_x S G Q c r u'`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!x. x IN cball(c:real^2,r) ==> (u:real^3->real^K)(cm_capmap Q x) = u'(cm_capmap Q x)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `cmr_minw S (G:real^K->real^K^K) (c:real^2) r (\x. (u:real^3->real^K)(cm_capmap Q x)) =
                cmr_minw S G c r (\x. u'(cm_capmap Q x))` ASSUME_TAC THENL
   [MATCH_MP_TAC CMR_MINW_CONG THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN ball(c:real^2,r) ==> (u:real^3->real^K)(cm_capmap Q x) = u'(cm_capmap Q x)`
  ASSUME_TAC THENL [ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[cmr_stab_df; cmr_stab_x] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CMW_DIR_EQ_ON THEN ASM_SIMP_TAC[];
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC CMW_DIR_EQ_ON THEN ASM_SIMP_TAC[]]);;

let CMR_REPN_STAB_SUM = prove
 (`!S (G:real^K->real^K^K) e K2 Lam n (Q:num->real^3^3) (c:num->real^2) (r:num->real)
    (u:real^3->real^K) W.
     cmw_repex S G e /\ CMR_GCOND G Lam /\
     (!(Q:real^3^3) (c:real^2) r (v:real^3->real^K) W.
        cm_smap S v /\ orthogonal_matrix Q /\ &0 < r /\
        wan_gdir (ball(c,r)) G (\x. v(cm_capmap Q x)) <= e /\
        open_in (subtopology euclidean (sphere(vec 0,&1))) W
        ==> abs(cmr_sen_on G (cmr_rep1 S G Q c r v) W - cmr_sen_on G v W)
            <= K2 * sqrt(cmr_stab_df S G Q c r v) * cmr_stab_x S G Q c r v) /\
     cm_smap S u /\
     (!k. 1 <= k /\ k <= n ==> orthogonal_matrix(Q k)) /\
     (!k l. 1 <= k /\ k < l /\ l <= n /\ &0 < r k /\ &0 < r l
            ==> DISJOINT (IMAGE (cm_capmap (Q k)) (cball(c k,r k)))
                         (IMAGE (cm_capmap (Q l)) (cball(c l,r l)))) /\
     (!k. 1 <= k /\ k <= n /\ &0 < r k
          ==> wan_gdir (ball(c k,r k)) G (\x. u(cm_capmap (Q k) x)) <= e) /\
     open_in (subtopology euclidean (sphere(vec 0,&1))) W
     ==> !m. m <= n
             ==> abs(cmr_sen_on G (cmr_repn S G m Q c r u) W - cmr_sen_on G u W)
                 <= K2 * sum(1..m) (\k. if &0 < r k
                                       then sqrt(cmr_stab_df S G (Q k) (c k) (r k) u) *
                                            cmr_stab_x S G (Q k) (c k) (r k) u
                                       else &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n:num`;
                 `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`; `u:real^3->real^K`]
                CMR_REPN_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[cmr_repn; SUM_CLAUSES_NUMSEG; ARITH; REAL_SUB_REFL; REAL_ABS_0;
                REAL_MUL_RZERO; REAL_LE_REFL];
    ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o
    check (fun th -> is_forall(concl th) &&
                     can (find_term (fun t -> is_const t && fst(dest_const t) = "cmr_repn"))
                         (concl th))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  REWRITE_TAC[cmr_repn; SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC m`] THEN
  ABBREV_TAC `um = cmr_repn S (G:real^K->real^K^K) m (Q:num->real^3^3) (c:num->real^2) r
                     (u:real^3->real^K)` THEN
  COND_CASES_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[CMR_REP1_NONPOS; REAL_ARITH `~(&0 < r) ==> r <= &0`; REAL_ADD_RID]] THEN
  SUBGOAL_THEN
   `!y. y IN IMAGE (cm_capmap ((Q:num->real^3^3)(SUC m))) (cball((c:num->real^2)(SUC m),r(SUC m)))
        ==> (um:real^3->real^K) y = u y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o
      check (fun th -> is_forall(concl th) &&
                       can (find_term (fun t -> is_const t && fst(dest_const t) = "cball"))
                           (concl th) &&
                       can (find_term (fun t -> is_var t && fst(dest_var t) = "um")) (concl th))) THEN
    EXISTS_TAC `SUC m` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `(Q:num->real^3^3)(SUC m)`;
                 `(c:num->real^2)(SUC m)`; `(r:num->real)(SUC m)`; `um:real^3->real^K`;
                 `u:real^3->real^K`] CMR_STAB_CONG) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`(Q:num->real^3^3)(SUC m)`; `(c:num->real^2)(SUC m)`;
                                `(r:num->real)(SUC m)`; `um:real^3->real^K`; `W:real^3->bool`] o
    check (fun th -> is_forall(concl th) &&
                     can (find_term (fun t -> t = `K2:real`)) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[LE_REFL; ARITH_RULE `1 <= SUC m`]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `wan_gdir (ball((c:num->real^2)(SUC m),r(SUC m))) G
                  (\x. (u:real^3->real^K)(cm_capmap ((Q:num->real^3^3)(SUC m)) x))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC CMT_WAN_GDIR_EQ THEN
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `x:real^2` THEN ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC
   `abs(cmr_sen_on (G:real^K->real^K^K) (um:real^3->real^K) W - cmr_sen_on G u W) <=
    K2 * sum(1..m) (\k. if &0 < r k
                        then sqrt(cmr_stab_df S G ((Q:num->real^3^3) k) ((c:num->real^2) k) (r k)
                                     (u:real^3->real^K)) *
                             cmr_stab_x S G (Q k) (c k) (r k) u
                        else &0)` THEN
  REAL_ARITH_TAC);;

(* Bounds for the one-cap stability terms.                                  *)

let CMR_STAB_TERMS = prove
 (`!S (G:real^K->real^K^K) d e ec cc lam Lam (Q:real^3^3) (c:real^2) r (u:real^3->real^K).
     cm_target S G d /\ cmw_repex S G e /\ e <= ec /\ &0 < lam /\
     (!z v. lam * norm v pow 2 <= v dot (G z ** v)) /\
     (!z v. &0 <= v dot (G z ** v) /\ v dot (G z ** v) <= Lam * norm v pow 2) /\
     (!(a:real^2) r (u:real^2->real^K) v.
        &0 < r /\ cm_harmonic S G (ball(a,r)) v /\ cm_wmap S (ball(a,r)) v /\
        wan_gdir (ball(a,r)) G v <= ec /\ cm_wmap S (ball(a,r)) u /\
        wan_w120 (ball(a,r)) (\x. u x - v x)
        ==> cc * wan_dir (ball(a,r)) (\x. u x - v x)
            <= wan_gdir (ball(a,r)) G u - wan_gdir (ball(a,r)) G v) /\
     cm_smap S u /\ orthogonal_matrix Q /\ &0 < r /\
     wan_gdir (ball(c,r)) G (\x. u(cm_capmap Q x)) <= e
     ==> &0 <= cmr_stab_df S G Q c r u /\ &0 <= cmr_stab_x S G Q c r u /\
         cc * cmr_stab_df S G Q c r u <=
         &2 * (cm_gen G (ball(c,r)) (\x. u(cm_capmap Q x)) -
               cm_gen G (ball(c,r)) (cmr_minw S G c r (\x. u(cm_capmap Q x)))) /\
         cmr_stab_x S G Q c r u pow 2 <=
         (&8 * wan_gdir (ball(c,r)) G (\x. u(cm_capmap Q x)) +
          &2 * wan_gdir (ball(c,r)) G (\x. u(cm_capmap Q x)) pow 2) / lam`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMW_TARGET_FACTS) THEN
  ABBREV_TAC `U = \x. (u:real^3->real^K)(cm_capmap Q x)` THEN
  SUBGOAL_THEN `cm_cmap S (ball(c:real^2,r)) (U:real^2->real^K)` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN ASM_SIMP_TAC[CMR_CHART_CMAP]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `c:real^2`; `r:real`;
                 `U:real^2->real^K`] CMR_MINW_WORKS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `M = cmr_minw S (G:real^K->real^K^K) (c:real^2) r (U:real^2->real^K)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `wan_w120 (ball(c:real^2,r)) (\x. (U:real^2->real^K) x - M x)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(\x. (U:real^2->real^K) x - M x) = (\x. --((\x. M x - U x) x))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC WAN_W120_NEG THEN ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_gdir (ball(c:real^2,r)) G (M:real^2->real^K) <=
                wan_gdir (ball(c,r)) G (U:real^2->real^K)` ASSUME_TAC THENL
   [UNDISCH_TAC `cm_minimizer S (G:real^K->real^K^K) (ball(c,r)) (M:real^2->real^K)` THEN
    REWRITE_TAC[cm_minimizer; cm_gen] THEN
    DISCH_THEN(MP_TAC o SPEC `U:real^2->real^K` o CONJUNCT2) THEN
    ASM_SIMP_TAC[CMR_CMAP_WMAP] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 (ball(c:real^2,r)) (U:real^2->real^K) /\
                wan_w12 (ball(c:real^2,r)) (M:real^2->real^K)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_cmap]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(c:real^2,r)`; `G:real^K->real^K^K`; `U:real^2->real^K`;
                 `lam:real`; `Lam:real`] HMD_GDIR_BOUNDS) THEN
  MP_TAC(ISPECL [`ball(c:real^2,r)`; `G:real^K->real^K^K`; `M:real^2->real^K`;
                 `lam:real`; `Lam:real`] HMD_GDIR_BOUNDS) THEN
  ASM_SIMP_TAC[OPEN_BALL; REAL_LT_IMP_LE] THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= wan_dir (ball(c:real^2,r)) (\x. (U:real^2->real^K) x - M x) /\
                &0 <= wan_dir (ball(c:real^2,r)) (U:real^2->real^K) /\
                &0 <= wan_dir (ball(c:real^2,r)) (M:real^2->real^K)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_DIR_POS] THEN MATCH_MP_TAC WAN_DIR_POS THEN ASM_MESON_TAC[wan_w120];
    ALL_TAC] THEN
  REWRITE_TAC[cmr_stab_df; cmr_stab_x; cm_gen] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\x. (u:real^3->real^K)(cm_capmap Q x) - M x) = (\x. (U:real^2->real^K) x - M x)`
  SUBST1_TAC THENL [EXPAND_TAC "U" THEN REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    MATCH_MP_TAC SQRT_POS_LE THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`c:real^2`; `r:real`; `U:real^2->real^K`; `M:real^2->real^K`] o
      check (fun th -> is_forall(concl th) &&
                       can (find_term (fun t -> t = `cc:real`)) (concl th))) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[CMR_CMAP_WMAP] THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `g = wan_gdir (ball(c:real^2,r)) G (U:real^2->real^K)` THEN
  SUBGOAL_THEN `&0 <= g` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `sqrt(wan_dir (ball(c:real^2,r)) (U:real^2->real^K)) <= sqrt(g / lam) /\
    sqrt(wan_dir (ball(c:real^2,r)) (M:real^2->real^K)) <= sqrt(g / lam) /\
    sqrt(wan_gdir (ball(c:real^2,r)) G (M:real^2->real^K)) <= sqrt g`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC SQRT_MONO_LE THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(sqrt(g / lam) + sqrt(g / lam) + sqrt g * sqrt(g / lam)) pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
      TRY(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      MATCH_MP_TAC SQRT_POS_LE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[SQRT_POS_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= g / lam` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(a + a + b * a) pow 2 = (a pow 2) * (&2 + b) pow 2`] THEN
  ASM_SIMP_TAC[SQRT_POW_2] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `g / lam * (&8 + &2 * sqrt g pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `sqrt g - &2` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[SQRT_POW_2] THEN
    REWRITE_TAC[real_div; REAL_POW_2] THEN REAL_ARITH_TAC]);;

(* Global stability: replacement on disjoint small caps changes the energy  *)
(* on any open subset of S^2 by at most                                     *)
(*   CS sqrt(energy decrease) sqrt(sum of (E_k + E_k^2)).                    *)

let CMR_REPN_STAB = prove
 (`!S (G:real^K->real^K^K) d e0 (C:num->real) e ec cc.
     cm_target S G d /\
     (!(a:real^2) r (u:real^2->real^K) l x.
        &0 < r /\ cm_harmonic S G (ball(a,r)) u /\ wan_w12 (ball(a,r)) u /\
        wan_gdir (ball(a,r)) G u <= e0 /\
        ALL (\i. 1 <= i /\ i <= 2) l /\ ~(l = []) /\ x IN ball(a,r / &2)
        ==> r pow (LENGTH l) * norm(iterated_partial l u x)
            <= C (LENGTH l) * sqrt(wan_gdir (ball(a,r)) G u)) /\
     (!k. &0 < C k) /\ cmw_repex S G e /\ e <= e0 /\ e <= ec /\ &0 < cc /\
     (!(a:real^2) r (u:real^2->real^K) v.
        &0 < r /\ cm_harmonic S G (ball(a,r)) v /\ cm_wmap S (ball(a,r)) v /\
        wan_gdir (ball(a,r)) G v <= ec /\ cm_wmap S (ball(a,r)) u /\
        wan_w120 (ball(a,r)) (\x. u x - v x)
        ==> cc * wan_dir (ball(a,r)) (\x. u x - v x)
            <= wan_gdir (ball(a,r)) G u - wan_gdir (ball(a,r)) G v)
     ==> ?CS. &0 < CS /\
              !n (Q:num->real^3^3) (c:num->real^2) (r:num->real) (u:real^3->real^K) W.
                cm_smap S u /\
                (!k. 1 <= k /\ k <= n ==> orthogonal_matrix(Q k)) /\
                (!k l. 1 <= k /\ k < l /\ l <= n /\ &0 < r k /\ &0 < r l
                       ==> DISJOINT (IMAGE (cm_capmap (Q k)) (cball(c k,r k)))
                                    (IMAGE (cm_capmap (Q l)) (cball(c l,r l)))) /\
                (!k. 1 <= k /\ k <= n /\ &0 < r k
                     ==> wan_gdir (ball(c k,r k)) G (\x. u(cm_capmap (Q k) x)) <= e) /\
                open_in (subtopology euclidean (sphere(vec 0,&1))) W
                ==> abs(cmr_sen_on G (cmr_repn S G n Q c r u) W - cmr_sen_on G u W)
                    <= CS * sqrt(cm_sen G u - cm_sen G (cmr_repn S G n Q c r u)) *
                       sqrt(sum(1..n) (\k. if &0 < r k
                                           then wan_gdir (ball(c k,r k)) G
                                                  (\x. u(cm_capmap (Q k) x)) +
                                                wan_gdir (ball(c k,r k)) G
                                                  (\x. u(cm_capmap (Q k) x)) pow 2
                                           else &0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CMW_TARGET_FACTS) THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Lg:real` STRIP_ASSUME_TAC o MATCH_MP CMR_TARGET_GCOND) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e0:real`; `C:num->real`;
                 `e:real`] CMR_REP1_STAB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `K2:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `K2 * sqrt(&2 / cc) * sqrt(&8 / lam)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LT THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `K2:real`; `Lg:real`;
                 `n:num`; `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`;
                 `u:real^3->real^K`; `W:real^3->bool`] CMR_REPN_STAB_SUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[cmr_stab_df; cmr_stab_x] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[LE_REFL] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lg:real`; `n:num`;
                 `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`; `u:real^3->real^K`]
                CMR_REPN_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[LE_REFL] THEN
  DISCH_THEN(ASSUME_TAC o last o CONJUNCTS) THEN
  SUBGOAL_THEN
   `!k. 1 <= k /\ k <= n /\ &0 < r k
        ==> &0 <= cmr_stab_df S (G:real^K->real^K^K) ((Q:num->real^3^3) k) ((c:num->real^2) k)
                    (r k) (u:real^3->real^K) /\
            &0 <= cmr_stab_x S G (Q k) (c k) (r k) u /\
            cc * cmr_stab_df S G (Q k) (c k) (r k) u <=
            &2 * (cm_gen G (ball(c k,r k)) (\x. u(cm_capmap (Q k) x)) -
                  cm_gen G (ball(c k,r k)) (cmr_minw S G (c k) (r k) (\x. u(cm_capmap (Q k) x)))) /\
            cmr_stab_x S G (Q k) (c k) (r k) u pow 2 <=
            (&8 * wan_gdir (ball(c k,r k)) G (\x. u(cm_capmap (Q k) x)) +
             &2 * wan_gdir (ball(c k,r k)) G (\x. u(cm_capmap (Q k) x)) pow 2) / lam`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CMR_STAB_TERMS THEN
    MAP_EVERY EXISTS_TAC [`d:real`; `e:real`; `ec:real`; `Lam:real`] THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `aa = \k. if &0 < (r:num->real) k
                       then cmr_stab_df S (G:real^K->real^K^K) ((Q:num->real^3^3) k)
                              ((c:num->real^2) k) (r k) (u:real^3->real^K)
                       else &0` THEN
  ABBREV_TAC `bb = \k. if &0 < (r:num->real) k
                       then cmr_stab_x S (G:real^K->real^K^K) ((Q:num->real^3^3) k)
                              ((c:num->real^2) k) (r k) (u:real^3->real^K) pow 2
                       else &0` THEN
  SUBGOAL_THEN
   `sum(1..n) (\k. if &0 < (r:num->real) k
                   then sqrt(cmr_stab_df S (G:real^K->real^K^K) ((Q:num->real^3^3) k)
                               ((c:num->real^2) k) (r k) (u:real^3->real^K)) *
                        cmr_stab_x S G (Q k) (c k) (r k) u
                   else &0) =
    sum(1..n) (\k. sqrt((aa:num->real) k) * sqrt((bb:num->real) k))`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    MAP_EVERY EXPAND_TAC ["aa"; "bb"] THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[SQRT_0; REAL_MUL_LZERO] THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC POW_2_SQRT THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. 1 <= k /\ k <= n ==> &0 <= (aa:num->real) k /\ &0 <= (bb:num->real) k`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN STRIP_TAC THEN MAP_EVERY EXPAND_TAC ["aa"; "bb"] THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL; REAL_LE_POW_2] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`aa:num->real`; `bb:num->real`; `n:num`] CMR_SUM_SQRT_CS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `sum(1..n) (aa:num->real) <=
    &2 / cc * (cm_sen G (u:real^3->real^K) -
               cm_sen G (cmr_repn S (G:real^K->real^K^K) n (Q:num->real^3^3) (c:num->real^2)
                           (r:num->real) u)) /\
    sum(1..n) (bb:num->real) <=
    &8 / lam * sum(1..n) (\k. if &0 < r k
                              then wan_gdir (ball(c k,r k)) G (\x. u(cm_capmap (Q k) x)) +
                                   wan_gdir (ball(c k,r k)) G (\x. u(cm_capmap (Q k) x)) pow 2
                              else &0)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_ARITH `a - (a - b) = b`] THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN CONJ_TAC THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN MAP_EVERY EXPAND_TAC ["aa"; "bb"] THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RZERO; REAL_LE_REFL] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o
      check (fun th -> is_forall(concl th) &&
                       can (find_term (fun t -> t = `cc:real`)) (concl th) &&
                       can (find_term (fun t -> t = `lam:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&2 / cc * x = (&2 * x) / cc`;
                   REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(&8 * wan_gdir (ball((c:num->real^2) k,r k)) G
                          (\x. (u:real^3->real^K)(cm_capmap ((Q:num->real^3^3) k) x)) +
                   &2 * wan_gdir (ball(c k,r k)) G (\x. u(cm_capmap (Q k) x)) pow 2) / lam` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_ARITH `&8 / l * x = (&8 * x) / l`] THEN
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
      MP_TAC(SPEC `wan_gdir (ball((c:num->real^2) k,r k)) G
                     (\x. (u:real^3->real^K)(cm_capmap ((Q:num->real^3^3) k) x))` REAL_LE_POW_2) THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o
    check (fun th -> is_eq(concl th) &&
                     can (find_term (fun t -> is_const t && fst(dest_const t) = "cm_sen"))
                         (lhs(concl th)))) THEN
  SUBGOAL_THEN `&0 <= sum(1..n) (aa:num->real) /\ &0 <= sum(1..n) (bb:num->real)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= cm_sen G (u:real^3->real^K) -
          cm_sen G (cmr_repn S (G:real^K->real^K^K) n (Q:num->real^3^3) (c:num->real^2)
                      (r:num->real) u)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &2 / cc` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[GSYM(MATCH_MP (CONJUNCT1 REAL_LE_MUL_EQ) th)]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `K2 * sqrt(sum(1..n) (aa:num->real)) * sqrt(sum(1..n) (bb:num->real))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `K2 * sum(1..n) (\k. sqrt((aa:num->real) k) * sqrt((bb:num->real) k))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(K * a * b) * c * d = K * (a * c) * (b * d)`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_MESON_TAC[];
    ASM_SIMP_TAC[GSYM SQRT_MUL; REAL_LE_DIV; REAL_LT_IMP_LE; REAL_POS] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_MESON_TAC[];
    ASM_SIMP_TAC[GSYM SQRT_MUL; REAL_LE_DIV; REAL_LT_IMP_LE; REAL_POS] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN FIRST_ASSUM ACCEPT_TAC]);;


(* ========================================================================= *)
(* Disjoint cap families on S^2.  The energy on an open subset               *)
(* of S^2 splits over the caps of a disjoint family; replacement on the     *)
(* family minimizes the energy among maps that agree with u off its open    *)
(* caps (so energy decreases are monotone in the radius); bounds for the    *)
(* energy of the replaced map on open sets and for the S^2 Dirichlet        *)
(* energy of the change.                                                    *)
(* ========================================================================= *)

let cmr_dfam = new_definition
 `cmr_dfam (n:num) (Q:num->real^3^3) (c:num->real^2) (r:num->real) <=>
    (!k. 1 <= k /\ k <= n ==> orthogonal_matrix(Q k)) /\
    (!k l. 1 <= k /\ k < l /\ l <= n /\ &0 < r k /\ &0 < r l
           ==> DISJOINT (IMAGE (cm_capmap (Q k)) (cball(c k,r k)))
                        (IMAGE (cm_capmap (Q l)) (cball(c l,r l))))`;;

let cmr_fop = new_definition
 `cmr_fop (n:num) (Q:num->real^3^3) (c:num->real^2) (r:num->real) =
    {y:real^3 | ?k. 1 <= k /\ k <= n /\ y IN IMAGE (cm_capmap (Q k)) (ball(c k,r k))}`;;

let cmr_fcl = new_definition
 `cmr_fcl (n:num) (Q:num->real^3^3) (c:num->real^2) (r:num->real) =
    {y:real^3 | ?k. 1 <= k /\ k <= n /\ &0 < r k /\
                    y IN IMAGE (cm_capmap (Q k)) (cball(c k,r k))}`;;

let CMR_CONE_SETOPS = prove
 (`cmr_cone {} = {} /\
   (!E1 E2. cmr_cone (E1 DIFF E2) = cmr_cone E1 DIFF cmr_cone E2) /\
   (!E1 E2. cmr_cone (E1 INTER E2) = cmr_cone E1 INTER cmr_cone E2) /\
   (!E1 E2. E1 SUBSET E2 ==> cmr_cone E1 SUBSET cmr_cone E2) /\
   (!E. cmr_cone E SUBSET wan_shell)`,
  REWRITE_TAC[cmr_cone] THEN SET_TAC[]);;

let CMR_SEN_ON_BASICS = prove
 (`!(G:real^K->real^K^K) (u:real^3->real^K) Lam.
     CMR_GCOND G Lam /\ wan_s2_w12 u
     ==> cmr_sen_on G u {} = &0 /\
         (!E. lebesgue_measurable(cmr_cone E) ==> &0 <= cmr_sen_on G u E) /\
         (!E. negligible(cmr_cone E) ==> cmr_sen_on G u E = &0) /\
         (!E1 E2. lebesgue_measurable(cmr_cone E1) /\ lebesgue_measurable(cmr_cone E2) /\
                  E1 SUBSET E2
                  ==> cmr_sen_on G u E1 <= cmr_sen_on G u E2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CMR_GCOND] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!E. lebesgue_measurable(cmr_cone E)
        ==> (\z. lift(cmr_dens (G:real^K->real^K^K) (u:real^3->real^K) z))
            integrable_on cmr_cone E`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`; `Lam:real`;
                   `cmr_cone E`] CMR_DENS_FACTS) THEN
    ASM_REWRITE_TAC[CMR_CONE_SETOPS] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. &0 <= cmr_dens (G:real^K->real^K^K) (u:real^3->real^K) z`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`; `Lam:real`;
                   `{}:real^3->bool`] CMR_DENS_FACTS) THEN
    ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_EMPTY; EMPTY_SUBSET] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[cmr_sen_on] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[CMR_CONE_SETOPS; INTEGRAL_EMPTY; DROP_VEC] THEN REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_SIMP_TAC[LIFT_DROP];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `integral (cmr_cone E)
                    (\z. lift(cmr_dens (G:real^K->real^K^K) (u:real^3->real^K) z)) = vec 0`
    SUBST1_TAC THENL
     [MATCH_MP_TAC INTEGRAL_UNIQUE THEN MATCH_MP_TAC HAS_INTEGRAL_NEGLIGIBLE THEN
      EXISTS_TAC `cmr_cone E` THEN ASM_REWRITE_TAC[DIFF_EQ_EMPTY; NOT_IN_EMPTY];
      REWRITE_TAC[DROP_VEC] THEN REAL_ARITH_TAC];
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> a / &3 <= b / &3`) THEN
    MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
    ASM_SIMP_TAC[LIFT_DROP] THEN MATCH_MP_TAC(el 3 (CONJUNCTS CMR_CONE_SETOPS)) THEN
    ASM_REWRITE_TAC[]]);;

let CMR_FAM_SETS0 = prove
 (`!(Q:num->real^3^3) (c:num->real^2) r. cmr_fop 0 Q c r = {} /\ cmr_fcl 0 Q c r = {}`,
  REWRITE_TAC[cmr_fop; cmr_fcl; EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  MESON_TAC[ARITH_RULE `~(1 <= k /\ k <= 0)`]);;

let CMR_FAM_SETS_SUC = prove
 (`!n (Q:num->real^3^3) (c:num->real^2) r.
      cmr_fop (SUC n) Q c r =
      cmr_fop n Q c r UNION IMAGE (cm_capmap (Q(SUC n))) (ball(c(SUC n),r(SUC n))) /\
      cmr_fcl (SUC n) Q c r =
      cmr_fcl n Q c r UNION
      (if &0 < r(SUC n) then IMAGE (cm_capmap (Q(SUC n))) (cball(c(SUC n),r(SUC n)))
       else {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmr_fop; cmr_fcl; EXTENSION; IN_ELIM_THM; IN_UNION] THEN
  CONJ_TAC THEN X_GEN_TAC `y:real^3` THENL
   [ALL_TAC; COND_CASES_TAC THEN REWRITE_TAC[NOT_IN_EMPTY]] THEN
  REWRITE_TAC[LE] THEN ASM_MESON_TAC[ARITH_RULE `1 <= SUC n`]);;

let CMR_FCL_CLOSED = prove
 (`!n (Q:num->real^3^3) (c:num->real^2) r. closed(cmr_fcl n Q c r)`,
  INDUCT_TAC THEN REWRITE_TAC[CMR_FAM_SETS0; CMR_FAM_SETS_SUC; CLOSED_EMPTY] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC CLOSED_UNION THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[CLOSED_EMPTY] THEN
  MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
  MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN REWRITE_TAC[COMPACT_CBALL] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
  SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; CMR_CAPMAP_SMOOTH; SUBSET_UNIV]);;

let CMR_FOP_SUBSET = prove
 (`!n (Q:num->real^3^3) (c:num->real^2) r. cmr_fop n Q c r SUBSET cmr_fcl n Q c r`,
  REWRITE_TAC[cmr_fop; cmr_fcl; SUBSET; IN_ELIM_THM; IN_IMAGE; IN_BALL; IN_CBALL] THEN
  MESON_TAC[DIST_POS_LE; REAL_LET_TRANS; REAL_LT_IMP_LE]);;

let CMR_FAM_IN_SPHERE = prove
 (`!n (Q:num->real^3^3) (c:num->real^2) r.
     (!k. 1 <= k /\ k <= n ==> orthogonal_matrix(Q k))
     ==> cmr_fcl n Q c r SUBSET sphere(vec 0,&1) /\
         cmr_fop n Q c r SUBSET sphere(vec 0,&1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(SET_RULE `t SUBSET u /\ s SUBSET t ==> t SUBSET u /\ s SUBSET (u:real^3->bool)`) THEN
  REWRITE_TAC[CMR_FOP_SUBSET] THEN
  REWRITE_TAC[cmr_fcl; SUBSET; IN_ELIM_THM; IN_IMAGE] THEN ASM_MESON_TAC[CMR_CAPMAP_FACTS]);;

let CMR_FOP_OPEN_IN = prove
 (`!n (Q:num->real^3^3) (c:num->real^2) r.
     (!k. 1 <= k /\ k <= n ==> orthogonal_matrix(Q k))
     ==> open_in (subtopology euclidean (sphere(vec 0,&1))) (cmr_fop n Q c r)`,
  INDUCT_TAC THEN REWRITE_TAC[CMR_FAM_SETS0; CMR_FAM_SETS_SUC; OPEN_IN_EMPTY] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OPEN_IN_UNION THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[ARITH_RULE `k <= n ==> k <= SUC n`];
    MATCH_MP_TAC CMR_CAP_OPEN_IN THEN REWRITE_TAC[OPEN_BALL] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC]);;

let CMR_DFAM_SUC = prove
 (`!n (Q:num->real^3^3) (c:num->real^2) r.
     cmr_dfam (SUC n) Q c r ==> cmr_dfam n Q c r`,
  REWRITE_TAC[cmr_dfam] THEN MESON_TAC[ARITH_RULE `k <= n ==> k <= SUC n`]);;

let CMR_DFAM_LE = prove
 (`!n m (Q:num->real^3^3) (c:num->real^2) r.
     cmr_dfam n Q c r /\ m <= n ==> cmr_dfam m Q c r`,
  REWRITE_TAC[cmr_dfam] THEN MESON_TAC[LE_TRANS]);;

(* Shrinking the radii keeps a family disjoint.                             *)

let CMR_DFAM_SHRINK = prove
 (`!n (Q:num->real^3^3) (c:num->real^2) r r'.
     cmr_dfam n Q c r /\ (!k. 1 <= k /\ k <= n /\ &0 < r' k ==> r' k <= r k)
     ==> cmr_dfam n Q c r'`,
  REWRITE_TAC[cmr_dfam] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `r' (k:num) <= r k /\ r' (l:num) <= (r:num->real) l` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `l:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `s SUBSET s' /\ t SUBSET t'
                         ==> DISJOINT s' t' ==> DISJOINT s (t:real^3->bool)`) THEN
  CONJ_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN
  MATCH_MP_TAC SUBSET_CBALL THEN ASM_REWRITE_TAC[]);;

(* The energy on an open subset W of S^2 splits over a disjoint family:    *)
(* the parts in the open caps and the part off the closed caps.            *)

let CMR_SEN_ON_FAM_SPLIT = prove
 (`!(G:real^K->real^K^K) Lam (f:real^3->real^K) n Q (c:num->real^2) r W.
     CMR_GCOND G Lam /\ wan_s2_w12 f /\ cmr_dfam n Q c r /\
     open_in (subtopology euclidean (sphere(vec 0,&1))) W
     ==> cmr_sen_on G f W =
         sum(1..n) (\k. cmr_sen_on G f (W INTER IMAGE (cm_capmap (Q k)) (ball(c k,r k)))) +
         cmr_sen_on G f (W DIFF cmr_fcl n Q c r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `f:real^3->real^K`; `Lam:real`] CMR_SEN_ON_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `cmr_dfam n Q (c:num->real^2) r` THEN SPEC_TAC(`n:num`,`n:num`) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[CMR_FAM_SETS0; SUM_CLAUSES_NUMSEG; ARITH; DIFF_EMPTY; REAL_ADD_LID];
    ALL_TAC] THEN
  DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP CMR_DFAM_SUC) THEN
  FIRST_X_ASSUM(fun th -> DISCH_THEN(SUBST1_TAC o MATCH_MP th)) THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`; GSYM REAL_ADD_ASSOC] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `orthogonal_matrix((Q:num->real^3^3)(SUC n))` ASSUME_TAC THENL
   [ASM_MESON_TAC[cmr_dfam; ARITH_RULE `1 <= SUC n /\ SUC n <= SUC n`]; ALL_TAC] THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean (sphere(vec 0:real^3,&1)))
      (W DIFF cmr_fcl n Q (c:num->real^2) r)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `W DIFF cmr_fcl n Q (c:num->real^2) r =
                  W DIFF (sphere(vec 0:real^3,&1) INTER cmr_fcl n Q c r)`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN REWRITE_TAC[CMR_FCL_CLOSED];
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 < (r:num->real)(SUC n)` THENL
   [ALL_TAC;
    SUBGOAL_THEN `ball((c:num->real^2)(SUC n),r(SUC n)) = {}` SUBST1_TAC THENL
     [REWRITE_TAC[BALL_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[CMR_FAM_SETS_SUC; IMAGE_CLAUSES; INTER_EMPTY; UNION_EMPTY;
                    REAL_ADD_LID]] THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `Lam:real`; `(Q:num->real^3^3)(SUC n)`;
                 `(c:num->real^2)(SUC n)`; `(r:num->real)(SUC n)`; `f:real^3->real^K`;
                 `W DIFF cmr_fcl n Q (c:num->real^2) r`] CMR_SEN_ON_CAP_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  BINOP_TAC THEN AP_TERM_TAC THENL
   [SUBGOAL_THEN
     `DISJOINT (IMAGE (cm_capmap ((Q:num->real^3^3)(SUC n))) (ball(c(SUC n),r(SUC n))))
               (cmr_fcl n Q (c:num->real^2) r)`
    MP_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    REWRITE_TAC[cmr_fcl; DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    UNDISCH_TAC `cmr_dfam (SUC n) Q (c:num->real^2) r` THEN REWRITE_TAC[cmr_dfam] THEN
    DISCH_THEN(MP_TAC o SPECL [`k:num`; `SUC n`] o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[LE_REFL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `y IN IMAGE (cm_capmap ((Q:num->real^3^3)(SUC n))) (ball(c(SUC n),r(SUC n)))` THEN
    MP_TAC(ISPECL [`(c:num->real^2)(SUC n)`; `(r:num->real)(SUC n)`] BALL_SUBSET_CBALL) THEN
    SET_TAC[];
    ASM_REWRITE_TAC[CMR_FAM_SETS_SUC] THEN ASM SET_TAC[]]);;

(* The boundary circle of a cap of a disjoint family meets no open cap of  *)
(* the family.                                                              *)

let CMR_FOP_CIRCLE = prove
 (`!n (Q:num->real^3^3) (c:num->real^2) r k x.
     cmr_dfam n Q c r /\ 1 <= k /\ k <= n /\ &0 < r k /\ x IN sphere(c k,r k)
     ==> ~(cm_capmap (Q k) x IN cmr_fop n Q c r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmr_dfam; cmr_fop; IN_ELIM_THM; IN_IMAGE] THEN
  STRIP_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `l:num` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `x':real^2` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `&0 < (r:num->real) l` ASSUME_TAC THENL
   [UNDISCH_TAC `x' IN ball((c:num->real^2) l,r l)` THEN REWRITE_TAC[IN_BALL] THEN
    MP_TAC(ISPECL [`(c:num->real^2) l`; `x':real^2`] DIST_POS_LE) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cm_capmap ((Q:num->real^3^3) k) x IN IMAGE (cm_capmap (Q k)) (cball(c k,r k)) /\
    cm_capmap (Q l) x' IN IMAGE (cm_capmap (Q l)) (cball((c:num->real^2) l,r l))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_MESON_TAC[SPHERE_SUBSET_CBALL; BALL_SUBSET_CBALL; SUBSET];
    ALL_TAC] THEN
  ASM_CASES_TAC `l:num = k` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `x:real^2 = x'` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[CMR_CAPMAP_FACTS]; ALL_TAC] THEN
    ASM_MESON_TAC[IN_BALL; IN_SPHERE; REAL_LT_REFL];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE `~(l:num = k) ==> l < k \/ k < l`)) THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`l:num`; `k:num`]);
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `l:num`])] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  ASM_MESON_TAC[]);;

(* A chart competitor that agrees on the circle with a continuous map v on  *)
(* the closed disc differs from v by a W_0 map.                              *)

let CMR_CHART_W120 = prove
 (`!S (Q:real^3^3) (c:real^2) r (w:real^3->real^K) (v:real^2->real^K).
     cm_smap S w /\ orthogonal_matrix Q /\ &0 < r /\ cm_cmap S (ball(c,r)) v /\
     (!x. x IN sphere(c,r) ==> w(cm_capmap Q x) = v x)
     ==> wan_w120 (ball(c,r)) (\x. w(cm_capmap Q x) - v x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:2)`; `(:K)`] WAN_W120_CONT) THEN
  REWRITE_TAC[WAN_W120_CONT_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[VECTOR_SUB_EQ] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC CMR_CHART_CONT THEN
      ASM_MESON_TAC[cm_smap];
      ASM_MESON_TAC[cm_cmap; CLOSURE_BALL]];
    MATCH_MP_TAC WAN_W12_SUB THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`S:real^K->bool`; `w:real^3->real^K`; `Q:real^3^3`; `c:real^2`; `r:real`]
             CMR_CHART_CMAP) THEN ASM_SIMP_TAC[cm_cmap];
      ASM_MESON_TAC[cm_cmap]]]);;

(* Replacement on a disjoint family minimizes the energy among maps that    *)
(* agree with u off its open caps.                                          *)

let CMR_REPN_MIN = prove
 (`!S (G:real^K->real^K^K) e Lam n Q (c:num->real^2) r (u:real^3->real^K) w.
     cmw_repex S G e /\ CMR_GCOND G Lam /\ cm_smap S u /\ cm_smap S w /\
     cmr_dfam n Q c r /\
     (!k. 1 <= k /\ k <= n /\ &0 < r k
          ==> wan_gdir (ball(c k,r k)) G (\x. u(cm_capmap (Q k) x)) <= e) /\
     (!y. y IN sphere(vec 0,&1) /\ ~(y IN cmr_fop n Q c r) ==> w y = u y)
     ==> cm_sen G (cmr_repn S G n Q c r u) <= cm_sen G w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n:num`;
                 `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`; `u:real^3->real^K`]
                CMR_REPN_FACTS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[cmr_dfam]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[LE_REFL] THEN
  ABBREV_TAC `h = cmr_repn S G n Q (c:num->real^2) r (u:real^3->real^K)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `wan_s2_w12 (h:real^3->real^K) /\ wan_s2_w12 (w:real^3->real^K)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[cm_smap]; ALL_TAC] THEN
  MP_TAC(ASSUME `CMR_GCOND (G:real^K->real^K^K) Lam`) THEN
  REWRITE_TAC[CMR_GCOND] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `h:real^3->real^K`; `Lam:real`] CMR_SEN_DENS) THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `w:real^3->real^K`; `Lam:real`] CMR_SEN_DENS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `Lam:real`; `h:real^3->real^K`; `n:num`;
                 `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`;
                 `sphere(vec 0:real^3,&1)`] CMR_SEN_ON_FAM_SPLIT) THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `Lam:real`; `w:real^3->real^K`; `n:num`;
                 `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`;
                 `sphere(vec 0:real^3,&1)`] CMR_SEN_ON_FAM_SPLIT) THEN
  ASM_REWRITE_TAC[OPEN_IN_REFL] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `cmr_sen_on G (h:real^3->real^K) (sphere(vec 0,&1) DIFF cmr_fcl n Q (c:num->real^2) r) =
    cmr_sen_on G (w:real^3->real^K) (sphere(vec 0,&1) DIFF cmr_fcl n Q c r)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CMR_SEN_ON_EQ_OPEN THEN
    EXISTS_TAC `sphere(vec 0:real^3,&1) DIFF cmr_fcl n Q (c:num->real^2) r` THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CMR_CONE_OPEN THEN MATCH_MP_TAC OPEN_IN_DIFF_CLOSED THEN
      REWRITE_TAC[CMR_FCL_CLOSED];
      ALL_TAC] THEN
    X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(y IN cmr_fop n Q (c:num->real^2) r)` ASSUME_TAC THENL
     [ASM_MESON_TAC[CMR_FOP_SUBSET; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `(h:real^3->real^K) y = u y` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `~(y IN cmr_fop n Q (c:num->real^2) r)` THEN
      REWRITE_TAC[cmr_fop; IN_ELIM_THM] THEN MESON_TAC[];
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> a + x <= b + x`) THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `orthogonal_matrix((Q:num->real^3^3) k)` ASSUME_TAC THENL
   [ASM_MESON_TAC[cmr_dfam]; ALL_TAC] THEN
  ASM_CASES_TAC `&0 < (r:num->real) k` THENL
   [ALL_TAC;
    SUBGOAL_THEN `ball((c:num->real^2) k,r k) = {}` SUBST1_TAC THENL
     [REWRITE_TAC[BALL_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IMAGE_CLAUSES; INTER_EMPTY] THEN
    SUBGOAL_THEN `cmr_sen_on G (h:real^3->real^K) {} = &0 /\
                  cmr_sen_on G (w:real^3->real^K) {} = &0`
      (fun th -> REWRITE_TAC[th; REAL_LE_REFL]) THEN
    ASM_MESON_TAC[CMR_SEN_ON_BASICS]] THEN
  SUBGOAL_THEN
   `sphere(vec 0,&1) INTER IMAGE (cm_capmap ((Q:num->real^3^3) k)) (ball((c:num->real^2) k,r k)) =
    IMAGE (cm_capmap (Q k)) (ball(c k,r k))`
  SUBST1_TAC THENL
   [MP_TAC(SPEC `(Q:num->real^3^3) k` CMR_CAPMAP_FACTS) THEN ASM_REWRITE_TAC[] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `h:real^3->real^K`; `(Q:num->real^3^3) k`; `Lam:real`;
                 `ball((c:num->real^2) k,r k)`] CMR_CAP_EN) THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `w:real^3->real^K`; `(Q:num->real^3^3) k`; `Lam:real`;
                 `ball((c:num->real^2) k,r k)`] CMR_CAP_EN) THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `wan_gdir (ball((c:num->real^2) k,r k)) G (\y. (h:real^3->real^K)(cm_capmap (Q k) y)) =
    wan_gdir (ball(c k,r k)) G (cmr_minw S G (c k) (r k) (\x. u(cm_capmap (Q k) x)))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CMT_WAN_GDIR_EQ THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `(c:num->real^2) k`;
                 `(r:num->real) k`; `\x. (u:real^3->real^K)(cm_capmap ((Q:num->real^3^3) k) x)`]
                CMR_MINW_WORKS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN MATCH_MP_TAC CMR_CHART_CMAP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `m = cmr_minw S G ((c:num->real^2) k) (r k) (\x. (u:real^3->real^K)(cm_capmap (Q k) x))` THEN
  STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `a / &2 <= b / &2 ==> a / &2 <= b / &2`) THEN
  UNDISCH_TAC `cm_minimizer S G (ball((c:num->real^2) k,r k)) (m:real^2->real^K)` THEN
  REWRITE_TAC[cm_minimizer; cm_gen] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN CONJ_TAC THENL
   [MATCH_MP_TAC CMR_CMAP_WMAP THEN MATCH_MP_TAC CMR_CHART_CMAP THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC CMR_CHART_W120 THEN EXISTS_TAC `S:real^K->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `x IN sphere((c:num->real^2) k,r k)`)]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[CMR_CAPMAP_FACTS];
    MATCH_MP_TAC CMR_FOP_CIRCLE THEN ASM_REWRITE_TAC[]]);;

(* G-energies of a W^{1,2} map are monotone in the open domain.             *)

let CMR_GDIR_MONO_W12 = prove
 (`!s t (G:real^K->real^K^K) (u:real^N->real^K) Lam.
     open s /\ open t /\ t SUBSET s /\ wan_w12 s u /\ CMR_GCOND G Lam
     ==> wan_gdir t G u <= wan_gdir s G u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CMR_GCOND] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`; `G:real^K->real^K^K`;
                 `u:real^N->real^K`] CMR_GDIR_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[wan_gdir] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!x. &0 <= wan_wd s i (u:real^N->real^K) x dot
             ((G:real^K->real^K^K)(u x) ** wan_wd s i u x)`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(wan_wd s i (u:real^N->real^K) x dot
              ((G:real^K->real^K^K)(u x) ** wan_wd s i u x)))
    absolutely_integrable_on s`
  ASSUME_TAC THENL
   [MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN CONJ_TAC THENL
     [REWRITE_TAC[DIMINDEX_1] THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `i' = 1` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[GSYM drop; LIFT_DROP];
      MATCH_MP_TAC HMD_GDIR_INTEGRABLE THEN EXISTS_TAC `Lam:real` THEN
      ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[REAL_ARITH `&0 <= x /\ x <= l ==> abs x <= l`]];
    ALL_TAC] THEN
  MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN];
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE]]);;

(* Replacement on one cap as a family with one member.                      *)

let CMR_REPN_ONE = prove
 (`!S (G:real^K->real^K^K) (Q:real^3^3) (c:real^2) r (u:real^3->real^K).
     cmr_repn S G 1 (\k. Q) (\k. c) (\k. r) u = cmr_rep1 S G Q c r u /\
     cmr_fop 1 (\k. Q) (\k. c) (\k. r) = IMAGE (cm_capmap Q) (ball(c,r)) /\
     (orthogonal_matrix Q ==> cmr_dfam 1 (\k. Q) (\k. c) (\k. r))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[num_CONV `1`; cmr_repn; CMR_FAM_SETS_SUC; CMR_FAM_SETS0;
                                  UNION_EMPTY] THEN
  REWRITE_TAC[cmr_dfam] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* Energy decreases from replacement grow with the radius.                  *)

let CMR_REP1_MONO = prove
 (`!S (G:real^K->real^K^K) e Lam (Q:real^3^3) (c:real^2) r r' (u:real^3->real^K).
     cmw_repex S G e /\ CMR_GCOND G Lam /\ cm_smap S u /\ orthogonal_matrix Q /\
     &0 < r /\ r' <= r /\ wan_gdir (ball(c,r)) G (\x. u(cm_capmap Q x)) <= e
     ==> cm_sen G (cmr_rep1 S G Q c r u) <= cm_sen G (cmr_rep1 S G Q c r' u)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `Q:real^3^3`; `c:real^2`;
                 `r:real`; `u:real^3->real^K`] CMR_REPN_ONE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `cm_smap S (cmr_rep1 S G Q (c:real^2) r' (u:real^3->real^K))` ASSUME_TAC THENL
   [ASM_CASES_TAC `&0 < r'` THENL
     [MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Q:real^3^3`;
                     `c:real^2`; `r':real`; `u:real^3->real^K`] CMR_REP1_FACTS) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `wan_gdir (ball(c,r)) G (\x. (u:real^3->real^K)(cm_capmap Q x))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CMR_GDIR_MONO_W12 THEN
      EXISTS_TAC `Lam:real` THEN ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_BALL THEN ASM_REWRITE_TAC[];
        MP_TAC(ISPECL [`S:real^K->bool`; `u:real^3->real^K`; `Q:real^3^3`; `c:real^2`;
                       `r:real`] CMR_CHART_CMAP) THEN ASM_SIMP_TAC[cm_cmap]];
      SUBGOAL_THEN `r' <= &0` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[CMR_REP1_NONPOS]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN sphere(vec 0,&1) /\ ~(y IN IMAGE (cm_capmap Q) (ball(c:real^2,r)))
        ==> cmr_rep1 S G Q c r' (u:real^3->real^K) y = u y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN REWRITE_TAC[cmr_rep1] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `~(y IN IMAGE (cm_capmap Q) (ball(c:real^2,r)))` THEN
    UNDISCH_TAC `y IN IMAGE (cm_capmap Q) (ball(c:real^2,r'))` THEN
    MP_TAC(ISPECL [`c:real^2`; `r':real`; `r:real`] SUBSET_BALL) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CMR_REPN_MIN THEN
  MAP_EVERY EXISTS_TAC [`e:real`; `Lam:real`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `k = 1` SUBST1_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* The energy of a map on S^2 and on the open caps of a disjoint family,   *)
(* computed in the charts of the caps.                                      *)

let CMR_SEN_FAM_SUM = prove
 (`!(G:real^K->real^K^K) Lam (f:real^3->real^K) n Q (c:num->real^2) r.
     CMR_GCOND G Lam /\ wan_s2_w12 f /\ cmr_dfam n Q c r
     ==> cm_sen G f =
         sum(1..n) (\k. cm_gen G (ball(c k,r k)) (\x. f(cm_capmap (Q k) x))) +
         cmr_sen_on G f (sphere(vec 0,&1) DIFF cmr_fcl n Q c r) /\
         cmr_sen_on G f (cmr_fop n Q c r) =
         sum(1..n) (\k. cm_gen G (ball(c k,r k)) (\x. f(cm_capmap (Q k) x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!k. 1 <= k /\ k <= n ==> orthogonal_matrix((Q:num->real^3^3) k)`
  ASSUME_TAC THENL [ASM_MESON_TAC[cmr_dfam]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. 1 <= k /\ k <= n
        ==> cmr_sen_on G (f:real^3->real^K)
              (IMAGE (cm_capmap ((Q:num->real^3^3) k)) (ball((c:num->real^2) k,r k))) =
            cm_gen G (ball(c k,r k)) (\x. f(cm_capmap (Q k) x))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[cm_gen] THEN MATCH_MP_TAC CMR_CAP_EN THEN
    EXISTS_TAC `Lam:real` THEN ASM_SIMP_TAC[OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. 1 <= k /\ k <= n
        ==> IMAGE (cm_capmap ((Q:num->real^3^3) k)) (ball((c:num->real^2) k,r k)) SUBSET
            cmr_fop n Q c r /\
            IMAGE (cm_capmap (Q k)) (ball(c k,r k)) SUBSET sphere(vec 0,&1)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[cmr_fop; SUBSET; IN_ELIM_THM] THENL
     [ASM_MESON_TAC[]; REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_MESON_TAC[CMR_CAPMAP_FACTS]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ASSUME `CMR_GCOND (G:real^K->real^K^K) Lam`) THEN
    REWRITE_TAC[CMR_GCOND] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`G:real^K->real^K^K`; `f:real^3->real^K`; `Lam:real`] CMR_SEN_DENS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
    MP_TAC(ISPECL [`G:real^K->real^K^K`; `Lam:real`; `f:real^3->real^K`; `n:num`;
                   `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`;
                   `sphere(vec 0:real^3,&1)`] CMR_SEN_ON_FAM_SPLIT) THEN
    ASM_REWRITE_TAC[OPEN_IN_REFL] THEN DISCH_THEN SUBST1_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM(MATCH_MP th (CONJ
      (ASSUME `1 <= (k:num)`) (ASSUME `(k:num) <= n`)))]) THEN
    AP_TERM_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `Lam:real`; `f:real^3->real^K`; `n:num`;
                 `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`;
                 `cmr_fop n Q (c:num->real^2) r`] CMR_SEN_ON_FAM_SPLIT) THEN
  ASM_SIMP_TAC[CMR_FOP_OPEN_IN] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MATCH_MP (SET_RULE `s SUBSET t ==> s DIFF t = ({}:real^3->bool)`)
                (SPEC_ALL CMR_FOP_SUBSET)] THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `f:real^3->real^K`; `Lam:real`] CMR_SEN_ON_BASICS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  REWRITE_TAC[REAL_ADD_RID] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM(MATCH_MP th (CONJ
    (ASSUME `1 <= (k:num)`) (ASSUME `(k:num) <= n`)))]) THEN
  AP_TERM_TAC THEN ASM SET_TAC[]);;

(* The energy on any part of S^2 is at most the total energy.             *)

let CMR_SEN_ON_LE_SEN = prove
 (`!(G:real^K->real^K^K) (u:real^3->real^K) Lam E.
     CMR_GCOND G Lam /\ wan_s2_w12 u /\ lebesgue_measurable(cmr_cone E)
     ==> cmr_sen_on G u E <= cm_sen G u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CMR_GCOND] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`; `Lam:real`] CMR_SEN_DENS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  REWRITE_TAC[cmr_sen_on] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> a / &3 <= b / &3`) THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`; `Lam:real`; `cmr_cone E`]
                CMR_DENS_FACTS) THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`; `Lam:real`; `wan_shell`]
                CMR_DENS_FACTS) THEN
  ASM_SIMP_TAC[CMR_CONE_SETOPS; SUBSET_REFL; LEBESGUE_MEASURABLE_OPEN; CMT_SHELL_OPEN] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
  ASM_SIMP_TAC[CMR_CONE_SETOPS; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; LIFT_DROP]);;

(* The zero map has zero energy for the identity metric.                    *)

let CMR_SEN_ON_ZERO = prove
 (`!E. lebesgue_measurable(cmr_cone E)
       ==> cmr_sen_on (\y:real^K. mat 1) (\y:real^3. vec 0:real^K) E = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `wan_s2_w12 (\y:real^3. vec 0:real^K)` ASSUME_TAC THENL
   [REWRITE_TAC[wan_s2_w12; wan_rext; WAN_W12_ZERO]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\y:real^K. mat 1:real^K^K`; `\y:real^3. vec 0:real^K`; `&1`]
                CMR_SEN_ON_BASICS) THEN
  ASM_REWRITE_TAC[CMR_GCOND_ID] THEN STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &0 ==> x = &0`) THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `cm_sen (\y:real^K. mat 1) (\y:real^3. vec 0:real^K)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CMR_SEN_ON_LE_SEN THEN EXISTS_TAC `&1` THEN
    ASM_REWRITE_TAC[CMR_GCOND_ID];
    REWRITE_TAC[cm_sen; WAN_GDIR_ID; wan_rext] THEN
    MATCH_MP_TAC(REAL_ARITH `x = &0 ==> x / &3 <= &0`) THEN
    MATCH_MP_TAC CMR_DIR_ZERO_ON THEN REWRITE_TAC[CMT_SHELL_OPEN]]);;

let CMR_CM_GEN_EMPTY = prove
 (`!(G:real^K->real^K^K) (f:real^2->real^K). cm_gen G {} f = &0`,
  REWRITE_TAC[cm_gen; wan_gdir; INTEGRAL_EMPTY; DROP_VEC; SUM_0] THEN REAL_ARITH_TAC);;

(* The energy of the replaced map on an open set is at most the energy of u *)
(* there plus the energy of u on the caps.                                  *)

let CMR_REPN_SEN_ON_LE = prove
 (`!S (G:real^K->real^K^K) e Lam n Q (c:num->real^2) r (u:real^3->real^K) W.
     cmw_repex S G e /\ CMR_GCOND G Lam /\ cm_smap S u /\ cmr_dfam n Q c r /\
     (!k. 1 <= k /\ k <= n /\ &0 < r k
          ==> wan_gdir (ball(c k,r k)) G (\x. u(cm_capmap (Q k) x)) <= e) /\
     open_in (subtopology euclidean (sphere(vec 0,&1))) W
     ==> cmr_sen_on G (cmr_repn S G n Q c r u) W <=
         cmr_sen_on G u W +
         sum(1..n) (\k. cm_gen G (ball(c k,r k)) (\x. u(cm_capmap (Q k) x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!k. 1 <= k /\ k <= n ==> orthogonal_matrix((Q:num->real^3^3) k)`
  ASSUME_TAC THENL [ASM_MESON_TAC[cmr_dfam]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n:num`;
                 `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`; `u:real^3->real^K`]
                CMR_REPN_FACTS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[cmr_dfam]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[LE_REFL] THEN
  ABBREV_TAC `h = cmr_repn S G n Q (c:num->real^2) r (u:real^3->real^K)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `wan_s2_w12 (h:real^3->real^K) /\ wan_s2_w12 (u:real^3->real^K)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[cm_smap]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `Lam:real`; `h:real^3->real^K`; `n:num`;
                 `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`; `W:real^3->bool`]
                CMR_SEN_ON_FAM_SPLIT) THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `Lam:real`; `u:real^3->real^K`; `n:num`;
                 `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`; `W:real^3->bool`]
                CMR_SEN_ON_FAM_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean (sphere(vec 0:real^3,&1)))
      (W DIFF cmr_fcl n Q (c:num->real^2) r)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `W DIFF cmr_fcl n Q (c:num->real^2) r =
                  W DIFF (sphere(vec 0:real^3,&1) INTER cmr_fcl n Q c r)`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN REWRITE_TAC[CMR_FCL_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cmr_sen_on G (h:real^3->real^K) (W DIFF cmr_fcl n Q (c:num->real^2) r) =
    cmr_sen_on G (u:real^3->real^K) (W DIFF cmr_fcl n Q c r)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CMR_SEN_ON_EQ_OPEN THEN
    EXISTS_TAC `W DIFF cmr_fcl n Q (c:num->real^2) r` THEN
    ASM_SIMP_TAC[SUBSET_REFL; CMR_CONE_OPEN] THEN
    X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `~(y IN cmr_fcl n Q (c:num->real^2) r)` THEN
    MP_TAC(SPEC_ALL CMR_FOP_SUBSET) THEN
    REWRITE_TAC[cmr_fop; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`; `Lam:real`] CMR_SEN_ON_BASICS) THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `h:real^3->real^K`; `Lam:real`] CMR_SEN_ON_BASICS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `a <= c /\ &0 <= b ==> a + x <= (b + x) + c`) THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC LEBESGUE_MEASURABLE_OPEN THEN
    MATCH_MP_TAC CMR_CONE_OPEN THEN MATCH_MP_TAC OPEN_IN_INTER THEN
    ASM_SIMP_TAC[CMR_CAP_OPEN_IN; OPEN_BALL]] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `orthogonal_matrix((Q:num->real^3^3) k)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `&0 < (r:num->real) k` THENL
   [ALL_TAC;
    SUBGOAL_THEN `ball((c:num->real^2) k,r k) = {}` SUBST1_TAC THENL
     [REWRITE_TAC[BALL_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; INTER_EMPTY; CMR_CM_GEN_EMPTY; REAL_LE_REFL]] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `cmr_sen_on G (h:real^3->real^K)
                (IMAGE (cm_capmap ((Q:num->real^3^3) k)) (ball((c:num->real^2) k,r k)))` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[INTER_SUBSET] THEN CONJ_TAC THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_OPEN THEN MATCH_MP_TAC CMR_CONE_OPEN THEN
    ASM_SIMP_TAC[CMR_CAP_OPEN_IN; OPEN_BALL; OPEN_IN_INTER];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `h:real^3->real^K`; `(Q:num->real^3^3) k`; `Lam:real`;
                 `ball((c:num->real^2) k,r k)`] CMR_CAP_EN) THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `wan_gdir (ball((c:num->real^2) k,r k)) G (\y. (h:real^3->real^K)(cm_capmap (Q k) y)) =
    wan_gdir (ball(c k,r k)) G (cmr_minw S G (c k) (r k) (\x. u(cm_capmap (Q k) x)))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CMT_WAN_GDIR_EQ THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM cm_gen] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `(Q:num->real^3^3) k`;
                 `(c:num->real^2) k`; `(r:num->real) k`; `u:real^3->real^K`; `Lam:real`]
                CMR_REP1_SEN_LE) THEN
  ASM_SIMP_TAC[]);;

(* The S^2 Dirichlet energy of the change made by replacement is bounded by *)
(* the energy decrease (convexity on each cap).                             *)

let CMR_REPN_DIR_CHANGE = prove
 (`!S (G:real^K->real^K^K) d e ec cc lam Lam n Q (c:num->real^2) r (u:real^3->real^K).
     cm_target S G d /\ cmw_repex S G e /\ e <= ec /\ &0 < lam /\
     (!z v. lam * norm v pow 2 <= v dot (G z ** v)) /\
     (!z v. &0 <= v dot (G z ** v) /\ v dot (G z ** v) <= Lam * norm v pow 2) /\
     (!(a:real^2) r (u:real^2->real^K) v.
        &0 < r /\ cm_harmonic S G (ball(a,r)) v /\ cm_wmap S (ball(a,r)) v /\
        wan_gdir (ball(a,r)) G v <= ec /\ cm_wmap S (ball(a,r)) u /\
        wan_w120 (ball(a,r)) (\x. u x - v x)
        ==> cc * wan_dir (ball(a,r)) (\x. u x - v x)
            <= wan_gdir (ball(a,r)) G u - wan_gdir (ball(a,r)) G v) /\
     cm_smap S u /\ cmr_dfam n Q c r /\
     (!k. 1 <= k /\ k <= n /\ &0 < r k
          ==> wan_gdir (ball(c k,r k)) G (\x. u(cm_capmap (Q k) x)) <= e)
     ==> cc * cm_sen (\y:real^K. mat 1) (\y. cmr_repn S G n Q c r u y - u y)
         <= cm_sen G u - cm_sen G (cmr_repn S G n Q c r u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `CMR_GCOND (G:real^K->real^K^K) Lam` ASSUME_TAC THENL
   [ASM_MESON_TAC[CMR_TARGET_GCOND; CMR_GCOND]; ALL_TAC] THEN
  SUBGOAL_THEN `!k. 1 <= k /\ k <= n ==> orthogonal_matrix((Q:num->real^3^3) k)`
  ASSUME_TAC THENL [ASM_MESON_TAC[cmr_dfam]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n:num`;
                 `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`; `u:real^3->real^K`]
                CMR_REPN_FACTS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[cmr_dfam]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[LE_REFL] THEN
  ABBREV_TAC `h = cmr_repn S G n Q (c:num->real^2) r (u:real^3->real^K)` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[REAL_ARITH `u - (u - s) = s:real`] THEN
  SUBGOAL_THEN `wan_s2_w12 (\y. (h:real^3->real^K) y - u y)` ASSUME_TAC THENL
   [MATCH_MP_TAC CMR_S2_W12_SUB THEN ASM_MESON_TAC[cm_smap]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\y:real^K. mat 1:real^K^K`; `&1`; `\y. (h:real^3->real^K) y - u y`;
                 `n:num`; `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`]
                CMR_SEN_FAM_SUM) THEN
  ASM_REWRITE_TAC[CMR_GCOND_ID] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN
   `cmr_sen_on (\y:real^K. mat 1) (\y. (h:real^3->real^K) y - u y)
      (sphere(vec 0,&1) DIFF cmr_fcl n Q (c:num->real^2) r) = &0`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `cmr_sen_on (\y:real^K. mat 1) (\y:real^3. vec 0:real^K)
                  (sphere(vec 0,&1) DIFF cmr_fcl n Q (c:num->real^2) r)` THEN
    SUBGOAL_THEN `open(cmr_cone (sphere(vec 0:real^3,&1) DIFF cmr_fcl n Q (c:num->real^2) r))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC CMR_CONE_OPEN THEN MATCH_MP_TAC OPEN_IN_DIFF_CLOSED THEN
      REWRITE_TAC[CMR_FCL_CLOSED];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CMR_SEN_ON_EQ_OPEN THEN
      EXISTS_TAC `sphere(vec 0:real^3,&1) DIFF cmr_fcl n Q (c:num->real^2) r` THEN
      ASM_REWRITE_TAC[SUBSET_REFL] THEN CONJ_TAC THENL
       [REWRITE_TAC[wan_s2_w12; wan_rext; WAN_W12_ZERO]; ALL_TAC] THEN
      X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
      REWRITE_TAC[VECTOR_SUB_EQ] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `~(y IN cmr_fcl n Q (c:num->real^2) r)` THEN
      MP_TAC(SPEC_ALL CMR_FOP_SUBSET) THEN
      REWRITE_TAC[cmr_fop; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
      MATCH_MP_TAC CMR_SEN_ON_ZERO THEN ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_RID; GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  ASM_CASES_TAC `&0 < (r:num->real) k` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    SUBGOAL_THEN `ball((c:num->real^2) k,r k) = {}` SUBST1_TAC THENL
     [REWRITE_TAC[BALL_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[CMR_CM_GEN_EMPTY; REAL_MUL_RZERO; REAL_LE_REFL]] THEN
  SUBGOAL_THEN `orthogonal_matrix((Q:num->real^3^3) k)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `cm_gen (\y:real^K. mat 1) (ball((c:num->real^2) k,r k))
      (\x. (h:real^3->real^K)(cm_capmap ((Q:num->real^3^3) k) x) - u(cm_capmap (Q k) x)) =
    cmr_stab_df S G (Q k) (c k) (r k) u / &2`
  SUBST1_TAC THENL
   [REWRITE_TAC[cmr_stab_df; cm_gen; WAN_GDIR_ID] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `(c:num->real^2) k`;
                   `(r:num->real) k`;
                   `\x. (u:real^3->real^K)(cm_capmap ((Q:num->real^3^3) k) x)`]
                  CMR_MINW_WORKS) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN MATCH_MP_TAC CMR_CHART_CMAP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `wan_dir (ball((c:num->real^2) k,r k))
                  (\x. cmr_minw S G (c k) (r k) (\x. (u:real^3->real^K)(cm_capmap (Q k) x)) x -
                       u(cm_capmap (Q k) x))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CMW_DIR_EQ_ON THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC CMW_DIR_SUB_SYM THEN REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`S:real^K->bool`; `u:real^3->real^K`; `(Q:num->real^3^3) k`;
                       `(c:num->real^2) k`; `(r:num->real) k`] CMR_CHART_CMAP) THEN
        ASM_SIMP_TAC[cm_cmap];
        UNDISCH_TAC `cm_cmap S (ball((c:num->real^2) k,r k))
                       (cmr_minw S G (c k) (r k)
                          (\x. (u:real^3->real^K)(cm_capmap ((Q:num->real^3^3) k) x)))` THEN
        SIMP_TAC[cm_cmap; ETA_AX]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`; `ec:real`;
                 `cc:real`; `lam:real`; `Lam:real`; `(Q:num->real^3^3) k`;
                 `(c:num->real^2) k`; `(r:num->real) k`; `u:real^3->real^K`]
                CMR_STAB_TERMS) THEN
  ASM_SIMP_TAC[] THEN REAL_ARITH_TAC);;


(* ========================================================================= *)
(* A circle in an open cap.  If the image of a planar circle                 *)
(* under a chart lies in an open cap, then the cap contains the closed disc *)
(* or the cap and the open disc cover S^2 (the complement of an open cap is *)
(* connected and misses the circle).  Consequence: a circle around a disc   *)
(* that lies in no open cap of a disjoint family meets the complement of    *)
(* the family's open caps, unless one cap and the open disc cover S^2.      *)
(* ========================================================================= *)

let CMR_OPEN_IN_SUBSET_INTER = prove
 (`!u v s:real^N->bool.
     open_in (subtopology euclidean u) s /\ v SUBSET u
     ==> open_in (subtopology euclidean v) (v INTER s)`,
  REWRITE_TAC[OPEN_IN_OPEN] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* Distance of a chart point from the pole of the chart.                    *)

let CMR_CAPMAP_POLE_DIST = prove
 (`!(Q:real^3^3) (y:real^2).
     orthogonal_matrix Q
     ==> norm(cm_capmap Q y - Q ** basis 3) pow 2 = &4 / (norm y pow 2 + &1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cm_capmap; GSYM MATRIX_VECTOR_MUL_SUB_LDISTRIB] THEN
  ASM_SIMP_TAC[ORTHOGONAL_MATRIX_NORM] THEN
  SIMP_TAC[NORM_POW_2; DOT_3; DOT_2; VECTOR_SUB_COMPONENT; STEX_STEREO2_N_INV_COMPONENTS;
           BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
  SUBGOAL_THEN `&0 < (y:real^2)$1 * y$1 + y$2 * y$2 + &1` MP_TAC THENL
   [MP_TAC(SPEC `(y:real^2)$1` REAL_LE_SQUARE) THEN MP_TAC(SPEC `(y:real^2)$2` REAL_LE_SQUARE) THEN
    REAL_ARITH_TAC;
    CONV_TAC REAL_FIELD]);;

(* The pole is a limit of chart points outside any disc.                    *)

let CMR_POLE_IN_CLOSURE = prove
 (`!(Q:real^3^3) (c:real^2) r.
     orthogonal_matrix Q
     ==> Q ** basis 3 IN closure(IMAGE (cm_capmap Q) ((:real^2) DIFF ball(c,r)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  ABBREV_TAC `t = norm(c:real^2) + abs r + &2 / e + &1` THEN
  SUBGOAL_THEN `&2 / e < t /\ norm(c:real^2) + abs r < t` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN
    SUBGOAL_THEN `&0 < &2 / e` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPEC `c:real^2` NORM_POS_LE) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(t % basis 1:real^2) = t` ASSUME_TAC THENL
   [SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_2; ARITH; REAL_MUL_RID] THEN
    MP_TAC(ISPEC `c:real^2` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `cm_capmap Q (t % basis 1:real^2)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_DIFF; IN_UNIV; IN_BALL; dist] THEN
    MP_TAC(ISPECL [`t % basis 1:real^2`; `c:real^2`] NORM_TRIANGLE_SUB) THEN
    MP_TAC(ISPECL [`c:real^2`; `t % basis 1:real^2`] NORM_SUB) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[dist] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(e <= x) ==> x < e`) THEN
  REWRITE_TAC[NORM_POS_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `e pow 2 <= norm(cm_capmap Q (t % basis 1:real^2) - Q ** basis 3) pow 2`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[CMR_CAPMAP_POLE_DIST] THEN
  SUBGOAL_THEN `&0 < t pow 2 + &1` ASSUME_TAC THENL
   [MP_TAC(SPEC `t:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_NOT_LE; REAL_LT_LDIV_EQ] THEN
  SUBGOAL_THEN `&2 < e * t` MP_TAC THENL
   [SUBGOAL_THEN `e * &2 / e < e * t` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&2 pow 2 < (e * t) pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `e:real` REAL_LE_POW_2) THEN
  REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC);;

(* The complement of an open cap is the image of the complement of the     *)
(* disc together with the pole; it is connected.                            *)

let CMR_CAP_COMPLEMENT = prove
 (`!(Q:real^3^3) (c:real^2) r.
     orthogonal_matrix Q
     ==> sphere(vec 0,&1) DIFF IMAGE (cm_capmap Q) (ball(c,r)) =
         IMAGE (cm_capmap Q) ((:real^2) DIFF ball(c,r)) UNION {Q ** basis 3}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `Q:real^3^3` CMR_CAPMAP_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(Q:real^3^3) ** basis 3 IN sphere(vec 0:real^3,&1)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_SPHERE_0] THEN ASM_SIMP_TAC[ORTHOGONAL_MATRIX_NORM] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNION; IN_SING; IN_IMAGE; IN_UNIV] THEN
  X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
   [STRIP_TAC THEN ASM_CASES_TAC `y = (Q:real^3^3) ** basis 3` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `cmr_chart Q (y:real^3)` THEN ASM_SIMP_TAC[] THEN
    DISCH_TAC THEN UNDISCH_TAC `~(?x. y = cm_capmap Q x /\ x IN ball(c:real^2,r))` THEN
    REWRITE_TAC[] THEN EXISTS_TAC `cmr_chart Q (y:real^3)` THEN ASM_SIMP_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    TRY(DISCH_THEN(X_CHOOSE_THEN `x':real^2` STRIP_ASSUME_TAC)) THEN
    ASM_MESON_TAC[]]);;

let CMR_CAP_COMPLEMENT_CONNECTED = prove
 (`!(Q:real^3^3) (c:real^2) r.
     orthogonal_matrix Q
     ==> connected(sphere(vec 0,&1) DIFF IMAGE (cm_capmap Q) (ball(c,r)))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CMR_CAP_COMPLEMENT] THEN
  MATCH_MP_TAC CONNECTED_INTERMEDIATE_CLOSURE THEN
  EXISTS_TAC `IMAGE (cm_capmap Q) ((:real^2) DIFF ball(c,r))` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; CMR_CAPMAP_SMOOTH; SUBSET_UNIV];
      MATCH_MP_TAC CONNECTED_COMPLEMENT_BOUNDED_CONVEX THEN
      REWRITE_TAC[BOUNDED_BALL; CONVEX_BALL; DIMINDEX_2; LE_REFL]];
    SET_TAC[];
    REWRITE_TAC[UNION_SUBSET; CLOSURE_SUBSET; SING_SUBSET] THEN
    MATCH_MP_TAC CMR_POLE_IN_CLOSURE THEN ASM_REWRITE_TAC[]]);;

(* A circle in an open cap.                                                 *)

let CMR_CIRCLE_IN_CAP = prove
 (`!(Qa:real^3^3) (ca:real^2) ra (Qj:real^3^3) (cj:real^2) rho.
     orthogonal_matrix Qa /\ orthogonal_matrix Qj /\ &0 < rho /\
     IMAGE (cm_capmap Qj) (sphere(cj,rho)) SUBSET IMAGE (cm_capmap Qa) (ball(ca,ra))
     ==> IMAGE (cm_capmap Qj) (cball(cj,rho)) SUBSET IMAGE (cm_capmap Qa) (ball(ca,ra)) \/
         sphere(vec 0,&1) SUBSET
         IMAGE (cm_capmap Qa) (ball(ca,ra)) UNION IMAGE (cm_capmap Qj) (ball(cj,rho))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Qa:real^3^3`; `ca:real^2`; `ra:real`] CMR_CAP_COMPLEMENT_CONNECTED) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `A = IMAGE (cm_capmap Qa) (ball(ca:real^2,ra))` THEN
  ABBREV_TAC `D = IMAGE (cm_capmap Qj) (ball(cj:real^2,rho))` THEN
  ABBREV_TAC `Dc = IMAGE (cm_capmap Qj) (cball(cj:real^2,rho))` THEN
  ABBREV_TAC `Ci = IMAGE (cm_capmap Qj) (sphere(cj:real^2,rho))` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `Dc:real^3->bool = D UNION Ci` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Dc"; "D"; "Ci"] THEN
    REWRITE_TAC[GSYM IMAGE_UNION; BALL_UNION_SPHERE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean (sphere(vec 0:real^3,&1))) D /\
    open_in (subtopology euclidean (sphere(vec 0:real^3,&1))) (sphere(vec 0,&1) DIFF Dc)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "D" THEN MATCH_MP_TAC CMR_CAP_OPEN_IN THEN ASM_REWRITE_TAC[OPEN_BALL];
      MATCH_MP_TAC OPEN_IN_DIFF_CLOSED THEN EXPAND_TAC "Dc" THEN
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      REWRITE_TAC[COMPACT_CBALL] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `(:real^2)` THEN
      SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; CMR_CAPMAP_SMOOTH; SUBSET_UNIV]];
    ALL_TAC] THEN
  SUBGOAL_THEN `Dc SUBSET sphere(vec 0:real^3,&1)` ASSUME_TAC THENL
   [EXPAND_TAC "Dc" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[CMR_CAPMAP_FACTS];
    ALL_TAC] THEN
  ASM_CASES_TAC `Dc SUBSET (A:real^3->bool)` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~(Dc SUBSET (A:real^3->bool))` THEN
  REWRITE_TAC[SUBSET; NOT_FORALL_THM; NOT_IMP] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[SUBSET; IN_UNION] THEN X_GEN_TAC `q:real^3` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(q:real^3) IN A` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(q:real^3) IN D` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `connected(sphere(vec 0:real^3,&1) DIFF A)` THEN
  REWRITE_TAC[CONNECTED_OPEN_IN] THEN
  MAP_EVERY EXISTS_TAC [`(sphere(vec 0:real^3,&1) DIFF A) INTER D`;
                        `(sphere(vec 0:real^3,&1) DIFF A) INTER (sphere(vec 0,&1) DIFF Dc)`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CMR_OPEN_IN_SUBSET_INTER THEN
    EXISTS_TAC `sphere(vec 0:real^3,&1)` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    MATCH_MP_TAC CMR_OPEN_IN_SUBSET_INTER THEN
    EXISTS_TAC `sphere(vec 0:real^3,&1)` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    UNDISCH_TAC `(Ci:real^3->bool) SUBSET A` THEN
    UNDISCH_TAC `Dc:real^3->bool = D UNION Ci` THEN SET_TAC[];
    UNDISCH_TAC `Dc:real^3->bool = D UNION Ci` THEN SET_TAC[];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `p:real^3` THEN
    UNDISCH_TAC `(Ci:real^3->bool) SUBSET A` THEN
    UNDISCH_TAC `Dc:real^3->bool = D UNION Ci` THEN
    UNDISCH_TAC `Dc SUBSET sphere(vec 0:real^3,&1)` THEN ASM SET_TAC[];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `q:real^3` THEN
    UNDISCH_TAC `(Ci:real^3->bool) SUBSET A` THEN
    UNDISCH_TAC `Dc:real^3->bool = D UNION Ci` THEN ASM SET_TAC[]]);;

(* A circle around a disc that lies in no open cap of a disjoint family     *)
(* meets the complement of the family's open caps, unless one cap and the   *)
(* open disc cover S^2.                                                     *)

let CMR_CIRCLE_MEETS_OFF = prove
 (`!n (Q:num->real^3^3) (c:num->real^2) r (Qj:real^3^3) (cj:real^2) s rho.
     cmr_dfam n Q c r /\ orthogonal_matrix Qj /\ &0 < s /\ s <= rho /\
     (!k. 1 <= k /\ k <= n /\ &0 < r k
          ==> ~(IMAGE (cm_capmap Qj) (cball(cj,s)) SUBSET
                IMAGE (cm_capmap (Q k)) (ball(c k,r k))) /\
              ~(sphere(vec 0,&1) SUBSET
                IMAGE (cm_capmap (Q k)) (ball(c k,r k)) UNION
                IMAGE (cm_capmap Qj) (ball(cj,rho))))
     ==> ?y. y IN IMAGE (cm_capmap Qj) (sphere(cj,rho)) /\ ~(y IN cmr_fop n Q c r)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "H"))))) THEN
  SUBGOAL_THEN `!k. 1 <= k /\ k <= n ==> orthogonal_matrix((Q:num->real^3^3) k)`
  ASSUME_TAC THENL [ASM_MESON_TAC[cmr_dfam]; ALL_TAC] THEN
  ABBREV_TAC `Ci = IMAGE (cm_capmap Qj) (sphere(cj:real^2,rho))` THEN
  REWRITE_TAC[SET_RULE `(?y. y IN s /\ ~(y IN t)) <=> ~(s SUBSET (t:real^3->bool))`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `connected(Ci:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Ci" THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; CMR_CAPMAP_SMOOTH; SUBSET_UNIV];
      MATCH_MP_TAC CONNECTED_SPHERE THEN REWRITE_TAC[DIMINDEX_2; LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?y0:real^3. y0 IN Ci` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Ci" THEN
    EXISTS_TAC `cm_capmap Qj (cj + rho % basis 1:real^2)` THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[IN_SPHERE; NORM_ARITH `dist(a:real^2,a + b) = norm b`] THEN
    SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_2; ARITH] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(y0:real^3) IN cmr_fop n Q (c:num->real^2) r` MP_TAC THENL
   [UNDISCH_TAC `(Ci:real^3->bool) SUBSET cmr_fop n Q (c:num->real^2) r` THEN
    UNDISCH_TAC `(y0:real^3) IN Ci` THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[cmr_fop; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < (r:num->real) k0` ASSUME_TAC THENL
   [UNDISCH_TAC `y0 IN IMAGE (cm_capmap ((Q:num->real^3^3) k0)) (ball((c:num->real^2) k0,r k0))` THEN
    REWRITE_TAC[IN_IMAGE; IN_BALL] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(c:num->real^2) k0`; `x:real^2`] DIST_POS_LE) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `A0 = IMAGE (cm_capmap ((Q:num->real^3^3) k0)) (ball((c:num->real^2) k0,r k0))` THEN
  ABBREV_TAC `Ac0 = IMAGE (cm_capmap ((Q:num->real^3^3) k0)) (cball((c:num->real^2) k0,r k0))` THEN
  SUBGOAL_THEN `(A0:real^3->bool) SUBSET Ac0` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A0"; "Ac0"] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Ci:real^3->bool) SUBSET A0` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `Ci SUBSET A0 UNION (cmr_fop n Q (c:num->real^2) r DIFF (Ac0:real^3->bool))`
    ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNION; IN_DIFF] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(y:real^3) IN cmr_fop n Q (c:num->real^2) r` ASSUME_TAC THENL
       [UNDISCH_TAC `(Ci:real^3->bool) SUBSET cmr_fop n Q (c:num->real^2) r` THEN
        UNDISCH_TAC `(y:real^3) IN Ci` THEN SET_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y:real^3) IN cmr_fop n Q (c:num->real^2) r` THEN
      REWRITE_TAC[cmr_fop; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
      ASM_CASES_TAC `k:num = k0` THENL
       [UNDISCH_TAC `y IN IMAGE (cm_capmap ((Q:num->real^3^3) k)) (ball((c:num->real^2) k,r k))` THEN
        ASM_REWRITE_TAC[] THEN SIMP_TAC[];
        ALL_TAC] THEN
      DISJ2_TAC THEN
      SUBGOAL_THEN `&0 < (r:num->real) k` ASSUME_TAC THENL
       [UNDISCH_TAC `y IN IMAGE (cm_capmap ((Q:num->real^3^3) k)) (ball((c:num->real^2) k,r k))` THEN
        REWRITE_TAC[IN_IMAGE; IN_BALL] THEN STRIP_TAC THEN
        MP_TAC(ISPECL [`(c:num->real^2) k`; `x:real^2`] DIST_POS_LE) THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `DISJOINT (IMAGE (cm_capmap ((Q:num->real^3^3) k)) (cball((c:num->real^2) k,r k)))
                 (Ac0:real^3->bool)`
      MP_TAC THENL
       [EXPAND_TAC "Ac0" THEN
        FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE `~(k:num = k0) ==> k < k0 \/ k0 < k`)) THENL
         [UNDISCH_TAC `cmr_dfam n Q (c:num->real^2) r` THEN REWRITE_TAC[cmr_dfam] THEN
          DISCH_THEN(MP_TAC o SPECL [`k:num`; `k0:num`] o CONJUNCT2) THEN
          ASM_REWRITE_TAC[];
          UNDISCH_TAC `cmr_dfam n Q (c:num->real^2) r` THEN REWRITE_TAC[cmr_dfam] THEN
          DISCH_THEN(MP_TAC o SPECL [`k0:num`; `k:num`] o CONJUNCT2) THEN
          ASM_REWRITE_TAC[DISJOINT_SYM]];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `(y:real^3) IN IMAGE (cm_capmap ((Q:num->real^3^3) k)) (cball((c:num->real^2) k,r k))`
      MP_TAC THENL
       [MP_TAC(ISPECL [`(c:num->real^2) k`; `(r:num->real) k`] BALL_SUBSET_CBALL) THEN
        DISCH_THEN(MP_TAC o MATCH_MP (ISPEC `cm_capmap ((Q:num->real^3^3) k)` IMAGE_SUBSET)) THEN
        UNDISCH_TAC `y IN IMAGE (cm_capmap ((Q:num->real^3^3) k)) (ball((c:num->real^2) k,r k))` THEN
        REWRITE_TAC[SUBSET] THEN MESON_TAC[];
        REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN MESON_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `connected(Ci:real^3->bool)` THEN REWRITE_TAC[CONNECTED_OPEN_IN] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`Ci INTER (A0:real^3->bool)`;
                               `Ci INTER (cmr_fop n Q (c:num->real^2) r DIFF Ac0)`]) THEN
    SUBGOAL_THEN `(Ci:real^3->bool) SUBSET sphere(vec 0,&1)` ASSUME_TAC THENL
     [EXPAND_TAC "Ci" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      ASM_MESON_TAC[CMR_CAPMAP_FACTS];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `open_in (subtopology euclidean (sphere(vec 0:real^3,&1))) A0 /\
      open_in (subtopology euclidean (sphere(vec 0:real^3,&1)))
        (cmr_fop n Q (c:num->real^2) r DIFF Ac0)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [EXPAND_TAC "A0" THEN MATCH_MP_TAC CMR_CAP_OPEN_IN THEN ASM_SIMP_TAC[OPEN_BALL];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `cmr_fop n Q (c:num->real^2) r DIFF (Ac0:real^3->bool) =
        cmr_fop n Q c r DIFF (sphere(vec 0,&1) INTER Ac0)`
      SUBST1_TAC THENL
       [MP_TAC(ISPECL [`n:num`; `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`]
                CMR_FAM_IN_SPHERE) THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_SIMP_TAC[CMR_FOP_OPEN_IN] THEN
      MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN EXPAND_TAC "Ac0" THEN
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      REWRITE_TAC[COMPACT_CBALL] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `(:real^2)` THEN
      SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; CMR_CAPMAP_SMOOTH; SUBSET_UNIV];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `a /\ b /\ c /\ d /\ e /\ (g ==> f)
                       ==> ~(a /\ b /\ c /\ d /\ e /\ ~g) ==> f`) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CMR_OPEN_IN_SUBSET_INTER THEN
      EXISTS_TAC `sphere(vec 0:real^3,&1)` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CMR_OPEN_IN_SUBSET_INTER THEN
      EXISTS_TAC `sphere(vec 0:real^3,&1)` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC
       `Ci SUBSET A0 UNION (cmr_fop n Q (c:num->real^2) r DIFF (Ac0:real^3->bool))` THEN
      SET_TAC[];
      UNDISCH_TAC `(A0:real^3->bool) SUBSET Ac0` THEN SET_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `y0:real^3` THEN
      ASM_REWRITE_TAC[IN_INTER];
      UNDISCH_TAC
       `Ci SUBSET A0 UNION (cmr_fop n Q (c:num->real^2) r DIFF (Ac0:real^3->bool))` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(Q:num->real^3^3) k0`; `(c:num->real^2) k0`; `(r:num->real) k0`;
                 `Qj:real^3^3`; `cj:real^2`; `rho:real`] CMR_CIRCLE_IN_CAP) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "H" (MP_TAC o SPEC `k0:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`cj:real^2`; `s:real`; `rho:real`] SUBSET_CBALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ISPEC `cm_capmap Qj` IMAGE_SUBSET)) THEN
  SET_TAC[]);;

(* If two open caps cover S^2, the energy is at most the sum of the two cap *)
(* energies.                                                                *)

let CMR_TWO_CAPS_COVER = prove
 (`!(G:real^K->real^K^K) Lam (u:real^3->real^K) (Qa:real^3^3) (ca:real^2) ra
    (Qj:real^3^3) (cj:real^2) rho.
     CMR_GCOND G Lam /\ wan_s2_w12 u /\ orthogonal_matrix Qa /\ orthogonal_matrix Qj /\
     sphere(vec 0,&1) SUBSET
     IMAGE (cm_capmap Qa) (ball(ca,ra)) UNION IMAGE (cm_capmap Qj) (ball(cj,rho))
     ==> cm_sen G u <= cm_gen G (ball(ca,ra)) (\x. u(cm_capmap Qa x)) +
                       cm_gen G (ball(cj,rho)) (\x. u(cm_capmap Qj x))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `A = IMAGE (cm_capmap Qa) (ball(ca:real^2,ra))` THEN
  ABBREV_TAC `D = IMAGE (cm_capmap Qj) (ball(cj:real^2,rho))` THEN
  SUBGOAL_THEN `open(cmr_cone A) /\ open(cmr_cone D)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CMR_CONE_OPEN THEN MAP_EVERY EXPAND_TAC ["A"; "D"] THEN
    MATCH_MP_TAC CMR_CAP_OPEN_IN THEN ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `cmr_sen_on G (u:real^3->real^K) A = cm_gen G (ball(ca,ra)) (\x. u(cm_capmap Qa x)) /\
                cmr_sen_on G u D = cm_gen G (ball(cj,rho)) (\x. u(cm_capmap Qj x))`
  (CONJUNCTS_THEN (SUBST1_TAC o SYM)) THENL
   [REWRITE_TAC[cm_gen] THEN MAP_EVERY EXPAND_TAC ["A"; "D"] THEN
    CONJ_TAC THEN MATCH_MP_TAC CMR_CAP_EN THEN EXISTS_TAC `Lam:real` THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  MP_TAC(ASSUME `CMR_GCOND (G:real^K->real^K^K) Lam`) THEN
  REWRITE_TAC[CMR_GCOND] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`; `Lam:real`] CMR_SEN_DENS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN `sphere(vec 0:real^3,&1) = A UNION (D DIFF A)` SUBST1_TAC THENL
   [SUBGOAL_THEN `(A:real^3->bool) SUBSET sphere(vec 0,&1) /\
                  (D:real^3->bool) SUBSET sphere(vec 0,&1)`
    MP_TAC THENL
     [MAP_EVERY EXPAND_TAC ["A"; "D"] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      ASM_MESON_TAC[CMR_CAPMAP_FACTS];
      UNDISCH_TAC `sphere(vec 0:real^3,&1) SUBSET A UNION D` THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`; `Lam:real`;
                 `A:real^3->bool`; `D DIFF (A:real^3->bool)`] CMR_SEN_ON_UNION) THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; CMR_CONE_SETOPS; LEBESGUE_MEASURABLE_DIFF] THEN
  ANTS_TAC THENL [SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a + b <= a + c`) THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`; `Lam:real`] CMR_SEN_ON_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; CMR_CONE_SETOPS; LEBESGUE_MEASURABLE_DIFF] THEN
  SET_TAC[]);;

