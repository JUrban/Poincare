(* ========================================================================= *)
(* pc_smt_disc: M3, the weak disc theorem (SMT_DISC_STATEMENT, Palais 1960; *)
(* Cerf): two ball charts b, b' of a connected Hausdorff smooth manifold    *)
(* agree on cball(0,3/2) after a compactly supported diffeomorphism Phi and *)
(* an orthogonal map Q of the domain: Phi(b x) = b'(Q x).  Route:           *)
(* (1) homogeneity (Milnor, Topology from the Differentiable Viewpoint,     *)
(*     section 4, Homogeneity Lemma): local pushes x + bump(x) a (S4a) in   *)
(*     ball charts, extended by the identity, move b(0) to b'(0);           *)
(* (2) germ step: Q = U^T for the polar decomposition U P of the derivative *)
(*     of the transition b'^-1 o b at 0, S4b' (SMT_POSDEF_GERM) for P and   *)
(*     SMT_GERM_CUTOFF for the remaining germ tangent to the identity;      *)
(* (3) radial expansion: the time-log(lambda) map of the cut-off radial     *)
(*     field bump(x) x, applied in both charts.                              *)
(*                                                                           *)
(* Diffeomorphisms of R^N: scaling conjugates, local pushes                 *)
(* and radial expansions.                                                    *)
(* ========================================================================= *)

needs "src/pc_smt_pole.ml";;
needs "src/pc_smt_glue.ml";;
needs "src/pc_top_cover.ml";;

prioritize_real();;
type_invention_error := true;;

let SMT_DISC_CONJ_SCALE = prove
 (`!(G:real^N->real^N) G' c.
        diffeomorphism_on (:real^N) (:real^N) G G' /\ &0 < c
        ==> diffeomorphism_on (:real^N) (:real^N)
              (\x. c % G(inv c % x)) (\y. c % G'(inv c % y))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `diffeomorphism_on (:real^N) (:real^N) (\x. inv c % x) (\y. c % y) /\
    diffeomorphism_on (:real^N) (:real^N) (\x. c % x) (\y. inv c % y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMT_LINEAR_INVERSES_DIFFEO THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
    CONJ_TAC THEN MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN REWRITE_TAC[LINEAR_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x:real^N. c % (G:real^N->real^N)(inv c % x)) =
    (\x. c % x) o (G o (\x. inv c % x)) /\
    (\y:real^N. c % (G':real^N->real^N)(inv c % y)) =
    ((\y. c % y) o G') o (\y. inv c % y)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN EXISTS_TAC `(:real^N)` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN EXISTS_TAC `(:real^N)` THEN
  ASM_REWRITE_TAC[]);;

(* Local pushes: a compactly supported diffeomorphism moving 0 to a small a. *)

let SMT_DISC_PUSH = prove
 (`?d. &0 < d /\
       !a:real^N.
         norm a <= d
         ==> ?G G'. diffeomorphism_on (:real^N) (:real^N) G G' /\
                    (!x. &1 <= norm x ==> G x = x) /\ G(vec 0) = a`,
  MP_TAC(INST_TYPE [`:N`,`:N`] SMT_BUMP_LIPSCHITZ) THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `inv(&2 * L)` THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
  MP_TAC(REWRITE_RULE[SMT_PERTURB_ID_STATEMENT] (ISPEC `(:N)` SMT_PERTURB_ID)) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`\(t:real) (x:real^N). smooth_bump (&1 / &2) (&1) x % (a:real^N)`; `&1 / &2`]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[smooth_family; UNIV_PCROSS_UNIV] THEN
      SUBGOAL_THEN `!u:real^N->real^N. smooth_map_on (:real^N) u
                    ==> smooth_map_on (:real^(1,N)finite_sum) (\z. u(sndcart z))`
      (MP_TAC o ISPEC `\y:real^N. smooth_bump (&1 / &2) (&1) y % (a:real^N)`) THENL
       [REPEAT STRIP_TAC THEN
        SUBGOAL_THEN `(\z:real^(1,N)finite_sum. (u:real^N->real^N)(sndcart z)) = u o sndcart`
        SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^N)` THEN
        ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
        MP_TAC(ISPECL [`(:real^(1,N)finite_sum)`; `\x:real^(1,N)finite_sum. x`;
                       `sndcart:real^(1,N)finite_sum->real^N`] SMOOTH_MAP_ON_LINEAR_O) THEN
        REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; LINEAR_SNDCART; o_DEF; ETA_AX];
        ALL_TAC] THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      MP_TAC(ISPECL [`(:real^N)`; `\y:real^N. lift(smooth_bump (&1 / &2) (&1) y)`;
                     `\y:real^N. (a:real^N)`] SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
      REWRITE_TAC[LIFT_DROP; OPEN_UNIV; SMOOTH_MAP_ON_CONST] THEN
      DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC SMOOTH_BUMP_SMOOTH THEN
      REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
      REWRITE_TAC[GSYM VECTOR_SUB_RDISTRIB; NORM_MUL] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(L * norm(x - y:real^N)) * inv(&2 * L)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE];
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < L` THEN
        CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real->real^N->real^N` MP_TAC) THEN
  REWRITE_TAC[diffeo_isotopy] THEN
  DISCH_THEN(MP_TAC o SPEC `&0` o CONJUNCT2 o CONJUNCT2) THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`\x:real^N. x + smooth_bump (&1 / &2) (&1) x % (a:real^N)`;
    `(K:real->real^N->real^N) (&0)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `smooth_bump (&1 / &2) (&1) (x:real^N) = &0` SUBST1_TAC THENL
     [MATCH_MP_TAC SMOOTH_BUMP_0 THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID]];
    SUBGOAL_THEN `smooth_bump (&1 / &2) (&1) (vec 0:real^N) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC SMOOTH_BUMP_1 THEN REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
      REWRITE_TAC[VECTOR_MUL_LID; VECTOR_ADD_LID]]]);;

(* Radial expansions: lambda x on cball(0, 3 / (2 lambda)), the identity    *)
(* outside ball(0, 7/4); the time-log(lambda) map of bump(x) x.             *)

let SMT_DISC_EXP_DERIV = prove
 (`!(x:real^N) s. ((\t. exp(drop t) % x) has_vector_derivative (exp(drop s) % x)) (at s)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[HAS_VECTOR_DERIVATIVE_COMPONENTWISE_AT] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN
  MP_TAC(REAL_DIFF_CONV
   `((\t. exp t * (x:real^N)$i) has_real_derivative f) (atreal (drop s))`) THEN
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; LIFT_DROP; o_DEF] THEN
  REWRITE_TAC[REAL_MUL_LID; REAL_MUL_RID; REAL_MUL_RZERO; REAL_ADD_RID]);;

let SMT_DISC_EXPAND = prove
 (`!lam. &1 <= lam
            ==> ?E E'. diffeomorphism_on (:real^N) (:real^N) E E' /\
                       (!x. &7 / &4 <= norm x ==> E x = x) /\
                       (!x. norm x <= &3 / &2 / lam ==> E x = lam % x)`,
  GEN_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `X = \y:real^N. smooth_bump (&3 / &2) (&13 / &8) y % y` THEN
  SUBGOAL_THEN `smooth_map_on (:real^N) (X:real^N->real^N)` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN
    MP_TAC(ISPECL [`(:real^N)`; `\y:real^N. lift(smooth_bump (&3 / &2) (&13 / &8) y)`;
                   `\y:real^N. y`] SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
    REWRITE_TAC[LIFT_DROP; OPEN_UNIV; SMOOTH_MAP_ON_ID] THEN
    DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC SMOOTH_BUMP_SMOOTH THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `continuously_differentiable 1 (:real^N) (X:real^N->real^N)`
  ASSUME_TAC THENL [ASM_MESON_TAC[smooth_map_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`X:real^N->real^N`; `(:real^N)`; `cball(vec 0:real^N,&13 / &8)`]
    ODE_VF_COMPLETE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_UNIV; COMPACT_CBALL; SUBSET_UNIV; IN_UNIV;
                    IN_CBALL_0; REAL_NOT_LE] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN EXPAND_TAC "X" THEN
    SUBGOAL_THEN `smooth_bump (&3 / &2) (&13 / &8) (y:real^N) = &0` SUBST1_TAC THENL
     [MATCH_MP_TAC SMOOTH_BUMP_0 THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[VECTOR_MUL_LZERO]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIV; IN_CBALL_0; REAL_NOT_LE; UNIV_PCROSS_UNIV] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "max")
    (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "dif")
    (CONJUNCTS_THEN2 (LABEL_TAC "off") (K ALL_TAC))))) THEN
  MAP_EVERY EXISTS_TAC
   [`ode_vf_flow (X:real^N->real^N) (:real^N) (lift(log lam))`;
    `ode_vf_flow (X:real^N->real^N) (:real^N) (--lift(log lam))`] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "dif" (fun th -> REWRITE_TAC[th]);
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN USE_THEN "off" MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < lam /\ &0 <= log lam` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`X:real^N->real^N`; `(:real^N)`; `{t:real^1 | drop t <= log lam}`;
                 `\t:real^1. exp(drop t) % (x:real^N)`; `vec 0:real^1`] ODE_VF_UNIQUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; IN_ELIM_THM; DROP_VEC; IS_INTERVAL_1] THEN
    CONJ_TAC THENL [MESON_TAC[REAL_LE_TRANS]; ALL_TAC] THEN
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
    SUBGOAL_THEN `(X:real^N->real^N)(exp(drop t) % x) = exp(drop t) % x` SUBST1_TAC THENL
     [EXPAND_TAC "X" THEN
      SUBGOAL_THEN `smooth_bump (&3 / &2) (&13 / &8) (exp(drop t) % (x:real^N)) = &1`
      SUBST1_TAC THENL
       [MATCH_MP_TAC SMOOTH_BUMP_1 THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[NORM_MUL; REAL_ABS_EXP] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `lam * &3 / &2 / lam` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE; NORM_POS_LE] THEN
          GEN_REWRITE_TAC RAND_CONV [GSYM(MATCH_MP EXP_LOG (ASSUME `&0 < lam`))] THEN
          ASM_REWRITE_TAC[REAL_EXP_MONO_LE];
          MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < lam` THEN
          CONV_TAC REAL_FIELD];
        REWRITE_TAC[VECTOR_MUL_LID]];
      REWRITE_TAC[SMT_DISC_EXP_DERIV]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `lift(log lam)`) THEN
  REWRITE_TAC[IN_ELIM_THM; LIFT_DROP; REAL_LE_REFL; VECTOR_SUB_RZERO; DROP_VEC;
              REAL_EXP_0; VECTOR_MUL_LID] THEN
  ASM_SIMP_TAC[EXP_LOG] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The germ step in R^N.  For a smooth f near 0 with f 0 = 0                *)
(* and invertible derivative D = U P (polar decomposition) there are an     *)
(* orthogonal Q = U^T and a diffeomorphism G, the identity outside          *)
(* ball(0,1), with G = Q o f near 0: G = H1 o G2 with H1 the scaled S4b'     *)
(* isotopy end for P and G2 the cut-off of P^-1 o Q o f (SMT_GERM_CUTOFF).   *)
(* ------------------------------------------------------------------------- *)

let SMT_DISC_GERM = prove
 (`!(f:real^N->real^N) W.
        open W /\ vec 0 IN W /\ smooth_map_on W f /\ f(vec 0) = vec 0 /\
        invertible(matrix(frechet_derivative f (at (vec 0))))
        ==> ?Q G G' d. orthogonal_transformation Q /\
                       diffeomorphism_on (:real^N) (:real^N) G G' /\
                       (!x. &1 <= norm x ==> G x = x) /\ &0 < d /\
                       (!z. norm z <= d ==> z IN W /\ G z = Q(f z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `D = frechet_derivative (f:real^N->real^N) (at (vec 0))` THEN
  SUBGOAL_THEN `((f:real^N->real^N) has_derivative D) (at (vec 0))` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `W:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(D:real^N->real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
  MP_TAC(ISPEC `matrix(D:real^N->real^N)` RIGHT_POLAR_DECOMPOSITION_INVERTIBLE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:real^N^N` (X_CHOOSE_THEN `Pm:real^N^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `Pm ** matrix_inv Pm = mat 1 /\ matrix_inv Pm ** (Pm:real^N^N) = mat 1`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MATRIX_INV THEN MATCH_MP_TAC POSITIVE_DEFINITE_IMP_INVERTIBLE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `transp U ** (U:real^N^N) = mat 1` ASSUME_TAC THENL
   [ASM_MESON_TAC[ORTHOGONAL_MATRIX]; ALL_TAC] THEN
  (* the S4b' isotopy for P *)
  MP_TAC(REWRITE_RULE[SMT_POSDEF_GERM_STATEMENT] (ISPEC `(:N)` SMT_POSDEF_GERM)) THEN
  DISCH_THEN(MP_TAC o SPEC `\x:real^N. (Pm:real^N^N) ** x`) THEN
  REWRITE_TAC[MATRIX_OF_MATRIX_VECTOR_MUL; MATRIX_VECTOR_MUL_LINEAR] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `H:real->real^N->real^N` (X_CHOOSE_THEN `K:real->real^N->real^N`
    (X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 (LABEL_TAC "iso")
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
        (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "lin")
          (X_CHOOSE_THEN `R0:real` (LABEL_TAC "far")))))))))) THEN
  (* the germ tangent to the identity and its cut-off *)
  ABBREV_TAC `M:real^N^N = matrix_inv (Pm:real^N^N) ** transp (U:real^N^N)` THEN
  SUBGOAL_THEN `(M:real^N^N) ** matrix(D:real^N->real^N) = mat 1` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN UNDISCH_TAC `(U:real^N^N) ** Pm = matrix(D:real^N->real^N)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[MATRIX_MUL_ASSOC] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM MATRIX_MUL_ASSOC] THEN
    ASM_REWRITE_TAC[MATRIX_MUL_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\z:real^N. (M:real^N^N) ** (f:real^N->real^N) z) has_derivative (\y. y)) (at (vec 0))`
  (LABEL_TAC "der0") THENL
   [SUBGOAL_THEN `(\y:real^N. y) = (\v. (M:real^N^N) ** v) o D` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `y:real^N` THEN
      FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
        [GSYM(MATCH_MP MATRIX_WORKS th)]) THEN
      ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID];
      ALL_TAC] THEN
    SUBGOAL_THEN `(\z:real^N. (M:real^N^N) ** (f:real^N->real^N) z) = (\v. M ** v) o f`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z:real^N. (M:real^N^N) ** (f:real^N->real^N) z`;
                 `W INTER ball(vec 0:real^N,&1 / &2)`] SMT_GERM_CUTOFF) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL; IN_INTER; CENTRE_IN_BALL; MATRIX_VECTOR_MUL_RZERO] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `W:real^N->bool` THEN
    REWRITE_TAC[INTER_SUBSET] THEN
    SUBGOAL_THEN `(\z:real^N. (M:real^N^N) ** (f:real^N->real^N) z) = (\v. M ** v) o f`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `G2:real->real^N->real^N` (X_CHOOSE_THEN
    `G2':real->real^N->real^N` (X_CHOOSE_THEN `s:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "iso2")
        (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
          (CONJUNCTS_THEN2 (LABEL_TAC "far2") (LABEL_TAC "lin2" o BETA_RULE)))))))))) THEN
  SUBGOAL_THEN `s <= &1 / &2` ASSUME_TAC THENL
   [UNDISCH_TAC `cball(vec 0:real^N,s) SUBSET W INTER ball(vec 0,&1 / &2)` THEN
    REWRITE_TAC[SUBSET_INTER; SUBSET_BALLS; DIST_REFL] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the scaled end of the S4b' isotopy *)
  ABBREV_TAC `c = inv(&2 * (abs R0 + &1))` THEN
  SUBGOAL_THEN `&0 < c /\ inv c = &2 * (abs R0 + &1)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[REAL_INV_INV] THEN
    MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(H:real->real^N->real^N) (&1)`; `(K:real->real^N->real^N) (&1)`; `c:real`]
    SMT_DISC_CONJ_SCALE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "iso" (MP_TAC o REWRITE_RULE[diffeo_isotopy]) THEN
    SIMP_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN `!x:real^N. &1 / &2 <= norm x
                           ==> c % (H:real->real^N->real^N) (&1) (inv c % x) = x`
  (LABEL_TAC "hfar") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(H:real->real^N->real^N) (&1) (inv c % x) = inv c % x` SUBST1_TAC THENL
     [USE_THEN "far" MATCH_MP_TAC THEN
      ASM_SIMP_TAC[NORM_MUL; REAL_ARITH `&0 < c ==> abs c = c`; REAL_LT_INV] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(&2 * (abs R0 + &1)) * (&1 / &2)` THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^N. norm x <= c * e
                           ==> c % (H:real->real^N->real^N) (&1) (inv c % x) = Pm ** x`
  (LABEL_TAC "hlin") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(H:real->real^N->real^N) (&1) (inv c % x) = Pm ** (inv c % x)`
    SUBST1_TAC THENL
     [USE_THEN "lin" MATCH_MP_TAC THEN
      ASM_SIMP_TAC[NORM_MUL; REAL_ARITH `&0 < c ==> abs c = c`; REAL_LT_INV] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2 * (abs R0 + &1)) * (c * e)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN
        UNDISCH_TAC `inv c = &2 * (abs R0 + &1)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD];
      REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL] THEN
      ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID]];
    ALL_TAC] THEN
  (* continuity of the germ at 0 *)
  SUBGOAL_THEN
   `?d1. &0 < d1 /\
         !z:real^N. norm z < d1 ==> norm((M:real^N^N) ** (f:real^N->real^N) z) < c * e`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(\z:real^N. (M:real^N^N) ** (f:real^N->real^N) z) continuous (at (vec 0))`
    MP_TAC THENL
     [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN REWRITE_TAC[differentiable] THEN
      EXISTS_TAC `\y:real^N. y` THEN USE_THEN "der0" ACCEPT_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[continuous_at; DIST_0] THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DIST_0] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_MUL];
    ALL_TAC] THEN
  ABBREV_TAC `d = min (d1 / &2) (s / &2)` THEN
  SUBGOAL_THEN `&0 < d /\ d < d1 /\ d <= s / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`\x:real^N. transp(U:real^N^N) ** x`;
    `(\x. c % (H:real->real^N->real^N) (&1) (inv c % x)) o (G2:real->real^N->real^N) (&1)`;
    `(G2':real->real^N->real^N) (&1) o (\y. c % (K:real->real^N->real^N) (&1) (inv c % y))`;
    `d:real`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[ORTHOGONAL_TRANSFORMATION_MATRIX; MATRIX_VECTOR_MUL_LINEAR;
                MATRIX_OF_MATRIX_VECTOR_MUL] THEN
    ASM_SIMP_TAC[ORTHOGONAL_MATRIX_TRANSP];
    MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN EXISTS_TAC `(:real^N)` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "iso2" (MP_TAC o REWRITE_RULE[diffeo_isotopy]) THEN
    SIMP_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(G2:real->real^N->real^N) (&1) x = x` SUBST1_TAC THENL
     [USE_THEN "far2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    BETA_TAC THEN USE_THEN "hfar" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[];
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `cball(vec 0:real^N,s) SUBSET W INTER ball(vec 0,&1 / &2)` THEN
      REWRITE_TAC[SUBSET; IN_CBALL_0; IN_INTER] THEN
      DISCH_THEN(MP_TAC o SPEC `z:real^N`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(G2:real->real^N->real^N) (&1) z = (M:real^N^N) ** (f:real^N->real^N) z`
    SUBST1_TAC THENL
     [USE_THEN "lin2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `norm((M:real^N^N) ** (f:real^N->real^N) z) <= c * e` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    BETA_TAC THEN USE_THEN "hlin" (fun th -> ASM_SIMP_TAC[th]) THEN
    EXPAND_TAC "M" THEN REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_MUL_ASSOC] THEN
    ASM_REWRITE_TAC[MATRIX_MUL_LID]]);;

(* ------------------------------------------------------------------------- *)
(* Transport through ball charts.  A diffeomorphism of R^N                  *)
(* that is the identity outside cball(0,r), r < 2, carried by a ball chart  *)
(* b and extended by the identity, is a diffeomorphism of the manifold      *)
(* supported in the compact set b(cball(0,r)); every point is the centre    *)
(* of a ball chart.                                                          *)
(* ------------------------------------------------------------------------- *)

let SMT_DISC_INVERSE_FAR = prove
 (`!(G:real^N->real^N) G' r.
        diffeomorphism_on (:real^N) (:real^N) G G' /\ (!x. r <= norm x ==> G x = x)
        ==> (!x. r <= norm x ==> G' x = x) /\
            (!x. norm x < r ==> norm(G x) < r /\ norm(G' x) < r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[diffeomorphism_on; IN_UNIV] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x:real^N. r <= norm x ==> (G':real^N->real^N) x = x` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN CONJ_TAC THEN DISCH_TAC THENL
   [MP_TAC(MATCH_MP (ASSUME `!x:real^N. r <= norm x ==> (G':real^N->real^N) x = x`)
                    (ASSUME `r <= norm((G:real^N->real^N) x)`)) THEN
    DISCH_THEN(MP_TAC o AP_TERM `norm:real^N->real`) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MP_TAC(MATCH_MP (ASSUME `!x:real^N. r <= norm x ==> (G:real^N->real^N) x = x`)
                    (ASSUME `r <= norm((G':real^N->real^N) x)`)) THEN
    DISCH_THEN(MP_TAC o AP_TERM `norm:real^N->real`) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let SMT_DISC_TRANSPORT = prove
 (`!top atlas (b:real^N->A) G G' r.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        mfd_ball_chart top atlas b /\
        diffeomorphism_on (:real^N) (:real^N) G G' /\ &0 < r /\ r < &2 /\
        (!x. r <= norm x ==> G x = x)
        ==> ?Phi Psi.
              mfd_diffeo top atlas (topspace top) top atlas (topspace top) Phi Psi /\
              compact_in top (IMAGE b (cball(vec 0,r))) /\
              (!p. p IN topspace top DIFF IMAGE b (cball(vec 0,r))
                   ==> Phi p = p /\ Psi p = p) /\
              (!x. x IN ball(vec 0,&2) ==> Phi(b x) = b(G x) /\ Psi(b x) = b(G' x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:real^N->real^N`; `G':real^N->real^N`; `r:real`] SMT_DISC_INVERSE_FAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MFD_PARAM_MAPS o REWRITE_RULE[mfd_ball_chart]) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:A->real^N` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `Kc = IMAGE (b:real^N->A) (cball(vec 0,r))` THEN
  SUBGOAL_THEN `compact_in top (Kc:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Kc" THEN MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `ball(vec 0:real^N,&2)`] THEN
    ASM_REWRITE_TAC[GSYM mfd_ball_chart; COMPACT_CBALL; SUBSET; IN_CBALL_0; IN_BALL_0] THEN
    ASM_MESON_TAC[REAL_LET_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Kc:A->bool) SUBSET IMAGE (b:real^N->A) (ball(vec 0,&2)) /\
                IMAGE (b:real^N->A) (ball(vec 0,&2)) SUBSET topspace top`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Kc" THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN
      ASM_MESON_TAC[REAL_LET_TRANS];
      ASM_MESON_TAC[OPEN_IN_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (topspace top DIFF (Kc:A->bool))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `Kc:A->bool`] COMPACT_IN_IMP_CLOSED_IN) THEN
    ASM_SIMP_TAC[closed_in];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (b:real^N->A) (ball(vec 0,&2)) UNION (topspace top DIFF Kc) = topspace top`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  (* G as a diffeomorphism of ball(0,2) *)
  SUBGOAL_THEN
   `diffeomorphism_on (ball(vec 0,&2)) (ball(vec 0,&2)) (G:real^N->real^N) G'`
  ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on (:real^N) (:real^N) G G'` THEN
    REWRITE_TAC[diffeomorphism_on; OPEN_BALL; IN_UNIV] THEN STRIP_TAC THEN
    SUBGOAL_THEN `!x:real^N. norm x < &2 ==> norm((G:real^N->real^N) x) < &2 /\
                                             norm((G':real^N->real^N) x) < &2`
    ASSUME_TAC THENL
     [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN ASM_CASES_TAC `norm(x:real^N) < r` THENL
       [ASM_MESON_TAC[REAL_LT_TRANS];
        SUBGOAL_THEN `r <= norm(x:real^N)` ASSUME_TAC THENL
         [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[]]];
      ALL_TAC] THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_BALL_0] THEN ASM_SIMP_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      ASM_MESON_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV]];
    ALL_TAC] THEN
  (* the transported map on the chart image *)
  SUBGOAL_THEN
   `mfd_diffeo top (atlas:((A->bool)#(A->real^N))->bool) (IMAGE (b:real^N->A) (ball(vec 0,&2)))
                top atlas (IMAGE b (ball(vec 0,&2)))
      ((b:real^N->A) o (G:real^N->real^N) o (e:A->real^N)) ((b o G') o e)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_COMPOSE THEN
    MAP_EVERY EXISTS_TAC [`euclidean:(real^N)topology`; `open_set_atlas(:real^N)`;
                          `ball(vec 0:real^N,&2)`] THEN
    ASM_REWRITE_TAC[MFD_EUCLIDEAN_ATLAS] THEN
    MATCH_MP_TAC MFD_DIFFEO_COMPOSE THEN
    MAP_EVERY EXISTS_TAC [`euclidean:(real^N)topology`; `open_set_atlas(:real^N)`;
                          `ball(vec 0:real^N,&2)`] THEN
    ASM_REWRITE_TAC[MFD_EUCLIDEAN_ATLAS; MFD_DIFFEO_EUCLIDEAN] THEN
    MATCH_MP_TAC MFD_DIFFEO_SYM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p:A. p IN topspace top DIFF Kc
          ==> (if p IN IMAGE (b:real^N->A) (ball(vec 0,&2))
               then b((G:real^N->real^N)((e:A->real^N) p)) else p) = p /\
              (if p IN IMAGE b (ball(vec 0,&2)) then b((G':real^N->real^N)(e p)) else p) = p`
  (LABEL_TAC "offK") THENL
   [X_GEN_TAC `p:A` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(b:real^N->A)((e:A->real^N) p) = p` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `r <= norm((e:A->real^N) p)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      UNDISCH_TAC `~((p:A) IN Kc)` THEN REWRITE_TAC[] THEN EXPAND_TAC "Kc" THEN
      REWRITE_TAC[IN_IMAGE; IN_CBALL_0] THEN EXISTS_TAC `(e:A->real^N) p` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`\p:A. if p IN IMAGE (b:real^N->A) (ball(vec 0,&2))
           then b((G:real^N->real^N)((e:A->real^N) p)) else p`;
    `\p:A. if p IN IMAGE (b:real^N->A) (ball(vec 0,&2))
           then b((G':real^N->real^N)((e:A->real^N) p)) else p`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_GLUE THEN
    MAP_EVERY EXISTS_TAC
     [`IMAGE (b:real^N->A) (ball(vec 0,&2))`; `topspace top DIFF (Kc:A->bool)`;
      `IMAGE (b:real^N->A) (ball(vec 0,&2))`; `topspace top DIFF (Kc:A->bool)`;
      `(b:real^N->A) o (G:real^N->real^N) o (e:A->real^N)`;
      `((b:real^N->A) o G') o (e:A->real^N)`; `\p:A. p`; `\p:A. p`] THEN
    ASM_SIMP_TAC[MFD_DIFFEO_ID; o_THM];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[] THEN USE_THEN "offK" ACCEPT_TAC;
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(b:real^N->A) x IN IMAGE b (ball(vec 0,&2))` (fun th -> REWRITE_TAC[th]) THENL
     [ASM SET_TAC[]; ASM_SIMP_TAC[]]]);;

(* Every point is the centre of a ball chart.                                *)

let SMT_DISC_AFFINE_DIFFEO = prove
 (`!(a:real^N) rho.
        &0 < rho
        ==> diffeomorphism_on (ball(vec 0,&2)) (ball(a,rho * &2))
              (\x. a + rho % x) (\y. inv rho % (y - a))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (\x:real^N. a + rho % x) (ball(vec 0,&2)) = ball(a,rho * &2)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\x:real^N. a + rho % x) = (\y. a + y) o (\x. rho % x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    REWRITE_TAC[IMAGE_o] THEN
    ASM_SIMP_TAC[GSYM BALL_SCALING; VECTOR_MUL_RZERO] THEN
    REWRITE_TAC[GSYM BALL_TRANSLATION; VECTOR_ADD_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!x:real^N. inv rho % ((a + rho % x) - a) = x) /\
                (!y:real^N. a + rho % (inv rho % (y - a)) = y)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[VECTOR_ADD_SUB; VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[diffeomorphism_on; OPEN_BALL] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `IMAGE (\x:real^N. a + rho % x) (ball(vec 0,&2)) = ball(a,rho * &2)` THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
    REWRITE_TAC[OPEN_BALL; SMOOTH_MAP_ON_CONST] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN REWRITE_TAC[OPEN_BALL; SMOOTH_MAP_ON_ID];
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN REWRITE_TAC[OPEN_BALL] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    REWRITE_TAC[OPEN_BALL; SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_ID]]);;

let SMT_DISC_BALL_AT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) p.
        smooth_manifold_atlas top atlas /\ p IN topspace top
        ==> ?b. mfd_ball_chart top atlas b /\ b(vec 0) = p`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `p:A`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A)`,
           `c:(A->bool)#(A->real^N)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `(phi:A->real^N) p` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `chart_inv (U:A->bool,phi:A->real^N) o (\x. phi p + (eps / &2) % x)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[mfd_ball_chart] THEN MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (phi:A->real^N) U`; `ball((phi:A->real^N) p,(eps / &2) * &2)`;
                          `\y:real^N. inv(eps / &2) % (y - (phi:A->real^N) p)`] THEN
    ASM_SIMP_TAC[MFD_PARAM_CHART_INV; SMT_DISC_AFFINE_DIFFEO; REAL_HALF] THEN
    REWRITE_TAC[REAL_ARITH `(e / &2) * &2 = e`] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[o_THM; VECTOR_MUL_RZERO; VECTOR_ADD_RID] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Homogeneity.  Compactly supported diffeomorphisms compose;               *)
(* near every point the points of a small chart ball are reached by a       *)
(* transported push, in both directions; so the points reachable from p     *)
(* form an open and closed set, all of a connected manifold.                *)
(* ------------------------------------------------------------------------- *)

let SMT_DISC_COMPOSE_CS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) Phi1 Psi1 K1 Phi2 Psi2 K2.
        smooth_manifold_atlas top atlas /\
        mfd_diffeo top atlas (topspace top) top atlas (topspace top) Phi1 Psi1 /\
        compact_in top K1 /\ (!x. x IN topspace top DIFF K1 ==> Phi1 x = x) /\
        mfd_diffeo top atlas (topspace top) top atlas (topspace top) Phi2 Psi2 /\
        compact_in top K2 /\ (!x. x IN topspace top DIFF K2 ==> Phi2 x = x)
        ==> mfd_diffeo top atlas (topspace top) top atlas (topspace top)
                       (Phi2 o Phi1) (Psi1 o Psi2) /\
            compact_in top (K1 UNION K2) /\
            (!x. x IN topspace top DIFF (K1 UNION K2) ==> (Phi2 o Phi1) x = x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_COMPOSE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `topspace top:A->bool`] THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[COMPACT_IN_UNION];
    REWRITE_TAC[IN_DIFF; IN_UNION; DE_MORGAN_THM; o_THM] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(Phi1:A->A) x = x` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `Phi1:A->A`)) (concl th) &&
                                             is_forall(concl th))) THEN
      ASM_REWRITE_TAC[IN_DIFF];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `Phi2:A->A`)) (concl th) &&
                                             is_forall(concl th))) THEN
      ASM_REWRITE_TAC[IN_DIFF]]]);;

(* Local pushes on the manifold, in both directions.                         *)

let SMT_DISC_LOCAL_PUSH = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) q0.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ q0 IN topspace top
        ==> ?W. open_in top W /\ q0 IN W /\
                !q1. q1 IN W
                     ==> (?Phi Psi K.
                            mfd_diffeo top atlas (topspace top) top atlas (topspace top)
                                       Phi Psi /\
                            compact_in top K /\
                            (!x. x IN topspace top DIFF K ==> Phi x = x) /\ Phi q0 = q1) /\
                         (?Phi Psi K.
                            mfd_diffeo top atlas (topspace top) top atlas (topspace top)
                                       Phi Psi /\
                            compact_in top K /\
                            (!x. x IN topspace top DIFF K ==> Phi x = x) /\ Phi q1 = q0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `q0:A`]
    SMT_DISC_BALL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `b:real^N->A` STRIP_ASSUME_TAC) THEN
  MP_TAC(INST_TYPE [`:N`,`:N`] SMT_DISC_PUSH) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "push"))) THEN
  EXISTS_TAC `IMAGE (b:real^N->A) (ball(vec 0,min d (&1)))` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `ball(vec 0:real^N,&2)`] THEN
    REWRITE_TAC[OPEN_BALL; GSYM mfd_ball_chart] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_BALL_0] THEN REAL_ARITH_TAC;
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 0:real^N` THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_BALL_0] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  USE_THEN "push" (MP_TAC o SPEC `y:real^N`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:real^N->real^N` (X_CHOOSE_THEN `G':real^N->real^N`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `b:real^N->A`;
                 `G:real^N->real^N`; `G':real^N->real^N`; `&1`] SMT_DISC_TRANSPORT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Phi:A->A` (X_CHOOSE_THEN `Psi:A->A` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(G':real^N->real^N) y = vec 0` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
      GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
    DISCH_THEN(MP_TAC o SPEC `vec 0:real^N`) THEN ASM_REWRITE_TAC[IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(y:real^N) < &2 /\ norm(vec 0:real^N) < &2` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[NORM_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`Phi:A->A`; `Psi:A->A`; `IMAGE (b:real^N->A) (cball(vec 0,&1))`] THEN
    ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `vec 0:real^N` o check (is_forall o concl) o
      check (fun th -> can (find_term ((=) `ball(vec 0:real^N,&2)`)) (concl th))) THEN
    ASM_REWRITE_TAC[IN_BALL_0] THEN SIMP_TAC[];
    MAP_EVERY EXISTS_TAC [`Psi:A->A`; `Phi:A->A`; `IMAGE (b:real^N->A) (cball(vec 0,&1))`] THEN
    ASM_SIMP_TAC[MFD_DIFFEO_SYM] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check (is_forall o concl) o
      check (fun th -> can (find_term ((=) `ball(vec 0:real^N,&2)`)) (concl th))) THEN
    ASM_REWRITE_TAC[IN_BALL_0] THEN SIMP_TAC[]]);;

let SMT_DISC_HOMOGENEOUS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) p q.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ connected_space top /\
        p IN topspace top /\ q IN topspace top
        ==> ?Phi Psi K. mfd_diffeo top atlas (topspace top) top atlas (topspace top) Phi Psi /\
                        compact_in top K /\
                        (!x. x IN topspace top DIFF K ==> Phi x = x) /\ Phi p = q`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `S = {q:A | q IN topspace top /\
               ?Phi Psi K. mfd_diffeo top (atlas:((A->bool)#(A->real^N))->bool) (topspace top)
                                      top atlas (topspace top) Phi Psi /\
                           compact_in top K /\
                           (!x. x IN topspace top DIFF K ==> Phi x = x) /\ Phi p = q}` THEN
  SUBGOAL_THEN `(S:A->bool) = topspace top` MP_TAC THENL
   [MATCH_MP_TAC TOPC_CONNECTED_SPACE_CLOPEN THEN EXISTS_TAC `p:A` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "S" THEN SET_TAC[];
      EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`\x:A. x`; `\x:A. x`; `{}:A->bool`] THEN
      ASM_SIMP_TAC[MFD_DIFFEO_ID; OPEN_IN_TOPSPACE; COMPACT_IN_EMPTY];
      X_GEN_TAC `z:A` THEN EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `Phi1:A->A`
        (X_CHOOSE_THEN `Psi1:A->A` (X_CHOOSE_THEN `K1:A->bool` STRIP_ASSUME_TAC)))) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `z:A`]
        SMT_DISC_LOCAL_PUSH) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `W:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lp")))) THEN
      EXISTS_TAC `W:A->bool` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "S" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      X_GEN_TAC `q1:A` THEN DISCH_TAC THEN CONJ_TAC THENL
       [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
      USE_THEN "lp" (MP_TAC o SPEC `q1:A`) THEN
      (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
      DISCH_THEN(X_CHOOSE_THEN `Phi2:A->A` (X_CHOOSE_THEN `Psi2:A->A`
        (X_CHOOSE_THEN `K2:A->bool` STRIP_ASSUME_TAC)) o CONJUNCT1) THEN
      MAP_EVERY EXISTS_TAC [`(Phi2:A->A) o (Phi1:A->A)`; `(Psi1:A->A) o (Psi2:A->A)`;
                            `(K1:A->bool) UNION K2`] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `Phi1:A->A`; `Psi1:A->A`; `K1:A->bool`;
                     `Phi2:A->A`; `Psi2:A->A`; `K2:A->bool`] SMT_DISC_COMPOSE_CS) THEN
      ASM_SIMP_TAC[o_THM];
      X_GEN_TAC `z:A` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `z:A`]
        SMT_DISC_LOCAL_PUSH) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `W:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lp")))) THEN
      EXISTS_TAC `W:A->bool` THEN ASM_REWRITE_TAC[SUBSET; IN_DIFF] THEN
      X_GEN_TAC `q1:A` THEN DISCH_TAC THEN CONJ_TAC THENL
       [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
      DISCH_TAC THEN UNDISCH_TAC `~((z:A) IN S)` THEN REWRITE_TAC[] THEN
      UNDISCH_TAC `(q1:A) IN S` THEN EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `Phi1:A->A`
        (X_CHOOSE_THEN `Psi1:A->A` (X_CHOOSE_THEN `K1:A->bool` STRIP_ASSUME_TAC)))) THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "lp" (MP_TAC o SPEC `q1:A`) THEN
      (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
      DISCH_THEN(X_CHOOSE_THEN `Phi2:A->A` (X_CHOOSE_THEN `Psi2:A->A`
        (X_CHOOSE_THEN `K2:A->bool` STRIP_ASSUME_TAC)) o CONJUNCT2) THEN
      MAP_EVERY EXISTS_TAC [`(Phi2:A->A) o (Phi1:A->A)`; `(Psi1:A->A) o (Psi2:A->A)`;
                            `(K1:A->bool) UNION K2`] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `Phi1:A->A`; `Psi1:A->A`; `K1:A->bool`;
                     `Phi2:A->A`; `Psi2:A->A`; `K2:A->bool`] SMT_DISC_COMPOSE_CS) THEN
      ASM_SIMP_TAC[o_THM]];
    EXPAND_TAC "S" THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `q:A`) THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* M3.  For ball charts with b(0) = b'(0) the germ step in the              *)
(* b' chart gives Phi(b y) = b'(Q y) near 0; the radial expansion in both   *)
(* charts spreads this to cball(0,3/2); homogeneity reduces the general     *)
(* case to b(0) = b'(0).                                                     *)
(* ------------------------------------------------------------------------- *)

let SMT_DISC_GERM_MFD = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) b b'.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        mfd_ball_chart top atlas b /\ mfd_ball_chart top atlas b' /\ b(vec 0) = b'(vec 0)
        ==> ?Phi Psi K Q d.
              mfd_diffeo top atlas (topspace top) top atlas (topspace top) Phi Psi /\
              compact_in top K /\ (!x. x IN topspace top DIFF K ==> Phi x = x) /\
              orthogonal_transformation Q /\ &0 < d /\
              (!y. norm y <= d ==> Phi(b y) = b'(Q y))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(MATCH_MP MFD_PARAM_MAPS (REWRITE_RULE[mfd_ball_chart]
    (ASSUME `mfd_ball_chart top (atlas:((A->bool)#(A->real^N))->bool) b`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:A->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(MATCH_MP MFD_PARAM_MAPS (REWRITE_RULE[mfd_ball_chart]
    (ASSUME `mfd_ball_chart top (atlas:((A->bool)#(A->real^N))->bool) b'`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `e':A->real^N` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `W = {z:real^N | z IN ball(vec 0,&2) /\
                              (b':real^N->A) z IN IMAGE (b:real^N->A) (ball(vec 0,&2))}` THEN
  SUBGOAL_THEN `open(W:real^N->bool) /\ vec 0 IN W /\ W SUBSET ball(vec 0,&2)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM OPEN_IN_EUCLIDEAN] THEN MATCH_MP_TAC MFDM_OPEN_IN_PREIMAGE THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[OPEN_IN_EUCLIDEAN; OPEN_BALL];
      REAL_ARITH_TAC;
      UNDISCH_TAC `(b:real^N->A)(vec 0) = (b':real^N->A)(vec 0)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      REWRITE_TAC[CENTRE_IN_BALL] THEN REAL_ARITH_TAC;
      SET_TAC[]];
    ALL_TAC] THEN
  (* the transition T = e o b' is a diffeomorphism of W onto its image *)
  SUBGOAL_THEN
   `diffeomorphism_on W (IMAGE ((e:A->real^N) o (b':real^N->A)) W)
                      (e o b') ((e':A->real^N) o (b:real^N->A))`
  ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_o; GSYM MFD_DIFFEO_EUCLIDEAN] THEN
    MATCH_MP_TAC MFD_DIFFEO_COMPOSE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `IMAGE (b':real^N->A) W`] THEN
    ASM_REWRITE_TAC[MFD_EUCLIDEAN_ATLAS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
      MAP_EVERY EXISTS_TAC [`ball(vec 0:real^N,&2)`; `IMAGE (b':real^N->A) (ball(vec 0,&2))`] THEN
      ASM_REWRITE_TAC[OPEN_IN_EUCLIDEAN];
      MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
      MAP_EVERY EXISTS_TAC [`IMAGE (b:real^N->A) (ball(vec 0,&2))`; `ball(vec 0:real^N,&2)`] THEN
      ASM_SIMP_TAC[MFD_DIFFEO_SYM] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
        MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `ball(vec 0:real^N,&2)`] THEN
        ASM_REWRITE_TAC[GSYM mfd_ball_chart];
        EXPAND_TAC "W" THEN SET_TAC[]]];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  SUBGOAL_THEN `((e:A->real^N) o (b':real^N->A)) (vec 0) = vec 0` ASSUME_TAC THENL
   [REWRITE_TAC[o_THM] THEN
    UNDISCH_TAC `(b:real^N->A)(vec 0) = (b':real^N->A)(vec 0)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `e:A->real^N`)) (concl th) &&
      can (find_term ((=) `(b:real^N->A)`)) (concl th) && is_forall(concl th) &&
      not (can (find_term ((=) `b':real^N->A`)) (concl th)))) THEN
    REWRITE_TAC[CENTRE_IN_BALL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(e:A->real^N) o (b':real^N->A)`; `W:real^N->bool`] SMT_DISC_GERM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMT_LOCAL_INVERSE_DERIVATIVE THEN
    MAP_EVERY EXISTS_TAC [`(e':A->real^N) o (b:real^N->A)`; `W:real^N->bool`;
                          `IMAGE ((e:A->real^N) o (b':real^N->A)) W`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Q:real^N->real^N` (X_CHOOSE_THEN `G:real^N->real^N`
    (X_CHOOSE_THEN `G':real^N->real^N` (X_CHOOSE_THEN `d:real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gq"))))))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `b':real^N->A`;
                 `G:real^N->real^N`; `G':real^N->real^N`; `&1`] SMT_DISC_TRANSPORT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Phi:A->A` (X_CHOOSE_THEN `Psi:A->A`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "phib")))))) THEN
  (* T maps W INTER ball(0,d) onto a neighbourhood of 0 *)
  SUBGOAL_THEN
   `?d5. &0 < d5 /\
         !y:real^N. norm y <= d5
                    ==> ?z. z IN W /\ norm z < d /\ ((e:A->real^N) o (b':real^N->A)) z = y`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(e':A->real^N) o (b:real^N->A)`;
                   `IMAGE ((e:A->real^N) o (b':real^N->A)) W`;
                   `W INTER ball(vec 0:real^N,d)`] CONTINUOUS_OPEN_PREIMAGE) THEN
    ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL; SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
    DISCH_THEN(MP_TAC o SPEC `vec 0:real^N` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM; IN_INTER; CENTRE_IN_BALL] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 0:real^N` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `((e':A->real^N) o (b:real^N->A)) (vec 0) = vec 0` SUBST1_TAC THENL
       [UNDISCH_TAC `((e:A->real^N) o (b':real^N->A)) (vec 0) = vec 0` THEN
        DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[CENTRE_IN_BALL]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d4:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `d4 / &2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    UNDISCH_TAC `ball(vec 0:real^N,d4) SUBSET
                 {x | x IN IMAGE ((e:A->real^N) o (b':real^N->A)) W /\
                      ((e':A->real^N) o (b:real^N->A)) x IN W INTER ball(vec 0,d)}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_BALL_0; IN_INTER] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC)
      STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `z:real^N` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `norm(((e':A->real^N) o (b:real^N->A)) y) < d` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `((e':A->real^N) o (b:real^N->A)) (((e:A->real^N) o (b':real^N->A)) z) = z`
    (fun th -> REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`Phi:A->A`; `Psi:A->A`; `IMAGE (b':real^N->A) (cball(vec 0,&1))`;
                        `Q:real^N->real^N`; `d5:real`] THEN
  ASM_SIMP_TAC[] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  SUBGOAL_THEN `(b:real^N->A)(((e:A->real^N) o (b':real^N->A)) z) = b' z` SUBST1_TAC THENL
   [REWRITE_TAC[o_THM] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `e:A->real^N`)) (concl th) && is_forall(concl th) &&
      can (find_term ((=) `IMAGE (b:real^N->A) (ball(vec 0,&2))`)) (concl th) &&
      not (can (find_term ((=) `b':real^N->A`)) (concl th)))) THEN
    UNDISCH_TAC `(z:real^N) IN W` THEN
    SUBST1_TAC(SYM(ASSUME `{z:real^N | z IN ball(vec 0,&2) /\
                                      (b':real^N->A) z IN IMAGE (b:real^N->A) (ball(vec 0,&2))} =
                           W`)) THEN
    SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `z IN ball(vec 0:real^N,&2)` ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^N) IN W` THEN UNDISCH_TAC `W SUBSET ball(vec 0:real^N,&2)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "phib" (MP_TAC o SPEC `z:real^N`) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN AP_TERM_TAC THEN
  USE_THEN "gq" (MP_TAC o SPEC `z:real^N`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]);;

let SMT_DISC_EXPAND_MFD = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) b b' Phi Psi K Q d.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        mfd_ball_chart top atlas b /\ mfd_ball_chart top atlas b' /\
        mfd_diffeo top atlas (topspace top) top atlas (topspace top) Phi Psi /\
        compact_in top K /\ (!x. x IN topspace top DIFF K ==> Phi x = x) /\
        orthogonal_transformation Q /\ &0 < d /\
        (!y. norm y <= d ==> Phi(b y) = b'(Q y))
        ==> ?Phi' Psi' K'.
              mfd_diffeo top atlas (topspace top) top atlas (topspace top) Phi' Psi' /\
              compact_in top K' /\ (!x. x IN topspace top DIFF K' ==> Phi' x = x) /\
              (!x. norm x <= &3 / &2 ==> Phi'(b x) = b'(Q x))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "germ")))))))))) THEN
  ABBREV_TAC `del = min d (&3 / &2)` THEN
  SUBGOAL_THEN `&0 < del /\ del <= d /\ del <= &3 / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "del" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `lam = (&3 / &2) / del` THEN
  SUBGOAL_THEN `&1 <= lam /\ &0 < lam /\ &3 / &2 / lam = del /\
                !t. t <= &3 / &2 ==> inv lam * t <= del`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "lam" THEN
    UNDISCH_TAC `&0 < del` THEN UNDISCH_TAC `del <= &3 / &2` THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < del` THEN CONV_TAC REAL_FIELD;
      X_GEN_TAC `t:real` THEN DISCH_TAC THEN
      SUBGOAL_THEN `inv(&3 / &2 / del) = del * &2 / &3` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < del` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      SUBGOAL_THEN `(del * &2 / &3) * t = del * (&2 / &3 * t)` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPEC `lam:real` (INST_TYPE [`:N`,`:N`] SMT_DISC_EXPAND)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `E:real^N->real^N` (X_CHOOSE_THEN `E':real^N->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "elin"))))) THEN
  SUBGOAL_THEN `!x:real^N. norm x <= &3 / &2 ==> norm(inv lam % x) <= del`
  (LABEL_TAC "small") THENL
   [REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[NORM_MUL; REAL_ABS_INV; REAL_ARITH `&0 < x ==> abs x = x`];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^N. norm x <= &3 / &2 ==> (E':real^N->real^N) x = inv lam % x`
  (LABEL_TAC "einv") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(E:real^N->real^N)(inv lam % x) = x` ASSUME_TAC THENL
     [USE_THEN "elin" (MP_TAC o SPEC `inv lam % x:real^N`) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
      ALL_TAC] THEN
    UNDISCH_TAC `diffeomorphism_on (:real^N) (:real^N) E E'` THEN
    REWRITE_TAC[diffeomorphism_on; IN_UNIV] THEN
    DISCH_THEN(MP_TAC o SPEC `inv lam % x:real^N` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
               CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `b:real^N->A`;
                 `E:real^N->real^N`; `E':real^N->real^N`; `&7 / &4`] SMT_DISC_TRANSPORT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Ab:A->A` (X_CHOOSE_THEN `Ab':A->A`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "aoff") (LABEL_TAC "ab")))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `b':real^N->A`;
                 `E:real^N->real^N`; `E':real^N->real^N`; `&7 / &4`] SMT_DISC_TRANSPORT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Bb:A->A` (X_CHOOSE_THEN `Bb':A->A`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "boff") (LABEL_TAC "bb")))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `Ab':A->A`; `Ab:A->A`; `IMAGE (b:real^N->A) (cball(vec 0,&7 / &4))`;
                 `Phi:A->A`; `Psi:A->A`; `K:A->bool`] SMT_DISC_COMPOSE_CS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MFD_DIFFEO_SYM] THEN REPEAT STRIP_TAC THEN
    USE_THEN "aoff" (MP_TAC o SPEC `x:A`) THEN ASM_SIMP_TAC[];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(Phi:A->A) o (Ab':A->A)`; `(Ab:A->A) o (Psi:A->A)`;
                 `IMAGE (b:real^N->A) (cball(vec 0,&7 / &4)) UNION K`;
                 `Bb:A->A`; `Bb':A->A`; `IMAGE (b':real^N->A) (cball(vec 0,&7 / &4))`]
    SMT_DISC_COMPOSE_CS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    USE_THEN "boff" (MP_TAC o SPEC `x:A`) THEN ASM_SIMP_TAC[];
    STRIP_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`(Bb:A->A) o (Phi:A->A) o (Ab':A->A)`; `((Ab:A->A) o (Psi:A->A)) o (Bb':A->A)`;
    `(IMAGE (b:real^N->A) (cball(vec 0,&7 / &4)) UNION K) UNION
     IMAGE (b':real^N->A) (cball(vec 0,&7 / &4))`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN `x IN ball(vec 0:real^N,&2)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "ab" (MP_TAC o SPEC `x:real^N`) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  USE_THEN "einv" (fun th -> ASM_SIMP_TAC[th]) THEN
  SUBGOAL_THEN `norm(inv lam % x:real^N) <= del` ASSUME_TAC THENL
   [USE_THEN "small" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "germ" (MP_TAC o SPEC `inv lam % x:real^N`) THEN
  (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `norm((Q:real^N->real^N)(inv lam % x)) <= del` ASSUME_TAC THENL
   [ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION]; ALL_TAC] THEN
  USE_THEN "bb" (MP_TAC o SPEC `(Q:real^N->real^N)(inv lam % x)`) THEN
  (ANTS_TAC THENL [REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN AP_TERM_TAC THEN
  USE_THEN "elin" (MP_TAC o SPEC `(Q:real^N->real^N)(inv lam % x)`) THEN
  (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `linear(Q:real^N->real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM LINEAR_CMUL; VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ;
               VECTOR_MUL_LID]);;

(* The weak disc theorem M3: homogeneity moves b(0) to b'(0), then the germ *)
(* step and the radial expansion for the ball charts Phi1 o b and b'.       *)

let SMT_DISC = prove
 (`!(u:A->bool) (n:N->bool). SMT_DISC_STATEMENT u n`,
  REWRITE_TAC[SMT_DISC_STATEMENT] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (b:real^N->A) (ball(vec 0,&2)) SUBSET topspace top /\
                IMAGE (b':real^N->A) (ball(vec 0,&2)) SUBSET topspace top`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MFD_PARAM_IMAGE_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `ball(vec 0:real^N,&2)`] THEN
    ASM_REWRITE_TAC[GSYM mfd_ball_chart; SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(vec 0:real^N) IN ball(vec 0,&2)` ASSUME_TAC THENL
   [REWRITE_TAC[CENTRE_IN_BALL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(b:real^N->A)(vec 0) IN topspace top /\ (b':real^N->A)(vec 0) IN topspace top`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC(SET_RULE `!s t (x:A). s SUBSET t /\ x IN s ==> x IN t`) THENL
     [EXISTS_TAC `IMAGE (b:real^N->A) (ball(vec 0,&2))`;
      EXISTS_TAC `IMAGE (b':real^N->A) (ball(vec 0,&2))`] THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(b:real^N->A)(vec 0)`; `(b':real^N->A)(vec 0)`] SMT_DISC_HOMOGENEOUS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Phi1:A->A` (X_CHOOSE_THEN `Psi1:A->A`
    (X_CHOOSE_THEN `K1:A->bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `mfd_ball_chart top (atlas:((A->bool)#(A->real^N))->bool)
                               ((Phi1:A->A) o (b:real^N->A))` ASSUME_TAC THENL
   [REWRITE_TAC[mfd_ball_chart] THEN MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `topspace top:A->bool`; `topspace top:A->bool`; `Psi1:A->A`] THEN
    ASM_REWRITE_TAC[GSYM mfd_ball_chart];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(Phi1:A->A) o (b:real^N->A)`; `b':real^N->A`] SMT_DISC_GERM_MFD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[o_THM]; REWRITE_TAC[o_THM]] THEN
  DISCH_THEN(X_CHOOSE_THEN `Phi2:A->A` (X_CHOOSE_THEN `Psi2:A->A`
    (X_CHOOSE_THEN `K2:A->bool` (X_CHOOSE_THEN `Q:real^N->real^N`
      (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(Phi1:A->A) o (b:real^N->A)`; `b':real^N->A`;
                 `Phi2:A->A`; `Psi2:A->A`; `K2:A->bool`; `Q:real^N->real^N`; `d:real`]
    SMT_DISC_EXPAND_MFD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[o_THM]; REWRITE_TAC[o_THM]] THEN
  DISCH_THEN(X_CHOOSE_THEN `Phi3:A->A` (X_CHOOSE_THEN `Psi3:A->A`
    (X_CHOOSE_THEN `K3:A->bool` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `Phi1:A->A`; `Psi1:A->A`; `K1:A->bool`;
                 `Phi3:A->A`; `Psi3:A->A`; `K3:A->bool`] SMT_DISC_COMPOSE_CS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[o_THM] THEN STRIP_TAC] THEN
  MAP_EVERY EXISTS_TAC [`(Phi3:A->A) o (Phi1:A->A)`; `(Psi1:A->A) o (Psi3:A->A)`;
                        `Q:real^N->real^N`; `(K1:A->bool) UNION K3`] THEN
  ASM_REWRITE_TAC[o_THM]);;

(* ------------------------------------------------------------------------- *)
(* M4 (the complement of a ball in S^3 is a ball) and M5                    *)
(* (sphere sums X # S^3 = X) without conditions: the implications of        *)
(* pc_smt_glue applied to the disc theorem M3.                              *)
(* ------------------------------------------------------------------------- *)

let SMT_S3_BALL_COMPLEMENT_ALL = prove
 (`SMT_S3_BALL_COMPLEMENT_STATEMENT`,
  MATCH_MP_TAC SMT_S3_BALL_COMPLEMENT THEN REWRITE_TAC[SMT_DISC]);;

let SMT_SPHERE_SUM_ALL = prove
 (`!u:A->bool v:B->bool w:C->bool. SMT_SPHERE_SUM_STATEMENT u v w`,
  MP_TAC SMT_SPHERE_SUM THEN REWRITE_TAC[SMT_S3_BALL_COMPLEMENT_ALL]);;

