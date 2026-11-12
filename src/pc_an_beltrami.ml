(* ========================================================================= *)
(* Unit pc_an_beltrami: CM Lemma D.7 in the form used by CM Prop 1.5         *)
(* (W_E <= W_A): smooth metrics on S^2, continuous in t in C^infinity, give  *)
(* conformal diffeomorphisms continuous in C^1 (route B: Ahlfors' proof of   *)
(* the mapping theorem for smooth compactly supported Beltrami coefficients, *)
(* L^2 theory only).                                                         *)
(*                                                                           *)
(* First the statement CM_D7_UNIFORMIZATION_STATEMENT and its sanity         *)
(* theorems.  make.ml loads 100/green.ml first, which provides wirtinger_dz, *)
(* wirtinger_dbar and CAUCHY_TRANSFORM_INVERTS_DBAR.                         *)
(* ========================================================================= *)

needs "src/pc_wan_defs.ml";;
needs "src/pc_smt_sphere.ml";;
needs "src/pc_mfd_examples.ml";;

prioritize_real();;
type_invention_error := true;;

let CM_D7_UNIFORMIZATION_STATEMENT = new_definition
 `CM_D7_UNIFORMIZATION_STATEMENT <=>
    !G:real->real^3->real^3^3.
       (!t i j. t IN real_interval[&0,&1] /\
                1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
                ==> smooth_map_on {z:real^3 | ~(z = vec 0)}
                      (\z. lift(G t (inv(norm z) % z)$i$j))) /\
       (!l i j. ALL (\k. 1 <= k /\ k <= 3) l /\
                1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
                ==> (\x:real^(3,1)finite_sum.
                       iterated_partial l
                         (\z. lift(G (drop(sndcart x)) (inv(norm z) % z)$i$j))
                         (fstcart x))
                    continuous_on
                    {x | ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1]}) /\
       (!t y. t IN real_interval[&0,&1] /\ y IN sphere(vec 0,&1)
              ==> transp(G t y) = G t y) /\
       (?c. &0 < c /\
            !t y v. t IN real_interval[&0,&1] /\ y IN sphere(vec 0,&1) /\ v dot y = &0
                    ==> c * (v dot v) <= v dot (G t y ** v))
       ==> ?h:real->real^3->real^3.
             (!t. t IN real_interval[&0,&1]
                  ==> (!y. y IN sphere(vec 0,&1) ==> h t y IN sphere(vec 0,&1)) /\
                      (!x. x IN sphere(vec 0,&1)
                           ==> ?!y. y IN sphere(vec 0,&1) /\ h t y = x) /\
                      smooth_map_on {z:real^3 | ~(z = vec 0)} (\z. h t (inv(norm z) % z)) /\
                      (!y. y IN sphere(vec 0,&1)
                           ==> ?lam. &0 < lam /\
                                     !v w. v dot y = &0 /\ w dot y = &0
                                           ==> (jacobian (\z. h t (inv(norm z) % z)) (at y) ** v)
                                               dot
                                               (G t (h t y) **
                                                (jacobian (\z. h t (inv(norm z) % z)) (at y) **
                                                 w)) =
                                               lam * (v dot w))) /\
             (\x:real^(3,1)finite_sum.
                 h (drop(sndcart x)) (inv(norm(fstcart x)) % fstcart x))
             continuous_on
             {x | ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1]} /\
             (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
                    ==> (\x:real^(3,1)finite_sum.
                           lift(jacobian (\z. h (drop(sndcart x)) (inv(norm z) % z))
                                         (at (fstcart x))$i$j))
                        continuous_on
                        {x | ~(fstcart x = vec 0) /\
                             drop(sndcart x) IN real_interval[&0,&1]}) /\
             (!t. t IN real_interval[&0,&1] /\
                  (?c. !y v w. y IN sphere(vec 0,&1) /\ v dot y = &0 /\ w dot y = &0
                               ==> v dot (G t y ** w) = c * (v dot w))
                  ==> !y. y IN sphere(vec 0,&1) ==> h t y = y)`;;

let BEL_NORMALIZE_HAS_DERIVATIVE = prove
 (`!y:real^N. ~(y = vec 0)
        ==> ((\z. inv(norm z) % z) has_derivative
             (\h. inv(norm y) % h - ((y dot h) / norm y pow 3) % y)) (at y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((lift o (\z:real^N. inv(norm z))) has_derivative
     (lift o (\h. --((y dot h) / norm y pow 3)))) (at y)`
  ASSUME_TAC THENL
   [MP_TAC(INST [`norm(y:real^N) pow 2`,`s:real`]
      (DISCH_ALL(REAL_DIFF_CONV `((\s. inv(sqrt s)) has_real_derivative f') (atreal s)`))) THEN
    ASM_SIMP_TAC[POW_2_SQRT; NORM_POS_LE; REAL_LT_IMP_NZ; REAL_POW_LT] THEN
    REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT] THEN DISCH_TAC THEN
    MP_TAC(ISPEC `y:real^N` HAS_DERIVATIVE_SQNORM_AT) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\x:real^N. lift(norm x pow 2)`;
                   `lift o (\s. inv(sqrt s)) o drop`;
                   `\x:real^N. &2 % lift(y dot x)`;
                   `\x:real^1. (--(&1 * inv(&2 * norm(y:real^N))) / norm y pow 2) % x`;
                   `y:real^N`] DIFF_CHAIN_AT) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP] THEN X_GEN_TAC `x:real^N` THENL
     [SIMP_TAC[POW_2_SQRT; NORM_POS_LE];
      REWRITE_TAC[VECTOR_MUL_ASSOC; GSYM LIFT_CMUL; LIFT_EQ] THEN
      UNDISCH_TAC `&0 < norm(y:real^N)` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z:real^N. inv(norm z)`; `\h:real^N. --((y dot h) / norm y pow 3)`;
                 `\z:real^N. z`; `\h:real^N. h`; `y:real^N`] HAS_DERIVATIVE_MUL_AT) THEN
  ASM_REWRITE_TAC[HAS_DERIVATIVE_ID] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN VECTOR_ARITH_TAC);;

let BEL_NORMALIZE_JAC_TANGENT = prove
 (`!y v:real^N. norm y = &1 /\ v dot y = &0
                ==> jacobian (\z. inv(norm z) % z) (at y) ** v = v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(y:real^N = vec 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `norm(vec 0:real^N) = &1` THEN
    REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP BEL_NORMALIZE_HAS_DERIVATIVE) THEN
  REWRITE_TAC[jacobian] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [has_derivative]) THEN
  ASM_SIMP_TAC[MATRIX_WORKS] THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO; VECTOR_MUL_LZERO; VECTOR_SUB_RZERO;
              REAL_INV_1; VECTOR_MUL_LID]);;

let BEL_ITERATED_PARTIAL_CONST = prove
 (`!l (c:real^N). iterated_partial l (\z:real^M. c) =
                  if l = [] then (\z. c) else (\z. vec 0)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[iterated_partial; NOT_CONS_NIL] THEN
  GEN_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[PARTIAL_DERIVATIVE_ALT; FRECHET_DERIVATIVE_CONST_AT]);;

let CM_D7_HYP_ROUND = prove
 (`(!t i j. t IN real_interval[&0,&1] /\
            1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
            ==> smooth_map_on {z:real^3 | ~(z = vec 0)}
                  (\z. lift((\t:real y:real^3. mat 1:real^3^3) t (inv(norm z) % z)$i$j))) /\
   (!l i j. ALL (\k. 1 <= k /\ k <= 3) l /\
            1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
            ==> (\x:real^(3,1)finite_sum.
                   iterated_partial l
                     (\z. lift((\t:real y:real^3. mat 1:real^3^3) (drop(sndcart x))
                                 (inv(norm z) % z)$i$j))
                     (fstcart x))
                continuous_on
                {x | ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1]}) /\
   (!t y. t IN real_interval[&0,&1] /\ y IN sphere(vec 0,&1)
          ==> transp((\t:real y:real^3. mat 1:real^3^3) t y) =
              (\t:real y:real^3. mat 1:real^3^3) t y) /\
   (?c. &0 < c /\
        !t y v. t IN real_interval[&0,&1] /\ y IN sphere(vec 0,&1) /\ v dot y = &0
                ==> c * (v dot v) <= v dot ((\t:real y:real^3. mat 1:real^3^3) t y ** v))`,
  REWRITE_TAC[SMOOTH_MAP_ON_CONST; BEL_ITERATED_PARTIAL_CONST; TRANSP_MAT;
              MATRIX_VECTOR_MUL_LID] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[CONTINUOUS_ON_CONST];
    EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01; REAL_MUL_LID; REAL_LE_REFL]]);;

let BEL_NORMALIZE_JAC_PARTIAL = prove
 (`!z:real^3 i j. 1 <= j /\ j <= 3
        ==> jacobian (\z. inv(norm z) % z) (at z)$i$j =
            partial_derivative j (\z. inv(norm z) % z) z$i`,
  SIMP_TAC[jacobian; MATRIX_COMPONENT; DIMINDEX_3; partial_derivative]);;

let BEL_FSTCART_NONZERO_CONT = prove
 (`!f:real^3->real^N.
        f continuous_on {z | ~(z = vec 0)}
        ==> (\x:real^(3,1)finite_sum. f(fstcart x)) continuous_on
            {x | ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1]}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^(3,1)finite_sum. (f:real^3->real^N)(fstcart x)) = f o fstcart`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[]);;

let CM_D7_CONCL_ROUND = prove
 (`?h:real->real^3->real^3.
     (!t. t IN real_interval[&0,&1]
          ==> (!y. y IN sphere(vec 0,&1) ==> h t y IN sphere(vec 0,&1)) /\
              (!x. x IN sphere(vec 0,&1)
                   ==> ?!y. y IN sphere(vec 0,&1) /\ h t y = x) /\
              smooth_map_on {z:real^3 | ~(z = vec 0)} (\z. h t (inv(norm z) % z)) /\
              (!y. y IN sphere(vec 0,&1)
                   ==> ?lam. &0 < lam /\
                             !v w. v dot y = &0 /\ w dot y = &0
                                   ==> (jacobian (\z. h t (inv(norm z) % z)) (at y) ** v)
                                       dot
                                       ((mat 1:real^3^3) **
                                        (jacobian (\z. h t (inv(norm z) % z)) (at y) **
                                         w)) =
                                       lam * (v dot w))) /\
     (\x:real^(3,1)finite_sum.
         h (drop(sndcart x)) (inv(norm(fstcart x)) % fstcart x))
     continuous_on
     {x | ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1]} /\
     (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
            ==> (\x:real^(3,1)finite_sum.
                   lift(jacobian (\z. h (drop(sndcart x)) (inv(norm z) % z))
                                 (at (fstcart x))$i$j))
                continuous_on
                {x | ~(fstcart x = vec 0) /\
                     drop(sndcart x) IN real_interval[&0,&1]}) /\
     (!t. t IN real_interval[&0,&1] /\
          (?c. !y v w. y IN sphere(vec 0,&1) /\ v dot y = &0 /\ w dot y = &0
                       ==> v dot ((mat 1:real^3^3) ** w) = c * (v dot w))
          ==> !y. y IN sphere(vec 0,&1) ==> h t y = y)`,
  EXISTS_TAC `\t:real y:real^3. y` THEN REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN REWRITE_TAC[EXISTS_UNIQUE] THEN
      EXISTS_TAC `x:real^3` THEN ASM_SIMP_TAC[];
      REWRITE_TAC[SMOOTH_MAP_ON_NORMALIZE];
      X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_SPHERE_0] THEN DISCH_TAC THEN
      EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01; REAL_MUL_LID; MATRIX_VECTOR_MUL_LID] THEN
      ASM_SIMP_TAC[BEL_NORMALIZE_JAC_TANGENT]];
    MP_TAC(ISPEC `\z:real^3. inv(norm z) % z` BEL_FSTCART_NONZERO_CONT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN REWRITE_TAC[SMOOTH_MAP_ON_NORMALIZE];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[BEL_NORMALIZE_JAC_PARTIAL] THEN
    MP_TAC(ISPEC `\z:real^3. lift(partial_derivative j (\z:real^3. inv(norm z) % z) z$i)`
                 BEL_FSTCART_NONZERO_CONT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN
    REWRITE_TAC[OPEN_NONZERO; SMOOTH_MAP_ON_NORMALIZE]]);;

(* Teeth: for the constant field diag(1,1,4) the identity is not conformal *)
(* at basis 2 (the tangent vectors basis 1 and basis 3 get the factors 1    *)
(* and 4).                                                                   *)

let CM_D7_TEETH = prove
 (`~(?lam. &0 < lam /\
           !v w. v dot basis 2 = &0 /\ w dot basis 2 = &0
                 ==> (jacobian (\z:real^3. inv(norm z) % z) (at (basis 2)) ** v) dot
                     ((lambda i j. if i = j then (if i = 3 then &4 else &1) else &0):real^3^3 **
                      (jacobian (\z:real^3. inv(norm z) % z) (at (basis 2)) ** w)) =
                     lam * (v dot w))`,
  STRIP_TAC THEN
  SUBGOAL_THEN `!v:real^3. v dot basis 2 = &0
                ==> jacobian (\z:real^3. inv(norm z) % z) (at (basis 2)) ** v = v`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC BEL_NORMALIZE_JAC_TANGENT THEN
    ASM_SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(SPECL [`basis 1:real^3`; `basis 1:real^3`] th) THEN
    MP_TAC(SPECL [`basis 3:real^3`; `basis 3:real^3`] th)) THEN
  ASM_SIMP_TAC[DOT_BASIS_BASIS; DIMINDEX_3; ARITH] THEN
  SIMP_TAC[matrix_vector_mul; dot; LAMBDA_BETA; DIMINDEX_3; ARITH; SUM_3;
           BASIS_COMPONENT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The Cauchy transform of a continuous compactly supported                  *)
(* function: definition (normalized to invert d/dzbar, Pompeiu), support     *)
(* predicate, integrability, linearity, translation, a uniform bound in      *)
(* terms of the sup norm, decay at infinity, continuity.                     *)
(* ========================================================================= *)

let bel_ct = new_definition
 `bel_ct (h:complex->complex) (z:complex) =
    --(Cx(inv pi)) * integral (:complex) (\w. h w / (w - z))`;;

let bel_supp = new_definition
 `bel_supp (R:real) (h:complex->complex) <=> !w. R < norm w ==> h w = Cx(&0)`;;

let BEL_SUPP_BOUNDED = prove
 (`!R h. bel_supp R h ==> bounded (support (+) h (:complex))`,
  REWRITE_TAC[bel_supp; support; NEUTRAL_VECTOR_ADD; IN_UNIV] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BOUNDED_SUBSET THEN
  EXISTS_TAC `cball(Cx(&0),R)` THEN REWRITE_TAC[BOUNDED_CBALL] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_CBALL; dist; COMPLEX_SUB_LZERO; NORM_NEG] THEN
  X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  UNDISCH_TAC `~((h:complex->complex) w = vec 0)` THEN
  ASM_SIMP_TAC[COMPLEX_VEC_0]);;

let BEL_SUPP_MONO = prove
 (`!R R' h. bel_supp R h /\ R <= R' ==> bel_supp R' h`,
  REWRITE_TAC[bel_supp] THEN MESON_TAC[REAL_LET_TRANS]);;

let BEL_SUPP_ZERO = prove
 (`!R. bel_supp R (\w. Cx(&0))`,
  REWRITE_TAC[bel_supp]);;

let BEL_CT_INTEGRABLE = prove
 (`!R h z. h continuous_on (:complex) /\ bel_supp R h
           ==> (\w. h w / (w - z)) absolutely_integrable_on (:complex)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CAUCHY_KERNEL_ABSOLUTELY_INTEGRABLE THEN
  ASM_MESON_TAC[BEL_SUPP_BOUNDED]);;

let BEL_SUPP_ADD = prove
 (`!R h1 h2. bel_supp R h1 /\ bel_supp R h2 ==> bel_supp R (\w. h1 w + h2 w)`,
  SIMP_TAC[bel_supp; COMPLEX_ADD_LID]);;

let BEL_SUPP_SUB = prove
 (`!R h1 h2. bel_supp R h1 /\ bel_supp R h2 ==> bel_supp R (\w. h1 w - h2 w)`,
  SIMP_TAC[bel_supp; COMPLEX_SUB_REFL]);;

let BEL_SUPP_LMUL = prove
 (`!R c h. bel_supp R h ==> bel_supp R (\w. c * h w)`,
  SIMP_TAC[bel_supp; COMPLEX_MUL_RZERO]);;

let BEL_SUPP_MUL = prove
 (`!R g h. bel_supp R h ==> bel_supp R (\w. g w * h w)`,
  SIMP_TAC[bel_supp; COMPLEX_MUL_RZERO]);;

let BEL_CT_ADD = prove
 (`!R h1 h2 z.
        h1 continuous_on (:complex) /\ bel_supp R h1 /\
        h2 continuous_on (:complex) /\ bel_supp R h2
        ==> bel_ct (\w. h1 w + h2 w) z = bel_ct h1 z + bel_ct h2 z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bel_ct; GSYM COMPLEX_ADD_LDISTRIB] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[complex_div; COMPLEX_ADD_RDISTRIB] THEN
  REWRITE_TAC[GSYM complex_div] THEN
  MATCH_MP_TAC INTEGRAL_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  MATCH_MP_TAC BEL_CT_INTEGRABLE THEN EXISTS_TAC `R:real` THEN ASM_REWRITE_TAC[]);;

let BEL_CT_SUB = prove
 (`!R h1 h2 z.
        h1 continuous_on (:complex) /\ bel_supp R h1 /\
        h2 continuous_on (:complex) /\ bel_supp R h2
        ==> bel_ct (\w. h1 w - h2 w) z = bel_ct h1 z - bel_ct h2 z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bel_ct; GSYM COMPLEX_SUB_LDISTRIB] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[complex_div; COMPLEX_SUB_RDISTRIB] THEN
  REWRITE_TAC[GSYM complex_div] THEN
  MATCH_MP_TAC INTEGRAL_SUB THEN CONJ_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  MATCH_MP_TAC BEL_CT_INTEGRABLE THEN EXISTS_TAC `R:real` THEN ASM_REWRITE_TAC[]);;

let BEL_CT_LMUL = prove
 (`!R c h z.
        h continuous_on (:complex) /\ bel_supp R h
        ==> bel_ct (\w. c * h w) z = c * bel_ct h z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bel_ct] THEN
  REWRITE_TAC[complex_div; GSYM COMPLEX_MUL_ASSOC] THEN
  REWRITE_TAC[GSYM complex_div] THEN
  MP_TAC(BETA_RULE(ISPECL [`\w. (h:complex->complex) w / (w - z)`; `(:complex)`; `c:complex`]
                INTEGRAL_COMPLEX_LMUL)) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC BEL_CT_INTEGRABLE THEN EXISTS_TAC `R:real` THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN CONV_TAC COMPLEX_RING]);;

let BEL_CT_SHIFT = prove
 (`!h z d. bel_ct h (z + d) = bel_ct (\w. h(w + d)) z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bel_ct] THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`\w:complex. (h:complex->complex) w / (w - (z + d))`;
                 `(:complex)`; `d:complex`] INTEGRAL_TRANSLATION) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `IMAGE (\x:complex. d + x) (:complex) = (:complex)` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN X_GEN_TAC `y:complex` THEN
    EXISTS_TAC `y - d:complex` THEN CONV_TAC COMPLEX_RING;
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `w:complex` THEN
  REWRITE_TAC[COMPLEX_ADD_SYM] THEN
  AP_TERM_TAC THEN CONV_TAC COMPLEX_RING);;

(* The Cauchy kernel is uniformly integrable over a fixed disc.             *)

let BEL_BALL_TRANSLATE = prove
 (`!a c:complex r. IMAGE (\x. a + x) (ball(c,r)) = ball(a + c,r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_BALL] THEN
  X_GEN_TAC `y:complex` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:complex` (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
    REWRITE_TAC[dist] THEN
    MATCH_MP_TAC(REAL_ARITH `a = b ==> a < r ==> b < r`) THEN
    AP_TERM_TAC THEN VECTOR_ARITH_TAC;
    DISCH_TAC THEN EXISTS_TAC `y - a:complex` THEN
    CONJ_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `dist(a + c:complex,y) < r` THEN REWRITE_TAC[dist] THEN
    MATCH_MP_TAC(REAL_ARITH `a = b ==> a < r ==> b < r`) THEN
    AP_TERM_TAC THEN VECTOR_ARITH_TAC]);;

let BEL_KERNEL_INTEGRABLE_BALL = prove
 (`!c:complex r z. (\y. lift(norm(inv(y - z)))) integrable_on ball(c,r)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`ball(c:complex,r)`; `z:complex`] INV_ABSOLUTELY_INTEGRABLE_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_BALL; MEASURABLE_BALL] THEN
  SIMP_TAC[absolutely_integrable_on]);;

let BEL_KERNEL0_INTEGRABLE_BALL = prove
 (`!c:complex r. (\y. lift(norm(inv y))) integrable_on ball(c,r)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`c:complex`; `r:real`; `Cx(&0)`] BEL_KERNEL_INTEGRABLE_BALL) THEN
  REWRITE_TAC[COMPLEX_SUB_RZERO]);;

let BEL_KERNEL_BALL_BOUND = prove
 (`!R. &0 < R
       ==> ?C. &0 <= C /\
               !z. drop(integral (ball(Cx(&0),R)) (\y. lift(norm(inv(y - z))))) <= C`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `I3 = drop(integral (ball(Cx(&0),&3 * R)) (\y. lift(norm(inv y))))` THEN
  EXISTS_TAC `max I3 (measure(ball(Cx(&0),R)) / R)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= b ==> &0 <= max a b`) THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[MEASURE_POS_LE; MEASURABLE_BALL; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  X_GEN_TAC `z:complex` THEN
  ASM_CASES_TAC `norm(z:complex) <= &2 * R` THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= a ==> x <= max a b`) THEN EXPAND_TAC "I3" THEN
    MP_TAC(ISPECL [`\v:complex. lift(norm(inv v))`; `ball(Cx(&0),R)`;
                   `--z:complex`] INTEGRAL_TRANSLATION) THEN
    REWRITE_TAC[BEL_BALL_TRANSLATE; COMPLEX_ADD_RID] THEN
    REWRITE_TAC[COMPLEX_RING `--z + y:complex = y - z`] THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
    REWRITE_TAC[BEL_KERNEL0_INTEGRABLE_BALL; LIFT_DROP; NORM_POS_LE] THEN
    REWRITE_TAC[SUBSET; IN_BALL; dist; COMPLEX_SUB_LZERO; NORM_NEG] THEN
    X_GEN_TAC `y:complex` THEN
    MP_TAC(ISPECL [`--z - y:complex`; `z:complex`] NORM_TRIANGLE) THEN
    REWRITE_TAC[COMPLEX_RING `(--z - y) + z:complex = --y`; NORM_NEG] THEN
    UNDISCH_TAC `norm(z:complex) <= &2 * R` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= b ==> x <= max a b`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (ball(Cx(&0),R)) (\y:complex. lift(inv R)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN
    REWRITE_TAC[BEL_KERNEL_INTEGRABLE_BALL; INTEGRABLE_ON_CONST; MEASURABLE_BALL] THEN
    REWRITE_TAC[LIFT_DROP; IN_BALL; dist; COMPLEX_SUB_LZERO; NORM_NEG; COMPLEX_NORM_INV] THEN
    X_GEN_TAC `y:complex` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`z:complex`; `y:complex`] NORM_TRIANGLE_SUB) THEN
    MP_TAC(ISPECL [`z:complex`; `y:complex`] NORM_SUB) THEN
    UNDISCH_TAC `~(norm(z:complex) <= &2 * R)` THEN
    UNDISCH_TAC `norm(y:complex) < R` THEN REAL_ARITH_TAC;
    SIMP_TAC[INTEGRAL_CONST_GEN; MEASURABLE_BALL; DROP_CMUL; LIFT_DROP; real_div;
             REAL_LE_REFL]]);;

(* Restriction of the Cauchy integral to a disc containing the support.     *)

let BEL_CT_INTEGRAND_RESTRICT = prove
 (`!R R' h z. bel_supp R h /\ R < R'
              ==> (\w. h w / (w - z)) =
                  (\w. if w IN ball(Cx(&0),R') then h w / (w - z) else vec 0)`,
  REWRITE_TAC[bel_supp; FUN_EQ_THM; IN_BALL; dist; COMPLEX_SUB_LZERO; NORM_NEG] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `w:complex` THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `(h:complex->complex) w = Cx(&0)` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[complex_div; COMPLEX_MUL_LZERO; COMPLEX_VEC_0]]);;

let BEL_CT_RESTRICT_BALL = prove
 (`!R R' h z. bel_supp R h /\ R < R'
              ==> integral (:complex) (\w. h w / (w - z)) =
                  integral (ball(Cx(&0),R')) (\w. h w / (w - z))`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM INTEGRAL_RESTRICT_UNIV] THEN
  AP_TERM_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC BEL_CT_INTEGRAND_RESTRICT THEN
  EXISTS_TAC `R:real` THEN ASM_REWRITE_TAC[]);;

let BEL_CT_INTEGRABLE_BALL = prove
 (`!R R' h z. h continuous_on (:complex) /\ bel_supp R h /\ R < R'
              ==> (\w. h w / (w - z)) integrable_on ball(Cx(&0),R')`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM INTEGRABLE_RESTRICT_UNIV] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP BEL_CT_INTEGRAND_RESTRICT
                                       (CONJ (ASSUME `bel_supp R h`) th))]) THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  MATCH_MP_TAC BEL_CT_INTEGRABLE THEN EXISTS_TAC `R:real` THEN ASM_REWRITE_TAC[]);;

(* A uniform bound: |C h| <= C sup|h| for h supported in a fixed disc.      *)

let BEL_CT_BOUND = prove
 (`!R. ?C. &0 <= C /\
           !h M z. h continuous_on (:complex) /\ bel_supp R h /\ (!w. norm(h w) <= M)
                   ==> norm(bel_ct h z) <= C * M`,
  GEN_TAC THEN
  MP_TAC(SPEC `abs R + &1` BEL_KERNEL_BALL_BOUND) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `inv pi * C0` THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_INV_EQ; REAL_LT_IMP_LE; PI_POS] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
   [ASM_MESON_TAC[NORM_POS_LE; REAL_LE_TRANS]; ALL_TAC] THEN
  REWRITE_TAC[bel_ct; COMPLEX_NORM_MUL; NORM_NEG; COMPLEX_NORM_CX] THEN
  REWRITE_TAC[REAL_ABS_INV; REAL_ABS_PI] THEN
  MP_TAC(ISPECL [`R:real`; `abs R + &1`; `h:complex->complex`; `z:complex`]
                BEL_CT_RESTRICT_BALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE; PI_POS] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (ball(Cx(&0),abs R + &1))
                            (\w. M % lift(norm(inv(w - z)))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
    SIMP_TAC[INTEGRABLE_CMUL; BEL_KERNEL_INTEGRABLE_BALL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC BEL_CT_INTEGRABLE_BALL THEN EXISTS_TAC `R:real` THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
      REWRITE_TAC[DROP_CMUL; LIFT_DROP; complex_div; COMPLEX_NORM_MUL] THEN
      ASM_SIMP_TAC[REAL_LE_RMUL; NORM_POS_LE]];
    ASM_SIMP_TAC[INTEGRAL_CMUL; BEL_KERNEL_INTEGRABLE_BALL; DROP_CMUL] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]]);;

(* Decay at infinity: |C h(z)| = O(1/|z|).                                  *)

let BEL_CT_DECAY = prove
 (`!R h M z. h continuous_on (:complex) /\ bel_supp R h /\ (!w. norm(h w) <= M) /\
             &2 * (abs R + &1) <= norm z
             ==> norm(bel_ct h z) <=
                 &2 * inv pi * M * measure(ball(Cx(&0),abs R + &1)) / norm z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
   [ASM_MESON_TAC[NORM_POS_LE; REAL_LE_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(z:complex)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[bel_ct; COMPLEX_NORM_MUL; NORM_NEG; COMPLEX_NORM_CX] THEN
  REWRITE_TAC[REAL_ABS_INV; REAL_ABS_PI] THEN
  MP_TAC(ISPECL [`R:real`; `abs R + &1`; `h:complex->complex`; `z:complex`]
                BEL_CT_RESTRICT_BALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv pi * drop(integral (ball(Cx(&0),abs R + &1))
                                     (\w:complex. lift(M * (&2 / norm(z:complex)))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE; PI_POS] THEN
    MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
    REWRITE_TAC[INTEGRABLE_ON_CONST; MEASURABLE_BALL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC BEL_CT_INTEGRABLE_BALL THEN EXISTS_TAC `R:real` THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      X_GEN_TAC `w:complex` THEN REWRITE_TAC[IN_BALL; dist; COMPLEX_SUB_LZERO; NORM_NEG] THEN
      DISCH_TAC THEN REWRITE_TAC[LIFT_DROP; complex_div; COMPLEX_NORM_MUL; COMPLEX_NORM_INV] THEN
      SUBGOAL_THEN `norm(z:complex) / &2 <= norm(w - z:complex)` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`z:complex`; `w:complex`] NORM_TRIANGLE_SUB) THEN
        MP_TAC(ISPECL [`z:complex`; `w:complex`] NORM_SUB) THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE; REAL_LE_INV_EQ] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(norm(z:complex) / &2)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_INV_DIV; REAL_LE_REFL]]];
    SIMP_TAC[INTEGRAL_CONST_GEN; MEASURABLE_BALL; DROP_CMUL; LIFT_DROP] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC]);;

(* Uniform continuity and boundedness of continuous compactly supported     *)
(* functions; translates.                                                    *)

let BEL_SUPP_UNIFORMLY_CONTINUOUS = prove
 (`!R h. h continuous_on (:complex) /\ bel_supp R h
         ==> h uniformly_continuous_on (:complex)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:complex->complex`; `cball(Cx(&0),abs R + &1)`]
                COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_CBALL] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[uniformly_continuous_on; IN_UNIV] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d (&1)` THEN ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LT_01] THEN
  MAP_EVERY X_GEN_TAC [`x:complex`; `y:complex`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `x IN cball(Cx(&0),abs R + &1) /\ y IN cball(Cx(&0),abs R + &1)` THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `R < norm(x:complex) /\ R < norm(y:complex)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(x IN cball(Cx(&0),abs R + &1) /\ y IN cball(Cx(&0),abs R + &1))` THEN
    UNDISCH_TAC `dist(y:complex,x) < &1` THEN
    REWRITE_TAC[IN_CBALL; dist; COMPLEX_SUB_LZERO; NORM_NEG] THEN
    MP_TAC(ISPECL [`x:complex`; `y:complex`] NORM_TRIANGLE_SUB) THEN
    MP_TAC(ISPECL [`y:complex`; `x:complex`] NORM_TRIANGLE_SUB) THEN
    MP_TAC(ISPECL [`x:complex`; `y:complex`] NORM_SUB) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `bel_supp R h` THEN REWRITE_TAC[bel_supp] THEN
  DISCH_THEN(fun th -> ASM_SIMP_TAC[th]) THEN ASM_REWRITE_TAC[DIST_REFL]);;

let BEL_SUPP_BOUNDED_FN = prove
 (`!R h. h continuous_on (:complex) /\ bel_supp R h ==> ?M. !w. norm(h w) <= M`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:complex->complex`; `cball(Cx(&0),abs R)`] COMPACT_CONTINUOUS_IMAGE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_CBALL] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `B:real` THEN X_GEN_TAC `w:complex` THEN
  ASM_CASES_TAC `w IN cball(Cx(&0),abs R)` THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `(h:complex->complex) w = Cx(&0)` SUBST1_TAC THENL
   [UNDISCH_TAC `bel_supp R h` THEN REWRITE_TAC[bel_supp] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `~(w IN cball(Cx(&0),abs R))` THEN
    REWRITE_TAC[IN_CBALL; dist; COMPLEX_SUB_LZERO; NORM_NEG] THEN REAL_ARITH_TAC;
    REWRITE_TAC[COMPLEX_NORM_0] THEN ASM_REAL_ARITH_TAC]);;

let BEL_TRANSLATE_CONTINUOUS = prove
 (`!(h:complex->complex) d. h continuous_on (:complex)
         ==> (\w. h(w + d)) continuous_on (:complex)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[COMPLEX_ADD_SYM] THEN
  MATCH_MP_TAC CONTINUOUS_ON_TRANSLATE_UNIV THEN ASM_REWRITE_TAC[]);;

let BEL_SUPP_TRANSLATE = prove
 (`!R h d. bel_supp R h ==> bel_supp (R + norm d) (\w. h(w + d))`,
  REWRITE_TAC[bel_supp] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`w:complex`; `--d:complex`] NORM_TRIANGLE_SUB) THEN
  REWRITE_TAC[NORM_NEG; COMPLEX_SUB_RNEG] THEN ASM_REAL_ARITH_TAC);;

let BEL_FRAC_LT = prove
 (`!C e. &0 <= C /\ &0 < e ==> C * (e / (C + &1)) < e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `C * (e / (C + &1)) = e - e / (C + &1)` SUBST1_TAC THENL
   [SUBGOAL_THEN `~(C + &1 = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> e - x < e`) THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC]);;

let BEL_CT_CONTINUOUS = prove
 (`!R h. h continuous_on (:complex) /\ bel_supp R h
         ==> (bel_ct h) continuous_on (:complex)`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV] THEN
  X_GEN_TAC `z:complex` THEN REWRITE_TAC[continuous_at] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `abs R + &1` BEL_CT_BOUND) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`R:real`; `h:complex->complex`] BEL_SUPP_UNIFORMLY_CONTINUOUS) THEN
  ASM_REWRITE_TAC[uniformly_continuous_on; IN_UNIV] THEN
  DISCH_THEN(MP_TAC o SPEC `e / (C + &1)`) THEN
  ANTS_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d (&1)` THEN ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LT_01] THEN
  X_GEN_TAC `y:complex` THEN STRIP_TAC THEN
  SUBGOAL_THEN `bel_ct h y = bel_ct h (z + (y - z))` SUBST1_TAC THENL
   [AP_TERM_TAC THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  REWRITE_TAC[BEL_CT_SHIFT; dist] THEN
  SUBGOAL_THEN `norm(y - z:complex) < &1` ASSUME_TAC THENL
   [ASM_MESON_TAC[dist]; ALL_TAC] THEN
  MP_TAC(ISPECL [`abs R + &1`; `\w:complex. (h:complex->complex)(w + (y - z))`;
                 `h:complex->complex`; `z:complex`] BEL_CT_SUB) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[BEL_TRANSLATE_CONTINUOUS] THEN CONJ_TAC THEN
    MATCH_MP_TAC BEL_SUPP_MONO THENL
     [EXISTS_TAC `R + norm(y - z:complex)` THEN ASM_SIMP_TAC[BEL_SUPP_TRANSLATE] THEN
      ASM_REAL_ARITH_TAC;
      EXISTS_TAC `R:real` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `C * (e / (C + &1))` THEN
  ASM_SIMP_TAC[BEL_FRAC_LT] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_SIMP_TAC[BEL_TRANSLATE_CONTINUOUS; ETA_AX];
    MATCH_MP_TAC BEL_SUPP_SUB THEN CONJ_TAC THEN
    MATCH_MP_TAC BEL_SUPP_MONO THENL
     [EXISTS_TAC `R + norm(y - z:complex)` THEN ASM_SIMP_TAC[BEL_SUPP_TRANSLATE] THEN
      ASM_REAL_ARITH_TAC;
      EXISTS_TAC `R:real` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    X_GEN_TAC `w:complex` THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[GSYM dist] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[dist; COMPLEX_RING `(w + (y - z)) - w:complex = y - z`] THEN
    ASM_MESON_TAC[dist]]);;

(* The Cauchy transform tends to zero at infinity.                           *)

let BEL_CT_LIM_INFINITY = prove
 (`!R h. h continuous_on (:complex) /\ bel_supp R h
         ==> ((bel_ct h) --> Cx(&0)) at_infinity`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`R:real`; `h:complex->complex`] BEL_SUPP_BOUNDED_FN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `M:real`) THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
   [ASM_MESON_TAC[NORM_POS_LE; REAL_LE_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &2 * inv pi * M * measure(ball(Cx(&0),abs R + &1))` MP_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; REAL_LE_INV_EQ; PI_POS_LE; MEASURE_POS_LE; MEASURABLE_BALL];
    ALL_TAC] THEN
  ABBREV_TAC `K = &2 * inv pi * M * measure(ball(Cx(&0),abs R + &1))` THEN
  DISCH_TAC THEN
  REWRITE_TAC[LIM_AT_INFINITY; GSYM COMPLEX_VEC_0; DIST_0] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  EXISTS_TAC `max (&2 * (abs R + &1)) (K / e + &1)` THEN
  X_GEN_TAC `z:complex` THEN REWRITE_TAC[real_ge; REAL_MAX_LE] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`R:real`; `h:complex->complex`; `M:real`; `z:complex`] BEL_CT_DECAY) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < norm(z:complex)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `b < e ==> x <= b ==> x < e`) THEN
  REWRITE_TAC[REAL_ARITH `&2 * inv pi * M * m / n = (&2 * inv pi * M * m) / n`] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
  SUBGOAL_THEN `K / e < norm(z:complex)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Derivatives of the Cauchy transform.  For h of class C^1                  *)
(* with compact support, C h is differentiable with D(C h)(z) v =           *)
(* C(Dh(.) v)(z) (uniform first-order Taylor bound and the uniform bound    *)
(* above); hence C maps smooth compactly supported functions to smooth      *)
(* functions, commutes with partial derivatives, and (Pompeiu, green.ml)    *)
(* d/dzbar (C h) = h.  The Beurling transform S h := C(h_z) = (C h)_z.      *)
(* ========================================================================= *)

let bel_c1 = new_definition
 `bel_c1 (h:complex->complex) <=>
    h differentiable_on (:complex) /\
    (!v. (\w. frechet_derivative h (at w) v) continuous_on (:complex))`;;

let BEL_C1_HAS_DERIVATIVE = prove
 (`!h w. bel_c1 h ==> (h has_derivative frechet_derivative h (at w)) (at w)`,
  REWRITE_TAC[bel_c1] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
  MATCH_MP_TAC DIFFERENTIABLE_ON_IMP_DIFFERENTIABLE_AT THEN
  EXISTS_TAC `(:complex)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV]);;

let BEL_C1_LINEAR = prove
 (`!h w. bel_c1 h ==> linear(frechet_derivative h (at w))`,
  MESON_TAC[BEL_C1_HAS_DERIVATIVE; has_derivative]);;

let BEL_C1_CONTINUOUS = prove
 (`!h. bel_c1 h ==> h continuous_on (:complex)`,
  SIMP_TAC[bel_c1; DIFFERENTIABLE_IMP_CONTINUOUS_ON]);;

let BEL_SMOOTH_C1 = prove
 (`!h. smooth_map_on (:complex) h ==> bel_c1 h`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bel_c1] THEN CONJ_TAC THENL
   [REWRITE_TAC[differentiable_on] THEN X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
    MATCH_MP_TAC DIFFERENTIABLE_AT_WITHIN THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(:complex)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[OPEN_UNIV]]);;

let BEL_SUPP_FRECHET = prove
 (`!R h v. h differentiable_on (:complex) /\ bel_supp R h
           ==> bel_supp R (\w. frechet_derivative h (at w) v)`,
  REWRITE_TAC[bel_supp] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN MATCH_MP_TAC FRECHET_DERIVATIVE_ZERO_OUTSIDE THEN
  EXISTS_TAC `R:real` THEN ASM_SIMP_TAC[COMPLEX_VEC_0]);;

let BEL_C1_SUPP_FRECHET = prove
 (`!R h v. bel_c1 h /\ bel_supp R h
           ==> bel_supp R (\w. frechet_derivative h (at w) v)`,
  SIMP_TAC[bel_c1; BEL_SUPP_FRECHET]);;

let BEL_LINEAR_EXPAND = prove
 (`!L:complex->complex x.
        linear L ==> L x = Cx(Re x) * L(Cx(&1)) + Cx(Im x) * L ii`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [COMPLEX_EXPAND] THEN
  SUBGOAL_THEN `Cx(Re x) + ii * Cx(Im x) = Re x % Cx(&1) + Im x % ii` SUBST1_TAC THENL
   [REWRITE_TAC[COMPLEX_CMUL] THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th; MATCH_MP LINEAR_CMUL th]) THEN
  REWRITE_TAC[COMPLEX_CMUL]);;

(* The difference of two linear maps of the plane is bounded in terms of     *)
(* the differences on the basis 1, ii.                                      *)

let BEL_LINEAR_DIFF_BOUND = prove
 (`!L1 L2:complex->complex x e.
        linear L1 /\ linear L2 /\
        norm(L1(Cx(&1)) - L2(Cx(&1))) <= e / &2 /\ norm(L1 ii - L2 ii) <= e / &2
        ==> norm(L1 x - L2 x) <= e * norm x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L1:complex->complex`; `x:complex`] BEL_LINEAR_EXPAND) THEN
  MP_TAC(ISPECL [`L2:complex->complex`; `x:complex`] BEL_LINEAR_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[COMPLEX_RING
   `(Cx a * p + Cx b * q) - (Cx a * r + Cx b * s) =
    Cx a * (p - r) + Cx b * (q - s)`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs(Re x) * norm(L1(Cx(&1)) - L2(Cx(&1)):complex) +
              abs(Im x) * norm(L1 ii - L2 ii:complex)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `norm(a + b:complex) <= norm a + norm b /\
                             norm a = x /\ norm b = y ==> norm(a + b) <= x + y`) THEN
    REWRITE_TAC[NORM_TRIANGLE; COMPLEX_NORM_MUL; COMPLEX_NORM_CX];
    MP_TAC(SPEC `x:complex` COMPLEX_NORM_GE_RE_IM) THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(x:complex) * (e / &2) + norm(x:complex) * (e / &2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE];
      REAL_ARITH_TAC]]);;

(* Uniform first-order Taylor bound for C^1 functions with compact support. *)

let BEL_UNIFORM_TAYLOR = prove
 (`!R h. bel_c1 h /\ bel_supp R h
         ==> !e. &0 < e
                 ==> ?d. &0 < d /\
                         !w v. norm v < d
                               ==> norm(h(w + v) - h w - frechet_derivative h (at w) v)
                                   <= e * norm v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!v. (\w. frechet_derivative (h:complex->complex) (at w) v)
        uniformly_continuous_on (:complex)`
  MP_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC BEL_SUPP_UNIFORMLY_CONTINUOUS THEN
    EXISTS_TAC `R:real` THEN
    ASM_MESON_TAC[bel_c1; BEL_SUPP_FRECHET];
    ALL_TAC] THEN
  REWRITE_TAC[uniformly_continuous_on; IN_UNIV] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`Cx(&1)`; `e / &2`]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ii`; `e / &2`]) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d1 d2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MAP_EVERY X_GEN_TAC [`w:complex`; `v:complex`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\u:complex. (h:complex->complex)(u + w) - frechet_derivative h (at w) u`;
    `\u:complex x:complex. frechet_derivative (h:complex->complex) (at (u + w)) x -
                           frechet_derivative h (at w) x`;
    `ball(vec 0:complex,min d1 d2)`; `e:real`] DIFFERENTIABLE_BOUND) THEN
  REWRITE_TAC[CONVEX_BALL] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `u:complex` THEN DISCH_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
      MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN CONJ_TAC THENL
       [MATCH_MP_TAC HAS_DERIVATIVE_TRANSLATION THEN
        ASM_SIMP_TAC[BEL_C1_HAS_DERIVATIVE; ETA_AX];
        MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN ASM_SIMP_TAC[BEL_C1_LINEAR; ETA_AX]];
      X_GEN_TAC `u:complex` THEN REWRITE_TAC[IN_BALL; dist; VECTOR_SUB_LZERO; NORM_NEG] THEN
      DISCH_TAC THEN
      MP_TAC(ISPEC `\x:complex. frechet_derivative (h:complex->complex) (at (u + w)) x -
                                frechet_derivative h (at w) x` ONORM) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC LINEAR_COMPOSE_SUB THEN ASM_SIMP_TAC[BEL_C1_LINEAR; ETA_AX];
        ALL_TAC] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN X_GEN_TAC `x:complex` THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC BEL_LINEAR_DIFF_BOUND THEN
      ASM_SIMP_TAC[BEL_C1_LINEAR; ETA_AX] THEN
      CONJ_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[GSYM dist] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[dist; COMPLEX_RING `(u + w) - w:complex = u`] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`v:complex`; `vec 0:complex`]) THEN
  REWRITE_TAC[IN_BALL; dist; VECTOR_SUB_LZERO; VECTOR_SUB_RZERO; NORM_NEG; NORM_0;
              REAL_LT_MIN; VECTOR_ADD_LID] THEN
  ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`h:complex->complex`; `w:complex`] BEL_C1_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP LINEAR_0 th]) THEN
  SUBGOAL_THEN `v + w:complex = w + v` SUBST1_TAC THENL
   [CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> a <= x ==> b <= x`) THEN
  AP_TERM_TAC THEN VECTOR_ARITH_TAC);;

(* Linearity in v of v |-> C(Dh(.) v)(z).                                    *)

let BEL_C1_FRECHET_CONTINUOUS = prove
 (`!h v. bel_c1 h ==> (\w. frechet_derivative h (at w) v) continuous_on (:complex)`,
  SIMP_TAC[bel_c1]);;

let BEL_CT_FRECHET_LINEAR = prove
 (`!R h z. bel_c1 h /\ bel_supp R h
           ==> linear (\v. bel_ct (\w. frechet_derivative h (at w) v) z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[linear] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:complex`; `y:complex`] THEN
    SUBGOAL_THEN
     `(\w. frechet_derivative (h:complex->complex) (at w) (x + y)) =
      (\w. frechet_derivative h (at w) x + frechet_derivative h (at w) y)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `w:complex` THEN
      MATCH_MP_TAC LINEAR_ADD THEN ASM_SIMP_TAC[BEL_C1_LINEAR];
      ALL_TAC] THEN
    MATCH_MP_TAC BEL_CT_ADD THEN EXISTS_TAC `R:real` THEN
    ASM_SIMP_TAC[BEL_C1_FRECHET_CONTINUOUS] THEN
    ASM_MESON_TAC[BEL_SUPP_FRECHET; bel_c1];
    MAP_EVERY X_GEN_TAC [`c:real`; `x:complex`] THEN
    SUBGOAL_THEN
     `(\w. frechet_derivative (h:complex->complex) (at w) (c % x)) =
      (\w. Cx c * frechet_derivative h (at w) x)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `w:complex` THEN
      REWRITE_TAC[GSYM COMPLEX_CMUL] THEN
      MATCH_MP_TAC LINEAR_CMUL THEN ASM_SIMP_TAC[BEL_C1_LINEAR];
      ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_CMUL] THEN
    MATCH_MP_TAC BEL_CT_LMUL THEN EXISTS_TAC `R:real` THEN
    ASM_SIMP_TAC[BEL_C1_FRECHET_CONTINUOUS] THEN
    ASM_MESON_TAC[BEL_SUPP_FRECHET; bel_c1]]);;

(* The derivative of the Cauchy transform.                                    *)

let BEL_CT_HAS_DERIVATIVE = prove
 (`!R h z. bel_c1 h /\ bel_supp R h
           ==> (bel_ct h has_derivative
                (\v. bel_ct (\w. frechet_derivative h (at w) v) z)) (at z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_DERIVATIVE_AT_ALT] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[BEL_CT_FRECHET_LINEAR]; ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `abs R + &1` BEL_CT_BOUND) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`R:real`; `h:complex->complex`] BEL_UNIFORM_TAYLOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e / (C + &1)`) THEN
  ANTS_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d (&1)` THEN ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LT_01] THEN
  X_GEN_TAC `y:complex` THEN STRIP_TAC THEN
  ABBREV_TAC `v:complex = y - z` THEN
  SUBGOAL_THEN `y:complex = z + v` SUBST1_TAC THENL
   [EXPAND_TAC "v" THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  REWRITE_TAC[BEL_CT_SHIFT] THEN
  SUBGOAL_THEN `bel_supp (abs R + &1) (h:complex->complex) /\
                bel_supp (abs R + &1) (\w. h(w + v)) /\
                bel_supp (abs R + &1) (\w. frechet_derivative h (at w) v)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC BEL_SUPP_MONO THENL
     [EXISTS_TAC `R:real` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      EXISTS_TAC `R + norm(v:complex)` THEN ASM_SIMP_TAC[BEL_SUPP_TRANSLATE] THEN
      ASM_REAL_ARITH_TAC;
      EXISTS_TAC `R:real` THEN CONJ_TAC THENL
       [ASM_MESON_TAC[BEL_SUPP_FRECHET; bel_c1]; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:complex->complex) continuous_on (:complex) /\
                (\w. h(w + v)) continuous_on (:complex) /\
                (\w. frechet_derivative h (at w) v) continuous_on (:complex)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[BEL_C1_CONTINUOUS; BEL_TRANSLATE_CONTINUOUS; BEL_C1_FRECHET_CONTINUOUS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`abs R + &1`; `\w:complex. (h:complex->complex)(w + v)`;
                 `h:complex->complex`; `z:complex`] BEL_CT_SUB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`abs R + &1`; `\w:complex. (h:complex->complex)(w + v) - h w`;
                 `\w:complex. frechet_derivative (h:complex->complex) (at w) v`;
                 `z:complex`] BEL_CT_SUB) THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_SUB; BEL_SUPP_SUB; ETA_AX] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C * (e / (C + &1) * norm(v:complex))` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC) THEN
      ASM_REWRITE_TAC[ETA_AX];
      REPEAT(MATCH_MP_TAC BEL_SUPP_SUB THEN CONJ_TAC) THEN ASM_REWRITE_TAC[ETA_AX];
      X_GEN_TAC `w:complex` THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN EXPAND_TAC "v" THEN ASM_MESON_TAC[dist; NORM_SUB]];
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[NORM_POS_LE] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    ASM_SIMP_TAC[GSYM REAL_MUL_ASSOC; BEL_FRAC_LT]]);;

let BEL_CT_FRECHET = prove
 (`!R h z v. bel_c1 h /\ bel_supp R h
             ==> frechet_derivative (bel_ct h) (at z) v =
                 bel_ct (\w. frechet_derivative h (at w) v) z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`R:real`; `h:complex->complex`; `z:complex`] BEL_CT_HAS_DERIVATIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[]);;

let BEL_SMOOTH_SUPP_FRECHET = prove
 (`!R h v. smooth_map_on (:complex) h /\ bel_supp R h
           ==> smooth_map_on (:complex) (\w. frechet_derivative h (at w) v) /\
               bel_supp R (\w. frechet_derivative h (at w) v)`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[OPEN_UNIV];
    MATCH_MP_TAC BEL_SUPP_FRECHET THEN ASM_MESON_TAC[BEL_SMOOTH_C1; bel_c1]]);;

let BEL_CT_CONTINUOUSLY_DIFFERENTIABLE = prove
 (`!n R h. smooth_map_on (:complex) h /\ bel_supp R h
           ==> continuously_differentiable n (:complex) (bel_ct h)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC BEL_CT_CONTINUOUS THEN EXISTS_TAC `R:real` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS];
    REPEAT STRIP_TAC THEN REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_UNIV] THEN
    EXISTS_TAC `\z v. bel_ct (\w. frechet_derivative (h:complex->complex) (at w) v) z` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC BEL_CT_HAS_DERIVATIVE THEN EXISTS_TAC `R:real` THEN
      ASM_SIMP_TAC[BEL_SMOOTH_C1];
      X_GEN_TAC `v:complex` THEN REWRITE_TAC[ETA_AX] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `R:real` THEN
      MATCH_MP_TAC BEL_SMOOTH_SUPP_FRECHET THEN ASM_REWRITE_TAC[]]]);;

let BEL_CT_SMOOTH = prove
 (`!R h. smooth_map_on (:complex) h /\ bel_supp R h
         ==> smooth_map_on (:complex) (bel_ct h)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smooth_map_on] THEN GEN_TAC THEN
  MATCH_MP_TAC BEL_CT_CONTINUOUSLY_DIFFERENTIABLE THEN EXISTS_TAC `R:real` THEN
  ASM_REWRITE_TAC[]);;

let BEL_CT_PARTIAL = prove
 (`!R h i. smooth_map_on (:complex) h /\ bel_supp R h
           ==> partial_derivative i (bel_ct h) = bel_ct (partial_derivative i h)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM; PARTIAL_DERIVATIVE_ALT] THEN
  X_GEN_TAC `z:complex` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC BEL_CT_FRECHET THEN EXISTS_TAC `R:real` THEN ASM_SIMP_TAC[BEL_SMOOTH_C1]);;

let BEL_SUPP_ITERATED_PARTIAL = prove
 (`!l R f. smooth_map_on (:complex) f /\ bel_supp R f
           ==> smooth_map_on (:complex) (iterated_partial l f) /\
               bel_supp R (iterated_partial l f)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[iterated_partial] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[PARTIAL_DERIVATIVE_ALT] THEN
  MATCH_MP_TAC BEL_SMOOTH_SUPP_FRECHET THEN ASM_MESON_TAC[]);;

let BEL_CT_ITERATED_PARTIAL = prove
 (`!l R f. smooth_map_on (:complex) f /\ bel_supp R f
           ==> iterated_partial l (bel_ct f) = bel_ct (iterated_partial l f)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[iterated_partial] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th (CONJ (ASSUME `smooth_map_on (:complex) (f:complex->complex)`)
                                                     (ASSUME `bel_supp R f`))]) THEN
  MATCH_MP_TAC BEL_CT_PARTIAL THEN EXISTS_TAC `R:real` THEN
  MATCH_MP_TAC BEL_SUPP_ITERATED_PARTIAL THEN ASM_REWRITE_TAC[]);;

(* Pompeiu (green.ml): C(dh/dzbar) = h for h of class C^1 with compact      *)
(* support.                                                                   *)

let BEL_CT_POMPEIU = prove
 (`!R h z. bel_c1 h /\ bel_supp R h ==> bel_ct (wirtinger_dbar h) z = h z`,
  REWRITE_TAC[bel_c1] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[bel_ct] THEN
  MP_TAC(ISPECL [`h:complex->complex`; `z:complex`] CAUCHY_TRANSFORM_INVERTS_DBAR) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[BEL_SUPP_BOUNDED]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `Cx(inv pi) * Cx pi = Cx(&1)` MP_TAC THENL
   [REWRITE_TAC[GSYM CX_MUL] THEN AP_TERM_TAC THEN MATCH_MP_TAC REAL_MUL_LINV THEN
    MP_TAC PI_POS THEN REAL_ARITH_TAC;
    CONV_TAC COMPLEX_RING]);;

let BEL_CT_LINCOMB = prove
 (`!R f1 f2 a b z.
        f1 continuous_on (:complex) /\ bel_supp R f1 /\
        f2 continuous_on (:complex) /\ bel_supp R f2
        ==> bel_ct (\w. a * f1 w + b * f2 w) z = a * bel_ct f1 z + b * bel_ct f2 z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`R:real`; `\w:complex. a * (f1:complex->complex) w`;
                 `\w:complex. b * (f2:complex->complex) w`; `z:complex`] BEL_CT_ADD) THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_COMPLEX_LMUL; BEL_SUPP_LMUL; ETA_AX] THEN
  DISCH_THEN SUBST1_TAC THEN BINOP_TAC THEN MATCH_MP_TAC BEL_CT_LMUL THEN
  EXISTS_TAC `R:real` THEN ASM_REWRITE_TAC[]);;

let BEL_WIRTINGER_FUN = prove
 (`!h:complex->complex.
        wirtinger_dbar h =
        (\w. inv(Cx(&2)) * frechet_derivative h (at w) (Cx(&1)) +
             (ii * inv(Cx(&2))) * frechet_derivative h (at w) ii) /\
        wirtinger_dz h =
        (\w. inv(Cx(&2)) * frechet_derivative h (at w) (Cx(&1)) +
             (--ii * inv(Cx(&2))) * frechet_derivative h (at w) ii)`,
  GEN_TAC THEN CONJ_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; WIRTINGER_DBAR_FRECHET; WIRTINGER_DZ_FRECHET] THEN
  GEN_TAC THEN REWRITE_TAC[complex_div] THEN CONV_TAC COMPLEX_RING);;

let BEL_CT_WIRTINGER = prove
 (`!R h z. bel_c1 h /\ bel_supp R h
           ==> wirtinger_dbar (bel_ct h) z = bel_ct (wirtinger_dbar h) z /\
               wirtinger_dz (bel_ct h) z = bel_ct (wirtinger_dz h) z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[BEL_WIRTINGER_FUN] THEN
  MP_TAC(ISPECL [`R:real`; `h:complex->complex`; `z:complex`; `Cx(&1)`] BEL_CT_FRECHET) THEN
  MP_TAC(ISPECL [`R:real`; `h:complex->complex`; `z:complex`; `ii`] BEL_CT_FRECHET) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  SUBGOAL_THEN
   `!a b. bel_ct (\w. a * frechet_derivative (h:complex->complex) (at w) (Cx(&1)) +
                      b * frechet_derivative h (at w) ii) z =
          a * bel_ct (\w. frechet_derivative h (at w) (Cx(&1))) z +
          b * bel_ct (\w. frechet_derivative h (at w) ii) z`
   (fun th -> REWRITE_TAC[th]) THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC BEL_CT_LINCOMB THEN EXISTS_TAC `R:real` THEN
  ASM_SIMP_TAC[BEL_C1_FRECHET_CONTINUOUS; BEL_C1_SUPP_FRECHET]);;

(* The Beurling transform.                                                    *)

let bel_s = new_definition
 `bel_s (h:complex->complex) = bel_ct (wirtinger_dz h)`;;

let BEL_CT_DBAR = prove
 (`!R h z. bel_c1 h /\ bel_supp R h ==> wirtinger_dbar (bel_ct h) z = h z`,
  MESON_TAC[BEL_CT_WIRTINGER; BEL_CT_POMPEIU]);;

let BEL_CT_DZ = prove
 (`!R h z. bel_c1 h /\ bel_supp R h ==> wirtinger_dz (bel_ct h) z = bel_s h z`,
  REWRITE_TAC[bel_s] THEN MESON_TAC[BEL_CT_WIRTINGER]);;

(* ========================================================================= *)
(* Algebra of smooth complex functions of the plane, a smooth                *)
(* cutoff, product rules for the Wirtinger derivatives, and the null         *)
(* Lagrangian identity int |v_z|^2 = int |v_zbar|^2 for smooth v with        *)
(* compact support.                                                          *)
(* ========================================================================= *)

let BEL_SMOOTH_ADD = prove
 (`!f g:complex->complex.
        smooth_map_on (:complex) f /\ smooth_map_on (:complex) g
        ==> smooth_map_on (:complex) (\w. f w + g w)`,
  SIMP_TAC[SMOOTH_MAP_ON_ADD_OPEN; OPEN_UNIV]);;

let BEL_SMOOTH_SUB = prove
 (`!f g:complex->complex.
        smooth_map_on (:complex) f /\ smooth_map_on (:complex) g
        ==> smooth_map_on (:complex) (\w. f w - g w)`,
  SIMP_TAC[SMOOTH_MAP_ON_SUB_OPEN; OPEN_UNIV]);;

let BEL_SMOOTH_MUL = prove
 (`!f g:complex->complex.
        smooth_map_on (:complex) f /\ smooth_map_on (:complex) g
        ==> smooth_map_on (:complex) (\w. f w * g w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:complex)`; `( * ):complex->complex->complex`;
                 `f:complex->complex`; `g:complex->complex`]
                SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; BILINEAR_COMPLEX_MUL]);;

let BEL_SMOOTH_LMUL = prove
 (`!c f:complex->complex.
        smooth_map_on (:complex) f ==> smooth_map_on (:complex) (\w. c * f w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\w:complex. c:complex`; `f:complex->complex`] BEL_SMOOTH_MUL) THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST]);;

let BEL_SMOOTH_CNJ = prove
 (`!f:complex->complex.
        smooth_map_on (:complex) f ==> smooth_map_on (:complex) (\w. cnj(f w))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\w. cnj((f:complex->complex) w)) = cnj o f` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
  ASM_REWRITE_TAC[OPEN_UNIV; LINEAR_CNJ]);;

let BEL_SMOOTH_WIRTINGER = prove
 (`!h:complex->complex.
        smooth_map_on (:complex) h
        ==> smooth_map_on (:complex) (wirtinger_dbar h) /\
            smooth_map_on (:complex) (wirtinger_dz h)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[BEL_WIRTINGER_FUN] THEN
  MATCH_MP_TAC BEL_SMOOTH_ADD THEN CONJ_TAC THEN MATCH_MP_TAC BEL_SMOOTH_LMUL THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[OPEN_UNIV]);;

let BEL_SUPP_WIRTINGER = prove
 (`!R h. bel_c1 h /\ bel_supp R h
         ==> bel_supp R (wirtinger_dbar h) /\ bel_supp R (wirtinger_dz h)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[BEL_WIRTINGER_FUN] THEN
  MATCH_MP_TAC BEL_SUPP_ADD THEN CONJ_TAC THEN MATCH_MP_TAC BEL_SUPP_LMUL THEN
  ASM_SIMP_TAC[BEL_C1_SUPP_FRECHET]);;

let BEL_C1_WIRTINGER_CONTINUOUS = prove
 (`!h. bel_c1 h
       ==> (wirtinger_dbar h) continuous_on (:complex) /\
           (wirtinger_dz h) continuous_on (:complex)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[BEL_WIRTINGER_FUN] THEN
  MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN ASM_SIMP_TAC[BEL_C1_FRECHET_CONTINUOUS]);;

let BEL_S_SMOOTH = prove
 (`!R h. smooth_map_on (:complex) h /\ bel_supp R h
         ==> smooth_map_on (:complex) (bel_s h)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bel_s] THEN MATCH_MP_TAC BEL_CT_SMOOTH THEN
  EXISTS_TAC `R:real` THEN ASM_SIMP_TAC[BEL_SMOOTH_WIRTINGER] THEN
  ASM_MESON_TAC[BEL_SUPP_WIRTINGER; BEL_SMOOTH_C1]);;

(* Product rule for the Wirtinger derivatives.                               *)

let BEL_WIRTINGER_MUL = prove
 (`!f g:complex->complex z.
        f differentiable at z /\ g differentiable at z
        ==> wirtinger_dz (\w. f w * g w) z =
            wirtinger_dz f z * g z + f z * wirtinger_dz g z /\
            wirtinger_dbar (\w. f w * g w) z =
            wirtinger_dbar f z * g z + f z * wirtinger_dbar g z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FRECHET_DERIVATIVE_WORKS] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`( * ):complex->complex->complex`; `f:complex->complex`;
                 `g:complex->complex`; `frechet_derivative (f:complex->complex) (at z)`;
                 `frechet_derivative (g:complex->complex) (at z)`; `z:complex`]
                HAS_DERIVATIVE_BILINEAR_AT) THEN
  ASM_REWRITE_TAC[BILINEAR_COMPLEX_MUL] THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[WIRTINGER_DZ_FRECHET; WIRTINGER_DBAR_FRECHET] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[] THEN
  REWRITE_TAC[complex_div] THEN CONV_TAC COMPLEX_RING);;

(* The cutoff: 1 on cball(0,R), 0 outside ball(0,2R), derivatives O(1/R).  *)

let bel_cut = new_definition
 `bel_cut (R:real) (z:complex) = Cx(smooth_bump (&1) (&2) (inv R % z))`;;

let BEL_LINEAR_CX_DROP = prove
 (`linear (\x:real^1. Cx(drop x))`,
  REWRITE_TAC[linear; DROP_ADD; DROP_CMUL; CX_ADD; CX_MUL; COMPLEX_CMUL]);;

let BEL_CUT_SMOOTH = prove
 (`!R. smooth_map_on (:complex) (bel_cut R)`,
  GEN_TAC THEN
  SUBGOAL_THEN `bel_cut R = (\x:real^1. Cx(drop x)) o
                            ((\x:complex. lift(smooth_bump (&1) (&2) x)) o
                             (\z:complex. inv R % z))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; bel_cut; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN REWRITE_TAC[OPEN_UNIV; BEL_LINEAR_CX_DROP] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:complex)` THEN
  REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID];
    MATCH_MP_TAC SMOOTH_BUMP_SMOOTH THEN REAL_ARITH_TAC]);;

let BEL_CUT_SUPP = prove
 (`!R. &0 < R ==> bel_supp (&2 * R) (bel_cut R)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bel_supp; bel_cut; CX_INJ] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_BUMP_0 THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < R ==> abs R = R`] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] (GSYM real_div)] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

let BEL_CUT_ONE = prove
 (`!R z. &0 < R /\ norm z <= R ==> bel_cut R z = Cx(&1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bel_cut; CX_INJ] THEN
  MATCH_MP_TAC SMOOTH_BUMP_1 THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < R ==> abs R = R`] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] (GSYM real_div)] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

let BEL_CUT_BOUND = prove
 (`!R z. norm(bel_cut R z) <= &1`,
  REWRITE_TAC[bel_cut; COMPLEX_NORM_CX] THEN
  MESON_TAC[SMOOTH_BUMP_BOUNDS; REAL_ARITH `&0 <= x /\ x <= &1 ==> abs x <= &1`]);;

let BEL_CUT_DERIV_BOUND = prove
 (`?c. &0 <= c /\
       !R z v. &0 < R
               ==> norm(frechet_derivative (bel_cut R) (at z) v) <= c / R * norm v`,
  SUBGOAL_THEN `!v. ?M. !w. norm(frechet_derivative (bel_cut(&1)) (at w) v) <= M`
  MP_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC BEL_SUPP_BOUNDED_FN THEN EXISTS_TAC `&2 * &1` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN
      REWRITE_TAC[OPEN_UNIV; BEL_CUT_SMOOTH];
      MATCH_MP_TAC BEL_C1_SUPP_FRECHET THEN
      SIMP_TAC[BEL_CUT_SUPP; REAL_LT_01; BEL_SMOOTH_C1; BEL_CUT_SMOOTH]];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `Cx(&1)` th) THEN MP_TAC(SPEC `ii` th)) THEN
  DISCH_THEN(X_CHOOSE_TAC `M2:real`) THEN DISCH_THEN(X_CHOOSE_TAC `M1:real`) THEN
  EXISTS_TAC `abs M1 + abs M2` THEN REWRITE_TAC[REAL_ARITH `&0 <= abs a + abs b`] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `bel_cut R = bel_cut (&1) o (\z:complex. inv R % z)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; bel_cut; REAL_INV_1; VECTOR_MUL_LID]; ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (bel_cut (&1) o (\z:complex. inv R % z)) (at z) =
    frechet_derivative (bel_cut (&1)) (at (inv R % z)) o (\v:complex. inv R % v)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MP_TAC(ISPECL [`\z:complex. inv R % z`; `bel_cut(&1)`; `\v:complex. inv R % v`;
                   `frechet_derivative (bel_cut (&1)) (at (inv R % z))`; `z:complex`]
                  DIFF_CHAIN_AT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_SCALING];
      MATCH_MP_TAC BEL_C1_HAS_DERIVATIVE THEN SIMP_TAC[BEL_SMOOTH_C1; BEL_CUT_SMOOTH]];
    ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN
  MP_TAC(ISPECL [`frechet_derivative (bel_cut (&1)) (at (inv R % z))`; `inv R % v:complex`]
                BEL_LINEAR_EXPAND) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC BEL_C1_LINEAR THEN SIMP_TAC[BEL_SMOOTH_C1; BEL_CUT_SMOOTH];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(inv R % v:complex) * abs M1 + norm(inv R % v:complex) * abs M2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(NORM_ARITH `norm(a:complex) <= x /\ norm(b:complex) <= y
                             ==> norm(a + b) <= x + y`) THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    MP_TAC(SPEC `inv R % v:complex` COMPLEX_NORM_GE_RE_IM) THEN STRIP_TAC THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_MESON_TAC[REAL_ABS_POS; NORM_POS_LE; REAL_LE_TRANS;
                  REAL_ARITH `x <= abs x`];
    REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < R ==> abs R = R`] THEN
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC]);;

let BEL_CUT_WIRTINGER_BOUND = prove
 (`?c. &0 <= c /\
       !R z. &0 < R
             ==> norm(wirtinger_dz (bel_cut R) z) <= c / R /\
                 norm(wirtinger_dbar (bel_cut R) z) <= c / R`,
  X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC BEL_CUT_DERIV_BOUND THEN
  EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[WIRTINGER_DZ_FRECHET; WIRTINGER_DBAR_FRECHET; COMPLEX_NORM_DIV;
              COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`R:real`; `z:complex`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `Cx(&1)` th) THEN MP_TAC(SPEC `ii` th)) THEN
  REWRITE_TAC[COMPLEX_NORM_CX; COMPLEX_NORM_II; REAL_ABS_NUM; REAL_MUL_RID] THEN
  MP_TAC(ISPEC `frechet_derivative (bel_cut R) (at z) ii` (GEN `x:complex`
    (REWRITE_RULE[COMPLEX_NORM_II; REAL_MUL_LID]
      (ISPECL [`ii`; `x:complex`] COMPLEX_NORM_MUL)))) THEN
  SPEC_TAC(`frechet_derivative (bel_cut R) (at z) ii`,`B:complex`) THEN
  SPEC_TAC(`frechet_derivative (bel_cut R) (at z) (Cx(&1))`,`A:complex`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  CONJ_TAC THEN MATCH_MP_TAC(REAL_ARITH `x <= &2 * y ==> x / &2 <= y`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm(A:complex) + norm(ii * B)` THEN
  REWRITE_TAC[NORM_ARITH `norm(a - b:complex) <= norm a + norm b`;
              NORM_ARITH `norm(a + b:complex) <= norm a + norm b`] THEN
  ASM_REAL_ARITH_TAC);;

let BEL_CUT_DERIV_ZERO = prove
 (`!R z. &0 < R /\ (norm z < R \/ &2 * R < norm z)
         ==> frechet_derivative (bel_cut R) (at z) = (\v. vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THENL
   [MP_TAC(ISPECL [`\w:complex. bel_cut R w - Cx(&1)`;
                   `\v:complex. frechet_derivative (bel_cut R) (at z) v - vec 0`;
                   `ball(Cx(&0),R)`; `z:complex`] WAN_NT_DERIVATIVE_ZERO_LOCAL) THEN
    REWRITE_TAC[OPEN_BALL; IN_BALL; dist; COMPLEX_SUB_LZERO; NORM_NEG] THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[BEL_CUT_ONE; REAL_LT_IMP_LE] THEN
        REWRITE_TAC[COMPLEX_SUB_REFL; COMPLEX_VEC_0];
        MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
        REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC BEL_C1_HAS_DERIVATIVE THEN
        SIMP_TAC[BEL_SMOOTH_C1; BEL_CUT_SMOOTH]];
      REWRITE_TAC[FUN_EQ_THM; VECTOR_SUB_RZERO] THEN MESON_TAC[]];
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `v:complex` THEN
    MATCH_MP_TAC FRECHET_DERIVATIVE_ZERO_OUTSIDE THEN EXISTS_TAC `&2 * R` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MESON_TAC[BEL_SMOOTH_C1; bel_c1; BEL_CUT_SMOOTH];
      MP_TAC(SPEC `R:real` BEL_CUT_SUPP) THEN ASM_REWRITE_TAC[bel_supp; COMPLEX_VEC_0]]]);;

(* The null Lagrangian: for smooth v with compact support,                   *)
(* int (cnj(v_x) v_y - cnj(v_y) v_x) = 0, hence int |v_z|^2 = int |v_zbar|^2. *)

let BEL_FRECHET_CNJ_MUL = prove
 (`!v g:complex->complex z d.
        v differentiable at z /\ g differentiable at z
        ==> frechet_derivative (\w. cnj(v w) * g w) (at z) d =
            cnj(v z) * frechet_derivative g (at z) d +
            cnj(frechet_derivative v (at z) d) * g z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FRECHET_DERIVATIVE_WORKS] THEN STRIP_TAC THEN
  SUBGOAL_THEN `((\w. cnj((v:complex->complex) w)) has_derivative
                 (\d. cnj(frechet_derivative v (at z) d))) (at z)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`v:complex->complex`; `cnj`; `frechet_derivative (v:complex->complex) (at z)`;
                   `cnj`; `z:complex`] DIFF_CHAIN_AT) THEN
    ASM_REWRITE_TAC[HAS_DERIVATIVE_CNJ; o_DEF];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`( * ):complex->complex->complex`; `\w. cnj((v:complex->complex) w)`;
                 `g:complex->complex`; `\d. cnj(frechet_derivative (v:complex->complex) (at z) d)`;
                 `frechet_derivative (g:complex->complex) (at z)`; `z:complex`]
                HAS_DERIVATIVE_BILINEAR_AT) THEN
  ASM_REWRITE_TAC[BILINEAR_COMPLEX_MUL] THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[] THEN CONV_TAC COMPLEX_RING);;

let BEL_PARTIAL_COMPLEX = prove
 (`!v:complex->complex z.
        partial_derivative 1 v z = frechet_derivative v (at z) (Cx(&1)) /\
        partial_derivative 2 v z = frechet_derivative v (at z) ii`,
  REWRITE_TAC[partial_derivative; COMPLEX_BASIS]);;

let BEL_DIV_IDENTITY = prove
 (`!v:complex->complex z.
        smooth_map_on (:complex) v
        ==> frechet_derivative (\w. cnj(v w) * partial_derivative 2 v w) (at z) (Cx(&1)) -
            frechet_derivative (\w. cnj(v w) * partial_derivative 1 v w) (at z) ii =
            cnj(partial_derivative 1 v z) * partial_derivative 2 v z -
            cnj(partial_derivative 2 v z) * partial_derivative 1 v z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!i. smooth_map_on (:complex) (partial_derivative i (v:complex->complex))`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN
    ASM_REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!f:complex->complex w. smooth_map_on (:complex) f ==> f differentiable at w`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(:complex)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`v:complex->complex`; `partial_derivative 2 (v:complex->complex)`;
                 `z:complex`; `Cx(&1)`] BEL_FRECHET_CNJ_MUL) THEN
  MP_TAC(ISPECL [`v:complex->complex`; `partial_derivative 1 (v:complex->complex)`;
                 `z:complex`; `ii`] BEL_FRECHET_CNJ_MUL) THEN
  ASM_SIMP_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  SUBGOAL_THEN
   `frechet_derivative (partial_derivative 2 (v:complex->complex)) (at z) (Cx(&1)) =
    frechet_derivative (partial_derivative 1 v) (at z) ii`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM BEL_PARTIAL_COMPLEX] THEN
    MATCH_MP_TAC PARTIAL_DERIVATIVE_SYM THEN EXISTS_TAC `(:complex)` THEN
    REWRITE_TAC[OPEN_UNIV; IN_UNIV; DIMINDEX_2] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_MESON_TAC[smooth_map_on];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM BEL_PARTIAL_COMPLEX] THEN CONV_TAC COMPLEX_RING);;

let BEL_JAC_HAS_INTEGRAL_ZERO = prove
 (`!R v:complex->complex.
        smooth_map_on (:complex) v /\ bel_supp R v
        ==> ((\z. cnj(partial_derivative 1 v z) * partial_derivative 2 v z -
                  cnj(partial_derivative 2 v z) * partial_derivative 1 v z)
             has_integral Cx(&0)) (:complex)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!i. smooth_map_on (:complex) (\w. cnj((v:complex->complex) w) *
                                                  partial_derivative i v w)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC BEL_SMOOTH_MUL THEN ASM_SIMP_TAC[BEL_SMOOTH_CNJ] THEN
    REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN
    ASM_REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i x. ~(x IN cball(Cx(&0),R))
                      ==> (\w. cnj((v:complex->complex) w) * partial_derivative i v w) x =
                          vec 0`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[IN_CBALL; dist; COMPLEX_SUB_LZERO; NORM_NEG] THEN
    DISCH_TAC THEN UNDISCH_TAC `bel_supp R (v:complex->complex)` THEN
    REWRITE_TAC[bel_supp] THEN DISCH_THEN(MP_TAC o SPEC `x:complex`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[CNJ_CX; COMPLEX_MUL_LZERO; COMPLEX_VEC_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\w:complex. cnj((v:complex->complex) w) * partial_derivative 2 v w`;
                 `cball(Cx(&0),R)`; `Cx(&1)`] WAN_INTEGRAL_DIRDERIV_ZERO) THEN
  MP_TAC(ISPECL [`\w:complex. cnj((v:complex->complex) w) * partial_derivative 1 v w`;
                 `cball(Cx(&0),R)`; `ii`] WAN_INTEGRAL_DIRDERIV_ZERO) THEN
  ASM_REWRITE_TAC[COMPACT_CBALL] THEN
  DISCH_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th1 -> FIRST_X_ASSUM(fun th2 ->
    MP_TAC(MATCH_MP HAS_INTEGRAL_SUB (CONJ th1 th2)))) THEN
  REWRITE_TAC[VECTOR_SUB_REFL; GSYM COMPLEX_VEC_0] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:complex` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC BEL_DIV_IDENTITY THEN ASM_REWRITE_TAC[]);;

let BEL_SQNORM_ALG = prove
 (`!a b:complex.
        norm((a - ii * b) / Cx(&2)) pow 2 - norm((a + ii * b) / Cx(&2)) pow 2 =
        Im(cnj a * b)`,
  REWRITE_TAC[COMPLEX_SQNORM; RE_DIV_CX; IM_DIV_CX; RE_SUB; IM_SUB; RE_ADD; IM_ADD;
              complex_mul; RE; IM; RE_CNJ; IM_CNJ; RE_II; IM_II] THEN
  CONV_TAC REAL_RING);;

let BEL_CNJ_ANTISYM = prove
 (`!a b:complex. cnj a * b - cnj b * a = Cx(&2) * ii * Cx(Im(cnj a * b))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[COMPLEX_EQ; RE_SUB; IM_SUB; complex_mul; RE; IM; RE_CNJ; IM_CNJ;
              RE_CX; IM_CX; RE_II; IM_II] THEN
  CONJ_TAC THEN CONV_TAC REAL_RING);;

let BEL_WIRT_SQ_DIFF = prove
 (`!v:complex->complex z.
        norm(wirtinger_dz v z) pow 2 - norm(wirtinger_dbar v z) pow 2 =
        Im(cnj(partial_derivative 1 v z) * partial_derivative 2 v z)`,
  REWRITE_TAC[WIRTINGER_DZ_FRECHET; WIRTINGER_DBAR_FRECHET; BEL_PARTIAL_COMPLEX;
              BEL_SQNORM_ALG]);;

let BEL_INTEGRABLE_CBALL_SUPPORT = prove
 (`!f:complex->real^N R.
        f continuous_on (:complex) /\ (!z. R < norm z ==> f z = vec 0)
        ==> f integrable_on (:complex)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_NT_INTEGRABLE_COMPACT_SUPPORT THEN
  EXISTS_TAC `cball(Cx(&0),R)` THEN
  ASM_REWRITE_TAC[OPEN_UNIV; COMPACT_CBALL; SUBSET_UNIV; IN_UNIV; IN_CBALL; dist;
                  COMPLEX_SUB_LZERO; NORM_NEG] THEN
  ASM_MESON_TAC[REAL_NOT_LE]);;

let BEL_SQ_INTEGRABLE = prove
 (`!R f:complex->complex.
        f continuous_on (:complex) /\ bel_supp R f
        ==> (\z. lift(norm(f z) pow 2)) integrable_on (:complex)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BEL_INTEGRABLE_CBALL_SUPPORT THEN
  EXISTS_TAC `R:real` THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `bel_supp R (f:complex->complex)` THEN REWRITE_TAC[bel_supp] THEN
    SIMP_TAC[COMPLEX_NORM_0; REAL_ARITH `&0 pow 2 = &0`; LIFT_NUM]]);;

let BEL_DZ_DBAR_L2 = prove
 (`!R v:complex->complex.
        smooth_map_on (:complex) v /\ bel_supp R v
        ==> integral (:complex) (\z. lift(norm(wirtinger_dz v z) pow 2)) =
            integral (:complex) (\z. lift(norm(wirtinger_dbar v z) pow 2))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `J = \z. Im(cnj(partial_derivative 1 (v:complex->complex) z) *
                         partial_derivative 2 v z)` THEN
  SUBGOAL_THEN `!i. smooth_map_on (:complex) (partial_derivative i (v:complex->complex)) /\
                    bel_supp R (partial_derivative i v)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MP_TAC(ISPECL [`[i:num]`; `R:real`; `v:complex->complex`]
                               BEL_SUPP_ITERATED_PARTIAL) THEN
    ASM_REWRITE_TAC[iterated_partial];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z. lift((J:complex->real) z)) integrable_on (:complex)` ASSUME_TAC THENL
   [MATCH_MP_TAC BEL_INTEGRABLE_CBALL_SUPPORT THEN EXISTS_TAC `R:real` THEN
    EXPAND_TAC "J" THEN CONJ_TAC THENL
     [REWRITE_TAC[IM_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN CONJ_TAC THENL
       [SUBGOAL_THEN `(\z. cnj(partial_derivative 1 (v:complex->complex) z)) =
                      cnj o partial_derivative 1 v` SUBST1_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC[CONTINUOUS_ON_CNJ] THEN
        ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS];
        REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS]];
      X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
      SUBGOAL_THEN `partial_derivative 1 (v:complex->complex) z = Cx(&0)` SUBST1_TAC THENL
       [ASM_MESON_TAC[bel_supp]; ALL_TAC] THEN
      REWRITE_TAC[CNJ_CX; COMPLEX_MUL_LZERO; IM_CX; LIFT_NUM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `drop(integral (:complex) (\z. lift((J:complex->real) z))) = &0`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\z. lift((J:complex->real) z)`; `(:complex)`;
                   `\x:real^1. Cx(drop x)`] INTEGRAL_LINEAR) THEN
    ASM_REWRITE_TAC[BEL_LINEAR_CX_DROP; o_DEF; LIFT_DROP] THEN
    MP_TAC(ISPECL [`R:real`; `v:complex->complex`] BEL_JAC_HAS_INTEGRAL_ZERO) THEN
    ASM_REWRITE_TAC[BEL_CNJ_ANTISYM] THEN
    DISCH_THEN(MP_TAC o SPEC `inv(Cx(&2) * ii)` o MATCH_MP HAS_INTEGRAL_COMPLEX_LMUL) THEN
    REWRITE_TAC[COMPLEX_MUL_RZERO] THEN
    SUBGOAL_THEN `!x. inv(Cx(&2) * ii) * Cx(&2) * ii * x = x`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN
      SUBGOAL_THEN `~(Cx(&2) * ii = Cx(&0))` MP_TAC THENL
       [REWRITE_TAC[COMPLEX_ENTIRE; CX_INJ; II_NZ] THEN REAL_ARITH_TAC;
        CONV_TAC COMPLEX_FIELD];
      ALL_TAC] THEN
    EXPAND_TAC "J" THEN REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN
    REWRITE_TAC[CX_INJ] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z. lift(norm(wirtinger_dz (v:complex->complex) z) pow 2)) =
                (\z. lift(norm(wirtinger_dbar v z) pow 2) + lift(J z))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_ADD; LIFT_EQ] THEN EXPAND_TAC "J" THEN
    REWRITE_TAC[GSYM BEL_WIRT_SQ_DIFF] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z. lift(norm(wirtinger_dbar (v:complex->complex) z) pow 2)`;
                 `\z. lift((J:complex->real) z)`; `(:complex)`] INTEGRAL_ADD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC BEL_SQ_INTEGRABLE THEN EXISTS_TAC `R:real` THEN
    REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN ASM_SIMP_TAC[BEL_SMOOTH_WIRTINGER];
      MP_TAC(ISPECL [`R:real`; `v:complex->complex`] BEL_SUPP_WIRTINGER) THEN
      ASM_SIMP_TAC[BEL_SMOOTH_C1]];
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[VECTOR_ARITH `a + b:real^1 = a <=> b = vec 0`] THEN
  REWRITE_TAC[GSYM DROP_EQ; DROP_VEC] THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The L^2 bound for the Beurling transform.  For g smooth with              *)
(* compact support and every disc cball(0,rho):                              *)
(*   int_{cball(0,rho)} |S g|^2 <= int |g|^2.                                *)
(* Proof: v = (C g) chi_R with the cutoff chi_R; int |v_z|^2 = int |v_zbar|^2 *)
(* (above); v_z = S g on the disc, v_zbar = g + (C g)(chi_R)_zbar, and the   *)
(* error term is O(1/R) in L^2 by the decay of C g; let R -> infinity.       *)
(* ========================================================================= *)

let BEL_EPS_LE = prove
 (`!X A. &0 <= A /\ (!e. &0 < e /\ e <= &1 ==> X <= (&1 + e) * A + e) ==> X <= A`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `min (&1) ((X - A) / (A + &2))`) THEN
  SUBGOAL_THEN `&0 < (X - A) / (A + &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_NOT_LE] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `A + (X - A) / (A + &2) * (A + &1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= (A + &1) * (y - x) ==> (&1 + x) * A + x <= A + y * (A + &1)`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `y < X - A ==> A + y < X`) THEN
    SIMP_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `(X - A) * &1` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `inv(A + &2) * (A + &1) = (A + &1) / (A + &2)` SUBST1_TAC THENL
       [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 <= A ==> &0 < A + &2`] THEN
      REAL_ARITH_TAC;
      REAL_ARITH_TAC]]);;

let BEL_AMGM = prove
 (`!x y e. &0 < e ==> &2 * x * y <= e * x pow 2 + inv e * y pow 2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `e:real` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `e * inv e = &1` MP_TAC THENL
   [MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`inv e`,`f:real`) THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `e * (e * x pow 2 + f * y pow 2) - e * (&2 * x * y) =
                (e * x - y) * (e * x - y)` MP_TAC THENL
   [UNDISCH_TAC `e * f = &1` THEN CONV_TAC REAL_RING;
    MP_TAC(SPEC `e * x - y` REAL_LE_SQUARE) THEN REAL_ARITH_TAC]);;

let BEL_SQ_SPLIT = prove
 (`!a b:complex e.
        &0 < e
        ==> norm(a + b) pow 2 <= (&1 + e) * norm a pow 2 + (&1 + inv e) * norm b pow 2`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(norm(a:complex) + norm(b:complex)) pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE; NORM_TRIANGLE];
    MP_TAC(SPECL [`norm(a:complex)`; `norm(b:complex)`; `e:real`] BEL_AMGM) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let BEL_CUT_ERROR_BOUND = prove
 (`!u:complex->complex K c R.
        &0 < R /\ &0 <= K /\ &0 <= c /\
        (!z. R <= norm z ==> norm(u z) <= K / norm z) /\
        (!z. norm(wirtinger_dbar (bel_cut R) z) <= c / R)
        ==> !z. norm(u z * wirtinger_dbar (bel_cut R) z) pow 2 <=
                (if z IN cball(Cx(&0),&2 * R) then (c * K / R pow 2) pow 2 else &0)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `norm(z:complex) < R \/ &2 * R < norm z` THENL
   [SUBGOAL_THEN `wirtinger_dbar (bel_cut R) z = Cx(&0)` SUBST1_TAC THENL
     [REWRITE_TAC[WIRTINGER_DBAR_FRECHET] THEN
      MP_TAC(SPECL [`R:real`; `z:complex`] BEL_CUT_DERIV_ZERO) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_MUL_RZERO; COMPLEX_ADD_RID; complex_div;
                  COMPLEX_MUL_LZERO];
      REWRITE_TAC[COMPLEX_MUL_RZERO; COMPLEX_NORM_0] THEN
      COND_CASES_TAC THEN
      REWRITE_TAC[REAL_ARITH `&0 pow 2 = &0`; REAL_LE_REFL; REAL_LE_POW_2]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
  REWRITE_TAC[DE_MORGAN_THM; REAL_NOT_LT] THEN STRIP_TAC THEN
  SUBGOAL_THEN `z IN cball(Cx(&0),&2 * R)` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[IN_CBALL; dist; COMPLEX_SUB_LZERO; NORM_NEG] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE; COMPLEX_NORM_MUL] THEN
  SUBGOAL_THEN `norm((u:complex->complex) z) <= K / R` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K / norm(z:complex)` THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K / R * c / R` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_ARITH `K / R * c / R = (K / R) * (c / R)`] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE];
    REWRITE_TAC[real_div; REAL_POW_2; REAL_INV_MUL] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC]);;

let BEL_SQ_INTEGRABLE_SUBSET = prove
 (`!R f:complex->complex s.
        f continuous_on (:complex) /\ bel_supp R f /\ lebesgue_measurable s
        ==> (\z. lift(norm(f z) pow 2)) integrable_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
  EXISTS_TAC `(:complex)` THEN ASM_REWRITE_TAC[SUBSET_UNIV] THEN
  MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN CONJ_TAC THENL
   [SIMP_TAC[DIMINDEX_1; LIFT_COMPONENT; REAL_LE_POW_2] THEN
    REWRITE_TAC[ARITH_RULE `1 <= i /\ i <= 1 <=> i = 1`] THEN
    SIMP_TAC[GSYM drop; LIFT_DROP; REAL_LE_POW_2];
    MATCH_MP_TAC BEL_SQ_INTEGRABLE THEN EXISTS_TAC `R:real` THEN ASM_REWRITE_TAC[]]);;

let BEL_INDICATOR_INTEGRAL = prove
 (`!r C. (\z. if z IN cball(Cx(&0),r) then lift C else vec 0) integrable_on (:complex) /\
         drop(integral (:complex) (\z. if z IN cball(Cx(&0),r) then lift C else vec 0)) =
         C * measure(cball(Cx(&0),r))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV; INTEGRAL_RESTRICT_UNIV] THEN
  SIMP_TAC[INTEGRABLE_ON_CONST; MEASURABLE_CBALL; INTEGRAL_CONST_GEN; DROP_CMUL;
           LIFT_DROP] THEN
  REAL_ARITH_TAC);;

let BEL_S_L2_EPS = prove
 (`!g u:complex->complex R1 K c rho e R0.
        smooth_map_on (:complex) g /\ bel_supp R1 g /\ &0 < R1 /\
        smooth_map_on (:complex) u /\ (!z. wirtinger_dbar u z = g z) /\
        (!z. R0 <= norm z ==> norm(u z) <= K / norm z) /\ &0 <= K /\
        &0 <= c /\
        (!R z. &0 < R ==> norm(wirtinger_dz (bel_cut R) z) <= c / R /\
                          norm(wirtinger_dbar (bel_cut R) z) <= c / R) /\
        &0 < e /\ rho < R0 /\ R1 <= R0 /\ &1 <= R0 /\
        (&1 + inv e) * (&16 * (c * K) pow 2) <= e * R0 pow 2
        ==> drop(integral (cball(Cx(&0),rho)) (\z. lift(norm(wirtinger_dz u z) pow 2)))
            <= (&1 + e) * drop(integral (:complex) (\z. lift(norm(g z) pow 2))) + e`,
  (REPEAT STRIP_TAC THEN
  ABBREV_TAC `v = \z:complex. (u:complex->complex) z * bel_cut R0 z` THEN
  SUBGOAL_THEN `&0 < R0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:complex) (v:complex->complex) /\ bel_supp (&2 * R0) v`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN CONJ_TAC THENL
     [MATCH_MP_TAC BEL_SMOOTH_MUL THEN ASM_REWRITE_TAC[ETA_AX; BEL_CUT_SMOOTH];
      MATCH_MP_TAC BEL_SUPP_MUL THEN ASM_SIMP_TAC[ETA_AX; BEL_CUT_SUPP]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. wirtinger_dz v z = wirtinger_dz u z * bel_cut R0 z +
                           u z * wirtinger_dz (bel_cut R0) z /\
        wirtinger_dbar v z = wirtinger_dbar u z * bel_cut R0 z +
                             u z * wirtinger_dbar (bel_cut R0) z`
  (LABEL_TAC "prod") THENL
   [GEN_TAC THEN EXPAND_TAC "v" THEN MATCH_MP_TAC BEL_WIRTINGER_MUL THEN
    CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(:complex)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; BEL_CUT_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN `(wirtinger_dz v) continuous_on (:complex) /\
                bel_supp (&2 * R0) (wirtinger_dz v) /\
                (wirtinger_dbar v) continuous_on (:complex) /\
                bel_supp (&2 * R0) (wirtinger_dbar v)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`&2 * R0`; `v:complex->complex`] BEL_SUPP_WIRTINGER) THEN
    MP_TAC(ISPEC `v:complex->complex` BEL_SMOOTH_WIRTINGER) THEN
    ASM_SIMP_TAC[BEL_SMOOTH_C1; SMOOTH_MAP_ON_CONTINUOUS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `drop(integral (cball(Cx(&0),rho)) (\z. lift(norm(wirtinger_dz u z) pow 2))) =
    drop(integral (cball(Cx(&0),rho)) (\z. lift(norm(wirtinger_dz v z) pow 2)))`
  SUBST1_TAC THENL
   [AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `z:complex` THEN
    REWRITE_TAC[IN_CBALL; dist; COMPLEX_SUB_LZERO; NORM_NEG] THEN DISCH_TAC THEN
    REMOVE_THEN "prod" (fun th -> REWRITE_TAC[CONJUNCT1(SPEC `z:complex` th)]) THEN
    SUBGOAL_THEN `bel_cut R0 z = Cx(&1) /\ wirtinger_dz (bel_cut R0) z = Cx(&0)`
    (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC BEL_CUT_ONE THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[WIRTINGER_DZ_FRECHET] THEN
        MP_TAC(SPECL [`R0:real`; `z:complex`] BEL_CUT_DERIV_ZERO) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
        REWRITE_TAC[COMPLEX_VEC_0] THEN CONV_TAC COMPLEX_RING];
      REWRITE_TAC[COMPLEX_MUL_RID; COMPLEX_MUL_RZERO; COMPLEX_ADD_RID]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (:complex) (\z. lift(norm(wirtinger_dz v z) pow 2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
    REWRITE_TAC[SUBSET_UNIV; LIFT_DROP; REAL_LE_POW_2] THEN CONJ_TAC THENL
     [MATCH_MP_TAC BEL_SQ_INTEGRABLE_SUBSET THEN EXISTS_TAC `&2 * R0` THEN
      ASM_REWRITE_TAC[ETA_AX; LEBESGUE_MEASURABLE_CBALL];
      MATCH_MP_TAC BEL_SQ_INTEGRABLE THEN EXISTS_TAC `&2 * R0` THEN
      ASM_REWRITE_TAC[ETA_AX]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`&2 * R0`; `v:complex->complex`] BEL_DZ_DBAR_L2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC]) THEN
  (SUBGOAL_THEN
   `!z. norm(wirtinger_dbar v z) pow 2 <=
        (&1 + e) * norm((g:complex->complex) z) pow 2 +
        (&1 + inv e) * (if z IN cball(Cx(&0),&2 * R0) then (c * K / R0 pow 2) pow 2
                        else &0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:complex` THEN
    REMOVE_THEN "prod" (fun th -> REWRITE_TAC[CONJUNCT2(SPEC `z:complex` th)]) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(g:complex->complex) z * bel_cut R0 z = g z` SUBST1_TAC THENL
     [ASM_CASES_TAC `norm(z:complex) <= R1` THENL
       [MP_TAC(SPECL [`R0:real`; `z:complex`] BEL_CUT_ONE) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[COMPLEX_MUL_RID]];
        UNDISCH_TAC `bel_supp R1 (g:complex->complex)` THEN REWRITE_TAC[bel_supp] THEN
        DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[COMPLEX_MUL_LZERO]]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + e) * norm((g:complex->complex) z) pow 2 +
                (&1 + inv e) * norm((u:complex->complex) z *
                                    wirtinger_dbar (bel_cut R0) z) pow 2` THEN
    ASM_SIMP_TAC[BEL_SQ_SPLIT] THEN
    MATCH_MP_TAC REAL_LE_LADD_IMP THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
      MP_TAC(ISPECL [`u:complex->complex`; `K:real`; `c:real`; `R0:real`]
                    BEL_CUT_ERROR_BOUND) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC]) THEN
  (SUBGOAL_THEN
   `(\z. (&1 + e) % lift(norm((g:complex->complex) z) pow 2)) integrable_on (:complex) /\
    (\z. (&1 + inv e) % (if z IN cball(Cx(&0),&2 * R0)
                         then lift((c * K / R0 pow 2) pow 2) else vec 0))
    integrable_on (:complex)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_CMUL THENL
     [MATCH_MP_TAC BEL_SQ_INTEGRABLE THEN EXISTS_TAC `R1:real` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS];
      REWRITE_TAC[BEL_INDICATOR_INTEGRAL]];
    ALL_TAC]) THEN
  (MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (:complex)
                (\z. (&1 + e) % lift(norm((g:complex->complex) z) pow 2) +
                     (&1 + inv e) % (if z IN cball(Cx(&0),&2 * R0)
                                     then lift((c * K / R0 pow 2) pow 2) else vec 0)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC BEL_SQ_INTEGRABLE THEN EXISTS_TAC `&2 * R0` THEN
      ASM_REWRITE_TAC[ETA_AX];
      MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
      REWRITE_TAC[DROP_ADD; DROP_CMUL; LIFT_DROP] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `z:complex`) THEN
      COND_CASES_TAC THEN REWRITE_TAC[DROP_VEC; LIFT_DROP] THEN REAL_ARITH_TAC];
    ALL_TAC]) THEN
  (MP_TAC(ISPECL [`\z. (&1 + e) % lift(norm((g:complex->complex) z) pow 2)`;
                 `\z. (&1 + inv e) % (if z IN cball(Cx(&0),&2 * R0)
                                      then lift((c * K / R0 pow 2) pow 2) else vec 0)`;
                 `(:complex)`] INTEGRAL_ADD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DROP_ADD] THEN
  MP_TAC(ISPECL [`\z. lift(norm((g:complex->complex) z) pow 2)`; `&1 + e`; `(:complex)`]
                INTEGRAL_CMUL) THEN
  MP_TAC(ISPECL [`\z. if z IN cball(Cx(&0),&2 * R0)
                      then lift((c * K / R0 pow 2) pow 2) else vec 0:real^1`;
                 `&1 + inv e`; `(:complex)`] INTEGRAL_CMUL) THEN
  REWRITE_TAC[BEL_INDICATOR_INTEGRAL]) THEN
  (DISCH_THEN SUBST1_TAC THEN ANTS_TAC THENL
   [MATCH_MP_TAC BEL_SQ_INTEGRABLE THEN EXISTS_TAC `R1:real` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[DROP_CMUL; BEL_INDICATOR_INTEGRAL] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= e ==> a + y <= a + e`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&1 + inv e) * ((c * K / R0 pow 2) pow 2 * (&4 * R0) pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      MP_TAC(ISPECL [`Cx(&0)`; `&2 * R0`] MEASURE_CBALL_BOUND) THEN
      REWRITE_TAC[DIMINDEX_2] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c * K / R0 pow 2) pow 2 * (&4 * R0) pow 2 =
                (&16 * (c * K) pow 2) / R0 pow 2` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < R0` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `a * b / c = (a * b) / c`] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT]));;

let BEL_S_L2 = prove
 (`!R g rho.
        smooth_map_on (:complex) g /\ bel_supp R g
        ==> drop(integral (cball(Cx(&0),rho)) (\z. lift(norm(bel_s g z) pow 2)))
            <= drop(integral (:complex) (\z. lift(norm(g z) pow 2)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `R1 = abs R + &1` THEN
  SUBGOAL_THEN `&0 < R1 /\ bel_supp R1 (g:complex->complex)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "R1" THEN CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC BEL_SUPP_MONO THEN EXISTS_TAC `R:real` THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`R1:real`; `g:complex->complex`] BEL_SUPP_BOUNDED_FN) THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS] THEN DISCH_THEN(X_CHOOSE_TAC `M:real`) THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
   [ASM_MESON_TAC[NORM_POS_LE; REAL_LE_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &2 * inv pi * M * measure(ball(Cx(&0),abs R1 + &1))` MP_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; REAL_LE_INV_EQ; PI_POS_LE; MEASURE_POS_LE; MEASURABLE_BALL];
    ALL_TAC] THEN
  ABBREV_TAC `K = &2 * inv pi * M * measure(ball(Cx(&0),abs R1 + &1))` THEN
  DISCH_TAC THEN
  X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC BEL_CUT_WIRTINGER_BOUND THEN
  SUBGOAL_THEN `!z. bel_s g z = wirtinger_dz (bel_ct g) z` (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC BEL_CT_DZ THEN
    EXISTS_TAC `R1:real` THEN ASM_SIMP_TAC[BEL_SMOOTH_C1];
    ALL_TAC] THEN
  MATCH_MP_TAC BEL_EPS_LE THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_POS THEN REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN
    MATCH_MP_TAC BEL_SQ_INTEGRABLE THEN EXISTS_TAC `R1:real` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS];
    ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  ABBREV_TAC `Q = (&1 + inv e) * (&16 * (c * K) pow 2)` THEN
  SUBGOAL_THEN `&0 <= Q` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; REAL_LE_POW_2]];
    ALL_TAC] THEN
  MATCH_MP_TAC BEL_S_L2_EPS THEN
  MAP_EVERY EXISTS_TAC
   [`R1:real`; `K:real`; `c:real`;
    `max (max rho R1) (&2 * (abs R1 + &1)) + Q / e + &1`] THEN
  ABBREV_TAC `R0 = max (max rho R1) (&2 * (abs R1 + &1)) + Q / e + &1` THEN
  SUBGOAL_THEN `&0 <= Q / e` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC BEL_CT_SMOOTH THEN EXISTS_TAC `R1:real` THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN MATCH_MP_TAC BEL_CT_DBAR THEN EXISTS_TAC `R1:real` THEN
    ASM_SIMP_TAC[BEL_SMOOTH_C1];
    X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`R1:real`; `g:complex->complex`; `M:real`; `z:complex`]
                  BEL_CT_DECAY) THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS] THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "K" THEN MATCH_MP_TAC(REAL_ARITH `a = b ==> x <= a ==> x <= b`) THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e * R0` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `Q = e * (Q / e)` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < e` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_POW_2] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]]);;

(* ========================================================================= *)
(* The L^2 norm, the operator T g = mu S g, its derivatives, a               *)
(* sup bound by the L^2 norm of the second derivative (a Pompeiu identity    *)
(* with the bounded kernel (cnj(w - z))/(w - z)).                            *)
(* ========================================================================= *)

let bel_n2 = new_definition
 `bel_n2 (g:complex->complex) = lnorm (:complex) (&2) g`;;

let bel_tt = new_definition
 `bel_tt (mu:complex->complex) (g:complex->complex) = \z. mu z * bel_s g z`;;

let BEL_LSPACE2 = prove
 (`!R g:complex->complex.
        g continuous_on (:complex) /\ bel_supp R g ==> g IN lspace (:complex) (&2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LSPACE_ALT; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[CONTINUOUS_IMP_MEASURABLE_ON; RPOW_POW] THEN
  MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN CONJ_TAC THENL
   [SIMP_TAC[DIMINDEX_1; ARITH_RULE `1 <= i /\ i <= 1 <=> i = 1`] THEN
    SIMP_TAC[GSYM drop; LIFT_DROP; REAL_LE_POW_2];
    MATCH_MP_TAC BEL_SQ_INTEGRABLE THEN EXISTS_TAC `R:real` THEN ASM_REWRITE_TAC[]]);;

let BEL_N2_SQ = prove
 (`!R g:complex->complex.
        g continuous_on (:complex) /\ bel_supp R g
        ==> bel_n2 g pow 2 = drop(integral (:complex) (\z. lift(norm(g z) pow 2)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bel_n2] THEN
  MP_TAC(ISPECL [`(:complex)`; `&2`; `g:complex->complex`] LNORM_RPOW) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC BEL_LSPACE2 THEN ASM_MESON_TAC[]; REAL_ARITH_TAC];
    REWRITE_TAC[RPOW_POW]]);;

let BEL_N2_POS = prove
 (`!R g:complex->complex.
        g continuous_on (:complex) /\ bel_supp R g ==> &0 <= bel_n2 g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bel_n2] THEN MATCH_MP_TAC LNORM_POS_LE THEN
  MATCH_MP_TAC BEL_LSPACE2 THEN ASM_MESON_TAC[]);;

let BEL_N2_LE_SQ = prove
 (`!R g:complex->complex B.
        g continuous_on (:complex) /\ bel_supp R g /\ &0 <= B /\
        drop(integral (:complex) (\z. lift(norm(g z) pow 2))) <= B pow 2
        ==> bel_n2 g <= B`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
  ASM_REWRITE_TAC[ARITH] THEN ASM_MESON_TAC[BEL_N2_SQ]);;

let BEL_N2_TRIANGLE = prove
 (`!R f g:complex->complex.
        f continuous_on (:complex) /\ bel_supp R f /\
        g continuous_on (:complex) /\ bel_supp R g
        ==> bel_n2 (\z. f z + g z) <= bel_n2 f + bel_n2 g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bel_n2] THEN MATCH_MP_TAC LNORM_TRIANGLE THEN
  REWRITE_TAC[REAL_ARITH `&1 <= &2`] THEN CONJ_TAC THEN
  MATCH_MP_TAC BEL_LSPACE2 THEN ASM_MESON_TAC[]);;

let BEL_N2_LMUL = prove
 (`!R c f:complex->complex.
        f continuous_on (:complex) /\ bel_supp R f
        ==> bel_n2 (\z. c * f z) = norm c * bel_n2 f`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= bel_n2 (\z. c * (f:complex->complex) z) /\ &0 <= bel_n2 f /\
                bel_n2 (\z. c * f z) pow 2 = (norm c * bel_n2 f) pow 2`
  MP_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC BEL_N2_POS THEN EXISTS_TAC `R:real` THEN
      ASM_SIMP_TAC[CONTINUOUS_ON_COMPLEX_LMUL; BEL_SUPP_LMUL];
      MATCH_MP_TAC BEL_N2_POS THEN EXISTS_TAC `R:real` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_POW_MUL] THEN
      MP_TAC(ISPECL [`R:real`; `\z. c * (f:complex->complex) z`] BEL_N2_SQ) THEN
      MP_TAC(ISPECL [`R:real`; `f:complex->complex`] BEL_N2_SQ) THEN
      ASM_SIMP_TAC[CONTINUOUS_ON_COMPLEX_LMUL; BEL_SUPP_LMUL] THEN
      REPEAT(DISCH_THEN SUBST1_TAC) THEN
      REWRITE_TAC[COMPLEX_NORM_MUL; REAL_POW_MUL] THEN
      REWRITE_TAC[LIFT_CMUL] THEN
      MP_TAC(ISPECL [`\z. lift(norm((f:complex->complex) z) pow 2)`; `norm(c:complex) pow 2`;
                     `(:complex)`] INTEGRAL_CMUL) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC BEL_SQ_INTEGRABLE THEN EXISTS_TAC `R:real` THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DROP_CMUL]]];
    STRIP_TAC THEN MATCH_MP_TAC REAL_POW_EQ THEN EXISTS_TAC `2` THEN
    ASM_SIMP_TAC[ARITH_EQ; REAL_LE_MUL; NORM_POS_LE]]);;

let BEL_N2_ZERO = prove
 (`bel_n2 (\z. Cx(&0)) = &0`,
  REWRITE_TAC[bel_n2; GSYM COMPLEX_VEC_0] THEN MATCH_MP_TAC LNORM_0 THEN REAL_ARITH_TAC);;

let BEL_N2_MONO = prove
 (`!R f g:complex->complex.
        f continuous_on (:complex) /\ bel_supp R f /\
        g continuous_on (:complex) /\ bel_supp R g /\
        (!z. norm(f z) <= norm(g z))
        ==> bel_n2 f <= bel_n2 g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bel_n2] THEN MATCH_MP_TAC LNORM_MONO THEN
  EXISTS_TAC `{}:complex->bool` THEN
  ASM_REWRITE_TAC[NEGLIGIBLE_EMPTY; DIFF_EMPTY; REAL_POS] THEN
  CONJ_TAC THEN MATCH_MP_TAC BEL_LSPACE2 THEN ASM_MESON_TAC[]);;

let BEL_INTEGRAL_SQ_RESTRICT = prove
 (`!R f:complex->complex.
        bel_supp R f
        ==> integral (:complex) (\z. lift(norm(f z) pow 2)) =
            integral (cball(Cx(&0),R)) (\z. lift(norm(f z) pow 2))`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM INTEGRAL_RESTRICT_UNIV] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:complex` THEN
  REWRITE_TAC[IN_CBALL; dist; COMPLEX_SUB_LZERO; NORM_NEG] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  UNDISCH_TAC `bel_supp R (f:complex->complex)` THEN REWRITE_TAC[bel_supp] THEN
  DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[COMPLEX_NORM_0; REAL_ARITH `&0 pow 2 = &0`; LIFT_NUM]);;

let BEL_N2_BOUND = prove
 (`!R f:complex->complex M.
        f continuous_on (:complex) /\ bel_supp R f /\ (!z. norm(f z) <= M)
        ==> bel_n2 f <= M * sqrt(measure(cball(Cx(&0),R)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
   [ASM_MESON_TAC[NORM_POS_LE; REAL_LE_TRANS]; ALL_TAC] THEN
  MATCH_MP_TAC BEL_N2_LE_SQ THEN EXISTS_TAC `R:real` THEN
  ASM_SIMP_TAC[REAL_LE_MUL; SQRT_POS_LE; MEASURE_POS_LE; MEASURABLE_CBALL] THEN
  ASM_SIMP_TAC[BEL_INTEGRAL_SQ_RESTRICT] THEN
  REWRITE_TAC[REAL_POW_MUL] THEN
  SIMP_TAC[SQRT_POW_2; MEASURE_POS_LE; MEASURABLE_CBALL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (cball(Cx(&0),R)) (\z:complex. lift(M pow 2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN
    REWRITE_TAC[INTEGRABLE_ON_CONST; MEASURABLE_CBALL; LIFT_DROP] THEN CONJ_TAC THENL
     [MATCH_MP_TAC BEL_SQ_INTEGRABLE_SUBSET THEN EXISTS_TAC `R:real` THEN
      ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_CBALL];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE]];
    SIMP_TAC[INTEGRAL_CONST_GEN; MEASURABLE_CBALL; DROP_CMUL; LIFT_DROP] THEN
    REAL_ARITH_TAC]);;

let BEL_CONT_INTEGRABLE_CBALL = prove
 (`!f:complex->real^N r. f continuous_on (:complex) ==> f integrable_on cball(Cx(&0),r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `cball(Cx(&0),r)` BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
  REWRITE_TAC[BOUNDED_CBALL; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:complex`; `b:complex`] THEN DISCH_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
  EXISTS_TAC `interval[a:complex,b]` THEN ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_CBALL] THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_CONTINUOUS THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET)) THEN
  REWRITE_TAC[SUBSET_UNIV]);;

let BEL_SQ_CONT_INTEGRABLE_CBALL = prove
 (`!f:complex->complex r.
        f continuous_on (:complex)
        ==> (\z. lift(norm(f z) pow 2)) integrable_on cball(Cx(&0),r)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BEL_CONT_INTEGRABLE_CBALL THEN
  MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN
  MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN ASM_REWRITE_TAC[]);;

(* The operator T and its L^2 bound.                                          *)

let BEL_TT_SMOOTH = prove
 (`!R mu g. smooth_map_on (:complex) mu /\ smooth_map_on (:complex) g /\ bel_supp R g
            ==> smooth_map_on (:complex) (bel_tt mu g)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bel_tt] THEN MATCH_MP_TAC BEL_SMOOTH_MUL THEN
  ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC BEL_S_SMOOTH THEN EXISTS_TAC `R:real` THEN
  ASM_REWRITE_TAC[]);;

let BEL_TT_SUPP = prove
 (`!rho mu g. bel_supp rho mu ==> bel_supp rho (bel_tt mu g)`,
  SIMP_TAC[bel_supp; bel_tt; COMPLEX_MUL_LZERO]);;

let BEL_TT_L2 = prove
 (`!rho R mu g k.
        smooth_map_on (:complex) mu /\ bel_supp rho mu /\ (!z. norm(mu z) <= k) /\
        smooth_map_on (:complex) g /\ bel_supp R g
        ==> bel_n2 (bel_tt mu g) <= k * bel_n2 g`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= k` ASSUME_TAC THENL
   [ASM_MESON_TAC[NORM_POS_LE; REAL_LE_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:complex) (bel_tt mu g) /\ bel_supp rho (bel_tt mu g)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[BEL_TT_SUPP] THEN MATCH_MP_TAC BEL_TT_SMOOTH THEN
    EXISTS_TAC `R:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC BEL_N2_LE_SQ THEN EXISTS_TAC `rho:real` THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC BEL_N2_POS THEN EXISTS_TAC `R:real` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`R:real`; `g:complex->complex`] BEL_N2_SQ) THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS; REAL_POW_MUL] THEN DISCH_THEN(K ALL_TAC) THEN
  MP_TAC(ISPECL [`rho:real`; `bel_tt mu g`] BEL_INTEGRAL_SQ_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (cball(Cx(&0),rho))
                 (\z. k pow 2 % lift(norm(bel_s g z) pow 2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC BEL_SQ_INTEGRABLE_SUBSET THEN EXISTS_TAC `rho:real` THEN
      REWRITE_TAC[ETA_AX] THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_CBALL; SMOOTH_MAP_ON_CONTINUOUS];
      MATCH_MP_TAC INTEGRABLE_CMUL THEN MATCH_MP_TAC BEL_SQ_CONT_INTEGRABLE_CBALL THEN
      REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN MATCH_MP_TAC BEL_S_SMOOTH THEN
      EXISTS_TAC `R:real` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
      REWRITE_TAC[bel_tt; DROP_CMUL; LIFT_DROP; COMPLEX_NORM_MUL; REAL_POW_MUL] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z. lift(norm(bel_s (g:complex->complex) z) pow 2)`; `k pow 2`;
                 `cball(Cx(&0),rho)`] INTEGRAL_CMUL) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC BEL_SQ_CONT_INTEGRABLE_CBALL THEN REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN MATCH_MP_TAC BEL_S_SMOOTH THEN
    EXISTS_TAC `R:real` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[DROP_CMUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[REAL_LE_POW_2] THEN MATCH_MP_TAC BEL_S_L2 THEN
  EXISTS_TAC `R:real` THEN ASM_REWRITE_TAC[]);;

(* Partial derivatives: algebra, commutation with S and with T.              *)

let BEL_SMOOTH_DIFFERENTIABLE = prove
 (`!f:complex->complex z. smooth_map_on (:complex) f ==> f differentiable at z`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `(:complex)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV]);;

let BEL_PD_MUL = prove
 (`!i f g:complex->complex z.
        f differentiable at z /\ g differentiable at z
        ==> partial_derivative i (\w. f w * g w) z =
            partial_derivative i f z * g z + f z * partial_derivative i g z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FRECHET_DERIVATIVE_WORKS; partial_derivative] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`( * ):complex->complex->complex`; `f:complex->complex`;
                 `g:complex->complex`; `frechet_derivative (f:complex->complex) (at z)`;
                 `frechet_derivative (g:complex->complex) (at z)`; `z:complex`]
                HAS_DERIVATIVE_BILINEAR_AT) THEN
  ASM_REWRITE_TAC[BILINEAR_COMPLEX_MUL] THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[] THEN CONV_TAC COMPLEX_RING);;

let BEL_DIFFERENTIABLE_MUL = prove
 (`!f g:complex->complex z.
        f differentiable at z /\ g differentiable at z
        ==> (\w. f w * g w) differentiable at z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[differentiable] THEN
  EXISTS_TAC `\d. (f:complex->complex) z * frechet_derivative g (at z) d +
                  frechet_derivative f (at z) d * g z` THEN
  MP_TAC(ISPECL [`( * ):complex->complex->complex`; `f:complex->complex`;
                 `g:complex->complex`; `frechet_derivative (f:complex->complex) (at z)`;
                 `frechet_derivative (g:complex->complex) (at z)`; `z:complex`]
                HAS_DERIVATIVE_BILINEAR_AT) THEN
  ASM_REWRITE_TAC[BILINEAR_COMPLEX_MUL; GSYM FRECHET_DERIVATIVE_WORKS]);;

let BEL_DIFFERENTIABLE_LMUL = prove
 (`!c f:complex->complex z.
        f differentiable at z ==> (\w. c * f w) differentiable at z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\w:complex. c:complex`; `f:complex->complex`; `z:complex`]
                BEL_DIFFERENTIABLE_MUL) THEN
  ASM_REWRITE_TAC[DIFFERENTIABLE_CONST]);;

let BEL_PD_LMUL = prove
 (`!i c f:complex->complex z.
        f differentiable at z
        ==> partial_derivative i (\w. c * f w) z = c * partial_derivative i f z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`i:num`; `\w:complex. c:complex`; `f:complex->complex`; `z:complex`]
                BEL_PD_MUL) THEN
  ASM_REWRITE_TAC[DIFFERENTIABLE_CONST; PARTIAL_DERIVATIVE_CONST] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_MUL_LZERO; COMPLEX_ADD_LID]);;

let BEL_PD_LINCOMB = prove
 (`!i a b f g:complex->complex z.
        f differentiable at z /\ g differentiable at z
        ==> partial_derivative i (\w. a * f w + b * g w) z =
            a * partial_derivative i f z + b * partial_derivative i g z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`i:num`; `\w:complex. a * (f:complex->complex) w`;
                 `\w:complex. b * (g:complex->complex) w`; `z:complex`]
                PARTIAL_DERIVATIVE_ADD) THEN
  ASM_SIMP_TAC[BEL_DIFFERENTIABLE_LMUL; BEL_PD_LMUL]);;

let BEL_WIRTINGER_PD = prove
 (`!h:complex->complex.
        wirtinger_dbar h =
        (\w. inv(Cx(&2)) * partial_derivative 1 h w +
             (ii * inv(Cx(&2))) * partial_derivative 2 h w) /\
        wirtinger_dz h =
        (\w. inv(Cx(&2)) * partial_derivative 1 h w +
             (--ii * inv(Cx(&2))) * partial_derivative 2 h w)`,
  REWRITE_TAC[BEL_PARTIAL_COMPLEX; GSYM BEL_WIRTINGER_FUN]);;

let BEL_SCHWARZ = prove
 (`!f:complex->complex i j z.
        smooth_map_on (:complex) f /\ 1 <= i /\ i <= 2 /\ 1 <= j /\ j <= 2
        ==> partial_derivative i (partial_derivative j f) z =
            partial_derivative j (partial_derivative i f) z`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PARTIAL_DERIVATIVE_SYM THEN
  EXISTS_TAC `(:complex)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; DIMINDEX_2] THEN
  ASM_MESON_TAC[smooth_map_on]);;

let BEL_WIRT_PARTIAL = prove
 (`!g:complex->complex i.
        smooth_map_on (:complex) g /\ 1 <= i /\ i <= 2
        ==> partial_derivative i (wirtinger_dz g) = wirtinger_dz (partial_derivative i g) /\
            partial_derivative i (wirtinger_dbar g) =
            wirtinger_dbar (partial_derivative i g)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!j. smooth_map_on (:complex) (partial_derivative j (g:complex->complex))`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN
    ASM_REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[BEL_WIRTINGER_PD; FUN_EQ_THM] THEN CONJ_TAC THEN
  X_GEN_TAC `z:complex` THEN
  W(fun (asl,w) ->
    let lam = rand(rator(lhs w)) in
    let bod = body lam in
    let a = lhand(lhand bod) and f = rator(rand(lhand bod))
    and b = lhand(rand bod) and g' = rator(rand(rand bod)) in
    MP_TAC(ISPECL [`i:num`; a; b; f; g'; `z:complex`] BEL_PD_LINCOMB)) THEN
  ASM_SIMP_TAC[BEL_SMOOTH_DIFFERENTIABLE] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[BEL_SCHWARZ; ARITH]);;

let BEL_S_PARTIAL = prove
 (`!R g:complex->complex i.
        smooth_map_on (:complex) g /\ bel_supp R g /\ 1 <= i /\ i <= 2
        ==> partial_derivative i (bel_s g) = bel_s (partial_derivative i g)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bel_s] THEN
  MP_TAC(ISPECL [`R:real`; `wirtinger_dz (g:complex->complex)`; `i:num`] BEL_CT_PARTIAL) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[BEL_SMOOTH_WIRTINGER] THEN
    MP_TAC(ISPECL [`R:real`; `g:complex->complex`] BEL_SUPP_WIRTINGER) THEN
    ASM_SIMP_TAC[BEL_SMOOTH_C1];
    DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN ASM_SIMP_TAC[BEL_WIRT_PARTIAL]);;

let BEL_TT_PARTIAL = prove
 (`!R mu g:complex->complex i.
        smooth_map_on (:complex) mu /\ smooth_map_on (:complex) g /\ bel_supp R g /\
        1 <= i /\ i <= 2
        ==> partial_derivative i (bel_tt mu g) =
            (\z. bel_tt (partial_derivative i mu) g z + bel_tt mu (partial_derivative i g) z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bel_tt; FUN_EQ_THM] THEN X_GEN_TAC `z:complex` THEN
  MP_TAC(ISPECL [`i:num`; `mu:complex->complex`; `bel_s (g:complex->complex)`; `z:complex`]
                BEL_PD_MUL) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[BEL_SMOOTH_DIFFERENTIABLE] THEN MATCH_MP_TAC BEL_SMOOTH_DIFFERENTIABLE THEN
    MATCH_MP_TAC BEL_S_SMOOTH THEN EXISTS_TAC `R:real` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[ETA_AX] THEN DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`R:real`; `g:complex->complex`; `i:num`] BEL_S_PARTIAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

(* ========================================================================= *)
(* Sobolev-type norms E_m (sums of L^2 norms of derivatives up               *)
(* to order m, defined recursively), their calculus, the Leibniz bound for  *)
(* T, and uniform bounds for the Neumann iterates u_(n+1) = T u_n.           *)
(* ========================================================================= *)

let bel_en = define
 `(bel_en 0 (g:complex->complex) = bel_n2 g) /\
  (bel_en (SUC m) g = bel_en m g + bel_en m (partial_derivative 1 g) +
                      bel_en m (partial_derivative 2 g))`;;

let bel_fn = define
 `(bel_fn 0 (g:complex->complex) = &0) /\
  (bel_fn (SUC m) g = bel_en m g)`;;

let BEL_SMOOTH_PD = prove
 (`!R g:complex->complex i.
        smooth_map_on (:complex) g /\ bel_supp R g
        ==> smooth_map_on (:complex) (partial_derivative i g) /\
            bel_supp R (partial_derivative i g)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`[i:num]`; `R:real`; `g:complex->complex`] BEL_SUPP_ITERATED_PARTIAL) THEN
  ASM_REWRITE_TAC[iterated_partial]);;

let BEL_SMOOTH_PD_SMOOTH = prove
 (`!g:complex->complex i.
        smooth_map_on (:complex) g ==> smooth_map_on (:complex) (partial_derivative i g)`,
  SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; OPEN_UNIV]);;

let BEL_SUPP_PD = prove
 (`!R g:complex->complex i.
        smooth_map_on (:complex) g /\ bel_supp R g ==> bel_supp R (partial_derivative i g)`,
  MESON_TAC[BEL_SMOOTH_PD]);;

let BEL_EN_POS = prove
 (`!m R g:complex->complex.
        smooth_map_on (:complex) g /\ bel_supp R g ==> &0 <= bel_en m g`,
  INDUCT_TAC THEN REWRITE_TAC[bel_en] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC BEL_N2_POS THEN EXISTS_TAC `R:real` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS];
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b /\ &0 <= c ==> &0 <= a + b + c`) THEN
    REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `R:real` THEN
    ASM_SIMP_TAC[BEL_SMOOTH_PD_SMOOTH; BEL_SUPP_PD]]);;

let BEL_FN_LE_EN = prove
 (`!m R g:complex->complex.
        smooth_map_on (:complex) g /\ bel_supp R g ==> bel_fn m g <= bel_en m g`,
  INDUCT_TAC THEN REWRITE_TAC[bel_en; bel_fn] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC BEL_N2_POS THEN EXISTS_TAC `R:real` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS];
    MATCH_MP_TAC(REAL_ARITH `&0 <= b /\ &0 <= c ==> a <= a + b + c`) THEN
    CONJ_TAC THEN MATCH_MP_TAC BEL_EN_POS THEN EXISTS_TAC `R:real` THEN
    ASM_SIMP_TAC[BEL_SMOOTH_PD_SMOOTH; BEL_SUPP_PD]]);;

let BEL_FN_POS = prove
 (`!m R g:complex->complex.
        smooth_map_on (:complex) g /\ bel_supp R g ==> &0 <= bel_fn m g`,
  INDUCT_TAC THEN REWRITE_TAC[bel_fn; REAL_LE_REFL] THEN
  MESON_TAC[BEL_EN_POS]);;

let BEL_EN_PD_LE = prove
 (`!m R g:complex->complex.
        smooth_map_on (:complex) g /\ bel_supp R g
        ==> bel_en m (partial_derivative 1 g) <= bel_en (SUC m) g /\
            bel_en m (partial_derivative 2 g) <= bel_en (SUC m) g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[bel_en] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b /\ &0 <= c
                           ==> b <= a + b + c /\ c <= a + b + c`) THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC BEL_EN_POS THEN EXISTS_TAC `R:real` THEN
  ASM_SIMP_TAC[BEL_SMOOTH_PD_SMOOTH; BEL_SUPP_PD]);;

let BEL_PD_ADD_FUN = prove
 (`!i f g:complex->complex.
        smooth_map_on (:complex) f /\ smooth_map_on (:complex) g
        ==> partial_derivative i (\z. f z + g z) =
            (\z. partial_derivative i f z + partial_derivative i g z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  MATCH_MP_TAC PARTIAL_DERIVATIVE_ADD THEN ASM_SIMP_TAC[BEL_SMOOTH_DIFFERENTIABLE]);;

let BEL_PD_LMUL_FUN = prove
 (`!i c f:complex->complex.
        smooth_map_on (:complex) f
        ==> partial_derivative i (\z. c * f z) = (\z. c * partial_derivative i f z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  MATCH_MP_TAC BEL_PD_LMUL THEN ASM_SIMP_TAC[BEL_SMOOTH_DIFFERENTIABLE]);;

let BEL_EN_ADD = prove
 (`!m R f g:complex->complex.
        smooth_map_on (:complex) f /\ bel_supp R f /\
        smooth_map_on (:complex) g /\ bel_supp R g
        ==> bel_en m (\z. f z + g z) <= bel_en m f + bel_en m g`,
  INDUCT_TAC THEN REWRITE_TAC[bel_en] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC BEL_N2_TRIANGLE THEN EXISTS_TAC `R:real` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS];
    ASM_SIMP_TAC[BEL_PD_ADD_FUN] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= a1 + a2 /\ b <= b1 + b2 /\ c <= c1 + c2
                             ==> a + b + c <= (a1 + b1 + c1) + (a2 + b2 + c2)`) THEN
    REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `R:real` THEN
    ASM_SIMP_TAC[BEL_SMOOTH_PD_SMOOTH; BEL_SUPP_PD]]);;

let BEL_EN_LMUL = prove
 (`!m R c f:complex->complex.
        smooth_map_on (:complex) f /\ bel_supp R f
        ==> bel_en m (\z. c * f z) = norm c * bel_en m f`,
  INDUCT_TAC THEN REWRITE_TAC[bel_en] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC BEL_N2_LMUL THEN EXISTS_TAC `R:real` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS];
    ASM_SIMP_TAC[BEL_PD_LMUL_FUN] THEN
    SUBGOAL_THEN `!i. bel_en m (\z. c * partial_derivative i (f:complex->complex) z) =
                      norm c * bel_en m (partial_derivative i f)`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `R:real` THEN
      ASM_SIMP_TAC[BEL_SMOOTH_PD_SMOOTH; BEL_SUPP_PD];
      FIRST_X_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th (CONJ
        (ASSUME `smooth_map_on (:complex) (f:complex->complex)`)
        (ASSUME `bel_supp R (f:complex->complex)`))]) THEN
      REAL_ARITH_TAC]]);;

let BEL_EN_ITERATED = prove
 (`!l a R g:complex->complex.
        smooth_map_on (:complex) g /\ bel_supp R g /\ ALL (\i. i = 1 \/ i = 2) l
        ==> bel_en a (iterated_partial l g) <= bel_en (a + LENGTH l) g`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[iterated_partial; LENGTH; ADD_CLAUSES; REAL_LE_REFL; ALL] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `bel_en (SUC a) (iterated_partial t (g:complex->complex))` THEN
  CONJ_TAC THEN
  TRY(MP_TAC(ISPECL [`a:num`; `R:real`; `iterated_partial t (g:complex->complex)`]
                    BEL_EN_PD_LE) THEN
      ANTS_TAC THENL [MATCH_MP_TAC BEL_SUPP_ITERATED_PARTIAL THEN ASM_REWRITE_TAC[];
                      SIMP_TAC[]] THEN NO_TAC) THEN
  (FIRST_X_ASSUM(MP_TAC o SPECL [`SUC a`; `R:real`; `g:complex->complex`]) THEN
   ASM_REWRITE_TAC[ADD_CLAUSES]));;

let BEL_N2_ITERATED = prove
 (`!l R g:complex->complex.
        smooth_map_on (:complex) g /\ bel_supp R g /\ ALL (\i. i = 1 \/ i = 2) l
        ==> bel_n2 (iterated_partial l g) <= bel_en (LENGTH l) g`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:num list`; `0`; `R:real`; `g:complex->complex`] BEL_EN_ITERATED) THEN
  ASM_REWRITE_TAC[bel_en; ADD_CLAUSES]);;

let BEL_EN_WIRT = prove
 (`!a R h:complex->complex.
        smooth_map_on (:complex) h /\ bel_supp R h
        ==> bel_en a (wirtinger_dbar h) <= bel_en (SUC a) h /\
            bel_en a (wirtinger_dz h) <= bel_en (SUC a) h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[BEL_WIRTINGER_PD] THEN
  SUBGOAL_THEN
   `!c1 c2. norm(c1:complex) = &1 / &2 /\ norm(c2:complex) = &1 / &2
            ==> bel_en a (\z. c1 * partial_derivative 1 h z +
                              c2 * partial_derivative 2 (h:complex->complex) z)
                <= bel_en (SUC a) h`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`a:num`; `R:real`;
                   `\w. c1 * partial_derivative 1 (h:complex->complex) w`;
                   `\w. c2 * partial_derivative 2 (h:complex->complex) w`] BEL_EN_ADD) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN
      TRY(MATCH_MP_TAC BEL_SMOOTH_LMUL THEN
          ASM_SIMP_TAC[ETA_AX; BEL_SMOOTH_PD_SMOOTH] THEN NO_TAC) THEN
      MATCH_MP_TAC BEL_SUPP_LMUL THEN ASM_SIMP_TAC[ETA_AX; BEL_SUPP_PD];
      REWRITE_TAC[]] THEN
    MP_TAC(ISPECL [`a:num`; `R:real`; `c1:complex`;
                   `partial_derivative 1 (h:complex->complex)`] BEL_EN_LMUL) THEN
    MP_TAC(ISPECL [`a:num`; `R:real`; `c2:complex`;
                   `partial_derivative 2 (h:complex->complex)`] BEL_EN_LMUL) THEN
    ASM_SIMP_TAC[BEL_SMOOTH_PD_SMOOTH; BEL_SUPP_PD] THEN
    REPEAT(DISCH_THEN SUBST1_TAC) THEN
    MP_TAC(ISPECL [`a:num`; `R:real`; `h:complex->complex`] BEL_EN_PD_LE) THEN
    MP_TAC(ISPECL [`a:num`; `R:real`; `partial_derivative 1 (h:complex->complex)`]
                  BEL_EN_POS) THEN
    MP_TAC(ISPECL [`a:num`; `R:real`; `partial_derivative 2 (h:complex->complex)`]
                  BEL_EN_POS) THEN
    ASM_SIMP_TAC[BEL_SMOOTH_PD_SMOOTH; BEL_SUPP_PD] THEN REAL_ARITH_TAC;
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_INV; COMPLEX_NORM_CX; COMPLEX_NORM_II;
                NORM_NEG] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV]);;

let BEL_PD_ITERATED_APPEND = prove
 (`!l i g:complex->complex.
        iterated_partial l (partial_derivative i g) = iterated_partial (APPEND l [i]) g`,
  REWRITE_TAC[ITERATED_PARTIAL_APPEND; iterated_partial]);;

let BEL_EN_BOUND = prove
 (`!m R M g:complex->complex.
        smooth_map_on (:complex) g /\ bel_supp R g /\
        (!l z. LENGTH l <= m /\ ALL (\i. i = 1 \/ i = 2) l
               ==> norm(iterated_partial l g z) <= M)
        ==> bel_en m g <= &3 pow m * M * sqrt(measure(cball(Cx(&0),R)))`,
  INDUCT_TAC THEN REWRITE_TAC[bel_en] THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[real_pow; REAL_MUL_LID] THEN MATCH_MP_TAC BEL_N2_BOUND THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `[]:num list`) THEN
    REWRITE_TAC[LENGTH; ALL; iterated_partial; LE_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[real_pow; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= x /\ b <= x /\ c <= x ==> a + b + c <= &3 * x`) THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[BEL_SMOOTH_PD_SMOOTH; BEL_SUPP_PD] THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
    ASM_ARITH_TAC;
    REPEAT STRIP_TAC THEN REWRITE_TAC[BEL_PD_ITERATED_APPEND] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; ALL_APPEND; ALL] THEN ASM_ARITH_TAC;
    REPEAT STRIP_TAC THEN REWRITE_TAC[BEL_PD_ITERATED_APPEND] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; ALL_APPEND; ALL] THEN ASM_ARITH_TAC]);;

let BEL_FN_PD_LE = prove
 (`!m R g:complex->complex.
        smooth_map_on (:complex) g /\ bel_supp R g
        ==> bel_fn m (partial_derivative 1 g) <= bel_en m g /\
            bel_fn m (partial_derivative 2 g) <= bel_en m g`,
  INDUCT_TAC THEN REWRITE_TAC[bel_fn] THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [MATCH_MP_TAC BEL_EN_POS THEN EXISTS_TAC `R:real` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC BEL_EN_PD_LE THEN EXISTS_TAC `R:real` THEN ASM_REWRITE_TAC[]]);;

let BEL_EN_TT = prove
 (`!m M. ?K. &0 <= K /\
       !mu g:complex->complex rho R k.
          smooth_map_on (:complex) mu /\ bel_supp rho mu /\ (!z. norm(mu z) <= k) /\
          (!l z. LENGTH l <= m /\ ALL (\i. i = 1 \/ i = 2) l
                 ==> norm(iterated_partial l mu z) <= M) /\
          smooth_map_on (:complex) g /\ bel_supp R g
          ==> bel_en m (bel_tt mu g) <= k * bel_en m g + K * bel_fn m g`,
  INDUCT_TAC THENL
   [GEN_TAC THEN EXISTS_TAC `&0` THEN
    REWRITE_TAC[REAL_LE_REFL; bel_en; bel_fn; REAL_MUL_LZERO; REAL_ADD_RID] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC BEL_TT_L2 THEN
    MAP_EVERY EXISTS_TAC [`rho:real`; `R:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `M:real` THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `K0:real` STRIP_ASSUME_TAC o SPEC `M:real`) THEN
  EXISTS_TAC `&5 * K0 + &2 * abs M` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!i. i = 1 \/ i = 2
                    ==> smooth_map_on (:complex) (partial_derivative i (mu:complex->complex)) /\
                        bel_supp rho (partial_derivative i mu) /\
                        (!z. norm(partial_derivative i mu z) <= M) /\
                        (!l z. LENGTH l <= m /\ ALL (\i. i = 1 \/ i = 2) l
                               ==> norm(iterated_partial l (partial_derivative i mu) z) <= M) /\
                        smooth_map_on (:complex) (partial_derivative i (g:complex->complex)) /\
                        bel_supp R (partial_derivative i g)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[BEL_SMOOTH_PD_SMOOTH; BEL_SUPP_PD] THEN CONJ_TAC THENL
     [X_GEN_TAC `z:complex` THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`[i:num]`; `z:complex`]) THEN
      ASM_REWRITE_TAC[iterated_partial; LENGTH; ALL] THEN
      ANTS_TAC THENL [ARITH_TAC; REWRITE_TAC[]];
      REPEAT STRIP_TAC THEN REWRITE_TAC[BEL_PD_ITERATED_APPEND] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; ALL_APPEND; ALL] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!l z. LENGTH l <= m /\ ALL (\i. i = 1 \/ i = 2) l
                      ==> norm(iterated_partial l (mu:complex->complex) z) <= M`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i = 1 \/ i = 2
        ==> bel_en m (partial_derivative i (bel_tt mu (g:complex->complex))) <=
            (M * bel_en m g + K0 * bel_fn m g) +
            (k * bel_en m (partial_derivative i g) + K0 * bel_fn m (partial_derivative i g))`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `i = 1 \/ i = 2`)) THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`R:real`; `mu:complex->complex`; `g:complex->complex`; `i:num`]
                  BEL_TT_PARTIAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `bel_en m (bel_tt (partial_derivative i mu) (g:complex->complex)) +
                bel_en m (bel_tt mu (partial_derivative i g))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC BEL_EN_ADD THEN EXISTS_TAC `rho:real` THEN
      ASM_SIMP_TAC[BEL_TT_SUPP; ETA_AX] THEN CONJ_TAC THEN MATCH_MP_TAC BEL_TT_SMOOTH THEN
      EXISTS_TAC `R:real` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THENL
       [MAP_EVERY EXISTS_TAC [`rho:real`; `R:real`] THEN ASM_REWRITE_TAC[];
        MAP_EVERY EXISTS_TAC [`rho:real`; `R:real`] THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[bel_en; bel_fn] THEN
  FIRST_ASSUM(MP_TAC o SPEC `1`) THEN FIRST_ASSUM(MP_TAC o SPEC `2`) THEN
  REWRITE_TAC[ARITH] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `bel_en m (bel_tt mu (g:complex->complex)) <= k * bel_en m g + K0 * bel_fn m g`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`rho:real`; `R:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:num`; `R:real`; `g:complex->complex`] BEL_FN_PD_LE) THEN
  MP_TAC(ISPECL [`m:num`; `R:real`; `g:complex->complex`] BEL_FN_LE_EN) THEN
  MP_TAC(ISPECL [`m:num`; `R:real`; `g:complex->complex`] BEL_EN_POS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `K0 * bel_fn m (g:complex->complex) <= K0 * bel_en m g /\
                K0 * bel_fn m (partial_derivative 1 g) <= K0 * bel_en m g /\
                K0 * bel_fn m (partial_derivative 2 g) <= K0 * bel_en m g /\
                M * bel_en m g <= abs M * bel_en m g`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The Neumann iterates u_0 = e, u_(n+1) = T u_n (T g = mu S g) and their    *)
(* bounds.                                                                    *)

let bel_ue = define
 `(bel_ue (mu:complex->complex) (e:complex->complex) 0 = e) /\
  (bel_ue mu e (SUC n) = bel_tt mu (bel_ue mu e n))`;;

let BEL_UE_SMOOTH = prove
 (`!rho mu e:complex->complex n.
        smooth_map_on (:complex) mu /\ bel_supp rho mu /\
        smooth_map_on (:complex) e /\ bel_supp rho e
        ==> smooth_map_on (:complex) (bel_ue mu e n) /\ bel_supp rho (bel_ue mu e n)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[bel_ue] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[BEL_TT_SUPP] THEN
  MATCH_MP_TAC BEL_TT_SMOOTH THEN EXISTS_TAC `rho:real` THEN ASM_SIMP_TAC[]);;

let BEL_SUM_SHIFT = prove
 (`!a:num->real n. sum(0..SUC n) a = a 0 + sum(0..n) (\i. a(SUC i))`,
  GEN_TAC THEN INDUCT_TAC THEN ONCE_REWRITE_TAC[SUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[LE_0] THENL
   [REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let BEL_REC_SUM = prove
 (`!a c k B. (!n. &0 <= a n) /\ &0 <= k /\ k < &1 /\
             (!n. a(SUC n) <= k * a n + c n) /\ (!n. sum(0..n) c <= B)
             ==> !n. sum(0..n) a <= (a 0 + B) / (&1 - k)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_SUB_LT] THEN
  SUBGOAL_THEN `sum(0..SUC n) a <= a 0 + k * sum(0..n) a + B` MP_TAC THENL
   [REWRITE_TAC[BEL_SUM_SHIFT] THEN
    MATCH_MP_TAC(REAL_ARITH `!x y. x <= k * s + y /\ y <= B ==> a0 + x <= a0 + k * s + B`) THEN
    EXISTS_TAC `sum(0..n) (c:num->real)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_ADD_NUMSEG] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sum(0..n) a <= sum(0..SUC n) a` MP_TAC THENL
   [REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN ASM_SIMP_TAC[REAL_LE_ADDR];
    REAL_ARITH_TAC]);;

(* Weighted version (geometric decay, uniform in the data).                  *)

let BEL_REC_SUM_W = prove
 (`!a c k r B. (!n. &0 <= a n) /\ &0 <= k /\ &1 <= r /\ r * k < &1 /\
               (!n. a(SUC n) <= k * a n + c n) /\
               (!n. sum(0..n) (\i. r pow i * c i) <= B)
               ==> !n. sum(0..n) (\i. r pow i * a i) <= (a 0 + r * B) / (&1 - r * k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\i. r pow i * (a:num->real) i`; `\i. r * r pow i * (c:num->real) i`;
                 `r * k`; `r * B`] BEL_REC_SUM) THEN
  REWRITE_TAC[real_pow; REAL_MUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[];
    X_GEN_TAC `n:num` THEN
    SUBGOAL_THEN `&0 <= r * r pow n` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(r * r pow n) * (k * (a:num->real) n + c n)` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC];
    GEN_TAC THEN REWRITE_TAC[SUM_LMUL; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let BEL_UE_EN_SUM_W = prove
 (`!m M k r rho.
     &1 <= r /\ r * k < &1
     ==> ?B. !mu e:complex->complex.
               smooth_map_on (:complex) mu /\ bel_supp rho mu /\ (!z. norm(mu z) <= k) /\
               (!l z. LENGTH l <= m /\ ALL (\i. i = 1 \/ i = 2) l
                      ==> norm(iterated_partial l mu z) <= M) /\
               smooth_map_on (:complex) e /\ bel_supp rho e /\
               (!l z. LENGTH l <= m /\ ALL (\i. i = 1 \/ i = 2) l
                      ==> norm(iterated_partial l e z) <= M)
               ==> !N. sum(0..N) (\n. r pow n * bel_en m (bel_ue mu e n)) <= B`,
  INDUCT_TAC THEN REPEAT STRIP_TAC THENL
   [EXISTS_TAC `(M * sqrt(measure(cball(Cx(&0),rho))) + r * &0) / (&1 - r * k)` THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= k` ASSUME_TAC THENL
     [ASM_MESON_TAC[NORM_POS_LE; REAL_LE_TRANS]; ALL_TAC] THEN
    MP_TAC(ISPECL [`\n. bel_en 0 (bel_ue (mu:complex->complex) e n)`; `\n:num. &0`;
                   `k:real`; `r:real`; `&0`] BEL_REC_SUM_W) THEN
    REWRITE_TAC[REAL_MUL_RZERO; SUM_0; REAL_LE_REFL; REAL_ADD_RID] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `n:num` THENL
       [MATCH_MP_TAC BEL_EN_POS THEN EXISTS_TAC `rho:real` THEN
        ASM_MESON_TAC[BEL_UE_SMOOTH];
        REWRITE_TAC[bel_en; bel_ue] THEN MATCH_MP_TAC BEL_TT_L2 THEN
        MAP_EVERY EXISTS_TAC [`rho:real`; `rho:real`] THEN
        ASM_MESON_TAC[BEL_UE_SMOOTH]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `N:num`) THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_SUB_LT; REAL_MUL_RZERO; REAL_ADD_RID] THEN
    REWRITE_TAC[bel_en; bel_ue] THEN MATCH_MP_TAC BEL_N2_BOUND THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS] THEN X_GEN_TAC `z:complex` THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`[]:num list`; `z:complex`]) THEN
    REWRITE_TAC[LENGTH; ALL; iterated_partial; LE_REFL];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`M:real`; `k:real`; `r:real`; `rho:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `B0:real`) THEN
  MP_TAC(SPECL [`SUC m`; `M:real`] BEL_EN_TT) THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(&3 pow (SUC m) * M * sqrt(measure(cball(Cx(&0),rho))) + r * (K * B0)) /
              (&1 - r * k)` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= k` ASSUME_TAC THENL
   [ASM_MESON_TAC[NORM_POS_LE; REAL_LE_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `!l z. LENGTH l <= m /\ ALL (\i. i = 1 \/ i = 2) l
                      ==> norm(iterated_partial l (mu:complex->complex) z) <= M /\
                          norm(iterated_partial l (e:complex->complex) z) <= M`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\n. bel_en (SUC m) (bel_ue (mu:complex->complex) e n)`;
                 `\n. K * bel_en m (bel_ue (mu:complex->complex) e n)`;
                 `k:real`; `r:real`; `K * B0`] BEL_REC_SUM_W) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN X_GEN_TAC `n:num` THENL
     [MATCH_MP_TAC BEL_EN_POS THEN EXISTS_TAC `rho:real` THEN
      ASM_MESON_TAC[BEL_UE_SMOOTH];
      REWRITE_TAC[bel_ue] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`mu:complex->complex`; `bel_ue (mu:complex->complex) e n`;
                                    `rho:real`; `rho:real`; `k:real`]) THEN
      REWRITE_TAC[bel_fn] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_MESON_TAC[BEL_UE_SMOOTH];
      REWRITE_TAC[REAL_ARITH `r * K * x = K * r * x`; SUM_LMUL] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `N:num`) THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_SUB_LT; REAL_LE_RADD] THEN
  REWRITE_TAC[bel_ue] THEN MATCH_MP_TAC BEL_EN_BOUND THEN ASM_REWRITE_TAC[]);;

let BEL_UE_EN_SUM = prove
 (`!m M k rho.
     k < &1
     ==> ?B. !mu e:complex->complex.
               smooth_map_on (:complex) mu /\ bel_supp rho mu /\ (!z. norm(mu z) <= k) /\
               (!l z. LENGTH l <= m /\ ALL (\i. i = 1 \/ i = 2) l
                      ==> norm(iterated_partial l mu z) <= M) /\
               smooth_map_on (:complex) e /\ bel_supp rho e /\
               (!l z. LENGTH l <= m /\ ALL (\i. i = 1 \/ i = 2) l
                      ==> norm(iterated_partial l e z) <= M)
               ==> !N. sum(0..N) (\n. bel_en m (bel_ue mu e n)) <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`m:num`; `M:real`; `k:real`; `&1`; `rho:real`] BEL_UE_EN_SUM_W) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; REAL_MUL_LID; REAL_POW_ONE]);;

(* ========================================================================= *)
(* A sup bound by the L^2 norm of the second dbar derivative.               *)
(* Pompeiu applied to w and to V(x) = cnj(x - z) w_zbar(x) (which vanishes *)
(* at z) gives w(z) = (1/pi) int cnj(x - z)/(x - z) w_zbarzbar(x) dx, with  *)
(* a bounded kernel; then Cauchy-Schwarz on the disc.                       *)
(* ========================================================================= *)

let BEL_L1_L2 = prove
 (`!R f:complex->complex.
        f continuous_on (:complex) /\ bel_supp R f
        ==> drop(integral (:complex) (\z. lift(norm(f z)))) <=
            sqrt(measure(cball(Cx(&0),R))) * bel_n2 f`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `integral (:complex) (\z. lift(norm((f:complex->complex) z))) =
                integral (cball(Cx(&0),R)) (\z. lift(norm(f z) * norm(Cx(&1))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM; REAL_MUL_RID] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM INTEGRAL_RESTRICT_UNIV] THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:complex` THEN
    REWRITE_TAC[IN_CBALL; dist; COMPLEX_SUB_LZERO; NORM_NEG] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `bel_supp R (f:complex->complex)` THEN REWRITE_TAC[bel_supp] THEN
    DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[COMPLEX_NORM_0; LIFT_NUM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:complex->complex) IN lspace (cball(Cx(&0),R)) (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `(:complex)` THEN
    REWRITE_TAC[LEBESGUE_MEASURABLE_CBALL; SUBSET_UNIV] THEN
    MATCH_MP_TAC BEL_LSPACE2 THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`cball(Cx(&0),R)`; `&2`; `&2`; `f:complex->complex`;
                 `\x:complex. Cx(&1)`] HOELDER_INEQUALITY) THEN
  ASM_SIMP_TAC[LSPACE_CONST; MEASURABLE_CBALL] THEN
  ANTS_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> x <= a ==> x <= b`) THEN
  SIMP_TAC[LNORM_CONST; MEASURABLE_CBALL; REAL_ARITH `&0 < &2`] THEN
  REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM; REAL_MUL_RID] THEN
  REWRITE_TAC[REAL_ARITH `inv(&2) = &1 / &2`] THEN
  SIMP_TAC[RPOW_SQRT; MEASURE_POS_LE; MEASURABLE_CBALL] THEN
  SUBGOAL_THEN `lnorm (cball(Cx(&0),R)) (&2) (f:complex->complex) = bel_n2 f`
  SUBST1_TAC THENL
   [REWRITE_TAC[bel_n2; lnorm] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[RPOW_POW] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC BEL_INTEGRAL_SQ_RESTRICT THEN
    ASM_REWRITE_TAC[];
    REAL_ARITH_TAC]);;

let BEL_CNJ_SHIFT_SMOOTH = prove
 (`!z:complex. smooth_map_on (:complex) (\w. cnj(w - z))`,
  GEN_TAC THEN MATCH_MP_TAC BEL_SMOOTH_CNJ THEN
  MATCH_MP_TAC BEL_SMOOTH_SUB THEN REWRITE_TAC[SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST]);;

let BEL_CNJ_SHIFT_DBAR = prove
 (`!z w:complex. wirtinger_dbar (\x. cnj(x - z)) w = Cx(&1)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `frechet_derivative (\x:complex. cnj(x - z)) (at w) = cnj`
  ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    SUBGOAL_THEN `(\x:complex. cnj(x - z)) = (\x. cnj x - cnj z)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; CNJ_SUB]; ALL_TAC] THEN
    SUBGOAL_THEN `cnj = (\h:complex. cnj h - vec 0)` (fun th ->
      GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [th]) THENL
     [REWRITE_TAC[FUN_EQ_THM; VECTOR_SUB_RZERO]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
    REWRITE_TAC[HAS_DERIVATIVE_CONST; ETA_AX; HAS_DERIVATIVE_CNJ];
    ASM_REWRITE_TAC[WIRTINGER_DBAR_FRECHET; CNJ_CX; CNJ_II] THEN
    CONV_TAC COMPLEX_FIELD]);;

let BEL_BOUNDED_KERNEL = prove
 (`!R w:complex->complex z.
        smooth_map_on (:complex) w /\ bel_supp R w
        ==> w z = Cx(inv pi) *
                  integral (:complex)
                    (\x. (cnj(x - z) * wirtinger_dbar (wirtinger_dbar w) x) / (x - z))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `q = wirtinger_dbar (w:complex->complex)` THEN
  SUBGOAL_THEN `smooth_map_on (:complex) (q:complex->complex) /\ bel_supp R q`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN ASM_SIMP_TAC[BEL_SMOOTH_WIRTINGER] THEN
    MP_TAC(ISPECL [`R:real`; `w:complex->complex`] BEL_SUPP_WIRTINGER) THEN
    ASM_SIMP_TAC[BEL_SMOOTH_C1];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:complex) (wirtinger_dbar (q:complex->complex)) /\
                bel_supp R (wirtinger_dbar q)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[BEL_SMOOTH_WIRTINGER] THEN
    MP_TAC(ISPECL [`R:real`; `q:complex->complex`] BEL_SUPP_WIRTINGER) THEN
    ASM_SIMP_TAC[BEL_SMOOTH_C1];
    ALL_TAC] THEN
  ABBREV_TAC `V = \x:complex. cnj(x - z) * (q:complex->complex) x` THEN
  SUBGOAL_THEN `smooth_map_on (:complex) (V:complex->complex) /\ bel_supp R V`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN CONJ_TAC THENL
     [MATCH_MP_TAC BEL_SMOOTH_MUL THEN ASM_REWRITE_TAC[ETA_AX; BEL_CNJ_SHIFT_SMOOTH];
      MATCH_MP_TAC BEL_SUPP_MUL THEN ASM_REWRITE_TAC[ETA_AX]];
    ALL_TAC] THEN
  SUBGOAL_THEN `wirtinger_dbar (V:complex->complex) =
                (\x. q x + cnj(x - z) * wirtinger_dbar q x)` ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:complex` THEN EXPAND_TAC "V" THEN
    MP_TAC(ISPECL [`\x:complex. cnj(x - z)`; `q:complex->complex`; `x:complex`]
                  BEL_WIRTINGER_MUL) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC BEL_SMOOTH_DIFFERENTIABLE THEN
      ASM_REWRITE_TAC[BEL_CNJ_SHIFT_SMOOTH];
      DISCH_THEN(fun th -> REWRITE_TAC[BETA_RULE(CONJUNCT2 th)])] THEN
    REWRITE_TAC[BEL_CNJ_SHIFT_DBAR; COMPLEX_MUL_LID] THEN REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`R:real`; `V:complex->complex`; `z:complex`] BEL_CT_POMPEIU) THEN
  ASM_SIMP_TAC[BEL_SMOOTH_C1] THEN
  SUBGOAL_THEN `(V:complex->complex) z = Cx(&0)` SUBST1_TAC THENL
   [EXPAND_TAC "V" THEN REWRITE_TAC[COMPLEX_SUB_REFL; CNJ_CX; COMPLEX_MUL_LZERO];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`R:real`; `\x:complex. (q:complex->complex) x`;
                 `\x:complex. cnj(x - z) * wirtinger_dbar (q:complex->complex) x`;
                 `z:complex`] BEL_CT_ADD) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN MATCH_MP_TAC BEL_SMOOTH_MUL THEN
      ASM_REWRITE_TAC[ETA_AX; BEL_CNJ_SHIFT_SMOOTH];
      MATCH_MP_TAC BEL_SUPP_MUL THEN ASM_REWRITE_TAC[ETA_AX]];
    REWRITE_TAC[ETA_AX] THEN DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`R:real`; `w:complex->complex`; `z:complex`] BEL_CT_POMPEIU) THEN
  ASM_SIMP_TAC[BEL_SMOOTH_C1] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[bel_ct] THEN DISCH_TAC THEN
  MATCH_MP_TAC(COMPLEX_RING `!a b c. a + --c * b = Cx(&0) ==> a = c * b`) THEN
  FIRST_ASSUM ACCEPT_TAC);;

let BEL_SUP_BOUND = prove
 (`!R w:complex->complex z.
        smooth_map_on (:complex) w /\ bel_supp R w
        ==> norm(w z) <= inv pi * sqrt(measure(cball(Cx(&0),R))) *
                         bel_n2 (wirtinger_dbar (wirtinger_dbar w))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `p = wirtinger_dbar (wirtinger_dbar (w:complex->complex))` THEN
  SUBGOAL_THEN `smooth_map_on (:complex) (p:complex->complex) /\ bel_supp R p`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN
    SUBGOAL_THEN `smooth_map_on (:complex) (wirtinger_dbar (w:complex->complex)) /\
                  bel_supp R (wirtinger_dbar w)` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[BEL_SMOOTH_WIRTINGER] THEN
      MP_TAC(ISPECL [`R:real`; `w:complex->complex`] BEL_SUPP_WIRTINGER) THEN
      ASM_SIMP_TAC[BEL_SMOOTH_C1];
      ASM_SIMP_TAC[BEL_SMOOTH_WIRTINGER] THEN
      MP_TAC(ISPECL [`R:real`; `wirtinger_dbar (w:complex->complex)`] BEL_SUPP_WIRTINGER) THEN
      ASM_SIMP_TAC[BEL_SMOOTH_C1]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`R:real`; `w:complex->complex`; `z:complex`] BEL_BOUNDED_KERNEL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_ABS_INV; REAL_ABS_PI] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_INV_EQ; PI_POS_LE] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (:complex) (\x. lift(norm((p:complex->complex) x))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MP_TAC(ISPECL [`R:real`; `\x:complex. cnj(x - z) * (p:complex->complex) x`; `z:complex`]
                    BEL_CT_INTEGRABLE) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN MATCH_MP_TAC BEL_SMOOTH_MUL THEN
        ASM_REWRITE_TAC[ETA_AX; BEL_CNJ_SHIFT_SMOOTH];
        MATCH_MP_TAC BEL_SUPP_MUL THEN ASM_REWRITE_TAC[ETA_AX]];
      MATCH_MP_TAC BEL_INTEGRABLE_CBALL_SUPPORT THEN EXISTS_TAC `R:real` THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
        ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS];
        UNDISCH_TAC `bel_supp R (p:complex->complex)` THEN REWRITE_TAC[bel_supp] THEN
        SIMP_TAC[COMPLEX_NORM_0; LIFT_NUM]];
      X_GEN_TAC `x:complex` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
      REWRITE_TAC[complex_div; COMPLEX_NORM_MUL; COMPLEX_NORM_CNJ; COMPLEX_NORM_INV] THEN
      ASM_CASES_TAC `x:complex = z` THENL
       [ASM_REWRITE_TAC[COMPLEX_SUB_REFL; COMPLEX_NORM_0; REAL_MUL_LZERO; NORM_POS_LE];
        ALL_TAC] THEN
      SUBGOAL_THEN `~(norm(x - z:complex) = &0)` MP_TAC THENL
       [ASM_REWRITE_TAC[NORM_EQ_0; VECTOR_SUB_EQ]; ALL_TAC] THEN
      SPEC_TAC(`norm(x - z:complex)`,`t:real`) THEN
      SPEC_TAC(`norm((p:complex->complex) x)`,`s:real`) THEN
      REPEAT GEN_TAC THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `~(t = &0)` THEN
      CONV_TAC REAL_FIELD];
    MATCH_MP_TAC BEL_L1_L2 THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS]]);;

let BEL_SUP_EN = prove
 (`!R w:complex->complex z.
        smooth_map_on (:complex) w /\ bel_supp R w
        ==> norm(w z) <= inv pi * sqrt(measure(cball(Cx(&0),R))) * bel_en 2 w`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv pi * sqrt(measure(cball(Cx(&0),R))) *
              bel_n2 (wirtinger_dbar (wirtinger_dbar (w:complex->complex)))` THEN
  CONJ_TAC THENL [MATCH_MP_TAC BEL_SUP_BOUND THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  SIMP_TAC[REAL_LE_MUL; REAL_LE_INV_EQ; PI_POS_LE; SQRT_POS_LE; MEASURE_POS_LE;
           MEASURABLE_CBALL] THEN
  SUBGOAL_THEN `smooth_map_on (:complex) (wirtinger_dbar (w:complex->complex)) /\
                bel_supp R (wirtinger_dbar w)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[BEL_SMOOTH_WIRTINGER] THEN
    MP_TAC(ISPECL [`R:real`; `w:complex->complex`] BEL_SUPP_WIRTINGER) THEN
    ASM_SIMP_TAC[BEL_SMOOTH_C1];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `bel_en 1 (wirtinger_dbar (w:complex->complex))` THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`0`; `R:real`; `wirtinger_dbar (w:complex->complex)`] BEL_EN_WIRT) THEN
    ASM_REWRITE_TAC[bel_en; ONE] THEN SIMP_TAC[];
    MP_TAC(ISPECL [`1`; `R:real`; `w:complex->complex`] BEL_EN_WIRT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `SUC 1 = 2`] THEN SIMP_TAC[]]);;

(* ========================================================================= *)
(* Series of smooth functions with summable sup bounds of all               *)
(* derivatives (Weierstrass M-test): the sum is continuous, differentiable  *)
(* termwise, smooth, and its iterated partials are the termwise series.     *)
(* ========================================================================= *)

let BEL_POS_SUMMABLE = prove
 (`!a:num->real B. (!n. &0 <= a n) /\ (!N. sum(0..N) a <= B)
                   ==> ?l. ((lift o a) sums l) (from 0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sums; FROM_INTER_NUMSEG] THEN
  MATCH_MP_TAC BOUNDED_INCREASING_CONVERGENT THEN CONJ_TAC THENL
   [REWRITE_TAC[bounded; FORALL_IN_GSPEC; IN_UNIV] THEN
    EXISTS_TAC `abs B + abs(a 0)` THEN X_GEN_TAC `n:num` THEN
    REWRITE_TAC[GSYM LIFT_SUM; NORM_LIFT] THEN
    MP_TAC(SPEC `n:num` (ASSUME `!N. sum(0..N) a <= B`)) THEN
    SUBGOAL_THEN `&0 <= sum(0..n) a` MP_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    X_GEN_TAC `n:num` THEN REWRITE_TAC[GSYM LIFT_SUM; LIFT_DROP] THEN
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN ASM_SIMP_TAC[REAL_LE_ADDR]]);;

let BEL_MTEST = prove
 (`!uu:num->real^M->real^N a B.
        (!n. &0 <= a n) /\ (!N. sum(0..N) a <= B) /\ (!n z. norm(uu n z) <= a n)
        ==> (!z. ((\n. uu n z) sums infsum (from 0) (\n. uu n z)) (from 0)) /\
            (!e. &0 < e
                 ==> ?N. !n z. N <= n
                               ==> norm(vsum(0..n) (\i. uu i z) -
                                        infsum (from 0) (\i. uu i z)) < e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:num->real`; `B:real`] BEL_POS_SUMMABLE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`\z:real^M n:num. (uu:num->real^M->real^N) n z`; `a:num->real`;
                 `\z:real^M. T`; `from 0`] SERIES_COMPARISON_UNIFORM) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FROM_INTER_NUMSEG] THEN
  DISCH_THEN(X_CHOOSE_TAC `G:real^M->real^N`) THEN
  SUBGOAL_THEN `!z. ((\n. (uu:num->real^M->real^N) n z) sums G z) (from 0)` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[sums; LIM_SEQUENTIALLY; FROM_INTER_NUMSEG] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. infsum (from 0) (\n. (uu:num->real^M->real^N) n z) = G z` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC INFSUM_UNIQUE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[NORM_SUB] THEN REWRITE_TAC[GSYM dist] THEN
  ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_SIMP_TAC[]);;

let BEL_SERIES_CONT = prove
 (`!uu:num->real^M->real^N a B s.
        (!n. &0 <= a n) /\ (!N. sum(0..N) a <= B) /\ (!n z. norm(uu n z) <= a n) /\
        (!n. (uu n) continuous_on s)
        ==> (\z. infsum (from 0) (\n. uu n z)) continuous_on s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`uu:num->real^M->real^N`; `a:num->real`; `B:real`] BEL_MTEST) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` CONTINUOUS_UNIFORM_LIMIT) THEN
  EXISTS_TAC `\n z. vsum(0..n) (\i. (uu:num->real^M->real^N) i z)` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
  CONJ_TAC THENL
   [EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; ETA_AX];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[]]);;

let BEL_SERIES_HAS_DERIVATIVE = prove
 (`!uu:num->complex->complex a0 a1 a2 B0 B1 B2.
     (!n. smooth_map_on (:complex) (uu n)) /\
     (!n. &0 <= a0 n) /\ (!N. sum(0..N) a0 <= B0) /\ (!n z. norm(uu n z) <= a0 n) /\
     (!n. &0 <= a1 n) /\ (!N. sum(0..N) a1 <= B1) /\
     (!n z. norm(partial_derivative 1 (uu n) z) <= a1 n) /\
     (!n. &0 <= a2 n) /\ (!N. sum(0..N) a2 <= B2) /\
     (!n z. norm(partial_derivative 2 (uu n) z) <= a2 n)
     ==> !z. ((\w. infsum (from 0) (\n. uu n w)) has_derivative
              (\h. Cx(Re h) * infsum (from 0) (\n. partial_derivative 1 (uu n) z) +
                   Cx(Im h) * infsum (from 0) (\n. partial_derivative 2 (uu n) z))) (at z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`uu:num->complex->complex`; `a0:num->real`; `B0:real`] BEL_MTEST) THEN
  MP_TAC(ISPECL [`\n. partial_derivative 1 ((uu:num->complex->complex) n)`;
                 `a1:num->real`; `B1:real`] BEL_MTEST) THEN
  MP_TAC(ISPECL [`\n. partial_derivative 2 ((uu:num->complex->complex) n)`;
                 `a2:num->real`; `B2:real`] BEL_MTEST) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT2) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT2) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`(:complex)`; `uu:num->complex->complex`;
                 `\n x. frechet_derivative ((uu:num->complex->complex) n) (at x)`;
                 `\z h. Cx(Re h) * infsum (from 0) (\n. partial_derivative 1
                                                     ((uu:num->complex->complex) n) z) +
                        Cx(Im h) * infsum (from 0) (\n. partial_derivative 2 (uu n) z)`;
                 `from 0`] HAS_DERIVATIVE_SERIES) THEN
  REWRITE_TAC[CONVEX_UNIV; IN_UNIV; WITHIN_UNIV; FROM_INTER_NUMSEG] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REPEAT GEN_TAC THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      ASM_SIMP_TAC[BEL_SMOOTH_DIFFERENTIABLE];
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN
      ASM_REWRITE_TAC[REAL_HALF] THEN
      DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
      EXISTS_TAC `N1 + N2:num` THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `x:complex`; `h:complex`] THEN
      REWRITE_TAC[GE] THEN DISCH_TAC THEN
      SUBGOAL_THEN `!i. frechet_derivative ((uu:num->complex->complex) i) (at x) h =
                        Cx(Re h) * partial_derivative 1 (uu i) x +
                        Cx(Im h) * partial_derivative 2 (uu i) x`
      (fun th -> REWRITE_TAC[th]) THENL
       [GEN_TAC THEN REWRITE_TAC[BEL_PARTIAL_COMPLEX] THEN
        MATCH_MP_TAC BEL_LINEAR_EXPAND THEN REWRITE_TAC[ETA_AX] THEN
        MATCH_MP_TAC BEL_C1_LINEAR THEN
        ASM_SIMP_TAC[BEL_SMOOTH_C1];
        ALL_TAC] THEN
      REWRITE_TAC[VSUM_ADD_NUMSEG] THEN
      SIMP_TAC[VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
      REWRITE_TAC[COMPLEX_RING
       `(a * p + b * q) - (a * p' + b * q') = a * (p - p') + b * (q - q'):complex`] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `abs(Re h) * e / &2 + abs(Im h) * e / &2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC(NORM_ARITH `norm(a:complex) <= x /\ norm(b:complex) <= y
                                 ==> norm(a + b) <= x + y`) THEN
        REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN CONJ_TAC THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
        MP_TAC(SPEC `h:complex` COMPLEX_NORM_GE_RE_IM) THEN
        MP_TAC(SPECL [`abs(Re h)`; `norm(h:complex)`; `e / &2`] REAL_LE_RMUL) THEN
        MP_TAC(SPECL [`abs(Im h)`; `norm(h:complex)`; `e / &2`] REAL_LE_RMUL) THEN
        ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `G:complex->complex`) THEN X_GEN_TAC `z:complex` THEN
  SUBGOAL_THEN `(\w. infsum (from 0) (\n. (uu:num->complex->complex) n w)) = G`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `w:complex` THEN
    MATCH_MP_TAC INFSUM_UNIQUE THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

let bel_sumbd = new_definition
 `bel_sumbd (uu:num->complex->complex) <=>
    (!n. smooth_map_on (:complex) (uu n)) /\
    !l. ALL (\i. i = 1 \/ i = 2) l
        ==> ?a B. (!n. &0 <= a n) /\ (!N. sum(0..N) a <= B) /\
                  (!n z. norm(iterated_partial l (uu n) z) <= a n)`;;

let BEL_SUMBD_ITERATED = prove
 (`!uu l. bel_sumbd uu /\ ALL (\i. i = 1 \/ i = 2) l
          ==> bel_sumbd (\n. iterated_partial l (uu n))`,
  REWRITE_TAC[bel_sumbd] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_ITERATED_PARTIAL THEN ASM_REWRITE_TAC[OPEN_UNIV];
    REWRITE_TAC[GSYM ITERATED_PARTIAL_APPEND] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[ALL_APPEND]]);;

let BEL_SUMBD_PD = prove
 (`!uu i. bel_sumbd uu /\ (i = 1 \/ i = 2)
          ==> bel_sumbd (\n. partial_derivative i (uu n))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`uu:num->complex->complex`; `[i:num]`] BEL_SUMBD_ITERATED) THEN
  ASM_REWRITE_TAC[ALL; iterated_partial]);;

let BEL_ITERATED_LINCOMB = prove
 (`!l a b f g:complex->complex.
        smooth_map_on (:complex) f /\ smooth_map_on (:complex) g
        ==> iterated_partial l (\z. a * f z + b * g z) =
            (\z. a * iterated_partial l f z + b * iterated_partial l g z)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[iterated_partial; ETA_AX] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `z:complex` THEN MATCH_MP_TAC BEL_PD_LINCOMB THEN
  CONJ_TAC THEN MATCH_MP_TAC BEL_SMOOTH_DIFFERENTIABLE THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ITERATED_PARTIAL THEN ASM_REWRITE_TAC[OPEN_UNIV]);;

let BEL_SUMBD_LINCOMB = prove
 (`!u1 u2 c1 c2. bel_sumbd u1 /\ bel_sumbd u2
                 ==> bel_sumbd (\n z. c1 * u1 n z + c2 * u2 n z)`,
  REWRITE_TAC[bel_sumbd] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC BEL_SMOOTH_ADD THEN CONJ_TAC THEN MATCH_MP_TAC BEL_SMOOTH_LMUL THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `l:num list`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `l:num list`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a1:num->real`; `B1:real`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`a2:num->real`; `B2:real`] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`\n:num. norm(c1:complex) * (a1:num->real) n +
                             norm(c2:complex) * (a2:num->real) n`;
                        `norm(c1:complex) * B1 + norm(c2:complex) * B2`] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
    GEN_TAC THEN REWRITE_TAC[SUM_ADD_NUMSEG; SUM_LMUL] THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[NORM_POS_LE];
    MAP_EVERY X_GEN_TAC [`n:num`; `z:complex`] THEN
    MP_TAC(ISPECL [`l:num list`; `c1:complex`; `c2:complex`;
                   `(u1:num->complex->complex) n`; `(u2:num->complex->complex) n`]
                  BEL_ITERATED_LINCOMB) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(NORM_ARITH `norm(a:complex) <= x /\ norm(b:complex) <= y
                             ==> norm(a + b) <= x + y`) THEN
    REWRITE_TAC[COMPLEX_NORM_MUL] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[NORM_POS_LE]]);;

let BEL_SUMBD_BOUNDS = prove
 (`!uu. bel_sumbd uu
        ==> !l. ALL (\i. i = 1 \/ i = 2) l
                ==> ?a B. (!n. &0 <= a n) /\ (!N. sum(0..N) a <= B) /\
                          (!n z. norm(iterated_partial l (uu n) z) <= a n)`,
  SIMP_TAC[bel_sumbd]);;

let BEL_SERIES_HAS_DERIVATIVE_SUMBD = prove
 (`!uu:num->complex->complex z.
        bel_sumbd uu
        ==> ((\w. infsum (from 0) (\n. uu n w)) has_derivative
             (\h. Cx(Re h) * infsum (from 0) (\n. partial_derivative 1 (uu n) z) +
                  Cx(Im h) * infsum (from 0) (\n. partial_derivative 2 (uu n) z))) (at z)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `[]:num list` o MATCH_MP BEL_SUMBD_BOUNDS) THEN
  FIRST_ASSUM(MP_TAC o SPEC `[1]` o MATCH_MP BEL_SUMBD_BOUNDS) THEN
  FIRST_ASSUM(MP_TAC o SPEC `[2]` o MATCH_MP BEL_SUMBD_BOUNDS) THEN
  REWRITE_TAC[ALL; iterated_partial; ARITH; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a2:num->real`; `B2:real`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`a1:num->real`; `B1:real`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`a0:num->real`; `B0:real`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`uu:num->complex->complex`; `a0:num->real`; `a1:num->real`;
                 `a2:num->real`; `B0:real`; `B1:real`; `B2:real`]
                BEL_SERIES_HAS_DERIVATIVE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[bel_sumbd]; SIMP_TAC[]]);;

let BEL_SERIES_PD = prove
 (`!uu:num->complex->complex i z.
        bel_sumbd uu /\ (i = 1 \/ i = 2)
        ==> partial_derivative i (\w. infsum (from 0) (\n. uu n w)) z =
            infsum (from 0) (\n. partial_derivative i (uu n) z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `z:complex` o MATCH_MP BEL_SERIES_HAS_DERIVATIVE_SUMBD) THEN
  DISCH_THEN(ASSUME_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  GEN_REWRITE_TAC LAND_CONV [partial_derivative] THEN
  ASM_REWRITE_TAC[COMPLEX_BASIS; RE_CX; IM_CX; RE_II; IM_II] THEN
  REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_MUL_LID; COMPLEX_ADD_RID; COMPLEX_ADD_LID]);;

let BEL_SUMBD_SUMMABLE = prove
 (`!uu:num->complex->complex z. bel_sumbd uu ==> summable (from 0) (\n. uu n z)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `[]:num list` o MATCH_MP BEL_SUMBD_BOUNDS) THEN
  REWRITE_TAC[ALL; iterated_partial; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:num->real`; `B:real`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`uu:num->complex->complex`; `a:num->real`; `B:real`] BEL_MTEST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `z:complex` o CONJUNCT1) THEN
  REWRITE_TAC[SUMS_INFSUM]);;

let BEL_SERIES_CD = prove
 (`!k uu:num->complex->complex.
        bel_sumbd uu
        ==> continuously_differentiable k (:complex) (\w. infsum (from 0) (\n. uu n w))`,
  INDUCT_TAC THENL
   [REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0] THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `[]:num list` o MATCH_MP BEL_SUMBD_BOUNDS) THEN
    REWRITE_TAC[ALL; iterated_partial; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:num->real`; `B:real`] THEN STRIP_TAC THEN
    MATCH_MP_TAC BEL_SERIES_CONT THEN MAP_EVERY EXISTS_TAC [`a:num->real`; `B:real`] THEN
    ASM_REWRITE_TAC[] THEN GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN
    ASM_MESON_TAC[bel_sumbd];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_UNIV] THEN
  EXISTS_TAC
   `\z h. Cx(Re h) * infsum (from 0) (\n. partial_derivative 1
                                         ((uu:num->complex->complex) n) z) +
          Cx(Im h) * infsum (from 0) (\n. partial_derivative 2 (uu n) z)` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC BEL_SERIES_HAS_DERIVATIVE_SUMBD THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `h:complex` THEN
  SUBGOAL_THEN
   `(\z. Cx(Re h) * infsum (from 0) (\n. partial_derivative 1
                                          ((uu:num->complex->complex) n) z) +
         Cx(Im h) * infsum (from 0) (\n. partial_derivative 2 (uu n) z)) =
    (\z. infsum (from 0) (\n. Cx(Re h) * partial_derivative 1 (uu n) z +
                              Cx(Im h) * partial_derivative 2 (uu n) z))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:complex` THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC INFSUM_UNIQUE THEN
    MATCH_MP_TAC SERIES_ADD THEN CONJ_TAC THEN MATCH_MP_TAC SERIES_COMPLEX_LMUL THEN
    REWRITE_TAC[SUMS_INFSUM] THENL
     [MP_TAC(ISPECL [`\n. partial_derivative 1 ((uu:num->complex->complex) n)`;
                     `z:complex`] BEL_SUMBD_SUMMABLE);
      MP_TAC(ISPECL [`\n. partial_derivative 2 ((uu:num->complex->complex) n)`;
                     `z:complex`] BEL_SUMBD_SUMMABLE)] THEN
    ASM_SIMP_TAC[BEL_SUMBD_PD; ARITH];
    ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`\n. partial_derivative 1 ((uu:num->complex->complex) n)`;
                 `\n. partial_derivative 2 ((uu:num->complex->complex) n)`;
                 `Cx(Re h)`; `Cx(Im h)`] BEL_SUMBD_LINCOMB) THEN
  ASM_SIMP_TAC[BEL_SUMBD_PD; ARITH]);;

let BEL_SERIES_SMOOTH = prove
 (`!uu:num->complex->complex.
        bel_sumbd uu ==> smooth_map_on (:complex) (\w. infsum (from 0) (\n. uu n w))`,
  SIMP_TAC[smooth_map_on; BEL_SERIES_CD]);;

let BEL_SERIES_ITERATED = prove
 (`!l uu:num->complex->complex.
        bel_sumbd uu /\ ALL (\i. i = 1 \/ i = 2) l
        ==> iterated_partial l (\w. infsum (from 0) (\n. uu n w)) =
            (\w. infsum (from 0) (\n. iterated_partial l (uu n) w))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[iterated_partial; ALL; ETA_AX] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `w:complex` THEN
  MP_TAC(ISPECL [`\n. iterated_partial t ((uu:num->complex->complex) n)`; `h:num`;
                 `w:complex`] BEL_SERIES_PD) THEN
  ASM_SIMP_TAC[BEL_SUMBD_ITERATED]);;

(* ========================================================================= *)
(* The Neumann solution h = sum_n T^n mu of h = mu + mu S h for              *)
(* smooth compactly supported mu with |mu| <= k < 1: the iterates satisfy  *)
(* the summable sup bounds of all derivatives (E_m bounds and the sup bound  *)
(* above), so h is smooth (M-test),                                          *)
(* supported in supp mu, and solves the equation.                           *)
(* ========================================================================= *)

let BEL_LIST_SNOC = prove
 (`!l:num list. ~(l = []) ==> ?l' i. l = APPEND l' [i]`,
  MESON_TAC[APPEND_BUTLAST_LAST]);;

let BEL_DERIV_BOUND_EXISTS = prove
 (`!m R f:complex->complex.
        smooth_map_on (:complex) f /\ bel_supp R f
        ==> ?M. !l z. LENGTH l <= m /\ ALL (\i. i = 1 \/ i = 2) l
                      ==> norm(iterated_partial l f z) <= M`,
  INDUCT_TAC THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[LE; LENGTH_EQ_NIL] THEN
    MP_TAC(ISPECL [`R:real`; `f:complex->complex`] BEL_SUPP_BOUNDED_FN) THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[iterated_partial];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`R:real`; `f:complex->complex`]) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`R:real`; `partial_derivative 1 (f:complex->complex)`]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`R:real`; `partial_derivative 2 (f:complex->complex)`]) THEN
  ASM_SIMP_TAC[BEL_SMOOTH_PD_SMOOTH; BEL_SUPP_PD] THEN
  DISCH_THEN(X_CHOOSE_TAC `M2:real`) THEN DISCH_THEN(X_CHOOSE_TAC `M1:real`) THEN
  DISCH_THEN(X_CHOOSE_TAC `M0:real`) THEN
  EXISTS_TAC `max M0 (max M1 M2)` THEN
  MAP_EVERY X_GEN_TAC [`l:num list`; `z:complex`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `LENGTH(l:num list) <= m` THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= a ==> x <= max a (max b c)`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(l:num list = [])` MP_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~(LENGTH([]:num list) <= m)` THEN REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l':num list` (X_CHOOSE_THEN `i:num` SUBST_ALL_TAC) o
             MATCH_MP BEL_LIST_SNOC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND; LENGTH; ALL_APPEND; ALL]) THEN
  REWRITE_TAC[GSYM BEL_PD_ITERATED_APPEND] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC (DISJ_CASES_THEN SUBST_ALL_TAC)) THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= b ==> x <= max a (max b c)`);
    MATCH_MP_TAC(REAL_ARITH `x <= c ==> x <= max a (max b c)`)] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let BEL_UE_SUMBD = prove
 (`!rho mu e:complex->complex k.
        smooth_map_on (:complex) mu /\ bel_supp rho mu /\ (!z. norm(mu z) <= k) /\ k < &1 /\
        smooth_map_on (:complex) e /\ bel_supp rho e
        ==> bel_sumbd (bel_ue mu e)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bel_sumbd] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[BEL_UE_SMOOTH]; ALL_TAC] THEN
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`2 + LENGTH(l:num list)`; `rho:real`; `mu:complex->complex`]
                BEL_DERIV_BOUND_EXISTS) THEN
  MP_TAC(ISPECL [`2 + LENGTH(l:num list)`; `rho:real`; `e:complex->complex`]
                BEL_DERIV_BOUND_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `M2:real`) THEN
  DISCH_THEN(X_CHOOSE_TAC `M1:real`) THEN
  MP_TAC(ISPECL [`2 + LENGTH(l:num list)`; `max M1 M2`; `k:real`; `rho:real`]
                BEL_UE_EN_SUM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real`
    (MP_TAC o SPECL [`mu:complex->complex`; `e:complex->complex`])) THEN
  ASM_SIMP_TAC[REAL_LE_MAX] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= inv pi * sqrt(measure(cball(Cx(&0),rho)))` MP_TAC THENL
   [SIMP_TAC[REAL_LE_MUL; REAL_LE_INV_EQ; PI_POS_LE; SQRT_POS_LE; MEASURE_POS_LE;
             MEASURABLE_CBALL];
    ALL_TAC] THEN
  ABBREV_TAC `c = inv pi * sqrt(measure(cball(Cx(&0),rho)))` THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`\n. c * bel_en (2 + LENGTH(l:num list)) (bel_ue (mu:complex->complex) e n)`;
    `c * B`] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC BEL_EN_POS THEN EXISTS_TAC `rho:real` THEN ASM_MESON_TAC[BEL_UE_SMOOTH];
    GEN_TAC THEN REWRITE_TAC[SUM_LMUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`n:num`; `z:complex`] THEN
    MP_TAC(ISPECL [`rho:real`; `iterated_partial l (bel_ue (mu:complex->complex) e n)`;
                   `z:complex`] BEL_SUP_EN) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC BEL_SUPP_ITERATED_PARTIAL THEN ASM_MESON_TAC[BEL_UE_SMOOTH];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`l:num list`; `2`; `rho:real`; `bel_ue (mu:complex->complex) e n`]
                  BEL_EN_ITERATED) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[BEL_UE_SMOOTH]; REWRITE_TAC[]]]);;

(* The Cauchy and Beurling transforms of a series.                           *)

(* A geometric majorant, uniform in the data (used for families).             *)

let BEL_UE_GEOM_BOUND = prove
 (`!l M k r rho.
        ALL (\i. i = 1 \/ i = 2) l /\ &1 <= r /\ r * k < &1
        ==> ?B. !mu e:complex->complex.
                  smooth_map_on (:complex) mu /\ bel_supp rho mu /\ (!z. norm(mu z) <= k) /\
                  (!l' z. LENGTH l' <= 2 + LENGTH l /\ ALL (\i. i = 1 \/ i = 2) l'
                          ==> norm(iterated_partial l' mu z) <= M) /\
                  smooth_map_on (:complex) e /\ bel_supp rho e /\
                  (!l' z. LENGTH l' <= 2 + LENGTH l /\ ALL (\i. i = 1 \/ i = 2) l'
                          ==> norm(iterated_partial l' e z) <= M)
                  ==> !n z. norm(iterated_partial l (bel_ue mu e n) z) <= B / r pow n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`2 + LENGTH(l:num list)`; `M:real`; `k:real`; `r:real`; `rho:real`]
               BEL_UE_EN_SUM_W) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `B0:real`) THEN
  EXISTS_TAC `inv pi * sqrt(measure(cball(Cx(&0),rho))) * B0` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < r pow n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!i. smooth_map_on (:complex) (bel_ue (mu:complex->complex) e i) /\
                    bel_supp rho (bel_ue mu e i)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC BEL_UE_SMOOTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `r pow n * bel_en (2 + LENGTH(l:num list)) (bel_ue (mu:complex->complex) e n)
                <= B0` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`mu:complex->complex`; `e:complex->complex`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
    MATCH_MP_TAC(REAL_ARITH `!x s b. x <= s ==> s <= b ==> x <= b`) THEN
    STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
    REWRITE_TAC[SUM_SING_NUMSEG; REAL_LE_REFL] THEN
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0; REAL_LE_ADDL] THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC BEL_EN_POS THEN EXISTS_TAC `rho:real` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rho:real`; `iterated_partial l (bel_ue (mu:complex->complex) e n)`;
                 `z:complex`] BEL_SUP_EN) THEN
  ANTS_TAC THENL [MATCH_MP_TAC BEL_SUPP_ITERATED_PARTIAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_INV_EQ; PI_POS_LE] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[SQRT_POS_LE; MEASURE_POS_LE; MEASURABLE_CBALL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `bel_en (2 + LENGTH(l:num list)) (bel_ue (mu:complex->complex) e n)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC BEL_EN_ITERATED THEN EXISTS_TAC `rho:real` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[]]);;

let BEL_SUPP_VSUM = prove
 (`!R uu:num->complex->complex N.
        (!n. bel_supp R (uu n)) ==> bel_supp R (\w. vsum(0..N) (\n. uu n w))`,
  REWRITE_TAC[bel_supp] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM COMPLEX_VEC_0; VSUM_0] THEN REWRITE_TAC[COMPLEX_VEC_0] THEN
  MATCH_MP_TAC VSUM_EQ_0 THEN ASM_SIMP_TAC[COMPLEX_VEC_0]);;

let BEL_CT_VSUM = prove
 (`!R uu:num->complex->complex z N.
        (!n. (uu n) continuous_on (:complex) /\ bel_supp R (uu n))
        ==> bel_ct (\w. vsum(0..N) (\n. uu n w)) z = vsum(0..N) (\n. bel_ct (uu n) z)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[VSUM_CLAUSES_NUMSEG; LE_0; ETA_AX] THEN
  MP_TAC(ISPECL [`R:real`; `\w. vsum(0..N) (\n. (uu:num->complex->complex) n w)`;
                 `(uu:num->complex->complex) (SUC N)`; `z:complex`] BEL_CT_ADD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; ETA_AX];
      MATCH_MP_TAC BEL_SUPP_VSUM THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[]]);;

let BEL_SERIES_SUPP = prove
 (`!R uu:num->complex->complex.
        (!n. bel_supp R (uu n)) ==> bel_supp R (\w. infsum (from 0) (\n. uu n w))`,
  REWRITE_TAC[bel_supp] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC INFSUM_UNIQUE THEN
  SUBGOAL_THEN `(\n. (uu:num->complex->complex) n w) = (\n. vec 0)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN ASM_SIMP_TAC[COMPLEX_VEC_0];
    REWRITE_TAC[SERIES_0; GSYM COMPLEX_VEC_0]]);;

let BEL_CT_SERIES = prove
 (`!R uu:num->complex->complex z.
        bel_sumbd uu /\ (!n. bel_supp R (uu n))
        ==> ((\n. bel_ct (uu n) z) sums
             bel_ct (\w. infsum (from 0) (\n. uu n w)) z) (from 0)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `[]:num list` o MATCH_MP BEL_SUMBD_BOUNDS) THEN
  REWRITE_TAC[ALL; iterated_partial; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:num->real`; `B:real`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`uu:num->complex->complex`; `a:num->real`; `B:real`] BEL_MTEST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN `!n. (uu:num->complex->complex) n continuous_on (:complex)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN ASM_MESON_TAC[bel_sumbd];
    ALL_TAC] THEN
  ABBREV_TAC `H = \w. infsum (from 0) (\n. (uu:num->complex->complex) n w)` THEN
  SUBGOAL_THEN `(H:complex->complex) continuous_on (:complex) /\ bel_supp R H`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "H" THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN MATCH_MP_TAC BEL_SERIES_SMOOTH THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC BEL_SERIES_SUPP THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[sums; FROM_INTER_NUMSEG; LIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `R:real` BEL_CT_BOUND) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / (C + &1)`) THEN
  ANTS_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`R:real`; `uu:num->complex->complex`; `z:complex`; `n:num`]
                BEL_CT_VSUM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[dist] THEN
  MP_TAC(ISPECL [`R:real`; `\w. vsum(0..n) (\n. (uu:num->complex->complex) n w)`;
                 `H:complex->complex`; `z:complex`] BEL_CT_SUB) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; ETA_AX];
      MATCH_MP_TAC BEL_SUPP_VSUM THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `C * (e / (C + &1))` THEN ASM_SIMP_TAC[BEL_FRAC_LT] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; ETA_AX];
    MATCH_MP_TAC BEL_SUPP_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC BEL_SUPP_VSUM THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `w:complex` THEN REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    EXPAND_TAC "H" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let BEL_SUMBD_WIRT = prove
 (`!uu:num->complex->complex. bel_sumbd uu ==> bel_sumbd (\n. wirtinger_dz (uu n))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[BEL_WIRTINGER_PD] THEN
  MP_TAC(ISPECL [`\n. partial_derivative 1 ((uu:num->complex->complex) n)`;
                 `\n. partial_derivative 2 ((uu:num->complex->complex) n)`;
                 `inv(Cx(&2))`; `--ii * inv(Cx(&2))`] BEL_SUMBD_LINCOMB) THEN
  ASM_SIMP_TAC[BEL_SUMBD_PD; ARITH]);;

let BEL_WIRT_SERIES = prove
 (`!uu:num->complex->complex.
        bel_sumbd uu
        ==> wirtinger_dz (\w. infsum (from 0) (\n. uu n w)) =
            (\w. infsum (from 0) (\n. wirtinger_dz (uu n) w))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[BEL_WIRTINGER_PD; FUN_EQ_THM] THEN
  X_GEN_TAC `w:complex` THEN
  ASM_SIMP_TAC[BEL_SERIES_PD; ARITH] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC INFSUM_UNIQUE THEN MATCH_MP_TAC SERIES_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC SERIES_COMPLEX_LMUL THEN REWRITE_TAC[SUMS_INFSUM] THENL
   [MP_TAC(ISPECL [`\n. partial_derivative 1 ((uu:num->complex->complex) n)`;
                   `w:complex`] BEL_SUMBD_SUMMABLE);
    MP_TAC(ISPECL [`\n. partial_derivative 2 ((uu:num->complex->complex) n)`;
                   `w:complex`] BEL_SUMBD_SUMMABLE)] THEN
  ASM_SIMP_TAC[BEL_SUMBD_PD; ARITH]);;

let BEL_S_SERIES = prove
 (`!R uu:num->complex->complex z.
        bel_sumbd uu /\ (!n. bel_supp R (uu n))
        ==> ((\n. bel_s (uu n) z) sums bel_s (\w. infsum (from 0) (\n. uu n w)) z) (from 0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bel_s] THEN ASM_SIMP_TAC[BEL_WIRT_SERIES] THEN
  MP_TAC(ISPECL [`R:real`; `\n. wirtinger_dz ((uu:num->complex->complex) n)`; `z:complex`]
                BEL_CT_SERIES) THEN
  ASM_SIMP_TAC[BEL_SUMBD_WIRT] THEN DISCH_THEN MATCH_MP_TAC THEN GEN_TAC THEN
  SUBGOAL_THEN `smooth_map_on (:complex) ((uu:num->complex->complex) n)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [bel_sumbd]) THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`R:real`; `(uu:num->complex->complex) n`] BEL_SUPP_WIRTINGER) THEN
  ASM_SIMP_TAC[BEL_SMOOTH_C1]);;

(* The Neumann solution of h = e + mu S h.                                    *)

let bel_nsol = new_definition
 `bel_nsol (mu:complex->complex) (e:complex->complex) =
    \z. infsum (from 0) (\n. bel_ue mu e n z)`;;

let BEL_NSOL_SMOOTH = prove
 (`!rho mu e:complex->complex k.
        smooth_map_on (:complex) mu /\ bel_supp rho mu /\ (!z. norm(mu z) <= k) /\ k < &1 /\
        smooth_map_on (:complex) e /\ bel_supp rho e
        ==> smooth_map_on (:complex) (bel_nsol mu e)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bel_nsol] THEN MATCH_MP_TAC BEL_SERIES_SMOOTH THEN
  REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC BEL_UE_SUMBD THEN ASM_MESON_TAC[]);;

let BEL_NSOL_SUPP = prove
 (`!rho mu e:complex->complex.
        smooth_map_on (:complex) mu /\ bel_supp rho mu /\
        smooth_map_on (:complex) e /\ bel_supp rho e
        ==> bel_supp rho (bel_nsol mu e)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bel_nsol] THEN MATCH_MP_TAC BEL_SERIES_SUPP THEN
  GEN_TAC THEN
  MP_TAC(ISPECL [`rho:real`; `mu:complex->complex`; `e:complex->complex`; `n:num`]
                BEL_UE_SMOOTH) THEN
  ASM_SIMP_TAC[ETA_AX]);;

let BEL_NSOL_EQ = prove
 (`!rho mu e:complex->complex k z.
        smooth_map_on (:complex) mu /\ bel_supp rho mu /\ (!z. norm(mu z) <= k) /\ k < &1 /\
        smooth_map_on (:complex) e /\ bel_supp rho e
        ==> bel_nsol mu e z = e z + mu z * bel_s (bel_nsol mu e) z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `bel_sumbd (bel_ue (mu:complex->complex) e)` ASSUME_TAC THENL
   [MATCH_MP_TAC BEL_UE_SUMBD THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. bel_supp rho (bel_ue (mu:complex->complex) e n)` ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`rho:real`; `mu:complex->complex`; `e:complex->complex`; `n:num`]
                  BEL_UE_SMOOTH) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\n. bel_ue (mu:complex->complex) e n z) sums bel_nsol mu e z) (from 0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[bel_nsol; SUMS_INFSUM] THEN MATCH_MP_TAC BEL_SUMBD_SUMMABLE THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\n. bel_ue (mu:complex->complex) e n z`;
                 `bel_nsol (mu:complex->complex) e z`; `0`; `1`] SUMS_OFFSET) THEN
  ASM_REWRITE_TAC[ARITH; VSUM_SING_NUMSEG] THEN
  REWRITE_TAC[bel_ue] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [ARITH_RULE `1 = 0 + 1`] THEN
  REWRITE_TAC[GSYM SUMS_REINDEX; GSYM ADD1] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`rho:real`; `bel_ue (mu:complex->complex) e`; `z:complex`] BEL_S_SERIES) THEN
  ASM_REWRITE_TAC[GSYM bel_nsol; ETA_AX] THEN
  DISCH_THEN(MP_TAC o SPEC `(mu:complex->complex) z` o MATCH_MP SERIES_COMPLEX_LMUL) THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\n. bel_ue (mu:complex->complex) e (SUC n) z`;
                 `bel_nsol (mu:complex->complex) e z - e z`;
                 `(mu:complex->complex) z * bel_s (bel_nsol mu e) z`; `from 0`]
                SERIES_UNIQUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[bel_ue; bel_tt] THEN ASM_REWRITE_TAC[];
    CONV_TAC COMPLEX_RING]);;

(* ========================================================================= *)
(* Wirtinger calculus helpers (identity, sums, commutation,                  *)
(* composition with cexp) and the planar solution f = z + C h of the         *)
(* Beltrami equation f_zbar = mu f_z.                                        *)
(* ========================================================================= *)

let BEL_WIRT_ID = prove
 (`!z:complex. wirtinger_dz (\w. w) z = Cx(&1) /\ wirtinger_dbar (\w. w) z = Cx(&0)`,
  GEN_TAC THEN
  SUBGOAL_THEN `frechet_derivative (\w:complex. w) (at z) = (\h. h)` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    REWRITE_TAC[HAS_DERIVATIVE_ID];
    ASM_REWRITE_TAC[WIRTINGER_DZ_FRECHET; WIRTINGER_DBAR_FRECHET] THEN
    CONV_TAC COMPLEX_FIELD]);;

let BEL_WIRT_ADD = prove
 (`!f g:complex->complex z.
        f differentiable at z /\ g differentiable at z
        ==> wirtinger_dz (\w. f w + g w) z = wirtinger_dz f z + wirtinger_dz g z /\
            wirtinger_dbar (\w. f w + g w) z = wirtinger_dbar f z + wirtinger_dbar g z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FRECHET_DERIVATIVE_WORKS] THEN STRIP_TAC THEN
  REWRITE_TAC[WIRTINGER_DZ_FRECHET; WIRTINGER_DBAR_FRECHET] THEN
  MP_TAC(ISPECL [`f:complex->complex`; `frechet_derivative (f:complex->complex) (at z)`;
                 `g:complex->complex`; `frechet_derivative (g:complex->complex) (at z)`;
                 `at (z:complex)`] HAS_DERIVATIVE_ADD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[] THEN
  REWRITE_TAC[complex_div] THEN CONV_TAC COMPLEX_RING);;

let BEL_WIRT_SUB = prove
 (`!f g:complex->complex z.
        f differentiable at z /\ g differentiable at z
        ==> wirtinger_dz (\w. f w - g w) z = wirtinger_dz f z - wirtinger_dz g z /\
            wirtinger_dbar (\w. f w - g w) z = wirtinger_dbar f z - wirtinger_dbar g z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FRECHET_DERIVATIVE_WORKS] THEN STRIP_TAC THEN
  REWRITE_TAC[WIRTINGER_DZ_FRECHET; WIRTINGER_DBAR_FRECHET] THEN
  MP_TAC(ISPECL [`f:complex->complex`; `frechet_derivative (f:complex->complex) (at z)`;
                 `g:complex->complex`; `frechet_derivative (g:complex->complex) (at z)`;
                 `at (z:complex)`] HAS_DERIVATIVE_SUB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[] THEN
  REWRITE_TAC[complex_div] THEN CONV_TAC COMPLEX_RING);;

let BEL_WIRT_COMMUTE = prove
 (`!f:complex->complex z.
        smooth_map_on (:complex) f
        ==> wirtinger_dbar (wirtinger_dz f) z = wirtinger_dz (wirtinger_dbar f) z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!j. smooth_map_on (:complex) (partial_derivative j (f:complex->complex))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[BEL_SMOOTH_PD_SMOOTH]; ALL_TAC] THEN
  REWRITE_TAC[BEL_WIRTINGER_PD] THEN
  SUBGOAL_THEN
   `!a b i. partial_derivative i
              (\w. a * partial_derivative 1 (f:complex->complex) w +
                   b * partial_derivative 2 f w) z =
            a * partial_derivative i (partial_derivative 1 f) z +
            b * partial_derivative i (partial_derivative 2 f) z`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC BEL_PD_LINCOMB THEN
    ASM_SIMP_TAC[BEL_SMOOTH_DIFFERENTIABLE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:complex->complex`; `1`; `2`; `z:complex`] BEL_SCHWARZ) THEN
  ASM_REWRITE_TAC[ARITH] THEN DISCH_THEN SUBST1_TAC THEN
  CONV_TAC COMPLEX_RING);;

(* Composition with cexp.                                                    *)

let BEL_CEXP_CD = prove
 (`!n c. continuously_differentiable n (:complex) (\z. c * cexp z)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0] THEN GEN_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN REWRITE_TAC[CONTINUOUS_ON_CEXP];
    ALL_TAC] THEN
  GEN_TAC THEN REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_UNIV] THEN
  EXISTS_TAC `\z h. (c * h) * cexp z` THEN REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:complex` THEN
  MP_TAC(ISPECL [`( * ):complex->complex->complex`; `\z:complex. c:complex`; `cexp`;
                 `\h:complex. Cx(&0)`; `\h:complex. cexp z * h`; `z:complex`]
                HAS_DERIVATIVE_BILINEAR_AT) THEN
  REWRITE_TAC[BILINEAR_COMPLEX_MUL; GSYM COMPLEX_VEC_0; HAS_DERIVATIVE_CONST] THEN
  REWRITE_TAC[GSYM has_complex_derivative; HAS_COMPLEX_DERIVATIVE_CEXP] THEN
  REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_MUL_LZERO; COMPLEX_ADD_RID; ETA_AX] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN CONV_TAC COMPLEX_RING);;

let BEL_SMOOTH_CEXP = prove
 (`!f:complex->complex.
        smooth_map_on (:complex) f ==> smooth_map_on (:complex) (\z. cexp(f z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z. cexp((f:complex->complex) z)) = cexp o f` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:complex)` THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; smooth_map_on] THEN GEN_TAC THEN
  MP_TAC(SPECL [`n:num`; `Cx(&1)`] BEL_CEXP_CD) THEN
  REWRITE_TAC[COMPLEX_MUL_LID; ETA_AX]);;

let BEL_WIRT_CEXP = prove
 (`!f:complex->complex z.
        f differentiable at z
        ==> wirtinger_dz (\w. cexp(f w)) z = cexp(f z) * wirtinger_dz f z /\
            wirtinger_dbar (\w. cexp(f w)) z = cexp(f z) * wirtinger_dbar f z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FRECHET_DERIVATIVE_WORKS] THEN STRIP_TAC THEN
  SUBGOAL_THEN `frechet_derivative (\w. cexp((f:complex->complex) w)) (at z) =
                (\h. cexp(f z) * frechet_derivative f (at z) h)` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MP_TAC(ISPECL [`f:complex->complex`; `cexp`;
                   `frechet_derivative (f:complex->complex) (at z)`;
                   `\h. cexp((f:complex->complex) z) * h`; `z:complex`] DIFF_CHAIN_AT) THEN
    ASM_REWRITE_TAC[GSYM has_complex_derivative; HAS_COMPLEX_DERIVATIVE_CEXP; o_DEF];
    ASM_REWRITE_TAC[WIRTINGER_DZ_FRECHET; WIRTINGER_DBAR_FRECHET] THEN
    REWRITE_TAC[complex_div] THEN CONV_TAC COMPLEX_RING]);;

(* Liouville for smooth functions with vanishing dbar derivative.            *)

let BEL_LIOUVILLE_DBAR = prove
 (`!W:complex->complex.
        smooth_map_on (:complex) W /\ (!z. wirtinger_dbar W z = Cx(&0)) /\
        (W --> Cx(&0)) at_infinity
        ==> !z. W z = Cx(&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`W:complex->complex`; `Cx(&0)`] LIOUVILLE_WEAK) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[holomorphic_on; IN_UNIV; WITHIN_UNIV] THEN X_GEN_TAC `w:complex` THEN
  REWRITE_TAC[GSYM complex_differentiable] THEN
  MP_TAC(ISPECL [`W:complex->complex`; `w:complex`] WIRTINGER_DBAR_EQ_ZERO) THEN
  ASM_SIMP_TAC[BEL_SMOOTH_DIFFERENTIABLE]);;

let BEL_N2_ZERO_IMP = prove
 (`!R f:complex->complex.
        f continuous_on (:complex) /\ bel_supp R f /\ bel_n2 f = &0
        ==> !z. f z = Cx(&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(:complex)`; `&2`; `f:complex->complex`] LNORM_EQ_0) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC BEL_LSPACE2 THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM bel_n2; IN_UNIV] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN
  SUBGOAL_THEN `{x:complex | ~((f:complex->complex) x = vec 0)} = {}` MP_TAC THENL
   [MATCH_MP_TAC(MESON[OPEN_NOT_NEGLIGIBLE] `open (s:complex->bool) /\ negligible s ==> s = {}`) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `{x:complex | ~((f:complex->complex) x = vec 0)} =
                  {x | f x IN (:complex) DIFF {vec 0}}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_SING]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    SIMP_TAC[OPEN_DIFF; OPEN_UNIV; CLOSED_SING] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV];
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN MESON_TAC[]]);;

let BEL_SUPP_MUL_LEFT = prove
 (`!R f g:complex->complex. bel_supp R f ==> bel_supp R (\w. f w * g w)`,
  SIMP_TAC[bel_supp; COMPLEX_MUL_LZERO]);;

let BEL_S_ZERO = prove
 (`!z. bel_s (\w. Cx(&0)) z = Cx(&0)`,
  GEN_TAC THEN REWRITE_TAC[bel_s] THEN
  SUBGOAL_THEN `wirtinger_dz (\w:complex. Cx(&0)) = (\w. Cx(&0))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; WIRTINGER_DZ_FRECHET; FRECHET_DERIVATIVE_CONST_AT] THEN
    REWRITE_TAC[COMPLEX_VEC_0] THEN CONV_TAC COMPLEX_FIELD;
    REWRITE_TAC[bel_ct; complex_div; COMPLEX_MUL_LZERO] THEN
    REWRITE_TAC[GSYM COMPLEX_VEC_0; INTEGRAL_0] THEN
    REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_MUL_RZERO]]);;

let BEL_HOMOG_ZERO = prove
 (`!rho mu k ff:complex->complex.
        smooth_map_on (:complex) mu /\ bel_supp rho mu /\ (!z. norm(mu z) <= k) /\ k < &1 /\
        smooth_map_on (:complex) ff /\ (ff --> Cx(&0)) at_infinity /\
        (!z. wirtinger_dbar ff z = wirtinger_dz (\w. mu w * ff w) z)
        ==> !z. ff z = Cx(&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `P = \w:complex. (mu:complex->complex) w * ff w` THEN
  SUBGOAL_THEN `smooth_map_on (:complex) (P:complex->complex) /\ bel_supp rho P`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN CONJ_TAC THENL
     [MATCH_MP_TAC BEL_SMOOTH_MUL THEN ASM_REWRITE_TAC[ETA_AX];
      MATCH_MP_TAC BEL_SUPP_MUL_LEFT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:complex) (wirtinger_dz (P:complex->complex)) /\
                bel_supp rho (wirtinger_dz P)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[BEL_SMOOTH_WIRTINGER] THEN
    MP_TAC(ISPECL [`rho:real`; `P:complex->complex`] BEL_SUPP_WIRTINGER) THEN
    ASM_SIMP_TAC[BEL_SMOOTH_C1];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. (ff:complex->complex) z = bel_s P z` ASSUME_TAC THENL
   [MP_TAC(ISPEC `\w. (ff:complex->complex) w - bel_s P w` BEL_LIOUVILLE_DBAR) THEN
    REWRITE_TAC[COMPLEX_SUB_0] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC BEL_SMOOTH_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC BEL_S_SMOOTH THEN EXISTS_TAC `rho:real` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `z:complex` THEN
      MP_TAC(ISPECL [`ff:complex->complex`; `bel_s (P:complex->complex)`; `z:complex`]
                    BEL_WIRT_SUB) THEN
      ANTS_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC BEL_SMOOTH_DIFFERENTIABLE THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC BEL_S_SMOOTH THEN EXISTS_TAC `rho:real` THEN
        ASM_REWRITE_TAC[];
        DISCH_THEN(fun th -> REWRITE_TAC[ETA_AX; CONJUNCT2 th])] THEN
      ASM_REWRITE_TAC[bel_s] THEN
      MP_TAC(ISPECL [`rho:real`; `wirtinger_dz (P:complex->complex)`; `z:complex`]
                    BEL_CT_DBAR) THEN
      ASM_SIMP_TAC[BEL_SMOOTH_C1; COMPLEX_SUB_REFL];
      REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN
      SUBGOAL_THEN `vec 0:complex = vec 0 - vec 0` SUBST1_TAC THENL
       [REWRITE_TAC[VECTOR_SUB_REFL]; ALL_TAC] THEN
      MATCH_MP_TAC LIM_SUB THEN REWRITE_TAC[COMPLEX_VEC_0; ETA_AX] THEN
      ASM_REWRITE_TAC[bel_s] THEN MATCH_MP_TAC BEL_CT_LIM_INFINITY THEN
      EXISTS_TAC `rho:real` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `bel_tt mu (P:complex->complex) = P` ASSUME_TAC THENL
   [REWRITE_TAC[bel_tt; FUN_EQ_THM] THEN EXPAND_TAC "P" THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `bel_n2 (P:complex->complex) = &0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`rho:real`; `rho:real`; `mu:complex->complex`; `P:complex->complex`;
                   `k:real`] BEL_TT_L2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`rho:real`; `P:complex->complex`] BEL_N2_POS) THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(&1 - k) * bel_n2 (P:complex->complex) <= (&1 - k) * &0` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_SUB_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `P = (\w:complex. Cx(&0))` ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN MATCH_MP_TAC BEL_N2_ZERO_IMP THEN
    EXISTS_TAC `rho:real` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[BEL_S_ZERO]);;

(* The planar solution f = z + C h, h = bel_nsol mu mu.                       *)

let bel_fsol = new_definition
 `bel_fsol (mu:complex->complex) = \z. z + bel_ct (bel_nsol mu mu) z`;;

let BEL_FSOL_PROPS = prove
 (`!rho mu:complex->complex k.
        smooth_map_on (:complex) mu /\ bel_supp rho mu /\ (!z. norm(mu z) <= k) /\ k < &1
        ==> smooth_map_on (:complex) (bel_fsol mu) /\
            (!z. wirtinger_dbar (bel_fsol mu) z = bel_nsol mu mu z) /\
            (!z. wirtinger_dz (bel_fsol mu) z = Cx(&1) + bel_s (bel_nsol mu mu) z) /\
            (!z. wirtinger_dbar (bel_fsol mu) z = mu z * wirtinger_dz (bel_fsol mu) z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on (:complex) (bel_nsol (mu:complex->complex) mu) /\
                bel_supp rho (bel_nsol mu mu)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC BEL_NSOL_SMOOTH THEN ASM_MESON_TAC[];
      MATCH_MP_TAC BEL_NSOL_SUPP THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:complex) (bel_ct (bel_nsol (mu:complex->complex) mu))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC BEL_CT_SMOOTH THEN EXISTS_TAC `rho:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:complex) (bel_fsol (mu:complex->complex))` ASSUME_TAC THENL
   [REWRITE_TAC[bel_fsol] THEN MATCH_MP_TAC BEL_SMOOTH_ADD THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. wirtinger_dbar (bel_fsol mu) z = bel_nsol (mu:complex->complex) mu z /\
        wirtinger_dz (bel_fsol mu) z = Cx(&1) + bel_s (bel_nsol mu mu) z`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[bel_fsol] THEN
    MP_TAC(ISPECL [`\w:complex. w`; `bel_ct (bel_nsol (mu:complex->complex) mu)`;
                   `z:complex`] BEL_WIRT_ADD) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[DIFFERENTIABLE_ID] THEN MATCH_MP_TAC BEL_SMOOTH_DIFFERENTIABLE THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[ETA_AX] THEN DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
    REWRITE_TAC[BEL_WIRT_ID; COMPLEX_ADD_LID; COMPLEX_EQ_ADD_LCANCEL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC BEL_CT_DBAR; MATCH_MP_TAC BEL_CT_DZ] THEN
    EXISTS_TAC `rho:real` THEN ASM_SIMP_TAC[BEL_SMOOTH_C1];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:complex` THEN
  MP_TAC(ISPECL [`rho:real`; `mu:complex->complex`; `mu:complex->complex`; `k:real`;
                 `z:complex`] BEL_NSOL_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC COMPLEX_RING);;

(* Ahlfors' sigma: f_z = exp(sigma), sigma = C q, q = mu_z + mu S q.         *)

let bel_sigma = new_definition
 `bel_sigma (mu:complex->complex) = bel_ct (bel_nsol mu (wirtinger_dz mu))`;;

let BEL_SIGMA_PROPS = prove
 (`!rho mu:complex->complex k.
        smooth_map_on (:complex) mu /\ bel_supp rho mu /\ (!z. norm(mu z) <= k) /\ k < &1
        ==> smooth_map_on (:complex) (bel_sigma mu) /\
            (!z. wirtinger_dbar (bel_sigma mu) z =
                 wirtinger_dz mu z + mu z * wirtinger_dz (bel_sigma mu) z) /\
            (bel_sigma mu --> Cx(&0)) at_infinity`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on (:complex) (wirtinger_dz (mu:complex->complex)) /\
                bel_supp rho (wirtinger_dz mu)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[BEL_SMOOTH_WIRTINGER] THEN
    MP_TAC(ISPECL [`rho:real`; `mu:complex->complex`] BEL_SUPP_WIRTINGER) THEN
    ASM_SIMP_TAC[BEL_SMOOTH_C1];
    ALL_TAC] THEN
  ABBREV_TAC `q = bel_nsol (mu:complex->complex) (wirtinger_dz mu)` THEN
  SUBGOAL_THEN `smooth_map_on (:complex) (q:complex->complex) /\ bel_supp rho q`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN CONJ_TAC THENL
     [MATCH_MP_TAC BEL_NSOL_SMOOTH THEN ASM_MESON_TAC[];
      MATCH_MP_TAC BEL_NSOL_SUPP THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[bel_sigma] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC BEL_CT_SMOOTH THEN EXISTS_TAC `rho:real` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `z:complex` THEN
    MP_TAC(ISPECL [`rho:real`; `q:complex->complex`; `z:complex`] BEL_CT_DBAR) THEN
    MP_TAC(ISPECL [`rho:real`; `q:complex->complex`; `z:complex`] BEL_CT_DZ) THEN
    ASM_SIMP_TAC[BEL_SMOOTH_C1] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
    EXPAND_TAC "q" THEN MATCH_MP_TAC BEL_NSOL_EQ THEN ASM_MESON_TAC[];
    MATCH_MP_TAC BEL_CT_LIM_INFINITY THEN EXISTS_TAC `rho:real` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS]]);;

let BEL_FSOL_DZ_EXP = prove
 (`!rho mu:complex->complex k z.
        smooth_map_on (:complex) mu /\ bel_supp rho mu /\ (!z. norm(mu z) <= k) /\ k < &1
        ==> wirtinger_dz (bel_fsol mu) z = cexp(bel_sigma mu z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rho:real`; `mu:complex->complex`; `k:real`] BEL_FSOL_PROPS) THEN
  MP_TAC(ISPECL [`rho:real`; `mu:complex->complex`; `k:real`] BEL_SIGMA_PROPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `f = bel_fsol (mu:complex->complex)` THEN
  ABBREV_TAC `s = bel_sigma (mu:complex->complex)` THEN
  SUBGOAL_THEN `smooth_map_on (:complex) (wirtinger_dz (f:complex->complex)) /\
                smooth_map_on (:complex) (\w. cexp((s:complex->complex) w))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[BEL_SMOOTH_WIRTINGER; BEL_SMOOTH_CEXP]; ALL_TAC] THEN
  MP_TAC(ISPECL [`rho:real`; `mu:complex->complex`; `k:real`;
                 `\w. wirtinger_dz (f:complex->complex) w - cexp((s:complex->complex) w)`]
                BEL_HOMOG_ZERO) THEN
  REWRITE_TAC[COMPLEX_SUB_0] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [MATCH_MP_TAC BEL_SMOOTH_SUB THEN ASM_REWRITE_TAC[ETA_AX];
    REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN
    SUBGOAL_THEN `vec 0:complex = Cx(&1) - Cx(&1)` SUBST1_TAC THENL
     [REWRITE_TAC[COMPLEX_SUB_REFL; COMPLEX_VEC_0]; ALL_TAC] THEN
    MATCH_MP_TAC LIM_SUB THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `((\w. Cx(&1) + bel_s (bel_nsol (mu:complex->complex) mu) w) -->
                     Cx(&1) + Cx(&0)) at_infinity` MP_TAC THENL
       [ALL_TAC; REWRITE_TAC[COMPLEX_ADD_RID]] THEN
      MATCH_MP_TAC LIM_ADD THEN REWRITE_TAC[LIM_CONST] THEN
      REWRITE_TAC[bel_s; ETA_AX] THEN MATCH_MP_TAC BEL_CT_LIM_INFINITY THEN
      EXISTS_TAC `rho:real` THEN
      SUBGOAL_THEN `smooth_map_on (:complex) (bel_nsol (mu:complex->complex) mu) /\
                    bel_supp rho (bel_nsol mu mu)` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC BEL_NSOL_SMOOTH THEN ASM_MESON_TAC[];
          MATCH_MP_TAC BEL_NSOL_SUPP THEN ASM_MESON_TAC[]];
        ALL_TAC] THEN
      MP_TAC(ISPEC `bel_nsol (mu:complex->complex) mu` BEL_SMOOTH_WIRTINGER) THEN
      MP_TAC(ISPECL [`rho:real`; `bel_nsol (mu:complex->complex) mu`] BEL_SUPP_WIRTINGER) THEN
      ASM_SIMP_TAC[BEL_SMOOTH_C1; SMOOTH_MAP_ON_CONTINUOUS];
      REWRITE_TAC[GSYM CEXP_0] THEN
      MATCH_MP_TAC(REWRITE_RULE[o_DEF] LIM_CONTINUOUS_FUNCTION) THEN
      ASM_REWRITE_TAC[CONTINUOUS_AT_CEXP; ETA_AX]];
    X_GEN_TAC `z:complex` THEN
    SUBGOAL_THEN `!g:complex->complex. smooth_map_on (:complex) g ==> g differentiable at z`
    ASSUME_TAC THENL [SIMP_TAC[BEL_SMOOTH_DIFFERENTIABLE]; ALL_TAC] THEN
    SUBGOAL_THEN `smooth_map_on (:complex) (\w. (mu:complex->complex) w * wirtinger_dz f w) /\
                  smooth_map_on (:complex) (\w. (mu:complex->complex) w * cexp(s w))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC BEL_SMOOTH_MUL THEN ASM_REWRITE_TAC[ETA_AX];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`wirtinger_dz (f:complex->complex)`; `\w. cexp((s:complex->complex) w)`;
                   `z:complex`] BEL_WIRT_SUB) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
                    ALL_TAC] THEN
    REWRITE_TAC[ETA_AX] THEN DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2 th]) THEN
    SUBGOAL_THEN `(\w. (mu:complex->complex) w * (wirtinger_dz f w - cexp(s w))) =
                  (\w. mu w * wirtinger_dz f w - mu w * cexp(s w))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
    MP_TAC(BETA_RULE(ISPECL [`\w. (mu:complex->complex) w * wirtinger_dz f w`;
                             `\w. (mu:complex->complex) w * cexp(s w)`; `z:complex`]
                            BEL_WIRT_SUB)) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
                    ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN
    MP_TAC(ISPECL [`f:complex->complex`; `z:complex`] BEL_WIRT_COMMUTE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `wirtinger_dbar (f:complex->complex) =
                  (\w. (mu:complex->complex) w * wirtinger_dz f w)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MP_TAC(BETA_RULE(ISPECL [`mu:complex->complex`; `\w. cexp((s:complex->complex) w)`;
                             `z:complex`] BEL_WIRTINGER_MUL)) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
                    ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN
    MP_TAC(ISPECL [`s:complex->complex`; `z:complex`] BEL_WIRT_CEXP) THEN
    ANTS_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:complex` o check (fun th ->
      is_forall(concl th) &&
      (try fst(dest_const(fst(strip_comb(lhs(snd(dest_forall(concl th))))))) = "wirtinger_dbar" &&
           rand(rator(lhs(snd(dest_forall(concl th))))) = `s:complex->complex`
       with Failure _ -> false))) THEN
    DISCH_THEN SUBST1_TAC THEN CONV_TAC COMPLEX_RING]);;

(* The Jacobian determinant in Wirtinger form; positivity for f.              *)

let BEL_DET_WIRT = prove
 (`!f:complex->complex z.
        det(matrix(frechet_derivative f (at z))) =
        norm(wirtinger_dz f z) pow 2 - norm(wirtinger_dbar f z) pow 2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BEL_WIRT_SQ_DIFF; DET_2; partial_derivative] THEN
  SIMP_TAC[matrix; LAMBDA_BETA; DIMINDEX_2; ARITH] THEN
  REWRITE_TAC[GSYM RE_DEF; GSYM IM_DEF; complex_mul; RE; IM; RE_CNJ; IM_CNJ] THEN
  REAL_ARITH_TAC);;

let BEL_FSOL_DET_POS = prove
 (`!rho mu:complex->complex k z.
        smooth_map_on (:complex) mu /\ bel_supp rho mu /\ (!z. norm(mu z) <= k) /\ k < &1
        ==> &0 < det(matrix(frechet_derivative (bel_fsol mu) (at z)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[BEL_DET_WIRT] THEN
  MP_TAC(ISPECL [`rho:real`; `mu:complex->complex`; `k:real`] BEL_FSOL_PROPS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `z:complex` o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`rho:real`; `mu:complex->complex`; `k:real`; `z:complex`]
                BEL_FSOL_DZ_EXP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; REAL_POW_MUL] THEN
  SUBGOAL_THEN `&0 < norm(cexp(bel_sigma (mu:complex->complex) z)) pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN REWRITE_TAC[NORM_POS_LT; COMPLEX_VEC_0; CEXP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm((mu:complex->complex) z) pow 2 < &1` MP_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `k pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE];
      MATCH_MP_TAC(REAL_ARITH `x < &1 pow 2 ==> x < &1`) THEN
      MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH] THEN
      ASM_MESON_TAC[NORM_POS_LE; REAL_LE_TRANS]];
    ALL_TAC] THEN
  SPEC_TAC(`norm(cexp(bel_sigma (mu:complex->complex) z)) pow 2`,`a:real`) THEN
  SPEC_TAC(`norm((mu:complex->complex) z) pow 2`,`b:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 < a * (&1 - b)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* f is a proper local homeomorphism, hence a homeomorphism of the plane     *)
(* (PROPER_LOCAL_HOMEOMORPHISM_GLOBAL), with smooth inverse.                  *)

let BEL_FSOL_PERTURB_BOUND = prove
 (`!rho mu:complex->complex k.
        smooth_map_on (:complex) mu /\ bel_supp rho mu /\ (!z. norm(mu z) <= k) /\ k < &1
        ==> ?C. !z. norm(bel_fsol mu z - z) <= C`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on (:complex) (bel_nsol (mu:complex->complex) mu) /\
                bel_supp rho (bel_nsol mu mu)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC BEL_NSOL_SMOOTH THEN ASM_MESON_TAC[];
      MATCH_MP_TAC BEL_NSOL_SUPP THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rho:real`; `bel_nsol (mu:complex->complex) mu`] BEL_SUPP_BOUNDED_FN) THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS] THEN DISCH_THEN(X_CHOOSE_TAC `M:real`) THEN
  MP_TAC(SPEC `rho:real` BEL_CT_BOUND) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `C * M` THEN X_GEN_TAC `z:complex` THEN
  REWRITE_TAC[bel_fsol; COMPLEX_RING `(z + c) - z:complex = c`] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS]);;

let BEL_FSOL_HOMEO = prove
 (`!rho mu:complex->complex k.
        smooth_map_on (:complex) mu /\ bel_supp rho mu /\ (!z. norm(mu z) <= k) /\ k < &1
        ==> ?g. homeomorphism ((:complex),(:complex)) (bel_fsol mu,g)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`rho:real`; `mu:complex->complex`; `k:real`] BEL_FSOL_PROPS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`rho:real`; `mu:complex->complex`; `k:real`] BEL_FSOL_PERTURB_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `C:real`) THEN
  MATCH_MP_TAC PROPER_LOCAL_HOMEOMORPHISM_GLOBAL THEN
  REWRITE_TAC[PATH_CONNECTED_UNIV; IN_UNIV; SUBSET_UNIV; SUBTOPOLOGY_UNIV] THEN
  SIMP_TAC[CONVEX_IMP_SIMPLY_CONNECTED; CONVEX_UNIV] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `K:complex->bool` THEN DISCH_TAC THEN
    REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
      REWRITE_TAC[BOUNDED_POS; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `B + abs C + &1` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `bel_fsol (mu:complex->complex) z`) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `z:complex`) THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`z:complex`; `bel_fsol (mu:complex->complex) z`] NORM_TRIANGLE_SUB) THEN
      REWRITE_TAC[NORM_SUB] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_UNIV THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN GEN_TAC THEN
      MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
      MATCH_MP_TAC BEL_SMOOTH_DIFFERENTIABLE THEN ASM_REWRITE_TAC[ETA_AX]];
    X_GEN_TAC `x:complex` THEN
    MP_TAC(ISPECL [`bel_fsol (mu:complex->complex)`;
                   `\x. frechet_derivative (bel_fsol (mu:complex->complex)) (at x)`;
                   `x:complex`; `(:complex)`] INVERSE_FUNCTION_THEOREM) THEN
    REWRITE_TAC[OPEN_UNIV; IN_UNIV; SUBSET_UNIV] THEN ANTS_TAC THENL
     [X_GEN_TAC `y:complex` THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
        MATCH_MP_TAC BEL_SMOOTH_DIFFERENTIABLE THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC BEL_FSOL_DET_POS THEN
        ASM_MESON_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`t:complex->bool`; `u:complex->bool`; `g:complex->complex`;
                         `g':complex->complex->complex`] THEN
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`t:complex->bool`; `u:complex->bool`;
                                         `g:complex->complex`] THEN
    ASM_REWRITE_TAC[GSYM OPEN_IN]]);;

let BEL_FSOL_INV_SMOOTH = prove
 (`!rho mu:complex->complex k g.
        smooth_map_on (:complex) mu /\ bel_supp rho mu /\ (!z. norm(mu z) <= k) /\ k < &1 /\
        homeomorphism ((:complex),(:complex)) (bel_fsol mu,g)
        ==> smooth_map_on (:complex) g`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`rho:real`; `mu:complex->complex`; `k:real`] BEL_FSOL_PROPS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  UNDISCH_TAC `homeomorphism ((:complex),(:complex))
                 (bel_fsol (mu:complex->complex),(g:complex->complex))` THEN
  REWRITE_TAC[HOMEOMORPHISM; IN_UNIV] THEN STRIP_TAC THEN
  REWRITE_TAC[smooth_map_on] THEN X_GEN_TAC `n:num` THEN
  MP_TAC(ISPECL [`n:num`; `(:complex)`; `g:complex->complex`]
                CONTINUOUSLY_DIFFERENTIABLE_LOCAL_OPEN) THEN
  REWRITE_TAC[OPEN_UNIV; IN_UNIV; SUBSET_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  X_GEN_TAC `y:complex` THEN
  MP_TAC(ISPECL [`bel_fsol (mu:complex->complex)`; `(:complex)`; `(g:complex->complex) y`]
                SMOOTH_INVERSE_FUNCTION_THEOREM) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC BEL_FSOL_DET_POS THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; diffeomorphism_on] THEN
  MAP_EVERY X_GEN_TAC [`t:complex->bool`; `u:complex->bool`; `g0:complex->complex`] THEN
  STRIP_TAC THEN EXISTS_TAC `u:complex->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_EQ_OPEN THEN
  EXISTS_TAC `g0:complex->complex` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(g:complex->complex) w = g (bel_fsol (mu:complex->complex) (g0 w))`
    SUBST1_TAC THENL
     [AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[]];
    ASM_MESON_TAC[smooth_map_on]]);;

(* The trivial coefficient gives the identity; f(z) - z -> 0 at infinity.   *)

let BEL_UE_ZERO = prove
 (`!n. bel_ue (\z:complex. Cx(&0)) (\z. Cx(&0)) n = (\z. Cx(&0))`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[bel_ue; bel_tt; COMPLEX_MUL_LZERO]);;

let BEL_NSOL_ZERO = prove
 (`bel_nsol (\z:complex. Cx(&0)) (\z. Cx(&0)) = (\z. Cx(&0))`,
  REWRITE_TAC[bel_nsol; BEL_UE_ZERO; FUN_EQ_THM] THEN
  MATCH_MP_TAC INFSUM_UNIQUE THEN REWRITE_TAC[GSYM COMPLEX_VEC_0; SERIES_0]);;

let BEL_FSOL_ZERO = prove
 (`bel_fsol (\z:complex. Cx(&0)) = (\z. z)`,
  REWRITE_TAC[bel_fsol; BEL_NSOL_ZERO; FUN_EQ_THM] THEN TRY GEN_TAC THEN
  REWRITE_TAC[bel_ct; complex_div; COMPLEX_MUL_LZERO] THEN
  REWRITE_TAC[GSYM COMPLEX_VEC_0; INTEGRAL_0] THEN
  REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_MUL_RZERO; COMPLEX_ADD_RID]);;

let BEL_FSOL_LIM = prove
 (`!rho mu:complex->complex k.
        smooth_map_on (:complex) mu /\ bel_supp rho mu /\ (!z. norm(mu z) <= k) /\ k < &1
        ==> ((\z. bel_fsol mu z - z) --> Cx(&0)) at_infinity`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[bel_fsol; COMPLEX_RING `(z + c) - z:complex = c`; ETA_AX] THEN
  MATCH_MP_TAC BEL_CT_LIM_INFINITY THEN EXISTS_TAC `rho:real` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN MATCH_MP_TAC BEL_NSOL_SMOOTH THEN
    ASM_MESON_TAC[];
    MATCH_MP_TAC BEL_NSOL_SUPP THEN ASM_MESON_TAC[]]);;

let BEL_FSOL_HOLOMORPHIC_OUTSIDE = prove
 (`!rho mu:complex->complex k z.
        smooth_map_on (:complex) mu /\ bel_supp rho mu /\ (!z. norm(mu z) <= k) /\ k < &1 /\
        rho < norm z
        ==> wirtinger_dbar (bel_fsol mu) z = Cx(&0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`rho:real`; `mu:complex->complex`; `k:real`] BEL_FSOL_PROPS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `z:complex` o CONJUNCT2 o CONJUNCT2 o
                                    CONJUNCT2) THEN
  UNDISCH_TAC `bel_supp rho (mu:complex->complex)` THEN REWRITE_TAC[bel_supp] THEN
  DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[COMPLEX_MUL_LZERO]);;

(* ========================================================================= *)
(* Families depending on a parameter t in [0,1], smooth in the               *)
(* space variable with all spatial derivatives jointly continuous in (x,t)   *)
(* (the regularity of the hypothesis of CM_D7_UNIFORMIZATION_STATEMENT).     *)
(* bel_jfam m U F: derivatives up to order m jointly continuous.              *)
(* ========================================================================= *)

let bel_dom = new_definition
 `bel_dom (U:real^M->bool) =
    {x:real^(M,1)finite_sum | fstcart x IN U /\ drop(sndcart x) IN real_interval[&0,&1]}`;;

let bel_jfam = new_definition
 `bel_jfam (m:num) (U:real^M->bool) (ff:real->real^M->real^N) <=>
    (!t. t IN real_interval[&0,&1] ==> smooth_map_on U (ff t)) /\
    !l. LENGTH l <= m /\ ALL (\i. 1 <= i /\ i <= dimindex(:M)) l
        ==> (\x. iterated_partial l (ff (drop(sndcart x))) (fstcart x)) continuous_on
            bel_dom U`;;

let BEL_JFAM_MONO = prove
 (`!m m' U ff:real->real^M->real^N.
        m <= m' /\ bel_jfam m' U ff ==> bel_jfam m U ff`,
  REWRITE_TAC[bel_jfam] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let BEL_JFAM_0 = prove
 (`!U ff:real->real^M->real^N.
        bel_jfam 0 U ff <=>
        (!t. t IN real_interval[&0,&1] ==> smooth_map_on U (ff t)) /\
        (\x. ff (drop(sndcart x)) (fstcart x)) continuous_on bel_dom U`,
  REWRITE_TAC[bel_jfam; LE; LENGTH_EQ_NIL] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[MESON[] `(!l:num list. l = [] /\ P l ==> Q l) <=> (P [] ==> Q [])`] THEN
  REWRITE_TAC[ALL; iterated_partial; ETA_AX]);;

let BEL_JFAM_SUC = prove
 (`!m U ff:real->real^M->real^N.
        open U
        ==> (bel_jfam (SUC m) U ff <=>
             bel_jfam 0 U ff /\
             !i. 1 <= i /\ i <= dimindex(:M)
                 ==> bel_jfam m U (\t. partial_derivative i (ff t)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC BEL_JFAM_MONO THEN EXISTS_TAC `SUC m` THEN ASM_REWRITE_TAC[LE_0];
      ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    UNDISCH_TAC `bel_jfam (SUC m) U (ff:real->real^M->real^N)` THEN
    REWRITE_TAC[bel_jfam] THEN STRIP_TAC THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN
      ASM_SIMP_TAC[];
      X_GEN_TAC `l:num list` THEN STRIP_TAC THEN
      REWRITE_TAC[REWRITE_RULE[iterated_partial]
                  (SPECL [`l:num list`; `[i:num]`] ITERATED_PARTIAL_APPEND)] THEN
      REWRITE_TAC[GSYM(REWRITE_RULE[iterated_partial]
                  (SPECL [`l:num list`; `[i:num]`] ITERATED_PARTIAL_APPEND))] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; ALL_APPEND; ALL] THEN ASM_ARITH_TAC];
    REWRITE_TAC[bel_jfam] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `l:num list` THEN STRIP_TAC THEN
    ASM_CASES_TAC `l:num list = []` THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `l:num list`) THEN ASM_REWRITE_TAC[LENGTH; LE_REFL; ALL];
      ALL_TAC] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `l':num list` (X_CHOOSE_THEN `j:num` SUBST_ALL_TAC) o
                  MATCH_MP BEL_LIST_SNOC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND; LENGTH; ALL_APPEND; ALL]) THEN
    REWRITE_TAC[ITERATED_PARTIAL_APPEND; iterated_partial] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[bel_jfam] THEN
    DISCH_THEN(MP_TAC o SPEC `l':num list` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]]]);;

let BEL_ITERATED_PARTIAL_LOCAL = prove
 (`!l U f g:real^M->real^N z.
        open U /\ (!z. z IN U ==> f z = g z) /\ z IN U
        ==> iterated_partial l f z = iterated_partial l g z`,
  SUBGOAL_THEN
   `!l U f g:real^M->real^N.
        open U /\ (!z. z IN U ==> f z = g z)
        ==> !z. z IN U ==> iterated_partial l f z = iterated_partial l g z`
   (fun th -> MESON_TAC[th]) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[iterated_partial] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN
  EXISTS_TAC `U:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let BEL_IN_DOM = prove
 (`!U x:real^(M,1)finite_sum.
        x IN bel_dom U <=> fstcart x IN U /\ drop(sndcart x) IN real_interval[&0,&1]`,
  REWRITE_TAC[bel_dom; IN_ELIM_THM]);;

let BEL_JFAM_EQ = prove
 (`!m U ff gg:real->real^M->real^N.
        open U /\
        (!t z. t IN real_interval[&0,&1] /\ z IN U ==> ff t z = gg t z) /\
        bel_jfam m U ff
        ==> bel_jfam m U gg`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bel_jfam] THEN STRIP_TAC THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[smooth_map_on] THEN GEN_TAC THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_EQ_OPEN THEN
    EXISTS_TAC `(ff:real->real^M->real^N) t` THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[smooth_map_on];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `\x. iterated_partial l ((ff:real->real^M->real^N) (drop(sndcart x)))
                                       (fstcart x)` THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[BEL_IN_DOM] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC BEL_ITERATED_PARTIAL_LOCAL THEN
    EXISTS_TAC `U:real^M->bool` THEN ASM_SIMP_TAC[]]);;

let BEL_JFAM_CONST = prove
 (`!m U f:real^M->real^N.
        open U /\ smooth_map_on U f ==> bel_jfam m U (\t. f)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bel_jfam] THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^(M,1)finite_sum. iterated_partial l (f:real^M->real^N) (fstcart x)) =
                iterated_partial l f o fstcart` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `U:real^M->bool` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ITERATED_PARTIAL THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; BEL_IN_DOM] THEN SIMP_TAC[]]);;

(* Algebra of families.                                                       *)

let BEL_JFAM_SMOOTH = prove
 (`!m U ff:real->real^M->real^N t.
        bel_jfam m U ff /\ t IN real_interval[&0,&1] ==> smooth_map_on U (ff t)`,
  SIMP_TAC[bel_jfam]);;

let BEL_JFAM_DIFF = prove
 (`!m U ff:real->real^M->real^N t z.
        open U /\ bel_jfam m U ff /\ t IN real_interval[&0,&1] /\ z IN U
        ==> ff t differentiable at z`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `U:real^M->bool` THEN ASM_MESON_TAC[BEL_JFAM_SMOOTH]);;

let BEL_JFAM_PD = prove
 (`!m U ff:real->real^M->real^N i.
        open U /\ bel_jfam (SUC m) U ff /\ 1 <= i /\ i <= dimindex(:M)
        ==> bel_jfam m U (\t. partial_derivative i (ff t))`,
  MESON_TAC[BEL_JFAM_SUC]);;

let BEL_JFAM_ADD0 = prove
 (`!U ff gg:real->real^M->real^N.
        open U /\ bel_jfam 0 U ff /\ bel_jfam 0 U gg
        ==> bel_jfam 0 U (\t x. ff t x + gg t x)`,
  REWRITE_TAC[BEL_JFAM_0] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_SIMP_TAC[ETA_AX];
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN ASM_REWRITE_TAC[]]);;

let BEL_JFAM_ADD = prove
 (`!m U ff gg:real->real^M->real^N.
        open U /\ bel_jfam m U ff /\ bel_jfam m U gg
        ==> bel_jfam m U (\t x. ff t x + gg t x)`,
  INDUCT_TAC THENL [REWRITE_TAC[BEL_JFAM_ADD0]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[BEL_JFAM_SUC] THEN CONJ_TAC THENL
   [MATCH_MP_TAC BEL_JFAM_ADD0 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC BEL_JFAM_MONO THEN EXISTS_TAC `SUC m` THEN ASM_REWRITE_TAC[LE_0];
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC BEL_JFAM_EQ THEN
  EXISTS_TAC `\t x. partial_derivative i ((ff:real->real^M->real^N) t) x +
                    partial_derivative i (gg t) x` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC PARTIAL_DERIVATIVE_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC BEL_JFAM_DIFF THEN
    MAP_EVERY EXISTS_TAC [`SUC m`; `U:real^M->bool`] THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[BEL_JFAM_PD; ETA_AX]]);;

let BEL_JFAM_MUL_DROP0 = prove
 (`!U a:real->real^M->real^1 gg:real->real^M->real^N.
        open U /\ bel_jfam 0 U a /\ bel_jfam 0 U gg
        ==> bel_jfam 0 U (\t x. drop(a t x) % gg t x)`,
  REWRITE_TAC[BEL_JFAM_0] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_SIMP_TAC[ETA_AX];
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX] THEN
    ASM_REWRITE_TAC[]]);;

let BEL_JFAM_MUL_DROP = prove
 (`!m U a:real->real^M->real^1 gg:real->real^M->real^N.
        open U /\ bel_jfam m U a /\ bel_jfam m U gg
        ==> bel_jfam m U (\t x. drop(a t x) % gg t x)`,
  INDUCT_TAC THENL [REWRITE_TAC[BEL_JFAM_MUL_DROP0]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[BEL_JFAM_SUC] THEN CONJ_TAC THENL
   [MATCH_MP_TAC BEL_JFAM_MUL_DROP0 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC BEL_JFAM_MONO THEN EXISTS_TAC `SUC m` THEN ASM_REWRITE_TAC[LE_0];
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC BEL_JFAM_EQ THEN
  EXISTS_TAC `\t x. drop((a:real->real^M->real^1) t x) %
                    partial_derivative i ((gg:real->real^M->real^N) t) x +
                    drop(partial_derivative i (a t) x) % gg t x` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC PARTIAL_DERIVATIVE_MUL THEN CONJ_TAC THEN
    MATCH_MP_TAC BEL_JFAM_DIFF THEN
    MAP_EVERY EXISTS_TAC [`SUC m`; `U:real^M->bool`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC BEL_JFAM_ADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    TRY(CONJ_TAC THEN MATCH_MP_TAC BEL_JFAM_MONO THEN EXISTS_TAC `SUC m` THEN
        ASM_REWRITE_TAC[] THEN ARITH_TAC) THEN
    ASM_SIMP_TAC[BEL_JFAM_PD; ETA_AX] THEN
    MATCH_MP_TAC BEL_JFAM_MONO THEN EXISTS_TAC `SUC m` THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

let BEL_PD_LINEAR_O = prove
 (`!i (L:real^N->real^P) (f:real^M->real^N) x.
        linear L /\ f differentiable at x
        ==> partial_derivative i (L o f) x = L(partial_derivative i f x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`i:num`; `f:real^M->real^N`; `L:real^N->real^P`; `x:real^M`]
                PARTIAL_DERIVATIVE_CHAIN) THEN
  ASM_SIMP_TAC[DIFFERENTIABLE_LINEAR] THEN DISCH_THEN SUBST1_TAC THEN
  AP_THM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR]);;

let BEL_JFAM_LINEAR_O0 = prove
 (`!U (L:real^N->real^P) ff:real->real^M->real^N.
        open U /\ linear L /\ bel_jfam 0 U ff ==> bel_jfam 0 U (\t. L o ff t)`,
  REWRITE_TAC[BEL_JFAM_0] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_SIMP_TAC[];
    REWRITE_TAC[o_DEF] THEN
    SUBGOAL_THEN `(\x. (L:real^N->real^P) ((ff:real->real^M->real^N) (drop(sndcart x))
                                                                 (fstcart x))) =
                  L o (\x. ff (drop(sndcart x)) (fstcart x))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON]]);;

let BEL_JFAM_LINEAR_O = prove
 (`!m U (L:real^N->real^P) ff:real->real^M->real^N.
        open U /\ linear L /\ bel_jfam m U ff ==> bel_jfam m U (\t. L o ff t)`,
  INDUCT_TAC THENL [REWRITE_TAC[BEL_JFAM_LINEAR_O0]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[BEL_JFAM_SUC] THEN CONJ_TAC THENL
   [MATCH_MP_TAC BEL_JFAM_LINEAR_O0 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC BEL_JFAM_MONO THEN EXISTS_TAC `SUC m` THEN ASM_REWRITE_TAC[LE_0];
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC BEL_JFAM_EQ THEN
  EXISTS_TAC `\t. (L:real^N->real^P) o partial_derivative i ((ff:real->real^M->real^N) t)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC BEL_PD_LINEAR_O THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC BEL_JFAM_DIFF THEN
    MAP_EVERY EXISTS_TAC [`SUC m`; `U:real^M->bool`] THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[BEL_JFAM_PD]]);;

let BEL_JFAM_CMUL = prove
 (`!m U c ff:real->real^M->real^N.
        open U /\ bel_jfam m U ff ==> bel_jfam m U (\t x. c % ff t x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:num`; `U:real^M->bool`; `\x:real^N. c % x`;
                 `ff:real->real^M->real^N`] BEL_JFAM_LINEAR_O) THEN
  ASM_REWRITE_TAC[LINEAR_SCALING; o_DEF]);;

let BEL_JFAM_NEG = prove
 (`!m U ff:real->real^M->real^N.
        open U /\ bel_jfam m U ff ==> bel_jfam m U (\t x. --(ff t x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:num`; `U:real^M->bool`; `--(&1)`; `ff:real->real^M->real^N`]
                BEL_JFAM_CMUL) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LNEG; VECTOR_MUL_LID]);;

let BEL_JFAM_SUB = prove
 (`!m U ff gg:real->real^M->real^N.
        open U /\ bel_jfam m U ff /\ bel_jfam m U gg
        ==> bel_jfam m U (\t x. ff t x - gg t x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VECTOR_SUB] THEN
  MP_TAC(ISPECL [`m:num`; `U:real^M->bool`; `ff:real->real^M->real^N`;
                 `\t x. --((gg:real->real^M->real^N) t x)`] BEL_JFAM_ADD) THEN
  ASM_SIMP_TAC[BEL_JFAM_NEG]);;

let BEL_JFAM_COMPONENT = prove
 (`!m U ff:real->real^M->real^N k.
        open U /\ bel_jfam m U ff ==> bel_jfam m U (\t x. lift(ff t x$k))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:num`; `U:real^M->bool`; `\x:real^N. lift(x$k)`;
                 `ff:real->real^M->real^N`] BEL_JFAM_LINEAR_O) THEN
  ASM_REWRITE_TAC[LINEAR_LIFT_COMPONENT; o_DEF]);;

let BEL_JFAM_VSUM = prove
 (`!m U n (ff:num->real->real^M->real^N).
        open U /\ (!j. j IN 1..n ==> bel_jfam m U (ff j))
        ==> bel_jfam m U (\t x. vsum(1..n) (\j. ff j t x))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[VSUM_CLAUSES_NUMSEG; ARITH] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`m:num`; `U:real^M->bool`; `\x:real^M. vec 0:real^N`] BEL_JFAM_CONST) THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[VSUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
  MATCH_MP_TAC BEL_JFAM_ADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `j IN 1..n` THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    REWRITE_TAC[ETA_AX] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC]);;



(* Composition of families.                                                   *)

let BEL_LINEAR_BASIS_EXPAND = prove
 (`!L:real^P->real^N v.
        linear L ==> L v = vsum(1..dimindex(:P)) (\j. v$j % L(basis j))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
  ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL]);;

let BEL_PD_COMPOSE_EXPAND = prove
 (`!i (f:real^P->real^N) (g:real^M->real^P) x.
        g differentiable at x /\ f differentiable at (g x)
        ==> partial_derivative i (f o g) x =
            vsum(1..dimindex(:P))
              (\j. drop(lift(partial_derivative i g x$j)) %
                   partial_derivative j f (g x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`i:num`; `g:real^M->real^P`; `f:real^P->real^N`; `x:real^M`]
                PARTIAL_DERIVATIVE_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[LIFT_DROP; partial_derivative] THEN
  MATCH_MP_TAC BEL_LINEAR_BASIS_EXPAND THEN REWRITE_TAC[ETA_AX] THEN
  UNDISCH_TAC `(f:real^P->real^N) differentiable at (g(x:real^M))` THEN
  REWRITE_TAC[FRECHET_DERIVATIVE_WORKS] THEN SIMP_TAC[has_derivative]);;

let BEL_JFAM_COMPOSE0 = prove
 (`!U V (ff:real->real^P->real^N) (gg:real->real^M->real^P).
        open U /\ open V /\ bel_jfam 0 V ff /\ bel_jfam 0 U gg /\
        (!t x. t IN real_interval[&0,&1] /\ x IN U ==> gg t x IN V)
        ==> bel_jfam 0 U (\t. ff t o gg t)`,
  REWRITE_TAC[BEL_JFAM_0] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `V:real^P->bool` THEN
    ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x:real^(M,1)finite_sum.
       ((ff:real->real^P->real^N) (drop(sndcart x)) o gg (drop(sndcart x))) (fstcart x)) =
    (\y:real^(P,1)finite_sum. ff (drop(sndcart y)) (fstcart y)) o
    (\x. pastecart ((gg:real->real^M->real^P) (drop(sndcart x)) (fstcart x)) (sndcart x))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART; ETA_AX];
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; BEL_IN_DOM; FSTCART_PASTECART;
                SNDCART_PASTECART] THEN
    ASM_SIMP_TAC[]]);;

let BEL_JFAM_COMPOSE = prove
 (`!m U V (ff:real->real^P->real^N) (gg:real->real^M->real^P).
        open U /\ open V /\ (!n. bel_jfam n V ff) /\ bel_jfam m U gg /\
        (!t x. t IN real_interval[&0,&1] /\ x IN U ==> gg t x IN V)
        ==> bel_jfam m U (\t. ff t o gg t)`,
  INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC BEL_JFAM_COMPOSE0 THEN
    EXISTS_TAC `V:real^P->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[BEL_JFAM_SUC] THEN CONJ_TAC THENL
   [MATCH_MP_TAC BEL_JFAM_COMPOSE0 THEN EXISTS_TAC `V:real^P->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC BEL_JFAM_MONO THEN EXISTS_TAC `SUC m` THEN
    ASM_REWRITE_TAC[LE_0];
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC BEL_JFAM_EQ THEN
  EXISTS_TAC
   `\t x. vsum(1..dimindex(:P))
            (\j. drop(lift(partial_derivative i ((gg:real->real^M->real^P) t) x$j)) %
                 ((\t. partial_derivative j ((ff:real->real^P->real^N) t) o gg t) t) x)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN REWRITE_TAC[o_THM] THEN
    MATCH_MP_TAC BEL_PD_COMPOSE_EXPAND THEN CONJ_TAC THEN
    MATCH_MP_TAC BEL_JFAM_DIFF THENL
     [MAP_EVERY EXISTS_TAC [`SUC m`; `U:real^M->bool`] THEN ASM_REWRITE_TAC[];
      MAP_EVERY EXISTS_TAC [`0`; `V:real^P->bool`] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC BEL_JFAM_VSUM THEN ASM_REWRITE_TAC[IN_NUMSEG] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC BEL_JFAM_MUL_DROP THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC BEL_JFAM_COMPONENT THEN ASM_SIMP_TAC[BEL_JFAM_PD; ETA_AX];
    REWRITE_TAC[ETA_AX] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `V:real^P->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC BEL_JFAM_PD THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC BEL_JFAM_MONO THEN EXISTS_TAC `SUC m` THEN ASM_REWRITE_TAC[] THEN
      ARITH_TAC]]);;

(* ========================================================================= *)
(* More family calculus (products, inverses, time-dependent                  *)
(* constants), uniform bounds, and the Cauchy transform, Neumann series and  *)
(* planar solution of a family of Beltrami coefficients.                     *)
(* ========================================================================= *)

let BEL_HOLOMORPHIC_SMOOTH = prove
 (`!f s. open s /\ f holomorphic_on s ==> smooth_map_on s f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smooth_map_on] THEN
  SUBGOAL_THEN
   `!n (g:complex->complex). g holomorphic_on s
         ==> continuously_differentiable n s g`
   (fun th -> ASM_MESON_TAC[th]) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0] THEN
    MESON_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON];
    ALL_TAC] THEN
  X_GEN_TAC `g:complex->complex` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN] THEN
  EXISTS_TAC `\x:complex h:complex. complex_derivative g x * h` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM has_complex_derivative] THEN
    REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE] THEN
    ASM_MESON_TAC[HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT];
    X_GEN_TAC `h:complex` THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN
    ASM_SIMP_TAC[ETA_AX; HOLOMORPHIC_COMPLEX_DERIVATIVE; HOLOMORPHIC_ON_CONST]]);;

let BEL_OPEN_NONZERO_C = prove
 (`open {z:complex | ~(z = Cx(&0))}`,
  REWRITE_TAC[SET_RULE `{z:complex | ~(z = a)} = (:complex) DELETE a`] THEN
  SIMP_TAC[OPEN_DELETE; OPEN_UNIV]);;

let BEL_JFAM_SMOOTH_O = prove
 (`!m U V (phi:real^P->real^N) (gg:real->real^M->real^P).
        open U /\ open V /\ smooth_map_on V phi /\ bel_jfam m U gg /\
        (!t x. t IN real_interval[&0,&1] /\ x IN U ==> gg t x IN V)
        ==> bel_jfam m U (\t. phi o gg t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:num`; `U:real^M->bool`; `V:real^P->bool`;
                 `\t:real. (phi:real^P->real^N)`; `gg:real->real^M->real^P`]
                BEL_JFAM_COMPOSE) THEN
  ASM_SIMP_TAC[BEL_JFAM_CONST]);;

let BEL_JFAM_CMUL_FUN = prove
 (`!m U (ff:real->real^M->complex) gg.
        open U /\ bel_jfam m U ff /\ bel_jfam m U gg
        ==> bel_jfam m U (\t x. ff t x * gg t x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BEL_JFAM_EQ THEN
  EXISTS_TAC `\t x. drop(lift((ff:real->real^M->complex) t x$1)) % gg t x +
                    drop(lift(ff t x$2)) % (\t. (\z. ii * z) o gg t) t x` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM; LIFT_DROP; COMPLEX_CMUL] THEN
    REWRITE_TAC[GSYM RE_DEF; GSYM IM_DEF] THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [COMPLEX_EXPAND] THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  MATCH_MP_TAC BEL_JFAM_ADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  MATCH_MP_TAC BEL_JFAM_MUL_DROP THEN ASM_SIMP_TAC[BEL_JFAM_COMPONENT; ETA_AX] THEN
  MATCH_MP_TAC BEL_JFAM_LINEAR_O THEN
  ASM_REWRITE_TAC[LINEAR_COMPLEX_MUL; REWRITE_RULE[ETA_AX] LINEAR_COMPLEX_MUL]);;

let BEL_JFAM_CINV = prove
 (`!m U (ff:real->real^M->complex).
        open U /\ bel_jfam m U ff /\
        (!t x. t IN real_interval[&0,&1] /\ x IN U ==> ~(ff t x = Cx(&0)))
        ==> bel_jfam m U (\t x. inv(ff t x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:num`; `U:real^M->bool`; `{z:complex | ~(z = Cx(&0))}`;
                 `inv:complex->complex`; `ff:real->real^M->complex`]
                BEL_JFAM_SMOOTH_O) THEN
  REWRITE_TAC[o_DEF; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[BEL_OPEN_NONZERO_C] THEN
  MATCH_MP_TAC BEL_HOLOMORPHIC_SMOOTH THEN REWRITE_TAC[BEL_OPEN_NONZERO_C] THEN
  MP_TAC(ISPECL [`\z:complex. z`; `{z:complex | ~(z = Cx(&0))}`] HOLOMORPHIC_ON_INV) THEN
  REWRITE_TAC[HOLOMORPHIC_ON_ID; IN_ELIM_THM; ETA_AX]);;

let BEL_JFAM_CNJ = prove
 (`!m U (ff:real->real^M->complex).
        open U /\ bel_jfam m U ff ==> bel_jfam m U (\t x. cnj(ff t x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:num`; `U:real^M->bool`; `cnj`; `ff:real->real^M->complex`]
                BEL_JFAM_LINEAR_O) THEN
  ASM_REWRITE_TAC[LINEAR_CNJ; o_DEF]);;

let BEL_JFAM_EVAL = prove
 (`!m U W (ff:real->real^M->real^N) z0.
        open W /\ z0 IN U /\ bel_jfam 0 U ff
        ==> bel_jfam m W (\t (x:real^P). ff t z0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BEL_JFAM_0] THEN STRIP_TAC THEN
  REWRITE_TAC[bel_jfam; SMOOTH_MAP_ON_CONST; BEL_ITERATED_PARTIAL_CONST] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `l:num list = []` THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
  SUBGOAL_THEN
   `(\x:real^(P,1)finite_sum. (ff:real->real^M->real^N) (drop(sndcart x)) z0) =
    (\y:real^(M,1)finite_sum. ff (drop(sndcart y)) (fstcart y)) o
    (\x. pastecart z0 (sndcart x))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
    SIMP_TAC[CONTINUOUS_ON_CONST; LINEAR_CONTINUOUS_ON; LINEAR_SNDCART; ETA_AX];
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; BEL_IN_DOM; FSTCART_PASTECART;
                SNDCART_PASTECART] THEN
    ASM_SIMP_TAC[]]);;

(* Compact parameter domains and uniform bounds.                              *)

let BEL_DOM_PCROSS = prove
 (`!U:real^M->bool. bel_dom U = U PCROSS interval[vec 0:real^1,vec 1]`,
  GEN_TAC THEN REWRITE_TAC[EXTENSION; BEL_IN_DOM] THEN
  X_GEN_TAC `x:real^(M,1)finite_sum` THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [GSYM PASTECART_FST_SND] THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; IN_REAL_INTERVAL; DROP_VEC]);;

let BEL_DOM_COMPACT = prove
 (`!U:real^M->bool. compact U ==> compact(bel_dom U)`,
  SIMP_TAC[BEL_DOM_PCROSS; COMPACT_PCROSS; COMPACT_INTERVAL]);;

let BEL_JFAM_BOUND0 = prove
 (`!rho (ff:real->complex->complex).
        (\x. ff (drop(sndcart x)) (fstcart x)) continuous_on bel_dom (:complex) /\
        (!t. t IN real_interval[&0,&1] ==> bel_supp rho (ff t))
        ==> ?M. !t z. t IN real_interval[&0,&1] ==> norm(ff t z) <= M`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^(2,1)finite_sum.
                   (ff:real->complex->complex) (drop(sndcart x)) (fstcart x)`;
                 `bel_dom(cball(vec 0:complex,rho))`] COMPACT_CONTINUOUS_IMAGE) THEN
  ANTS_TAC THENL
   [SIMP_TAC[BEL_DOM_COMPACT; COMPACT_CBALL] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET; BEL_IN_DOM; IN_UNIV] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; BEL_IN_DOM; IN_CBALL_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `b:real` THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `norm(z:complex) <= rho` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (z:complex) (lift t)`) THEN
    ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
    SUBGOAL_THEN `(ff:real->complex->complex) t z = Cx(&0)` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[bel_supp] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[COMPLEX_NORM_0] THEN ASM_REAL_ARITH_TAC]]);;

let BEL_JFAM_BOUND = prove
 (`!m rho (ff:real->complex->complex).
        bel_jfam m (:complex) ff /\
        (!t. t IN real_interval[&0,&1] ==> bel_supp rho (ff t))
        ==> ?M. !t l z. t IN real_interval[&0,&1] /\ LENGTH l <= m /\
                        ALL (\i. i = 1 \/ i = 2) l
                        ==> norm(iterated_partial l (ff t) z) <= M`,
  INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[BEL_JFAM_0; LE; LENGTH_EQ_NIL] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`rho:real`; `ff:real->complex->complex`] BEL_JFAM_BOUND0) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    SIMP_TAC[iterated_partial];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN SIMP_TAC[BEL_JFAM_SUC; OPEN_UNIV; DIMINDEX_2] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rho:real`; `ff:real->complex->complex`] BEL_JFAM_BOUND0) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[BEL_JFAM_0]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `M0:real` (LABEL_TAC "M0")) THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> ?M. !t l z. t IN real_interval[&0,&1] /\ LENGTH l <= m /\
                        ALL (\i. i = 1 \/ i = 2) l
                        ==> norm(iterated_partial l
                              (partial_derivative i ((ff:real->complex->complex) t)) z) <= M`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `rho:real` THEN
    ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC BEL_SUPP_PD THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[BEL_JFAM_0];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th)) THEN
  REWRITE_TAC[ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `M2:real` (LABEL_TAC "M2")) THEN
  DISCH_THEN(X_CHOOSE_THEN `M1:real` (LABEL_TAC "M1")) THEN
  EXISTS_TAC `abs M0 + abs M1 + abs M2` THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `l:num list`; `z:complex`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `l:num list = []` THENL
   [ASM_REWRITE_TAC[iterated_partial] THEN
    REMOVE_THEN "M0" (MP_TAC o SPECL [`t:real`; `z:complex`]) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `l':num list` (X_CHOOSE_THEN `j:num` SUBST_ALL_TAC) o
                MATCH_MP BEL_LIST_SNOC) THEN
  SUBGOAL_THEN `LENGTH(l':num list) <= m /\ ALL (\i. i = 1 \/ i = 2) l' /\ (j = 1 \/ j = 2)`
  MP_TAC THENL
   [UNDISCH_TAC `LENGTH(APPEND l' [j:num]) <= SUC m` THEN
    UNDISCH_TAC `ALL (\i. i = 1 \/ i = 2) (APPEND l' [j:num])` THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH; ALL_APPEND; ALL] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM BEL_PD_ITERATED_APPEND] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (DISJ_CASES_THEN SUBST_ALL_TAC))) THENL
   [REMOVE_THEN "M1" (MP_TAC o SPECL [`t:real`; `l':num list`; `z:complex`]);
    REMOVE_THEN "M2" (MP_TAC o SPECL [`t:real`; `l':num list`; `z:complex`])] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let BEL_UNIF_PARAM = prove
 (`!rho (hh:real->complex->complex) e.
        (\x. hh (drop(sndcart x)) (fstcart x)) continuous_on bel_dom (:complex) /\
        (!t. t IN real_interval[&0,&1] ==> bel_supp rho (hh t)) /\ &0 < e
        ==> ?d. &0 < d /\
                !t t' w. t IN real_interval[&0,&1] /\ t' IN real_interval[&0,&1] /\
                         abs(t' - t) < d
                         ==> norm(hh t' w - hh t w) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^(2,1)finite_sum.
                   (hh:real->complex->complex) (drop(sndcart x)) (fstcart x)`;
                 `bel_dom(cball(vec 0:complex,rho))`] COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ANTS_TAC THENL
   [SIMP_TAC[BEL_DOM_COMPACT; COMPACT_CBALL] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET; BEL_IN_DOM; IN_UNIV] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `norm(w:complex) <= rho` THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`pastecart (w:complex) (lift t)`;
                                  `pastecart (w:complex) (lift t')`]) THEN
    ASM_REWRITE_TAC[BEL_IN_DOM; IN_CBALL_0; FSTCART_PASTECART; SNDCART_PASTECART;
                    LIFT_DROP; DIST_PASTECART_CANCEL; DIST_LIFT] THEN
    REWRITE_TAC[dist];
    SUBGOAL_THEN `(hh:real->complex->complex) t w = Cx(&0) /\ hh t' w = Cx(&0)`
     (fun th -> ASM_REWRITE_TAC[th; COMPLEX_SUB_REFL; COMPLEX_NORM_0]) THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `t:real`); FIRST_X_ASSUM(MP_TAC o SPEC `t':real`)] THEN
    ASM_REWRITE_TAC[bel_supp] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

(* The Cauchy transform of a family with a common compact support.           *)

let BEL_JFAM_CT0 = prove
 (`!rho (hh:real->complex->complex).
        bel_jfam 0 (:complex) hh /\
        (!t. t IN real_interval[&0,&1] ==> bel_supp rho (hh t))
        ==> bel_jfam 0 (:complex) (\t. bel_ct (hh t))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BEL_JFAM_0] THEN STRIP_TAC THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC BEL_CT_SMOOTH THEN EXISTS_TAC `rho:real` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `rho:real` BEL_CT_BOUND) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[continuous_on; BEL_IN_DOM; IN_UNIV] THEN
  X_GEN_TAC `x:real^(2,1)finite_sum` THEN STRIP_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < e / &2 / (C + &1)` ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rho:real`; `hh:real->complex->complex`; `e / &2 / (C + &1)`]
                BEL_UNIF_PARAM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "U"))) THEN
  SUBGOAL_THEN `(bel_ct ((hh:real->complex->complex) (drop(sndcart(x:real^(2,1)finite_sum)))))
                continuous_on (:complex)`
  MP_TAC THENL
   [MATCH_MP_TAC BEL_CT_CONTINUOUS THEN EXISTS_TAC `rho:real` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_on; IN_UNIV] THEN
  DISCH_THEN(MP_TAC o SPECL [`fstcart(x:real^(2,1)finite_sum)`; `e / &2`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "V"))) THEN
  EXISTS_TAC `min d1 d2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `y:real^(2,1)finite_sum` THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs(drop(sndcart(y:real^(2,1)finite_sum)) - drop(sndcart(x:real^(2,1)finite_sum)))
                < d1 /\ dist(fstcart y,fstcart x) < d2`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[dist; GSYM DROP_SUB; GSYM NORM_1; GSYM FSTCART_SUB; GSYM SNDCART_SUB] THEN
    MP_TAC(ISPEC `y - x:real^(2,1)finite_sum` NORM_FSTCART) THEN
    MP_TAC(ISPEC `y - x:real^(2,1)finite_sum` NORM_SNDCART) THEN
    UNDISCH_TAC `dist(y:real^(2,1)finite_sum,x) < d1` THEN
    UNDISCH_TAC `dist(y:real^(2,1)finite_sum,x) < d2` THEN
    REWRITE_TAC[dist] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `s = drop(sndcart(y:real^(2,1)finite_sum))` THEN
  ABBREV_TAC `t = drop(sndcart(x:real^(2,1)finite_sum))` THEN
  SUBGOAL_THEN
   `norm(bel_ct ((hh:real->complex->complex) s) (fstcart(y:real^(2,1)finite_sum)) -
         bel_ct (hh t) (fstcart y)) <= C * (e / &2 / (C + &1))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`rho:real`; `(hh:real->complex->complex) s`; `(hh:real->complex->complex) t`;
                   `fstcart(y:real^(2,1)finite_sum)`] BEL_CT_SUB) THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; CONTINUOUS_ON_SUB; ETA_AX;
                 BEL_SUPP_SUB] THEN
    GEN_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN REMOVE_THEN "U" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `C * (e / &2 / (C + &1)) < e / &2` ASSUME_TAC THENL
   [SUBGOAL_THEN `C * (e / &2 / (C + &1)) = (e / &2) * (C / (C + &1))` SUBST1_TAC THENL
     [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `x * y < x * &1 ==> x * y < x`) THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 <= C ==> &0 < C + &1`] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REMOVE_THEN "V" (MP_TAC o SPEC `fstcart(y:real^(2,1)finite_sum)`) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `norm(bel_ct ((hh:real->complex->complex) s) (fstcart(y:real^(2,1)finite_sum)) -
                    bel_ct (hh t) (fstcart y)) <= C * (e / &2 / (C + &1))` THEN
  UNDISCH_TAC `C * (e / &2 / (C + &1)) < e / &2` THEN
  REWRITE_TAC[dist] THEN CONV_TAC NORM_ARITH);;

let BEL_JFAM_CT = prove
 (`!m rho (hh:real->complex->complex).
        bel_jfam m (:complex) hh /\
        (!t. t IN real_interval[&0,&1] ==> bel_supp rho (hh t))
        ==> bel_jfam m (:complex) (\t. bel_ct (hh t))`,
  INDUCT_TAC THENL [REWRITE_TAC[BEL_JFAM_CT0]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN SIMP_TAC[BEL_JFAM_SUC; OPEN_UNIV] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC BEL_JFAM_CT0 THEN EXISTS_TAC `rho:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC BEL_JFAM_EQ THEN
  EXISTS_TAC `\t. bel_ct (partial_derivative i ((hh:real->complex->complex) t))` THEN
  REWRITE_TAC[OPEN_UNIV] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN AP_THM_TAC THEN
    MATCH_MP_TAC BEL_CT_PARTIAL THEN EXISTS_TAC `rho:real` THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[BEL_JFAM_0];
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `rho:real` THEN ASM_SIMP_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC BEL_SUPP_PD THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[BEL_JFAM_0]]);;

(* The Beurling transform and the Neumann series of a family.                 *)

let BEL_DIM2_PRED = prove
 (`(\i. 1 <= i /\ i <= dimindex(:2)) = (\i. i = 1 \/ i = 2)`,
  REWRITE_TAC[FUN_EQ_THM; DIMINDEX_2] THEN ARITH_TAC);;

let BEL_JFAM_WDZ = prove
 (`!m (hh:real->complex->complex).
        bel_jfam (SUC m) (:complex) hh
        ==> bel_jfam m (:complex) (\t. wirtinger_dz (hh t))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BEL_JFAM_EQ THEN
  EXISTS_TAC `\t w. (\t. (\z. inv(Cx(&2)) * z) o
                         partial_derivative 1 ((hh:real->complex->complex) t)) t w +
                    (\t. (\z. (--ii * inv(Cx(&2))) * z) o
                         partial_derivative 2 (hh t)) t w` THEN
  REWRITE_TAC[OPEN_UNIV] THEN CONJ_TAC THENL
   [REWRITE_TAC[BEL_WIRTINGER_FUN; partial_derivative; COMPLEX_BASIS; o_THM];
    ALL_TAC] THEN
  MATCH_MP_TAC BEL_JFAM_ADD THEN REWRITE_TAC[OPEN_UNIV] THEN CONJ_TAC THEN
  REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC BEL_JFAM_LINEAR_O THEN
  REWRITE_TAC[OPEN_UNIV; LINEAR_COMPLEX_MUL; REWRITE_RULE[ETA_AX] LINEAR_COMPLEX_MUL] THEN
  MATCH_MP_TAC BEL_JFAM_PD THEN ASM_REWRITE_TAC[OPEN_UNIV; DIMINDEX_2; ARITH]);;

let BEL_JFAM_S = prove
 (`!m rho (hh:real->complex->complex).
        bel_jfam (SUC m) (:complex) hh /\
        (!t. t IN real_interval[&0,&1] ==> bel_supp rho (hh t))
        ==> bel_jfam m (:complex) (\t. bel_s (hh t))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bel_s] THEN MATCH_MP_TAC BEL_JFAM_CT THEN
  EXISTS_TAC `rho:real` THEN ASM_SIMP_TAC[BEL_JFAM_WDZ] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`rho:real`; `(hh:real->complex->complex) t`] BEL_SUPP_WIRTINGER) THEN
  ASM_SIMP_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  MATCH_MP_TAC BEL_SMOOTH_C1 THEN ASM_MESON_TAC[BEL_JFAM_SMOOTH]);;

let BEL_JFAM_UE = prove
 (`!n mu e:real->complex->complex rho.
        (!m. bel_jfam m (:complex) mu) /\ (!m. bel_jfam m (:complex) e) /\
        (!t. t IN real_interval[&0,&1] ==> bel_supp rho (mu t) /\ bel_supp rho (e t))
        ==> !m. bel_jfam m (:complex) (\t. bel_ue (mu t) (e t) n)`,
  INDUCT_TAC THENL [SIMP_TAC[bel_ue; ETA_AX]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN REWRITE_TAC[bel_ue; bel_tt] THEN
  MATCH_MP_TAC BEL_JFAM_CMUL_FUN THEN ASM_REWRITE_TAC[OPEN_UNIV] THEN
  REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC BEL_JFAM_S THEN EXISTS_TAC `rho:real` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`mu:real->complex->complex`; `e:real->complex->complex`;
                                  `rho:real`]) THEN
    ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`rho:real`; `(mu:real->complex->complex) t`; `(e:real->complex->complex) t`;
                   `n:num`] BEL_UE_SMOOTH) THEN
    ASM_SIMP_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_MESON_TAC[BEL_JFAM_SMOOTH]]);;

let BEL_SERIES_CONT_ON = prove
 (`!uu:num->real^M->real^N a B s.
        (!n. &0 <= a n) /\ (!N. sum(0..N) a <= B) /\
        (!n z. z IN s ==> norm(uu n z) <= a n) /\
        (!n. (uu n) continuous_on s)
        ==> (\z. infsum (from 0) (\n. uu n z)) continuous_on s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\n z. if z IN s then (uu:num->real^M->real^N) n z else vec 0`;
                 `a:num->real`; `B:real`; `s:real^M->bool`] BEL_SERIES_CONT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[NORM_0];
      GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
      EXISTS_TAC `(uu:num->real^M->real^N) n` THEN ASM_SIMP_TAC[]];
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_EQ) THEN
    SIMP_TAC[]]);;

let BEL_GEOM_SUM = prove
 (`!B r N. &0 <= B /\ &1 < r ==> sum(0..N) (\n. B / r pow n) <= B * r / (r - &1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < inv r /\ inv r < &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. B / r pow n = B * inv r pow n` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[real_div; REAL_POW_INV]; ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL] THEN
  SUBGOAL_THEN `B * r / (r - &1) = B * inv(&1 - inv r)` SUBST1_TAC THENL
   [MATCH_MP_TAC(REAL_FIELD `~(r = &0) /\ ~(r - &1 = &0)
                             ==> B * r / (r - &1) = B * inv(&1 - inv r)`) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[SUM_GP; LT] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NE; CONJUNCT1 real_pow] THEN
  REWRITE_TAC[real_div] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= b * i ==> (&1 - b) * i <= i`) THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC]);;

let BEL_JFAM_NSOL = prove
 (`!mu e:real->complex->complex rho k.
        (!m. bel_jfam m (:complex) mu) /\ (!m. bel_jfam m (:complex) e) /\
        (!t. t IN real_interval[&0,&1] ==> bel_supp rho (mu t) /\ bel_supp rho (e t)) /\
        (!t z. t IN real_interval[&0,&1] ==> norm(mu t z) <= k) /\ k < &1
        ==> !m. bel_jfam m (:complex) (\t. bel_nsol (mu t) (e t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  SUBGOAL_THEN `&0 <= k` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm((mu:real->complex->complex) (&0) (Cx(&0)))` THEN
    REWRITE_TAC[NORM_POS_LE] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t IN real_interval[&0,&1]
        ==> smooth_map_on (:complex) ((mu:real->complex->complex) t) /\
            smooth_map_on (:complex) ((e:real->complex->complex) t)`
  ASSUME_TAC THENL [ASM_MESON_TAC[BEL_JFAM_SMOOTH]; ALL_TAC] THEN
  REWRITE_TAC[bel_jfam] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC BEL_NSOL_SMOOTH THEN
    MAP_EVERY EXISTS_TAC [`rho:real`; `k:real`] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `l:num list` THEN REWRITE_TAC[BEL_DIM2_PRED] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?r. &1 < r /\ r * k < &1` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `&2 / (&1 + k)` THEN
    SUBGOAL_THEN `&0 < &1 + k` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `&2 / (&1 + k) * k = (&2 * k) / (&1 + k)`] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_LDIV_EQ] THEN
    UNDISCH_TAC `k < &1` THEN UNDISCH_TAC `&0 <= k` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`2 + LENGTH(l:num list)`; `rho:real`; `mu:real->complex->complex`]
                BEL_JFAM_BOUND) THEN
  MP_TAC(ISPECL [`2 + LENGTH(l:num list)`; `rho:real`; `e:real->complex->complex`]
                BEL_JFAM_BOUND) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M2:real` (LABEL_TAC "M2")) THEN
  DISCH_THEN(X_CHOOSE_THEN `M1:real` (LABEL_TAC "M1")) THEN
  MP_TAC(ISPECL [`l:num list`; `max M1 M2`; `k:real`; `r:real`; `rho:real`]
                BEL_UE_GEOM_BOUND) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` (LABEL_TAC "B")) THEN
  SUBGOAL_THEN
   `!t l' z. t IN real_interval[&0,&1] /\ LENGTH l' <= 2 + LENGTH(l:num list) /\
             ALL (\i. i = 1 \/ i = 2) l'
             ==> norm(iterated_partial l' ((mu:real->complex->complex) t) z) <= max M1 M2 /\
                 norm(iterated_partial l' ((e:real->complex->complex) t) z) <= max M1 M2`
  (LABEL_TAC "MM") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `x <= a ==> x <= max a b`) THEN
      USE_THEN "M1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(REAL_ARITH `x <= b ==> x <= max a b`) THEN
      USE_THEN "M2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t n z. t IN real_interval[&0,&1]
            ==> norm(iterated_partial l
                  (bel_ue ((mu:real->complex->complex) t) ((e:real->complex->complex) t) n) z)
                <= abs B / r pow n`
  (LABEL_TAC "G") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B / r pow n` THEN
    CONJ_TAC THENL
     [REMOVE_THEN "B" (MP_TAC o SPECL [`(mu:real->complex->complex) t`;
                                        `(e:real->complex->complex) t`]) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
        USE_THEN "MM" (MP_TAC o SPECL [`t:real`; `l':num list`; `z:complex`]) THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]);
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      REWRITE_TAC[REAL_ABS_LE] THEN MATCH_MP_TAC REAL_LE_INV THEN
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC
   `\x. infsum (from 0)
          (\n. iterated_partial l
                 (bel_ue ((mu:real->complex->complex) (drop(sndcart x)))
                         ((e:real->complex->complex) (drop(sndcart x))) n)
                 (fstcart x))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BEL_IN_DOM] THEN X_GEN_TAC `x:real^(2,1)finite_sum` THEN STRIP_TAC THEN
    REWRITE_TAC[bel_nsol] THEN
    MP_TAC(ISPECL [`l:num list`;
                   `bel_ue ((mu:real->complex->complex) (drop(sndcart(x:real^(2,1)finite_sum))))
                           ((e:real->complex->complex) (drop(sndcart x)))`]
                  BEL_SERIES_ITERATED) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC BEL_UE_SUMBD THEN
      MAP_EVERY EXISTS_TAC [`rho:real`; `k:real`] THEN ASM_SIMP_TAC[];
      DISCH_THEN(fun th -> REWRITE_TAC[th])];
    ALL_TAC] THEN
  MATCH_MP_TAC BEL_SERIES_CONT_ON THEN
  MAP_EVERY EXISTS_TAC [`\n. abs B / r pow n`; `abs B * r / (r - &1)`] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    GEN_TAC THEN MATCH_MP_TAC BEL_GEOM_SUM THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    REWRITE_TAC[BEL_IN_DOM] THEN REPEAT STRIP_TAC THEN
    REMOVE_THEN "G" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN
    MP_TAC(ISPECL [`n:num`; `mu:real->complex->complex`; `e:real->complex->complex`;
                   `rho:real`] BEL_JFAM_UE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `LENGTH(l:num list)`) THEN
    REWRITE_TAC[bel_jfam; BEL_DIM2_PRED] THEN
    DISCH_THEN(MP_TAC o SPEC `l:num list` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[LE_REFL]]);;

let BEL_JFAM_FSOL = prove
 (`!mu:real->complex->complex rho k.
        (!m. bel_jfam m (:complex) mu) /\
        (!t. t IN real_interval[&0,&1] ==> bel_supp rho (mu t)) /\
        (!t z. t IN real_interval[&0,&1] ==> norm(mu t z) <= k) /\ k < &1
        ==> !m. bel_jfam m (:complex) (\t. bel_fsol (mu t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN REWRITE_TAC[bel_fsol] THEN
  MATCH_MP_TAC BEL_JFAM_ADD THEN REWRITE_TAC[OPEN_UNIV] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`m:num`; `(:complex)`; `\z:complex. z`] BEL_JFAM_CONST) THEN
    REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID];
    ALL_TAC] THEN
  REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC BEL_JFAM_CT THEN EXISTS_TAC `rho:real` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`mu:real->complex->complex`; `mu:real->complex->complex`;
                   `rho:real`; `k:real`] BEL_JFAM_NSOL) THEN
    ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC BEL_NSOL_SUPP THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[BEL_JFAM_SMOOTH]]);;

let BEL_FSOL_UNIF_BOUND = prove
 (`!mu:real->complex->complex rho k.
        (!m. bel_jfam m (:complex) mu) /\
        (!t. t IN real_interval[&0,&1] ==> bel_supp rho (mu t)) /\
        (!t z. t IN real_interval[&0,&1] ==> norm(mu t z) <= k) /\ k < &1
        ==> ?C. !t z. t IN real_interval[&0,&1] ==> norm(bel_fsol (mu t) z - z) <= C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. t IN real_interval[&0,&1]
        ==> smooth_map_on (:complex) ((mu:real->complex->complex) t) /\
            smooth_map_on (:complex) (bel_nsol (mu t) (mu t)) /\
            bel_supp rho (bel_nsol (mu t) (mu t))`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `smooth_map_on (:complex) ((mu:real->complex->complex) t)` ASSUME_TAC THENL
     [ASM_MESON_TAC[BEL_JFAM_SMOOTH]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC BEL_NSOL_SMOOTH THEN MAP_EVERY EXISTS_TAC [`rho:real`; `k:real`] THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC BEL_NSOL_SUPP THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`0`; `rho:real`; `\t. bel_nsol ((mu:real->complex->complex) t) (mu t)`]
                BEL_JFAM_BOUND) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`mu:real->complex->complex`; `mu:real->complex->complex`;
                   `rho:real`; `k:real`] BEL_JFAM_NSOL) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` (MP_TAC o GEN `t:real` o GEN `z:complex` o
    SPECL [`t:real`; `[]:num list`; `z:complex`])) THEN
  REWRITE_TAC[LENGTH; LE_REFL; ALL; iterated_partial] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `rho:real` BEL_CT_BOUND) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `C * M` THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[bel_fsol; COMPLEX_ADD_SUB] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS]);;


(* ========================================================================= *)
(* Inverses of families of diffeomorphisms of the plane, and                 *)
(* local-to-global continuity on parameter domains.                          *)
(* ========================================================================= *)

let BEL_HOMEO_INV_SMOOTH = prove
 (`!f g:real^N->real^N.
        smooth_map_on (:real^N) f /\ homeomorphism ((:real^N),(:real^N)) (f,g) /\
        (!z. ~(det(matrix(frechet_derivative f (at z))) = &0))
        ==> smooth_map_on (:real^N) g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HOMEOMORPHISM; IN_UNIV] THEN STRIP_TAC THEN
  REWRITE_TAC[smooth_map_on] THEN X_GEN_TAC `n:num` THEN
  MP_TAC(ISPECL [`n:num`; `(:real^N)`; `g:real^N->real^N`]
                CONTINUOUSLY_DIFFERENTIABLE_LOCAL_OPEN) THEN
  REWRITE_TAC[OPEN_UNIV; IN_UNIV; SUBSET_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  X_GEN_TAC `y:real^N` THEN
  MP_TAC(ISPECL [`f:real^N->real^N`; `(:real^N)`; `(g:real^N->real^N) y`]
                SMOOTH_INVERSE_FUNCTION_THEOREM) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; diffeomorphism_on] THEN
  MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `u:real^N->bool`; `g0:real^N->real^N`] THEN
  STRIP_TAC THEN EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_EQ_OPEN THEN
  EXISTS_TAC `g0:real^N->real^N` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(g:real^N->real^N) w = g ((f:real^N->real^N) ((g0:real^N->real^N) w))`
    SUBST1_TAC THENL
     [AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[]];
    ASM_MESON_TAC[smooth_map_on]]);;

let BEL_DOM_OPEN_IN = prove
 (`!U V:real^M->bool.
        open V ==> open_in (subtopology euclidean (bel_dom U)) (bel_dom (U INTER V))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `bel_dom (U INTER V) =
                bel_dom U INTER (V PCROSS (:real^1)):real^(M,1)finite_sum->bool`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; BEL_IN_DOM] THEN
    X_GEN_TAC `x:real^(M,1)finite_sum` THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV) [GSYM PASTECART_FST_SND] THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV] THEN CONV_TAC TAUT;
    MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN MATCH_MP_TAC OPEN_PCROSS THEN
    ASM_REWRITE_TAC[OPEN_UNIV]]);;

let BEL_CONT_LOCAL = prove
 (`!(f:real^(M,1)finite_sum->real^N) U.
        (!x. x IN bel_dom U
             ==> ?V. open V /\ fstcart x IN V /\ f continuous_on bel_dom (U INTER V))
        ==> f continuous_on bel_dom U`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  X_GEN_TAC `x:real^(M,1)finite_sum` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^(M,1)finite_sum`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^M->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:real^(M,1)finite_sum) IN bel_dom (U INTER V)` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^(M,1)finite_sum) IN bel_dom U` THEN
    ASM_REWRITE_TAC[BEL_IN_DOM; IN_INTER] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^(M,1)finite_sum->real^N`; `x:real^(M,1)finite_sum`;
                 `bel_dom (U:real^M->bool)`; `bel_dom (U INTER V:real^M->bool)`]
                CONTINUOUS_WITHIN_OPEN_IN) THEN
  ASM_SIMP_TAC[BEL_DOM_OPEN_IN] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  UNDISCH_TAC `(f:real^(M,1)finite_sum->real^N) continuous_on bel_dom (U INTER V)` THEN
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let BEL_INV_CONT = prove
 (`!ff kk:real->complex->complex C0.
        (\x. ff (drop(sndcart x)) (fstcart x)) continuous_on bel_dom (:complex) /\
        (!t. t IN real_interval[&0,&1]
             ==> homeomorphism ((:complex),(:complex)) (ff t,kk t)) /\
        (!t z. t IN real_interval[&0,&1] ==> norm(ff t z - z) <= C0)
        ==> (\x. kk (drop(sndcart x)) (fstcart x)) continuous_on bel_dom (:complex)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fcont")
    (CONJUNCTS_THEN2 (LABEL_TAC "homeo") (LABEL_TAC "C0"))) THEN
  MATCH_MP_TAC BEL_CONT_LOCAL THEN
  X_GEN_TAC `x0:real^(2,1)finite_sum` THEN DISCH_TAC THEN
  ABBREV_TAC `r = norm(fstcart(x0:real^(2,1)finite_sum)) + &1` THEN
  EXISTS_TAC `ball(vec 0:complex,r)` THEN REWRITE_TAC[OPEN_BALL; IN_BALL_0] THEN
  CONJ_TAC THENL [EXPAND_TAC "r" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `bel_dom(cball(vec 0:complex,r))` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; BEL_IN_DOM; IN_INTER; IN_UNIV; IN_BALL_0; IN_CBALL_0] THEN
    SIMP_TAC[REAL_LT_IMP_LE]] THEN
  ABBREV_TAC `S = bel_dom(cball(vec 0:complex,r + abs C0))` THEN
  ABBREV_TAC `Phi = \x:real^(2,1)finite_sum.
                       pastecart ((ff:real->complex->complex) (drop(sndcart x)) (fstcart x))
                                 (sndcart x)` THEN
  MP_TAC(ISPECL [`S:real^(2,1)finite_sum->bool`;
                 `Phi:real^(2,1)finite_sum->real^(2,1)finite_sum`;
                 `IMAGE (Phi:real^(2,1)finite_sum->real^(2,1)finite_sum) S`]
                HOMEOMORPHISM_COMPACT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "S" THEN SIMP_TAC[BEL_DOM_COMPACT; COMPACT_CBALL];
      EXPAND_TAC "Phi" THEN MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART; ETA_AX] THEN
      USE_THEN "fcont" (MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET)) THEN
      EXPAND_TAC "S" THEN REWRITE_TAC[SUBSET; BEL_IN_DOM; IN_UNIV] THEN SIMP_TAC[];
      REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`x:real^(2,1)finite_sum`; `y:real^(2,1)finite_sum`] THEN
      EXPAND_TAC "S" THEN EXPAND_TAC "Phi" THEN
      REWRITE_TAC[BEL_IN_DOM; PASTECART_INJ] THEN STRIP_TAC THEN
      ONCE_REWRITE_TAC[PASTECART_EQ] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(ff:real->complex->complex) (drop(sndcart(x:real^(2,1)finite_sum)))
                     (fstcart x) = ff (drop(sndcart(y:real^(2,1)finite_sum))) (fstcart y)` THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o AP_TERM
        `(kk:real->complex->complex) (drop(sndcart(y:real^(2,1)finite_sum)))`) THEN
      USE_THEN "homeo" (fun th -> MP_TAC(MATCH_MP th
        (ASSUME `drop(sndcart(y:real^(2,1)finite_sum)) IN real_interval[&0,&1]`))) THEN
      REWRITE_TAC[homeomorphism; IN_UNIV] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^(2,1)finite_sum->real^(2,1)finite_sum` MP_TAC) THEN
  REWRITE_TAC[homeomorphism] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "gPhi")
    (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "Phig") (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "gcont"))))) THEN
  SUBGOAL_THEN
   `!y:real^(2,1)finite_sum. y IN bel_dom(cball(vec 0:complex,r))
        ==> pastecart ((kk:real->complex->complex) (drop(sndcart y)) (fstcart y)) (sndcart y)
              IN S /\
            (Phi:real^(2,1)finite_sum->real^(2,1)finite_sum)
              (pastecart (kk (drop(sndcart y)) (fstcart y)) (sndcart y)) = y`
  (LABEL_TAC "pre") THENL
   [X_GEN_TAC `y:real^(2,1)finite_sum` THEN REWRITE_TAC[BEL_IN_DOM; IN_CBALL_0] THEN
    STRIP_TAC THEN
    USE_THEN "homeo" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `drop(sndcart(y:real^(2,1)finite_sum)) IN real_interval[&0,&1]`))) THEN
    REWRITE_TAC[homeomorphism; IN_UNIV] THEN STRIP_TAC THEN
    REMOVE_THEN "C0" (MP_TAC o SPECL [`drop(sndcart(y:real^(2,1)finite_sum))`;
        `(kk:real->complex->complex) (drop(sndcart(y:real^(2,1)finite_sum))) (fstcart y)`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    EXPAND_TAC "S" THEN EXPAND_TAC "Phi" THEN
    REWRITE_TAC[BEL_IN_DOM; IN_CBALL_0; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(NORM_ARITH `!a b:complex r C. norm a <= r /\ norm(a - b) <= C
                                                 ==> norm b <= r + abs C`) THEN
      EXISTS_TAC `fstcart(y:real^(2,1)finite_sum)` THEN ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[PASTECART_EQ] THEN
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART]];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `fstcart o (g:real^(2,1)finite_sum->real^(2,1)finite_sum)` THEN CONJ_TAC THENL
   [X_GEN_TAC `y:real^(2,1)finite_sum` THEN DISCH_TAC THEN
    USE_THEN "pre" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `(y:real^(2,1)finite_sum) IN bel_dom(cball(vec 0:complex,r))`))) THEN
    ABBREV_TAC `p = pastecart ((kk:real->complex->complex)
                      (drop(sndcart(y:real^(2,1)finite_sum))) (fstcart y)) (sndcart y)` THEN
    STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(g:real^(2,1)finite_sum->real^(2,1)finite_sum) y = p` SUBST1_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `(g:real^(2,1)finite_sum->real^(2,1)finite_sum)
                    ((Phi:real^(2,1)finite_sum->real^(2,1)finite_sum) p)` THEN
      CONJ_TAC THENL
       [AP_TERM_TAC THEN ASM_REWRITE_TAC[];
        USE_THEN "gPhi" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      EXPAND_TAC "p" THEN REWRITE_TAC[FSTCART_PASTECART]];
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (Phi:real^(2,1)finite_sum->real^(2,1)finite_sum) S` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_IMAGE] THEN
    X_GEN_TAC `y:real^(2,1)finite_sum` THEN DISCH_TAC THEN
    EXISTS_TAC `pastecart ((kk:real->complex->complex)
                  (drop(sndcart(y:real^(2,1)finite_sum))) (fstcart y)) (sndcart y)` THEN
    USE_THEN "pre" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `(y:real^(2,1)finite_sum) IN bel_dom(cball(vec 0:complex,r))`))) THEN
    SIMP_TAC[]]);;

(* The derivative of the inverse, in complex notation.                        *)

let BEL_SOLVE_RLIN = prove
 (`!a b h v:complex.
        a * h + b * cnj h = v /\ ~(a * cnj a - b * cnj b = Cx(&0))
        ==> h = (cnj a * v - b * cnj v) * inv(a * cnj a - b * cnj b)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
  REWRITE_TAC[CNJ_ADD; CNJ_MUL; CNJ_CNJ] THEN
  UNDISCH_TAC `~(a * cnj a - b * cnj b = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD);;

let BEL_DET_CX = prove
 (`!f:complex->complex z.
        Cx(det(matrix(frechet_derivative f (at z)))) =
        wirtinger_dz f z * cnj(wirtinger_dz f z) - wirtinger_dbar f z * cnj(wirtinger_dbar f z)`,
  REWRITE_TAC[BEL_DET_WIRT; CX_SUB; CX_POW; COMPLEX_NORM_POW_2]);;

let BEL_INV_PARTIAL = prove
 (`!f g:complex->complex w.
        smooth_map_on (:complex) f /\ smooth_map_on (:complex) g /\
        (!w. f(g w) = w) /\ ~(det(matrix(frechet_derivative f (at (g w)))) = &0)
        ==> partial_derivative 1 g w =
              (cnj(wirtinger_dz f (g w)) - wirtinger_dbar f (g w)) *
              inv(wirtinger_dz f (g w) * cnj(wirtinger_dz f (g w)) -
                  wirtinger_dbar f (g w) * cnj(wirtinger_dbar f (g w))) /\
            partial_derivative 2 g w =
              ii * (cnj(wirtinger_dz f (g w)) + wirtinger_dbar f (g w)) *
              inv(wirtinger_dz f (g w) * cnj(wirtinger_dz f (g w)) -
                  wirtinger_dbar f (g w) * cnj(wirtinger_dbar f (g w)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(f:complex->complex) differentiable at ((g:complex->complex) w) /\
                g differentiable at w` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(:complex)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  ABBREV_TAC `a = wirtinger_dz (f:complex->complex) ((g:complex->complex) w)` THEN
  ABBREV_TAC `b = wirtinger_dbar (f:complex->complex) ((g:complex->complex) w)` THEN
  SUBGOAL_THEN `~(a * cnj a - b * cnj b = Cx(&0))` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    REWRITE_TAC[GSYM BEL_DET_CX; CX_INJ] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((f:complex->complex) has_derivative frechet_derivative f (at ((g:complex->complex) w)))
      (at (g w)) /\
    (g has_derivative frechet_derivative g (at w)) (at w)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[FRECHET_DERIVATIVE_WORKS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!v:complex. frechet_derivative (f:complex->complex) (at ((g:complex->complex) w))
                  (frechet_derivative g (at w) v) = v`
  (LABEL_TAC "inv") THENL
   [MP_TAC(ISPECL [`g:complex->complex`; `f:complex->complex`;
                   `frechet_derivative (g:complex->complex) (at w)`;
                   `frechet_derivative (f:complex->complex) (at ((g:complex->complex) w))`;
                   `w:complex`] DIFF_CHAIN_AT) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(f:complex->complex) o (g:complex->complex) = (\w. w)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`\w:complex. w`;
                   `frechet_derivative (f:complex->complex) (at ((g:complex->complex) w)) o
                    frechet_derivative g (at w)`;
                   `\h:complex. h`; `w:complex`] FRECHET_DERIVATIVE_UNIQUE_AT) THEN
    ASM_REWRITE_TAC[HAS_DERIVATIVE_ID] THEN REWRITE_TAC[FUN_EQ_THM; o_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:complex->complex`;
                 `frechet_derivative (f:complex->complex) (at ((g:complex->complex) w))`;
                 `(g:complex->complex) w`] FRECHET_WIRTINGER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "wirt") THEN
  SUBGOAL_THEN
   `!v:complex. (frechet_derivative (g:complex->complex) (at w) v) =
                (cnj a * v - b * cnj v) * inv(a * cnj a - b * cnj b)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC BEL_SOLVE_RLIN THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "wirt" (fun th -> REWRITE_TAC[GSYM th]) THEN
    USE_THEN "inv" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  ASM_REWRITE_TAC[partial_derivative; COMPLEX_BASIS; CNJ_CX; CNJ_II] THEN
  CONJ_TAC THEN CONV_TAC COMPLEX_RING);;

let BEL_JFAM_WDBAR = prove
 (`!m (hh:real->complex->complex).
        bel_jfam (SUC m) (:complex) hh
        ==> bel_jfam m (:complex) (\t. wirtinger_dbar (hh t))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BEL_JFAM_EQ THEN
  EXISTS_TAC `\t w. (\t. (\z. inv(Cx(&2)) * z) o
                         partial_derivative 1 ((hh:real->complex->complex) t)) t w +
                    (\t. (\z. (ii * inv(Cx(&2))) * z) o
                         partial_derivative 2 (hh t)) t w` THEN
  REWRITE_TAC[OPEN_UNIV] THEN CONJ_TAC THENL
   [REWRITE_TAC[BEL_WIRTINGER_FUN; partial_derivative; COMPLEX_BASIS; o_THM];
    ALL_TAC] THEN
  MATCH_MP_TAC BEL_JFAM_ADD THEN REWRITE_TAC[OPEN_UNIV] THEN CONJ_TAC THEN
  REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC BEL_JFAM_LINEAR_O THEN
  REWRITE_TAC[OPEN_UNIV; LINEAR_COMPLEX_MUL; REWRITE_RULE[ETA_AX] LINEAR_COMPLEX_MUL] THEN
  MATCH_MP_TAC BEL_JFAM_PD THEN ASM_REWRITE_TAC[OPEN_UNIV; DIMINDEX_2; ARITH]);;

let BEL_JFAM_CLMUL = prove
 (`!m U c (ff:real->real^M->complex).
        open U /\ bel_jfam m U ff ==> bel_jfam m U (\t x. c * ff t x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:num`; `U:real^M->bool`; `\z:complex. c * z`;
                 `ff:real->real^M->complex`] BEL_JFAM_LINEAR_O) THEN
  ASM_REWRITE_TAC[LINEAR_COMPLEX_MUL; o_DEF]);;

let BEL_JFAM_INV = prove
 (`!ff kk:real->complex->complex C0.
        (!m. bel_jfam m (:complex) ff) /\
        (!t. t IN real_interval[&0,&1]
             ==> homeomorphism ((:complex),(:complex)) (ff t,kk t)) /\
        (!t z. t IN real_interval[&0,&1]
               ==> &0 < det(matrix(frechet_derivative (ff t) (at z)))) /\
        (!t z. t IN real_interval[&0,&1] ==> norm(ff t z - z) <= C0)
        ==> !m. bel_jfam m (:complex) kk`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fj")
    (CONJUNCTS_THEN2 (LABEL_TAC "homeo") (CONJUNCTS_THEN2 (LABEL_TAC "det") (LABEL_TAC "C0")))) THEN
  SUBGOAL_THEN `bel_jfam 0 (:complex) (kk:real->complex->complex)` (LABEL_TAC "k0") THENL
   [REWRITE_TAC[BEL_JFAM_0] THEN CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN DISCH_TAC THEN MATCH_MP_TAC BEL_HOMEO_INV_SMOOTH THEN
      EXISTS_TAC `(ff:real->complex->complex) t` THEN
      USE_THEN "fj" (MP_TAC o SPEC `0`) THEN
      USE_THEN "homeo" (MP_TAC o SPEC `t:real`) THEN
      USE_THEN "det" (MP_TAC o SPEC `t:real`) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_NZ; BEL_JFAM_0];
      MATCH_MP_TAC BEL_INV_CONT THEN
      MAP_EVERY EXISTS_TAC [`ff:real->complex->complex`; `C0:real`] THEN
      USE_THEN "fj" (MP_TAC o SPEC `0`) THEN SIMP_TAC[BEL_JFAM_0] THEN DISCH_TAC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t w. t IN real_interval[&0,&1]
          ==> (ff:real->complex->complex) t ((kk:real->complex->complex) t w) = w /\
              smooth_map_on (:complex) (ff t) /\ smooth_map_on (:complex) (kk t) /\
              ~(det(matrix(frechet_derivative (ff t) (at (kk t w)))) = &0)`
  (LABEL_TAC "pt") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "homeo" (fun th -> MP_TAC(MATCH_MP th (ASSUME `t IN real_interval[&0,&1]`))) THEN
    REWRITE_TAC[homeomorphism; IN_UNIV] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC BEL_JFAM_SMOOTH THEN EXISTS_TAC `0` THEN
      USE_THEN "fj" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC BEL_JFAM_SMOOTH THEN EXISTS_TAC `0` THEN
      USE_THEN "k0" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LT_IMP_NZ THEN
      USE_THEN "det" (fun th -> MATCH_MP_TAC th) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  INDUCT_TAC THENL [USE_THEN "k0" ACCEPT_TAC; ALL_TAC] THEN
  SIMP_TAC[BEL_JFAM_SUC; OPEN_UNIV; DIMINDEX_2] THEN
  CONJ_TAC THENL [USE_THEN "k0" ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `bel_jfam m (:complex)
      (\t w. wirtinger_dz ((ff:real->complex->complex) t) ((kk:real->complex->complex) t w)) /\
    bel_jfam m (:complex) (\t w. wirtinger_dbar (ff t) (kk t w))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`m:num`; `(:complex)`; `(:complex)`;
                     `\t. wirtinger_dz ((ff:real->complex->complex) t)`;
                     `kk:real->complex->complex`] BEL_JFAM_COMPOSE);
      MP_TAC(ISPECL [`m:num`; `(:complex)`; `(:complex)`;
                     `\t. wirtinger_dbar ((ff:real->complex->complex) t)`;
                     `kk:real->complex->complex`] BEL_JFAM_COMPOSE)] THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
    GEN_TAC THEN
    USE_THEN "fj" (fun th -> SIMP_TAC[BEL_JFAM_WDZ; BEL_JFAM_WDBAR; th]);
    ALL_TAC] THEN
  ABBREV_TAC
   `D = \t w. wirtinger_dz ((ff:real->complex->complex) t) ((kk:real->complex->complex) t w) *
              cnj(wirtinger_dz (ff t) (kk t w)) -
              wirtinger_dbar (ff t) (kk t w) * cnj(wirtinger_dbar (ff t) (kk t w))` THEN
  SUBGOAL_THEN `bel_jfam m (:complex) (\t w. inv((D:real->complex->complex) t w))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC BEL_JFAM_CINV THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN CONJ_TAC THENL
     [EXPAND_TAC "D" THEN REWRITE_TAC[] THEN MATCH_MP_TAC BEL_JFAM_SUB THEN
      REWRITE_TAC[OPEN_UNIV] THEN CONJ_TAC THEN MATCH_MP_TAC BEL_JFAM_CMUL_FUN THEN
      ASM_SIMP_TAC[OPEN_UNIV; BEL_JFAM_CNJ];
      X_GEN_TAC `t:real` THEN X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
      EXPAND_TAC "D" THEN REWRITE_TAC[GSYM BEL_DET_CX; CX_INJ] THEN
      USE_THEN "pt" (MP_TAC o SPECL [`t:real`; `w:complex`]) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `i = 1 \/ i = 2` (DISJ_CASES_THEN SUBST1_TAC) THENL
   [ASM_ARITH_TAC;
    MATCH_MP_TAC BEL_JFAM_EQ THEN
    EXISTS_TAC `\t w. (cnj(wirtinger_dz ((ff:real->complex->complex) t)
                              ((kk:real->complex->complex) t w)) -
                       wirtinger_dbar (ff t) (kk t w)) * inv((D:real->complex->complex) t w)` THEN
    REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN EXPAND_TAC "D" THEN REWRITE_TAC[] THEN
      CONV_TAC SYM_CONV THEN
      MP_TAC(ISPECL [`(ff:real->complex->complex) t`; `(kk:real->complex->complex) t`;
                     `z:complex`] BEL_INV_PARTIAL) THEN
      USE_THEN "pt" (MP_TAC o SPECL [`t:real`; `z:complex`]) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC BEL_JFAM_CMUL_FUN THEN ASM_REWRITE_TAC[OPEN_UNIV] THEN
      MATCH_MP_TAC BEL_JFAM_SUB THEN ASM_SIMP_TAC[OPEN_UNIV; BEL_JFAM_CNJ]];
    MATCH_MP_TAC BEL_JFAM_EQ THEN
    EXISTS_TAC `\t w. ii * (cnj(wirtinger_dz ((ff:real->complex->complex) t)
                                  ((kk:real->complex->complex) t w)) +
                            wirtinger_dbar (ff t) (kk t w)) * inv((D:real->complex->complex) t w)` THEN
    REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN EXPAND_TAC "D" THEN REWRITE_TAC[] THEN
      CONV_TAC SYM_CONV THEN
      MP_TAC(ISPECL [`(ff:real->complex->complex) t`; `(kk:real->complex->complex) t`;
                     `z:complex`] BEL_INV_PARTIAL) THEN
      USE_THEN "pt" (MP_TAC o SPECL [`t:real`; `z:complex`]) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC BEL_JFAM_CLMUL THEN REWRITE_TAC[OPEN_UNIV] THEN
      MATCH_MP_TAC BEL_JFAM_CMUL_FUN THEN ASM_REWRITE_TAC[OPEN_UNIV] THEN
      MATCH_MP_TAC BEL_JFAM_ADD THEN ASM_SIMP_TAC[OPEN_UNIV; BEL_JFAM_CNJ]]]);;

(* A chosen inverse of a homeomorphism of the plane.                         *)

let bel_hinv = new_definition
 `bel_hinv (f:complex->complex) = @g. homeomorphism ((:complex),(:complex)) (f,g)`;;

let BEL_HINV = prove
 (`!f:complex->complex.
        (?g. homeomorphism ((:complex),(:complex)) (f,g))
        ==> homeomorphism ((:complex),(:complex)) (f,bel_hinv f)`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o SELECT_RULE) THEN REWRITE_TAC[bel_hinv]);;

let BEL_HINV_ID = prove
 (`bel_hinv (\z:complex. z) = (\z. z)`,
  MP_TAC(ISPEC `\z:complex. z` BEL_HINV) THEN ANTS_TAC THENL
   [EXISTS_TAC `\z:complex. z` THEN REWRITE_TAC[HOMEOMORPHISM_ID];
    REWRITE_TAC[homeomorphism; IN_UNIV; FUN_EQ_THM] THEN MESON_TAC[]]);;


(* ========================================================================= *)
(* Holomorphic families (all derivatives jointly continuous                  *)
(* from joint continuity, by the Cauchy inequality), and the removable       *)
(* singularity at a pole of the inverted chart.                              *)
(* ========================================================================= *)

let BEL_HOLO_PD = prove
 (`!f s z i. open s /\ f holomorphic_on s /\ z IN s
             ==> partial_derivative i f z = complex_derivative f z * basis i`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(f has_complex_derivative (complex_derivative f z)) (at z)` MP_TAC THENL
   [REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE] THEN
    ASM_MESON_TAC[HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT];
    REWRITE_TAC[has_complex_derivative; partial_derivative] THEN
    DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    REWRITE_TAC[]]);;

let BEL_HOLO_ITERATED = prove
 (`!l f s z. open s /\ f holomorphic_on s /\ z IN s
             ==> iterated_partial l f z =
                 ITLIST (\i c. basis i * c) l (Cx(&1)) *
                 higher_complex_derivative (LENGTH l) f z`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[iterated_partial; ITLIST; LENGTH; higher_complex_derivative;
                COMPLEX_MUL_LID];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[iterated_partial; ITLIST; LENGTH;
                                    higher_complex_derivative] THEN
  ABBREV_TAC `c = ITLIST (\i c. basis i * c) t (Cx(&1))` THEN
  SUBGOAL_THEN `(\w. c * higher_complex_derivative (LENGTH(t:num list)) (f:complex->complex) w)
                holomorphic_on s` ASSUME_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN REWRITE_TAC[HOLOMORPHIC_ON_CONST; ETA_AX] THEN
    ASM_SIMP_TAC[HOLOMORPHIC_HIGHER_COMPLEX_DERIVATIVE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:num`; `iterated_partial t (f:complex->complex)`;
                 `\w. c * higher_complex_derivative (LENGTH(t:num list)) (f:complex->complex) w`;
                 `s:complex->bool`; `z:complex`] PARTIAL_DERIVATIVE_LOCAL_OPEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:complex` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `s:complex->bool` THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`\w. c * higher_complex_derivative (LENGTH(t:num list)) (f:complex->complex) w`;
                 `s:complex->bool`; `z:complex`; `h:num`] BEL_HOLO_PD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`higher_complex_derivative (LENGTH(t:num list)) (f:complex->complex)`;
                 `c:complex`; `z:complex`] COMPLEX_DERIVATIVE_LMUL) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT THEN
    EXISTS_TAC `s:complex->bool` THEN
    ASM_SIMP_TAC[HOLOMORPHIC_HIGHER_COMPLEX_DERIVATIVE];
    DISCH_THEN SUBST1_TAC THEN CONV_TAC COMPLEX_RING]);;

let BEL_JOINT_CONT_UNIF = prove
 (`!(G:real->real^M->real^N) V.
        (!t. t IN real_interval[&0,&1] ==> (G t) continuous_on V) /\
        (!t1 e. t1 IN real_interval[&0,&1] /\ &0 < e
                ==> ?d. &0 < d /\
                        !t z. t IN real_interval[&0,&1] /\ abs(t - t1) < d /\ z IN V
                              ==> norm(G t z - G t1 z) < e)
        ==> (\x. G (drop(sndcart x)) (fstcart x)) continuous_on bel_dom V`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "c") (LABEL_TAC "u")) THEN
  REWRITE_TAC[continuous_on; BEL_IN_DOM] THEN
  X_GEN_TAC `x:real^(M,1)finite_sum` THEN STRIP_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  USE_THEN "u" (MP_TAC o SPECL [`drop(sndcart(x:real^(M,1)finite_sum))`; `e / &2`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_HALF]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d1"))) THEN
  USE_THEN "c" (fun th -> MP_TAC(MATCH_MP th
    (ASSUME `drop(sndcart(x:real^(M,1)finite_sum)) IN real_interval[&0,&1]`))) THEN
  REWRITE_TAC[continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `fstcart(x:real^(M,1)finite_sum)`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d2"))) THEN
  EXISTS_TAC `min d1 d2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `y:real^(M,1)finite_sum` THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs(drop(sndcart(y:real^(M,1)finite_sum)) - drop(sndcart(x:real^(M,1)finite_sum)))
                < d1 /\ dist(fstcart y,fstcart x) < d2`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[dist; GSYM DROP_SUB; GSYM NORM_1; GSYM FSTCART_SUB; GSYM SNDCART_SUB] THEN
    MP_TAC(ISPEC `y - x:real^(M,1)finite_sum` NORM_FSTCART) THEN
    MP_TAC(ISPEC `y - x:real^(M,1)finite_sum` NORM_SNDCART) THEN
    UNDISCH_TAC `dist(y:real^(M,1)finite_sum,x) < d1` THEN
    UNDISCH_TAC `dist(y:real^(M,1)finite_sum,x) < d2` THEN
    REWRITE_TAC[dist] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "d1" (MP_TAC o SPECL [`drop(sndcart(y:real^(M,1)finite_sum))`;
                                 `fstcart(y:real^(M,1)finite_sum)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "d2" (MP_TAC o SPEC `fstcart(y:real^(M,1)finite_sum)`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  UNDISCH_TAC `norm((G:real->real^M->real^N) (drop(sndcart(y:real^(M,1)finite_sum)))
                  (fstcart y) -
                G (drop(sndcart(x:real^(M,1)finite_sum))) (fstcart y)) < e / &2` THEN
  UNDISCH_TAC `dist((G:real->real^M->real^N) (drop(sndcart(x:real^(M,1)finite_sum)))
                  (fstcart(y:real^(M,1)finite_sum)),
                G (drop(sndcart x)) (fstcart x)) < e / &2` THEN
  REWRITE_TAC[dist] THEN CONV_TAC NORM_ARITH);;

let BEL_UNIF_PARAM_K = prove
 (`!(hh:real->real^M->real^N) K e.
        compact K /\ (\x. hh (drop(sndcart x)) (fstcart x)) continuous_on bel_dom K /\
        &0 < e
        ==> ?d. &0 < d /\
                !t t' w. t IN real_interval[&0,&1] /\ t' IN real_interval[&0,&1] /\
                         abs(t' - t) < d /\ w IN K
                         ==> norm(hh t' w - hh t w) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^(M,1)finite_sum. (hh:real->real^M->real^N) (drop(sndcart x)) (fstcart x)`;
                 `bel_dom(K:real^M->bool)`] COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ASM_SIMP_TAC[BEL_DOM_COMPACT] THEN
  REWRITE_TAC[uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`pastecart (w:real^M) (lift t)`;
                                `pastecart (w:real^M) (lift t')`]) THEN
  ASM_REWRITE_TAC[BEL_IN_DOM; FSTCART_PASTECART; SNDCART_PASTECART;
                  LIFT_DROP; DIST_PASTECART_CANCEL; DIST_LIFT] THEN
  REWRITE_TAC[dist]);;

let BEL_HOLO_UNIF = prove
 (`!Psi:real->complex->complex s z0 r n.
        open s /\ &0 < r /\ cball(z0,&2 * r) SUBSET s /\
        (!t. t IN real_interval[&0,&1] ==> (Psi t) holomorphic_on s) /\
        (\x. Psi (drop(sndcart x)) (fstcart x)) continuous_on bel_dom s
        ==> !t1 e. t1 IN real_interval[&0,&1] /\ &0 < e
                   ==> ?d. &0 < d /\
                           !t z. t IN real_interval[&0,&1] /\ abs(t - t1) < d /\
                                 z IN ball(z0,r)
                                 ==> norm(higher_complex_derivative n (Psi t) z -
                                          higher_complex_derivative n (Psi t1) z) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `B = e * r pow n / (&2 * &(FACT n))` THEN
  SUBGOAL_THEN `&0 < B /\ &(FACT n) * B / r pow n < e` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN
    SUBGOAL_THEN `&0 < &(FACT n) /\ &0 < r pow n` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_OF_NUM_LT; FACT_LT; REAL_POW_LT]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_LT_MUL; REAL_ARITH `&0 < &2`];
      SUBGOAL_THEN `&(FACT n) * (e * r pow n / (&2 * &(FACT n))) / r pow n = e / &2`
      SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < &(FACT n)` THEN UNDISCH_TAC `&0 < r pow n` THEN
        CONV_TAC REAL_FIELD;
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Psi:real->complex->complex`; `cball(z0:complex,&2 * r)`; `B:real`]
                BEL_UNIF_PARAM_K) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_CBALL] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET; BEL_IN_DOM] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "U")) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `z:complex`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `cball(z:complex,r) SUBSET s` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(z0:complex,&2 * r)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_CBALL] THEN
    UNDISCH_TAC `(z:complex) IN ball(z0,r)` THEN REWRITE_TAC[IN_BALL] THEN
    CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(Psi:real->complex->complex) t`; `(Psi:real->complex->complex) t1`;
                 `s:complex->bool`; `n:num`; `z:complex`] HIGHER_COMPLEX_DERIVATIVE_SUB) THEN
  ASM_SIMP_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `cball(z:complex,r) SUBSET s` THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[CENTRE_IN_CBALL] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&(FACT n) * B / r pow n` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CAUCHY_INEQUALITY THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\w. (Psi:real->complex->complex) t w - Psi t1 w) holomorphic_on s`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_ON_SUB THEN ASM_SIMP_TAC[ETA_AX]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:complex->bool` THEN
    ASM_SIMP_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON];
    MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN EXISTS_TAC `s:complex->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(z:complex,r)` THEN
    ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
    X_GEN_TAC `x:complex` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "U" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_CBALL] THEN
    UNDISCH_TAC `(z:complex) IN ball(z0,r)` THEN REWRITE_TAC[IN_BALL] THEN
    UNDISCH_TAC `norm(z - x:complex) = r` THEN CONV_TAC NORM_ARITH]);;

let BEL_HOLO_DERIV_CONT = prove
 (`!Psi:real->complex->complex s n.
        open s /\ (!t. t IN real_interval[&0,&1] ==> (Psi t) holomorphic_on s) /\
        (\x. Psi (drop(sndcart x)) (fstcart x)) continuous_on bel_dom s
        ==> (\x. higher_complex_derivative n (Psi (drop(sndcart x))) (fstcart x))
            continuous_on bel_dom s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BEL_CONT_LOCAL THEN
  X_GEN_TAC `x0:real^(2,1)finite_sum` THEN REWRITE_TAC[BEL_IN_DOM] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `fstcart(x0:real^(2,1)finite_sum)`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `ball(fstcart(x0:real^(2,1)finite_sum),r0 / &3)` THEN
  ASM_SIMP_TAC[OPEN_BALL; CENTRE_IN_BALL; REAL_LT_DIV; REAL_ARITH `&0 < &3`] THEN
  SUBGOAL_THEN `s INTER ball(fstcart(x0:real^(2,1)finite_sum),r0 / &3) =
                ball(fstcart x0,r0 / &3)` SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE `(t:complex->bool) SUBSET s ==> s INTER t = t`) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `ball(fstcart(x0:real^(2,1)finite_sum),r0)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. higher_complex_derivative n ((Psi:real->complex->complex) t)`;
                 `ball(fstcart(x0:real^(2,1)finite_sum),r0 / &3)`] BEL_JOINT_CONT_UNIF) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `s:complex->bool` THEN CONJ_TAC THENL
     [MATCH_MP_TAC HOLOMORPHIC_ON_IMP_CONTINUOUS_ON THEN
      MATCH_MP_TAC HOLOMORPHIC_HIGHER_COMPLEX_DERIVATIVE THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `ball(fstcart(x0:real^(2,1)finite_sum),r0)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC BEL_HOLO_UNIF THEN EXISTS_TAC `s:complex->bool` THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < &3`] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `ball(fstcart(x0:real^(2,1)finite_sum),r0)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN
    UNDISCH_TAC `&0 < r0` THEN REAL_ARITH_TAC]);;

let BEL_HOLO_JFAM = prove
 (`!Psi:real->complex->complex s.
        open s /\ (!t. t IN real_interval[&0,&1] ==> (Psi t) holomorphic_on s) /\
        (\x. Psi (drop(sndcart x)) (fstcart x)) continuous_on bel_dom s
        ==> !m. bel_jfam m s Psi`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bel_jfam] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC BEL_HOLOMORPHIC_SMOOTH THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `l:num list` THEN STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `\x. ITLIST (\i c. basis i * c) l (Cx(&1)) *
                  higher_complex_derivative (LENGTH(l:num list))
                    ((Psi:real->complex->complex) (drop(sndcart x))) (fstcart x)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BEL_IN_DOM] THEN REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC BEL_HOLO_ITERATED THEN
    EXISTS_TAC `s:complex->bool` THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN MATCH_MP_TAC BEL_HOLO_DERIV_CONT THEN
    ASM_REWRITE_TAC[]]);;

(* The pole of the inverted chart: w |-> 1 / cnj(K(1 / cnj w)), 0 |-> 0.    *)

let bel_pole = new_definition
 `bel_pole (K:complex->complex) (w:complex) =
    if w = Cx(&0) then Cx(&0) else inv(cnj(K(inv(cnj w))))`;;

let BEL_CNJ_CONJ_DIFF = prove
 (`!f:complex->complex z.
        f complex_differentiable at (cnj z)
        ==> (\w. cnj(f(cnj w))) complex_differentiable at z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[complex_differentiable; has_complex_derivative] THEN
  DISCH_THEN(X_CHOOSE_TAC `f':complex`) THEN EXISTS_TAC `cnj f'` THEN
  SUBGOAL_THEN `(cnj has_derivative cnj) (at (z:complex)) /\
                (cnj has_derivative cnj) (at ((f:complex->complex)(cnj z)))`
  STRIP_ASSUME_TAC THENL [SIMP_TAC[HAS_DERIVATIVE_LINEAR; LINEAR_CNJ]; ALL_TAC] THEN
  MP_TAC(ISPECL [`cnj`; `f:complex->complex`; `cnj`; `\h:complex. f' * h`; `z:complex`]
                DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(f:complex->complex) o cnj`; `cnj`; `(\h:complex. f' * h) o cnj`;
                 `cnj`; `z:complex`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[o_THM] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; CNJ_MUL; CNJ_CNJ]);;

let BEL_POLE_BOUND = prove
 (`!K:complex->complex C0 R0 w.
        (!z. norm(K z - z) <= C0) /\ ~(w = Cx(&0)) /\
        norm w < inv(abs R0 + &2 * abs C0 + &1)
        ==> R0 < norm(inv(cnj w)) /\ ~(K(inv(cnj w)) = Cx(&0)) /\
            norm(bel_pole K w) <= &2 * norm w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `z = inv(cnj w)` THEN
  SUBGOAL_THEN `&0 < norm(w:complex)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_NORM_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `abs R0 + &2 * abs C0 + &1 < norm(z:complex)` ASSUME_TAC THENL
   [SUBGOAL_THEN `norm(z:complex) = inv(norm(w:complex))` SUBST1_TAC THENL
     [EXPAND_TAC "z" THEN REWRITE_TAC[COMPLEX_NORM_INV; COMPLEX_NORM_CNJ]; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN
    MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(z:complex) / &2 <= norm((K:complex->complex) z)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `z:complex`) THEN
    UNDISCH_TAC `abs R0 + &2 * abs C0 + &1 < norm(z:complex)` THEN
    CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(z:complex) / &2` ASSUME_TAC THENL
   [UNDISCH_TAC `abs R0 + &2 * abs C0 + &1 < norm(z:complex)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `abs R0 + &2 * abs C0 + &1 < norm(z:complex)` THEN REAL_ARITH_TAC;
    REWRITE_TAC[GSYM COMPLEX_NORM_NZ] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[bel_pole] THEN ASM_REWRITE_TAC[COMPLEX_NORM_INV; COMPLEX_NORM_CNJ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(norm(z:complex) / &2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `norm(z:complex) = inv(norm(w:complex))` SUBST1_TAC THENL
       [EXPAND_TAC "z" THEN REWRITE_TAC[COMPLEX_NORM_INV; COMPLEX_NORM_CNJ]; ALL_TAC] THEN
      UNDISCH_TAC `&0 < norm(w:complex)` THEN CONV_TAC REAL_FIELD]]);;

let BEL_IN_BALL_C0 = prove
 (`!w r. w IN ball(Cx(&0),r) <=> norm w < r`,
  REWRITE_TAC[IN_BALL; dist; COMPLEX_SUB_LZERO; NORM_NEG]);;

let BEL_POLE_DIFF = prove
 (`!K:complex->complex C0 R0 w.
        (!z. norm(K z - z) <= C0) /\ (!z. R0 < norm z ==> K complex_differentiable at z) /\
        ~(w = Cx(&0)) /\ norm w < inv(abs R0 + &2 * abs C0 + &1)
        ==> (bel_pole K) complex_differentiable at w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`K:complex->complex`; `C0:real`; `R0:real`; `w:complex`] BEL_POLE_BOUND) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_TRANSFORM_AT THEN
  MAP_EVERY EXISTS_TAC [`\w. inv(cnj((K:complex->complex)(cnj(inv w))))`; `norm(w:complex)`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_NORM_NZ];
    X_GEN_TAC `x:complex` THEN DISCH_TAC THEN REWRITE_TAC[bel_pole; CNJ_INV] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `dist(x:complex,w) < norm w` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[dist; COMPLEX_SUB_LZERO; NORM_NEG; REAL_LT_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_INV_AT THEN CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[CNJ_EQ_0; CNJ_INV] THEN ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `(\w. cnj((K:complex->complex)(cnj(inv w)))) = (\u. cnj(K(cnj u))) o inv`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_COMPOSE_AT THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`\w:complex. w`; `w:complex`] COMPLEX_DIFFERENTIABLE_INV_AT) THEN
    ASM_REWRITE_TAC[COMPLEX_DIFFERENTIABLE_ID; ETA_AX];
    MATCH_MP_TAC BEL_CNJ_CONJ_DIFF THEN REWRITE_TAC[CNJ_INV] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let BEL_POLE_HOLO = prove
 (`!K:complex->complex C0 R0.
        (!z. norm(K z - z) <= C0) /\ (!z. R0 < norm z ==> K complex_differentiable at z)
        ==> (bel_pole K) holomorphic_on ball(Cx(&0),inv(abs R0 + &2 * abs C0 + &1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `r = inv(abs R0 + &2 * abs C0 + &1)` THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC NO_ISOLATED_SINGULARITY THEN EXISTS_TAC `{Cx(&0)}` THEN
  REWRITE_TAC[OPEN_BALL; FINITE_SING] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    X_GEN_TAC `w:complex` THEN REWRITE_TAC[BEL_IN_BALL_C0] THEN DISCH_TAC THEN
    ASM_CASES_TAC `w = Cx(&0)` THENL
     [ASM_REWRITE_TAC[continuous_at] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      EXISTS_TAC `min r (e / &2)` THEN ASM_REWRITE_TAC[REAL_LT_MIN; REAL_HALF] THEN
      X_GEN_TAC `x:complex` THEN
      REWRITE_TAC[dist; COMPLEX_SUB_RZERO] THEN STRIP_TAC THEN
      SUBGOAL_THEN `bel_pole (K:complex->complex) (Cx(&0)) = Cx(&0)` SUBST1_TAC THENL
       [REWRITE_TAC[bel_pole]; ALL_TAC] THEN
      REWRITE_TAC[COMPLEX_SUB_RZERO] THEN
      ASM_CASES_TAC `x = Cx(&0)` THENL
       [ASM_REWRITE_TAC[bel_pole; COMPLEX_NORM_0]; ALL_TAC] THEN
      MP_TAC(ISPECL [`K:complex->complex`; `C0:real`; `R0:real`; `x:complex`]
                    BEL_POLE_BOUND) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
      MATCH_MP_TAC BEL_POLE_DIFF THEN
      MAP_EVERY EXISTS_TAC [`C0:real`; `R0:real`] THEN ASM_REWRITE_TAC[]];
    SIMP_TAC[HOLOMORPHIC_ON_OPEN; OPEN_DIFF; OPEN_BALL; CLOSED_SING] THEN
    REWRITE_TAC[GSYM complex_differentiable; IN_DIFF; IN_SING; BEL_IN_BALL_C0] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC BEL_POLE_DIFF THEN
    MAP_EVERY EXISTS_TAC [`C0:real`; `R0:real`] THEN ASM_REWRITE_TAC[]]);;

let BEL_POLE_INJ = prove
 (`!K:complex->complex C0 R0 w1 w2.
        (!z. norm(K z - z) <= C0) /\ (!z1 z2. K z1 = K z2 ==> z1 = z2) /\
        w1 IN ball(Cx(&0),inv(abs R0 + &2 * abs C0 + &1)) /\
        w2 IN ball(Cx(&0),inv(abs R0 + &2 * abs C0 + &1)) /\
        bel_pole K w1 = bel_pole K w2
        ==> w1 = w2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BEL_IN_BALL_C0] THEN STRIP_TAC THEN
  ASM_CASES_TAC `w1 = Cx(&0)` THEN ASM_CASES_TAC `w2 = Cx(&0)` THEN ASM_REWRITE_TAC[] THENL
   [UNDISCH_TAC `bel_pole (K:complex->complex) w1 = bel_pole K w2` THEN
    ASM_REWRITE_TAC[bel_pole] THEN
    MP_TAC(ISPECL [`K:complex->complex`; `C0:real`; `R0:real`; `w2:complex`] BEL_POLE_BOUND) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    DISCH_THEN(MP_TAC o SYM) THEN ASM_REWRITE_TAC[COMPLEX_INV_EQ_0; CNJ_EQ_0];
    UNDISCH_TAC `bel_pole (K:complex->complex) w1 = bel_pole K w2` THEN
    ASM_REWRITE_TAC[bel_pole] THEN
    MP_TAC(ISPECL [`K:complex->complex`; `C0:real`; `R0:real`; `w1:complex`] BEL_POLE_BOUND) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[COMPLEX_INV_EQ_0; CNJ_EQ_0];
    UNDISCH_TAC `bel_pole (K:complex->complex) w1 = bel_pole K w2` THEN
    ASM_REWRITE_TAC[bel_pole] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\u:complex. cnj(inv u)`) THEN
    REWRITE_TAC[CNJ_INV; COMPLEX_INV_INV; CNJ_CNJ] THEN
    DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    DISCH_THEN(MP_TAC o AP_TERM `\u:complex. cnj(inv u)`) THEN
    REWRITE_TAC[CNJ_INV; COMPLEX_INV_INV; CNJ_CNJ]]);;

let BEL_POLE_JCONT = prove
 (`!K:real->complex->complex C0 R0.
        (!t z. t IN real_interval[&0,&1] ==> norm(K t z - z) <= C0) /\
        (\x. K (drop(sndcart x)) (fstcart x)) continuous_on bel_dom (:complex)
        ==> (\x. bel_pole (K (drop(sndcart x))) (fstcart x)) continuous_on
            bel_dom (ball(Cx(&0),inv(abs R0 + &2 * abs C0 + &1)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "C0") (LABEL_TAC "kc")) THEN
  ABBREV_TAC `r = inv(abs R0 + &2 * abs C0 + &1)` THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t w. t IN real_interval[&0,&1] /\ ~(w = Cx(&0)) /\ norm w < r
          ==> ~((K:real->complex->complex) t (inv(cnj w)) = Cx(&0)) /\
              norm(bel_pole (K t) w) <= &2 * norm w`
  (LABEL_TAC "bd") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(K:real->complex->complex) t`; `C0:real`; `R0:real`; `w:complex`]
                  BEL_POLE_BOUND) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN GEN_TAC THEN USE_THEN "C0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  X_GEN_TAC `x:real^(2,1)finite_sum` THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[BEL_IN_DOM; BEL_IN_BALL_C0]) THEN
  ASM_CASES_TAC `fstcart(x:real^(2,1)finite_sum) = Cx(&0)` THENL
   [REWRITE_TAC[continuous_within] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    EXISTS_TAC `min r (e / &2)` THEN ASM_REWRITE_TAC[REAL_LT_MIN; REAL_HALF] THEN
    X_GEN_TAC `y:real^(2,1)finite_sum` THEN REWRITE_TAC[BEL_IN_DOM; BEL_IN_BALL_C0] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[bel_pole; dist; COMPLEX_SUB_RZERO] THEN
    SUBGOAL_THEN `norm(fstcart(y:real^(2,1)finite_sum)) < e / &2` ASSUME_TAC THENL
     [MP_TAC(ISPEC `y - x:real^(2,1)finite_sum` NORM_FSTCART) THEN
      ASM_REWRITE_TAC[FSTCART_SUB; COMPLEX_SUB_RZERO] THEN
      UNDISCH_TAC `dist(y:real^(2,1)finite_sum,x) < e / &2` THEN
      REWRITE_TAC[dist] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[COMPLEX_NORM_0] THEN
    USE_THEN "bd" (MP_TAC o SPECL [`drop(sndcart(y:real^(2,1)finite_sum))`;
                                   `fstcart(y:real^(2,1)finite_sum)`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[bel_pole] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `V = {z:complex | ~(z = Cx(&0))}` THEN
  MP_TAC(ISPECL [`\x:real^(2,1)finite_sum. bel_pole ((K:real->complex->complex)
                    (drop(sndcart x))) (fstcart x)`;
                 `x:real^(2,1)finite_sum`; `bel_dom(ball(Cx(&0),r))`;
                 `bel_dom(ball(Cx(&0),r) INTER V)`] CONTINUOUS_WITHIN_OPEN_IN) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "V" THEN ASM_REWRITE_TAC[BEL_IN_DOM; IN_INTER; IN_ELIM_THM; BEL_IN_BALL_C0];
      MATCH_MP_TAC BEL_DOM_OPEN_IN THEN EXPAND_TAC "V" THEN REWRITE_TAC[BEL_OPEN_NONZERO_C]];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  SUBGOAL_THEN
   `(\x:real^(2,1)finite_sum. bel_pole ((K:real->complex->complex) (drop(sndcart x))) (fstcart x))
    continuous_on bel_dom(ball(Cx(&0),r) INTER V)`
  MP_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN DISCH_THEN MATCH_MP_TAC THEN
    EXPAND_TAC "V" THEN ASM_REWRITE_TAC[BEL_IN_DOM; IN_INTER; IN_ELIM_THM; BEL_IN_BALL_C0]] THEN
  MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `\x:real^(2,1)finite_sum.
                inv(cnj((K:real->complex->complex) (drop(sndcart x)) (inv(cnj(fstcart x)))))` THEN
  CONJ_TAC THENL
   [EXPAND_TAC "V" THEN REWRITE_TAC[BEL_IN_DOM; IN_INTER; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[bel_pole];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_INV THEN CONJ_TAC THENL
   [ALL_TAC;
    EXPAND_TAC "V" THEN REWRITE_TAC[BEL_IN_DOM; IN_INTER; IN_ELIM_THM; BEL_IN_BALL_C0] THEN
    X_GEN_TAC `y:real^(2,1)finite_sum` THEN STRIP_TAC THEN REWRITE_TAC[CNJ_EQ_0] THEN
    USE_THEN "bd" (MP_TAC o SPECL [`drop(sndcart(y:real^(2,1)finite_sum))`;
                                   `fstcart(y:real^(2,1)finite_sum)`]) THEN
    ASM_SIMP_TAC[]] THEN
  SUBGOAL_THEN
   `(\x:real^(2,1)finite_sum.
       cnj((K:real->complex->complex) (drop(sndcart x)) (inv(cnj(fstcart x))))) =
    cnj o (\y:real^(2,1)finite_sum. K (drop(sndcart y)) (fstcart y)) o
    (\x. pastecart (inv(cnj(fstcart x))) (sndcart x))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[CONTINUOUS_ON_CNJ]] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART; ETA_AX] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_INV THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\x:real^(2,1)finite_sum. cnj(fstcart x)) = cnj o fstcart` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; CONTINUOUS_ON_CNJ];
      EXPAND_TAC "V" THEN REWRITE_TAC[BEL_IN_DOM; IN_INTER; IN_ELIM_THM; CNJ_EQ_0] THEN
      SIMP_TAC[]];
    USE_THEN "kc" (MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; BEL_IN_DOM; IN_UNIV; FSTCART_PASTECART;
                SNDCART_PASTECART; IN_INTER] THEN
    SIMP_TAC[]]);;

let BEL_POLE = prove
 (`!K:real->complex->complex R0 C0.
      (!t. t IN real_interval[&0,&1] ==> (!z1 z2. K t z1 = K t z2 ==> z1 = z2)) /\
      (!t z. t IN real_interval[&0,&1] /\ R0 < norm z ==> K t complex_differentiable at z) /\
      (!t z. t IN real_interval[&0,&1] ==> norm(K t z - z) <= C0) /\
      (\x. K (drop(sndcart x)) (fstcart x)) continuous_on bel_dom (:complex)
      ==> ?r. &0 < r /\
              (!t. t IN real_interval[&0,&1]
                   ==> (bel_pole (K t)) holomorphic_on ball(Cx(&0),r) /\
                       (!w. w IN ball(Cx(&0),r)
                            ==> ~(complex_derivative (bel_pole (K t)) w = Cx(&0))) /\
                       (!w1 w2. w1 IN ball(Cx(&0),r) /\ w2 IN ball(Cx(&0),r) /\
                                bel_pole (K t) w1 = bel_pole (K t) w2 ==> w1 = w2)) /\
              (!m. bel_jfam m (ball(Cx(&0),r)) (\t. bel_pole (K t)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  EXISTS_TAC `inv(abs R0 + &2 * abs C0 + &1)` THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t IN real_interval[&0,&1]
        ==> (bel_pole ((K:real->complex->complex) t)) holomorphic_on
            ball(Cx(&0),inv(abs R0 + &2 * abs C0 + &1))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC BEL_POLE_HOLO THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t w1 w2. t IN real_interval[&0,&1] /\
              w1 IN ball(Cx(&0),inv(abs R0 + &2 * abs C0 + &1)) /\
              w2 IN ball(Cx(&0),inv(abs R0 + &2 * abs C0 + &1)) /\
              bel_pole ((K:real->complex->complex) t) w1 = bel_pole (K t) w2
              ==> w1 = w2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC BEL_POLE_INJ THEN
    MAP_EVERY EXISTS_TAC [`(K:real->complex->complex) t`; `C0:real`; `R0:real`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[];
      MATCH_MP_TAC HOLOMORPHIC_INJECTIVE_IMP_REGULAR THEN
      ASM_SIMP_TAC[OPEN_BALL] THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[]];
    MATCH_MP_TAC BEL_HOLO_JFAM THEN ASM_SIMP_TAC[OPEN_BALL] THEN
    MATCH_MP_TAC BEL_POLE_JCONT THEN ASM_REWRITE_TAC[]]);;

(* Inverses of maps that are holomorphic outside a disc.                      *)

let BEL_CDIFF_DET = prove
 (`!f:complex->complex z.
        f complex_differentiable at z
        ==> det(matrix(frechet_derivative f (at z))) = norm(complex_derivative f z) pow 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[BEL_DET_WIRT] THEN
  ASM_SIMP_TAC[WIRTINGER_DZ_COMPLEX_DERIVATIVE] THEN
  MP_TAC(ISPECL [`f:complex->complex`; `z:complex`] WIRTINGER_DBAR_EQ_ZERO) THEN
  ASM_SIMP_TAC[COMPLEX_DIFFERENTIABLE_IMP_DIFFERENTIABLE] THEN
  DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[COMPLEX_NORM_0] THEN REAL_ARITH_TAC);;

let BEL_INV_CDIFF = prove
 (`!f g:complex->complex z.
        f complex_differentiable at (g z) /\
        ~(det(matrix(frechet_derivative f (at (g z)))) = &0) /\
        g continuous at z /\ (!w. f(g w) = w)
        ==> g complex_differentiable at z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[complex_differentiable] THEN
  EXISTS_TAC `inv(complex_derivative (f:complex->complex) ((g:complex->complex) z))` THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_INVERSE_BASIC THEN
  EXISTS_TAC `f:complex->complex` THEN EXISTS_TAC `(:complex)` THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE] THEN
  UNDISCH_TAC `~(det(matrix(frechet_derivative (f:complex->complex)
                  (at ((g:complex->complex) z)))) = &0)` THEN
  ASM_SIMP_TAC[BEL_CDIFF_DET; REAL_POW_EQ_0; COMPLEX_NORM_ZERO; ARITH]);;


(* ========================================================================= *)
(* The stereographic charts stereo2_n_inv (P) and                            *)
(* stereo2_s_inv (Q) of pc_mfd_examples: explicit derivatives, conformality, *)
(* tangency, the tangent planes are their images, and the transition         *)
(* Q(1/cnj u) = P(u).                                                        *)
(* ========================================================================= *)

let bel_emb = new_definition
 `bel_emb (y:real^2) = (lambda i. if i = 3 then &0 else y$i):real^3`;;

let BEL_EMB_COMPONENTS = prove
 (`!y:real^2. bel_emb y$1 = y$1 /\ bel_emb y$2 = y$2 /\ bel_emb y$3 = &0`,
  SIMP_TAC[bel_emb; LAMBDA_BETA; DIMINDEX_3; ARITH]);;

let BEL_BASIS3_COMPONENTS = prove
 (`(basis 3:real^3)$1 = &0 /\ (basis 3:real^3)$2 = &0 /\ (basis 3:real^3)$3 = &1`,
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH]);;

let BEL_EMB_LINEAR = prove
 (`linear bel_emb`,
  REWRITE_TAC[linear; CART_EQ; DIMINDEX_3; FORALL_3; BEL_EMB_COMPONENTS;
              VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC);;

let BEL_EMB_DOT = prove
 (`!h k:real^2. bel_emb h dot bel_emb k = h dot k /\ bel_emb h dot basis 3 = &0`,
  REWRITE_TAC[DOT_3; DOT_2; BEL_EMB_COMPONENTS; BEL_BASIS3_COMPONENTS] THEN
  REAL_ARITH_TAC);;

let BEL_P_FORM = prove
 (`!y. stereo2_n_inv y =
       basis 3 + (&2 / (norm y pow 2 + &1)) % (bel_emb y - basis 3)`,
  GEN_TAC THEN MP_TAC(ISPEC `y:real^2` STEX_INV_STEREO_DENOM) THEN DISCH_TAC THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; STEX_STEREO2_N_INV_COMPONENTS;
              VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_SUB_COMPONENT;
              BEL_EMB_COMPONENTS; BEL_BASIS3_COMPONENTS] THEN
  UNDISCH_TAC `&0 < norm(y:real^2) pow 2 + &1` THEN CONV_TAC REAL_FIELD);;

let BEL_SCAL_HAS_DERIVATIVE = prove
 (`!y:real^2.
        ((lift o (\y. &2 / (norm y pow 2 + &1))) has_derivative
         (lift o (\h. --(&4 * (y dot h) / (norm y pow 2 + &1) pow 2)))) (at y)`,
  GEN_TAC THEN
  MP_TAC(ISPEC `y:real^2` STEX_INV_STEREO_DENOM) THEN DISCH_TAC THEN
  MP_TAC(INST [`norm(y:real^2) pow 2`,`s:real`]
     (DISCH_ALL(REAL_DIFF_CONV `((\s. &2 / (s + &1)) has_real_derivative f') (atreal s)`))) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN
  REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `y:real^2` HAS_DERIVATIVE_SQNORM_AT) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\x:real^2. lift(norm x pow 2)`;
                 `lift o (\s. &2 / (s + &1)) o drop`;
                 `\x:real^2. &2 % lift(y dot x)`;
                 `\x:real^1. ((&0 * (norm(y:real^2) pow 2 + &1) - &2 * (&1 + &0)) /
                              (norm y pow 2 + &1) pow 2) % x`;
                 `y:real^2`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP] THEN X_GEN_TAC `x:real^2` THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC; GSYM LIFT_CMUL; LIFT_EQ] THEN
  UNDISCH_TAC `&0 < norm(y:real^2) pow 2 + &1` THEN CONV_TAC REAL_FIELD);;

let bel_dP = new_definition
 `bel_dP (y:real^2) (h:real^2) =
    (&2 / (norm y pow 2 + &1)) % bel_emb h -
    (&4 * (y dot h) / (norm y pow 2 + &1) pow 2) % (bel_emb y - basis 3)`;;

let BEL_P_HAS_DERIVATIVE = prove
 (`!y. (stereo2_n_inv has_derivative bel_dP y) (at y)`,
  GEN_TAC THEN
  SUBGOAL_THEN `((\x:real^2. bel_emb x - basis 3) has_derivative bel_emb) (at y)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`bel_emb`; `bel_emb`; `\x:real^2. basis 3:real^3`; `\h:real^2. vec 0:real^3`;
                   `at (y:real^2)`] HAS_DERIVATIVE_SUB) THEN
    SIMP_TAC[HAS_DERIVATIVE_LINEAR; BEL_EMB_LINEAR; HAS_DERIVATIVE_CONST] THEN
    REWRITE_TAC[VECTOR_SUB_RZERO; ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\y:real^2. &2 / (norm y pow 2 + &1)`;
                 `\h:real^2. --(&4 * (y dot h) / (norm y pow 2 + &1) pow 2)`;
                 `\x:real^2. bel_emb x - basis 3`; `bel_emb`; `y:real^2`]
                HAS_DERIVATIVE_MUL_AT) THEN
  ASM_REWRITE_TAC[BEL_SCAL_HAS_DERIVATIVE] THEN
  DISCH_THEN(fun th -> MP_TAC(BETA_RULE(MATCH_MP HAS_DERIVATIVE_ADD
    (CONJ (ISPECL [`basis 3:real^3`; `at (y:real^2)`] HAS_DERIVATIVE_CONST) th)))) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; BEL_P_FORM; bel_dP] THEN VECTOR_ARITH_TAC);;

let BEL_EMB_DOT_ALL = prove
 (`!h k:real^2. bel_emb h dot bel_emb k = h dot k /\ bel_emb h dot basis 3 = &0 /\
                basis 3 dot bel_emb h = &0 /\ basis 3 dot (basis 3:real^3) = &1`,
  REWRITE_TAC[DOT_3; DOT_2; BEL_EMB_COMPONENTS; BEL_BASIS3_COMPONENTS] THEN
  REAL_ARITH_TAC);;

let BEL_P_CONF = prove
 (`!y h k. bel_dP y h dot bel_dP y k = (&4 / (norm y pow 2 + &1) pow 2) * (h dot k)`,
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `y:real^2` STEX_INV_STEREO_DENOM) THEN DISCH_TAC THEN
  REWRITE_TAC[bel_dP; DOT_LSUB; DOT_RSUB; DOT_LMUL; DOT_RMUL; BEL_EMB_DOT_ALL] THEN
  REWRITE_TAC[ISPECL [`y:real^2`; `h:real^2`] DOT_SYM;
              ISPECL [`y:real^2`; `k:real^2`] DOT_SYM; GSYM NORM_POW_2] THEN
  UNDISCH_TAC `&0 < norm(y:real^2) pow 2 + &1` THEN CONV_TAC REAL_FIELD);;

let BEL_P_TANG = prove
 (`!y h. stereo2_n_inv y dot bel_dP y h = &0`,
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `y:real^2` STEX_INV_STEREO_DENOM) THEN DISCH_TAC THEN
  REWRITE_TAC[BEL_P_FORM; bel_dP; DOT_LADD; DOT_LSUB; DOT_RSUB; DOT_LMUL; DOT_RMUL;
              BEL_EMB_DOT_ALL] THEN
  REWRITE_TAC[ISPECL [`y:real^2`; `h:real^2`] DOT_SYM; GSYM NORM_POW_2] THEN
  UNDISCH_TAC `&0 < norm(y:real^2) pow 2 + &1` THEN CONV_TAC REAL_FIELD);;

let BEL_ONB3 = prove
 (`!e1 e2 e3 v:real^3.
        e1 dot e1 = &1 /\ e2 dot e2 = &1 /\ e3 dot e3 = &1 /\
        e1 dot e2 = &0 /\ e1 dot e3 = &0 /\ e2 dot e3 = &0
        ==> v = (e1 dot v) % e1 + (e2 dot v) % e2 + (e3 dot v) % e3`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `M = (lambda i. if i = 1 then e1 else if i = 2 then e2 else e3):real^3^3` THEN
  SUBGOAL_THEN `(M:real^3^3)$1 = e1 /\ M$2 = e2 /\ M$3 = e3` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN SIMP_TAC[LAMBDA_BETA; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `(M:real^3^3) ** transp M = mat 1` ASSUME_TAC THENL
   [SIMP_TAC[CART_EQ; LAMBDA_BETA; DIMINDEX_3; FORALL_3; matrix_mul; transp; mat; ARITH;
             SUM_3] THEN
    ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[DOT_3]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `transp(M:real^3^3) ** M = mat 1` ASSUME_TAC THENL
   [ASM_MESON_TAC[MATRIX_LEFT_RIGHT_INVERSE]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `transp(M:real^3^3) ** (M ** v)` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_LID]; ALL_TAC] THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; DIMINDEX_3; FORALL_3; matrix_vector_mul; transp; ARITH;
           SUM_3; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  ASM_REWRITE_TAC[DOT_3] THEN REAL_ARITH_TAC);;

let BEL_DP_LINEAR = prove
 (`!y. linear(bel_dP y)`,
  MESON_TAC[BEL_P_HAS_DERIVATIVE; has_derivative]);;

let BEL_DP_EXPAND = prove
 (`!y a:real^2. bel_dP y a = a$1 % bel_dP y (basis 1) + a$2 % bel_dP y (basis 2)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`bel_dP y`; `a:real^2`] BEL_LINEAR_BASIS_EXPAND) THEN
  REWRITE_TAC[BEL_DP_LINEAR; DIMINDEX_2] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VSUM_2]);;

let BEL_P_NORM = prove
 (`!y. stereo2_n_inv y dot stereo2_n_inv y = &1`,
  GEN_TAC THEN MP_TAC(ISPEC `y:real^2` STEX_STEREO2_N_INV_IN) THEN
  REWRITE_TAC[IN_DELETE; IN_SPHERE_0; GSYM NORM_POW_2] THEN
  SIMP_TAC[REAL_POW_ONE]);;

let BEL_P_SPAN = prove
 (`!z v. v dot stereo2_n_inv z = &0 ==> ?a. bel_dP z a = v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(z:real^2) pow 2 + &1` ASSUME_TAC THENL
   [REWRITE_TAC[STEX_INV_STEREO_DENOM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `bel_dP z (basis 1) dot bel_dP z (basis 1) = &4 / (norm(z:real^2) pow 2 + &1) pow 2 /\
    bel_dP z (basis 2) dot bel_dP z (basis 2) = &4 / (norm z pow 2 + &1) pow 2 /\
    bel_dP z (basis 1) dot bel_dP z (basis 2) = &0 /\
    bel_dP z (basis 1) dot stereo2_n_inv z = &0 /\
    bel_dP z (basis 2) dot stereo2_n_inv z = &0 /\
    stereo2_n_inv z dot stereo2_n_inv z = &1`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[BEL_P_CONF; BEL_P_NORM] THEN
    SIMP_TAC[DOT_BASIS_BASIS; DIMINDEX_2; ARITH; REAL_MUL_RID; REAL_MUL_RZERO] THEN
    ONCE_REWRITE_TAC[DOT_SYM] THEN REWRITE_TAC[BEL_P_TANG];
    ALL_TAC] THEN
  ABBREV_TAC `s = norm(z:real^2) pow 2 + &1` THEN
  ABBREV_TAC `p1 = bel_dP z (basis 1)` THEN
  ABBREV_TAC `p2 = bel_dP z (basis 2)` THEN
  ABBREV_TAC `p = stereo2_n_inv z` THEN
  MP_TAC(ISPECL [`(s / &2) % p1:real^3`; `(s / &2) % p2:real^3`; `p:real^3`; `v:real^3`]
                BEL_ONB3) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[DOT_LMUL; DOT_RMUL] THEN UNDISCH_TAC `&0 < s` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `p dot (v:real^3) = &0` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; DOT_LMUL; VECTOR_MUL_ASSOC] THEN
  EXISTS_TAC `vector[(s / &2 * ((p1:real^3) dot (v:real^3))) * s / &2;
                     (s / &2 * ((p2:real^3) dot v)) * s / &2]:real^2` THEN
  ASM_REWRITE_TAC[BEL_DP_EXPAND; VECTOR_2]);;

(* The south chart is the reflection of the north chart.                      *)

let bel_refl3 = new_definition
 `bel_refl3 (x:real^3) = (lambda i. if i = 3 then --(x$3) else x$i):real^3`;;

let BEL_REFL3_COMPONENTS = prove
 (`!x:real^3. bel_refl3 x$1 = x$1 /\ bel_refl3 x$2 = x$2 /\ bel_refl3 x$3 = --(x$3)`,
  SIMP_TAC[bel_refl3; LAMBDA_BETA; DIMINDEX_3; ARITH]);;

let BEL_REFL3_LINEAR = prove
 (`linear bel_refl3`,
  REWRITE_TAC[linear; CART_EQ; DIMINDEX_3; FORALL_3; BEL_REFL3_COMPONENTS;
              VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC);;

let BEL_REFL3_DOT = prove
 (`!x y:real^3. bel_refl3 x dot bel_refl3 y = x dot y /\ bel_refl3(bel_refl3 x) = x`,
  REWRITE_TAC[DOT_3; CART_EQ; DIMINDEX_3; FORALL_3; BEL_REFL3_COMPONENTS] THEN
  REAL_ARITH_TAC);;

let BEL_Q_FORM = prove
 (`!y. stereo2_s_inv y = bel_refl3(stereo2_n_inv y)`,
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; BEL_REFL3_COMPONENTS;
              STEX_STEREO2_S_INV_COMPONENTS; STEX_STEREO2_N_INV_COMPONENTS] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_LNEG] THEN REAL_ARITH_TAC);;

let bel_dQ = new_definition
 `bel_dQ (y:real^2) (h:real^2) = bel_refl3(bel_dP y h)`;;

let BEL_Q_HAS_DERIVATIVE = prove
 (`!y. (stereo2_s_inv has_derivative bel_dQ y) (at y)`,
  GEN_TAC THEN
  SUBGOAL_THEN `stereo2_s_inv = bel_refl3 o stereo2_n_inv /\
                bel_dQ y = bel_refl3 o bel_dP y`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; BEL_Q_FORM; bel_dQ]; ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN
  SIMP_TAC[BEL_P_HAS_DERIVATIVE; HAS_DERIVATIVE_LINEAR; BEL_REFL3_LINEAR]);;

let BEL_Q_CONF = prove
 (`!y h k. bel_dQ y h dot bel_dQ y k = (&4 / (norm y pow 2 + &1) pow 2) * (h dot k)`,
  REWRITE_TAC[bel_dQ; BEL_REFL3_DOT; BEL_P_CONF]);;

let BEL_Q_TANG = prove
 (`!y h. stereo2_s_inv y dot bel_dQ y h = &0`,
  REWRITE_TAC[bel_dQ; BEL_Q_FORM; BEL_REFL3_DOT; BEL_P_TANG]);;

let BEL_DQ_LINEAR = prove
 (`!y. linear(bel_dQ y)`,
  MESON_TAC[BEL_Q_HAS_DERIVATIVE; has_derivative]);;

let BEL_Q_SPAN = prove
 (`!z v. v dot stereo2_s_inv z = &0 ==> ?a. bel_dQ z a = v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`z:real^2`; `bel_refl3 v`] BEL_P_SPAN) THEN ANTS_TAC THENL
   [UNDISCH_TAC `v dot stereo2_s_inv z = &0` THEN
    REWRITE_TAC[BEL_Q_FORM] THEN
    MESON_TAC[BEL_REFL3_DOT];
    MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[bel_dQ] THEN
    MESON_TAC[BEL_REFL3_DOT]]);;

(* The transition between the two charts and the poles.                       *)

let BEL_INV_CNJ_CMUL = prove
 (`!u. inv(cnj u) = inv(norm u pow 2) % u`,
  GEN_TAC THEN REWRITE_TAC[COMPLEX_CMUL; CX_INV; CX_POW; COMPLEX_NORM_POW_2] THEN
  ASM_CASES_TAC `u = Cx(&0)` THEN
  ASM_REWRITE_TAC[CNJ_CX; COMPLEX_INV_0; COMPLEX_MUL_RZERO] THEN
  SUBGOAL_THEN `~(cnj u = Cx(&0))` MP_TAC THENL [ASM_REWRITE_TAC[CNJ_EQ_0]; ALL_TAC] THEN
  UNDISCH_TAC `~(u = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD);;

let BEL_QT_P = prove
 (`!u. ~(u = Cx(&0)) ==> stereo2_s_inv(inv(cnj u)) = stereo2_n_inv u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[BEL_INV_CNJ_CMUL] THEN
  SUBGOAL_THEN `&0 < norm(u:complex) pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; COMPLEX_NORM_NZ]; ALL_TAC] THEN
  ABBREV_TAC `n2 = norm(u:complex) pow 2` THEN
  SUBGOAL_THEN `norm(inv n2 % (u:complex)) pow 2 = inv n2` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_MUL; REAL_POW_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
    UNDISCH_TAC `&0 < n2` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv n2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; STEX_STEREO2_S_INV_COMPONENTS;
                  STEX_STEREO2_N_INV_COMPONENTS; VECTOR_MUL_COMPONENT] THEN
  UNDISCH_TAC `&0 < inv n2` THEN UNDISCH_TAC `&0 < n2` THEN CONV_TAC REAL_FIELD);;

let BEL_P_ZERO = prove
 (`stereo2_n_inv(Cx(&0)) = --(basis 3) /\ stereo2_s_inv(Cx(&0)) = basis 3`,
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; STEX_STEREO2_S_INV_COMPONENTS;
              STEX_STEREO2_N_INV_COMPONENTS; VECTOR_NEG_COMPONENT; BEL_BASIS3_COMPONENTS;
              GSYM COMPLEX_VEC_0; NORM_0; VEC_COMPONENT] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let BEL_T_INVOL = prove
 (`!w. inv(cnj(inv(cnj w))) = w /\ (inv(cnj w) = Cx(&0) <=> w = Cx(&0))`,
  REWRITE_TAC[CNJ_INV; CNJ_CNJ; COMPLEX_INV_INV; COMPLEX_INV_EQ_0; CNJ_EQ_0]);;

let BEL_PQ_T = prove
 (`!w. ~(w = Cx(&0)) ==> stereo2_s_inv w = stereo2_n_inv(inv(cnj w))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `inv(cnj w)` BEL_QT_P) THEN ASM_REWRITE_TAC[BEL_T_INVOL]);;

let BEL_S_OF_P = prove
 (`!u. ~(u = Cx(&0)) ==> stereo2_s(stereo2_n_inv u) = inv(cnj u)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP BEL_QT_P) THEN
  REWRITE_TAC[STEX_STEREO2_S_RIGHT]);;

let BEL_N_OF_Q = prove
 (`!w. ~(w = Cx(&0)) ==> stereo2_n(stereo2_s_inv w) = inv(cnj w)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(SUBST1_TAC o MATCH_MP BEL_PQ_T) THEN
  REWRITE_TAC[STEX_STEREO2_N_RIGHT]);;


(* ========================================================================= *)
(* Pulled-back metrics on planar charts and the Beltrami                     *)
(* coefficient of a metric: a solution of the Beltrami equation is conformal *)
(* from the metric to the Euclidean one.                                      *)
(* ========================================================================= *)

let bel_pull = new_definition
 `bel_pull (M:real^3->real^3^3) (X:real^2->real^3) (w:real^2) =
    (lambda i j. partial_derivative i X w dot (M (X w) ** partial_derivative j X w)):real^2^2`;;

let bel_mu = new_definition
 `bel_mu (A:real^2^2) =
    complex(A$1$1 - A$2$2, A$1$2 + A$2$1) /
    Cx(A$1$1 + A$2$2 + &2 * sqrt(A$1$1 * A$2$2 - ((A$1$2 + A$2$1) / &2) pow 2))`;;

let BEL_QUAD_2 = prove
 (`!(A:real^2^2) a b.
        a dot (A ** b) = a$1 * b$1 * A$1$1 + a$1 * b$2 * A$1$2 +
                         a$2 * b$1 * A$2$1 + a$2 * b$2 * A$2$2`,
  SIMP_TAC[DOT_2; matrix_vector_mul; LAMBDA_BETA; DIMINDEX_2; ARITH; SUM_2] THEN
  REAL_ARITH_TAC);;

let BEL_PULL_COMPONENT = prove
 (`!M X w i j. 1 <= i /\ i <= 2 /\ 1 <= j /\ j <= 2
        ==> bel_pull M X w$i$j =
            partial_derivative i X w dot (M (X w) ** partial_derivative j X w)`,
  SIMP_TAC[bel_pull; LAMBDA_BETA; DIMINDEX_2]);;

let BEL_PULL_QUAD = prove
 (`!M X w a b.
        X differentiable at w
        ==> a dot (bel_pull M X w ** b) =
            frechet_derivative X (at w) a dot
            (M (X w) ** frechet_derivative X (at w) b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `linear(frechet_derivative (X:real^2->real^3) (at w))` ASSUME_TAC THENL
   [ASM_MESON_TAC[FRECHET_DERIVATIVE_WORKS; has_derivative]; ALL_TAC] THEN
  MP_TAC(ISPECL [`frechet_derivative (X:real^2->real^3) (at w)`; `a:real^2`]
                BEL_LINEAR_BASIS_EXPAND) THEN
  MP_TAC(ISPECL [`frechet_derivative (X:real^2->real^3) (at w)`; `b:real^2`]
                BEL_LINEAR_BASIS_EXPAND) THEN
  ASM_REWRITE_TAC[DIMINDEX_2; VSUM_2] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  SIMP_TAC[BEL_QUAD_2; BEL_PULL_COMPONENT; ARITH; partial_derivative] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL;
              DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL] THEN
  REAL_ARITH_TAC);;

let BEL_MU_ALG = prove
 (`!A:real^2^2.
        A$1$2 = A$2$1 /\ &0 < A$1$1 /\ &0 < A$1$1 * A$2$2 - A$1$2 pow 2
        ==> norm(bel_mu A) < &1 /\
            ?s. &0 < s /\
                !u v. Re(cnj(u + bel_mu A * cnj u) * (v + bel_mu A * cnj v)) =
                      (&4 / s) * (u dot (A ** v))`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[bel_mu; BEL_QUAD_2] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
  ABBREV_TAC `a = (A:real^2^2)$1$1` THEN ABBREV_TAC `b = (A:real^2^2)$1$2` THEN
  ABBREV_TAC `c = (A:real^2^2)$2$2` THEN
  REWRITE_TAC[REAL_ARITH `(b + b) / &2 = b`] THEN
  ABBREV_TAC `D = sqrt(a * c - b pow 2)` THEN
  SUBGOAL_THEN `&0 < D /\ D pow 2 = a * c - b pow 2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `a * c <= &0` MP_TAC THENL
     [REWRITE_TAC[REAL_ARITH `x <= &0 <=> &0 <= --x`; GSYM REAL_MUL_RNEG] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MP_TAC(SPEC `b:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `s = a + c + &2 * D` THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [EXPAND_TAC "s" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `complex(a - c,b + b) / Cx s = complex((a - c) / s,(b + b) / s)`
  SUBST1_TAC THENL
   [REWRITE_TAC[COMPLEX_EQ; RE_DIV_CX; IM_DIV_CX; RE; IM]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[complex_norm; RE; IM] THEN MATCH_MP_TAC REAL_LT_LSQRT THEN
    REWRITE_TAC[REAL_POS; REAL_POW_DIV; REAL_POW_ONE] THEN
    REWRITE_TAC[real_div] THEN REWRITE_TAC[GSYM REAL_ADD_RDISTRIB] THEN
    REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_POW_LT; REAL_MUL_LID] THEN
    SUBGOAL_THEN `&0 < D * (a + c)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "s" THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `s:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM RE_DEF; GSYM IM_DEF; complex_mul; complex_add; cnj; RE; IM] THEN
  UNDISCH_TAC `a + c + &2 * D = s` THEN UNDISCH_TAC `D pow 2 = a * c - b pow 2` THEN
  UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD);;

let BEL_BELTRAMI_CONF = prove
 (`!f:complex->complex z A.
        f differentiable at z /\
        A$1$2 = A$2$1 /\ &0 < A$1$1 /\ &0 < A$1$1 * A$2$2 - A$1$2 pow 2 /\
        wirtinger_dbar f z = bel_mu A * wirtinger_dz f z /\
        ~(wirtinger_dz f z = Cx(&0))
        ==> ?lam. &0 < lam /\
                  !u v. frechet_derivative f (at z) u dot frechet_derivative f (at z) v =
                        lam * (u dot (A ** v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `A:real^2^2` BEL_MU_ALG) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `norm(wirtinger_dz (f:complex->complex) z) pow 2 * (&4 / s)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT; COMPLEX_NORM_NZ] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN
  MP_TAC(ISPECL [`f:complex->complex`; `frechet_derivative (f:complex->complex) (at z)`;
                 `z:complex`] FRECHET_WIRTINGER) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[FRECHET_DERIVATIVE_WORKS]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `a = wirtinger_dz (f:complex->complex) z` THEN
  ABBREV_TAC `m = bel_mu A` THEN
  REWRITE_TAC[DOT_COMPLEX_MUL_CNJ; COMPLEX_SQNORM] THEN
  REWRITE_TAC[complex_mul; complex_add; cnj; RE; IM] THEN CONV_TAC REAL_RING);;

let BEL_POSDEF_2 = prove
 (`!A:real^2^2.
        A$1$2 = A$2$1 /\ (!a. ~(a = vec 0) ==> &0 < a dot (A ** a))
        ==> &0 < A$1$1 /\ &0 < A$1$1 * A$2$2 - A$1$2 pow 2`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (A:real^2^2)$1$1` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `basis 1:real^2`) THEN
    SIMP_TAC[BASIS_NONZERO; DIMINDEX_2; ARITH; BEL_QUAD_2; BASIS_COMPONENT] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `vector[--((A:real^2^2)$1$2); A$1$1]:real^2`) THEN
  REWRITE_TAC[BEL_QUAD_2; VECTOR_2] THEN ANTS_TAC THENL
   [REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VEC_COMPONENT] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 < (A:real^2^2)$1$1 * (A$1$1 * A$2$2 - A$1$2 pow 2)` MP_TAC THENL
   [POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LT_MUL_EQ]]);;

let BEL_INV_DERIV = prove
 (`!f g:real^N->real^N w.
        f differentiable at (g w) /\ g differentiable at w /\ (!w. f(g w) = w)
        ==> !h. frechet_derivative f (at (g w)) (frechet_derivative g (at w) h) = h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^N->real^N`; `f:real^N->real^N`;
                 `frechet_derivative (g:real^N->real^N) (at w)`;
                 `frechet_derivative (f:real^N->real^N) (at ((g:real^N->real^N) w))`;
                 `w:real^N`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
  SUBGOAL_THEN `(f:real^N->real^N) o (g:real^N->real^N) = (\w. w)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`\w:real^N. w`;
                 `frechet_derivative (f:real^N->real^N) (at ((g:real^N->real^N) w)) o
                  frechet_derivative g (at w)`;
                 `\h:real^N. h`; `w:real^N`] FRECHET_DERIVATIVE_UNIQUE_AT) THEN
  ASM_REWRITE_TAC[HAS_DERIVATIVE_ID] THEN REWRITE_TAC[FUN_EQ_THM; o_THM]);;

let BEL_INV_CONF = prove
 (`!f g:complex->complex z (A:real^2^2) lam.
        (!u v. frechet_derivative f (at z) u dot frechet_derivative f (at z) v =
               lam * (u dot (A ** v))) /\
        (!h. frechet_derivative f (at z) (frechet_derivative g (at (f z)) h) = h) /\
        &0 < lam
        ==> !h k. frechet_derivative g (at (f z)) h dot
                  (A ** frechet_derivative g (at (f z)) k) = inv lam * (h dot k)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`frechet_derivative (g:complex->complex) (at (f(z:complex))) h`;
                                `frechet_derivative (g:complex->complex) (at (f(z:complex))) k`] o
                check (fun th -> can (find_term ((=) `lam:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD);;

let BEL_PULL_COMPOSE_QUAD = prove
 (`!M (X:real^2->real^3) (f:real^2->real^2) w a b.
        f differentiable at w /\ X differentiable at (f w)
        ==> a dot (bel_pull M (X o f) w ** b) =
            frechet_derivative f (at w) a dot
            (bel_pull M X (f w) ** frechet_derivative f (at w) b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((X:real^2->real^3) o (f:real^2->real^2)) differentiable at w` ASSUME_TAC THENL
   [MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[BEL_PULL_QUAD; o_THM] THEN
  SUBGOAL_THEN `frechet_derivative ((X:real^2->real^3) o (f:real^2->real^2)) (at w) =
                frechet_derivative X (at (f w)) o frechet_derivative f (at w)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    REWRITE_TAC[o_THM]]);;

let BEL_MU_ZERO = prove
 (`!A:real^2^2 c. (!u v. u dot (A ** v) = c * (u dot v)) ==> bel_mu A = Cx(&0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(A:real^2^2)$1$1 = c /\ A$2$2 = c /\ A$1$2 = &0 /\ A$2$1 = &0`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      MP_TAC(SPECL [`basis 1:real^2`; `basis 1:real^2`] th) THEN
      MP_TAC(SPECL [`basis 2:real^2`; `basis 2:real^2`] th) THEN
      MP_TAC(SPECL [`basis 1:real^2`; `basis 2:real^2`] th) THEN
      MP_TAC(SPECL [`basis 2:real^2`; `basis 1:real^2`] th)) THEN
    SIMP_TAC[BEL_QUAD_2; BASIS_COMPONENT; DIMINDEX_2; ARITH; DOT_BASIS_BASIS] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[bel_mu; REAL_SUB_REFL; REAL_ADD_LID] THEN
    REWRITE_TAC[GSYM CX_DEF; complex_div; COMPLEX_MUL_LZERO]]);;

let BEL_CDIFF_CONF = prove
 (`!f:complex->complex z u v.
        f complex_differentiable at z
        ==> frechet_derivative f (at z) u dot frechet_derivative f (at z) v =
            norm(complex_derivative f z) pow 2 * (u dot v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE] THEN
  REWRITE_TAC[has_complex_derivative] THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[DOT_COMPLEX_MUL_CNJ; COMPLEX_SQNORM] THEN
  REWRITE_TAC[complex_mul; cnj; RE; IM] THEN CONV_TAC REAL_RING);;


(* ========================================================================= *)
(* General family lemmas for the sphere construction: local                  *)
(* gluing of families, pullbacks of the metric field, and the Beltrami       *)
(* coefficient of a family of metrics.                                       *)
(* ========================================================================= *)

let bel_hyp = new_definition
 `bel_hyp (G:real->real^3->real^3^3) <=>
    (!i j m. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
             ==> bel_jfam m {z:real^3 | ~(z = vec 0)}
                   (\t z. lift(G t (inv(norm z) % z)$i$j))) /\
    (!t y. t IN real_interval[&0,&1] /\ y IN sphere(vec 0,&1) ==> transp(G t y) = G t y) /\
    (?c. &0 < c /\
         !t y v. t IN real_interval[&0,&1] /\ y IN sphere(vec 0,&1) /\ v dot y = &0
                 ==> c * (v dot v) <= v dot (G t y ** v))`;;

let BEL_JFAM_LOCAL = prove
 (`!m U (ff:real->real^M->real^N).
        open U /\
        (!x. x IN U ==> ?V. open V /\ x IN V /\ bel_jfam m (U INTER V) ff)
        ==> bel_jfam m U ff`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[bel_jfam] THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[smooth_map_on] THEN
    X_GEN_TAC `n:num` THEN ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_LOCAL_OPEN] THEN
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `V:real^M->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `U INTER V:real^M->bool` THEN
    ASM_SIMP_TAC[OPEN_INTER; IN_INTER; INTER_SUBSET] THEN
    UNDISCH_TAC `bel_jfam m (U INTER V) (ff:real->real^M->real^N)` THEN
    ASM_SIMP_TAC[bel_jfam; smooth_map_on];
    ALL_TAC] THEN
  X_GEN_TAC `l:num list` THEN STRIP_TAC THEN MATCH_MP_TAC BEL_CONT_LOCAL THEN
  X_GEN_TAC `x:real^(M,1)finite_sum` THEN REWRITE_TAC[BEL_IN_DOM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `fstcart(x:real^(M,1)finite_sum)`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `V:real^M->bool` THEN
  SIMP_TAC[bel_jfam] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

let BEL_PULL_LOCAL = prove
 (`!M (X:real^2->real^3) Y U w.
        open U /\ w IN U /\ (!x. x IN U ==> X x = Y x)
        ==> bel_pull M X w = bel_pull M Y w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bel_pull] THEN
  SUBGOAL_THEN `(X:real^2->real^3) w = Y w /\
                !i. partial_derivative i X w = partial_derivative i Y w`
  (fun th -> REWRITE_TAC[th]) THEN
  ASM_SIMP_TAC[] THEN GEN_TAC THEN MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN
  EXISTS_TAC `U:real^2->bool` THEN ASM_SIMP_TAC[]);;

let BEL_LIFT_QUAD = prove
 (`!f g:real^N (A:real^N^N).
        lift(f dot (A ** g)) =
        vsum(1..dimindex(:N))
          (\k. vsum(1..dimindex(:N))
                 (\l. drop(lift(f$k)) % drop(lift(A$k$l)) % lift(g$l)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dot; LIFT_SUM; o_DEF] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT; dot; LIFT_DROP; GSYM LIFT_CMUL] THEN
  REWRITE_TAC[GSYM SUM_LMUL; LIFT_SUM; o_DEF; REAL_MUL_ASSOC]);;

let BEL_JFAM_BILIN = prove
 (`!m U (f:real->real^M->real^N) g (MM:real->real^M->real^N^N).
        open U /\ bel_jfam m U f /\ bel_jfam m U g /\
        (!k l. 1 <= k /\ k <= dimindex(:N) /\ 1 <= l /\ l <= dimindex(:N)
               ==> bel_jfam m U (\t x. lift(MM t x$k$l)))
        ==> bel_jfam m U (\t x. lift(f t x dot (MM t x ** g t x)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[BEL_LIFT_QUAD] THEN
  MATCH_MP_TAC BEL_JFAM_VSUM THEN ASM_REWRITE_TAC[IN_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC BEL_JFAM_VSUM THEN ASM_REWRITE_TAC[IN_NUMSEG] THEN
  X_GEN_TAC `l:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC BEL_JFAM_MUL_DROP THEN ASM_SIMP_TAC[BEL_JFAM_COMPONENT] THEN
  MATCH_MP_TAC BEL_JFAM_MUL_DROP THEN ASM_SIMP_TAC[BEL_JFAM_COMPONENT]);;

let BEL_JFAM_PULL = prove
 (`!G U (X:real->real^2->real^3).
        bel_hyp G /\ open U /\ (!m. bel_jfam m U X) /\
        (!t w. t IN real_interval[&0,&1] /\ w IN U ==> X t w IN sphere(vec 0,&1))
        ==> !i j m. 1 <= i /\ i <= 2 /\ 1 <= j /\ j <= 2
                    ==> bel_jfam m U (\t w. lift(bel_pull (G t) (X t) w$i$j))`,
  REWRITE_TAC[bel_hyp] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC BEL_JFAM_EQ THEN
  EXISTS_TAC `\t w. lift(partial_derivative i ((X:real->real^2->real^3) t) w dot
                         ((\t w. (G:real->real^3->real^3^3) t
                                   (inv(norm(X t w)) % X t w)) t w **
                          partial_derivative j (X t) w))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[BEL_PULL_COMPONENT] THEN
    SUBGOAL_THEN `inv(norm((X:real->real^2->real^3) t z)) % X t z = X t z`
    (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `norm((X:real->real^2->real^3) t z) = &1`
    (fun th -> REWRITE_TAC[th; REAL_INV_1; VECTOR_MUL_LID]) THEN
    REWRITE_TAC[GSYM IN_SPHERE_0] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC BEL_JFAM_BILIN THEN ASM_SIMP_TAC[BEL_JFAM_PD; DIMINDEX_2; DIMINDEX_3; ETA_AX] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `l:num`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:num`; `U:real^2->bool`; `{y:real^3 | ~(y = vec 0)}`;
                 `\t y. lift((G:real->real^3->real^3^3) t (inv(norm y) % y)$k$l)`;
                 `X:real->real^2->real^3`] BEL_JFAM_COMPOSE) THEN
  ASM_SIMP_TAC[OPEN_NONZERO; o_DEF; IN_ELIM_THM] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `w:real^2`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(X:real->real^2->real^3) t w IN sphere(vec 0,&1)` MP_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_SPHERE_0] THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o AP_TERM `norm:real^3->real`) THEN
  ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC);;

(* Real-valued families written with lift.                                    *)

let BEL_JFAM_RADD = prove
 (`!m U (a:real->real^M->real) b.
        open U /\ bel_jfam m U (\t x. lift(a t x)) /\ bel_jfam m U (\t x. lift(b t x))
        ==> bel_jfam m U (\t x. lift(a t x + b t x)) /\
            bel_jfam m U (\t x. lift(a t x - b t x)) /\
            bel_jfam m U (\t x. lift(a t x * b t x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_ADD; LIFT_SUB] THENL
   [MATCH_MP_TAC BEL_JFAM_ADD THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC BEL_JFAM_SUB THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[LIFT_CMUL] THEN
    MP_TAC(ISPECL [`m:num`; `U:real^M->bool`; `\t x. lift((a:real->real^M->real) t x)`;
                   `\t x. lift((b:real->real^M->real) t x)`] BEL_JFAM_MUL_DROP) THEN
    ASM_REWRITE_TAC[LIFT_DROP]]);;

let BEL_JFAM_RCMUL = prove
 (`!m U c (a:real->real^M->real).
        open U /\ bel_jfam m U (\t x. lift(a t x))
        ==> bel_jfam m U (\t x. lift(c * a t x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_CMUL] THEN
  MP_TAC(ISPECL [`m:num`; `U:real^M->bool`; `c:real`;
                 `\t x. lift((a:real->real^M->real) t x)`] BEL_JFAM_CMUL) THEN
  ASM_REWRITE_TAC[]);;

let BEL_JFAM_RSQRT = prove
 (`!m U (a:real->real^M->real).
        open U /\ bel_jfam m U (\t x. lift(a t x)) /\
        (!t x. t IN real_interval[&0,&1] /\ x IN U ==> &0 < a t x)
        ==> bel_jfam m U (\t x. lift(sqrt(a t x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:num`; `U:real^M->bool`; `{x:real^1 | &0 < drop x}`;
                 `\x:real^1. lift(sqrt(drop x))`;
                 `\t x. lift((a:real->real^M->real) t x)`] BEL_JFAM_SMOOTH_O) THEN
  ASM_SIMP_TAC[o_DEF; LIFT_DROP; IN_ELIM_THM; OPEN_DROP_POSITIVE] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`{x:real^1 | &0 < drop x}`; `\x:real^1. x`] SMOOTH_MAP_ON_LIFT_SQRT) THEN
  REWRITE_TAC[OPEN_DROP_POSITIVE; SMOOTH_MAP_ON_ID; IN_ELIM_THM] THEN
  REWRITE_TAC[ETA_AX]);;

let BEL_JFAM_CX = prove
 (`!m U (a:real->real^M->real).
        open U /\ bel_jfam m U (\t x. lift(a t x)) ==> bel_jfam m U (\t x. Cx(a t x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:num`; `U:real^M->bool`; `\x:real^1. Cx(drop x)`;
                 `\t x. lift((a:real->real^M->real) t x)`] BEL_JFAM_LINEAR_O) THEN
  ASM_REWRITE_TAC[BEL_LINEAR_CX_DROP; o_DEF; LIFT_DROP]);;

let BEL_MU_FORM = prove
 (`!A:real^2^2. bel_mu A =
     (Cx(A$1$1 - A$2$2) + ii * Cx(A$1$2 + A$2$1)) *
     inv(Cx(A$1$1 + A$2$2 + &2 * sqrt(A$1$1 * A$2$2 - ((A$1$2 + A$2$1) / &2) pow 2)))`,
  GEN_TAC THEN REWRITE_TAC[bel_mu; complex_div] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[COMPLEX_EQ; RE_ADD; IM_ADD; RE_CX; IM_CX; RE_MUL_II; IM_MUL_II; RE; IM] THEN
  REAL_ARITH_TAC);;

let BEL_JFAM_MU = prove
 (`!m U (AA:real->real^2->real^2^2).
        open U /\
        (!i j. 1 <= i /\ i <= 2 /\ 1 <= j /\ j <= 2
               ==> bel_jfam m U (\t w. lift(AA t w$i$j))) /\
        (!t w. t IN real_interval[&0,&1] /\ w IN U
               ==> &0 < AA t w$1$1 * AA t w$2$2 - ((AA t w$1$2 + AA t w$2$1) / &2) pow 2 /\
                   &0 < AA t w$1$1 + AA t w$2$2)
        ==> bel_jfam m U (\t w. bel_mu (AA t w))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[BEL_MU_FORM] THEN
  FIRST_X_ASSUM(fun th ->
    MAP_EVERY (fun (i,j) -> ASSUME_TAC(REWRITE_RULE[ARITH] (SPECL [i;j] th)))
      [`1`,`1`; `1`,`2`; `2`,`1`; `2`,`2`]) THEN
  SUBGOAL_THEN
   `bel_jfam m U (\t w. lift((AA:real->real^2->real^2^2) t w$1$1 * AA t w$2$2 -
                              ((AA t w$1$2 + AA t w$2$1) / &2) pow 2))`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN
    MP_TAC(ISPECL [`m:num`; `U:real^2->bool`;
                   `\t w. (AA:real->real^2->real^2^2) t w$1$1 * AA t w$2$2`;
                   `\t w. ((AA:real->real^2->real^2^2) t w$1$2 + AA t w$2$1) / &2 *
                          (AA t w$1$2 + AA t w$2$1) / &2`] BEL_JFAM_RADD) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`m:num`; `U:real^2->bool`;
                     `\t w. (AA:real->real^2->real^2^2) t w$1$1`;
                     `\t w. (AA:real->real^2->real^2^2) t w$2$2`] BEL_JFAM_RADD) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `bel_jfam m U (\t w. lift(((AA:real->real^2->real^2^2) t w$1$2 +
                                           AA t w$2$1) / &2))` ASSUME_TAC THENL
     [REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      MATCH_MP_TAC BEL_JFAM_RCMUL THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`m:num`; `U:real^2->bool`;
                     `\t w. (AA:real->real^2->real^2^2) t w$1$2`;
                     `\t w. (AA:real->real^2->real^2^2) t w$2$1`] BEL_JFAM_RADD) THEN
      ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`m:num`; `U:real^2->bool`;
                     `\t w. ((AA:real->real^2->real^2^2) t w$1$2 + AA t w$2$1) / &2`;
                     `\t w. ((AA:real->real^2->real^2^2) t w$1$2 + AA t w$2$1) / &2`]
                    BEL_JFAM_RADD) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC BEL_JFAM_CMUL_FUN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC BEL_JFAM_ADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC BEL_JFAM_CX THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`m:num`; `U:real^2->bool`;
                     `\t w. (AA:real->real^2->real^2^2) t w$1$1`;
                     `\t w. (AA:real->real^2->real^2^2) t w$2$2`] BEL_JFAM_RADD) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC BEL_JFAM_CLMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC BEL_JFAM_CX THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`m:num`; `U:real^2->bool`;
                     `\t w. (AA:real->real^2->real^2^2) t w$1$2`;
                     `\t w. (AA:real->real^2->real^2^2) t w$2$1`] BEL_JFAM_RADD) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC BEL_JFAM_CINV THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC BEL_JFAM_CX THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ADD_ASSOC] THEN
    MP_TAC(ISPECL [`m:num`; `U:real^2->bool`;
                   `\t w. (AA:real->real^2->real^2^2) t w$1$1 + AA t w$2$2`;
                   `\t w. &2 * sqrt((AA:real->real^2->real^2^2) t w$1$1 * AA t w$2$2 -
                                    ((AA t w$1$2 + AA t w$2$1) / &2) pow 2)`]
                  BEL_JFAM_RADD) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`m:num`; `U:real^2->bool`;
                     `\t w. (AA:real->real^2->real^2^2) t w$1$1`;
                     `\t w. (AA:real->real^2->real^2^2) t w$2$2`] BEL_JFAM_RADD) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC BEL_JFAM_RCMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC BEL_JFAM_RSQRT THEN ASM_SIMP_TAC[]];
    REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[CX_INJ] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < a + b /\ &0 < s ==> ~(a + b + &2 * s = &0)`) THEN
    ASM_SIMP_TAC[SQRT_POS_LT]]);;

(* Uniform bounds below 1, positive definite pullbacks.                       *)

let BEL_COMPACT_LT1 = prove
 (`!(f:real^N->complex) K.
        compact K /\ f continuous_on K /\ (!x. x IN K ==> norm(f x) < &1)
        ==> ?k. &0 <= k /\ k < &1 /\ !x. x IN K ==> norm(f x) <= k`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `K:real^N->bool = {}` THENL
   [EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^N. norm((f:real^N->complex) x)`; `K:real^N->bool`]
                CONTINUOUS_ATTAINS_SUP) THEN
  ASM_REWRITE_TAC[o_DEF] THEN ANTS_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `norm((f:real^N->complex) x0)` THEN ASM_SIMP_TAC[NORM_POS_LE]);;

let bel_pdm = new_definition
 `bel_pdm (A:real^2^2) <=>
    A$1$2 = A$2$1 /\ &0 < A$1$1 /\ &0 < A$2$2 /\ &0 < A$1$1 * A$2$2 - A$1$2 pow 2`;;

let BEL_PDM_MU = prove
 (`!A:real^2^2.
        bel_pdm A
        ==> norm(bel_mu A) < &1 /\
            &0 < A$1$1 * A$2$2 - ((A$1$2 + A$2$1) / &2) pow 2 /\ &0 < A$1$1 + A$2$2`,
  GEN_TAC THEN REWRITE_TAC[bel_pdm] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `A:real^2^2` BEL_MU_ALG) THEN ASM_SIMP_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
  REWRITE_TAC[REAL_ARITH `(b + b) / &2 = b`] THEN ASM_REAL_ARITH_TAC);;

let BEL_PULL_SYM = prove
 (`!M (X:real^2->real^3) w.
        transp(M (X w)) = M (X w) ==> bel_pull M X w$1$2 = bel_pull M X w$2$1`,
  REPEAT STRIP_TAC THEN SIMP_TAC[BEL_PULL_COMPONENT; ARITH] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV) [GSYM th]) THEN
  REWRITE_TAC[DOT_MATRIX_TRANSP_RMUL] THEN REWRITE_TAC[DOT_SYM]);;

let BEL_PULL_PDM = prove
 (`!M (X:real^2->real^3) w c.
        X differentiable at w /\ norm(X w) = &1 /\
        (!h. X w dot frechet_derivative X (at w) h = &0) /\
        (!h. ~(h = vec 0) ==> ~(frechet_derivative X (at w) h = vec 0)) /\
        transp(M (X w)) = M (X w) /\ &0 < c /\
        (!v. v dot X w = &0 ==> c * (v dot v) <= v dot (M (X w) ** v))
        ==> bel_pdm (bel_pull M X w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!a. ~(a = vec 0) ==> &0 < a dot (bel_pull M (X:real^2->real^3) w ** a)`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:real^2` THEN DISCH_TAC THEN ASM_SIMP_TAC[BEL_PULL_QUAD] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `c * (frechet_derivative (X:real^2->real^3) (at w) a dot
                     frechet_derivative X (at w) a)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[DOT_POS_LT] THEN ASM_SIMP_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `bel_pull M (X:real^2->real^3) w` BEL_POSDEF_2) THEN
  ASM_SIMP_TAC[BEL_PULL_SYM; bel_pdm] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `basis 2:real^2`) THEN
  SIMP_TAC[BASIS_NONZERO; DIMINDEX_2; ARITH; BEL_QUAD_2; BASIS_COMPONENT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC);;

(* One normalized Beltrami step for a family of coefficients.                 *)

let bel_nf = new_definition
 `bel_nf (mu:real->complex->complex) t z = bel_fsol (mu t) z - bel_fsol (mu t) (Cx(&0))`;;

let bel_nk = new_definition
 `bel_nk (mu:real->complex->complex) t = bel_hinv (bel_nf mu t)`;;

let BEL_SHIFT_FRECHET = prove
 (`!f:complex->complex c z.
        f differentiable at z
        ==> frechet_derivative (\z. f z - c) (at z) = frechet_derivative f (at z)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MP_TAC(ISPECL [`f:complex->complex`; `frechet_derivative (f:complex->complex) (at z)`;
                 `\z:complex. c:complex`; `\h:complex. vec 0:complex`; `at (z:complex)`]
                HAS_DERIVATIVE_SUB) THEN
  ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS; HAS_DERIVATIVE_CONST] THEN
  REWRITE_TAC[VECTOR_SUB_RZERO; ETA_AX]);;

let BEL_SHIFT_WIRT = prove
 (`!f:complex->complex c z.
        f differentiable at z
        ==> wirtinger_dbar (\z. f z - c) z = wirtinger_dbar f z /\
            wirtinger_dz (\z. f z - c) z = wirtinger_dz f z /\
            det(matrix(frechet_derivative (\z. f z - c) (at z))) =
            det(matrix(frechet_derivative f (at z)))`,
  SIMP_TAC[wirtinger_dbar; wirtinger_dz; jacobian; BEL_SHIFT_FRECHET]);;

let BEL_SHIFT_HOMEO = prove
 (`!f g:complex->complex c.
        homeomorphism ((:complex),(:complex)) (f,g)
        ==> homeomorphism ((:complex),(:complex)) ((\z. f z - c),(\w. g(w + c)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HOMEOMORPHISM; IN_UNIV; SUBSET_UNIV] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[COMPLEX_RING `(w + c) - c:complex = w`;
                                 COMPLEX_RING `(x - c) + c:complex = x`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[CONTINUOUS_ON_CONST; ETA_AX];
    SUBGOAL_THEN `(\w:complex. (g:complex->complex)(w + c)) = g o (\w. w + c)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:complex)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV]]);;

let BEL_NF_PROPS = prove
 (`!rho (mu:complex->complex) k.
        smooth_map_on (:complex) mu /\ bel_supp rho mu /\ (!z. norm(mu z) <= k) /\ k < &1
        ==> smooth_map_on (:complex) (\z. bel_fsol mu z - bel_fsol mu (Cx(&0))) /\
            (?g. homeomorphism ((:complex),(:complex))
                   ((\z. bel_fsol mu z - bel_fsol mu (Cx(&0))),g)) /\
            (!z. wirtinger_dbar (\z. bel_fsol mu z - bel_fsol mu (Cx(&0))) z =
                 mu z * wirtinger_dz (\z. bel_fsol mu z - bel_fsol mu (Cx(&0))) z /\
                 ~(wirtinger_dz (\z. bel_fsol mu z - bel_fsol mu (Cx(&0))) z = Cx(&0)) /\
                 &0 < det(matrix(frechet_derivative
                                   (\z. bel_fsol mu z - bel_fsol mu (Cx(&0))) (at z)))) /\
            (!z. rho < norm z
                 ==> (\z. bel_fsol mu z - bel_fsol mu (Cx(&0))) complex_differentiable at z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rho:real`; `mu:complex->complex`; `k:real`] BEL_FSOL_PROPS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC))) THEN
  SUBGOAL_THEN `!z. bel_fsol (mu:complex->complex) differentiable at z` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(:complex)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  ASM_SIMP_TAC[BEL_SHIFT_WIRT; ETA_AX] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST; ETA_AX];
    MP_TAC(ISPECL [`rho:real`; `mu:complex->complex`; `k:real`] BEL_FSOL_HOMEO) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `g:complex->complex`) THEN
    EXISTS_TAC `\w:complex. (g:complex->complex)(w + bel_fsol mu (Cx(&0)))` THEN
    MATCH_MP_TAC BEL_SHIFT_HOMEO THEN ASM_REWRITE_TAC[ETA_AX];
    GEN_TAC THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[BEL_FSOL_DZ_EXP; CEXP_NZ] THEN
      MP_TAC(ISPECL [`rho:real`; `mu:complex->complex`; `k:real`; `z:complex`]
                    BEL_FSOL_DZ_EXP) THEN
      ASM_SIMP_TAC[CEXP_NZ];
      MATCH_MP_TAC BEL_FSOL_DET_POS THEN
      MAP_EVERY EXISTS_TAC [`rho:real`; `k:real`] THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    UNDISCH_TAC `!z. wirtinger_dbar (bel_fsol (mu:complex->complex)) z =
                     mu z * wirtinger_dz (bel_fsol mu) z` THEN
    DISCH_THEN(K ALL_TAC) THEN
    SUBGOAL_THEN `(\z. bel_fsol (mu:complex->complex) z - bel_fsol mu (Cx(&0)))
                  differentiable at z` ASSUME_TAC THENL
     [MATCH_MP_TAC DIFFERENTIABLE_SUB THEN ASM_REWRITE_TAC[DIFFERENTIABLE_CONST; ETA_AX];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\z. bel_fsol (mu:complex->complex) z - bel_fsol mu (Cx(&0))`; `z:complex`]
                  WIRTINGER_DBAR_EQ_ZERO) THEN
    ASM_SIMP_TAC[BEL_SHIFT_WIRT; ETA_AX] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC BEL_FSOL_HOLOMORPHIC_OUTSIDE THEN
    MAP_EVERY EXISTS_TAC [`rho:real`; `k:real`] THEN ASM_REWRITE_TAC[]]);;

let BEL_STEP_PT = prove
 (`!mu:real->complex->complex rho k t.
        smooth_map_on (:complex) (mu t) /\ bel_supp rho (mu t) /\
        (!z. norm(mu t z) <= k) /\ k < &1
        ==> homeomorphism ((:complex),(:complex)) (bel_nf mu t,bel_nk mu t) /\
            bel_nf mu t (Cx(&0)) = Cx(&0) /\ bel_nk mu t (Cx(&0)) = Cx(&0) /\
            (!z. wirtinger_dbar (bel_nf mu t) z = mu t z * wirtinger_dz (bel_nf mu t) z /\
                 ~(wirtinger_dz (bel_nf mu t) z = Cx(&0)) /\
                 &0 < det(matrix(frechet_derivative (bel_nf mu t) (at z)))) /\
            (!z. rho < norm z ==> bel_nf mu t complex_differentiable at z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[bel_nk] THEN
  SUBGOAL_THEN `bel_nf (mu:real->complex->complex) t =
                (\z. bel_fsol (mu t) z - bel_fsol (mu t) (Cx(&0)))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; bel_nf]; ALL_TAC] THEN
  MP_TAC(ISPECL [`rho:real`; `(mu:real->complex->complex) t`; `k:real`] BEL_NF_PROPS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `ff = \z. bel_fsol ((mu:real->complex->complex) t) z -
                       bel_fsol (mu t) (Cx(&0))` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `homeomorphism ((:complex),(:complex)) (ff,bel_hinv ff)` ASSUME_TAC THENL
   [MATCH_MP_TAC BEL_HINV THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(ff:complex->complex) (Cx(&0)) = Cx(&0)` ASSUME_TAC THENL
   [EXPAND_TAC "ff" THEN REWRITE_TAC[COMPLEX_SUB_REFL]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `homeomorphism ((:complex),(:complex)) (ff,bel_hinv ff)` THEN
  REWRITE_TAC[homeomorphism; IN_UNIV] THEN
  DISCH_THEN(MP_TAC o SPEC `Cx(&0)` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[COMPLEX_SUB_REFL]);;

let BEL_STEP = prove
 (`!mu:real->complex->complex rho k.
        (!m. bel_jfam m (:complex) mu) /\
        (!t. t IN real_interval[&0,&1] ==> bel_supp rho (mu t)) /\
        (!t z. t IN real_interval[&0,&1] ==> norm(mu t z) <= k) /\ k < &1
        ==> (!m. bel_jfam m (:complex) (bel_nf mu)) /\
            (!m. bel_jfam m (:complex) (bel_nk mu)) /\
            (?C. !t z. t IN real_interval[&0,&1]
                       ==> norm(bel_nf mu t z - z) <= C /\ norm(bel_nk mu t z - z) <= C) /\
            (!t. t IN real_interval[&0,&1]
                 ==> homeomorphism ((:complex),(:complex)) (bel_nf mu t,bel_nk mu t) /\
                     bel_nf mu t (Cx(&0)) = Cx(&0) /\ bel_nk mu t (Cx(&0)) = Cx(&0) /\
                     (!z. wirtinger_dbar (bel_nf mu t) z =
                          mu t z * wirtinger_dz (bel_nf mu t) z /\
                          ~(wirtinger_dz (bel_nf mu t) z = Cx(&0)) /\
                          &0 < det(matrix(frechet_derivative (bel_nf mu t) (at z)))) /\
                     (!z. rho < norm z ==> bel_nf mu t complex_differentiable at z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. t IN real_interval[&0,&1]
        ==> homeomorphism ((:complex),(:complex)) (bel_nf mu t,bel_nk mu t) /\
            bel_nf mu t (Cx(&0)) = Cx(&0) /\ bel_nk mu t (Cx(&0)) = Cx(&0) /\
            (!z. wirtinger_dbar (bel_nf mu t) z =
                 (mu:real->complex->complex) t z * wirtinger_dz (bel_nf mu t) z /\
                 ~(wirtinger_dz (bel_nf mu t) z = Cx(&0)) /\
                 &0 < det(matrix(frechet_derivative (bel_nf mu t) (at z)))) /\
            (!z. rho < norm z ==> bel_nf mu t complex_differentiable at z)`
  (LABEL_TAC "pt") THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN MATCH_MP_TAC BEL_STEP_PT THEN
    EXISTS_TAC `k:real` THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[BEL_JFAM_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN `!m. bel_jfam m (:complex) (bel_nf (mu:real->complex->complex))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `bel_nf (mu:real->complex->complex) =
                  (\t z. bel_fsol (mu t) z - bel_fsol (mu t) (Cx(&0)))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; bel_nf]; ALL_TAC] THEN
    MATCH_MP_TAC BEL_JFAM_SUB THEN REWRITE_TAC[OPEN_UNIV] THEN CONJ_TAC THENL
     [REWRITE_TAC[ETA_AX] THEN
      MP_TAC(ISPECL [`mu:real->complex->complex`; `rho:real`; `k:real`] BEL_JFAM_FSOL) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC BEL_JFAM_EVAL THEN
      EXISTS_TAC `(:complex)` THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
      MP_TAC(ISPECL [`mu:real->complex->complex`; `rho:real`; `k:real`] BEL_JFAM_FSOL) THEN
      ASM_SIMP_TAC[ETA_AX]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`mu:real->complex->complex`; `rho:real`; `k:real`] BEL_FSOL_UNIF_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (LABEL_TAC "C")) THEN
  SUBGOAL_THEN `!t z. t IN real_interval[&0,&1]
                      ==> norm(bel_nf (mu:real->complex->complex) t z - z) <= &2 * C`
  (LABEL_TAC "C2") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[bel_nf] THEN
    USE_THEN "C" (fun th ->
      MP_TAC(MATCH_MP (SPECL [`t:real`; `z:complex`] th)
                      (ASSUME `t IN real_interval[&0,&1]`)) THEN
      MP_TAC(MATCH_MP (SPECL [`t:real`; `Cx(&0)`] th)
                      (ASSUME `t IN real_interval[&0,&1]`))) THEN
    REWRITE_TAC[COMPLEX_SUB_RZERO] THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t z. t IN real_interval[&0,&1]
                      ==> norm(bel_nk (mu:real->complex->complex) t z - z) <= &2 * C`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "pt" (fun th -> MP_TAC(MATCH_MP th (ASSUME `t IN real_interval[&0,&1]`))) THEN
    REWRITE_TAC[homeomorphism; IN_UNIV] THEN STRIP_TAC THEN
    USE_THEN "C2" (fun th ->
      MP_TAC(MATCH_MP (SPECL [`t:real`; `bel_nk (mu:real->complex->complex) t z`] th)
                      (ASSUME `t IN real_interval[&0,&1]`))) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC BEL_JFAM_INV THEN
    MAP_EVERY EXISTS_TAC [`bel_nf (mu:real->complex->complex)`; `&2 * C`] THEN
    ASM_SIMP_TAC[] THEN USE_THEN "pt" (fun th -> SIMP_TAC[th]);
    EXISTS_TAC `&2 * C` THEN ASM_SIMP_TAC[];
    USE_THEN "pt" ACCEPT_TAC]);;


(* ========================================================================= *)
(* Step 1 of the construction, in the north chart P =                        *)
(* stereo2_n_inv: the pulled-back metric A, the cut-off coefficient mu1, the *)
(* solution K1 (inverse of the normalized solution) and its conformality.    *)
(* ========================================================================= *)

let bel_A = new_definition
 `bel_A (G:real->real^3->real^3^3) t z = bel_pull (G t) stereo2_n_inv z`;;

let bel_mu1 = new_definition
 `bel_mu1 (G:real->real^3->real^3^3) t z = bel_cut (&1) z * bel_mu (bel_A G t z)`;;

let BEL_P_FRECHET = prove
 (`!z. stereo2_n_inv differentiable at z /\
       frechet_derivative stereo2_n_inv (at z) = bel_dP z /\
       stereo2_s_inv differentiable at z /\
       frechet_derivative stereo2_s_inv (at z) = bel_dQ z`,
  GEN_TAC THEN REWRITE_TAC[differentiable] THEN REPEAT CONJ_TAC THENL
   [MESON_TAC[BEL_P_HAS_DERIVATIVE];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    REWRITE_TAC[BEL_P_HAS_DERIVATIVE];
    MESON_TAC[BEL_Q_HAS_DERIVATIVE];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    REWRITE_TAC[BEL_Q_HAS_DERIVATIVE]]);;

let BEL_DP_INJ = prove
 (`!z h. bel_dP z h = vec 0 ==> h = vec 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `z:real^2` STEX_INV_STEREO_DENOM) THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &4 / (norm(z:real^2) pow 2 + &1) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_POW_LT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`z:real^2`; `h:real^2`; `h:real^2`] BEL_P_CONF) THEN
  ASM_REWRITE_TAC[DOT_LZERO] THEN DISCH_THEN(MP_TAC o SYM) THEN
  REWRITE_TAC[REAL_ENTIRE; DOT_EQ_0] THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ]);;

let BEL_DQ_INJ = prove
 (`!z h. bel_dQ z h = vec 0 ==> h = vec 0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BEL_DP_INJ THEN EXISTS_TAC `z:real^2` THEN
  UNDISCH_TAC `bel_dQ z h = vec 0` THEN REWRITE_TAC[bel_dQ] THEN
  DISCH_THEN(MP_TAC o AP_TERM `bel_refl3`) THEN REWRITE_TAC[BEL_REFL3_DOT] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; BEL_REFL3_COMPONENTS; VEC_COMPONENT] THEN
  REAL_ARITH_TAC);;

let BEL_HYP_POINT = prove
 (`!G t y. bel_hyp G /\ t IN real_interval[&0,&1] /\ y IN sphere(vec 0,&1)
           ==> transp((G:real->real^3->real^3^3) t y) = G t y /\
               ?c. &0 < c /\ !v. v dot y = &0 ==> c * (v dot v) <= v dot (G t y ** v)`,
  REWRITE_TAC[bel_hyp] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  EXISTS_TAC `c:real` THEN ASM_SIMP_TAC[]);;

let BEL_A_QUAD = prove
 (`!G t z a b. a dot (bel_A G t z ** b) =
               bel_dP z a dot ((G:real->real^3->real^3^3) t (stereo2_n_inv z) ** bel_dP z b)`,
  REWRITE_TAC[bel_A] THEN SIMP_TAC[BEL_PULL_QUAD; BEL_P_FRECHET]);;

let BEL_A_PDM = prove
 (`!G t z. bel_hyp G /\ t IN real_interval[&0,&1] ==> bel_pdm (bel_A G t z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:real->real^3->real^3^3`; `t:real`; `stereo2_n_inv z`] BEL_HYP_POINT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MP_TAC(ISPEC `z:real^2` STEX_STEREO2_N_INV_IN) THEN SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[bel_A] THEN MATCH_MP_TAC BEL_PULL_PDM THEN EXISTS_TAC `c:real` THEN
  ASM_REWRITE_TAC[BEL_P_FRECHET; BEL_P_TANG] THEN CONJ_TAC THENL
   [REWRITE_TAC[NORM_EQ_1; BEL_P_NORM];
    MESON_TAC[BEL_DP_INJ]]);;

let BEL_JFAM_A = prove
 (`!G. bel_hyp G
       ==> !i j m. 1 <= i /\ i <= 2 /\ 1 <= j /\ j <= 2
                   ==> bel_jfam m (:complex) (\t z. lift(bel_A G t z$i$j))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bel_A] THEN
  MP_TAC(ISPECL [`G:real->real^3->real^3^3`; `(:complex)`;
                 `\t:real. stereo2_n_inv`] BEL_JFAM_PULL) THEN
  ASM_SIMP_TAC[OPEN_UNIV; BEL_JFAM_CONST; STEX_STEREO2_N_INV_SMOOTH] THEN
  ANTS_TAC THENL
   [MP_TAC STEX_STEREO2_N_INV_IN THEN SET_TAC[];
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let BEL_JFAM_MUA = prove
 (`!G. bel_hyp G ==> !m. bel_jfam m (:complex) (\t z. bel_mu (bel_A G t z))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BEL_JFAM_MU THEN
  ASM_SIMP_TAC[OPEN_UNIV; BEL_JFAM_A; IN_UNIV] THEN
  X_GEN_TAC `t:real` THEN X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`G:real->real^3->real^3^3`; `t:real`; `w:complex`] BEL_A_PDM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP BEL_PDM_MU) THEN SIMP_TAC[]);;

let BEL_JFAM_MU1 = prove
 (`!G. bel_hyp G ==> !m. bel_jfam m (:complex) (bel_mu1 G)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `bel_mu1 (G:real->real^3->real^3^3) =
                (\t z. (\t:real. bel_cut (&1)) t z * bel_mu (bel_A G t z))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; bel_mu1]; ALL_TAC] THEN
  MATCH_MP_TAC BEL_JFAM_CMUL_FUN THEN
  ASM_SIMP_TAC[OPEN_UNIV; BEL_JFAM_MUA; BEL_JFAM_CONST; BEL_CUT_SMOOTH]);;

let BEL_MU1_SUPP = prove
 (`!G t. bel_supp (&2) (bel_mu1 G t)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `bel_mu1 (G:real->real^3->real^3^3) t =
                (\z. bel_cut (&1) z * bel_mu (bel_A G t z))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; bel_mu1]; ALL_TAC] THEN
  MATCH_MP_TAC BEL_SUPP_MUL_LEFT THEN
  MP_TAC(SPEC `&1` BEL_CUT_SUPP) THEN REWRITE_TAC[REAL_LT_01; REAL_MUL_RID] THEN
  REWRITE_TAC[ETA_AX]);;

let BEL_MU1_ONE = prove
 (`!G t z. norm z <= &1 ==> bel_mu1 G t z = bel_mu (bel_A G t z)`,
  SIMP_TAC[bel_mu1; BEL_CUT_ONE; REAL_LT_01; COMPLEX_MUL_LID]);;

let BEL_PDM_MU_LT1 = prove
 (`!A. bel_pdm A ==> norm(bel_mu A) < &1`,
  MESON_TAC[BEL_PDM_MU]);;

let BEL_MU1_BOUND = prove
 (`!G. bel_hyp G
       ==> ?k. &0 <= k /\ k < &1 /\
               !t z. t IN real_interval[&0,&1] ==> norm(bel_mu1 G t z) <= k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^(2,1)finite_sum.
                   bel_mu (bel_A (G:real->real^3->real^3^3) (drop(sndcart x)) (fstcart x))`;
                 `bel_dom(cball(vec 0:complex,&2))`] BEL_COMPACT_LT1) THEN
  ANTS_TAC THENL
   [SIMP_TAC[BEL_DOM_COMPACT; COMPACT_CBALL] THEN CONJ_TAC THENL
     [MP_TAC(SPEC `G:real->real^3->real^3^3` BEL_JFAM_MUA) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `0`) THEN REWRITE_TAC[BEL_JFAM_0] THEN
      DISCH_THEN(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET) o
                 CONJUNCT2) THEN
      REWRITE_TAC[SUBSET; BEL_IN_DOM; IN_UNIV] THEN SIMP_TAC[];
      REWRITE_TAC[BEL_IN_DOM] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC BEL_PDM_MU_LT1 THEN
      MATCH_MP_TAC BEL_A_PDM THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `norm(z:complex) <= &2` THENL
   [REWRITE_TAC[bel_mu1; COMPLEX_NORM_MUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&1 * norm(bel_mu (bel_A (G:real->real^3->real^3^3) t z))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE; BEL_CUT_BOUND];
      REWRITE_TAC[REAL_MUL_LID] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (z:complex) (lift t)`) THEN
      ASM_REWRITE_TAC[BEL_IN_DOM; IN_CBALL_0; FSTCART_PASTECART; SNDCART_PASTECART;
                      LIFT_DROP]];
    MP_TAC(SPECL [`G:real->real^3->real^3^3`; `t:real`] BEL_MU1_SUPP) THEN
    REWRITE_TAC[bel_supp] THEN DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_0]]);;

let BEL_STEP_CONF = prove
 (`!mu:real->complex->complex rho k (AA:real->complex->real^2^2) t w.
        (!m. bel_jfam m (:complex) mu) /\
        (!t. t IN real_interval[&0,&1] ==> bel_supp rho (mu t)) /\
        (!t z. t IN real_interval[&0,&1] ==> norm(mu t z) <= k) /\ k < &1 /\
        t IN real_interval[&0,&1] /\
        bel_pdm (AA t (bel_nk mu t w)) /\
        mu t (bel_nk mu t w) = bel_mu (AA t (bel_nk mu t w))
        ==> ?lam. &0 < lam /\
                  !h k. frechet_derivative (bel_nk mu t) (at w) h dot
                        (AA t (bel_nk mu t w) ** frechet_derivative (bel_nk mu t) (at w) k) =
                        lam * (h dot k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`mu:real->complex->complex`; `rho:real`; `k:real`] BEL_STEP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "jf")
    (CONJUNCTS_THEN2 (LABEL_TAC "jk") (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "pt")))) THEN
  USE_THEN "pt" (fun th -> MP_TAC(MATCH_MP th (ASSUME `t IN real_interval[&0,&1]`))) THEN
  REWRITE_TAC[homeomorphism; IN_UNIV] THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on (:complex) (bel_nf (mu:real->complex->complex) t) /\
                smooth_map_on (:complex) (bel_nk mu t)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC BEL_JFAM_SMOOTH THEN EXISTS_TAC `0` THEN
    ASM_REWRITE_TAC[] THENL [USE_THEN "jf" ACCEPT_TAC; USE_THEN "jk" ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. bel_nf (mu:real->complex->complex) t differentiable at x /\
                    bel_nk mu t differentiable at x` ASSUME_TAC THENL
   [GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(:complex)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`bel_nf (mu:real->complex->complex) t`; `bel_nk (mu:real->complex->complex) t`;
                 `w:complex`] BEL_INV_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `z = bel_nk (mu:real->complex->complex) t w` THEN
  SUBGOAL_THEN `bel_nf (mu:real->complex->complex) t z = w` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `bel_pdm((AA:real->complex->real^2^2) t z)` THEN
  REWRITE_TAC[bel_pdm] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`bel_nf (mu:real->complex->complex) t`; `z:complex`;
                 `(AA:real->complex->real^2^2) t z`] BEL_BELTRAMI_CONF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam0:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `inv lam0` THEN ASM_SIMP_TAC[REAL_LT_INV] THEN
  MP_TAC(ISPECL [`bel_nf (mu:real->complex->complex) t`; `bel_nk (mu:real->complex->complex) t`;
                 `z:complex`; `(AA:real->complex->real^2^2) t z`; `lam0:real`]
                BEL_INV_CONF) THEN
  ASM_REWRITE_TAC[]);;

let BEL_STEP_POLE = prove
 (`!mu:real->complex->complex rho k.
        (!m. bel_jfam m (:complex) mu) /\
        (!t. t IN real_interval[&0,&1] ==> bel_supp rho (mu t)) /\
        (!t z. t IN real_interval[&0,&1] ==> norm(mu t z) <= k) /\ k < &1
        ==> ?r. &0 < r /\
                (!t. t IN real_interval[&0,&1]
                     ==> (bel_pole (bel_nk mu t)) holomorphic_on ball(Cx(&0),r) /\
                         (!w. w IN ball(Cx(&0),r)
                              ==> ~(complex_derivative (bel_pole (bel_nk mu t)) w = Cx(&0))) /\
                         (!w1 w2. w1 IN ball(Cx(&0),r) /\ w2 IN ball(Cx(&0),r) /\
                                  bel_pole (bel_nk mu t) w1 = bel_pole (bel_nk mu t) w2
                                  ==> w1 = w2)) /\
                (!m. bel_jfam m (ball(Cx(&0),r)) (\t. bel_pole (bel_nk mu t)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`mu:real->complex->complex`; `rho:real`; `k:real`] BEL_STEP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "jf")
    (CONJUNCTS_THEN2 (LABEL_TAC "jk")
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `C:real` (LABEL_TAC "C")) (LABEL_TAC "pt")))) THEN
  MATCH_MP_TAC BEL_POLE THEN
  MAP_EVERY EXISTS_TAC [`abs rho + abs C`; `C:real`] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    USE_THEN "pt" (fun th -> MP_TAC(MATCH_MP th (ASSUME `t IN real_interval[&0,&1]`))) THEN
    REWRITE_TAC[homeomorphism; IN_UNIV] THEN MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`t:real`; `z:complex`] THEN STRIP_TAC THEN
    USE_THEN "pt" (fun th -> MP_TAC(MATCH_MP th (ASSUME `t IN real_interval[&0,&1]`))) THEN
    REWRITE_TAC[homeomorphism; IN_UNIV] THEN STRIP_TAC THEN
    MATCH_MP_TAC BEL_INV_CDIFF THEN EXISTS_TAC `bel_nf (mu:real->complex->complex) t` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      USE_THEN "C" (fun th -> MP_TAC(CONJUNCT2(MATCH_MP (SPECL [`t:real`; `z:complex`] th)
                                 (ASSUME `t IN real_interval[&0,&1]`)))) THEN
      UNDISCH_TAC `abs rho + abs C < norm(z:complex)` THEN CONV_TAC NORM_ARITH;
      MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:complex)` THEN
      REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN MATCH_MP_TAC BEL_JFAM_SMOOTH THEN
      EXISTS_TAC `0` THEN ASM_REWRITE_TAC[] THEN USE_THEN "jk" ACCEPT_TAC];
    REPEAT STRIP_TAC THEN
    USE_THEN "C" (fun th -> MP_TAC(CONJUNCT2(MATCH_MP (SPECL [`t:real`; `z:complex`] th)
                               (ASSUME `t IN real_interval[&0,&1]`)))) THEN
    SIMP_TAC[];
    USE_THEN "jk" (MP_TAC o SPEC `0`) THEN SIMP_TAC[BEL_JFAM_0]]);;

(* The inversion T(w) = 1 / cnj w of the chart transition.                    *)

let bel_dT = new_definition
 `bel_dT (w:complex) (h:complex) = cnj(--inv(w pow 2) * h)`;;

let BEL_T_HAS_DERIVATIVE = prove
 (`!w. ~(w = Cx(&0)) ==> ((\w. inv(cnj w)) has_derivative bel_dT w) (at w)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\w:complex. inv(cnj w)) = cnj o inv /\
                bel_dT w = cnj o (\h. --inv(w pow 2) * h)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; bel_dT; CNJ_INV]; ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN
  SIMP_TAC[HAS_DERIVATIVE_LINEAR; LINEAR_CNJ] THEN
  REWRITE_TAC[GSYM has_complex_derivative] THEN
  ASM_SIMP_TAC[HAS_COMPLEX_DERIVATIVE_INV_BASIC]);;

let BEL_CNJ_DOT = prove
 (`!x y. cnj x dot cnj y = x dot y`,
  REWRITE_TAC[DOT_COMPLEX_MUL_CNJ; CNJ_CNJ; GSYM CNJ_MUL; RE_CNJ]);;

let BEL_T_CONF = prove
 (`!w h k. bel_dT w h dot bel_dT w k = norm(inv(w pow 2)) pow 2 * (h dot k)`,
  REWRITE_TAC[bel_dT; BEL_CNJ_DOT] THEN
  REWRITE_TAC[DOT_COMPLEX_MUL_CNJ; COMPLEX_SQNORM] THEN
  REWRITE_TAC[complex_mul; cnj; RE; IM; COMPLEX_NEG_MUL2] THEN
  REWRITE_TAC[RE_NEG; IM_NEG] THEN CONV_TAC REAL_RING);;

let BEL_DT_INJ = prove
 (`!w h. ~(w = Cx(&0)) /\ bel_dT w h = Cx(&0) ==> h = Cx(&0)`,
  REWRITE_TAC[bel_dT; CNJ_EQ_0; COMPLEX_ENTIRE; COMPLEX_NEG_EQ_0; COMPLEX_INV_EQ_0;
              COMPLEX_POW_EQ_0] THEN
  CONV_TAC NUM_REDUCE_CONV THEN MESON_TAC[]);;

let BEL_T_SMOOTH = prove
 (`smooth_map_on {w:complex | ~(w = Cx(&0))} (\w. inv(cnj w))`,
  SUBGOAL_THEN `(\w:complex. inv(cnj w)) = inv o cnj` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `{w:complex | ~(w = Cx(&0))}` THEN
  REWRITE_TAC[BEL_OPEN_NONZERO_C; SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; CNJ_EQ_0] THEN
  SIMP_TAC[SMOOTH_MAP_ON_LINEAR_O; LINEAR_CNJ] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`{w:complex | ~(w = Cx(&0))}`; `\x:complex. x`; `cnj`]
                  SMOOTH_MAP_ON_LINEAR_O) THEN
    REWRITE_TAC[LINEAR_CNJ; SMOOTH_MAP_ON_ID; o_DEF; ETA_AX; BEL_OPEN_NONZERO_C];
    MATCH_MP_TAC BEL_HOLOMORPHIC_SMOOTH THEN REWRITE_TAC[BEL_OPEN_NONZERO_C] THEN
    MP_TAC(ISPECL [`\z:complex. z`; `{z:complex | ~(z = Cx(&0))}`] HOLOMORPHIC_ON_INV) THEN
    REWRITE_TAC[HOLOMORPHIC_ON_ID; IN_ELIM_THM; ETA_AX]]);;

(* Step 1 assembled; the map X1 = H1 o Q from the south chart to S^2.         *)

let bel_K1 = new_definition
 `bel_K1 (G:real->real^3->real^3^3) = bel_nk (bel_mu1 G)`;;

let BEL_STEP1 = prove
 (`!G. bel_hyp G
       ==> (!m. bel_jfam m (:complex) (bel_nf (bel_mu1 G))) /\
           (!m. bel_jfam m (:complex) (bel_K1 G)) /\
           (?C. !t z. t IN real_interval[&0,&1]
                      ==> norm(bel_nf (bel_mu1 G) t z - z) <= C /\
                          norm(bel_K1 G t z - z) <= C) /\
           (!t. t IN real_interval[&0,&1]
                ==> homeomorphism ((:complex),(:complex)) (bel_nf (bel_mu1 G) t,bel_K1 G t) /\
                    bel_nf (bel_mu1 G) t (Cx(&0)) = Cx(&0) /\ bel_K1 G t (Cx(&0)) = Cx(&0)) /\
           (?r. &0 < r /\
                (!t. t IN real_interval[&0,&1]
                     ==> (bel_pole (bel_K1 G t)) holomorphic_on ball(Cx(&0),r) /\
                         (!w. w IN ball(Cx(&0),r)
                              ==> ~(complex_derivative (bel_pole (bel_K1 G t)) w = Cx(&0)))) /\
                (!m. bel_jfam m (ball(Cx(&0),r)) (\t. bel_pole (bel_K1 G t))))`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `G:real->real^3->real^3^3` BEL_MU1_BOUND) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`bel_mu1 (G:real->real^3->real^3^3)`; `&2`; `k:real`] BEL_STEP) THEN
  MP_TAC(ISPECL [`bel_mu1 (G:real->real^3->real^3^3)`; `&2`; `k:real`] BEL_STEP_POLE) THEN
  ASM_SIMP_TAC[BEL_JFAM_MU1; BEL_MU1_SUPP; GSYM bel_K1] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `r:real` THEN ASM_SIMP_TAC[]);;

let bel_X1 = new_definition
 `bel_X1 (G:real->real^3->real^3^3) t w =
    if w = Cx(&0) then basis 3 else stereo2_n_inv (bel_K1 G t (inv(cnj w)))`;;

let BEL_K1_BASIC = prove
 (`!G t. bel_hyp G /\ t IN real_interval[&0,&1]
         ==> (!z1 z2. bel_K1 G t z1 = bel_K1 G t z2 ==> z1 = z2) /\
             bel_K1 G t (Cx(&0)) = Cx(&0) /\
             (!z. ~(z = Cx(&0)) ==> ~(bel_K1 G t z = Cx(&0)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `G:real->real^3->real^3^3` BEL_STEP1) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[homeomorphism; IN_UNIV] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z1 z2. bel_K1 (G:real->real^3->real^3^3) t z1 = bel_K1 G t z2 ==> z1 = z2`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let BEL_X1_Q = prove
 (`!G t w. bel_hyp G /\ t IN real_interval[&0,&1]
           ==> bel_X1 G t w = stereo2_s_inv(bel_pole (bel_K1 G t) w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`G:real->real^3->real^3^3`; `t:real`] BEL_K1_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[bel_X1; bel_pole] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[BEL_P_ZERO] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC BEL_QT_P THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[BEL_T_INVOL]);;

let BEL_X1_SPHERE = prove
 (`!G t w. bel_hyp G /\ t IN real_interval[&0,&1] ==> bel_X1 G t w IN sphere(vec 0,&1)`,
  SIMP_TAC[BEL_X1_Q] THEN
  MESON_TAC[STEX_STEREO2_S_INV_IN; IN_DELETE]);;

let BEL_JFAM_X1 = prove
 (`!G. bel_hyp G ==> !m. bel_jfam m (:complex) (bel_X1 G)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `G:real->real^3->real^3^3` BEL_STEP1) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "jk")
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
      (X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC
         (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "jp")))))))) THEN
  MATCH_MP_TAC BEL_JFAM_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV; INTER_UNIV] THEN
  X_GEN_TAC `w0:complex` THEN ASM_CASES_TAC `w0 = Cx(&0)` THENL
   [EXISTS_TAC `ball(Cx(&0),r)` THEN ASM_SIMP_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
    MATCH_MP_TAC BEL_JFAM_EQ THEN
    EXISTS_TAC `\t. stereo2_s_inv o bel_pole (bel_K1 (G:real->real^3->real^3^3) t)` THEN
    ASM_SIMP_TAC[OPEN_BALL; o_THM; BEL_X1_Q] THEN
    MP_TAC(ISPECL [`m:num`; `ball(Cx(&0),r)`; `(:complex)`; `\t:real. stereo2_s_inv`;
                   `\t. bel_pole (bel_K1 (G:real->real^3->real^3^3) t)`] BEL_JFAM_COMPOSE) THEN
    ASM_SIMP_TAC[OPEN_BALL; OPEN_UNIV; IN_UNIV; BEL_JFAM_CONST; STEX_STEREO2_S_INV_SMOOTH];
    ALL_TAC] THEN
  EXISTS_TAC `{w:complex | ~(w = Cx(&0))}` THEN
  ASM_REWRITE_TAC[BEL_OPEN_NONZERO_C; IN_ELIM_THM] THEN
  MATCH_MP_TAC BEL_JFAM_EQ THEN
  EXISTS_TAC `\t. stereo2_n_inv o (bel_K1 (G:real->real^3->real^3^3) t o (\w. inv(cnj w)))` THEN
  REWRITE_TAC[BEL_OPEN_NONZERO_C; IN_ELIM_THM; o_THM] THEN CONJ_TAC THENL
   [SIMP_TAC[bel_X1]; ALL_TAC] THEN
  MP_TAC(ISPECL [`m:num`; `{w:complex | ~(w = Cx(&0))}`; `(:complex)`; `\t:real. stereo2_n_inv`;
                 `\t. bel_K1 (G:real->real^3->real^3^3) t o (\w. inv(cnj w))`]
                BEL_JFAM_COMPOSE) THEN
  REWRITE_TAC[BEL_OPEN_NONZERO_C; OPEN_UNIV; IN_UNIV] THEN
  SIMP_TAC[BEL_JFAM_CONST; OPEN_UNIV; STEX_STEREO2_N_INV_SMOOTH] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`m:num`; `{w:complex | ~(w = Cx(&0))}`; `(:complex)`;
                 `bel_K1 (G:real->real^3->real^3^3)`; `\t:real. \w:complex. inv(cnj w)`]
                BEL_JFAM_COMPOSE) THEN
  REWRITE_TAC[BEL_OPEN_NONZERO_C; OPEN_UNIV; IN_UNIV] THEN
  ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN CONJ_TAC THENL
   [USE_THEN "jk" ACCEPT_TAC;
    MATCH_MP_TAC BEL_JFAM_CONST THEN REWRITE_TAC[BEL_OPEN_NONZERO_C; BEL_T_SMOOTH]]);;


(* ========================================================================= *)
(* Step 2 of the construction: the metric B1 = X1^* G in the                 *)
(* south chart, its Beltrami coefficient mu2 (compactly supported), and the  *)
(* second solution K2.                                                       *)
(* ========================================================================= *)

let bel_B1 = new_definition
 `bel_B1 (G:real->real^3->real^3^3) t w = bel_pull (G t) (bel_X1 G t) w`;;

let bel_mu2 = new_definition
 `bel_mu2 (G:real->real^3->real^3^3) t w = bel_mu (bel_B1 G t w)`;;

let BEL_FRECHET_CHAIN = prove
 (`!(f:real^M->real^N) (g:real^N->real^P) x.
        f differentiable at x /\ g differentiable at (f x)
        ==> (g o f) differentiable at x /\
            frechet_derivative (g o f) (at x) =
            frechet_derivative g (at (f x)) o frechet_derivative f (at x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `((g:real^N->real^P) o (f:real^M->real^N) has_derivative
                 frechet_derivative g (at (f x)) o frechet_derivative f (at x)) (at x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    CONJ_TAC THENL
     [REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
      ASM_REWRITE_TAC[]]]);;

let BEL_PULL_PDM_COMP = prove
 (`!M (Y:real^2->real^3) (g:real^2->real^2) w c.
        (!z. Y differentiable at z) /\ (!z. norm(Y z) = &1) /\
        (!z h. Y z dot frechet_derivative Y (at z) h = &0) /\
        (!z h. frechet_derivative Y (at z) h = vec 0 ==> h = vec 0) /\
        g differentiable at w /\
        (!h. frechet_derivative g (at w) h = vec 0 ==> h = vec 0) /\
        transp(M (Y (g w))) = M (Y (g w)) /\ &0 < c /\
        (!v. v dot Y (g w) = &0 ==> c * (v dot v) <= v dot (M (Y (g w)) ** v))
        ==> bel_pdm (bel_pull M (Y o g) w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^2->real^2`; `Y:real^2->real^3`; `w:real^2`] BEL_FRECHET_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC BEL_PULL_PDM THEN EXISTS_TAC `c:real` THEN
  ASM_REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[]);;

let BEL_P_CHART = prove
 (`(!z. stereo2_n_inv differentiable at z) /\ (!z. norm(stereo2_n_inv z) = &1) /\
   (!z h. stereo2_n_inv z dot frechet_derivative stereo2_n_inv (at z) h = &0) /\
   (!z h. frechet_derivative stereo2_n_inv (at z) h = vec 0 ==> h = vec 0) /\
   (!z. stereo2_s_inv differentiable at z) /\ (!z. norm(stereo2_s_inv z) = &1) /\
   (!z h. stereo2_s_inv z dot frechet_derivative stereo2_s_inv (at z) h = &0) /\
   (!z h. frechet_derivative stereo2_s_inv (at z) h = vec 0 ==> h = vec 0)`,
  REWRITE_TAC[BEL_P_FRECHET; BEL_P_TANG; BEL_Q_TANG; NORM_EQ_1; BEL_P_NORM] THEN
  REWRITE_TAC[BEL_DP_INJ; BEL_DQ_INJ] THEN
  REWRITE_TAC[BEL_Q_FORM; BEL_REFL3_DOT; BEL_P_NORM]);;

let BEL_HOMEO_DINJ = prove
 (`!f g:real^N->real^N w.
        f differentiable at (g w) /\ g differentiable at w /\ (!w. f(g w) = w)
        ==> !h. frechet_derivative g (at w) h = vec 0 ==> h = vec 0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP BEL_INV_DERIV) THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `h:real^N`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPEC `frechet_derivative (f:real^N->real^N) (at ((g:real^N->real^N) w))`
               LINEAR_0) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[FRECHET_DERIVATIVE_WORKS] THEN SIMP_TAC[has_derivative]);;

let BEL_CDIFF_DINJ = prove
 (`!f:complex->complex w.
        f complex_differentiable at w /\ ~(complex_derivative f w = Cx(&0))
        ==> f differentiable at w /\
            !h. frechet_derivative f (at w) h = vec 0 ==> h = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[COMPLEX_DIFFERENTIABLE_IMP_DIFFERENTIABLE] THEN
  UNDISCH_TAC `f complex_differentiable at w` THEN
  REWRITE_TAC[GSYM HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE; has_complex_derivative] THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  ASM_REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_ENTIRE]);;

let BEL_K1_DIFF = prove
 (`!G t. bel_hyp G /\ t IN real_interval[&0,&1]
         ==> (!z. bel_nf (bel_mu1 G) t differentiable at z) /\
             (!w. bel_K1 G t differentiable at w) /\
             (!w. bel_nf (bel_mu1 G) t (bel_K1 G t w) = w) /\
             (!w h. frechet_derivative (bel_K1 G t) (at w) h = vec 0 ==> h = vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `G:real->real^3->real^3^3` BEL_STEP1) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "jf") (CONJUNCTS_THEN2 (LABEL_TAC "jk")
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "pt") (K ALL_TAC))))) THEN
  USE_THEN "pt" (fun th -> MP_TAC(MATCH_MP th (ASSUME `t IN real_interval[&0,&1]`))) THEN
  REWRITE_TAC[homeomorphism; IN_UNIV] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(!z. bel_nf (bel_mu1 (G:real->real^3->real^3^3)) t differentiable at z) /\
                (!w. bel_K1 G t differentiable at w)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(:complex)` THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    MATCH_MP_TAC BEL_JFAM_SMOOTH THEN EXISTS_TAC `0` THEN ASM_REWRITE_TAC[] THENL
     [USE_THEN "jf" ACCEPT_TAC; USE_THEN "jk" ACCEPT_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:complex` THEN
  MATCH_MP_TAC BEL_HOMEO_DINJ THEN
  EXISTS_TAC `bel_nf (bel_mu1 (G:real->real^3->real^3^3)) t` THEN ASM_REWRITE_TAC[]);;

let BEL_T_FRECHET = prove
 (`!w. ~(w = Cx(&0))
       ==> (\w. inv(cnj w)) differentiable at w /\
           frechet_derivative (\w. inv(cnj w)) (at w) = bel_dT w`,
  GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP BEL_T_HAS_DERIVATIVE) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN ASM_REWRITE_TAC[]]);;

let BEL_KT_DIFF = prove
 (`!K:complex->complex w.
        ~(w = Cx(&0)) /\ K differentiable at (inv(cnj w)) /\
        (!h. frechet_derivative K (at (inv(cnj w))) h = vec 0 ==> h = vec 0)
        ==> (K o (\w. inv(cnj w))) differentiable at w /\
            (!h. frechet_derivative (K o (\w. inv(cnj w))) (at w) h = vec 0 ==> h = vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `w:complex` BEL_T_FRECHET) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\w:complex. inv(cnj w)`; `K:complex->complex`; `w:complex`]
                BEL_FRECHET_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[o_THM] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `bel_dT w h = vec 0` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_VEC_0] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`w:complex`; `h:complex`] BEL_DT_INJ) THEN
  ASM_REWRITE_TAC[COMPLEX_VEC_0]);;

let BEL_B1_PDM = prove
 (`!G t w. bel_hyp G /\ t IN real_interval[&0,&1] ==> bel_pdm (bel_B1 G t w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`G:real->real^3->real^3^3`; `t:real`] BEL_K1_DIFF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `w = Cx(&0)` THENL
   [FIRST_X_ASSUM SUBST1_TAC THEN
    MP_TAC(SPEC `G:real->real^3->real^3^3` BEL_STEP1) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC o
               CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `bel_B1 (G:real->real^3->real^3^3) t (Cx(&0)) =
                  bel_pull (G t) (stereo2_s_inv o bel_pole (bel_K1 G t)) (Cx(&0))`
    SUBST1_TAC THENL
     [REWRITE_TAC[bel_B1] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM; o_THM] THEN ASM_SIMP_TAC[BEL_X1_Q];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`G:real->real^3->real^3^3`; `t:real`;
                   `stereo2_s_inv(bel_pole (bel_K1 (G:real->real^3->real^3^3) t) (Cx(&0)))`]
                  BEL_HYP_POINT) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [MESON_TAC[STEX_STEREO2_S_INV_IN; IN_DELETE]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC)) THEN
    MATCH_MP_TAC BEL_PULL_PDM_COMP THEN EXISTS_TAC `c:real` THEN
    ASM_REWRITE_TAC[BEL_P_CHART; o_THM] THEN
    MATCH_MP_TAC BEL_CDIFF_DINJ THEN
    SUBGOAL_THEN `Cx(&0) IN ball(Cx(&0),r)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[CENTRE_IN_BALL]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT THEN
    EXISTS_TAC `ball(Cx(&0),r)` THEN ASM_SIMP_TAC[OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `bel_B1 (G:real->real^3->real^3^3) t w =
                bel_pull (G t) (stereo2_n_inv o (bel_K1 G t o (\w. inv(cnj w)))) w`
  SUBST1_TAC THENL
   [REWRITE_TAC[bel_B1] THEN MATCH_MP_TAC BEL_PULL_LOCAL THEN
    EXISTS_TAC `{w:complex | ~(w = Cx(&0))}` THEN
    ASM_REWRITE_TAC[BEL_OPEN_NONZERO_C; IN_ELIM_THM] THEN
    SIMP_TAC[bel_X1; o_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real->real^3->real^3^3`; `t:real`;
                 `(stereo2_n_inv o (bel_K1 (G:real->real^3->real^3^3) t o (\w. inv(cnj w)))) w`]
                BEL_HYP_POINT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[o_THM] THEN MESON_TAC[STEX_STEREO2_N_INV_IN; IN_DELETE]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC BEL_PULL_PDM_COMP THEN EXISTS_TAC `c:real` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[o_THM]) THEN
  ASM_REWRITE_TAC[BEL_P_CHART; o_THM] THEN
  MATCH_MP_TAC BEL_KT_DIFF THEN ASM_REWRITE_TAC[]);;

let BEL_JFAM_B1 = prove
 (`!G. bel_hyp G
       ==> !i j m. 1 <= i /\ i <= 2 /\ 1 <= j /\ j <= 2
                   ==> bel_jfam m (:complex) (\t w. lift(bel_B1 G t w$i$j))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bel_B1] THEN
  MP_TAC(ISPECL [`G:real->real^3->real^3^3`; `(:complex)`; `bel_X1 (G:real->real^3->real^3^3)`]
                BEL_JFAM_PULL) THEN
  ASM_SIMP_TAC[OPEN_UNIV; BEL_JFAM_X1; BEL_X1_SPHERE]);;

let BEL_JFAM_MU2 = prove
 (`!G. bel_hyp G ==> !m. bel_jfam m (:complex) (bel_mu2 G)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `bel_mu2 (G:real->real^3->real^3^3) = (\t w. bel_mu (bel_B1 G t w))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; bel_mu2]; ALL_TAC] THEN
  MATCH_MP_TAC BEL_JFAM_MU THEN ASM_SIMP_TAC[OPEN_UNIV; BEL_JFAM_B1; IN_UNIV] THEN
  X_GEN_TAC `t:real` THEN X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`G:real->real^3->real^3^3`; `t:real`; `w:complex`] BEL_B1_PDM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP BEL_PDM_MU) THEN SIMP_TAC[]);;

let BEL_UNIF_AT0 = prove
 (`!hh:real->complex->complex.
        (\x. hh (drop(sndcart x)) (fstcart x)) continuous_on bel_dom (:complex) /\
        (!t. t IN real_interval[&0,&1] ==> hh t (Cx(&0)) = Cx(&0))
        ==> ?d. &0 < d /\ d <= &1 /\
                !t z. t IN real_interval[&0,&1] /\ norm z < d ==> norm(hh t z) < &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^(2,1)finite_sum. (hh:real->complex->complex) (drop(sndcart x)) (fstcart x)`;
                 `bel_dom(cball(vec 0:complex,&1))`] COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ANTS_TAC THENL
   [SIMP_TAC[BEL_DOM_COMPACT; COMPACT_CBALL] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET; BEL_IN_DOM; IN_UNIV] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[uniformly_continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `&1`) THEN
  REWRITE_TAC[REAL_LT_01] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d (&1)` THEN ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LT_01] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`pastecart (Cx(&0)) (lift t)`; `pastecart (z:complex) (lift t)`]) THEN
  ASM_REWRITE_TAC[BEL_IN_DOM; IN_CBALL_0; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP;
                  DIST_PASTECART_CANCEL] THEN
  ASM_SIMP_TAC[GSYM COMPLEX_VEC_0; NORM_0; REAL_POS; DIST_0] THEN
  ASM_SIMP_TAC[COMPLEX_VEC_0; dist; COMPLEX_SUB_RZERO; REAL_LT_IMP_LE]);;

let BEL_B1_FAR = prove
 (`!G t w. bel_hyp G /\ t IN real_interval[&0,&1] /\ ~(w = Cx(&0)) /\
           norm(bel_K1 G t (inv(cnj w))) <= &1
           ==> ?lam. !a b. a dot (bel_B1 G t w ** b) = lam * (a dot b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`G:real->real^3->real^3^3`; `t:real`] BEL_K1_DIFF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `G:real->real^3->real^3^3` BEL_MU1_BOUND) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`bel_mu1 (G:real->real^3->real^3^3)`; `&2`; `k:real`;
                 `bel_A (G:real->real^3->real^3^3)`; `t:real`; `inv(cnj w)`]
                BEL_STEP_CONF) THEN
  ASM_SIMP_TAC[BEL_JFAM_MU1; BEL_MU1_SUPP; GSYM bel_K1; BEL_A_PDM; BEL_MU1_ONE] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `lam * norm(inv(w pow 2)) pow 2` THEN REPEAT GEN_TAC THEN
  SUBGOAL_THEN `bel_B1 (G:real->real^3->real^3^3) t w =
                bel_pull (G t) (stereo2_n_inv o (bel_K1 G t o (\w. inv(cnj w)))) w`
  SUBST1_TAC THENL
   [REWRITE_TAC[bel_B1] THEN MATCH_MP_TAC BEL_PULL_LOCAL THEN
    EXISTS_TAC `{w:complex | ~(w = Cx(&0))}` THEN
    ASM_REWRITE_TAC[BEL_OPEN_NONZERO_C; IN_ELIM_THM] THEN
    SIMP_TAC[bel_X1; o_THM];
    ALL_TAC] THEN
  MP_TAC(ISPEC `w:complex` BEL_T_FRECHET) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\w:complex. inv(cnj w)`; `bel_K1 (G:real->real^3->real^3^3) t`; `w:complex`]
                BEL_FRECHET_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G (t:real):real^3->real^3^3`; `stereo2_n_inv`;
                 `bel_K1 (G:real->real^3->real^3^3) t o (\w. inv(cnj w))`; `w:complex`;
                 `a:real^2`; `b:real^2`] BEL_PULL_COMPOSE_QUAD) THEN
  ASM_REWRITE_TAC[BEL_P_FRECHET; o_THM] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM bel_A] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[BEL_T_CONF] THEN REAL_ARITH_TAC);;

let BEL_MU2_SUPP = prove
 (`!G. bel_hyp G
       ==> ?R. &0 < R /\ !t. t IN real_interval[&0,&1] ==> bel_supp R (bel_mu2 G t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `G:real->real^3->real^3^3` BEL_STEP1) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "jk")
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "pt") (K ALL_TAC))))) THEN
  MP_TAC(ISPEC `bel_K1 (G:real->real^3->real^3^3)` BEL_UNIF_AT0) THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "jk" (MP_TAC o SPEC `0`) THEN SIMP_TAC[BEL_JFAM_0];
      USE_THEN "pt" (fun th -> SIMP_TAC[th])];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `inv d` THEN ASM_SIMP_TAC[REAL_LT_INV] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[bel_supp; bel_mu2] THEN
  X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(w = Cx(&0))` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `inv d < norm(Cx(&0))` THEN REWRITE_TAC[COMPLEX_NORM_0] THEN
    MP_TAC(ISPEC `d:real` REAL_LT_INV) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real->real^3->real^3^3`; `t:real`; `w:complex`] BEL_B1_FAR) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_INV; COMPLEX_NORM_CNJ] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN
    MATCH_MP_TAC REAL_LT_INV2 THEN ASM_SIMP_TAC[REAL_LT_INV];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `lam:real`) THEN MATCH_MP_TAC BEL_MU_ZERO THEN
  EXISTS_TAC `lam:real` THEN ASM_REWRITE_TAC[]);;

let BEL_MU2_BOUND = prove
 (`!G. bel_hyp G
       ==> ?R k. &0 < R /\ &0 <= k /\ k < &1 /\
                 (!t. t IN real_interval[&0,&1] ==> bel_supp R (bel_mu2 G t)) /\
                 (!t z. t IN real_interval[&0,&1] ==> norm(bel_mu2 G t z) <= k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `G:real->real^3->real^3^3` BEL_MU2_SUPP) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`\x:real^(2,1)finite_sum.
                   bel_mu2 (G:real->real^3->real^3^3) (drop(sndcart x)) (fstcart x)`;
                 `bel_dom(cball(vec 0:complex,R))`] BEL_COMPACT_LT1) THEN
  ANTS_TAC THENL
   [SIMP_TAC[BEL_DOM_COMPACT; COMPACT_CBALL] THEN CONJ_TAC THENL
     [MP_TAC(SPEC `G:real->real^3->real^3^3` BEL_JFAM_MU2) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `0`) THEN REWRITE_TAC[BEL_JFAM_0] THEN
      DISCH_THEN(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET) o
                 CONJUNCT2) THEN
      REWRITE_TAC[SUBSET; BEL_IN_DOM; IN_UNIV] THEN SIMP_TAC[];
      REWRITE_TAC[BEL_IN_DOM] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[bel_mu2] THEN
      MATCH_MP_TAC BEL_PDM_MU_LT1 THEN MATCH_MP_TAC BEL_B1_PDM THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`R:real`; `k:real`] THEN ASM_SIMP_TAC[] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `norm(z:complex) <= R` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (z:complex) (lift t)`) THEN
    ASM_REWRITE_TAC[BEL_IN_DOM; IN_CBALL_0; FSTCART_PASTECART; SNDCART_PASTECART;
                    LIFT_DROP];
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
      can (find_term ((=) `bel_supp`)) (concl th))) THEN
    ASM_REWRITE_TAC[bel_supp] THEN DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_0]]);;

let bel_K2 = new_definition
 `bel_K2 (G:real->real^3->real^3^3) = bel_nk (bel_mu2 G)`;;

let BEL_STEP2 = prove
 (`!G. bel_hyp G
       ==> (!m. bel_jfam m (:complex) (bel_nf (bel_mu2 G))) /\
           (!m. bel_jfam m (:complex) (bel_K2 G)) /\
           (?C. !t z. t IN real_interval[&0,&1]
                      ==> norm(bel_nf (bel_mu2 G) t z - z) <= C /\
                          norm(bel_K2 G t z - z) <= C) /\
           (!t. t IN real_interval[&0,&1]
                ==> homeomorphism ((:complex),(:complex)) (bel_nf (bel_mu2 G) t,bel_K2 G t) /\
                    bel_nf (bel_mu2 G) t (Cx(&0)) = Cx(&0) /\ bel_K2 G t (Cx(&0)) = Cx(&0)) /\
           (?r. &0 < r /\
                (!t. t IN real_interval[&0,&1]
                     ==> (bel_pole (bel_K2 G t)) holomorphic_on ball(Cx(&0),r) /\
                         (!w. w IN ball(Cx(&0),r)
                              ==> ~(complex_derivative (bel_pole (bel_K2 G t)) w = Cx(&0))) /\
                         (!w1 w2. w1 IN ball(Cx(&0),r) /\ w2 IN ball(Cx(&0),r) /\
                                  bel_pole (bel_K2 G t) w1 = bel_pole (bel_K2 G t) w2
                                  ==> w1 = w2)) /\
                (!m. bel_jfam m (ball(Cx(&0),r)) (\t. bel_pole (bel_K2 G t)))) /\
           (!t w. t IN real_interval[&0,&1]
                  ==> ?lam. &0 < lam /\
                            !h k. frechet_derivative (bel_K2 G t) (at w) h dot
                                  (bel_B1 G t (bel_K2 G t w) **
                                   frechet_derivative (bel_K2 G t) (at w) k) =
                                  lam * (h dot k))`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `G:real->real^3->real^3^3` BEL_MU2_BOUND) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real` (X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`bel_mu2 (G:real->real^3->real^3^3)`; `R:real`; `k:real`] BEL_STEP) THEN
  MP_TAC(ISPECL [`bel_mu2 (G:real->real^3->real^3^3)`; `R:real`; `k:real`] BEL_STEP_POLE) THEN
  ASM_SIMP_TAC[BEL_JFAM_MU2; GSYM bel_K2] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[bel_K2] THEN MATCH_MP_TAC BEL_STEP_CONF THEN
  MAP_EVERY EXISTS_TAC [`R:real`; `k:real`] THEN
  ASM_SIMP_TAC[BEL_JFAM_MU2; BEL_B1_PDM; bel_mu2]);;


(* ========================================================================= *)
(* The conformal map h = H1 o H2 of the sphere, its chart                    *)
(* representations, bijectivity and regularity of its radial extension.     *)
(* ========================================================================= *)

let bel_h = new_definition
 `bel_h (G:real->real^3->real^3^3) t y =
    if y = --(basis 3) then --(basis 3) else bel_X1 G t (bel_K2 G t (stereo2_s y))`;;

let BEL_Q_NE_S = prove
 (`!w. ~(stereo2_s_inv w = --(basis 3))`,
  MESON_TAC[STEX_STEREO2_S_INV_IN; IN_DELETE]);;

let BEL_P_NE_N = prove
 (`!u. ~(stereo2_n_inv u = basis 3)`,
  MESON_TAC[STEX_STEREO2_N_INV_IN; IN_DELETE]);;

let BEL_H_Q = prove
 (`!G t w. bel_h G t (stereo2_s_inv w) = bel_X1 G t (bel_K2 G t w)`,
  REWRITE_TAC[bel_h; BEL_Q_NE_S; STEX_STEREO2_S_RIGHT]);;

let BEL_POLE_INV = prove
 (`!K L:complex->complex.
        (!z. L(K z) = z) /\ (!z. K(L z) = z) /\ K(Cx(&0)) = Cx(&0)
        ==> (!w. bel_pole L (bel_pole K w) = w) /\ (!w. bel_pole K (bel_pole L w) = w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(L:complex->complex)(Cx(&0)) = Cx(&0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(!z. ~(z = Cx(&0)) ==> ~((K:complex->complex) z = Cx(&0))) /\
                (!z. ~(z = Cx(&0)) ==> ~((L:complex->complex) z = Cx(&0)))`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THEN X_GEN_TAC `w:complex` THEN REWRITE_TAC[bel_pole] THEN
  ASM_CASES_TAC `w = Cx(&0)` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[BEL_T_INVOL; COMPLEX_INV_EQ_0; CNJ_EQ_0]);;

let BEL_H_P = prove
 (`!G t u. bel_hyp G /\ t IN real_interval[&0,&1]
           ==> bel_h G t (stereo2_n_inv u) =
               stereo2_n_inv (bel_K1 G t (bel_pole (bel_K2 G t) u))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`G:real->real^3->real^3^3`; `t:real`] BEL_K1_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `G:real->real^3->real^3^3` BEL_STEP2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[homeomorphism; IN_UNIV] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z. ~(z = Cx(&0)) ==> ~(bel_K2 (G:real->real^3->real^3^3) t z = Cx(&0))`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `u = Cx(&0)` THENL
   [ASM_REWRITE_TAC[bel_h; BEL_P_ZERO; bel_pole]; ALL_TAC] THEN
  REWRITE_TAC[bel_h] THEN
  SUBGOAL_THEN `~(stereo2_n_inv u = --(basis 3))` (fun th -> REWRITE_TAC[th]) THENL
   [DISCH_THEN(MP_TAC o AP_TERM `stereo2_n`) THEN
    REWRITE_TAC[STEX_STEREO2_N_RIGHT; GSYM(CONJUNCT1 BEL_P_ZERO)] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[BEL_S_OF_P; bel_X1; BEL_T_INVOL; bel_pole]);;

let BEL_H_BIJ = prove
 (`!G t. bel_hyp G /\ t IN real_interval[&0,&1]
         ==> (!y. y IN sphere(vec 0,&1) ==> bel_h G t y IN sphere(vec 0,&1)) /\
             (!x. x IN sphere(vec 0,&1)
                  ==> ?!y. y IN sphere(vec 0,&1) /\ bel_h G t y = x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `G:real->real^3->real^3^3` BEL_STEP1) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[homeomorphism; IN_UNIV] THEN STRIP_TAC THEN
  MP_TAC(SPEC `G:real->real^3->real^3^3` BEL_STEP2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[homeomorphism; IN_UNIV] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`bel_K1 (G:real->real^3->real^3^3) t`; `bel_nf (bel_mu1 (G:real->real^3->real^3^3)) t`]
                BEL_POLE_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!w. bel_h (G:real->real^3->real^3^3) t (stereo2_s_inv w) =
        stereo2_s_inv(bel_pole (bel_K1 G t) (bel_K2 G t w))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[BEL_H_Q; BEL_X1_Q]; ALL_TAC] THEN
  SUBGOAL_THEN `bel_h (G:real->real^3->real^3^3) t (--(basis 3)) = --(basis 3)`
  ASSUME_TAC THENL [REWRITE_TAC[bel_h]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN sphere(vec 0,&1) /\ ~(x = --(basis 3))
                    ==> stereo2_s_inv(stereo2_s x) = x`
  ASSUME_TAC THENL [MESON_TAC[STEX_STEREO2_S_LEFT; IN_DELETE]; ALL_TAC] THEN
  SUBGOAL_THEN `!w. stereo2_s_inv w IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [MESON_TAC[STEX_STEREO2_S_INV_IN; IN_DELETE]; ALL_TAC] THEN
  SUBGOAL_THEN `--(basis 3:real^3) IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_SPHERE_0; NORM_NEG] THEN SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    ASM_CASES_TAC `y = --(basis 3):real^3` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `y = stereo2_s_inv(stereo2_s y)` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `x = --(basis 3):real^3` THENL
     [EXISTS_TAC `--(basis 3):real^3` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `stereo2_s_inv(bel_nf (bel_mu2 (G:real->real^3->real^3^3)) t
                  (bel_pole (bel_nf (bel_mu1 G) t) (stereo2_s x)))` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y1:real^3`; `y2:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y. y IN sphere(vec 0,&1) /\ ~(y = --(basis 3))
                    ==> ~(bel_h (G:real->real^3->real^3^3) t y = --(basis 3))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `y = stereo2_s_inv(stereo2_s y)` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[BEL_Q_NE_S];
    ALL_TAC] THEN
  ASM_CASES_TAC `y1 = --(basis 3):real^3` THEN ASM_CASES_TAC `y2 = --(basis 3):real^3` THENL
   [ASM_REWRITE_TAC[]; ASM_MESON_TAC[]; ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `y1 = stereo2_s_inv(stereo2_s y1) /\ y2 = stereo2_s_inv(stereo2_s y2)`
  (CONJUNCTS_THEN SUBST_ALL_TAC) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  AP_TERM_TAC THEN
  UNDISCH_TAC `bel_h (G:real->real^3->real^3^3) t (stereo2_s_inv (stereo2_s y1)) = x` THEN
  UNDISCH_TAC `bel_h (G:real->real^3->real^3^3) t (stereo2_s_inv (stereo2_s y2)) = x` THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  DISCH_THEN(MP_TAC o AP_TERM `stereo2_s`) THEN REWRITE_TAC[STEX_STEREO2_S_RIGHT] THEN
  DISCH_THEN(MP_TAC o AP_TERM `bel_pole (bel_nf (bel_mu1 (G:real->real^3->real^3^3)) t)`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM `bel_nf (bel_mu2 (G:real->real^3->real^3^3)) t`) THEN
  ASM_REWRITE_TAC[]);;

(* The radial extension of h has all derivatives jointly continuous.          *)

let BEL_NZ_SPHERE = prove
 (`!z:real^3. ~(z = vec 0) ==> inv(norm z) % z IN sphere(vec 0,&1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
  MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[NORM_EQ_0]);;

let BEL_NZ_CONT = prove
 (`(\z:real^3. inv(norm z) % z) continuous_on {z:real^3 | ~(z = vec 0)}`,
  MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN REWRITE_TAC[SMOOTH_MAP_ON_NORMALIZE]);;

let BEL_OPEN_V1 = prove
 (`open {z:real^3 | ~(z = vec 0) /\ ~(inv(norm z) % z = --(basis 3))}`,
  SUBGOAL_THEN `{z:real^3 | ~(z = vec 0) /\ ~(inv(norm z) % z = --(basis 3))} =
                {x | x IN {z:real^3 | ~(z = vec 0)} /\
                     (\z:real^3. inv(norm z) % z) x IN ((:real^3) DELETE --(basis 3))}`
  SUBST1_TAC THENL [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DELETE; IN_UNIV]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
  SIMP_TAC[BEL_NZ_CONT; OPEN_NONZERO; OPEN_DELETE; OPEN_UNIV]);;

let BEL_OPEN_V2 = prove
 (`!r. open {z:real^3 | ~(z = vec 0) /\ (inv(norm z) % z)$3 < &1 /\
                        norm(stereo2_n(inv(norm z) % z)) < r}`,
  GEN_TAC THEN
  SUBGOAL_THEN `open {z:real^3 | ~(z = vec 0) /\ (inv(norm z) % z)$3 < &1}` ASSUME_TAC THENL
   [SUBGOAL_THEN `{z:real^3 | ~(z = vec 0) /\ (inv(norm z) % z)$3 < &1} =
                  {x | x IN {z:real^3 | ~(z = vec 0)} /\
                       (\z:real^3. inv(norm z) % z) x IN {y:real^3 | y$3 < &1}}`
    SUBST1_TAC THENL [REWRITE_TAC[EXTENSION; IN_ELIM_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    SIMP_TAC[BEL_NZ_CONT; OPEN_NONZERO; OPEN_HALFSPACE_COMPONENT_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `{z:real^3 | ~(z = vec 0) /\ (inv(norm z) % z)$3 < &1 /\
                            norm(stereo2_n(inv(norm z) % z)) < r} =
                {x | x IN {z:real^3 | ~(z = vec 0) /\ (inv(norm z) % z)$3 < &1} /\
                     (stereo2_n o (\z:real^3. inv(norm z) % z)) x IN ball(vec 0,r)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; o_THM; IN_BALL_0; CONJ_ASSOC]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[OPEN_BALL] THEN
  REWRITE_TAC[ETA_AX] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN REWRITE_TAC[BEL_NZ_CONT] THEN SET_TAC[];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `{y:real^3 | y$3 < &1}` THEN
    SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS; STEX_STEREO2_N_SMOOTH] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[]]);;

let BEL_JFAM_HN_V1 = prove
 (`!G. bel_hyp G
       ==> !m. bel_jfam m {z:real^3 | ~(z = vec 0) /\ ~(inv(norm z) % z = --(basis 3))}
                 (\t z. bel_h G t (inv(norm z) % z))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `G:real->real^3->real^3^3` BEL_JFAM_X1) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "jx") THEN
  MP_TAC(SPEC `G:real->real^3->real^3^3` BEL_STEP2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "jk2") (K ALL_TAC))) THEN
  MATCH_MP_TAC BEL_JFAM_EQ THEN
  EXISTS_TAC `\t. (bel_X1 (G:real->real^3->real^3^3) t o bel_K2 G t) o
                  (stereo2_s o (\z:real^3. inv(norm z) % z))` THEN
  REWRITE_TAC[BEL_OPEN_V1] THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; o_THM] THEN SIMP_TAC[bel_h]; ALL_TAC] THEN
  MP_TAC(ISPECL [`m:num`; `{z:real^3 | ~(z = vec 0) /\ ~(inv(norm z) % z = --(basis 3))}`;
                 `(:complex)`;
                 `\t. bel_X1 (G:real->real^3->real^3^3) t o bel_K2 G t`;
                 `\t:real. stereo2_s o (\z:real^3. inv(norm z) % z)`] BEL_JFAM_COMPOSE) THEN
  REWRITE_TAC[BEL_OPEN_V1; OPEN_UNIV; IN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`n:num`; `(:complex)`; `(:complex)`; `bel_X1 (G:real->real^3->real^3^3)`;
                   `bel_K2 (G:real->real^3->real^3^3)`] BEL_JFAM_COMPOSE) THEN
    REWRITE_TAC[OPEN_UNIV; IN_UNIV; ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
    USE_THEN "jx" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "jk2" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  MATCH_MP_TAC BEL_JFAM_CONST THEN REWRITE_TAC[BEL_OPEN_V1] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `{x:real^3 | x$3 > -- &1}` THEN
  REWRITE_TAC[BEL_OPEN_V1; OPEN_HALFSPACE_COMPONENT_GT; STEX_STEREO2_S_SMOOTH] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MP_TAC STEX_STEREO2_S_DOMAIN THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DELETE] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[BEL_NZ_SPHERE];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN REWRITE_TAC[SMOOTH_MAP_ON_NORMALIZE] THEN
    SET_TAC[]]);;

let BEL_JFAM_HN_V2 = prove
 (`!G. bel_hyp G
       ==> ?r. &0 < r /\
               !m. bel_jfam m {z:real^3 | ~(z = vec 0) /\ (inv(norm z) % z)$3 < &1 /\
                                          norm(stereo2_n(inv(norm z) % z)) < r}
                     (\t z. bel_h G t (inv(norm z) % z))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `G:real->real^3->real^3^3` BEL_STEP1) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "jk1") (K ALL_TAC))) THEN
  MP_TAC(SPEC `G:real->real^3->real^3^3` BEL_STEP2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC
         (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "jp")))) (K ALL_TAC)))))) THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN
  ABBREV_TAC `V = {z:real^3 | ~(z = vec 0) /\ (inv(norm z) % z)$3 < &1 /\
                              norm(stereo2_n(inv(norm z) % z)) < r}` THEN
  SUBGOAL_THEN `open(V:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN REWRITE_TAC[BEL_OPEN_V2]; ALL_TAC] THEN
  MATCH_MP_TAC BEL_JFAM_EQ THEN
  EXISTS_TAC `\t. (stereo2_n_inv o (bel_K1 (G:real->real^3->real^3^3) t o
                                    bel_pole (bel_K2 G t))) o
                  (stereo2_n o (\z:real^3. inv(norm z) % z))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`t:real`; `z:real^3`] THEN EXPAND_TAC "V" THEN
    REWRITE_TAC[IN_ELIM_THM; o_THM] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`G:real->real^3->real^3^3`; `t:real`;
                   `stereo2_n(inv(norm z) % (z:real^3))`] BEL_H_P) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    AP_TERM_TAC THEN MATCH_MP_TAC STEX_STEREO2_N_LEFT THEN
    ASM_SIMP_TAC[IN_DELETE; BEL_NZ_SPHERE] THEN
    DISCH_TAC THEN UNDISCH_TAC `(inv(norm z) % (z:real^3))$3 < &1` THEN
    ASM_REWRITE_TAC[BEL_BASIS3_COMPONENTS] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:num`; `V:real^3->bool`; `ball(Cx(&0),r)`;
                 `\t. stereo2_n_inv o (bel_K1 (G:real->real^3->real^3^3) t o
                                       bel_pole (bel_K2 G t))`;
                 `\t:real. stereo2_n o (\z:real^3. inv(norm z) % z)`] BEL_JFAM_COMPOSE) THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`n:num`; `ball(Cx(&0),r)`; `(:complex)`; `\t:real. stereo2_n_inv`;
                   `\t. bel_K1 (G:real->real^3->real^3^3) t o bel_pole (bel_K2 G t)`]
                  BEL_JFAM_COMPOSE) THEN
    REWRITE_TAC[OPEN_BALL; OPEN_UNIV; IN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
    SIMP_TAC[BEL_JFAM_CONST; OPEN_UNIV; STEX_STEREO2_N_INV_SMOOTH] THEN
    MP_TAC(ISPECL [`n:num`; `ball(Cx(&0),r)`; `(:complex)`; `bel_K1 (G:real->real^3->real^3^3)`;
                   `\t. bel_pole (bel_K2 (G:real->real^3->real^3^3) t)`] BEL_JFAM_COMPOSE) THEN
    REWRITE_TAC[OPEN_BALL; OPEN_UNIV; IN_UNIV; ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
    USE_THEN "jk1" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "jp" (fun th -> REWRITE_TAC[th]);
    MATCH_MP_TAC BEL_JFAM_CONST THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `{x:real^3 | x$3 < &1}` THEN
    ASM_REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT; STEX_STEREO2_N_SMOOTH] THEN CONJ_TAC THENL
     [EXPAND_TAC "V" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN REWRITE_TAC[SMOOTH_MAP_ON_NORMALIZE] THEN
      EXPAND_TAC "V" THEN SET_TAC[]];
    EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM; o_THM; BEL_IN_BALL_C0] THEN SIMP_TAC[]]);;

let BEL_JFAM_HN = prove
 (`!G. bel_hyp G
       ==> !m. bel_jfam m {z:real^3 | ~(z = vec 0)} (\t z. bel_h G t (inv(norm z) % z))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `G:real->real^3->real^3^3` BEL_JFAM_HN_V2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC BEL_JFAM_LOCAL THEN REWRITE_TAC[OPEN_NONZERO] THEN
  X_GEN_TAC `z0:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  ASM_CASES_TAC `inv(norm z0) % z0 = --(basis 3):real^3` THENL
   [EXISTS_TAC `{z:real^3 | ~(z = vec 0) /\ (inv(norm z) % z)$3 < &1 /\
                            norm(stereo2_n(inv(norm z) % z)) < r}` THEN
    REWRITE_TAC[BEL_OPEN_V2] THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[IN_ELIM_THM; VECTOR_NEG_COMPONENT; BEL_BASIS3_COMPONENTS] THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[stereo2_n] THEN
      SUBGOAL_THEN `(lambda i. --(basis 3:real^3)$i / (&1 - --(basis 3:real^3)$3)):real^2 = vec 0`
      SUBST1_TAC THENL
       [SIMP_TAC[CART_EQ; LAMBDA_BETA; DIMINDEX_2; FORALL_2; VEC_COMPONENT;
                 VECTOR_NEG_COMPONENT; BEL_BASIS3_COMPONENTS] THEN REAL_ARITH_TAC;
        ASM_REWRITE_TAC[NORM_0]];
      SUBGOAL_THEN `{z:real^3 | ~(z = vec 0)} INTER
                    {z:real^3 | ~(z = vec 0) /\ (inv(norm z) % z)$3 < &1 /\
                                norm(stereo2_n(inv(norm z) % z)) < r} =
                    {z:real^3 | ~(z = vec 0) /\ (inv(norm z) % z)$3 < &1 /\
                                norm(stereo2_n(inv(norm z) % z)) < r}` SUBST1_TAC THENL
       [SET_TAC[]; ASM_REWRITE_TAC[]]];
    EXISTS_TAC `{z:real^3 | ~(z = vec 0) /\ ~(inv(norm z) % z = --(basis 3))}` THEN
    ASM_REWRITE_TAC[BEL_OPEN_V1; IN_ELIM_THM] THEN
    SUBGOAL_THEN `{z:real^3 | ~(z = vec 0)} INTER
                  {z:real^3 | ~(z = vec 0) /\ ~(inv(norm z) % z = --(basis 3))} =
                  {z:real^3 | ~(z = vec 0) /\ ~(inv(norm z) % z = --(basis 3))}` SUBST1_TAC THENL
     [SET_TAC[]; ASM_SIMP_TAC[BEL_JFAM_HN_V1]]]);;

(* Conformality of h from the round metric to G.                              *)

let BEL_JAC_APPLY = prove
 (`!f:real^M->real^N x v.
        f differentiable at x ==> jacobian f (at x) ** v = frechet_derivative f (at x) v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[jacobian] THEN
  SUBGOAL_THEN `linear(frechet_derivative (f:real^M->real^N) (at x))`
  (fun th -> REWRITE_TAC[MATCH_MP MATRIX_WORKS th]) THEN
  UNDISCH_TAC `(f:real^M->real^N) differentiable at x` THEN
  REWRITE_TAC[FRECHET_DERIVATIVE_WORKS] THEN SIMP_TAC[has_derivative]);;

let BEL_HN_DIFF = prove
 (`!G t y. bel_hyp G /\ t IN real_interval[&0,&1] /\ ~(y = vec 0)
           ==> (\z. bel_h G t (inv(norm z) % z)) differentiable at y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN ASM_REWRITE_TAC[OPEN_NONZERO; IN_ELIM_THM] THEN
  MP_TAC(SPEC `G:real->real^3->real^3^3` BEL_JFAM_HN) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `0`) THEN REWRITE_TAC[bel_jfam] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT1) THEN ASM_REWRITE_TAC[]);;

let BEL_NZ_ON_SPHERE = prove
 (`!y:real^3. y IN sphere(vec 0,&1) ==> inv(norm y) % y = y`,
  SIMP_TAC[IN_SPHERE_0; REAL_INV_1; VECTOR_MUL_LID]);;

let BEL_H_CONF_Q = prove
 (`!G t w0. bel_hyp G /\ t IN real_interval[&0,&1]
            ==> ?lam. &0 < lam /\
                      !v w. v dot stereo2_s_inv w0 = &0 /\ w dot stereo2_s_inv w0 = &0
                            ==> (jacobian (\z. bel_h G t (inv(norm z) % z))
                                          (at (stereo2_s_inv w0)) ** v) dot
                                (G t (bel_h G t (stereo2_s_inv w0)) **
                                 (jacobian (\z. bel_h G t (inv(norm z) % z))
                                           (at (stereo2_s_inv w0)) ** w)) =
                                lam * (v dot w)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Hn = \z:real^3. bel_h (G:real->real^3->real^3^3) t (inv(norm z) % z)` THEN
  SUBGOAL_THEN `(Hn:real^3->real^3) differentiable at (stereo2_s_inv w0)` ASSUME_TAC THENL
   [EXPAND_TAC "Hn" THEN MATCH_MP_TAC BEL_HN_DIFF THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[BEL_P_CHART; NORM_0; REAL_ARITH `~(&1 = &0)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Hn:real^3->real^3) o stereo2_s_inv =
                bel_X1 (G:real->real^3->real^3^3) t o bel_K2 G t` ASSUME_TAC THENL
   [EXPAND_TAC "Hn" THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
    SIMP_TAC[BEL_NZ_ON_SPHERE; STEX_STEREO2_S_INV_IN; IN_DELETE; BEL_H_Q] THEN
    MESON_TAC[STEX_STEREO2_S_INV_IN; IN_DELETE; BEL_NZ_ON_SPHERE; BEL_H_Q];
    ALL_TAC] THEN
  MP_TAC(SPEC `G:real->real^3->real^3^3` BEL_STEP2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "jk2")
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
      (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "conf")))))) THEN
  USE_THEN "conf" (fun th -> MP_TAC(MATCH_MP (SPECL [`t:real`; `w0:complex`] th)
                                             (ASSUME `t IN real_interval[&0,&1]`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `lam2:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `bel_K2 (G:real->real^3->real^3^3) t differentiable at w0 /\
                bel_X1 G t differentiable at (bel_K2 G t w0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(:complex)` THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    MATCH_MP_TAC BEL_JFAM_SMOOTH THEN EXISTS_TAC `0` THEN
    ASM_SIMP_TAC[BEL_JFAM_X1] THEN USE_THEN "jk2" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  ABBREV_TAC `s = norm(w0:complex) pow 2 + &1` THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[STEX_INV_STEREO_DENOM]; ALL_TAC] THEN
  EXISTS_TAC `lam2 * s pow 2 / &4` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_POW_LT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`v:real^3`; `v':real^3`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`w0:complex`; `v:real^3`] BEL_Q_SPAN) THEN
  MP_TAC(ISPECL [`w0:complex`; `v':real^3`] BEL_Q_SPAN) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^2` (SUBST1_TAC o SYM)) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^2` (SUBST1_TAC o SYM)) THEN
  ASM_SIMP_TAC[BEL_JAC_APPLY] THEN
  MP_TAC(ISPECL [`stereo2_s_inv`; `Hn:real^3->real^3`; `w0:complex`] BEL_FRECHET_CHAIN) THEN
  ASM_REWRITE_TAC[BEL_P_FRECHET] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!c. frechet_derivative (Hn:real^3->real^3) (at (stereo2_s_inv w0)) (bel_dQ w0 c) =
                    frechet_derivative (bel_X1 (G:real->real^3->real^3^3) t o bel_K2 G t)
                      (at w0) c` (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN ASM_REWRITE_TAC[o_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `bel_h (G:real->real^3->real^3^3) t (stereo2_s_inv w0) =
                (bel_X1 G t o bel_K2 G t) w0` SUBST1_TAC THENL
   [REWRITE_TAC[o_THM; BEL_H_Q]; ALL_TAC] THEN
  MP_TAC(ISPECL [`bel_K2 (G:real->real^3->real^3^3) t`; `bel_X1 (G:real->real^3->real^3^3) t`;
                 `w0:complex`] BEL_FRECHET_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G (t:real):real^3->real^3^3`; `bel_X1 (G:real->real^3->real^3^3) t o bel_K2 G t`;
                 `w0:complex`; `a:real^2`; `b:real^2`] BEL_PULL_QUAD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`G (t:real):real^3->real^3^3`; `bel_X1 (G:real->real^3->real^3^3) t`;
                 `bel_K2 (G:real->real^3->real^3^3) t`; `w0:complex`; `a:real^2`; `b:real^2`]
                BEL_PULL_COMPOSE_QUAD) THEN
  ASM_REWRITE_TAC[GSYM bel_B1] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[BEL_Q_CONF] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD);;

let BEL_H_CONF_S = prove
 (`!G t. bel_hyp G /\ t IN real_interval[&0,&1]
         ==> ?lam. &0 < lam /\
                   !v w. v dot --(basis 3) = &0 /\ w dot --(basis 3) = &0
                         ==> (jacobian (\z. bel_h G t (inv(norm z) % z))
                                       (at (--(basis 3))) ** v) dot
                             (G t (bel_h G t (--(basis 3))) **
                              (jacobian (\z. bel_h G t (inv(norm z) % z))
                                        (at (--(basis 3))) ** w)) =
                             lam * (v dot w)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Hn = \z:real^3. bel_h (G:real->real^3->real^3^3) t (inv(norm z) % z)` THEN
  SUBGOAL_THEN `(Hn:real^3->real^3) differentiable at (--(basis 3))` ASSUME_TAC THENL
   [EXPAND_TAC "Hn" THEN MATCH_MP_TAC BEL_HN_DIFF THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VECTOR_NEG_EQ_0] THEN SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  MP_TAC(SPEC `G:real->real^3->real^3^3` BEL_STEP2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC
         (CONJUNCTS_THEN2 (LABEL_TAC "pole") (K ALL_TAC)))) (K ALL_TAC)))))) THEN
  REMOVE_THEN "pole" (fun th -> MP_TAC(MATCH_MP th (ASSUME `t IN real_interval[&0,&1]`))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  ABBREV_TAC `Ps = bel_pole (bel_K2 (G:real->real^3->real^3^3) t)` THEN
  SUBGOAL_THEN `(Ps:complex->complex) (Cx(&0)) = Cx(&0)` ASSUME_TAC THENL
   [EXPAND_TAC "Ps" THEN REWRITE_TAC[bel_pole]; ALL_TAC] THEN
  SUBGOAL_THEN `(Ps:complex->complex) complex_differentiable at (Cx(&0)) /\
                ~(complex_derivative Ps (Cx(&0)) = Cx(&0))` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `Cx(&0) IN ball(Cx(&0),r)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[CENTRE_IN_BALL]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT THEN
    EXISTS_TAC `ball(Cx(&0),r)` THEN ASM_SIMP_TAC[OPEN_BALL];
    ALL_TAC] THEN
  MP_TAC(SPECL [`G:real->real^3->real^3^3`; `t:real`] BEL_K1_DIFF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  MP_TAC(SPECL [`G:real->real^3->real^3^3`; `t:real`] BEL_K1_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  MP_TAC(SPEC `G:real->real^3->real^3^3` BEL_MU1_BOUND) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`bel_mu1 (G:real->real^3->real^3^3)`; `&2`; `k:real`;
                 `bel_A (G:real->real^3->real^3^3)`; `t:real`; `Cx(&0)`] BEL_STEP_CONF) THEN
  REWRITE_TAC[GSYM bel_K1] THEN ASM_REWRITE_TAC[BEL_MU1_SUPP] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_SIMP_TAC[BEL_JFAM_MU1]; ALL_TAC] THEN
    CONJ_TAC THENL [MATCH_MP_TAC BEL_A_PDM; MATCH_MP_TAC BEL_MU1_ONE] THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_0; REAL_POS];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam1:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(Hn:real^3->real^3) o stereo2_n_inv =
                stereo2_n_inv o (bel_K1 (G:real->real^3->real^3^3) t o Ps)` ASSUME_TAC THENL
   [EXPAND_TAC "Hn" THEN EXPAND_TAC "Ps" THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
    GEN_TAC THEN
    SUBGOAL_THEN `!u. inv(norm(stereo2_n_inv u)) % stereo2_n_inv u = stereo2_n_inv u`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN MATCH_MP_TAC BEL_NZ_ON_SPHERE THEN
      MESON_TAC[STEX_STEREO2_N_INV_IN; IN_DELETE];
      MP_TAC(ISPECL [`G:real->real^3->real^3^3`; `t:real`; `x:complex`] BEL_H_P) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Ps:complex->complex) differentiable at (Cx(&0)) /\
                (!h. frechet_derivative Ps (at (Cx(&0))) h =
                     complex_derivative Ps (Cx(&0)) * h)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPLEX_DIFFERENTIABLE_IMP_DIFFERENTIABLE] THEN
    UNDISCH_TAC `(Ps:complex->complex) complex_differentiable at (Cx(&0))` THEN
    REWRITE_TAC[GSYM HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE; has_complex_derivative] THEN
    DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Ps:complex->complex`; `bel_K1 (G:real->real^3->real^3^3) t`; `Cx(&0)`]
                BEL_FRECHET_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`stereo2_n_inv`; `Hn:real^3->real^3`; `Cx(&0)`] BEL_FRECHET_CHAIN) THEN
  ASM_REWRITE_TAC[BEL_P_FRECHET; BEL_P_ZERO] THEN STRIP_TAC THEN
  ABBREV_TAC `c2 = complex_derivative (Ps:complex->complex) (Cx(&0))` THEN
  EXISTS_TAC `lam1 * norm(c2:complex) pow 2 / &4` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_POW_LT; COMPLEX_NORM_NZ] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`v:real^3`; `v':real^3`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`Cx(&0)`; `v:real^3`] BEL_P_SPAN) THEN
  MP_TAC(ISPECL [`Cx(&0)`; `v':real^3`] BEL_P_SPAN) THEN
  ASM_REWRITE_TAC[BEL_P_ZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^2` (SUBST1_TAC o SYM)) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^2` (SUBST1_TAC o SYM)) THEN
  ASM_SIMP_TAC[BEL_JAC_APPLY] THEN
  SUBGOAL_THEN `!d. frechet_derivative (Hn:real^3->real^3) (at (--(basis 3))) (bel_dP (Cx(&0)) d) =
                    frechet_derivative (stereo2_n_inv o (bel_K1 (G:real->real^3->real^3^3) t o Ps))
                      (at (Cx(&0))) d` (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN ASM_REWRITE_TAC[o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `bel_h (G:real->real^3->real^3^3) t (--(basis 3)) =
                (stereo2_n_inv o (bel_K1 G t o Ps)) (Cx(&0))` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[o_THM; BEL_P_ZERO; bel_h]; ALL_TAC] THEN
  MP_TAC(ISPECL [`bel_K1 (G:real->real^3->real^3^3) t o (Ps:complex->complex)`; `stereo2_n_inv`;
                 `Cx(&0)`] BEL_FRECHET_CHAIN) THEN
  ASM_REWRITE_TAC[BEL_P_FRECHET] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G (t:real):real^3->real^3^3`;
                 `stereo2_n_inv o (bel_K1 (G:real->real^3->real^3^3) t o (Ps:complex->complex))`;
                 `Cx(&0)`; `a:real^2`; `b:real^2`] BEL_PULL_QUAD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`G (t:real):real^3->real^3^3`; `stereo2_n_inv`;
                 `bel_K1 (G:real->real^3->real^3^3) t o (Ps:complex->complex)`; `Cx(&0)`;
                 `a:real^2`; `b:real^2`] BEL_PULL_COMPOSE_QUAD) THEN
  ASM_REWRITE_TAC[BEL_P_FRECHET; GSYM bel_A; o_THM] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[o_THM] THEN
  REWRITE_TAC[BEL_P_CONF; COMPLEX_NORM_0] THEN
  REWRITE_TAC[DOT_COMPLEX_MUL_CNJ; COMPLEX_SQNORM] THEN
  REWRITE_TAC[complex_mul; cnj; RE; IM] THEN CONV_TAC REAL_RING);;

let BEL_H_CONF = prove
 (`!G t y. bel_hyp G /\ t IN real_interval[&0,&1] /\ y IN sphere(vec 0,&1)
           ==> ?lam. &0 < lam /\
                     !v w. v dot y = &0 /\ w dot y = &0
                           ==> (jacobian (\z. bel_h G t (inv(norm z) % z)) (at y) ** v) dot
                               (G t (bel_h G t y) **
                                (jacobian (\z. bel_h G t (inv(norm z) % z)) (at y) ** w)) =
                               lam * (v dot w)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `y = --(basis 3):real^3` THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC BEL_H_CONF_S THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `y = stereo2_s_inv(stereo2_s y)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC STEX_STEREO2_S_LEFT THEN ASM_REWRITE_TAC[IN_DELETE];
    MATCH_MP_TAC BEL_H_CONF_Q THEN ASM_REWRITE_TAC[]]);;

let BEL_JAC_PARTIAL = prove
 (`!f:real^3->real^3 z i j.
        1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
        ==> jacobian f (at z)$i$j = partial_derivative j f z$i`,
  SIMP_TAC[jacobian; MATRIX_COMPONENT; DIMINDEX_3; partial_derivative]);;

let BEL_DOM_NONZERO = prove
 (`bel_dom {z:real^3 | ~(z = vec 0)} =
   {x:real^(3,1)finite_sum | ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1]}`,
  REWRITE_TAC[EXTENSION; BEL_IN_DOM; IN_ELIM_THM]);;

let BEL_H_JCONT = prove
 (`!G. bel_hyp G
       ==> (\x:real^(3,1)finite_sum.
               bel_h G (drop(sndcart x)) (inv(norm(fstcart x)) % fstcart x))
           continuous_on
           {x | ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1]} /\
           (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
                  ==> (\x:real^(3,1)finite_sum.
                         lift(jacobian (\z. bel_h G (drop(sndcart x)) (inv(norm z) % z))
                                       (at (fstcart x))$i$j))
                      continuous_on
                      {x | ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1]})`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM BEL_DOM_NONZERO] THEN
  MP_TAC(SPEC `G:real->real^3->real^3^3` BEL_JFAM_HN) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "j") THEN CONJ_TAC THENL
   [USE_THEN "j" (MP_TAC o SPEC `0`) THEN REWRITE_TAC[BEL_JFAM_0] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `\x:real^(3,1)finite_sum.
                lift(partial_derivative j
                       ((\t z. bel_h (G:real->real^3->real^3^3) t (inv(norm z) % z))
                          (drop(sndcart x))) (fstcart x)$i)` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[BEL_JAC_PARTIAL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`0`; `{z:real^3 | ~(z = vec 0)}`;
                 `\t. partial_derivative j
                        ((\t z. bel_h (G:real->real^3->real^3^3) t (inv(norm z) % z)) t)`;
                 `i:num`] BEL_JFAM_COMPONENT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[OPEN_NONZERO] THEN MATCH_MP_TAC BEL_JFAM_PD THEN
    ASM_REWRITE_TAC[OPEN_NONZERO; DIMINDEX_3] THEN USE_THEN "j" (fun th -> REWRITE_TAC[th]);
    REWRITE_TAC[BEL_JFAM_0] THEN SIMP_TAC[]]);;

(* The round case: h is the identity.                                          *)

let BEL_POLE_ID = prove
 (`bel_pole (\z:complex. z) = (\w. w)`,
  REWRITE_TAC[FUN_EQ_THM; bel_pole] THEN GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[BEL_T_INVOL]);;

let BEL_NF_ZERO = prove
 (`!mu:real->complex->complex t.
        mu t = (\z. Cx(&0)) ==> bel_nf mu t = (\z. z) /\ bel_nk mu t = (\z. z)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `bel_nf (mu:real->complex->complex) t = (\z. z)` ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; bel_nf] THEN ASM_REWRITE_TAC[BEL_FSOL_ZERO] THEN
    REWRITE_TAC[COMPLEX_SUB_RZERO];
    ASM_REWRITE_TAC[bel_nk; BEL_HINV_ID]]);;

let BEL_ROUND_PULL = prove
 (`!M (Y:real^2->real^3) dY c w.
        (Y has_derivative dY w) (at w) /\
        (!a. Y w dot dY w a = &0) /\
        (?s. !a b. dY w a dot dY w b = s * (a dot b)) /\
        (!v v'. v dot Y w = &0 /\ v' dot Y w = &0 ==> v dot (M (Y w) ** v') = c * (v dot v'))
        ==> bel_mu (bel_pull M Y w) = Cx(&0)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_TAC `s:real`) ASSUME_TAC))) THEN
  MATCH_MP_TAC BEL_MU_ZERO THEN EXISTS_TAC `c * s:real` THEN REPEAT GEN_TAC THEN
  SUBGOAL_THEN `(Y:real^2->real^3) differentiable at w /\
                frechet_derivative Y (at w) = dY (w:real^2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[BEL_PULL_QUAD] THEN
  W(fun (asl,g) -> MP_TAC(SPECL [lhand(lhand g); rand(rand(lhand g))]
      (ASSUME `!v v'. v dot (Y:real^2->real^3) w = &0 /\ v' dot Y w = &0
                      ==> v dot (M (Y w) ** v') = c * (v dot v')`))) THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let BEL_H_ROUND = prove
 (`!G t. bel_hyp G /\ t IN real_interval[&0,&1] /\
         (?c. !y v w. y IN sphere(vec 0,&1) /\ v dot y = &0 /\ w dot y = &0
                      ==> v dot (G t y ** w) = c * (v dot w))
         ==> !y. y IN sphere(vec 0,&1) ==> bel_h G t y = y`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `c:real` (LABEL_TAC "c")))) THEN
  SUBGOAL_THEN `bel_mu1 (G:real->real^3->real^3^3) t = (\z. Cx(&0))` ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; bel_mu1; bel_A] THEN X_GEN_TAC `z:complex` THEN
    SUBGOAL_THEN `bel_mu (bel_pull ((G:real->real^3->real^3^3) t) stereo2_n_inv z) = Cx(&0)`
    (fun th -> REWRITE_TAC[th; COMPLEX_MUL_RZERO]) THEN
    MATCH_MP_TAC BEL_ROUND_PULL THEN
    MAP_EVERY EXISTS_TAC [`bel_dP`; `c:real`] THEN
    REWRITE_TAC[BEL_P_HAS_DERIVATIVE; BEL_P_TANG] THEN CONJ_TAC THENL
     [EXISTS_TAC `&4 / (norm(z:complex) pow 2 + &1) pow 2` THEN REWRITE_TAC[BEL_P_CONF];
      REPEAT STRIP_TAC THEN USE_THEN "c" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MESON_TAC[STEX_STEREO2_N_INV_IN; IN_DELETE]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`bel_mu1 (G:real->real^3->real^3^3)`; `t:real`] BEL_NF_ZERO) THEN
  ASM_REWRITE_TAC[GSYM bel_K1] THEN STRIP_TAC THEN
  SUBGOAL_THEN `bel_X1 (G:real->real^3->real^3^3) t = stereo2_s_inv` ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN ASM_SIMP_TAC[BEL_X1_Q; BEL_POLE_ID]; ALL_TAC] THEN
  SUBGOAL_THEN `bel_mu2 (G:real->real^3->real^3^3) t = (\z. Cx(&0))` ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; bel_mu2; bel_B1] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `w:complex` THEN MATCH_MP_TAC BEL_ROUND_PULL THEN
    MAP_EVERY EXISTS_TAC [`bel_dQ`; `c:real`] THEN
    REWRITE_TAC[BEL_Q_HAS_DERIVATIVE; BEL_Q_TANG] THEN CONJ_TAC THENL
     [EXISTS_TAC `&4 / (norm(w:complex) pow 2 + &1) pow 2` THEN REWRITE_TAC[BEL_Q_CONF];
      REPEAT STRIP_TAC THEN USE_THEN "c" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MESON_TAC[STEX_STEREO2_S_INV_IN; IN_DELETE]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`bel_mu2 (G:real->real^3->real^3^3)`; `t:real`] BEL_NF_ZERO) THEN
  ASM_REWRITE_TAC[GSYM bel_K2] THEN STRIP_TAC THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN REWRITE_TAC[bel_h] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC STEX_STEREO2_S_LEFT THEN ASM_REWRITE_TAC[IN_DELETE]);;

(* The headline theorem.                                                       *)

let BEL_D7_HYP = prove
 (`!G:real->real^3->real^3^3.
       (!t i j. t IN real_interval[&0,&1] /\
                1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
                ==> smooth_map_on {z:real^3 | ~(z = vec 0)}
                      (\z. lift(G t (inv(norm z) % z)$i$j))) /\
       (!l i j. ALL (\k. 1 <= k /\ k <= 3) l /\
                1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
                ==> (\x:real^(3,1)finite_sum.
                       iterated_partial l
                         (\z. lift(G (drop(sndcart x)) (inv(norm z) % z)$i$j))
                         (fstcart x))
                    continuous_on
                    {x | ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1]}) /\
       (!t y. t IN real_interval[&0,&1] /\ y IN sphere(vec 0,&1)
              ==> transp(G t y) = G t y) /\
       (?c. &0 < c /\
            !t y v. t IN real_interval[&0,&1] /\ y IN sphere(vec 0,&1) /\ v dot y = &0
                    ==> c * (v dot v) <= v dot (G t y ** v))
       ==> bel_hyp G`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[bel_hyp] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[]] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[bel_jfam; DIMINDEX_3; BEL_DOM_NONZERO] THEN
  ASM_SIMP_TAC[]);;

let CM_D7_UNIFORMIZATION = prove
 (`CM_D7_UNIFORMIZATION_STATEMENT`,
  REWRITE_TAC[CM_D7_UNIFORMIZATION_STATEMENT] THEN GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP BEL_D7_HYP) THEN
  EXISTS_TAC `bel_h (G:real->real^3->real^3^3)` THEN
  ASM_SIMP_TAC[BEL_H_JCONT; BEL_H_ROUND] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[BEL_H_BIJ; BEL_H_CONF] THEN
  MP_TAC(SPEC `G:real->real^3->real^3^3` BEL_JFAM_HN) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `0`) THEN REWRITE_TAC[bel_jfam] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT1) THEN ASM_REWRITE_TAC[]);;


