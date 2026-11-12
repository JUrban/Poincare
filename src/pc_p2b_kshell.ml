(* ========================================================================= *)
(* pc_p2b_kshell (Part 2B, a step of the proof of P2B_SPLIT_ROUND_STATEMENT: *)
(* shells from the asymptotic soliton).  Main theorem:                       *)
(*   P2BKS_SHELLS_FROM_LIMIT: a slice limit (Q -> 0) of slices on which a    *)
(*   unit field X is parallel, the parallel limit field Y along a            *)
(*   subsequence (P2BPL_LIMIT_FIELD form) and the cylinder parametrization   *)
(*   p of the limit (P2B_SHRINKER_SPLIT_CYL form) give, for every tk, a      *)
(*   shell psi of annulus(exp(-a), exp a) with a primitive h of gs(X,.) and  *)
(*   abs(h(psi y) - c0 - kappa log(norm y)) <= delta, tk + delta < kappa a:  *)
(*   the hypothesis of P2BKG_SHELL_THICK_FAMILY (pc_p2b_kglob).              *)
(* Route: pointwise, the coordinate form of phi_n o p is                     *)
(* sqrt(2 lam / Q_n) y / |y|^2 up to Q_n^(-1/2) o(1)                         *)
(* (P2BKS_PFORM_CLOSE_POINT, from the slice closeness, the limit field       *)
(* closeness and the data of P2B_SHRINKER_SPLIT_CYL); the shell estimate in  *)
(* coordinates (slab pullbacks, P2BKG_SHELL_OSC) turns this into the         *)
(* logarithmic estimate (P2BKS_SHELL_FROM_FORM); the index n is chosen with  *)
(* Q_n small (kappa_n large, delta_n <= kappa_n / 2).  The U4 in theorem     *)
(* names such as P2BKS_U4_PARAM refers to P2B_SHRINKER_SPLIT_CYL.            *)
(* ========================================================================= *)

needs "src/pc_p2b_kglob.ml";;
needs "src/pc_p2b_parlim.ml";;
needs "src/pc_geo_s3.ml";;
needs "src/pc_geo_dist.ml";;
needs "src/pc_lrg_stab.ml";;
needs "src/pc_lrg_tensor.ml";;
needs "src/pc_top_cover.ml";;

prioritize_real();;
type_invention_error := true;;

(* P2BKS.S1 Slab pullbacks are bounded by the form (generic): on a closed  *)
(* slab piece norm(pr2 z) <= 1, a <= z$3 <= b the derivatives of the slab  *)
(* maps p2bpc_ann_n, p2bpc_ann_s are bounded (compactness), so             *)
(* norm(p2bpc_pull an u z) <= C norm(u(an z)) with C depending on a, b.    *)

let P2BKS_SLAB_PIECE_COMPACT = prove
 (`!a b. compact {z:real^3 | norm(p2bpc_pr2 z) <= &1 /\ a <= z$3 /\ z$3 <= b}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
   [REWRITE_TAC[BOUNDED_POS; IN_ELIM_THM] THEN EXISTS_TAC `&2 + abs a + abs b` THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:3)) (\i. abs((z:real^3)$i))` THEN
    REWRITE_TAC[NORM_LE_L1; DIMINDEX_3; SUM_3] THEN
    MP_TAC(ISPECL [`p2bpc_pr2 (z:real^3)`; `1`] COMPONENT_LE_NORM) THEN
    MP_TAC(ISPECL [`p2bpc_pr2 (z:real^3)`; `2`] COMPONENT_LE_NORM) THEN
    REWRITE_TAC[P2BPC_PR2_COMPONENTS] THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `{z:real^3 | norm(p2bpc_pr2 z) <= &1 /\ a <= z$3 /\ z$3 <= b} =
                  {z | p2bpc_pr2 z IN cball(vec 0,&1)} INTER {z | z$3 >= a} INTER
                  {z | z$3 <= b}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_CBALL_0; real_ge]; ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC CLOSED_INTER THEN CONJ_TAC) THEN
    REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_GE; CLOSED_HALFSPACE_COMPONENT_LE] THEN
    MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_UNIV THEN
    REWRITE_TAC[CLOSED_CBALL] THEN GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
    REWRITE_TAC[P2BPC_PR2_LINEAR]]);;

let P2BKS_SLAB_DERIV_BOUND = prove
 (`!(tau:real^3->real^3) a b j.
     smooth_map_on (:real^3) tau
     ==> ?B. &0 < B /\
             !z. norm(p2bpc_pr2 z) <= &1 /\ a <= z$3 /\ z$3 <= b
                 ==> norm(frechet_derivative tau (at z) (basis j)) <= B`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z. frechet_derivative (tau:real^3->real^3) (at z) (basis j)) continuous_on
                {z:real^3 | norm(p2bpc_pr2 z) <= &1 /\ a <= z$3 /\ z$3 <= b}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z. frechet_derivative (tau:real^3->real^3) (at z) (basis j)`;
                 `{z:real^3 | norm(p2bpc_pr2 z) <= &1 /\ a <= z$3 /\ z$3 <= b}`]
                COMPACT_CONTINUOUS_IMAGE) THEN
  ASM_REWRITE_TAC[P2BKS_SLAB_PIECE_COMPACT] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[]);;

let P2BKS_PULL_NORM_BOUND = prove
 (`!(tau:real^3->real^3) (u:real^3->real^3) z B1 B2 B3.
     norm(frechet_derivative tau (at z) (basis 1)) <= B1 /\
     norm(frechet_derivative tau (at z) (basis 2)) <= B2 /\
     norm(frechet_derivative tau (at z) (basis 3)) <= B3
     ==> norm(p2bpc_pull tau u z) <= (B1 + B2 + B3) * norm(u(tau z))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:3)) (\i. abs((p2bpc_pull tau u z:real^3)$i))` THEN
  REWRITE_TAC[NORM_LE_L1; DIMINDEX_3; SUM_3] THEN
  SIMP_TAC[p2bpc_pull; LAMBDA_BETA; DIMINDEX_3; ARITH] THEN
  MP_TAC(ISPECL [`(u:real^3->real^3)((tau:real^3->real^3) z)`;
                 `frechet_derivative (tau:real^3->real^3) (at z) (basis 1)`]
                NORM_CAUCHY_SCHWARZ_ABS) THEN
  MP_TAC(ISPECL [`(u:real^3->real^3)((tau:real^3->real^3) z)`;
                 `frechet_derivative (tau:real^3->real^3) (at z) (basis 2)`]
                NORM_CAUCHY_SCHWARZ_ABS) THEN
  MP_TAC(ISPECL [`(u:real^3->real^3)((tau:real^3->real^3) z)`;
                 `frechet_derivative (tau:real^3->real^3) (at z) (basis 3)`]
                NORM_CAUCHY_SCHWARZ_ABS) THEN
  SUBGOAL_THEN `&0 <= norm((u:real^3->real^3)((tau:real^3->real^3) z))` MP_TAC THENL
   [REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  ABBREV_TAC `n = norm((u:real^3->real^3)((tau:real^3->real^3) z))` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `n * norm(frechet_derivative (tau:real^3->real^3) (at z) (basis 1)) <= n * B1 /\
                n * norm(frechet_derivative tau (at z) (basis 2)) <= n * B2 /\
                n * norm(frechet_derivative tau (at z) (basis 3)) <= n * B3`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2BKS_SLAB_PULL_BOUND = prove
 (`!a b. ?C. &0 < C /\
        !(u:real^3->real^3) z.
           norm(p2bpc_pr2 z) <= &1 /\ a <= z$3 /\ z$3 <= b
           ==> norm(p2bpc_pull p2bpc_ann_n u z) <= C * norm(u(p2bpc_ann_n z)) /\
               norm(p2bpc_pull p2bpc_ann_s u z) <= C * norm(u(p2bpc_ann_s z))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `smooth_map_on (:real^3) p2bpc_ann_n /\ smooth_map_on (:real^3) p2bpc_ann_s`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[P2BPC_ANN_N_SMOOTH; P2BPC_ANN_S_SMOOTH; OPEN_UNIV]; ALL_TAC] THEN
  MAP_EVERY (fun (t,j,v) ->
    MP_TAC(ISPECL [t; `a:real`; `b:real`; j] P2BKS_SLAB_DERIV_BOUND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN v STRIP_ASSUME_TAC))
   [`p2bpc_ann_n`,`1`,`n1:real`; `p2bpc_ann_n`,`2`,`n2:real`; `p2bpc_ann_n`,`3`,`n3:real`;
    `p2bpc_ann_s`,`1`,`s1:real`; `p2bpc_ann_s`,`2`,`s2:real`; `p2bpc_ann_s`,`3`,`s3:real`] THEN
  EXISTS_TAC `(n1 + n2 + n3) + (s1 + s2 + s3):real` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
   [EXISTS_TAC `(n1 + n2 + n3) * norm((u:real^3->real^3)(p2bpc_ann_n z))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2BKS_PULL_NORM_BOUND THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC];
    EXISTS_TAC `(s1 + s2 + s3) * norm((u:real^3->real^3)(p2bpc_ann_s z))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2BKS_PULL_NORM_BOUND THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC]]);;

(* P2BKS.S2 The shell estimate from closeness of the form (generic): a       *)
(* primitive H of a covector field w on annulus r1 r2 with                   *)
(* norm(w y - kappa y / norm(y)^2) <= e satisfies                            *)
(* abs(H y - c0 - kappa log(norm y)) <= C e for one c0, C depending only on  *)
(* r1, r2: the slab pullbacks of kappa y / norm(y)^2 are kappa e_3           *)
(* (P2BKS_PULL_RADIAL), the slab bound P2BKS_SLAB_PULL_BOUND and             *)
(* P2BKG_SHELL_OSC.                                                          *)

let P2BKS_ANN_DOT_DERIV = prove
 (`!(an:real^3->real^3) z v.
     smooth_map_on (:real^3) an /\ (!z. norm(an z) = exp(z$3))
     ==> an z dot frechet_derivative an (at z) v = exp(&2 * z$3) * v$3`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^3)`; `an:real^3->real^3`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN
  ABBREV_TAC `D = frechet_derivative (an:real^3->real^3) (at z)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(((\x. lift(norm x pow 2)) o (an:real^3->real^3)) has_derivative
                 ((\x. &2 % lift(an z dot x)) o D)) (at z)` MP_TAC THENL
   [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[HAS_DERIVATIVE_SQNORM_AT]; ALL_TAC] THEN
  SUBGOAL_THEN `(\x. lift(norm x pow 2)) o (an:real^3->real^3) =
                (lift o exp o drop) o (\x:real^3. lift(&2 * x$3))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP] THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[REAL_POW_2; GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(((lift o exp o drop) o (\x:real^3. lift(&2 * x$3))) has_derivative
                 ((\x. exp(&2 * z$3) % x) o (\x:real^3. lift(&2 * x$3)))) (at z)` MP_TAC THENL
   [MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
      REWRITE_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      REWRITE_TAC[GSYM LIFT_ADD; GSYM LIFT_CMUL] THEN REPEAT STRIP_TAC THEN
      AP_TERM_TAC THEN REAL_ARITH_TAC;
      REWRITE_TAC[GSYM HAS_REAL_FRECHET_DERIVATIVE_AT; HAS_REAL_DERIVATIVE_EXP]];
    ALL_TAC] THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_UNIQUE_AT) THEN
  DISCH_THEN(MP_TAC o C AP_THM `v:real^3`) THEN
  REWRITE_TAC[o_THM] THEN DISCH_THEN(MP_TAC o AP_TERM `drop`) THEN
  REWRITE_TAC[DROP_CMUL; LIFT_DROP] THEN REAL_ARITH_TAC);;

let P2BKS_PULL_RADIAL = prove
 (`!(an:real^3->real^3) kappa z.
     smooth_map_on (:real^3) an /\ (!z. norm(an z) = exp(z$3))
     ==> p2bpc_pull an (\y. (kappa / norm y pow 2) % y) z = kappa % basis 3`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[CART_EQ; p2bpc_pull; LAMBDA_BETA; DIMINDEX_3; FORALL_3; ARITH] THEN
  ASM_SIMP_TAC[DOT_LMUL; P2BKS_ANN_DOT_DERIV; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
               DIMINDEX_3; ARITH] THEN
  SUBGOAL_THEN `exp(&2 * (z:real^3)$3) = exp(z$3) pow 2` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_2; GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `(z:real^3)$3` REAL_EXP_NZ) THEN CONV_TAC REAL_FIELD);;

let P2BKS_PULL_SUB = prove
 (`!(tau:real^N->real^N) u v z.
     p2bpc_pull tau (\y. u y - v y) z = p2bpc_pull tau u z - p2bpc_pull tau v z`,
  SIMP_TAC[CART_EQ; p2bpc_pull; LAMBDA_BETA; VECTOR_SUB_COMPONENT; DOT_LSUB]);;

let P2BKS_SHELL_ESTIMATE = prove
 (`!r1 r2. &0 < r1 /\ r1 < r2
   ==> ?C. &0 < C /\
       !(w:real^3->real^3) (H:real^3->real^1) kappa e.
          (!y. y IN annulus r1 r2 ==> (H has_derivative (\v. lift(w y dot v))) (at y)) /\
          (!y. y IN annulus r1 r2 ==> norm(w y - (kappa / norm y pow 2) % y) <= e)
          ==> ?c0. !y. y IN annulus r1 r2
                       ==> abs((drop(H y) - c0) - kappa * log(norm y)) <= C * e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`log r1`; `log r2`] P2BKS_SLAB_PULL_BOUND) THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "slab"))) THEN
  SUBGOAL_THEN `log r1 < log r2` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `&2 * B * (&4 + (log r2 - log r1))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`r1:real`; `r2:real`; `w:real^3->real^3`; `H:real^3->real^1`; `kappa:real`;
                 `B * e:real`] P2BKG_SHELL_OSC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `smooth_map_on (:real^3) p2bpc_ann_n /\ smooth_map_on (:real^3) p2bpc_ann_s`
    STRIP_ASSUME_TAC THENL
     [SIMP_TAC[P2BPC_ANN_N_SMOOTH; P2BPC_ANN_S_SMOOTH; OPEN_UNIV]; ALL_TAC] THEN
    SUBGOAL_THEN `!an:real^3->real^3.
                    smooth_map_on (:real^3) an /\ (!z. norm(an z) = exp(z$3))
                    ==> p2bpc_pull an w z - kappa % basis 3 =
                        p2bpc_pull an (\y. w y - (kappa / norm y pow 2) % y) z /\
                        an z IN annulus r1 r2`
    (LABEL_TAC "an") THENL
     [GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
       [REWRITE_TAC[P2BKS_PULL_SUB] THEN ASM_SIMP_TAC[P2BKS_PULL_RADIAL] THEN
        REWRITE_TAC[ETA_AX];
        ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN
        SUBGOAL_THEN `&0 < r2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MP_TAC(SPEC `r1:real` EXP_LOG) THEN MP_TAC(SPEC `r2:real` EXP_LOG) THEN
        ASM_REWRITE_TAC[] THEN
        REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
        ASM_REWRITE_TAC[REAL_EXP_MONO_LT]];
      ALL_TAC] THEN
    USE_THEN "an" (fun th ->
      MP_TAC(MATCH_MP th (CONJ (ASSUME `smooth_map_on (:real^3) p2bpc_ann_n`)
                               P2BPC_ANN_N_NORM)) THEN
      MP_TAC(MATCH_MP th (CONJ (ASSUME `smooth_map_on (:real^3) p2bpc_ann_s`)
                               P2BPC_ANN_S_NORM))) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
    USE_THEN "slab" (MP_TAC o SPECL [`\y:real^3. w y - (kappa / norm y pow 2) % y`; `z:real^3`]) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN (ASSUME_TAC o BETA_RULE)) THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `B * norm((w:real^3->real^3)(p2bpc_ann_n z) -
                           (kappa / norm(p2bpc_ann_n z) pow 2) % p2bpc_ann_n z)`;
      EXISTS_TAC `B * norm((w:real^3->real^3)(p2bpc_ann_s z) -
                           (kappa / norm(p2bpc_ann_s z) pow 2) % p2bpc_ann_s z)`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  DISCH_TAC THEN
  EXISTS_TAC `drop((H:real^3->real^1)(((r1 + r2) / &2) % basis 1)) -
              kappa * log(norm(((r1 + r2) / &2) % basis 1:real^3))` THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^3`; `((r1 + r2) / &2) % basis 1:real^3`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[annulus; IN_ELIM_THM; NORM_MUL] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b /\ c = d ==> abs a <= c ==> abs b <= d`) THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* P2BKS.S3 The primitive read through a parametrization (generic): for h  *)
(* a primitive of g(X,.) on V and psi an mfd_param of an open s into V,    *)
(* h o psi has the coordinate form p2bkg_pform as derivative (chain rule   *)
(* in the preferred chart, P2BKG_PFORM_LOCAL).                             *)

let P2BKS_PRIM_PARAM_DERIV = prove
 (`!top atlas (g:A->real^3^3) (X:A->real^3) V h s (psi:real^3->A) y.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     open_in top V /\ p2bkg_prim atlas g X V h /\
     open s /\ mfd_param top atlas s psi /\ IMAGE psi s SUBSET V /\ y IN s
     ==> ((\z. lift(h(psi z))) has_derivative
          (\v. lift(p2bkg_pform atlas g X psi y dot v))) (at y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bkg_prim] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(psi:real^3->A) y IN V` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(psi:real^3->A) y IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(psi:real^3->A) y`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `s:real^3->bool`; `psi:real^3->A`;
                 `chart_at (atlas:((A->bool)#(A->real^3))->bool) ((psi:real^3->A) y)`; `y:real^3`]
                P2BKG_PFORM_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) ((psi:real^3->A) y)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `s:real^3->bool`;
                 `psi:real^3->A`; `c:(A->bool)#(A->real^3)`] P2BKG_PARAM_CHART_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `Oc = {z:real^3 | z IN s /\ (psi:real^3->A) z IN FST(c:(A->bool)#(A->real^3))}` THEN
  SUBGOAL_THEN `(y:real^3) IN Oc` ASSUME_TAC THENL
   [EXPAND_TAC "Oc" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `((\z. SND (c:(A->bool)#(A->real^3)) ((psi:real^3->A) z)) has_derivative
                 frechet_derivative (\z. SND c (psi z)) (at y)) (at y)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`Oc:real^3->bool`; `\z. SND (c:(A->bool)#(A->real^3)) ((psi:real^3->A) z)`]
                  SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z. SND (c:(A->bool)#(A->real^3)) ((psi:real^3->A) z)) differentiable at y`
  ASSUME_TAC THENL [REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[P2BPC_PULL_DOT] THEN
  ABBREV_TAC `D = frechet_derivative (\z. SND (c:(A->bool)#(A->real^3)) ((psi:real^3->A) z)) (at y)` THEN
  SUBGOAL_THEN
   `((\u. lift((h:A->real)(chart_inv (c:(A->bool)#(A->real^3)) u))) has_derivative
     (\u. lift(p2bkg_cform atlas (g:A->real^3^3) (X:A->real^3) c (SND c ((psi:real^3->A) y)) dot u)))
    (at (SND c (psi y)))` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    EXISTS_TAC `(psi:real^3->A) y` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(((\u. lift((h:A->real)(chart_inv (c:(A->bool)#(A->real^3)) u))) o
      (\z. SND c ((psi:real^3->A) z))) has_derivative
     ((\u. lift(p2bkg_cform atlas (g:A->real^3^3) (X:A->real^3) c (SND c (psi y)) dot u)) o D))
    (at y)` MP_TAC THENL
   [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[o_DEF] THEN DISCH_TAC THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
  EXISTS_TAC `\z. lift((h:A->real)(chart_inv (c:(A->bool)#(A->real^3))
                                    (SND c ((psi:real^3->A) z))))` THEN
  EXISTS_TAC `Oc:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "Oc" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[]);;

(* P2BKS.S4 A shell whose coordinate form is close to kappa d log r gives a *)
(* primitive with the logarithmic estimate (generic): the primitive of      *)
(* P2BKG_SHELL_PRIMITIVE, its coordinate derivative                         *)
(* (P2BKS_PRIM_PARAM_DERIV) and P2BKS_SHELL_ESTIMATE.                       *)

let P2BKS_SHELL_FROM_FORM = prove
 (`!a. &0 < a
   ==> ?C. &0 < C /\
       !top atlas (g:A->real^3^3) (X:A->real^3) W (psi:real^3->A) kappa e.
          smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ open_in top W /\
          p2b_parallel_on atlas g W X /\
          mfd_param top atlas (annulus (exp(--a)) (exp a)) psi /\
          IMAGE psi (annulus (exp(--a)) (exp a)) SUBSET W /\
          (!y. y IN annulus (exp(--a)) (exp a)
               ==> norm(p2bkg_pform atlas g X psi y - (kappa / norm y pow 2) % y) <= e)
          ==> ?h c0. p2bkg_prim atlas g X (IMAGE psi (annulus (exp(--a)) (exp a))) h /\
                     !y. y IN annulus (exp(--a)) (exp a)
                         ==> abs((h(psi y) - c0) - kappa * log(norm y)) <= C * e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`exp(--a)`; `exp a`] P2BKS_SHELL_ESTIMATE) THEN
  REWRITE_TAC[REAL_EXP_POS_LT; REAL_EXP_MONO_LT] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "est"))) THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `W:A->bool`; `exp(--a)`; `exp a`; `psi:real^3->A`]
                P2BKG_SHELL_PRIMITIVE) THEN
  ASM_REWRITE_TAC[REAL_EXP_POS_LT; REAL_EXP_MONO_LT] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:A->real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `p2bkg_prim atlas (g:A->real^3^3) (X:A->real^3)
                  (IMAGE (psi:real^3->A) (annulus (exp(--a)) (exp a))) h` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[p2bkg_prim]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (IMAGE (psi:real^3->A) (annulus (exp(--a)) (exp a)))` ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_param top (atlas:((A->bool)#(A->real^3))->bool)
                           (annulus (exp(--a)) (exp a)) psi` THEN
    REWRITE_TAC[mfd_param] THEN DISCH_THEN(X_CHOOSE_TAC `e':A->real^3`) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `annulus (exp(--a)) (exp a):real^3->bool`; `psi:real^3->A`; `e':A->real^3`]
                  LVS_DIFFEO_FACTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "est" (MP_TAC o SPECL [`p2bkg_pform atlas (g:A->real^3^3) (X:A->real^3) (psi:real^3->A)`;
                                  `\z. lift((h:A->real)((psi:real^3->A) z))`; `kappa:real`; `e:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC P2BKS_PRIM_PARAM_DERIV THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`;
                          `IMAGE (psi:real^3->A) (annulus (exp(--a)) (exp a))`;
                          `annulus (exp(--a)) (exp a):real^3->bool`] THEN
    ASM_REWRITE_TAC[P2BPC_ANNULUS_OPEN; SUBSET_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN(X_CHOOSE_TAC `c0:real`) THEN
  MAP_EVERY EXISTS_TAC [`h:A->real`; `c0:real`] THEN ASM_REWRITE_TAC[]);;

(* P2BKS.S5 Chain rule for a smooth map after a parametrization: for an     *)
(* mfd_param Fm of an open U and a smooth map F1 on an open W               *)
(* containing Fm z, the derivative of the chart expression of F1 o Fm at z  *)
(* is mfd_differential F1 composed with the derivative of the chart         *)
(* expression of Fm (local version of P2BKF_MDIFF_CHAIN).                   *)

let P2BKS_MDIFF_CHAIN_PARAM = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) top' (atlas':((B->bool)#(B->real^3))->bool)
    (Fm:real^3->A) (F1:A->B) U W z.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
     open U /\ mfd_param top atlas U Fm /\ z IN U /\
     open_in top W /\ Fm z IN W /\ continuous_map (subtopology top W,top') F1 /\
     mfd_smooth_map atlas atlas' W F1
     ==> frechet_derivative (\y. SND(chart_at atlas' (F1(Fm z))) (F1(Fm y))) (at z) =
         mfd_differential atlas atlas' F1 (Fm z) o
         frechet_derivative (\y. SND(chart_at atlas (Fm z)) (Fm y)) (at z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(Fm:real^3->A) z IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(F1:A->B) ((Fm:real^3->A) z) IN topspace top'` ASSUME_TAC THENL
   [UNDISCH_TAC `continuous_map (subtopology top W,top') (F1:A->B)` THEN
    REWRITE_TAC[CONTINUOUS_MAP; SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `mfd_param top (atlas:((A->bool)#(A->real^3))->bool) U Fm` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  REWRITE_TAC[mfd_param] THEN DISCH_THEN(X_CHOOSE_TAC `e':A->real^3`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `U:real^3->bool`; `Fm:real^3->A`; `e':A->real^3`] LVS_DIFFEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `(Fm:real^3->A) z`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `p = chart_at (atlas:((A->bool)#(A->real^3))->bool) ((Fm:real^3->A) z)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(F1:A->B) ((Fm:real^3->A) z)`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `p' = chart_at (atlas':((B->bool)#(B->real^3))->bool) ((F1:A->B) ((Fm:real^3->A) z))` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `p:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `p':(B->bool)#(B->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[mfd_differential] THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `R1 = \y. SND (p':(B->bool)#(B->real^3)) ((F1:A->B) (chart_inv (p:(A->bool)#(A->real^3)) y))` THEN
  ABBREV_TAC `R2 = \y. SND (p:(A->bool)#(A->real^3)) ((Fm:real^3->A) y)` THEN
  ABBREV_TAC `S1 = IMAGE (SND (p:(A->bool)#(A->real^3)))
                     {x | x IN FST p INTER W /\ (F1:A->B) x IN FST(p':(B->bool)#(B->real^3))}` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `p:(A->bool)#(A->real^3)`; `p':(B->bool)#(B->real^3)`;
                 `W:A->bool`; `F1:A->B`] MFDM_CHART_DOMAIN_OPEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on S1 (R1:real^3->real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "S1" THEN EXPAND_TAC "R1" THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`p:(A->bool)#(A->real^3)`; `p':(B->bool)#(B->real^3)`] o
      GEN_REWRITE_RULE I [mfd_smooth_map]) THEN
    ASM_REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  SUBGOAL_THEN `SND (p:(A->bool)#(A->real^3)) ((Fm:real^3->A) z) IN S1` ASSUME_TAC THENL
   [EXPAND_TAC "S1" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER];
    ALL_TAC] THEN
  ABBREV_TAC `Oc = {y:real^3 | y IN U /\
                     (Fm:real^3->A) y IN {x | x IN FST(p:(A->bool)#(A->real^3)) INTER W /\
                                              (F1:A->B) x IN FST(p':(B->bool)#(B->real^3))}}` THEN
  SUBGOAL_THEN `open (Oc:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `U:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "Oc" THEN
    MP_TAC(ISPECL [`Fm:real^3->A`; `subtopology euclidean (U:real^3->bool)`; `top:A topology`;
                   `{x | x IN FST(p:(A->bool)#(A->real^3)) INTER W /\
                         (F1:A->B) x IN FST(p':(B->bool)#(B->real^3))}`]
                  OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN; INTER_UNIV; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3) IN Oc` ASSUME_TAC THENL
   [EXPAND_TAC "Oc" THEN ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:real^3->bool`;
                 `Fm:real^3->A`; `p:(A->bool)#(A->real^3)`] P2BKG_PARAM_CHART_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(R2:real^3->real^3) differentiable at z` ASSUME_TAC THENL
   [EXPAND_TAC "R2" THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `{y:real^3 | y IN U /\ (Fm:real^3->A) y IN FST(p:(A->bool)#(A->real^3))}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(R1:real^3->real^3) differentiable at (SND (p:(A->bool)#(A->real^3)) ((Fm:real^3->A) z))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `S1:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
  MAP_EVERY EXISTS_TAC [`(R1:real^3->real^3) o (R2:real^3->real^3)`; `Oc:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [EXPAND_TAC "Oc" THEN EXPAND_TAC "R1" THEN EXPAND_TAC "R2" THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INTER; o_THM] THEN SIMP_TAC[] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `frechet_derivative (\y. SND (p:(A->bool)#(A->real^3)) ((Fm:real^3->A) y)) (at z) =
                frechet_derivative (R2:real^3->real^3) (at z)` SUBST1_TAC THENL
   [EXPAND_TAC "R2" THEN REFL_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `frechet_derivative (\y. SND (p':(B->bool)#(B->real^3))
                   ((F1:A->B)(chart_inv (p:(A->bool)#(A->real^3)) y))) (at (SND p ((Fm:real^3->A) z))) =
                frechet_derivative (R1:real^3->real^3) (at (SND p (Fm z)))` SUBST1_TAC THENL
   [EXPAND_TAC "R1" THEN REFL_TAC; ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    SUBGOAL_THEN `(R2:real^3->real^3) z = SND (p:(A->bool)#(A->real^3)) ((Fm:real^3->A) z)`
    SUBST1_TAC THENL [EXPAND_TAC "R2" THEN REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]]);;

(* P2BKS.S6 Pointwise algebra of the form estimate: Cauchy-Schwarz for      *)
(* (0,2)-tensors in the G-norm (LRG_LTNORM2_BOUND), and the bound           *)
(* abs(zz . Gn P - Y . G0 P) <= (sqrt(3 eps) + sqrt(d eps) + sqrt d) |P|_G0 *)
(* when lck_dist2 m G0 Gn <= d, |zz - Y|_G0^2 <= eps, |Y|_G0 = 1.           *)

let P2BKS_TENSOR_CS = prove
 (`!U (G:real^3->real^3^3) (tf:real^3->(num->real^3)->real) y u v.
     metric_field U G /\ ltensor_field 2 U tf /\ y IN U
     ==> abs(tf y (\m. if m = 1 then u else v)) <=
         sqrt(ltnorm2 2 G tf y) * sqrt(u dot (G y ** u)) * sqrt(v dot (G y ** v))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `U:real^3->bool`; `G:real^3->real^3^3`;
                 `tf:real^3->(num->real^3)->real`; `y:real^3`;
                 `\m:num. if m = 1 then (u:real^3) else v`] LRG_LTNORM2_BOUND) THEN
  ASM_REWRITE_TAC[PRODUCT_2; ARITH] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM SQRT_MUL] THEN MATCH_MP_TAC REAL_LE_RSQRT THEN
  ASM_REWRITE_TAC[REAL_POW2_ABS]);;

let P2BKS_FORM_POINT = prove
 (`!s (G0:real^3->real^3^3) Gn y0 m zz Yv Pj eps d.
     metric_field s G0 /\ metric_field s Gn /\ y0 IN s /\
     lck_dist2 m G0 Gn y0 <= d /\
     (zz - Yv) dot (G0 y0 ** (zz - Yv)) <= eps /\ Yv dot (G0 y0 ** Yv) = &1
     ==> abs(zz dot (Gn y0 ** Pj) - Yv dot (G0 y0 ** Pj)) <=
         (sqrt(&3 * eps) + sqrt(d * eps) + sqrt d) * sqrt(Pj dot (G0 y0 ** Pj))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `G0:real^3->real^3^3`] LRG_LMETRIC2_FIELD) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `G0:real^3->real^3^3`; `Gn:real^3->real^3^3`]
                LRG_LMETRIC2_DIFF_FIELD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `G0:real^3->real^3^3`; `y0:real^3`] LRG_LTNORM2_METRIC) THEN
  ASM_REWRITE_TAC[DIMINDEX_3] THEN DISCH_TAC THEN
  ABBREV_TAC `Ld = ltnorm2 2 (G0:real^3->real^3^3)
                     (\z u. lmetric2 (Gn:real^3->real^3^3) z u - lmetric2 G0 z u) y0` THEN
  SUBGOAL_THEN `&0 <= Ld /\ Ld <= d` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Ld" THEN CONJ_TAC THENL
     [MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `lck_dist2 m (G0:real^3->real^3^3) Gn y0` THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`m:num`; `0`; `s:real^3->bool`; `G0:real^3->real^3^3`; `Gn:real^3->real^3^3`;
                     `y0:real^3`] LRG_LCK_DIST2_TERM_LE) THEN
      ASM_REWRITE_TAC[LE_0; lnabla_iter; ADD_CLAUSES]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u:real^3. &0 <= u dot ((G0:real^3->real^3^3) y0 ** u)` ASSUME_TAC THENL
   [GEN_TAC THEN ASM_CASES_TAC `u:real^3 = vec 0` THENL
     [ASM_REWRITE_TAC[DOT_LZERO; REAL_LE_REFL];
      MATCH_MP_TAC REAL_LT_IMP_LE THEN
      UNDISCH_TAC `metric_field s (G0:real^3->real^3^3)` THEN REWRITE_TAC[metric_field] THEN
      DISCH_THEN(MP_TAC o SPEC `y0:real^3` o CONJUNCT2 o CONJUNCT2) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `u = zz - Yv:real^3` THEN
  ABBREV_TAC `nP = sqrt(Pj dot ((G0:real^3->real^3^3) y0 ** Pj))` THEN
  SUBGOAL_THEN `abs(u dot ((G0:real^3->real^3^3) y0 ** Pj)) <= sqrt(&3 * eps) * nP` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^3->bool`; `G0:real^3->real^3^3`; `lmetric2 (G0:real^3->real^3^3)`;
                   `y0:real^3`; `u:real^3`; `Pj:real^3`] P2BKS_TENSOR_CS) THEN
    ASM_REWRITE_TAC[lmetric2; ARITH] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN EXPAND_TAC "nP" THEN
    REWRITE_TAC[SQRT_MUL; REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LE THEN REAL_ARITH_TAC;
        MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC SQRT_POS_LE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^3. abs(v dot ((Gn:real^3->real^3^3) y0 ** Pj) - v dot (G0 y0 ** Pj)) <=
                           sqrt d * sqrt(v dot (G0 y0 ** v)) * nP` ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`s:real^3->bool`; `G0:real^3->real^3^3`;
                   `\z u. lmetric2 (Gn:real^3->real^3^3) z u - lmetric2 G0 z u`;
                   `y0:real^3`; `v:real^3`; `Pj:real^3`] P2BKS_TENSOR_CS) THEN
    ASM_REWRITE_TAC[lmetric2; ARITH] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN EXPAND_TAC "nP" THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC SQRT_POS_LE THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC SQRT_POS_LE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `zz dot ((Gn:real^3->real^3^3) y0 ** Pj) - Yv dot (G0 y0 ** Pj) =
                u dot (G0 y0 ** Pj) +
                (u dot (Gn y0 ** Pj) - u dot (G0 y0 ** Pj)) +
                (Yv dot (Gn y0 ** Pj) - Yv dot (G0 y0 ** Pj))` SUBST1_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[DOT_LSUB] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `u:real^3`) THEN FIRST_X_ASSUM(MP_TAC o SPEC `Yv:real^3`) THEN
  ASM_REWRITE_TAC[SQRT_1; REAL_MUL_RID; REAL_MUL_LID] THEN
  SUBGOAL_THEN `sqrt d * sqrt(u dot ((G0:real^3->real^3^3) y0 ** u)) * nP <= sqrt(d * eps) * nP`
  MP_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [REWRITE_TAC[SQRT_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]];
      EXPAND_TAC "nP" THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `abs(u dot ((G0:real^3->real^3^3) y0 ** Pj)) <= sqrt(&3 * eps) * nP` THEN
  REAL_ARITH_TAC);;

(* P2BKS.S7 Algebra for the pointwise form estimate: the time-0 cylinder    *)
(* metric, the bilinear pullback identity, and the shape of the coordinate  *)
(* form of phi o p (chain rule P2BKS_MDIFF_CHAIN_PARAM).                    *)

let P2BKS_CYL0 = prove
 (`!y:real^3. cylinder_flow (&0) y = (&2 / norm y pow 2) %% mat 1`,
  GEN_TAC THEN REWRITE_TAC[cylinder_flow; REAL_SUB_RZERO; real_div; REAL_MUL_LZERO;
                           MATRIX_CMUL_LZERO; MATRIX_ADD_RID; MATRIX_CMUL_LID]);;

let P2BKS_DOT_PULLBACK_BILIN = prove
 (`!(M:real^3^3) (G:real^3^3) a b.
     (M ** a) dot (G ** (M ** b)) = a dot ((transp M ** G ** M) ** b)`,
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL]);;

let P2BKS_PFORM_COMPOSE = prove
 (`!top atlas top1 atlas1 (g1:A->real^3^3) (X:A->real^3) (phi:B->A) phi' W
    (p:real^3->B) U y zz.
     smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top1 atlas1 /\
     mfd_diffeo top atlas W top1 atlas1 (IMAGE phi W) phi phi' /\
     open U /\ mfd_param top atlas U p /\ IMAGE p U SUBSET W /\ y IN U /\
     mfd_differential atlas atlas1 phi (p y) zz = X(phi(p y))
     ==> !j. 1 <= j /\ j <= 3
             ==> (p2bkg_pform atlas1 g1 X (phi o p) y)$j =
                 zz dot ((transp(matrix(mfd_differential atlas atlas1 phi (p y))) **
                          g1(phi(p y)) ** matrix(mfd_differential atlas atlas1 phi (p y))) **
                         frechet_derivative (\z. SND(chart_at atlas (p y)) (p z)) (at y)
                                            (basis j))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo]) THEN
  SUBGOAL_THEN `(p:real^3->B) y IN W` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (subtopology top W,top1) (phi:B->A)` ASSUME_TAC THENL
   [UNDISCH_TAC `homeomorphic_maps (subtopology top W,subtopology top1 (IMAGE (phi:B->A) W))
                                   (phi,phi')` THEN
    REWRITE_TAC[homeomorphic_maps; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `top1:A topology`; `atlas1:((A->bool)#(A->real^3))->bool`;
                 `p:real^3->B`; `phi:B->A`; `U:real^3->bool`; `W:B->bool`; `y:real^3`]
                P2BKS_MDIFF_CHAIN_PARAM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SIMP_TAC[p2bkg_pform; LAMBDA_BETA; DIMINDEX_3; ASSUME `1 <= j`; ASSUME `j <= 3`] THEN
  REWRITE_TAC[o_THM] THEN ASM_REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN `linear(mfd_differential (atlas:((B->bool)#(B->real^3))->bool)
                        (atlas1:((A->bool)#(A->real^3))->bool) (phi:B->A) ((p:real^3->B) y))`
  ASSUME_TAC THENL
   [REWRITE_TAC[mfd_differential] THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    SUBGOAL_THEN `(p:real^3->B) y IN topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `(p:real^3->B) y`]
                  CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(phi:B->A) ((p:real^3->B) y) IN topspace top1` ASSUME_TAC THENL
     [UNDISCH_TAC `continuous_map (subtopology top W,top1) (phi:B->A)` THEN
      REWRITE_TAC[CONTINUOUS_MAP; SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top1:A topology`; `atlas1:((A->bool)#(A->real^3))->bool`;
                   `(phi:B->A) ((p:real^3->B) y)`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `top1:A topology`; `atlas1:((A->bool)#(A->real^3))->bool`;
                   `chart_at (atlas:((B->bool)#(B->real^3))->bool) ((p:real^3->B) y)`;
                   `chart_at (atlas1:((A->bool)#(A->real^3))->bool) ((phi:B->A) ((p:real^3->B) y))`;
                   `W:B->bool`; `phi:B->A`] MFDM_CHART_DOMAIN_OPEN) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) ((p:real^3->B) y)))
                  {x | x IN FST(chart_at atlas (p y)) INTER W /\
                       (phi:B->A) x IN FST(chart_at (atlas1:((A->bool)#(A->real^3))->bool) (phi(p y)))}` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `mfd_smooth_map (atlas:((B->bool)#(B->real^3))->bool)
                    (atlas1:((A->bool)#(A->real^3))->bool) W (phi:B->A)` THEN REWRITE_TAC[mfd_smooth_map] THEN
      DISCH_THEN(MP_TAC o SPECL [`chart_at (atlas:((B->bool)#(B->real^3))->bool) ((p:real^3->B) y)`;
                                 `chart_at (atlas1:((A->bool)#(A->real^3))->bool) ((phi:B->A) ((p:real^3->B) y))`]) THEN
      ASM_REWRITE_TAC[o_DEF];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER]];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP MATRIX_WORKS th)]) THEN
  UNDISCH_TAC `mfd_differential (atlas:((B->bool)#(B->real^3))->bool)
                 (atlas1:((A->bool)#(A->real^3))->bool) (phi:B->A) ((p:real^3->B) y) zz =
                (X:A->real^3)(phi(p y))` THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP MATRIX_WORKS th)]) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[P2BKS_DOT_PULLBACK_BILIN]);;

(* P2BKS.S8A Real-number rescaling step of the pointwise form estimate.     *)

let P2BKS_REAL_SCALE = prove
 (`!Q lam ny K yj Bd.
     &0 < Q /\ &0 < lam /\ &0 < ny /\
     abs(inv(sqrt Q) * Q * K - (lam * &2 / ny pow 2) * inv (sqrt (&2 * lam)) * yj) <=
     Bd * sqrt((lam * &2 / ny pow 2) * &1)
     ==> abs(K - sqrt (&2 * lam / Q) / ny pow 2 * yj) <=
         inv(sqrt Q) * Bd * sqrt(&2 * lam) / ny`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt Q /\ &0 < sqrt(&2 * lam)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt Q pow 2 = Q /\ sqrt(&2 * lam) pow 2 = &2 * lam` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt((lam * &2 / ny pow 2) * &1) = sqrt(&2 * lam) / ny` ASSUME_TAC THENL
   [SUBGOAL_THEN `(lam * &2 / ny pow 2) * &1 = (&2 * lam) / ny pow 2` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < ny` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    REWRITE_TAC[SQRT_DIV] THEN AP_TERM_TAC THEN MATCH_MP_TAC POW_2_SQRT THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&2 * lam / Q) = sqrt(&2 * lam) / sqrt Q` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SQRT_DIV] THEN AP_TERM_TAC THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `abs(inv(sqrt Q) * Q * K - (lam * &2 / ny pow 2) * inv (sqrt (&2 * lam)) * yj) <=
               Bd * sqrt((lam * &2 / ny pow 2) * &1)` THEN
  ASM_REWRITE_TAC[SQRT_DIV] THEN
  ABBREV_TAC `sQ = sqrt Q` THEN ABBREV_TAC `sL = sqrt(&2 * lam)` THEN
  SUBGOAL_THEN `inv sQ * Q * K - (lam * &2 / ny pow 2) * inv sL * yj =
                sQ * (K - sL / sQ / ny pow 2 * yj)` SUBST1_TAC THENL
   [UNDISCH_TAC `sQ pow 2 = Q` THEN UNDISCH_TAC `sL pow 2 = &2 * lam` THEN
    UNDISCH_TAC `&0 < sQ` THEN UNDISCH_TAC `&0 < sL` THEN UNDISCH_TAC `&0 < ny` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_MUL; REAL_ARITH `&0 < x ==> abs x = x`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `inv sQ * Bd * sL / ny = (Bd * sL / ny) / sQ` SUBST1_TAC THENL
   [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC);;
(* P2BKS.S8 The pointwise form estimate: at a shell point y where the limit *)
(* data hold (P2B_SHRINKER_SPLIT_CYL: p^* g0 = lam cyl(0),                  *)
(* Y = dp(y/sqrt(2 lam)) in the chart; parallel limit field: dphi zz = X    *)
(* with |Q^(-1/2) zz - Y|_g0^2 <= eps; slice limit: lck_dist2 <= d), the    *)
(* coordinate form of phi o p is close to sqrt(2 lam / Q) y / |y|^2.        *)

let P2BKS_PFORM_CLOSE_POINT = prove
 (`!top atlas (g0:B->real^3^3) (Y:B->real^3) top1 atlas1 (g1:A->real^3^3) (X:A->real^3)
    (phi:B->A) phi' W (p:real^3->B) U lam Q y zz eps d m.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g0 /\
     smooth_manifold_atlas top1 atlas1 /\ riemannian_metric atlas1 g1 /\
     mfd_diffeo top atlas W top1 atlas1 (IMAGE phi W) phi phi' /\
     open U /\ mfd_param top atlas U p /\ IMAGE p U SUBSET W /\ y IN U /\ ~(y = vec 0) /\
     &0 < lam /\ &0 < Q /\
     rfs_pullback atlas p g0 y = lam %% cylinder_flow (&0) y /\
     Y(p y) = frechet_derivative (\z. SND(chart_at atlas (p y)) (p z)) (at y)
                                 (inv(sqrt(&2 * lam)) % y) /\
     Y(p y) dot (g0(p y) ** Y(p y)) = &1 /\
     mfd_differential atlas atlas1 phi (p y) zz = X(phi(p y)) /\
     (inv(sqrt Q) % zz - Y(p y)) dot (g0(p y) ** (inv(sqrt Q) % zz - Y(p y))) <= eps /\
     lck_dist2 m (metric_local atlas (chart_at atlas (p y)) g0)
                 (metric_local atlas (chart_at atlas (p y))
                    (\x. Q %% mfd_pullback_metric atlas atlas1 phi g1 x))
                 (SND(chart_at atlas (p y)) (p y)) <= d
     ==> norm(p2bkg_pform atlas1 g1 X (phi o p) y - (sqrt(&2 * lam / Q) / norm y pow 2) % y) <=
         &3 * (inv(sqrt Q) * (sqrt(&3 * eps) + sqrt(d * eps) + sqrt d) *
               sqrt(&2 * lam) / norm y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  SUBGOAL_THEN `open_in top (W:B->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_diffeo]; ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3->B) y IN W` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3->B) y IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(phi:B->A) ((p:real^3->B) y) IN topspace top1` ASSUME_TAC THENL
   [UNDISCH_TAC `continuous_map (subtopology top W,top1) (phi:B->A)` THEN
    REWRITE_TAC[CONTINUOUS_MAP; SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `(p:real^3->B) y`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `top1:A topology`;
                 `atlas1:((A->bool)#(A->real^3))->bool`; `g1:A->real^3^3`; `X:A->real^3`;
                 `phi:B->A`; `phi':A->B`; `W:B->bool`; `p:real^3->B`; `U:real^3->bool`;
                 `y:real^3`; `zz:real^3`] P2BKS_PFORM_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "pf") THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `top1:A topology`;
                 `atlas1:((A->bool)#(A->real^3))->bool`; `phi:B->A`; `g1:A->real^3^3`;
                 `(p:real^3->B) y`] P2BPL_PB_METRIC_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `\x. Q %% mfd_pullback_metric (atlas:((B->bool)#(B->real^3))->bool)
                               (atlas1:((A->bool)#(A->real^3))->bool) (phi:B->A) (g1:A->real^3^3) x`;
                 `(p:real^3->B) y`] METRIC_LOCAL_AT) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                 `(p:real^3->B) y`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  ABBREV_TAC `c' = chart_at (atlas:((B->bool)#(B->real^3))->bool) ((p:real^3->B) y)` THEN
  ABBREV_TAC `P = frechet_derivative (\z. SND (c':(B->bool)#(B->real^3)) ((p:real^3->B) z)) (at y)` THEN
  ABBREV_TAC `Mg = transp(matrix(mfd_differential (atlas:((B->bool)#(B->real^3))->bool)
                                   (atlas1:((A->bool)#(A->real^3))->bool) (phi:B->A) ((p:real^3->B) y))) **
                   (g1:A->real^3^3)(phi(p y)) ** matrix(mfd_differential atlas atlas1 phi (p y))` THEN
  ABBREV_TAC `z0 = SND (c':(B->bool)#(B->real^3)) ((p:real^3->B) y)` THEN
  SUBGOAL_THEN `linear (P:real^3->real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `U:real^3->bool`;
                   `p:real^3->B`; `c':(B->bool)#(B->real^3)`] P2BKG_PARAM_CHART_SMOOTH) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `{z:real^3 | z IN U /\ (p:real^3->B) z IN FST(c':(B->bool)#(B->real^3))}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `transp(matrix(P:real^3->real^3)) ** (g0:B->real^3^3)((p:real^3->B) y) ** matrix P =
                (lam * (&2 / norm(y:real^3) pow 2)) %% mat 1` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_pullback (atlas:((B->bool)#(B->real^3))->bool) (p:real^3->B)
                   (g0:B->real^3^3) y = lam %% cylinder_flow (&0) y` THEN
    REWRITE_TAC[rfs_pullback; mpullback; P2BKS_CYL0; MATRIX_CMUL_ASSOC] THEN
    ASM_REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `SND (c':(B->bool)#(B->real^3)) o (p:real^3->B) = (\z. SND c' (p z))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v w:real^3. (P:real^3->real^3) v dot ((g0:B->real^3^3)((p:real^3->B) y) ** P w) =
                             (lam * (&2 / norm(y:real^3) pow 2)) * (v dot w)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[GSYM(MATCH_MP MATRIX_WORKS (ASSUME `linear (P:real^3->real^3)`))] THEN
    REWRITE_TAC[P2BKS_DOT_PULLBACK_BILIN] THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID; DOT_RMUL];
    ALL_TAC] THEN
  ABBREV_TAC `s = IMAGE (SND (c':(B->bool)#(B->real^3))) (FST c' INTER W)` THEN
  SUBGOAL_THEN
   `metric_field s (metric_local (atlas:((B->bool)#(B->real^3))->bool) c'
                     (\x. Q %% mfd_pullback_metric atlas (atlas1:((A->bool)#(A->real^3))->bool)
                                 (phi:B->A) (g1:A->real^3^3) x))`
  ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN MATCH_MP_TAC P2BPL_PULLBACK_METRIC_FIELD THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `top1:A topology`; `IMAGE (phi:B->A) W`; `phi':A->B`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field s (metric_local (atlas:((B->bool)#(B->real^3))->bool) c' (g0:B->real^3^3)) /\
                z0 IN s` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
      EXISTS_TAC `IMAGE (SND (c':(B->bool)#(B->real^3))) (FST c')` THEN REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `riemannian_metric atlas (g0:B->real^3^3)` THEN
        REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `metric_field s (metric_local (atlas:((B->bool)#(B->real^3))->bool) c'
                     (\x. Q %% mfd_pullback_metric atlas (atlas1:((A->bool)#(A->real^3))->bool)
                                 (phi:B->A) (g1:A->real^3^3) x))` THEN
        SIMP_TAC[metric_field];
        EXPAND_TAC "s" THEN SET_TAC[]];
      EXPAND_TAC "s" THEN EXPAND_TAC "z0" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[IN_INTER]];
    ALL_TAC] THEN
  UNDISCH_TAC `(Y:B->real^3)((p:real^3->B) y) = (P:real^3->real^3)(inv(sqrt(&2 * lam)) % y)` THEN
  SUBGOAL_THEN
   `!j. abs((inv(sqrt Q) % (zz:real^3)) dot ((Q %% (Mg:real^3^3)) ** (P:real^3->real^3)(basis j)) -
            (Y:B->real^3)((p:real^3->B) y) dot ((g0:B->real^3^3)(p y) ** P(basis j))) <=
        (sqrt(&3 * eps) + sqrt(d * eps) + sqrt d) *
        sqrt(P(basis j) dot (g0(p y) ** P(basis j)))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`s:real^3->bool`;
                   `metric_local (atlas:((B->bool)#(B->real^3))->bool) c' (g0:B->real^3^3)`;
                   `metric_local (atlas:((B->bool)#(B->real^3))->bool) c'
                     (\x. Q %% mfd_pullback_metric atlas (atlas1:((A->bool)#(A->real^3))->bool)
                                 (phi:B->A) (g1:A->real^3^3) x)`;
                   `z0:real^3`; `m:num`; `inv(sqrt Q) % (zz:real^3)`;
                   `(Y:B->real^3)((p:real^3->B) y)`; `(P:real^3->real^3)(basis j)`;
                   `eps:real`; `d:real`] P2BKS_FORM_POINT) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= 3
        ==> abs((p2bkg_pform atlas1 (g1:A->real^3^3) (X:A->real^3) ((phi:B->A) o (p:real^3->B)) y)$j -
                (sqrt(&2 * lam / Q) / norm(y:real^3) pow 2) * y$j) <=
            inv(sqrt Q) * (sqrt(&3 * eps) + sqrt(d * eps) + sqrt d) * sqrt(&2 * lam) / norm y`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    USE_THEN "pf" (fun th -> REWRITE_TAC[MATCH_MP th (CONJ (ASSUME `1 <= j`) (ASSUME `j <= 3`))]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN
    ASM_SIMP_TAC[DOT_LMUL; DOT_RMUL; MATRIX_VECTOR_LMUL; DOT_BASIS; DOT_BASIS_BASIS; DIMINDEX_3] THEN
    DISCH_TAC THEN MATCH_MP_TAC P2BKS_REAL_SCALE THEN ASM_REWRITE_TAC[NORM_POS_LT];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:3))
                (\i. abs((p2bkg_pform atlas1 (g1:A->real^3^3) (X:A->real^3) ((phi:B->A) o (p:real^3->B)) y -
                          (sqrt(&2 * lam / Q) / norm(y:real^3) pow 2) % y)$i))` THEN
  REWRITE_TAC[NORM_LE_L1; DIMINDEX_3; SUM_3; VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th) THEN MP_TAC(SPEC `3` th)) THEN
  REWRITE_TAC[ARITH] THEN REAL_ARITH_TAC);;

(* P2BKS.S9 Shell parametrizations through a slice-limit diffeomorphism,    *)
(* and invariance of primitives under metrics with the same g X.            *)

let P2BKS_PARAM_DIFFEO_COMPOSE = prove
 (`!top atlas top1 atlas1 (p:real^3->B) (phi:B->A) phi' S W.
     smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
     smooth_manifold_atlas top1 (atlas1:((A->bool)#(A->real^3))->bool) /\
     mfd_param top atlas S p /\ mfd_diffeo top atlas W top1 atlas1 (IMAGE phi W) phi phi' /\
     IMAGE p S SUBSET W
     ==> mfd_param top1 atlas1 S (phi o p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `mfd_param top (atlas:((B->bool)#(B->real^3))->bool) S p` THEN
  REWRITE_TAC[mfd_param] THEN DISCH_THEN(X_CHOOSE_TAC `p':B->real^3`) THEN
  EXISTS_TAC `(p':B->real^3) o (phi':A->B)` THEN
  SUBGOAL_THEN `IMAGE ((phi:B->A) o (p:real^3->B)) S = IMAGE phi (IMAGE p S)` SUBST1_TAC THENL
   [REWRITE_TAC[IMAGE_o]; ALL_TAC] THEN
  MATCH_MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `S:real^3->bool`;
                       `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `IMAGE (p:real^3->B) S`; `top1:A topology`;
                       `atlas1:((A->bool)#(A->real^3))->bool`;
                       `IMAGE (phi:B->A) (IMAGE (p:real^3->B) S)`; `p:real^3->B`; `p':B->real^3`;
                       `phi:B->A`; `phi':A->B`] MFD_DIFFEO_COMPOSE) THEN
  ASM_REWRITE_TAC[LVS_EUCLIDEAN_ATLAS] THEN
  MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN EXISTS_TAC `W:B->bool` THEN
  EXISTS_TAC `IMAGE (phi:B->A) W` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `S:real^3->bool`;
                 `p:real^3->B`; `p':B->real^3`] LVS_DIFFEO_FACTS) THEN
  ASM_SIMP_TAC[]);;

let P2BKS_CFORM_INVARIANT = prove
 (`!top atlas (g:A->real^3^3) g' (X:A->real^3) c y.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ y IN IMAGE (SND c) (FST c) /\
     g' (chart_inv c y) ** X(chart_inv c y) = g (chart_inv c y) ** X(chart_inv c y)
     ==> p2bkg_cform atlas g' X c y = p2bkg_cform atlas g X c y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^3)) y IN FST c` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `x = chart_inv (c:(A->bool)#(A->real^3)) y` THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[p2bkg_cform; metric_local; mfd_vrep] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  SUBGOAL_THEN
   `matrix(chart_jac (c:(A->bool)#(A->real^3)) (chart_at atlas (x:A)) x) **
    chart_jac (chart_at atlas x) c x ((X:A->real^3) x) = X x`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `FST(c:(A->bool)#(A->real^3))`; `SND(c:(A->bool)#(A->real^3))`;
                   `FST(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A))`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A))`; `x:A`]
                  CHART_JAC_LINEAR) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `FST(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A))`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A))`;
                   `FST(c:(A->bool)#(A->real^3))`; `SND(c:(A->bool)#(A->real^3))`; `x:A`]
                  CHART_JAC_INVERSE) THEN
    ASM_REWRITE_TAC[PAIR; IN_INTER] THEN
    DISCH_THEN(MP_TAC o C AP_THM `(X:A->real^3) x`) THEN REWRITE_TAC[o_THM] THEN
    DISCH_TAC THEN DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP MATRIX_WORKS th]) THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

let P2BKS_PRIM_INVARIANT = prove
 (`!top atlas (g:A->real^3^3) g' (X:A->real^3) V h.
     smooth_manifold_atlas top atlas /\ open_in top V /\
     (!x. x IN V ==> g' x ** X x = g x ** X x) /\ p2bkg_prim atlas g X V h
     ==> p2bkg_prim atlas g' X V h`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bkg_prim] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^3)`; `z:real^3`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `p2bkg_cform atlas (g':A->real^3^3) (X:A->real^3) c z = p2bkg_cform atlas g X c z`
  SUBST1_TAC THENL
   [MATCH_MP_TAC P2BKS_CFORM_INVARIANT THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `z IN IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c INTER V)` THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `c:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
    EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* P2BKS.S10 A one-to-one map that is a local parametrization near every    *)
(* point of an open set is a parametrization of the set (the map p of       *)
(* P2B_SHRINKER_SPLIT_CYL on the shell; GEOS_INJECTIVE_PARAM with local     *)
(* continuity and smoothness).                                              *)

let P2BKS_LOCAL_INJ_PARAM = prove
 (`!top atlas (p:real^3->B) S.
     hausdorff_space top /\ smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
     open S /\
     (!y. y IN S ==> ?r. &0 < r /\ ball(y,r) SUBSET S /\ mfd_param top atlas (ball(y,r)) p) /\
     (!y z. y IN S /\ z IN S /\ p y = p z ==> y = z)
     ==> mfd_param top atlas S p`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
    LABEL_TAC "loc" (CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2 th))))) THEN
  SUBGOAL_THEN `!y. y IN S ==> ?r. &0 < r /\ ball(y,r) SUBSET S /\
                                   continuous_map (subtopology euclidean (ball(y,r)),top) (p:real^3->B) /\
                                   mfd_smooth_map (open_set_atlas (:real^3)) atlas (ball(y,r)) p /\
                                   mfd_param top atlas (ball(y,r)) p`
  (LABEL_TAC "loc2") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "loc" (MP_TAC o C MATCH_MP (ASSUME `(y:real^3) IN S`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `mfd_param top (atlas:((B->bool)#(B->real^3))->bool) (ball(y,r)) p` THEN
    REWRITE_TAC[mfd_param] THEN DISCH_THEN(X_CHOOSE_TAC `p':B->real^3`) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_diffeo]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (subtopology euclidean S,top) (p:real^3->B)` ASSUME_TAC THENL
   [MATCH_MP_TAC TOPC_CONTINUOUS_MAP_LOCAL THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "loc2" (MP_TAC o C MATCH_MP (ASSUME `(y:real^3) IN S`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `ball(y:real^3,r)` THEN ASM_SIMP_TAC[CENTRE_IN_BALL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_SUBSET THEN ASM_REWRITE_TAC[OPEN_BALL]; ALL_TAC] THEN
    ASM_SIMP_TAC[SUBTOPOLOGY_SUBTOPOLOGY;
                 SET_RULE `!s t:real^3->bool. s SUBSET t ==> t INTER s = s`];
    ALL_TAC] THEN
  MATCH_MP_TAC GEOS_INJECTIVE_PARAM THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFDD_SMOOTH_MAP_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`euclidean:(real^3)topology`; `top:B topology`] THEN
    ASM_REWRITE_TAC[LVS_EUCLIDEAN_ATLAS; GSYM OPEN_IN] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "loc2" (MP_TAC o C MATCH_MP (ASSUME `(y:real^3) IN S`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `ball(y:real^3,r)` THEN ASM_REWRITE_TAC[GSYM OPEN_IN; OPEN_BALL; CENTRE_IN_BALL];
    MAP_EVERY X_GEN_TAC [`v:real^3`; `h:real^3`] THEN STRIP_TAC THEN
    USE_THEN "loc2" (MP_TAC o C MATCH_MP (ASSUME `(v:real^3) IN S`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                         `ball(v:real^3,r)`; `p:real^3->B`; `v:real^3`; `h:real^3`]
                        GEOD_PARAM_DIFF_INJ) THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL]]);;

(* P2BKS.S11 Two adapters for the output of P2B_SHRINKER_SPLIT_CYL: its      *)
(* cylinder param p is an mfd_param of every open set avoiding 0, and its    *)
(* mfd_differential for the open_set_atlas of real^3 minus 0 is the          *)
(* derivative of its chart expression.                                       *)

let P2BKS_MDIFF_OPEN_SET_LOCAL = prove
 (`!S (atlas:((B->bool)#(B->real^3))->bool) (f:real^3->B) y.
     open S /\ y IN S /\
     (\z. SND(chart_at atlas (f y)) (f z)) differentiable at y
     ==> mfd_differential (open_set_atlas S) atlas f y =
         frechet_derivative (\z. SND(chart_at atlas (f y)) (f z)) (at y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_differential] THEN
  ASM_SIMP_TAC[MFDD_OPEN_SET_CHART_AT] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
  EXISTS_TAC `\z. SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) ((f:real^3->B) y)) (f z)` THEN
  EXISTS_TAC `S:real^3->bool` THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
  ASM_SIMP_TAC[MFDM_CHART_INV_ID]);;

let P2BKS_U4_PARAM = prove
 (`!top atlas (p:real^3->B) S.
     hausdorff_space top /\ smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
     (!y. ~(y = vec 0) ==> ?r. &0 < r /\ r < norm y /\ mfd_param top atlas (ball(y,r)) p) /\
     (!y z. ~(y = vec 0) /\ ~(z = vec 0) ==> (p y = p z <=> z = y)) /\
     open S /\ ~(vec 0 IN S)
     ==> mfd_param top atlas S p`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
    LABEL_TAC "loc" (CONJUNCT1(CONJUNCT2(CONJUNCT2 th)))) THEN
  MATCH_MP_TAC P2BKS_LOCAL_INJ_PARAM THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    USE_THEN "loc" (MP_TAC o C MATCH_MP (ASSUME `~(y:real^3 = vec 0)`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `open(S:real^3->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r':real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min r r'` THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(y:real^3,r')` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC;
      MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `ball(y:real^3,r)` THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC];
    MAP_EVERY X_GEN_TAC [`y:real^3`; `z:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(y:real^3 = vec 0) /\ ~(z:real^3 = vec 0)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[]]);;

(* P2BKS.S12 Choice of constants for the shells: a small eta makes the      *)
(* pointwise bound Bd(eta) = sqrt(3 eta) + sqrt(eta eta) + sqrt eta small,  *)
(* and a small Q makes kappa = sqrt(2 lam / Q) large.                       *)

let P2BKS_ETA_CHOICE = prove
 (`!rho. &0 < rho ==> ?eta. &0 < eta /\ sqrt(&3 * eta) + sqrt(eta * eta) + sqrt eta <= rho`,
  REPEAT STRIP_TAC THEN ABBREV_TAC `u = min rho (&1) / &4` THEN
  SUBGOAL_THEN `&0 < u /\ u <= &1 / &4 /\ &4 * u <= rho` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `u pow 2` THEN CONJ_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(u pow 2) = u /\ sqrt(u pow 2 * u pow 2) = u pow 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SQRT_UNIQUE THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POW_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&3 * u pow 2) <= &2 * u` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_MUL] THEN
    MP_TAC(SPEC `u:real` REAL_LE_POW_2) THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `u pow 2 <= u` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN
    MATCH_MP_TAC(REAL_ARITH `u * u <= u * &1 ==> u * u <= u`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2BKS_KAPPA_BIG = prove
 (`!lam tk. &0 < lam
            ==> ?q0. &0 < q0 /\
                     !Q. &0 < Q /\ Q < q0 ==> &2 * abs tk < sqrt(&2 * lam / Q)`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `(&2 * lam) / (&4 * tk pow 2 + &1)` THEN
  SUBGOAL_THEN `&0 < &4 * tk pow 2 + &1` ASSUME_TAC THENL
   [MP_TAC(SPEC `tk:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `Q:real` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LT_RSQRT THEN
  SUBGOAL_THEN `&2 * lam / Q = (&2 * lam) / Q` SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_ASSOC]; ALL_TAC] THEN
  SUBGOAL_THEN `&4 * tk pow 2 + &1 < (&2 * lam) / Q` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
    UNDISCH_TAC `Q < (&2 * lam) / (&4 * tk pow 2 + &1)` THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_MUL; REAL_POW2_ABS] THEN REAL_ARITH_TAC);;

(* P2BKS.S13 The shell at one index of the slice limit: if at every point   *)
(* of the shell annulus(exp(-1), e) the data of P2B_SHRINKER_SPLIT_CYL, the *)
(* parallel limit field closeness and the slice closeness hold with         *)
(* tolerance eta, then phi o p carries a primitive of g1(X,.) with the      *)
(* logarithmic estimate.                                                    *)

let P2BKS_SHELL_AT_INDEX = prove
 (`?C. &0 < C /\
       !top atlas (g0:B->real^3^3) (Y:B->real^3) top1 atlas1 (g1:A->real^3^3) (X:A->real^3)
        (phi:B->A) phi' W (p:real^3->B) lam Q eta m.
         smooth_manifold_atlas top atlas /\ riemannian_metric atlas g0 /\
         smooth_manifold_atlas top1 atlas1 /\ riemannian_metric atlas1 g1 /\
         p2b_parallel_on atlas1 g1 (topspace top1) X /\
         mfd_diffeo top atlas W top1 atlas1 (IMAGE phi W) phi phi' /\
         mfd_param top atlas (annulus (exp(--(&1))) (exp(&1))) p /\
         IMAGE p (annulus (exp(--(&1))) (exp(&1))) SUBSET W /\
         &0 < lam /\ &0 < Q /\ &0 <= eta /\
         (!y. y IN annulus (exp(--(&1))) (exp(&1))
              ==> rfs_pullback atlas p g0 y = lam %% cylinder_flow (&0) y /\
                  Y(p y) = frechet_derivative (\z. SND(chart_at atlas (p y)) (p z)) (at y)
                                              (inv(sqrt(&2 * lam)) % y) /\
                  Y(p y) dot (g0(p y) ** Y(p y)) = &1 /\
                  (?zz. mfd_differential atlas atlas1 phi (p y) zz = X(phi(p y)) /\
                        (inv(sqrt Q) % zz - Y(p y)) dot
                        (g0(p y) ** (inv(sqrt Q) % zz - Y(p y))) <= eta) /\
                  lck_dist2 m (metric_local atlas (chart_at atlas (p y)) g0)
                              (metric_local atlas (chart_at atlas (p y))
                                 (\x. Q %% mfd_pullback_metric atlas atlas1 phi g1 x))
                              (SND(chart_at atlas (p y)) (p y)) <= eta)
         ==> ?h c0. p2bkg_prim atlas1 g1 X (IMAGE (phi o p) (annulus (exp(--(&1))) (exp(&1)))) h /\
                    !y. y IN annulus (exp(--(&1))) (exp(&1))
                        ==> abs((h((phi o p) y) - c0) - sqrt(&2 * lam / Q) * log(norm y)) <=
                            C * (&3 * (inv(sqrt Q) *
                                       (sqrt(&3 * eta) + sqrt(eta * eta) + sqrt eta) *
                                       sqrt(&2 * lam) * exp(&1)))`,
  MP_TAC(SPEC `&1` P2BKS_SHELL_FROM_FORM) THEN REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sff"))) THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN LABEL_TAC "dat"
    (funpow 11 CONJUNCT2 th)) THEN
  ABBREV_TAC `S = annulus (exp(--(&1))) (exp(&1)):real^3->bool` THEN
  SUBGOAL_THEN `mfd_param top1 atlas1 S ((phi:B->A) o (p:real^3->B))` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BKS_PARAM_DIFFEO_COMPOSE THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                          `phi':A->B`; `W:B->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Bd = sqrt(&3 * eta) + sqrt(eta * eta) + sqrt eta` THEN
  SUBGOAL_THEN `&0 <= Bd` ASSUME_TAC THENL
   [EXPAND_TAC "Bd" THEN MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LE THEN
    ASM_SIMP_TAC[REAL_LE_MUL];
    ALL_TAC] THEN
  USE_THEN "sff" (MP_TAC o SPECL
   [`top1:A topology`; `atlas1:((A->bool)#(A->real^3))->bool`; `g1:A->real^3^3`;
    `X:A->real^3`; `topspace top1:A->bool`; `(phi:B->A) o (p:real^3->B)`;
    `sqrt(&2 * lam / Q)`;
    `&3 * (inv(sqrt Q) * Bd * sqrt(&2 * lam) * exp(&1))`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_IN_TOPSPACE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_IMAGE_SUBSET THEN
      MAP_EVERY EXISTS_TAC [`atlas1:((A->bool)#(A->real^3))->bool`; `S:real^3->bool`] THEN
      ASM_REWRITE_TAC[SUBSET_REFL];
      ALL_TAC] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "dat" (MP_TAC o C MATCH_MP (ASSUME `(y:real^3) IN S`)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `zz:real^3` STRIP_ASSUME_TAC) ASSUME_TAC)))) THEN
    SUBGOAL_THEN `exp(--(&1)) < norm(y:real^3)` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN S` THEN EXPAND_TAC "S" THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `exp(--(&1)) < norm(y:real^3)` THEN
      ASM_REWRITE_TAC[NORM_0] THEN MP_TAC(SPEC `--(&1)` REAL_EXP_POS_LT) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&3 * (inv(sqrt Q) * (sqrt(&3 * eta) + sqrt(eta * eta) + sqrt eta) *
                      sqrt(&2 * lam) / norm(y:real^3))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(ISPECL
       [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `Y:B->real^3`;
        `top1:A topology`; `atlas1:((A->bool)#(A->real^3))->bool`; `g1:A->real^3^3`;
        `X:A->real^3`; `phi:B->A`; `phi':A->B`; `W:B->bool`; `p:real^3->B`; `S:real^3->bool`;
        `lam:real`; `Q:real`; `y:real^3`; `zz:real^3`; `eta:real`; `eta:real`; `m:num`]
       P2BKS_PFORM_CLOSE_POINT) THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      EXPAND_TAC "S" THEN REWRITE_TAC[P2BPC_ANNULUS_OPEN];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [REWRITE_TAC[REAL_LE_INV_EQ; SQRT_POS_LE] THEN
                    MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `exp(&1) = inv(exp(--(&1)))` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_EXP_NEG; REAL_NEG_NEG]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_EXP_POS_LT];
    ALL_TAC] THEN
  REWRITE_TAC[o_THM]);;

(* P2BKS.S14A Arithmetic for the choice of the shell index.                  *)

let P2BKS_DELTA_HALF = prove
 (`!C e1 Bd a b.
     &0 < C /\ &0 < e1 /\ &0 <= Bd /\ Bd <= inv(&6 * C * e1) /\ &0 <= a /\ &0 <= b
     ==> C * (&3 * (a * Bd * b * e1)) <= (b * a) / &2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `C * (&3 * (a * Bd * b * e1)) = (&3 * C * e1 * a * b) * Bd` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&3 * C * e1 * a * b) * inv(&6 * C * e1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    UNDISCH_TAC `&0 < C` THEN UNDISCH_TAC `&0 < e1` THEN CONV_TAC REAL_FIELD]);;

let P2BKS_KAPPA_SPLIT = prove
 (`!lam Q. &0 < lam /\ &0 < Q ==> sqrt(&2 * lam / Q) = sqrt(&2 * lam) * inv(sqrt Q)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM real_div; GSYM SQRT_DIV] THEN
  AP_TERM_TAC THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;
(* P2BKS.S14 Shells of every thickness from the asymptotic soliton: a slice *)
(* limit with Q -> 0 of slices on which X is parallel and unit, the         *)
(* parallel limit field Y along a subsequence, and the cylinder             *)
(* parametrization p of the limit (P2B_SHRINKER_SPLIT_CYL) give, for every  *)
(* tk, a shell (psi, h, a, kappa, delta, c0) with tk + delta < kappa a (the *)
(* hypothesis of P2BKG_SHELL_THICK_FAMILY), primitives taken for the        *)
(* reference metric gs (gs X = g_n X for all n).                            *)

let P2BKS_SHELLS_FROM_LIMIT = prove
 (`!V x t Q top atlas (g0:B->real^3^3) xl W (phi:num->B->A) (top1:A topology) atlas1
    (gs:A->real^3^3) (X:A->real^3) sub (Y:B->real^3) (p:real^3->B) lam.
     p2c_slice_limit_with V x t Q (top,atlas) g0 xl W phi /\
     (!n. rfs_vtop (V n) (t n) = top1 /\ rfs_vatlas (V n) (t n) = atlas1) /\
     hausdorff_space top1 /\ smooth_manifold_atlas top1 atlas1 /\
     (!n. riemannian_metric atlas1 (rfs_vmetric (V n) (t n)) /\
          p2b_parallel_on atlas1 (rfs_vmetric (V n) (t n)) (topspace top1) X /\
          (!y. y IN topspace top1 ==> rfs_vmetric (V n) (t n) y ** X y = gs y ** X y)) /\
     (!e. &0 < e ==> ?n0. !n. n0 <= n ==> Q n < e) /\
     p3_subseq sub /\
     (!y. y IN topspace top ==> Y y dot (g0 y ** Y y) = &1) /\
     (!K e. compact_in top K /\ &0 < e
            ==> ?n0. !n. n0 <= n
                         ==> !y. y IN K
                                 ==> ?z. mfd_differential atlas atlas1 (phi (sub n)) y z =
                                         X (phi (sub n) y) /\
                                         (inv(sqrt(Q(sub n))) % z - Y y) dot
                                         (g0 y ** (inv(sqrt(Q(sub n))) % z - Y y)) < e) /\
     &0 < lam /\
     (!y. ~(y = vec 0) ==> ?r. &0 < r /\ r < norm y /\ mfd_param top atlas (ball(y,r)) p) /\
     (!y z. ~(y = vec 0) /\ ~(z = vec 0) ==> (p y = p z <=> z = y)) /\
     (!y. ~(y = vec 0) ==> rfs_pullback atlas p g0 y = lam %% cylinder_flow (&0) y) /\
     (!y. ~(y = vec 0)
          ==> Y(p y) = mfd_differential (open_set_atlas {z:real^3 | ~(z = vec 0)}) atlas p y
                                        (inv(sqrt(&2 * lam)) % y))
     ==> !tk. ?psi h a kappa delta c0.
            mfd_param top1 atlas1 (annulus (exp(--a)) (exp a)) psi /\
            p2bkg_prim atlas1 gs X (IMAGE psi (annulus (exp(--a)) (exp a))) h /\
            &0 < kappa /\ &0 <= delta /\ tk + delta < kappa * a /\
            (!y. y IN annulus (exp(--a)) (exp a)
                 ==> abs((h(psi y) - c0) - kappa * log(norm y)) <= delta)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
     LABEL_TAC "qz" (CONJUNCT1(funpow 5 CONJUNCT2 th)) THEN
     LABEL_TAC "pf" (CONJUNCT1(funpow 8 CONJUNCT2 th))) THEN
  X_GEN_TAC `tk:real` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2c_slice_limit_with]) THEN
  MP_TAC P2BKS_SHELL_AT_INDEX THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sai"))) THEN
  MP_TAC(SPEC `inv(&6 * C * exp(&1))` P2BKS_ETA_CHOICE) THEN ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`lam:real`; `tk:real`] P2BKS_KAPPA_BIG) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "kb"))) THEN
  SUBGOAL_THEN `!S. open S /\ ~(vec 0 IN S) ==> mfd_param top atlas S (p:real^3->B)`
  (LABEL_TAC "par") THENL
   [GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC P2BKS_U4_PARAM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `S = annulus (exp(--(&1))) (exp(&1)):real^3->bool` THEN
  ABBREV_TAC `K0 = cball(vec 0:real^3,exp(&1)) DIFF ball(vec 0,exp(--(&1)))` THEN
  SUBGOAL_THEN `compact_in top (IMAGE (p:real^3->B) K0) /\ S SUBSET K0 /\
                mfd_param top atlas S p` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((B->bool)#(B->real^3))->bool`;
                            `annulus (exp(--(&2))) (exp(&2)):real^3->bool`] THEN
      REPEAT CONJ_TAC THENL
       [USE_THEN "par" MATCH_MP_TAC THEN
        REWRITE_TAC[P2BPC_ANNULUS_OPEN; annulus; IN_ELIM_THM; NORM_0] THEN
        MP_TAC(SPEC `--(&2)` REAL_EXP_POS_LT) THEN REAL_ARITH_TAC;
        EXPAND_TAC "K0" THEN SIMP_TAC[COMPACT_DIFF; COMPACT_CBALL; OPEN_BALL];
        EXPAND_TAC "K0" THEN
        REWRITE_TAC[SUBSET; IN_DIFF; IN_CBALL_0; IN_BALL_0; annulus; IN_ELIM_THM; REAL_NOT_LT] THEN
        GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `exp(--(&1))` THEN
          ASM_REWRITE_TAC[REAL_EXP_MONO_LT] THEN REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `exp(&1)` THEN
          ASM_REWRITE_TAC[REAL_EXP_MONO_LT] THEN REAL_ARITH_TAC]];
      EXPAND_TAC "S" THEN EXPAND_TAC "K0" THEN
      REWRITE_TAC[SUBSET; IN_DIFF; IN_CBALL_0; IN_BALL_0; annulus; IN_ELIM_THM] THEN
      REAL_ARITH_TAC;
      EXPAND_TAC "S" THEN USE_THEN "par" MATCH_MP_TAC THEN
      REWRITE_TAC[P2BPC_ANNULUS_OPEN; annulus; IN_ELIM_THM; NORM_0] THEN
      MP_TAC(SPEC `--(&1)` REAL_EXP_POS_LT) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `K = IMAGE (p:real^3->B) K0` THEN
  MP_TAC(ISPECL [`V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)`; `x:num->A`; `t:num->real`; `Q:num->real`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`;
                 `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `K:B->bool`; `0`; `eta:real`]
                P2BPL_SLICE_CLOSE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n1:num` (LABEL_TAC "sc")) THEN
  USE_THEN "pf" (MP_TAC o SPECL [`K:B->bool`; `eta:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n2:num` (LABEL_TAC "pfn")) THEN
  USE_THEN "qz" (MP_TAC o C MATCH_MP (ASSUME `&0 < q0`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `n3:num` (LABEL_TAC "qn")) THEN
  SUBGOAL_THEN `!n. n <= (sub:num->num) n` ASSUME_TAC THENL
   [MATCH_MP_TAC MONOTONE_BIGGER THEN ASM_MESON_TAC[p3_subseq]; ALL_TAC] THEN
  ABBREV_TAC `N = n1 + n2 + n3:num` THEN
  SUBGOAL_THEN `N <= (sub:num->num) N` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `k = (sub:num->num) N` THEN
  SUBGOAL_THEN `n1 <= (k:num) /\ n2 <= (N:num) /\ n3 <= (k:num)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `n1 + n2 + n3 = (N:num)` THEN UNDISCH_TAC `(N:num) <= k` THEN ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "sc" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sck")) THEN
  USE_THEN "pfn" (MP_TAC o SPEC `N:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "pfk") THEN
  USE_THEN "qn" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(SPEC `k:num` (ASSUME
   `!k. ?psi. mfd_diffeo top (atlas:((B->bool)#(B->real^3))->bool) ((W:num->B->bool) k)
                (rfs_vtop ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) k) (t k))
                (rfs_vatlas (V k) (t k)) (IMAGE ((phi:num->B->A) k) (W k)) (phi k) psi`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `phi':A->B` MP_TAC) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `IMAGE (p:real^3->B) S SUBSET (W:num->B->bool) k` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `K:B->bool` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "K" THEN ASM_SIMP_TAC[IMAGE_SUBSET];
    ALL_TAC] THEN
  USE_THEN "sai" (MP_TAC o SPECL
   [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g0:B->real^3^3`; `Y:B->real^3`;
    `top1:A topology`; `atlas1:((A->bool)#(A->real^3))->bool`;
    `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                          (real->A->real^3^3)) k) (t k)`;
    `X:A->real^3`; `(phi:num->B->A) k`; `phi':A->B`; `(W:num->B->bool) k`; `p:real^3->B`;
    `lam:real`; `(Q:num->real) k`; `eta:real`; `0`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(y:real^3 = vec 0) /\ (p:real^3->B) y IN K` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `(y:real^3) IN S` THEN EXPAND_TAC "S" THEN
        REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REWRITE_TAC[NORM_0] THEN
        MP_TAC(SPEC `--(&1)` REAL_EXP_POS_LT) THEN REAL_ARITH_TAC;
        EXPAND_TAC "K" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(p:real^3->B) y IN topspace top` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `S:real^3->bool`;
                     `p:real^3->B`; `S:real^3->bool`] MFD_PARAM_IMAGE_SUBSET) THEN
      ASM_REWRITE_TAC[SUBSET_REFL] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[];
      ALL_TAC;
      ASM_SIMP_TAC[];
      USE_THEN "pfk" (MP_TAC o C MATCH_MP (ASSUME `(p:real^3->B) y IN K`)) THEN
      MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[REAL_LT_IMP_LE];
      USE_THEN "sck" (MP_TAC o C MATCH_MP (ASSUME `(p:real^3->B) y IN K`)) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_LT_IMP_LE]] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(p:real^3->B) y`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `S:real^3->bool`;
                   `p:real^3->B`; `chart_at (atlas:((B->bool)#(B->real^3))->bool) ((p:real^3->B) y)`]
                  P2BKG_PARAM_CHART_SMOOTH) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [EXPAND_TAC "S" THEN REWRITE_TAC[P2BPC_ANNULUS_OPEN]; STRIP_TAC] THEN
    SUBGOAL_THEN `(\z. SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) ((p:real^3->B) y)) (p z))
                  differentiable at y` ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `{z:real^3 | z IN S /\
                     (p:real^3->B) z IN FST(chart_at (atlas:((B->bool)#(B->real^3))->bool) (p y))}` THEN
      ASM_REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`{z:real^3 | ~(z = vec 0)}`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `p:real^3->B`; `y:real^3`] P2BKS_MDIFF_OPEN_SET_LOCAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      SUBGOAL_THEN `{z:real^3 | ~(z = vec 0)} = (:real^3) DELETE vec 0` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DELETE; IN_UNIV]; ALL_TAC] THEN
      SIMP_TAC[OPEN_DELETE; OPEN_UNIV];
      ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:A->real` (X_CHOOSE_THEN `c0:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `mfd_param top1 atlas1 S ((phi:num->B->A) k o (p:real^3->B))` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BKS_PARAM_DIFFEO_COMPOSE THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                          `phi':A->B`; `(W:num->B->bool) k`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt(&3 * eta) + sqrt(eta * eta) + sqrt eta` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LE THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt((Q:num->real) k) /\ &0 < sqrt(&2 * lam)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`(phi:num->B->A) k o (p:real^3->B)`; `h:A->real`; `&1`; `sqrt(&2 * lam / (Q:num->real) k)`;
    `C * (&3 * (inv(sqrt((Q:num->real) k)) * (sqrt(&3 * eta) + sqrt(eta * eta) + sqrt eta) *
                sqrt(&2 * lam) * exp(&1)))`;
    `c0:real`] THEN
  ASM_REWRITE_TAC[REAL_MUL_RID] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2BKS_PRIM_INVARIANT THEN EXISTS_TAC `top1:A topology` THEN
    EXISTS_TAC `rfs_vmetric ((V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) k) (t k)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`atlas1:((A->bool)#(A->real^3))->bool`; `S:real^3->bool`] THEN
      ASM_REWRITE_TAC[SUBSET_REFL] THEN EXPAND_TAC "S" THEN REWRITE_TAC[P2BPC_ANNULUS_OPEN];
      X_GEN_TAC `xx:A` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(xx:A) IN topspace top1` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`top1:A topology`; `atlas1:((A->bool)#(A->real^3))->bool`;
                       `S:real^3->bool`; `(phi:num->B->A) k o (p:real^3->B)`; `S:real^3->bool`]
                      MFD_PARAM_IMAGE_SUBSET) THEN
        ASM_REWRITE_TAC[SUBSET_REFL] THEN ASM SET_TAC[];
        ASM_SIMP_TAC[]]];
    MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC REAL_LT_MUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[]];
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_INV_EQ; REAL_EXP_POS_LE] THEN REAL_ARITH_TAC;
    MP_TAC(ISPECL [`C:real`; `exp(&1)`; `sqrt(&3 * eta) + sqrt(eta * eta) + sqrt eta`;
                   `inv(sqrt((Q:num->real) k))`; `sqrt(&2 * lam)`] P2BKS_DELTA_HALF) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_EXP_POS_LT; REAL_LE_INV_EQ; REAL_LT_IMP_LE]; ALL_TAC] THEN
    USE_THEN "kb" (MP_TAC o SPEC `(Q:num->real) k`) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(SPECL [`lam:real`; `(Q:num->real) k`] P2BKS_KAPPA_SPLIT) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC]);;

