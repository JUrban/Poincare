(* ========================================================================= *)
(* Unit pc_pde_gauge: the DeTurck gauge.  A Ricci-DeTurck flow gb with       *)
(* background h becomes a Ricci flow g t = phi t pullback of gb t, where     *)
(* phi a = id and d/dt phi = -W(gb,h) o phi (CLN (2.52); MT's sketch has the *)
(* opposite sign).  The field is extended below a in the charts of a cover   *)
(* (partition of unity) so that the manifold flow PDE_REQ_MFLOW              *)
(* (pc_mfd_flow) starts at a.                                                *)
(* ========================================================================= *)

needs "src/pc_pde_mloc.ml";;
needs "src/pc_pde_st.ml";;
needs "src/pc_lrg_evol.ml";;
needs "src/pc_pde_rdt_symbol.ml";;
needs "src/pc_mfd_flow.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The time derivative of pullbacks along flows in coordinates (the Lie      *)
(* derivative of pullbacks along flows):                                     *)
(* d/dt (DF^T G(t,F) DF) = DF^T (d/dt G + L_X G)(F) DF when d/dt F = X(t,F).  *)
(* ========================================================================= *)

(* The vector derivative of a curve composed with a differentiable map.    *)

let PDG_VDERIV_CHAIN = prove
 (`!(f:real^1->real^M) (g:real^M->real^P) f' x.
        (f has_vector_derivative f') (at x) /\ g differentiable (at (f x))
        ==> ((g o f) has_vector_derivative frechet_derivative g (at (f x)) f') (at x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_vector_derivative] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
  UNDISCH_TAC `(g:real^M->real^P) differentiable (at (f(x:real^1)))` THEN
  REWRITE_TAC[FRECHET_DERIVATIVE_WORKS] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:real^1->real^M`; `g:real^M->real^P`; `\s:real^1. drop s % (f':real^M)`;
                 `frechet_derivative (g:real^M->real^P) (at (f(x:real^1)))`;
                 `x:real^1`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN
  ASM_SIMP_TAC[LINEAR_CMUL]);;

(* The algebra of the Lie derivative term.                                   *)

let PDG_LLIE_DOT_ALG = prove
 (`!(U:real^N) V (DX:real^N->real^N) (M0:real^N^N) P Q.
        linear DX
        ==> lift(U dot (M0 ** DX V + (P + Q) ** V)) + lift(DX U dot (M0 ** V)) =
            lift(U dot ((P + (Q + transp(matrix DX) ** M0 + M0 ** matrix DX)) ** V))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM LIFT_ADD; LIFT_EQ] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB; DOT_RADD; GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[MATRIX_WORKS] THEN
  SUBGOAL_THEN `(U:real^N) dot (transp(matrix(DX:real^N->real^N)) ** (M0:real^N^N) ** (V:real^N)) =
                DX U dot (M0 ** V)` SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[DOT_SYM] THEN REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL] THEN
    ASM_SIMP_TAC[MATRIX_WORKS] THEN REWRITE_TAC[DOT_SYM];
    REAL_ARITH_TAC]);;

(* The core identity, in dot form.                                           *)

let PDG_PULLBACK_FLOW_DOT = prove
 (`!(SS:real^(1,N)finite_sum->bool) (TT:real^(1,N)finite_sum->bool)
    (Fm:real^(1,N)finite_sum->real^N) (X:real^(1,N)finite_sum->real^N)
    (G:real^(1,N)finite_sum->real^N^N) t y a b.
     open SS /\ open TT /\ smooth_map_on SS Fm /\ smooth_map_on TT X /\
     smooth_map_on TT ((vectorize:real^N^N->real^(N,N)finite_prod) o G) /\
     (!s z. pastecart s z IN SS ==> pastecart s (Fm(pastecart s z)) IN TT) /\
     (!s z. pastecart s z IN SS
            ==> frechet_derivative Fm (at (pastecart s z)) (pastecart (lift(&1)) (vec 0)) =
                X(pastecart s (Fm(pastecart s z)))) /\
     pastecart (lift t) y IN SS
     ==> ((\s. lift(frechet_derivative (\z. Fm(pastecart s z)) (at y) a dot
                    (G(pastecart s (Fm(pastecart s y))) **
                     frechet_derivative (\z. Fm(pastecart s z)) (at y) b)))
          has_vector_derivative
          lift(frechet_derivative (\z. Fm(pastecart (lift t) z)) (at y) a dot
               (((matrify:real^(N,N)finite_prod->real^N^N)
                   (frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o G)
                      (at (pastecart (lift t) (Fm(pastecart (lift t) y))))
                      (pastecart (lift(&1)) (vec 0))) +
                 llie (\z. X(pastecart (lift t) z)) (\z. G(pastecart (lift t) z))
                      (Fm(pastecart (lift t) y))) **
                frechet_derivative (\z. Fm(pastecart (lift t) z)) (at y) b)))
         (at (lift t))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "inT")
    (CONJUNCTS_THEN2 (LABEL_TAC "ode") ASSUME_TAC))))))) THEN
  ABBREV_TAC `y1 = (Fm:real^(1,N)finite_sum->real^N) (pastecart (lift t) y)` THEN
  SUBGOAL_THEN `pastecart (lift t) (y1:real^N) IN TT` ASSUME_TAC THENL
   [EXPAND_TAC "y1" THEN USE_THEN "inT" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!w. w IN SS ==> (Fm:real^(1,N)finite_sum->real^N) differentiable (at w)) /\
    (!w. w IN TT ==> (X:real^(1,N)finite_sum->real^N) differentiable (at w)) /\
    (!w. w IN TT ==> ((vectorize:real^N^N->real^(N,N)finite_prod) o
                      (G:real^(1,N)finite_sum->real^N^N)) differentiable (at w))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  (* the slices *)
  SUBGOAL_THEN
   `((\z. (Fm:real^(1,N)finite_sum->real^N) (pastecart (lift t) z)) has_derivative
     frechet_derivative (\z. Fm(pastecart (lift t) z)) (at y)) (at y) /\
    ((\z. (X:real^(1,N)finite_sum->real^N) (pastecart (lift t) z)) has_derivative
     frechet_derivative (\z. X(pastecart (lift t) z)) (at y1)) (at y1)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS; differentiable] THEN CONJ_TAC THENL
     [EXISTS_TAC `\w. frechet_derivative (Fm:real^(1,N)finite_sum->real^N)
                        (at (pastecart (lift t) y)) (pastecart (vec 0) w)` THEN
      MATCH_MP_TAC LRG_HAS_DERIVATIVE_SPACE_SLICE THEN ASM_SIMP_TAC[];
      EXISTS_TAC `\w. frechet_derivative (X:real^(1,N)finite_sum->real^N)
                        (at (pastecart (lift t) y1)) (pastecart (vec 0) w)` THEN
      MATCH_MP_TAC LRG_HAS_DERIVATIVE_SPACE_SLICE THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  (* the time derivative of the spatial derivative of the flow *)
  SUBGOAL_THEN
   `!c. ((\s. frechet_derivative (\z. (Fm:real^(1,N)finite_sum->real^N) (pastecart s z))
                (at y) c) has_vector_derivative
         frechet_derivative (\z. (X:real^(1,N)finite_sum->real^N) (pastecart (lift t) z))
           (at y1) (frechet_derivative (\z. Fm(pastecart (lift t) z)) (at y) c))
        (at (lift t))`
  (LABEL_TAC "du") THENL
   [X_GEN_TAC `c:real^N` THEN
    MP_TAC(ISPECL [`SS:real^(1,N)finite_sum->bool`; `Fm:real^(1,N)finite_sum->real^N`;
                   `t:real`; `y:real^N`; `c:real^N`] LRG_TIME_SPACE_SWAP) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`\z. (Fm:real^(1,N)finite_sum->real^N) (pastecart (lift t) z)`;
                   `\z. (X:real^(1,N)finite_sum->real^N) (pastecart (lift t) z)`;
                   `frechet_derivative (\z. (Fm:real^(1,N)finite_sum->real^N)
                                              (pastecart (lift t) z)) (at y)`;
                   `frechet_derivative (\z. (X:real^(1,N)finite_sum->real^N)
                                              (pastecart (lift t) z)) (at y1)`;
                   `y:real^N`] DIFF_CHAIN_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `open {z:real^N | pastecart (lift t) z IN SS}` ASSUME_TAC THENL
     [MATCH_MP_TAC PDE_ST_SLICE_OPEN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `y:real^N` o REWRITE_RULE[OPEN_CONTAINS_BALL]) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL
     [`(\z. (X:real^(1,N)finite_sum->real^N) (pastecart (lift t) z)) o
       (\z. (Fm:real^(1,N)finite_sum->real^N) (pastecart (lift t) z))`;
      `frechet_derivative (\z. (X:real^(1,N)finite_sum->real^N) (pastecart (lift t) z)) (at y1) o
       frechet_derivative (\z. (Fm:real^(1,N)finite_sum->real^N) (pastecart (lift t) z)) (at y)`;
      `\x. frechet_derivative (Fm:real^(1,N)finite_sum->real^N) (at (pastecart (lift t) x))
             (pastecart (lift(&1)) (vec 0))`;
      `y:real^N`; `r:real`] HAS_DERIVATIVE_TRANSFORM_AT) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
      CONV_TAC SYM_CONV THEN USE_THEN "ode" MATCH_MP_TAC THEN
      UNDISCH_TAC `ball(y:real^N,r) SUBSET {z | pastecart (lift t) z IN SS}` THEN
      REWRITE_TAC[SUBSET; IN_BALL; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
      ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
      REWRITE_TAC[o_THM]];
    ALL_TAC] THEN
  (* the time derivative of the metric along the flow line *)
  SUBGOAL_THEN
   `((\s. (vectorize:real^N^N->real^(N,N)finite_prod)
            ((G:real^(1,N)finite_sum->real^N^N)
               (pastecart s ((Fm:real^(1,N)finite_sum->real^N) (pastecart s y)))))
     has_vector_derivative
     frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o G)
        (at (pastecart (lift t) y1)) (pastecart (lift(&1)) (vec 0)) +
     vectorize(mderiv (\z. G(pastecart (lift t) z)) y1
                 ((X:real^(1,N)finite_sum->real^N) (pastecart (lift t) y1))))
    (at (lift t))`
  (LABEL_TAC "dM") THENL
   [SUBGOAL_THEN
     `((\s. pastecart s ((Fm:real^(1,N)finite_sum->real^N) (pastecart s y)))
       has_vector_derivative
       pastecart (lift(&1)) ((X:real^(1,N)finite_sum->real^N) (pastecart (lift t) y1)))
      (at (lift t))`
    ASSUME_TAC THENL
     [REWRITE_TAC[has_vector_derivative] THEN
      SUBGOAL_THEN
       `(\x:real^1. drop x % pastecart (lift(&1))
                      ((X:real^(1,N)finite_sum->real^N) (pastecart (lift t) y1))) =
        (\x. pastecart (drop x % lift(&1)) (drop x % X(pastecart (lift t) y1)))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; PASTECART_CMUL]; ALL_TAC] THEN
      MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM has_vector_derivative; LIFT_NUM; HAS_VECTOR_DERIVATIVE_ID];
        REWRITE_TAC[GSYM has_vector_derivative] THEN
        MP_TAC(ISPECL [`Fm:real^(1,N)finite_sum->real^N`; `t:real`; `y:real^N`]
                      LRG_TIME_CURVE_VDERIV) THEN
        ASM_SIMP_TAC[] THEN
        USE_THEN "ode" (fun th -> REWRITE_TAC[MP (SPECL [`lift t`; `y:real^N`] th)
          (ASSUME `pastecart (lift t) (y:real^N) IN SS`)]) THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\s. pastecart s ((Fm:real^(1,N)finite_sum->real^N) (pastecart s y))`;
                   `(vectorize:real^N^N->real^(N,N)finite_prod) o
                    (G:real^(1,N)finite_sum->real^N^N)`;
                   `pastecart (lift(&1))
                      ((X:real^(1,N)finite_sum->real^N) (pastecart (lift t) y1))`;
                   `lift t`] PDG_VDERIV_CHAIN) THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[o_DEF] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN
     `pastecart (lift(&1)) ((X:real^(1,N)finite_sum->real^N) (pastecart (lift t) y1)) =
      pastecart (lift(&1)) (vec 0) + pastecart (vec 0) (X(pastecart (lift t) y1))`
    SUBST1_TAC THENL
     [REWRITE_TAC[PASTECART_ADD; VECTOR_ADD_LID; VECTOR_ADD_RID]; ALL_TAC] THEN
    SUBGOAL_THEN
     `linear(frechet_derivative (\x. (vectorize:real^N^N->real^(N,N)finite_prod)
                                       ((G:real^(1,N)finite_sum->real^N^N) x))
               (at (pastecart (lift t) y1)))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      SUBGOAL_THEN `(\x. (vectorize:real^N^N->real^(N,N)finite_prod)
                           ((G:real^(1,N)finite_sum->real^N^N) x)) = vectorize o G`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[LINEAR_ADD] THEN AP_TERM_TAC THEN
    REWRITE_TAC[mderiv; VECTORIZE_MATRIFY] THEN
    MP_TAC(ISPECL [`(vectorize:real^N^N->real^(N,N)finite_prod) o
                    (G:real^(1,N)finite_sum->real^N^N)`;
                   `lift t`; `y1:real^N`;
                   `(X:real^(1,N)finite_sum->real^N) (pastecart (lift t) y1)`]
                  LRG_SLICE_DERIV) THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[o_DEF] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REFL_TAC;
    ALL_TAC] THEN
  (* the product rules *)
  MP_TAC(ISPECL [`\(m:real^(N,N)finite_prod) (w:real^N). (matrify:real^(N,N)finite_prod->real^N^N) m ** w`;
                 `\s. (vectorize:real^N^N->real^(N,N)finite_prod)
                        ((G:real^(1,N)finite_sum->real^N^N)
                           (pastecart s ((Fm:real^(1,N)finite_sum->real^N) (pastecart s y))))`;
                 `\s. frechet_derivative (\z. (Fm:real^(1,N)finite_sum->real^N) (pastecart s z)) (at y) b`;
                 `frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o (G:real^(1,N)finite_sum->real^N^N)) (at (pastecart (lift t) y1)) (pastecart (lift(&1)) (vec 0)) + vectorize(mderiv (\z. (G:real^(1,N)finite_sum->real^N^N) (pastecart (lift t) z)) y1 ((X:real^(1,N)finite_sum->real^N) (pastecart (lift t) y1)))`;
                 `frechet_derivative (\z. (X:real^(1,N)finite_sum->real^N) (pastecart (lift t) z)) (at y1) (frechet_derivative (\z. (Fm:real^(1,N)finite_sum->real^N) (pastecart (lift t) z)) (at y) b)`;
                 `lift t`] HAS_VECTOR_DERIVATIVE_BILINEAR_AT) THEN
  REWRITE_TAC[BILINEAR_MATRIX_VECTOR_MUL] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [USE_THEN "dM" ACCEPT_TAC; USE_THEN "du" (ACCEPT_TAC o SPEC `b:real^N`)];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[MATRIFY_VECTORIZE; MATRIFY_ADD]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\(x:real^N) (w:real^N). lift(x dot w)`;
                 `\s. frechet_derivative (\z. (Fm:real^(1,N)finite_sum->real^N) (pastecart s z)) (at y) a`;
                 `\s. (G:real^(1,N)finite_sum->real^N^N)
                        (pastecart s ((Fm:real^(1,N)finite_sum->real^N) (pastecart s y))) **
                      frechet_derivative (\z. Fm (pastecart s z)) (at y) b`;
                 `frechet_derivative (\z. (X:real^(1,N)finite_sum->real^N) (pastecart (lift t) z)) (at y1) (frechet_derivative (\z. (Fm:real^(1,N)finite_sum->real^N) (pastecart (lift t) z)) (at y) a)`;
                 `(G:real^(1,N)finite_sum->real^N^N) (pastecart (lift t) y1) ** frechet_derivative (\z. (X:real^(1,N)finite_sum->real^N) (pastecart (lift t) z)) (at y1) (frechet_derivative (\z. (Fm:real^(1,N)finite_sum->real^N) (pastecart (lift t) z)) (at y) b) +
                  ((matrify:real^(N,N)finite_prod->real^N^N) (frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o (G:real^(1,N)finite_sum->real^N^N)) (at (pastecart (lift t) y1)) (pastecart (lift(&1)) (vec 0))) + mderiv (\z. (G:real^(1,N)finite_sum->real^N^N) (pastecart (lift t) z)) y1 ((X:real^(1,N)finite_sum->real^N) (pastecart (lift t) y1))) ** frechet_derivative (\z. (Fm:real^(1,N)finite_sum->real^N) (pastecart (lift t) z)) (at y) b`;
                 `lift t`] HAS_VECTOR_DERIVATIVE_BILINEAR_AT) THEN
  REWRITE_TAC[BILINEAR_DOT] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [USE_THEN "du" (ACCEPT_TAC o SPEC `a:real^N`); ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[llie] THEN MATCH_MP_TAC PDG_LLIE_DOT_ALG THEN
  MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN REWRITE_TAC[differentiable] THEN
  ASM_MESON_TAC[]);;

(* Matrix entries as dot products with basis vectors.                       *)

let PDG_ENTRY_DOT = prove
 (`!(B:real^N^N) i j.
        1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
        ==> B$i$j = basis i dot (B ** basis j)`,
  SIMP_TAC[DOT_BASIS; MATRIX_VECTOR_MUL_BASIS; column; LAMBDA_BETA]);;

(* The time derivative of the entries of the pullbacks along a flow.        *)

let PDG_MPULLBACK_FLOW_DERIV = prove
 (`!(SS:real^(1,N)finite_sum->bool) (TT:real^(1,N)finite_sum->bool)
    (Fm:real^(1,N)finite_sum->real^N) (X:real^(1,N)finite_sum->real^N)
    (G:real^(1,N)finite_sum->real^N^N) t y i j.
     open SS /\ open TT /\ smooth_map_on SS Fm /\ smooth_map_on TT X /\
     smooth_map_on TT ((vectorize:real^N^N->real^(N,N)finite_prod) o G) /\
     (!s z. pastecart s z IN SS ==> pastecart s (Fm(pastecart s z)) IN TT) /\
     (!s z. pastecart s z IN SS
            ==> frechet_derivative Fm (at (pastecart s z)) (pastecart (lift(&1)) (vec 0)) =
                X(pastecart s (Fm(pastecart s z)))) /\
     pastecart (lift t) y IN SS /\
     1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
     ==> ((\s. mpullback (\z. Fm(pastecart (lift s) z)) (\z. G(pastecart (lift s) z)) y$i$j)
          has_real_derivative
          (mpullback (\z. Fm(pastecart (lift t) z))
             (\z. (matrify:real^(N,N)finite_prod->real^N^N)
                    (frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o G)
                       (at (pastecart (lift t) z)) (pastecart (lift(&1)) (vec 0))) +
                  llie (\z. X(pastecart (lift t) z)) (\z. G(pastecart (lift t) z)) z) y)$i$j)
         (atreal t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!s. pastecart (lift s) y IN SS
        ==> linear(frechet_derivative (\z. (Fm:real^(1,N)finite_sum->real^N)
                                             (pastecart (lift s) z)) (at y))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    REWRITE_TAC[differentiable] THEN
    EXISTS_TAC `\w. frechet_derivative (Fm:real^(1,N)finite_sum->real^N)
                      (at (pastecart (lift s) y)) (pastecart (vec 0) w)` THEN
    MATCH_MP_TAC LRG_HAS_DERIVATIVE_SPACE_SLICE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `SS:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `pastecart (lift t) (y:real^N)` o
    REWRITE_RULE[OPEN_CONTAINS_BALL] o check (fun th -> concl th = `open (SS:real^(1,N)finite_sum->bool)`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!s. abs(s - t) < r ==> pastecart (lift s) (y:real^N) IN SS` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `ball(pastecart (lift t) (y:real^N),r) SUBSET SS` THEN
    REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[DIST_PASTECART_CANCEL; DIST_LIFT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC
   `\s. frechet_derivative (\z. (Fm:real^(1,N)finite_sum->real^N) (pastecart (lift s) z))
          (at y) (basis i) dot
        ((G:real^(1,N)finite_sum->real^N^N) (pastecart (lift s) (Fm(pastecart (lift s) y))) **
         frechet_derivative (\z. Fm(pastecart (lift s) z)) (at y) (basis j))` THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN REWRITE_TAC[mpullback] THEN
    ASM_SIMP_TAC[PDG_ENTRY_DOT; RFB_CONGRUENCE_DOT];
    ALL_TAC] THEN
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF; LIFT_DROP] THEN
  REWRITE_TAC[mpullback] THEN
  SUBGOAL_THEN `abs(t - t) < r` (fun th -> ASM_SIMP_TAC[th; PDG_ENTRY_DOT; RFB_CONGRUENCE_DOT]) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`SS:real^(1,N)finite_sum->bool`; `TT:real^(1,N)finite_sum->bool`;
                 `Fm:real^(1,N)finite_sum->real^N`; `X:real^(1,N)finite_sum->real^N`;
                 `G:real^(1,N)finite_sum->real^N^N`; `t:real`; `y:real^N`;
                 `basis i:real^N`; `basis j:real^N`] PDG_PULLBACK_FLOW_DOT) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[o_DEF]);;

(* ========================================================================= *)
(* Locality of the local DeTurck field and operator, their transformation    *)
(* under chart changes, and the chart forms of pde_deturck and pde_rdt_rhs.  *)
(* ========================================================================= *)

let PDG_LDETURCK_LOCAL = prove
 (`!s (H1:real^N->real^N^N) H2 G1 G2 y.
        open s /\ y IN s /\ (!z. z IN s ==> H1 z = H2 z /\ G1 z = G2 z)
        ==> pde_ldeturck H1 G1 y = pde_ldeturck H2 G2 y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_ldeturck] THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `(G1:real^N->real^N^N) y = G2 y` SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  AP_TERM_TAC THEN BINOP_TAC THEN MATCH_MP_TAC CHRISTOFFEL_LOCAL THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[]);;

let PDG_LRDT_LOCAL = prove
 (`!s (H1:real^N->real^N^N) H2 G1 G2 y.
        open s /\ y IN s /\ (!z. z IN s ==> H1 z = H2 z /\ G1 z = G2 z)
        ==> pde_lrdt H1 G1 y = pde_lrdt H2 G2 y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_lrdt; pde_lricci_matrix] THEN BINOP_TAC THENL
   [AP_TERM_TAC THEN SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC LRICCI_LOCAL THEN EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC LLIE_LOCAL THEN EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC PDG_LDETURCK_LOCAL THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[]]);;

(* The DeTurck field transforms as a vector under chart changes.             *)

let PDG_LDETURCK_CHART_TRANS = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) V psi (g:A->real^N^N) h x.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        riemannian_metric atlas h /\
        (U,phi) IN atlas /\ (V,psi) IN atlas /\ x IN U INTER V
        ==> chart_jac (U,phi) (V,psi) x
              (pde_ldeturck (metric_local atlas (U,phi) h) (metric_local atlas (U,phi) g)
                            (phi x)) =
            pde_ldeturck (metric_local atlas (V,psi) h) (metric_local atlas (V,psi) g)
                         (psi x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `pde_ldeturck (metric_local atlas (U:A->bool,phi:A->real^N) (h:A->real^N^N))
                 (metric_local atlas (U,phi) (g:A->real^N^N)) (phi x) =
    pde_ldeturck (mpullback (chart_trans (U,phi) (V,psi)) (metric_local atlas (V,psi) h))
                 (mpullback (chart_trans (U,phi) (V,psi)) (metric_local atlas (V,psi) g))
                 (phi x)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC PDG_LDETURCK_LOCAL THEN
    EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER V)` THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CHART_OVERLAP_IMAGE_OPEN]; ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC METRIC_LOCAL_TRANS THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`;
                `x:A`] CHART_TRANS_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `chart_jac (U:A->bool,phi:A->real^N) (V,psi) x =
    frechet_derivative (chart_trans (U,phi) (V,psi)) (at (phi x))`
  SUBST1_TAC THENL [REWRITE_TAC[chart_jac; SND]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC PDE_LDETURCK_PULLBACK THEN
  MAP_EVERY EXISTS_TAC
   [`IMAGE (psi:A->real^N) (U INTER V)`; `IMAGE (phi:A->real^N) (U INTER V)`;
    `chart_trans (V:A->bool,psi:A->real^N) (U,phi)`] THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CHART_TRANS_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[INTER_COMM] THEN MATCH_MP_TAC RIEMANNIAN_METRIC_OVERLAP THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `phi:A->real^N`] THEN ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[INTER_COMM] THEN MATCH_MP_TAC RIEMANNIAN_METRIC_OVERLAP THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `phi:A->real^N`] THEN ASM_REWRITE_TAC[]]);;

(* The local Ricci-DeTurck operator transforms as a metric.                 *)

let PDG_LRDT_CHART_TRANS = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) V psi (g:A->real^N^N) h x.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        riemannian_metric atlas h /\
        (U,phi) IN atlas /\ (V,psi) IN atlas /\ x IN U INTER V
        ==> pde_lrdt (metric_local atlas (U,phi) h) (metric_local atlas (U,phi) g) (phi x) =
            transp(matrix(chart_jac (U,phi) (V,psi) x)) **
            pde_lrdt (metric_local atlas (V,psi) h) (metric_local atlas (V,psi) g) (psi x) **
            matrix(chart_jac (U,phi) (V,psi) x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `pde_lrdt (metric_local atlas (U:A->bool,phi:A->real^N) (h:A->real^N^N))
             (metric_local atlas (U,phi) (g:A->real^N^N)) (phi x) =
    pde_lrdt (mpullback (chart_trans (U,phi) (V,psi)) (metric_local atlas (V,psi) h))
             (mpullback (chart_trans (U,phi) (V,psi)) (metric_local atlas (V,psi) g))
             (phi x)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC PDG_LRDT_LOCAL THEN
    EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER V)` THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CHART_OVERLAP_IMAGE_OPEN]; ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC METRIC_LOCAL_TRANS THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`;
                `x:A`] CHART_TRANS_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `chart_jac (U:A->bool,phi:A->real^N) (V,psi) x =
    frechet_derivative (chart_trans (U,phi) (V,psi)) (at (phi x))`
  SUBST1_TAC THENL [REWRITE_TAC[chart_jac; SND]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC PDE_LRDT_PULLBACK THEN
  MAP_EVERY EXISTS_TAC
   [`IMAGE (psi:A->real^N) (U INTER V)`; `IMAGE (phi:A->real^N) (U INTER V)`;
    `chart_trans (V:A->bool,psi:A->real^N) (U,phi)`] THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CHART_TRANS_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[INTER_COMM] THEN MATCH_MP_TAC RIEMANNIAN_METRIC_OVERLAP THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `phi:A->real^N`] THEN ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[INTER_COMM] THEN MATCH_MP_TAC RIEMANNIAN_METRIC_OVERLAP THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `phi:A->real^N`] THEN ASM_REWRITE_TAC[]]);;

(* The DeTurck field at a point is the local field in the preferred chart. *)

let PDG_DETURCK_AT = prove
 (`!top atlas (g:A->real^N^N) h x.
        smooth_manifold_atlas top atlas /\ x IN topspace top
        ==> pde_deturck atlas g h x =
            pde_ldeturck (metric_local atlas (chart_at atlas x) h)
                         (metric_local atlas (chart_at atlas x) g)
                         (SND(chart_at atlas x) x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_deturck; pde_ldeturck] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

(* Chart representatives of the DeTurck field.                               *)

let PDG_DETURCK_VREP = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N) h y.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        riemannian_metric atlas h /\ c IN atlas /\ y IN IMAGE (SND c) (FST c)
        ==> mfd_vrep atlas (pde_deturck atlas g h) c y =
            pde_ldeturck (metric_local atlas c h) (metric_local atlas c g) y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_vrep] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `x = chart_inv (c:(A->bool)#(A->real^N)) y` THEN
  SUBGOAL_THEN `(x:A) IN FST(c:(A->bool)#(A->real^N)) /\ SND c x = y` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `x:A`] PDM_CHART_AT_C) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `h:A->real^N^N`; `x:A`] PDG_DETURCK_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `g:A->real^N^N`; `h:A->real^N^N`; `x:A`] PDG_LDETURCK_CHART_TRANS) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER]);;

(* The right-hand side of the Ricci-DeTurck flow in any chart.               *)

let PDG_RDT_RHS_CHART = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N) h x.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        riemannian_metric atlas h /\ c IN atlas /\ x IN FST c
        ==> transp(matrix(chart_jac c (chart_at atlas x) x)) ** pde_rdt_rhs atlas h g x **
            matrix(chart_jac c (chart_at atlas x) x) =
            pde_lrdt (metric_local atlas c h) (metric_local atlas c g) (SND c x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_rdt_rhs] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `x:A`] PDM_CHART_AT_C) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                 `g:A->real^N^N`; `h:A->real^N^N`; `x:A`] PDG_LRDT_CHART_TRANS) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC);;

(* The Ricci-DeTurck equation in any chart.                                   *)

let PDG_RDT_CHART_DERIV = prove
 (`!top atlas (h:A->real^N^N) a b gb (c:(A->bool)#(A->real^N)) t z i j.
        pde_rdt_flow_from (top,atlas) h a b gb /\ riemannian_metric atlas h /\
        c IN atlas /\ a < t /\ t < b /\ z IN IMAGE (SND c) (FST c) /\
        1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
        ==> ((\s. metric_local atlas c (gb s) z$i$j) has_real_derivative
             pde_lrdt (metric_local atlas c h) (metric_local atlas c (gb t)) z$i$j)
            (atreal t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_rdt_flow_from] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `x = chart_inv (c:(A->bool)#(A->real^N)) z` THEN
  SUBGOAL_THEN `(x:A) IN FST(c:(A->bool)#(A->real^N)) /\ SND c x = z` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `x:A`] PDM_CHART_AT_C) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `J = matrix(chart_jac (c:(A->bool)#(A->real^N)) (chart_at atlas (x:A)) x)` THEN
  SUBGOAL_THEN
   `!s. metric_local atlas (c:(A->bool)#(A->real^N)) ((gb:real->A->real^N^N) s) z =
        transp J ** gb s x ** J`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[metric_local] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pde_lrdt (metric_local atlas c h) (metric_local atlas (c:(A->bool)#(A->real^N))
                                        ((gb:real->A->real^N^N) t)) z =
    transp J ** pde_rdt_rhs atlas h (gb t) x ** J`
  SUBST1_TAC THENL
   [EXPAND_TAC "J" THEN CONV_TAC SYM_CONV THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `SND (c:(A->bool)#(A->real^N)) x = z`)) THEN
    MATCH_MP_TAC PDG_RDT_RHS_CHART THEN EXISTS_TAC `top:A topology` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LRG_CONGRUENCE_ENTRY_MATRIX] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `p:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `q:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Smoothness up to time a is local in space-time: if near every point of    *)
(* [a,b) x U the family agrees (for t >= a) with a map smooth on an open     *)
(* set, it is pde_upto (PDE_SEELEY).                                         *)
(* ========================================================================= *)

let PDG_UPTO_LOCAL_ST = prove
 (`!a b (U:real^N->bool) (u:real->real^N->real^K).
        open U /\ a < b /\
        (!t y. a <= t /\ t < b /\ y IN U
               ==> ?O (Fl:real^(1,N)finite_sum->real^K).
                     open O /\ pastecart (lift t) y IN O /\ smooth_map_on O Fl /\
                     !s z. a <= s /\ s < b /\ z IN U /\ pastecart (lift s) z IN O
                           ==> Fl(pastecart (lift s) z) = u s z)
        ==> pde_upto a b U u`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "loc"))) THEN
  MP_TAC(SPECL [`a:real`; `b:real`] PDM_APPROACH_SEQ) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "dn") (LABEL_TAC "dlim")) THEN
  MATCH_MP_TAC PDE_SEELEY THEN ASM_REWRITE_TAC[pde_upto_classical] THEN
  REPEAT CONJ_TAC THENL
   [(* continuity *)
    MATCH_MP_TAC PDM_CONTINUOUS_ON_LOCAL THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN
    STRIP_TAC THEN USE_THEN "loc" (MP_TAC o SPECL [`t:real`; `y:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `O:real^(1,N)finite_sum->bool`
      (X_CHOOSE_THEN `Fl:real^(1,N)finite_sum->real^K` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `O:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_EQ THEN EXISTS_TAC `Fl:real^(1,N)finite_sum->real^K` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `w:real^(1,N)finite_sum` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real` (X_CHOOSE_THEN `z:real^N`
        STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `O:real^(1,N)finite_sum->bool` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN SET_TAC[]];
    (* smoothness on the open slab *)
    MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; FORALL_IN_PCROSS] THEN
    REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
    USE_THEN "loc" (MP_TAC o SPECL [`t:real`; `y:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `O:real^(1,N)finite_sum->bool`
      (X_CHOOSE_THEN `Fl:real^(1,N)finite_sum->real^K` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `(O:real^(1,N)finite_sum->bool) INTER
                (interval(lift a,lift b) PCROSS (U:real^N->bool))` THEN
    ASM_SIMP_TAC[OPEN_INTER; OPEN_PCROSS; OPEN_INTERVAL; IN_INTER; PASTECART_IN_PCROSS;
                 IN_INTERVAL_1; LIFT_DROP] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `Fl:real^(1,N)finite_sum->real^K` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_INTER; FORALL_PASTECART; PASTECART_IN_PCROSS; FORALL_LIFT;
                  IN_INTERVAL_1; LIFT_DROP; FSTCART_PASTECART; SNDCART_PASTECART] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `O:real^(1,N)finite_sum->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  (* the jets have continuous extensions *)
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
  EXISTS_TAC
   `\w:real^(1,N)finite_sum.
      if a < drop(fstcart w)
      then iterated_partial l (\z. (u:real->real^N->real^K) (drop(fstcart z)) (sndcart z)) w
      else lim sequentially
             (\n. iterated_partial l (\z. u (drop(fstcart z)) (sndcart z))
                    (pastecart (lift(a + (b - a) * inv(&n + &2))) (sndcart w)))` THEN
  REWRITE_TAC[FSTCART_PASTECART; LIFT_DROP] THEN
  CONJ_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  MATCH_MP_TAC PDM_CONTINUOUS_ON_LOCAL THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN
  STRIP_TAC THEN USE_THEN "loc" (MP_TAC o SPECL [`t:real`; `y:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `O:real^(1,N)finite_sum->bool`
    (X_CHOOSE_THEN `Fl:real^(1,N)finite_sum->real^K` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `O:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `iterated_partial l (Fl:real^(1,N)finite_sum->real^K)` THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `O:real^(1,N)finite_sum->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SMOOTH_MAP_ON_ITERATED_PARTIAL] THEN SET_TAC[]] THEN
  (* agreement of the jets with those of the local smooth map *)
  SUBGOAL_THEN
   `!s z. a < s /\ s < b /\ z IN U /\ pastecart (lift s) z IN O
          ==> iterated_partial l (\z. (u:real->real^N->real^K) (drop(fstcart z)) (sndcart z))
                (pastecart (lift s) z) =
              iterated_partial l (Fl:real^(1,N)finite_sum->real^K) (pastecart (lift s) z)`
  (LABEL_TAC "jagree") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN
    EXISTS_TAC `(O:real^(1,N)finite_sum->bool) INTER
                (interval(lift a,lift b) PCROSS (U:real^N->bool))` THEN
    ASM_SIMP_TAC[OPEN_INTER; OPEN_PCROSS; OPEN_INTERVAL; IN_INTER; PASTECART_IN_PCROSS;
                 IN_INTERVAL_1; LIFT_DROP] THEN
    REWRITE_TAC[IN_INTER; FORALL_PASTECART; PASTECART_IN_PCROSS; FORALL_LIFT;
                IN_INTERVAL_1; LIFT_DROP; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `w:real^(1,N)finite_sum` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real` (X_CHOOSE_THEN `z:real^N`
    STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  COND_CASES_TAC THENL
   [CONV_TAC SYM_CONV THEN USE_THEN "jagree" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `s:real = a` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC TENDSTO_LIM THEN REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  SUBGOAL_THEN
   `((\n. pastecart (lift(a + (b - a) * inv(&n + &2))) (z:real^N)) -->
     pastecart (lift a) z) sequentially`
  ASSUME_TAC THENL [MATCH_MP_TAC LIM_PASTECART THEN ASM_REWRITE_TAC[LIM_CONST]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?N. !n. N <= n
            ==> pastecart (lift(a + (b - a) * inv(&n + &2))) (z:real^N) IN
                (O:real^(1,N)finite_sum->bool)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `pastecart (lift a) (z:real^N)` o
      REWRITE_RULE[OPEN_CONTAINS_BALL] o
      check (fun th -> concl th = `open (O:real^(1,N)finite_sum->bool)`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC
     `((\n. pastecart (lift(a + (b - a) * inv(&n + &2))) (z:real^N)) -->
       pastecart (lift a) z) sequentially` THEN
    REWRITE_TAC[LIM_SEQUENTIALLY] THEN DISCH_THEN(MP_TAC o SPEC `r:real`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
    DISCH_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    UNDISCH_TAC `ball(pastecart (lift a) (z:real^N),r) SUBSET O` THEN
    REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\n. iterated_partial l (Fl:real^(1,N)finite_sum->real^K)
                    (pastecart (lift(a + (b - a) * inv(&n + &2))) z)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `N:num` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    USE_THEN "jagree" MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
    USE_THEN "dn" (MP_TAC o SPEC `n:num`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(iterated_partial l (Fl:real^(1,N)finite_sum->real^K)) continuous
      (at (pastecart (lift a) (z:real^N)))`
  MP_TAC THENL
   [MP_TAC(ISPECL [`iterated_partial l (Fl:real^(1,N)finite_sum->real^K)`;
                   `O:real^(1,N)finite_sum->bool`] CONTINUOUS_ON_EQ_CONTINUOUS_AT) THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SMOOTH_MAP_ON_ITERATED_PARTIAL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUS_AT_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `\n. pastecart (lift(a + (b - a) * inv(&n + &2))) (z:real^N)`) THEN
  ASM_REWRITE_TAC[o_DEF]);;

(* ========================================================================= *)
(* The local DeTurck field of a space-time family of invertible matrices is  *)
(* jointly smooth; smoothness up to time a from a smooth extension to an     *)
(* open set containing [a,b) x U.                                            *)
(* ========================================================================= *)

let PDG_LDETURCK_ST_SMOOTH = prove
 (`!D (U:real^N->bool) (H:real^N->real^N^N)
    (FU:real^(1,N)finite_sum->real^(N,N)finite_prod).
     open D /\ metric_field U H /\ smooth_map_on D FU /\
     (!w. w IN D ==> sndcart w IN U /\
                     ~(det((matrify:real^(N,N)finite_prod->real^N^N) (FU w)) = &0))
     ==> smooth_map_on D
           (\w. pde_ldeturck H (\z. (matrify:real^(N,N)finite_prod->real^N^N)
                                      (FU(pastecart (fstcart w) z))) (sndcart w))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC I [MATCH_MP SMOOTH_MAP_ON_COMPONENTWISE th] o
    check (fun _ -> concl th = `open (D:real^(1,N)finite_sum->bool)`)) THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[PDE_LDETURCK_JET] THEN
  MATCH_MP_TAC PDE_SM_JW THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[pde_jgi; PASTECART_FST_SND] THEN
    SUBGOAL_THEN
     `(\w. lift(matrix_inv((matrify:real^(N,N)finite_prod->real^N^N)
                             ((FU:real^(1,N)finite_sum->real^(N,N)finite_prod) w))$i$j)) =
      (\x:real^(N,N)finite_prod. lift((matrify x:real^N^N)$i$j)) o
      ((vectorize:real^N^N->real^(N,N)finite_prod) o (\w. matrix_inv(matrify(FU w))))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; MATRIFY_VECTORIZE]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[LRG_LINEAR_MATRIFY_ENTRY] THEN
    MATCH_MP_TAC LRG_SMOOTH_MATRIX_INV THEN ASM_SIMP_TAC[] THEN
    ASM_REWRITE_TAC[o_DEF; VECTORIZE_MATRIFY; ETA_AX];
    REPEAT GEN_TAC THEN REWRITE_TAC[pde_jd1; mderiv; o_DEF; VECTORIZE_MATRIFY] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `\w. lift(((matrify:real^(N,N)finite_prod->real^N^N)
                           (frechet_derivative (FU:real^(1,N)finite_sum->real^(N,N)finite_prod)
                              (at w) (pastecart (vec 0) (basis c))))$i$j)` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `w:real^(1,N)finite_sum` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`FU:real^(1,N)finite_sum->real^(N,N)finite_prod`;
                     `fstcart(w:real^(1,N)finite_sum)`; `sndcart(w:real^(1,N)finite_sum)`;
                     `basis c:real^N`] LRG_SLICE_DERIV) THEN
      REWRITE_TAC[PASTECART_FST_SND] THEN ANTS_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
        EXISTS_TAC `D:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[];
        DISCH_THEN(fun th -> REWRITE_TAC[th])];
      SUBGOAL_THEN
       `(\w. lift(((matrify:real^(N,N)finite_prod->real^N^N)
                    (frechet_derivative (FU:real^(1,N)finite_sum->real^(N,N)finite_prod)
                       (at w) (pastecart (vec 0) (basis c))))$i$j)) =
        (\x:real^(N,N)finite_prod. lift((matrify x:real^N^N)$i$j)) o
        (\w. frechet_derivative FU (at w) (pastecart (vec 0) (basis c)))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
      ASM_SIMP_TAC[LRG_LINEAR_MATRIFY_ENTRY; SMOOTH_MAP_ON_FRECHET_DERIVATIVE]];
    REPEAT GEN_TAC THEN REWRITE_TAC[pde_jhc] THEN
    SUBGOAL_THEN
     `(\w:real^(1,N)finite_sum. lift(christoffel (H:real^N->real^N^N) (sndcart w)
                                      (basis i) (basis j)$c)) =
      (\z. lift(christoffel H z (basis i) (basis j)$c)) o sndcart`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
    UNDISCH_TAC `metric_field U (H:real^N->real^N^N)` THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN
      STRIP_ASSUME_TAC(GEN_REWRITE_RULE I [metric_field] th)) THEN
    ASM_SIMP_TAC[PDE_SMOOTH_CHR_ENTRY] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^(1,N)finite_sum)` THEN
      REWRITE_TAC[SUBSET_UNIV; TEXT_SMOOTH_MAP_ON_FSTCART_SNDCART]]]);;

(* Smoothness up to time a from a smooth map on an open set containing     *)
(* [a,b) x U.                                                                *)

let PDG_UPTO_FROM_OPEN = prove
 (`!a b (U:real^N->bool) (u:real->real^N->real^K) D (Fl:real^(1,N)finite_sum->real^K).
        open U /\ a < b /\ open D /\ smooth_map_on D Fl /\
        (!t y. a <= t /\ t < b /\ y IN U
               ==> pastecart (lift t) y IN D /\ Fl(pastecart (lift t) y) = u t y)
        ==> pde_upto a b U u`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PDG_UPTO_LOCAL_ST THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`D:real^(1,N)finite_sum->bool`; `Fl:real^(1,N)finite_sum->real^K`] THEN
  ASM_SIMP_TAC[]);;

(* The chart representatives of the DeTurck field of a family of metrics   *)
(* smooth up to time a are smooth up to time a.                             *)

let PDG_DETURCK_FAMILY_UPTO = prove
 (`!top atlas (h:A->real^N^N) (gb:real->A->real^N^N) a b (c:(A->bool)#(A->real^N)).
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas h /\ a < b /\
        (!t. a <= t /\ t < b ==> riemannian_metric atlas (gb t)) /\
        pde_tfam_from atlas a b gb /\ c IN atlas
        ==> pde_upto a b (IMAGE (SND c) (FST c))
              (\t y. mfd_vrep atlas (pde_deturck atlas (gb t) h) c y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `pde_tfam_from atlas a b (gb:real->A->real^N^N)` THEN
  REWRITE_TAC[pde_tfam_from] THEN DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN
    `FF:real^(1,N)finite_sum->real^(N,N)finite_prod` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC
   `D = {w | w IN interval(lift(a - e),lift b) PCROSS IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c) /\
             lift(det((matrify:real^(N,N)finite_prod->real^N^N)
                        ((FF:real^(1,N)finite_sum->real^(N,N)finite_prod) w))) IN
             (:real^1) DIFF {vec 0}}` THEN
  SUBGOAL_THEN `open (D:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_DIFF; OPEN_UNIV; CLOSED_SING] THEN
    MATCH_MP_TAC CONTINUOUS_ON_DET_VECTORIZE THEN
    REWRITE_TAC[VECTORIZE_MATRIFY; ETA_AX] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `D SUBSET interval(lift(a - e),lift b) PCROSS IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`
  ASSUME_TAC THENL [EXPAND_TAC "D" THEN SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC PDG_UPTO_FROM_OPEN THEN
  EXISTS_TAC `D:real^(1,N)finite_sum->bool` THEN
  EXISTS_TAC
   `\w. pde_ldeturck (metric_local atlas (c:(A->bool)#(A->real^N)) (h:A->real^N^N))
          (\z. (matrify:real^(N,N)finite_prod->real^N^N)
                 ((FF:real^(1,N)finite_sum->real^(N,N)finite_prod) (pastecart (fstcart w) z)))
          (sndcart w)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PDG_LDETURCK_ST_SMOOTH THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas (h:A->real^N^N)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `interval(lift(a - e),lift b) PCROSS
                  IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[FORALL_PASTECART] THEN EXPAND_TAC "D" THEN
      REWRITE_TAC[IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_SING; GSYM LIFT_NUM; LIFT_EQ;
                  PASTECART_IN_PCROSS; SNDCART_PASTECART] THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric atlas ((gb:real->A->real^N^N) t)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))
                 (metric_local atlas c ((gb:real->A->real^N^N) t))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas ((gb:real->A->real^N^N) t)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [EXPAND_TAC "D" THEN
    REWRITE_TAC[IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_SING; GSYM LIFT_NUM; LIFT_EQ] THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[MATRIFY_VECTORIZE] THEN
      MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`;
                     `metric_local atlas (c:(A->bool)#(A->real^N)) ((gb:real->A->real^N^N) t)`;
                     `y:real^N`] LRG_METRIC_INVERTIBLE) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `(gb:real->A->real^N^N) t`; `h:A->real^N^N`;
                 `y:real^N`] PDG_DETURCK_VREP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC PDG_LDETURCK_LOCAL THEN
  EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN ASM_SIMP_TAC[MATRIFY_VECTORIZE]);;

(* ========================================================================= *)
(* Extension below time a of a family of vector fields whose chart           *)
(* representatives are smooth up to time a, by a partition of unity          *)
(* subordinate to a finite cover, to a field smooth on an open time interval *)
(* (the hypothesis mfl_hyp of the manifold flow).                            *)
(* ========================================================================= *)

let PDG_FINITE_POS_LB = prove
 (`!(f:num->real) n. (!i. i < n ==> &0 < f i) ==> ?e. &0 < e /\ !i. i < n ==> e <= f i`,
  GEN_TAC THEN INDUCT_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `&1` THEN REWRITE_TAC[LT] THEN REAL_ARITH_TAC;
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min e ((f:num->real) n)` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
      X_GEN_TAC `i:num` THEN REWRITE_TAC[LT] THEN STRIP_TAC THENL
       [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `e <= x ==> min e y <= x`) THEN ASM_SIMP_TAC[]]]]);;

(* Smoothness of the application of a Jacobian to a smooth family.          *)

let PDG_JAC_APPLY_SMOOTH = prove
 (`!(S:real^M->bool) s0 (tau:real^N->real^P) (sigma:real^M->real^N) (V:real^M->real^N).
        open S /\ open s0 /\ smooth_map_on s0 tau /\ smooth_map_on S sigma /\
        IMAGE sigma S SUBSET s0 /\ smooth_map_on S V
        ==> smooth_map_on S (\w. frechet_derivative tau (at (sigma w)) (V w))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `\w. vsum(1..dimindex(:N))
                    (\k. drop(lift((V:real^M->real^N) w$k)) %
                         ((\z. frechet_derivative (tau:real^N->real^P) (at z) (basis k)) o
                          (sigma:real^M->real^N)) w)` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `w:real^M` THEN DISCH_TAC THEN REWRITE_TAC[o_THM; LIFT_DROP] THEN
    SUBGOAL_THEN `linear(frechet_derivative (tau:real^N->real^P) (at ((sigma:real^M->real^N) w)))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s0:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
    ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL];
    MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_LIFT_COMPONENT; ETA_AX] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `s0:real^N->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE]]);;

(* One term of the extended field in a chart c.                               *)

let PDG_FIELD_TERM_SMOOTH = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) (ci:(A->bool)#(A->real^N)) (rho:A->real) L
    (J:real^1->bool) (E:real^(1,N)finite_sum->real^N).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ c IN atlas /\ ci IN atlas /\
        mfd_smooth atlas (\x. lift(rho x)) /\ compact_in top L /\ L SUBSET FST ci /\
        (!x. ~(x IN L) ==> rho x = &0) /\ open J /\
        smooth_map_on (J PCROSS IMAGE (SND ci) (FST ci)) E
        ==> smooth_map_on (J PCROSS IMAGE (SND c) (FST c))
              (\w. rho(chart_inv c (sndcart w)) %
                   (if chart_inv c (sndcart w) IN FST ci
                    then chart_jac ci c (chart_inv c (sndcart w))
                           (E(pastecart (fstcart w) (chart_trans c ci (sndcart w))))
                    else vec 0))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `ci:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_SIMP_TAC[OPEN_PCROSS; FORALL_IN_PCROSS] THEN
  MAP_EVERY X_GEN_TAC [`t0:real^1`; `y0:real^N`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `chart_inv (c:(A->bool)#(A->real^N)) y0 IN FST(ci:(A->bool)#(A->real^N))` THENL
   [EXISTS_TAC `(J:real^1->bool) PCROSS
                IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER FST(ci:(A->bool)#(A->real^N)))` THEN
    SUBGOAL_THEN
     `open(IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER FST(ci:(A->bool)#(A->real^N))))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_SIMP_TAC[OPEN_IN_INTER] THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[OPEN_PCROSS; PASTECART_IN_PCROSS] THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
      EXISTS_TAC `chart_inv (c:(A->bool)#(A->real^N)) y0` THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC
     `\w. drop(((\x:A. lift((rho:A->real) x)) o chart_inv (c:(A->bool)#(A->real^N)) o
               sndcart) w) %
          frechet_derivative (chart_trans (ci:(A->bool)#(A->real^N)) c)
            (at (chart_trans c ci (sndcart w)))
            ((E:real^(1,N)finite_sum->real^N) (pastecart (fstcart w) (chart_trans c ci (sndcart w))))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART; o_THM;
                  LIFT_DROP] THEN
      MAP_EVERY X_GEN_TAC [`t:real^1`; `y:real^N`] THEN
      REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) y = x` ASSUME_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[chart_jac] THEN REWRITE_TAC[chart_trans] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN
    ASM_SIMP_TAC[OPEN_PCROSS; ETA_AX] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `(J:real^1->bool) PCROSS IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL] THEN
        MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[o_ASSOC] THEN MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
      EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
      ASM_SIMP_TAC[OPEN_PCROSS] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; SNDCART_PASTECART] THEN SIMP_TAC[];
        MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^(1,N)finite_sum)` THEN
        REWRITE_TAC[SUBSET_UNIV; TEXT_SMOOTH_MAP_ON_FSTCART_SNDCART];
        UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x. lift((rho:A->real) x))` THEN
        REWRITE_TAC[mfd_smooth] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `FST(ci:(A->bool)#(A->real^N))`; `SND(ci:(A->bool)#(A->real^N))`]
                  CHART_TRANS_SMOOTH) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(ci:(A->bool)#(A->real^N))`; `SND(ci:(A->bool)#(A->real^N))`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
                  CHART_TRANS_SMOOTH) THEN
    ASM_REWRITE_TAC[PAIR] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `open(IMAGE (SND(ci:(A->bool)#(A->real^N))) (FST ci INTER FST(c:(A->bool)#(A->real^N))))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_SIMP_TAC[OPEN_IN_INTER] THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!y. y IN IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER FST(ci:(A->bool)#(A->real^N)))
          ==> chart_trans c ci y IN IMAGE (SND ci) (FST ci INTER FST c)`
    ASSUME_TAC THENL
     [REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
      REWRITE_TAC[chart_trans] THEN ASM_SIMP_TAC[] THEN
      REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC PDG_JAC_APPLY_SMOOTH THEN
    EXISTS_TAC `IMAGE (SND(ci:(A->bool)#(A->real^N))) (FST ci INTER FST(c:(A->bool)#(A->real^N)))` THEN
    ASM_SIMP_TAC[OPEN_PCROSS] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM o_DEF] THEN MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
      EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER FST(ci:(A->bool)#(A->real^N)))` THEN
      ASM_SIMP_TAC[OPEN_PCROSS] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; SNDCART_PASTECART] THEN SIMP_TAC[];
        MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^(1,N)finite_sum)` THEN
        REWRITE_TAC[SUBSET_UNIV; TEXT_SMOOTH_MAP_ON_FSTCART_SNDCART]];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; SNDCART_PASTECART] THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\w:real^(1,N)finite_sum. (E:real^(1,N)finite_sum->real^N)
         (pastecart (fstcart w) (chart_trans (c:(A->bool)#(A->real^N)) ci (sndcart w)))) =
      E o (\w. pastecart (fstcart w) (chart_trans c ci (sndcart w)))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `(J:real^1->bool) PCROSS IMAGE (SND(ci:(A->bool)#(A->real^N))) (FST ci)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; FSTCART_PASTECART;
                  SNDCART_PASTECART; PASTECART_IN_PCROSS] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MP_TAC o C MATCH_MP
        (ASSUME `(y:real^N) IN IMAGE (SND(c:(A->bool)#(A->real^N)))
                                    (FST c INTER FST(ci:(A->bool)#(A->real^N)))`)) THEN
      SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_SIMP_TAC[OPEN_PCROSS] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^(1,N)finite_sum)` THEN
      REWRITE_TAC[SUBSET_UNIV; ETA_AX; TEXT_SMOOTH_MAP_ON_FSTCART_SNDCART];
      REWRITE_TAC[GSYM o_DEF] THEN MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
      EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER FST(ci:(A->bool)#(A->real^N)))` THEN
      ASM_SIMP_TAC[OPEN_PCROSS] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; SNDCART_PASTECART] THEN SIMP_TAC[];
        MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^(1,N)finite_sum)` THEN
        REWRITE_TAC[SUBSET_UNIV; TEXT_SMOOTH_MAP_ON_FSTCART_SNDCART]]];
    ALL_TAC] THEN
  (* away from the support *)
  SUBGOAL_THEN `closed_in top (L:A->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `(J:real^1->bool) PCROSS
              IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c DIFF (L:A->bool))` THEN
  SUBGOAL_THEN `open(IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c DIFF (L:A->bool)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_DIFF] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[OPEN_PCROSS; PASTECART_IN_PCROSS] THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_IMAGE; IN_DIFF] THEN
    EXISTS_TAC `chart_inv (c:(A->bool)#(A->real^N)) y0` THEN ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `(L:A->bool) SUBSET FST(ci:(A->bool)#(A->real^N))` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `\w:real^(1,N)finite_sum. vec 0:real^N` THEN
  REWRITE_TAC[SMOOTH_MAP_ON_CONST; FORALL_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  MAP_EVERY X_GEN_TAC [`t:real^1`; `y:real^N`] THEN
  REWRITE_TAC[IN_IMAGE; IN_DIFF] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) y = x` SUBST1_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[VECTOR_MUL_LZERO]);;

(* The chart representative in c, carried back to the preferred chart.      *)

let PDG_VREP_INVERT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (Z:A->real^N) c x.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ x IN FST c
        ==> chart_jac c (chart_at atlas x) x (mfd_vrep atlas Z c (SND c x)) = Z x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `x:A`] PDM_CHART_AT_C) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[mfd_vrep] THEN
  TRANS_TAC EQ_TRANS
   `chart_jac (chart_at atlas (x:A)) (chart_at atlas x) x ((Z:A->real^N) x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MFL_CHART_JAC_CHAIN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(chart_at atlas (x:A):(A->bool)#(A->real^N))`;
                   `SND(chart_at atlas (x:A):(A->bool)#(A->real^N))`; `x:A`]
                  CHART_JAC_SELF) THEN
    ASM_REWRITE_TAC[PAIR] THEN DISCH_THEN(fun th -> REWRITE_TAC[th])]);;

(* A Jacobian applied to a partition sum of transported vectors.             *)

let PDG_JAC_VSUM_TERMS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) c (cs:num->(A->bool)#(A->real^N))
    (phi:num->A->real) (W:num->real^N) n0 x.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ x IN FST c /\
        (!i. i < n0 ==> cs i IN atlas)
        ==> chart_jac (chart_at atlas x) c x
              (vsum {i | i < n0}
                 (\i. phi i x % (if x IN FST(cs i)
                                 then chart_jac (cs i) (chart_at atlas x) x (W i)
                                 else vec 0))) =
            vsum {i | i < n0}
              (\i. phi i x % (if x IN FST(cs i) then chart_jac (cs i) c x (W i)
                              else vec 0))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `x:A`] PDM_CHART_AT_C) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `linear(chart_jac (chart_at atlas (x:A)) (c:(A->bool)#(A->real^N)) x)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `chart_at atlas (x:A):(A->bool)#(A->real^N)`;
                   `c:(A->bool)#(A->real^N)`; `x:A`] MFL_CHART_TRANS_DERIV) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_VSUM
    (CONJ th (SPEC `n0:num` FINITE_NUMSEG_LT))]) THEN
  REWRITE_TAC[o_DEF] THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[LINEAR_CMUL] THEN AP_TERM_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC; FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_0 th])] THEN
  MATCH_MP_TAC MFL_CHART_JAC_CHAIN THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
  ASM_SIMP_TAC[]);;

(* The extension of a family of vector fields below a.                       *)

let PDG_FIELD_EXTEND = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (X:real->A->real^N) a b.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
        a < b /\
        (!c. c IN atlas
             ==> pde_upto a b (IMAGE (SND c) (FST c)) (\t y. mfd_vrep atlas (X t) c y))
        ==> ?e Y. &0 < e /\
                  (!t x. a <= t /\ t < b /\ x IN topspace top ==> Y t x = X t x) /\
                  mfl_hyp top atlas Y (interval(lift(a - e),lift b)) (topspace top)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "up"))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`]
                PDE_COVER_CUTOFFS_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n0:num` (X_CHOOSE_THEN `cs:num->(A->bool)#(A->real^N)`
    (X_CHOOSE_THEN `ks:num->real^N->bool` (X_CHOOSE_THEN `psi:num->A->real`
      STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `psi:num->A->real`] PDM_CUTOFF_PARTITION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:num->A->real` (CONJUNCTS_THEN2
    (MP_TAC o REWRITE_RULE[RIGHT_AND_EXISTS_THM; RIGHT_IMP_EXISTS_THM; SKOLEM_THM])
    (LABEL_TAC "sum1"))) THEN
  DISCH_THEN(X_CHOOSE_THEN `L:num->A->bool` (X_CHOOSE_THEN `V:num->A->bool`
    (LABEL_TAC "phi"))) THEN
  (* facts on the pieces *)
  SUBGOAL_THEN
   `!i. i < n0
        ==> (cs:num->(A->bool)#(A->real^N)) i IN atlas /\
            mfd_smooth atlas (\x. lift((phi:num->A->real) i x)) /\
            compact_in top ((L:num->A->bool) i) /\ L i SUBSET FST(cs i) /\
            (!x. ~(x IN L i) ==> phi i x = &0)`
  (LABEL_TAC "pc") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "phi" (fun th -> STRIP_ASSUME_TAC(MP (SPEC `i:num` th) (ASSUME `(i:num) < n0`))) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `pde_cover (top,atlas) n0 (cs:num->(A->bool)#(A->real^N)) ks` THEN
      REWRITE_TAC[pde_cover] THEN DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT1) THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      MATCH_MP_TAC PDM_SUPPORT_IN_CHART THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                            `n0:num`; `ks:num->real^N->bool`; `psi:num->A->real`] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(psi:num->A->real) i x = &1` (fun th -> REWRITE_TAC[th]) THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* the Seeley extensions in the charts of the cover *)
  SUBGOAL_THEN
   `?EE (FE:num->real^(1,N)finite_sum->real^N).
      !i. i < n0
          ==> &0 < EE i /\
              smooth_map_on (interval(lift(a - EE i),lift b) PCROSS
                             IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i)))
                            (FE i) /\
              !t y. a <= t /\ t < b /\ y IN IMAGE (SND(cs i)) (FST(cs i))
                    ==> FE i (pastecart (lift t) y) = mfd_vrep atlas (X t) (cs i) y`
  (X_CHOOSE_THEN `EE:num->real` (X_CHOOSE_THEN `FE:num->real^(1,N)finite_sum->real^N`
    (LABEL_TAC "ext"))) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `i:num` THEN
    REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
    USE_THEN "up" (MP_TAC o SPEC `(cs:num->(A->bool)#(A->real^N)) i`) THEN
    USE_THEN "pc" (fun th -> REWRITE_TAC[CONJUNCT1(MP (SPEC `i:num` th) (ASSUME `(i:num) < n0`))]) THEN
    REWRITE_TAC[pde_upto];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`EE:num->real`; `n0:num`] PDG_FINITE_POS_LB) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "ext" (fun th -> REWRITE_TAC[CONJUNCT1(MP (SPEC `i:num` th) (ASSUME `(i:num) < n0`))]);
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `e:real` THEN
  EXISTS_TAC
   `\t x. vsum {i | i < n0}
            (\i. (phi:num->A->real) i x %
                 (if x IN FST((cs:num->(A->bool)#(A->real^N)) i)
                  then chart_jac (cs i) (chart_at atlas x) x
                         ((FE:num->real^(1,N)finite_sum->real^N) i
                            (pastecart (lift t) (SND(cs i) x)))
                  else vec 0))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [(* agreement with X on [a,b) *)
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
    TRANS_TAC EQ_TRANS
     `vsum {i | i < n0} (\i. (phi:num->A->real) i x % (X:real->A->real^N) t x)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN
      DISCH_TAC THEN
      USE_THEN "pc" (fun th -> STRIP_ASSUME_TAC(MP (SPEC `i:num` th) (ASSUME `(i:num) < n0`))) THEN
      COND_CASES_TAC THENL
       [AP_TERM_TAC THEN
        SUBGOAL_THEN
         `(FE:num->real^(1,N)finite_sum->real^N) i
            (pastecart (lift t) (SND((cs:num->(A->bool)#(A->real^N)) i) (x:A))) =
          mfd_vrep atlas ((X:real->A->real^N) t) (cs i) (SND(cs i) x)`
        SUBST1_TAC THENL
         [USE_THEN "ext" (fun th -> MATCH_MP_TAC(CONJUNCT2(CONJUNCT2
            (MP (SPEC `i:num` th) (ASSUME `(i:num) < n0`))))) THEN
          ASM_SIMP_TAC[FUN_IN_IMAGE];
          MATCH_MP_TAC PDG_VREP_INVERT THEN EXISTS_TAC `top:A topology` THEN
          ASM_REWRITE_TAC[]];
        SUBGOAL_THEN `(phi:num->A->real) i x = &0`
          (fun th -> REWRITE_TAC[th; VECTOR_MUL_LZERO]) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
      REWRITE_TAC[VSUM_RMUL] THEN
      USE_THEN "sum1" (fun th -> REWRITE_TAC[MP (SPEC `x:A` th) (ASSUME `(x:A) IN topspace top`)]) THEN
      REWRITE_TAC[VECTOR_MUL_LID]];
    ALL_TAC] THEN
  (* the flow hypotheses *)
  REWRITE_TAC[mfl_hyp] THEN
  ASM_REWRITE_TAC[OPEN_INTERVAL; IS_INTERVAL_INTERVAL; DIFF_EQ_EMPTY; NOT_IN_EMPTY;
                  GSYM compact_space] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC
   `\w:real^(1,N)finite_sum.
      vsum {i | i < n0}
        (\i. (phi:num->A->real) i (chart_inv (c:(A->bool)#(A->real^N)) (sndcart w)) %
             (if chart_inv c (sndcart w) IN FST((cs:num->(A->bool)#(A->real^N)) i)
              then chart_jac (cs i) c (chart_inv c (sndcart w))
                     ((FE:num->real^(1,N)finite_sum->real^N) i
                        (pastecart (fstcart w) (chart_trans c (cs i) (sndcart w))))
              else vec 0))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_PCROSS; MFL_FIELD_PASTECART; FSTCART_PASTECART;
                SNDCART_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`t:real^1`; `y:real^N`] THEN STRIP_TAC THEN
    REWRITE_TAC[mfd_vrep; LIFT_DROP; chart_trans] THEN
    SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) y IN FST c` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC PDG_JAC_VSUM_TERMS THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "pc" (fun th -> REWRITE_TAC[CONJUNCT1(MP (SPEC `i:num` th) (ASSUME `(i:num) < n0`))]);
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  USE_THEN "pc" (fun th -> STRIP_ASSUME_TAC(MP (SPEC `i:num` th) (ASSUME `(i:num) < n0`))) THEN
  MATCH_MP_TAC PDG_FIELD_TERM_SMOOTH THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                        `(L:num->A->bool) i`] THEN
  ASM_REWRITE_TAC[OPEN_INTERVAL; ETA_AX] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
  EXISTS_TAC `interval(lift(a - (EE:num->real) i),lift b) PCROSS
              IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))` THEN
  USE_THEN "ext" (fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2
    (MP (SPEC `i:num` th) (ASSUME `(i:num) < n0`)))]) THEN
  MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL] THEN
  REWRITE_TAC[SUBSET; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
  SUBGOAL_THEN `e <= (EE:num->real) i` MP_TAC THENL
   [ASM_SIMP_TAC[]; REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Smoothness of pullbacks of space-time families along space-time maps; the *)
(* negated DeTurck field; the pullback metric along a flow in a pair of      *)
(* charts; pullback by the identity; the pulled-back family is smooth up to  *)
(* time a in every chart.                                                    *)
(* ========================================================================= *)

(* Congruence of a constant matrix by a smooth matrix family.               *)

let PDG_CONGR_COEFF_SMOOTH = prove
 (`!s (A:real^M->real^N^N) (E:real^N^N).
        open s /\ smooth_map_on s ((vectorize:real^N^N->real^(N,N)finite_prod) o A)
        ==> smooth_map_on s
              (\w. (vectorize:real^N^N->real^(N,N)finite_prod) (transp(A w) ** E ** A w))`,
  REPEAT STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[o_DEF]) THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\w. transp((A:real^M->real^N^N) w)`;
                 `\w. (E:real^N^N) ** (A:real^M->real^N^N) w`] LRG_SMOOTH_MATMUL) THEN
  REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`s:real^M->bool`; `A:real^M->real^N^N`] LRG_SMOOTH_TRANSP) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`s:real^M->bool`; `\w:real^M. E:real^N^N`; `A:real^M->real^N^N`]
                  LRG_SMOOTH_MATMUL) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST]]);;

(* The spatial Jacobian matrix of a smooth space-time map is smooth.        *)

let PDG_ST_JAC_SMOOTH = prove
 (`!SS (Fm:real^(1,N)finite_sum->real^N).
        open SS /\ smooth_map_on SS Fm
        ==> smooth_map_on SS
              ((vectorize:real^N^N->real^(N,N)finite_prod) o
               (\w. matrix(frechet_derivative (\z. Fm(pastecart (fstcart w) z))
                                              (at (sndcart w)))))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LRG_SMOOTH_VECTORIZE] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MATRIX_COMPONENT] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `\w. lift(frechet_derivative (Fm:real^(1,N)finite_sum->real^N) (at w)
                         (pastecart (vec 0) (basis j))$i)` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `w:real^(1,N)finite_sum` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`Fm:real^(1,N)finite_sum->real^N`; `fstcart(w:real^(1,N)finite_sum)`;
                   `sndcart(w:real^(1,N)finite_sum)`; `basis j:real^N`] LRG_SLICE_DERIV) THEN
    REWRITE_TAC[PASTECART_FST_SND] THEN ANTS_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `SS:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(fun th -> REWRITE_TAC[th])];
    MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE]]);;

(* Pullback of a space-time family of matrices along a space-time map.      *)

let PDG_MPULLBACK_SMOOTH_TD = prove
 (`!SS DD (Fm:real^(1,N)finite_sum->real^N)
    (G:real^(1,N)finite_sum->real^(N,N)finite_prod).
        open SS /\ open DD /\ smooth_map_on SS Fm /\ smooth_map_on DD G /\
        (!w. w IN SS ==> pastecart (fstcart w) (Fm w) IN DD)
        ==> smooth_map_on SS
              (\w. (vectorize:real^N^N->real^(N,N)finite_prod)
                     (mpullback (\z. Fm(pastecart (fstcart w) z))
                        (\z. (matrify:real^(N,N)finite_prod->real^N^N)
                               (G(pastecart (fstcart w) z)))
                        (sndcart w)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[PDM_MPULLBACK_FORM; o_THM; VECTORIZE_MATRIFY; PASTECART_FST_SND] THEN
  MP_TAC(ISPECL [`SS:real^(1,N)finite_sum->bool`; `DD:real^(1,N)finite_sum->bool`;
                 `\w:real^(1,N)finite_sum.
                    pastecart (fstcart w) ((Fm:real^(1,N)finite_sum->real^N) w)`;
                 `\q (w:real^(1,N)finite_sum). (vectorize:real^N^N->real^(N,N)finite_prod)
                     (transp(matrix(frechet_derivative
                        (\z. (Fm:real^(1,N)finite_sum->real^N)(pastecart (fstcart w) z))
                        (at (sndcart w)))) **
                      (matrify(basis q):real^N^N) **
                      matrix(frechet_derivative (\z. Fm(pastecart (fstcart w) z))
                                                (at (sndcart w))))`;
                 `G:real^(1,N)finite_sum->real^(N,N)finite_prod`] PDM_FORM_SMOOTH) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^(1,N)finite_sum)` THEN
    REWRITE_TAC[SUBSET_UNIV; ETA_AX; TEXT_SMOOTH_MAP_ON_FSTCART_SNDCART];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
    X_GEN_TAC `q:num` THEN
    MP_TAC(ISPECL [`SS:real^(1,N)finite_sum->bool`;
                   `\w:real^(1,N)finite_sum.
                      matrix(frechet_derivative
                        (\z. (Fm:real^(1,N)finite_sum->real^N)(pastecart (fstcart w) z))
                        (at (sndcart w)))`;
                   `(matrify(basis q):real^N^N)`] PDG_CONGR_COEFF_SMOOTH) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[PDG_ST_JAC_SMOOTH]]);;

(* A pullback only uses the matrix field at the image point.                *)

let PDG_MPULLBACK_AT = prove
 (`!(hm:real^N->real^N) (G1:real^N->real^N^N) G2 y.
        G1(hm y) = G2(hm y) ==> mpullback hm G1 y = mpullback hm G2 y`,
  SIMP_TAC[mpullback]);;

(* Chart representatives of the negative of a vector field.                 *)

let PDG_VREP_NEG = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (Z:A->real^N) c y.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ y IN IMAGE (SND c) (FST c)
        ==> mfd_vrep atlas (\x. --(Z x)) c y = --(mfd_vrep atlas Z c y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `chart_inv (c:(A->bool)#(A->real^N)) y`]
                PDM_CHART_AT_C) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `chart_at atlas (chart_inv (c:(A->bool)#(A->real^N)) y)
                    :(A->bool)#(A->real^N)`;
                 `c:(A->bool)#(A->real^N)`; `chart_inv (c:(A->bool)#(A->real^N)) y`]
                MFL_CHART_TRANS_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[mfd_vrep] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_NEG th]));;

(* The chart representatives of the negated DeTurck field of a              *)
(* Ricci-DeTurck flow are smooth up to time a.                               *)

let PDG_NEG_DETURCK_UPTO = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) h a b gb c.
        riemannian_metric atlas h /\ pde_rdt_flow_from (top,atlas) h a b gb /\ c IN atlas
        ==> pde_upto a b (IMAGE (SND c) (FST c))
              (\t y. mfd_vrep atlas (\x. --(pde_deturck atlas (gb t) h x)) c y)`,
  REWRITE_TAC[pde_rdt_flow_from] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC PDM_UPTO_CONG THEN
  EXISTS_TAC `\t y. --(mfd_vrep atlas (pde_deturck atlas ((gb:real->A->real^N^N) t) h)
                                (c:(A->bool)#(A->real^N)) y)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `h:A->real^N^N`; `gb:real->A->real^N^N`; `a:real`; `b:real`;
                   `c:(A->bool)#(A->real^N)`] PDG_DETURCK_FAMILY_UPTO) THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[pde_upto] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `Fw:real^(1,N)finite_sum->real^N`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`e:real`; `\w. --((Fw:real^(1,N)finite_sum->real^N) w)`] THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_NEG_OPEN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OPEN_PCROSS THEN REWRITE_TAC[OPEN_INTERVAL] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
    ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC PDG_VREP_NEG THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]]);;

(* The pullback metric along a flow map in a pair of charts.                *)

let PDG_FLOW_METRIC_LOCAL = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (Y:real->A->real^N) J K s t
    (gm:A->real^N^N) c c' y.
        mfl_hyp top atlas Y J K /\ s IN J /\ t IN J /\ c IN atlas /\ c' IN atlas /\
        y IN IMAGE (SND c) (FST c) /\ mfl_flow top atlas Y s t (chart_inv c y) IN FST c'
        ==> metric_local atlas c
              (mfd_pullback_metric atlas atlas (mfl_flow top atlas Y s t) gm) y =
            mpullback (SND c' o mfl_flow top atlas Y s t o chart_inv c)
                      (metric_local atlas c' gm) y`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [mfl_hyp]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `mfl_flow top atlas (Y:real->A->real^N) s t`;
                 `mfl_flow top atlas (Y:real->A->real^N) t s`;
                 `gm:A->real^N^N`; `FST(c:(A->bool)#(A->real^N))`;
                 `SND(c:(A->bool)#(A->real^N))`;
                 `FST(c':(A->bool)#(A->real^N))`; `SND(c':(A->bool)#(A->real^N))`;
                 `chart_inv (c:(A->bool)#(A->real^N)) y`] MFD_PULLBACK_METRIC_LOCAL) THEN
  ASM_REWRITE_TAC[PAIR] THEN ANTS_TAC THENL
   [MATCH_MP_TAC MFL_FLOW_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `K:A->bool`] THEN ASM_REWRITE_TAC[];
    DISCH_THEN(fun th -> REWRITE_TAC[th])]);;

(* Pullback by a map that is the identity on the manifold.                  *)

let PDG_PULLBACK_ID = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (f:A->A) (gm:A->real^N^N) x.
        smooth_manifold_atlas top atlas /\ (!z. z IN topspace top ==> f z = z) /\
        x IN topspace top
        ==> mfd_pullback_metric atlas atlas f gm x = gm x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_pullback_metric] THEN
  ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `chart_at atlas (x:A):(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `chart_at atlas (x:A):(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `frechet_derivative (SND(chart_at atlas (x:A):(A->bool)#(A->real^N)) o (f:A->A) o
                        chart_inv (chart_at atlas x))
                       (at (SND(chart_at atlas x) x)) = (\v. v)`
  ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    MAP_EVERY EXISTS_TAC
     [`\y:real^N. y`;
      `IMAGE (SND(chart_at atlas (x:A):(A->bool)#(A->real^N))) (FST(chart_at atlas x))`] THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE; HAS_DERIVATIVE_ID] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN
     `chart_inv (chart_at atlas (x:A):(A->bool)#(A->real^N)) (y:real^N) IN
        FST(chart_at atlas x) /\
      SND(chart_at atlas x) (chart_inv (chart_at atlas x) y) = y`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(f:A->A) (chart_inv (chart_at atlas (x:A):(A->bool)#(A->real^N)) (y:real^N)) =
      chart_inv (chart_at atlas x) y`
    SUBST1_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[mpullback; MATRIX_ID; TRANSP_MAT; MATRIX_MUL_LID; MATRIX_MUL_RID;
                  o_THM] THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC METRIC_LOCAL_AT THEN
  EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]);;

(* The family pulled back along the flow from time a is smooth up to a in   *)
(* every chart.                                                              *)

let PDG_GAUGE_TFAM = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (Y:real->A->real^N) e a b
    (gb:real->A->real^N^N).
        mfl_hyp top atlas Y (interval(lift(a - e),lift b)) (topspace top) /\
        &0 < e /\ a < b /\ pde_tfam_from atlas a b gb
        ==> pde_tfam_from atlas a b
              (\t. mfd_pullback_metric atlas atlas
                     (mfl_flow top atlas Y (lift a) (lift t)) (gb t))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [mfl_hyp]) THEN
  REWRITE_TAC[PDM_TFAM_FROM_UPTO] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC PDG_UPTO_LOCAL_ST THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`t0:real`; `y0:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lift a IN interval(lift(a - e),lift b) /\
                lift t0 IN interval(lift(a - e),lift b)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) y0 IN FST c` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `x1 = mfl_flow top atlas (Y:real->A->real^N) (lift a) (lift t0)
                     (chart_inv (c:(A->bool)#(A->real^N)) y0)` THEN
  SUBGOAL_THEN `(x1:A) IN topspace top` ASSUME_TAC THENL
   [EXPAND_TAC "x1" THEN MATCH_MP_TAC MFL_FLOW_IN THEN
    MAP_EVERY EXISTS_TAC [`interval(lift(a - e),lift b)`; `topspace top:A->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x1:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c' = chart_at atlas (x1:A):(A->bool)#(A->real^N)` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c':(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `pde_tfam_from atlas a b (gb:real->A->real^N^N)` THEN
  REWRITE_TAC[pde_tfam_from] THEN DISCH_THEN(MP_TAC o SPEC `c':(A->bool)#(A->real^N)`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (X_CHOOSE_THEN
    `FG:real^(1,N)finite_sum->real^(N,N)finite_prod`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "FG"))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `Y:real->A->real^N`; `interval(lift(a - e),lift b)`;
                 `topspace top:A->bool`; `c:(A->bool)#(A->real^N)`;
                 `c':(A->bool)#(A->real^N)`; `lift a`] MFL_JOINT_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `O1 = {pastecart t y | t IN interval(lift(a - e),lift b) /\
                          y IN IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c) /\
                          mfl_flow top atlas (Y:real->A->real^N) (lift a) t (chart_inv c y) IN
                          FST (c':(A->bool)#(A->real^N))}` THEN
  ABBREV_TAC
   `Fm = \w:real^(1,N)finite_sum.
           SND (c':(A->bool)#(A->real^N))
             (mfl_flow top atlas (Y:real->A->real^N) (lift a) (fstcart w)
                (chart_inv (c:(A->bool)#(A->real^N)) (sndcart w)))` THEN
  STRIP_TAC THEN
  EXISTS_TAC `(O1:real^(1,N)finite_sum->bool) INTER
              (interval(lift(a - e1),lift b) PCROSS (:real^N))` THEN
  EXISTS_TAC
   `\w. (vectorize:real^N^N->real^(N,N)finite_prod)
          (mpullback (\z. (Fm:real^(1,N)finite_sum->real^N) (pastecart (fstcart w) z))
             (\z. (matrify:real^(N,N)finite_prod->real^N^N)
                    ((FG:real^(1,N)finite_sum->real^(N,N)finite_prod)
                       (pastecart (fstcart w) z)))
             (sndcart w))` THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[OPEN_INTER; OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV];
    EXPAND_TAC "O1" THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_PASTECART_THM; PASTECART_IN_PCROSS; IN_UNIV] THEN
    REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC PDG_MPULLBACK_SMOOTH_TD THEN
    EXISTS_TAC `interval(lift(a - e1),lift b) PCROSS
                IMAGE (SND (c':(A->bool)#(A->real^N))) (FST c')` THEN
    ASM_SIMP_TAC[OPEN_INTER; OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `O1:real^(1,N)finite_sum->bool` THEN
      ASM_REWRITE_TAC[INTER_SUBSET];
      REWRITE_TAC[FORALL_PASTECART; IN_INTER; PASTECART_IN_PCROSS; FSTCART_PASTECART;
                  IN_UNIV] THEN
      MAP_EVERY X_GEN_TAC [`t:real^1`; `y:real^N`] THEN EXPAND_TAC "O1" THEN
      REWRITE_TAC[IN_ELIM_PASTECART_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "Fm" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
      ASM_SIMP_TAC[FUN_IN_IMAGE]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `z:real^N`] THEN
  REWRITE_TAC[IN_INTER] THEN EXPAND_TAC "O1" THEN
  REWRITE_TAC[IN_ELIM_PASTECART_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `Y:real->A->real^N`; `interval(lift(a - e),lift b)`;
                 `topspace top:A->bool`; `lift a`; `lift s`; `(gb:real->A->real^N^N) s`;
                 `c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`; `z:real^N`]
                PDG_FLOW_METRIC_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `(\z'. (Fm:real^(1,N)finite_sum->real^N) (pastecart (lift s) z')) =
    SND (c':(A->bool)#(A->real^N)) o mfl_flow top atlas (Y:real->A->real^N) (lift a) (lift s) o
    chart_inv (c:(A->bool)#(A->real^N))`
  SUBST1_TAC THENL
   [EXPAND_TAC "Fm" THEN REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART;
                                     SNDCART_PASTECART];
    ALL_TAC] THEN
  MATCH_MP_TAC PDG_MPULLBACK_AT THEN REWRITE_TAC[o_THM] THEN
  USE_THEN "FG" (MP_TAC o SPECL [`s:real`;
    `SND (c':(A->bool)#(A->real^N)) (mfl_flow top atlas (Y:real->A->real^N) (lift a) (lift s)
       (chart_inv (c:(A->bool)#(A->real^N)) z))`]) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE; MATRIFY_VECTORIZE]);;

(* ========================================================================= *)
(* The Lie derivative along the negated field; time derivatives of matrix    *)
(* families entrywise; the time derivative of the flow in charts; the Ricci  *)
(* matrix under congruence; the cancellation of the DeTurck terms.           *)
(* ========================================================================= *)

let PDG_MATRIFY_NEG = prove
 (`!v:real^(N,N)finite_prod. (matrify(--v):real^N^N) = --(matrify v)`,
  REWRITE_TAC[VECTOR_NEG_MINUS1; MATRIFY_CMUL; GSYM MATRIX_NEG_MINUS1]);;

(* The Lie derivative along the negative of a differentiable field.         *)

let PDG_LLIE_NEG = prove
 (`!(W:real^N->real^N) (G:real^N->real^N^N) y.
        W differentiable at y /\
        ((vectorize:real^N^N->real^(N,N)finite_prod) o G) differentiable at y
        ==> llie (\z. --(W z)) G y = --(llie W G y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `frechet_derivative (\z. --((W:real^N->real^N) z)) (at y) =
                (\v. --(frechet_derivative W (at y) v))` (LABEL_TAC "dneg") THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC HAS_DERIVATIVE_NEG THEN
    ASM_REWRITE_TAC[ETA_AX; GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(frechet_derivative (W:real^N->real^N) (at y))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LINEAR_FRECHET_DERIVATIVE]; ALL_TAC] THEN
  SUBGOAL_THEN `linear(frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                           (G:real^N->real^N^N)) (at y))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LINEAR_FRECHET_DERIVATIVE]; ALL_TAC] THEN
  REWRITE_TAC[llie; mderiv] THEN USE_THEN "dneg" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[MATCH_MP MATRIX_NEG
    (ASSUME `linear(frechet_derivative (W:real^N->real^N) (at y))`)] THEN
  REWRITE_TAC[MATCH_MP LINEAR_NEG
    (ASSUME `linear(frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                        (G:real^N->real^N^N)) (at y))`)] THEN
  REWRITE_TAC[PDG_MATRIFY_NEG; TRANSP_MATRIX_NEG; MATRIX_MUL_LNEG; MATRIX_MUL_RNEG;
              MATRIX_NEG_ADD]);;

(* The time derivative of a space-time family of matrices, entrywise.       *)

let PDG_TIME_DERIV_MATRIX = prove
 (`!(Gm:real^(1,N)finite_sum->real^N^N) t z (Q:real^N^N).
        ((vectorize:real^N^N->real^(N,N)finite_prod) o Gm) differentiable
          at (pastecart (lift t) z) /\
        (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
               ==> ((\s. Gm(pastecart (lift s) z)$i$j) has_real_derivative Q$i$j)
                   (atreal t))
        ==> (matrify:real^(N,N)finite_prod->real^N^N)
              (frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o Gm)
                 (at (pastecart (lift t) z)) (pastecart (lift(&1)) (vec 0))) = Q`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LRG_TIME_CURVE_VDERIV) THEN
  ABBREV_TAC
   `V = frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o
                            (Gm:real^(1,N)finite_sum->real^N^N))
          (at (pastecart (lift t) z)) (pastecart (lift(&1)) (vec 0))` THEN
  REWRITE_TAC[o_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!p q. ((\s. (Gm:real^(1,N)finite_sum->real^N^N) (pastecart (lift s) z)$p$q)
           has_real_derivative ((matrify:real^(N,N)finite_prod->real^N^N) V)$p$q)
          (atreal t)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC LRG_VDERIV_MATRIX_ENTRY_REAL THEN
    ASM_REWRITE_TAC[VECTORIZE_MATRIFY; LIFT_DROP];
    ALL_TAC] THEN
  REWRITE_TAC[CART_EQ] THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
  X_GEN_TAC `q:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
  MAP_EVERY EXISTS_TAC
   [`\s. (Gm:real^(1,N)finite_sum->real^N^N) (pastecart (lift s) z)$p$q`; `t:real`] THEN
  ASM_SIMP_TAC[]);;

(* The time derivative of the flow in a pair of charts.                     *)

let PDG_FLOW_TIME_DERIV = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (Y:real->A->real^N) J K s0 c c' s z.
        mfl_hyp top atlas Y J K /\ s0 IN J /\ c IN atlas /\ c' IN atlas /\
        pastecart s z IN {pastecart t y | t IN J /\ y IN IMAGE (SND c) (FST c) /\
                                         mfl_flow top atlas Y s0 t (chart_inv c y) IN FST c'}
        ==> frechet_derivative
              (\w. SND c' (mfl_flow top atlas Y s0 (fstcart w) (chart_inv c (sndcart w))))
              (at (pastecart s z)) (pastecart (lift(&1)) (vec 0)) =
            mfl_field atlas Y c'
              (pastecart s (SND c' (mfl_flow top atlas Y s0 s (chart_inv c z))))`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[IN_ELIM_PASTECART_THM] (last(CONJUNCTS th)))) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [mfl_hyp]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `Y:real->A->real^N`; `J:real^1->bool`; `K:A->bool`;
                 `c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`; `s0:real^1`]
                MFL_JOINT_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\w. SND (c':(A->bool)#(A->real^N))
           (mfl_flow top atlas (Y:real->A->real^N) s0 (fstcart w)
              (chart_inv (c:(A->bool)#(A->real^N)) (sndcart w))))
    differentiable at (pastecart s (z:real^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `{pastecart t y | t IN J /\ y IN IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c) /\
                   mfl_flow top atlas (Y:real->A->real^N) s0 t (chart_inv c y) IN
                   FST (c':(A->bool)#(A->real^N))}` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\w. SND (c':(A->bool)#(A->real^N))
           (mfl_flow top atlas (Y:real->A->real^N) s0 (fstcart w)
              (chart_inv (c:(A->bool)#(A->real^N)) (sndcart w)))`;
    `drop s`; `z:real^N`] LRG_TIME_CURVE_VDERIV) THEN
  ASM_REWRITE_TAC[LIFT_DROP; FSTCART_PASTECART; SNDCART_PASTECART] THEN DISCH_TAC THEN
  MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_AT THEN
  MAP_EVERY EXISTS_TAC
   [`\r. SND (c':(A->bool)#(A->real^N))
           (mfl_flow top atlas (Y:real->A->real^N) s0 r (chart_inv (c:(A->bool)#(A->real^N)) z))`;
    `s:real^1`] THEN
  ASM_REWRITE_TAC[MFL_FIELD_PASTECART] THEN
  MATCH_MP_TAC MFL_FLOW_DERIV THEN
  MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `K:A->bool`] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `z:real^N` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

(* The Ricci matrix of the target under the congruence by the Jacobian of a *)
(* local diffeomorphism is the Ricci form of the pullback.                  *)

let PDG_LRICCI_CONGR = prove
 (`!U U' (hm:real^N->real^N) hm' (G:real^N->real^N^N) y i j.
        metric_field U G /\ diffeomorphism_on U' U hm hm' /\ y IN U' /\
        1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
        ==> (transp(matrix(frechet_derivative hm (at y))) ** pde_lricci_matrix G (hm y) **
             matrix(frechet_derivative hm (at y)))$i$j =
            lricci (mpullback hm G) y (basis i) (basis j)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  SUBGOAL_THEN `linear(frechet_derivative (hm:real^N->real^N) (at y))` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U':real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(hm:real^N->real^N) y IN U` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[PDG_ENTRY_DOT; RFB_CONGRUENCE_DOT] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `hm:real^N->real^N`;
                 `hm':real^N->real^N`; `G:real^N->real^N^N`; `y:real^N`;
                 `basis i:real^N`; `basis j:real^N`] LRICCI_PULLBACK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC PDE_LRICCI_MATRIX_DOT THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

(* The value of the derivative: congruence of the Ricci matrix of the       *)
(* target chart representative is the Ricci form of the pulled-back metric. *)

let PDG_RF_VALUE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (Y:real->A->real^N) J K s0 t
    (gm:A->real^N^N) c0 c' x i j.
        mfl_hyp top atlas Y J K /\ s0 IN J /\ t IN J /\ riemannian_metric atlas gm /\
        c0 IN atlas /\ c' IN atlas /\ x IN FST c0 /\
        mfl_flow top atlas Y s0 t x IN FST c' /\
        1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
        ==> (transp(matrix(frechet_derivative
                     (SND c' o mfl_flow top atlas Y s0 t o chart_inv c0) (at (SND c0 x)))) **
             pde_lricci_matrix (metric_local atlas c' gm)
               ((SND c' o mfl_flow top atlas Y s0 t o chart_inv c0) (SND c0 x)) **
             matrix(frechet_derivative
                     (SND c' o mfl_flow top atlas Y s0 t o chart_inv c0) (at (SND c0 x))))$i$j =
            lricci (metric_local atlas c0
                      (mfd_pullback_metric atlas atlas (mfl_flow top atlas Y s0 t) gm))
                   (SND c0 x) (basis i) (basis j)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [mfl_hyp]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c0:(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c0:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c':(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `topspace top:A->bool`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `topspace top:A->bool`;
                 `mfl_flow top atlas (Y:real->A->real^N) s0 t`;
                 `mfl_flow top atlas (Y:real->A->real^N) t s0`;
                 `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                 `FST(c':(A->bool)#(A->real^N))`; `SND(c':(A->bool)#(A->real^N))`]
                MFDR_DIFFEO_CHART_REP) THEN
  ASM_REWRITE_TAC[PAIR] THEN ANTS_TAC THENL
   [MATCH_MP_TAC MFL_FLOW_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `K:A->bool`] THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  SUBGOAL_THEN
   `SND (c0:(A->bool)#(A->real^N)) (x:A) IN
    IMAGE (SND c0) {x | x IN FST c0 INTER topspace top /\
                        mfl_flow top atlas (Y:real->A->real^N) s0 t x IN
                        FST (c':(A->bool)#(A->real^N))}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER]; ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `lricci (mpullback (SND (c':(A->bool)#(A->real^N)) o
                       mfl_flow top atlas (Y:real->A->real^N) s0 t o
                       chart_inv (c0:(A->bool)#(A->real^N)))
                      (metric_local atlas c' (gm:A->real^N^N)))
           (SND c0 (x:A)) (basis i) (basis j)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PDG_LRICCI_CONGR THEN
    MAP_EVERY EXISTS_TAC
     [`IMAGE (SND (c':(A->bool)#(A->real^N)))
        {y | y IN FST c' INTER topspace top /\
             mfl_flow top atlas (Y:real->A->real^N) t s0 y IN FST (c0:(A->bool)#(A->real^N))}`;
      `IMAGE (SND (c0:(A->bool)#(A->real^N)))
        {x | x IN FST c0 INTER topspace top /\
             mfl_flow top atlas (Y:real->A->real^N) s0 t x IN FST (c':(A->bool)#(A->real^N))}`;
      `SND (c0:(A->bool)#(A->real^N)) o mfl_flow top atlas (Y:real->A->real^N) t s0 o
       chart_inv (c':(A->bool)#(A->real^N))`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFDR_METRIC_FIELD_LOCAL THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    EXISTS_TAC `IMAGE (SND (c':(A->bool)#(A->real^N))) (FST c')` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC
       `(z:real^N) IN IMAGE (SND (c':(A->bool)#(A->real^N)))
          {y | y IN FST c' INTER topspace top /\
               mfl_flow top atlas (Y:real->A->real^N) t s0 y IN FST (c0:(A->bool)#(A->real^N))}` THEN
      SET_TAC[];
      UNDISCH_TAC `riemannian_metric atlas (gm:A->real^N^N)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC LRICCI_LOCAL THEN
    EXISTS_TAC
     `IMAGE (SND (c0:(A->bool)#(A->real^N)))
        {x | x IN FST c0 INTER topspace top /\
             mfl_flow top atlas (Y:real->A->real^N) s0 t x IN FST (c':(A->bool)#(A->real^N))}` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
    X_GEN_TAC `x':A` THEN STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `Y:real->A->real^N`; `J:real^1->bool`; `K:A->bool`; `s0:real^1`; `t:real^1`;
                   `gm:A->real^N^N`; `c0:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`;
                   `SND (c0:(A->bool)#(A->real^N)) (x':A)`] PDG_FLOW_METRIC_LOCAL) THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE]]);;

(* The cancellation of the DeTurck terms: the time derivative of the chart  *)
(* family of gb plus the Lie derivative along the chart field of the        *)
(* negated DeTurck field is -2 Ric.                                          *)

let PDG_ADD_NEG_CANCEL = prove
 (`!A B:real^N^N. (A + B) + --B = A`,
  MATRIX_ARITH_TAC);;

let PDG_GAUGE_CANCEL = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) h a b gb (Y:real->A->real^N) c t z.
        riemannian_metric atlas h /\ pde_rdt_flow_from (top,atlas) h a b gb /\
        (!t x. a <= t /\ t < b /\ x IN topspace top
               ==> Y t x = --(pde_deturck atlas (gb t) h x)) /\
        c IN atlas /\ a < t /\ t < b /\ z IN IMAGE (SND c) (FST c) /\
        ((vectorize:real^N^N->real^(N,N)finite_prod) o
         (\w. metric_local atlas c (gb (drop(fstcart w))) (sndcart w)))
          differentiable at (pastecart (lift t) z)
        ==> (matrify:real^(N,N)finite_prod->real^N^N)
              (frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o
                 (\w. metric_local atlas c (gb (drop(fstcart w))) (sndcart w)))
                 (at (pastecart (lift t) z)) (pastecart (lift(&1)) (vec 0))) +
            llie (\z'. mfl_field atlas Y c (pastecart (lift t) z'))
                 (metric_local atlas c (gb t)) z =
            --(&2) %% pde_lricci_matrix (metric_local atlas c (gb t)) z`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pde_rdt_flow_from]) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((gb:real->A->real^N^N) t)` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))
                 (metric_local atlas c ((gb:real->A->real^N^N) t)) /\
    metric_field (IMAGE (SND c) (FST c)) (metric_local atlas c (h:A->real^N^N))`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(matrify:real^(N,N)finite_prod->real^N^N)
      (frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o
         (\w. metric_local atlas (c:(A->bool)#(A->real^N))
                ((gb:real->A->real^N^N) (drop(fstcart w))) (sndcart w)))
         (at (pastecart (lift t) z)) (pastecart (lift(&1)) (vec 0))) =
    pde_lrdt (metric_local atlas c (h:A->real^N^N)) (metric_local atlas c (gb t)) z`
  SUBST1_TAC THENL
   [MATCH_MP_TAC PDG_TIME_DERIV_MATRIX THEN
    ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC PDG_RDT_CHART_DERIV THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `llie (\z'. mfl_field atlas (Y:real->A->real^N) (c:(A->bool)#(A->real^N))
                 (pastecart (lift t) z'))
         (metric_local atlas c ((gb:real->A->real^N^N) t)) z =
    llie (\z'. --(pde_ldeturck (metric_local atlas c (h:A->real^N^N))
                               (metric_local atlas c (gb t)) z'))
         (metric_local atlas c (gb t)) z`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LLIE_LOCAL THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[MFL_FIELD_PASTECART; LIFT_DROP] THEN
    TRANS_TAC EQ_TRANS
     `mfd_vrep atlas (\x. --(pde_deturck atlas ((gb:real->A->real^N^N) t) h x))
               (c:(A->bool)#(A->real^N)) y` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[mfd_vrep] THEN AP_TERM_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `pde_deturck atlas ((gb:real->A->real^N^N) t) h`;
                   `c:(A->bool)#(A->real^N)`; `y:real^N`] PDG_VREP_NEG) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC PDG_DETURCK_VREP THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`pde_ldeturck (metric_local atlas (c:(A->bool)#(A->real^N)) (h:A->real^N^N))
                               (metric_local atlas c ((gb:real->A->real^N^N) t))`;
                 `metric_local atlas (c:(A->bool)#(A->real^N)) ((gb:real->A->real^N^N) t)`;
                 `z:real^N`] PDG_LLIE_NEG) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
    ASM_SIMP_TAC[PDE_LDETURCK_SMOOTH] THEN ASM_MESON_TAC[metric_field];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[pde_lrdt; ETA_AX; PDG_ADD_NEG_CANCEL]);;

(* ========================================================================= *)
(* The Ricci flow equation for the family                                    *)
(* pulled back along the flow of the negated DeTurck field.                  *)
(* ========================================================================= *)

let PDG_DERIV_TRANSFER = prove
 (`!f g f' g' x.
        (?d. &0 < d /\ !y. abs(y - x) < d ==> f y = g y) /\ f' = g'
        ==> (f has_real_derivative f') (atreal x)
        ==> (g has_real_derivative g') (atreal x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) SUBST1_TAC) THEN
  DISCH_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  MAP_EVERY EXISTS_TAC [`f:real->real`; `d:real`] THEN ASM_REWRITE_TAC[]);;

let PDG_GAUGE_RF_EQ = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) h a b gb (Y:real->A->real^N) e t x i j.
        riemannian_metric atlas h /\ pde_rdt_flow_from (top,atlas) h a b gb /\ &0 < e /\
        (!t x. a <= t /\ t < b /\ x IN topspace top
               ==> Y t x = --(pde_deturck atlas (gb t) h x)) /\
        mfl_hyp top atlas Y (interval(lift(a - e),lift b)) (topspace top) /\
        a < t /\ t < b /\ x IN topspace top /\
        1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
        ==> ((\s. mfd_pullback_metric atlas atlas (mfl_flow top atlas Y (lift a) (lift s))
                    (gb s) x$i$j) has_real_derivative
             (--(&2) * mfd_ricci_matrix atlas
                 (mfd_pullback_metric atlas atlas (mfl_flow top atlas Y (lift a) (lift t))
                    (gb t)) x$i$j)) (atreal t)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pde_rdt_flow_from]) THEN
  SUBGOAL_THEN `lift a IN interval(lift(a - e),lift b) /\
                lift t IN interval(lift(a - e),lift b)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c0 = chart_at atlas (x:A):(A->bool)#(A->real^N)` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c0:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c0:(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `x1 = mfl_flow top atlas (Y:real->A->real^N) (lift a) (lift t) (x:A)` THEN
  SUBGOAL_THEN `(x1:A) IN topspace top` ASSUME_TAC THENL
   [EXPAND_TAC "x1" THEN MATCH_MP_TAC MFL_FLOW_IN THEN
    MAP_EVERY EXISTS_TAC [`interval(lift(a - e),lift b)`; `topspace top:A->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x1:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c' = chart_at atlas (x1:A):(A->bool)#(A->real^N)` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c':(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `pde_tfam_from atlas a b (gb:real->A->real^N^N)` THEN
  REWRITE_TAC[pde_tfam_from] THEN DISCH_THEN(MP_TAC o SPEC `c':(A->bool)#(A->real^N)`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (X_CHOOSE_THEN
    `FG:real^(1,N)finite_sum->real^(N,N)finite_prod`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "FG"))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `Y:real->A->real^N`; `interval(lift(a - e),lift b)`;
                 `topspace top:A->bool`; `c0:(A->bool)#(A->real^N)`;
                 `c':(A->bool)#(A->real^N)`; `lift a`] MFL_JOINT_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `O1 = {pastecart r y | r IN interval(lift(a - e),lift b) /\
                          y IN IMAGE (SND (c0:(A->bool)#(A->real^N))) (FST c0) /\
                          mfl_flow top atlas (Y:real->A->real^N) (lift a) r (chart_inv c0 y) IN
                          FST (c':(A->bool)#(A->real^N))}` THEN
  ABBREV_TAC
   `Fm = \w:real^(1,N)finite_sum.
           SND (c':(A->bool)#(A->real^N))
             (mfl_flow top atlas (Y:real->A->real^N) (lift a) (fstcart w)
                (chart_inv (c0:(A->bool)#(A->real^N)) (sndcart w)))` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `pastecart (lift t) (SND (c0:(A->bool)#(A->real^N)) x) IN O1` ASSUME_TAC THENL
   [EXPAND_TAC "O1" THEN REWRITE_TAC[IN_ELIM_PASTECART_THM] THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  (* smoothness on the target slab *)
  SUBGOAL_THEN `open(interval(lift a,lift b) PCROSS
                     IMAGE (SND (c':(A->bool)#(A->real^N))) (FST c'))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (interval(lift a,lift b) PCROSS
                   IMAGE (SND (c':(A->bool)#(A->real^N))) (FST c'))
      ((vectorize:real^N^N->real^(N,N)finite_prod) o
       (\w. metric_local atlas c' ((gb:real->A->real^N^N) (drop(fstcart w))) (sndcart w)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `FG:real^(1,N)finite_sum->real^(N,N)finite_prod` THEN CONJ_TAC THENL
     [REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; o_THM;
                  FSTCART_PASTECART; SNDCART_PASTECART] THEN
      MAP_EVERY X_GEN_TAC [`r:real^1`; `y:real^N`] THEN STRIP_TAC THEN
      USE_THEN "FG" (MP_TAC o SPECL [`drop r`; `y:real^N`]) THEN
      REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `interval(lift(a - e1),lift b) PCROSS
                  IMAGE (SND (c':(A->bool)#(A->real^N))) (FST c')` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN
      REWRITE_TAC[SUBSET_REFL; SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN
      GEN_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (interval(lift a,lift b) PCROSS
                   IMAGE (SND (c':(A->bool)#(A->real^N))) (FST c'))
      (mfl_field atlas (Y:real->A->real^N) c')`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `interval(lift(a - e),lift b) PCROSS
                IMAGE (SND (c':(A->bool)#(A->real^N))) (FST c')` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PCROSS_MONO THEN
      REWRITE_TAC[SUBSET_REFL; SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN
      GEN_TAC THEN ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `Y:real->A->real^N`; `interval(lift(a - e),lift b)`;
                     `topspace top:A->bool`; `c':(A->bool)#(A->real^N)`] MFL_HYP_CHART) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  (* the derivative of the pullback in the chart pair *)
  MP_TAC(ISPECL
   [`(O1:real^(1,N)finite_sum->bool) INTER (interval(lift a,lift b) PCROSS (:real^N))`;
    `interval(lift a,lift b) PCROSS IMAGE (SND (c':(A->bool)#(A->real^N))) (FST c')`;
    `Fm:real^(1,N)finite_sum->real^N`;
    `mfl_field atlas (Y:real->A->real^N) (c':(A->bool)#(A->real^N))`;
    `\w:real^(1,N)finite_sum. metric_local atlas (c':(A->bool)#(A->real^N))
                                ((gb:real->A->real^N^N) (drop(fstcart w))) (sndcart w)`;
    `t:real`; `SND (c0:(A->bool)#(A->real^N)) x`; `i:num`; `j:num`]
   PDG_MPULLBACK_FLOW_DERIV) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[OPEN_INTER; OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV];
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `O1:real^(1,N)finite_sum->bool` THEN
      ASM_REWRITE_TAC[INTER_SUBSET];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_INTER; PASTECART_IN_PCROSS; IN_UNIV] THEN
      MAP_EVERY X_GEN_TAC [`r:real^1`; `z:real^N`] THEN
      EXPAND_TAC "O1" THEN REWRITE_TAC[IN_ELIM_PASTECART_THM] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "Fm" THEN
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
      REWRITE_TAC[IN_INTER; PASTECART_IN_PCROSS; IN_UNIV] THEN
      MAP_EVERY X_GEN_TAC [`r:real^1`; `z:real^N`] THEN STRIP_TAC THEN
      EXPAND_TAC "Fm" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
      MATCH_MP_TAC PDG_FLOW_TIME_DERIV THEN
      MAP_EVERY EXISTS_TAC [`interval(lift(a - e),lift b)`; `topspace top:A->bool`] THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[IN_INTER; PASTECART_IN_PCROSS; IN_UNIV; IN_INTERVAL_1; LIFT_DROP];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; ETA_AX]) THEN
  MATCH_MP_TAC PDG_DERIV_TRANSFER THEN CONJ_TAC THENL
   [(* near t the manifold family is the chart-pair pullback *)
    FIRST_ASSUM(MP_TAC o SPEC `pastecart (lift t) (SND (c0:(A->bool)#(A->real^N)) x)` o
      REWRITE_RULE[OPEN_CONTAINS_BALL] o
      check (fun th -> concl th = `open (O1:real^(1,N)finite_sum->bool)`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `pastecart (lift s) (SND (c0:(A->bool)#(A->real^N)) x) IN O1` MP_TAC THENL
     [UNDISCH_TAC `ball(pastecart (lift t) (SND (c0:(A->bool)#(A->real^N)) x),r) SUBSET O1` THEN
      REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[DIST_PASTECART_CANCEL; DIST_LIFT] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "O1" THEN REWRITE_TAC[IN_ELIM_PASTECART_THM] THEN STRIP_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN
     `(\z:real^N. (Fm:real^(1,N)finite_sum->real^N) (pastecart (lift s) z)) =
      SND (c':(A->bool)#(A->real^N)) o mfl_flow top atlas (Y:real->A->real^N) (lift a) (lift s) o
      chart_inv (c0:(A->bool)#(A->real^N))`
    SUBST1_TAC THENL
     [EXPAND_TAC "Fm" THEN REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `Y:real->A->real^N`; `interval(lift(a - e),lift b)`;
                   `topspace top:A->bool`; `lift a`; `lift s`; `(gb:real->A->real^N^N) s`;
                   `c0:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`;
                   `SND (c0:(A->bool)#(A->real^N)) x`] PDG_FLOW_METRIC_LOCAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    EXPAND_TAC "c0" THEN MATCH_MP_TAC METRIC_LOCAL_AT THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    (* the value of the derivative *)
    SUBGOAL_THEN
     `(\z:real^N. (Fm:real^(1,N)finite_sum->real^N) (pastecart (lift t) z)) =
      SND (c':(A->bool)#(A->real^N)) o mfl_flow top atlas (Y:real->A->real^N) (lift a) (lift t) o
      chart_inv (c0:(A->bool)#(A->real^N))`
    SUBST1_TAC THENL
     [EXPAND_TAC "Fm" THEN REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(SND (c':(A->bool)#(A->real^N)) o mfl_flow top atlas (Y:real->A->real^N) (lift a) (lift t) o
       chart_inv (c0:(A->bool)#(A->real^N))) (SND c0 x) = SND c' (x1:A)`
    (LABEL_TAC "hy0") THENL
     [REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[mpullback] THEN USE_THEN "hy0" (fun th -> REWRITE_TAC[th]) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `h:A->real^N^N`;
                   `a:real`; `b:real`; `gb:real->A->real^N^N`; `Y:real->A->real^N`;
                   `c':(A->bool)#(A->real^N)`; `t:real`;
                   `SND (c':(A->bool)#(A->real^N)) (x1:A)`] PDG_GAUGE_CANCEL) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FUN_IN_IMAGE] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `interval(lift a,lift b) PCROSS
                  IMAGE (SND (c':(A->bool)#(A->real^N))) (FST c')` THEN
      ASM_SIMP_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; FUN_IN_IMAGE];
      DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
    REWRITE_TAC[MATRIX_MUL_LMUL; MATRIX_MUL_RMUL; MATRIX_CMUL_COMPONENT] THEN
    AP_TERM_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `Y:real->A->real^N`; `interval(lift(a - e),lift b)`;
                   `topspace top:A->bool`; `lift a`; `lift t`; `(gb:real->A->real^N^N) t`;
                   `c0:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`; `x:A`;
                   `i:num`; `j:num`] PDG_RF_VALUE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE];
      USE_THEN "hy0" (fun th -> REWRITE_TAC[th]) THEN DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[mfd_ricci_matrix; mfd_ricci] THEN ASM_SIMP_TAC[LAMBDA_BETA]]);;

(* ========================================================================= *)
(* The DeTurck gauge (PDE_GAUGE): a Ricci-DeTurck flow with background h     *)
(* becomes a Ricci flow after pulling back by the flow phi of the negated    *)
(* DeTurck field (the sign of CLN (2.52)), started at phi a = id; the field  *)
(* is first extended smoothly below a.                                       *)
(* ========================================================================= *)

let PDE_GAUGE = prove
 (`!(u:A->bool) (n:N->bool). PDE_GAUGE_STATEMENT u n`,
  REWRITE_TAC[PDE_GAUGE_STATEMENT] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pde_rdt_flow_from]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `\t x. --(pde_deturck atlas ((gb:real->A->real^N^N) t) (h:A->real^N^N) x)`;
                 `a:real`; `b:real`] PDG_FIELD_EXTEND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    MATCH_MP_TAC PDG_NEG_DETURCK_UPTO THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real`
      (X_CHOOSE_THEN `Y:real->A->real^N` STRIP_ASSUME_TAC))] THEN
  SUBGOAL_THEN `lift a IN interval(lift(a - e),lift b)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!t. a <= t /\ t < b ==> lift t IN interval(lift(a - e),lift b)`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. a <= t /\ t < b
        ==> mfd_diffeo top atlas (topspace top) top atlas (topspace top)
              (mfl_flow top atlas (Y:real->A->real^N) (lift a) (lift t))
              (mfl_flow top atlas Y (lift t) (lift a))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFL_FLOW_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`interval(lift(a - e),lift b)`; `topspace top:A->bool`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN topspace top
        ==> mfl_flow top atlas (Y:real->A->real^N) (lift a) (lift a) x = x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFL_FLOW_REFL THEN
    MAP_EVERY EXISTS_TAC [`interval(lift(a - e),lift b)`; `topspace top:A->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. a <= t /\ t < b
        ==> riemannian_metric atlas
              (mfd_pullback_metric atlas atlas
                 (mfl_flow top atlas (Y:real->A->real^N) (lift a) (lift t))
                 ((gb:real->A->real^N^N) t))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RIEMANNIAN_METRIC_PULLBACK THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `top:A topology`;
      `mfl_flow top atlas (Y:real->A->real^N) (lift t) (lift a)`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `\t. mfl_flow top atlas (Y:real->A->real^N) (lift a) (lift t)` THEN
  EXISTS_TAC
   `\t. mfd_pullback_metric atlas atlas
          (mfl_flow top atlas (Y:real->A->real^N) (lift a) (lift t))
          ((gb:real->A->real^N^N) t)` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    EXISTS_TAC `mfl_flow top atlas (Y:real->A->real^N) (lift t) (lift a)` THEN
    ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC PDG_PULLBACK_ID THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[ricci_flow_from; ricci_flow_on] THEN
  SUBGOAL_THEN
   `pde_tfam_from atlas a b
      (\t. mfd_pullback_metric atlas atlas
             (mfl_flow top atlas (Y:real->A->real^N) (lift a) (lift t))
             ((gb:real->A->real^N^N) t))`
  MP_TAC THENL
   [MATCH_MP_TAC PDG_GAUGE_TFAM THEN EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[pde_tfam_from] THEN DISCH_THEN(LABEL_TAC "tf") THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE];
    X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    USE_THEN "tf" (fun th -> MP_TAC(MP (SPEC `c:(A->bool)#(A->real^N)` th)
                                        (ASSUME `(c:(A->bool)#(A->real^N)) IN atlas`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `e1:real` (X_CHOOSE_THEN
      `FF:real^(1,N)finite_sum->real^(N,N)finite_prod`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "FF"))))) THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `FF:real^(1,N)finite_sum->real^(N,N)finite_prod` THEN CONJ_TAC THENL
     [REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP;
                  FSTCART_PASTECART; SNDCART_PASTECART] THEN
      MAP_EVERY X_GEN_TAC [`r:real^1`; `y:real^N`] THEN STRIP_TAC THEN
      USE_THEN "FF" (MP_TAC o SPECL [`drop r`; `y:real^N`]) THEN
      REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `interval(lift(a - e1),lift b) PCROSS
                  IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN
      REWRITE_TAC[SUBSET_REFL; SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN
      GEN_TAC THEN ASM_REAL_ARITH_TAC];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC PDG_GAUGE_RF_EQ THEN
    MAP_EVERY EXISTS_TAC [`h:A->real^N^N`; `b:real`; `e:real`] THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[REAL_LE_REFL]]);;

(* The implication from the manifold flow statement PDE_REQ_MFLOW_STATEMENT  *)
(* to PDE_GAUGE_STATEMENT, which holds outright by PDE_GAUGE (the manifold   *)
(* flow is built in pc_mfd_flow).                                            *)

let PDE_GAUGE_FROM_MFLOW = prove
 (`!(u:A->bool) (n:N->bool). PDE_REQ_MFLOW_STATEMENT u n ==> PDE_GAUGE_STATEMENT u n`,
  REWRITE_TAC[PDE_GAUGE]);;

