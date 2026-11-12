(* ========================================================================= *)
(* Unit pc_rf_glue: gluing Ricci flows in time (MT Prop 3.12,                *)
(* PDE_GLUE_STATEMENT of pc_pde_iface).  Time derivatives of a Ricci flow    *)
(* are differential polynomials in the spatial jets of the chart matrices    *)
(* (syntax pde_jpoly below); if the spatial jets of a flow on (a,b) converge *)
(* as t -> b- to those of a flow from b, all space-time partials match at    *)
(* t = b and the concatenation is smooth.                                    *)
(*                                                                           *)
(* First: a Ricci flow is a local Ricci flow in every chart.                 *)
(* ========================================================================= *)

needs "src/pc_pde_iface.ml";;
needs "src/pc_lrg_evol.ml";;
needs "src/pc_pde_seeley.ml";;
needs "src/pc_rf_extend.ml";;
needs "src/pc_pde_st.ml";;
needs "src/pc_lrg_flowsmooth.ml";;

prioritize_real();;
type_invention_error := true;;

let PDE_CONGR_ENTRY = prove
 (`!(J:real^N^N) (M:real^N^N) i j.
        1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
        ==> (transp J ** M ** J)$i$j =
            sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q. J$p$i * M$p$q * J$q$j))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[matrix_mul; LAMBDA_BETA; TRANSP_COMPONENT] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN REWRITE_TAC[GSYM SUM_LMUL; REAL_MUL_ASSOC]);;

(* A Ricci flow on a manifold is a local Ricci flow in every chart; this is *)
(* LRG_RICCI_FLOW_ON_CHART of the shared unit pc_lrg_flowsmooth.            *)

let PDE_RF_CHART_LOCAL = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b
    (g:real->A->real^N^N) c.
        ricci_flow_on (top,atlas) a b g /\ c IN atlas
        ==> lricci_flow (IMAGE (SND c) (FST c)) a b (\t. metric_local atlas c (g t))`,
  REWRITE_TAC[LRG_RICCI_FLOW_ON_CHART]);;

(* ========================================================================= *)
(* Differential polynomials in the entries of a matrix field (the entries of *)
(* its iterated spatial partials and of its inverse), their evaluation, the  *)
(* formal spatial derivative jp_dx, and the rule                             *)
(* partial_derivative k (jp_eval e G) = jp_eval (jp_dx n k e) G for smooth   *)
(* invertible matrix fields.                                                 *)
(* ========================================================================= *)

let pde_jpoly_INDUCT,pde_jpoly_RECURSION = define_type
 "pde_jpoly = JPconst real
            | JPvar (num list) num num
            | JPinv num num
            | JPadd pde_jpoly pde_jpoly
            | JPmul pde_jpoly pde_jpoly";;

let jp_eval = new_recursive_definition pde_jpoly_RECURSION
 `(!c G y. jp_eval (JPconst c) (G:real^N->real^N^N) (y:real^N) = c) /\
  (!l i j G y. jp_eval (JPvar l i j) (G:real^N->real^N^N) (y:real^N) =
     ((matrify:real^(N,N)finite_prod->real^N^N)
        (iterated_partial l ((vectorize:real^N^N->real^(N,N)finite_prod) o G) y))$i$j) /\
  (!i j G y. jp_eval (JPinv i j) (G:real^N->real^N^N) (y:real^N) = matrix_inv(G y)$i$j) /\
  (!e1 e2 G y. jp_eval (JPadd e1 e2) (G:real^N->real^N^N) (y:real^N) =
     jp_eval e1 G y + jp_eval e2 G y) /\
  (!e1 e2 G y. jp_eval (JPmul e1 e2) (G:real^N->real^N^N) (y:real^N) =
     jp_eval e1 G y * jp_eval e2 G y)`;;

let jp_sum = define
 `(!f:num->pde_jpoly. jp_sum 0 f = JPconst(&0)) /\
  (!m (f:num->pde_jpoly). jp_sum (SUC m) f = JPadd (jp_sum m f) (f (SUC m)))`;;

let JP_EVAL_SUM = prove
 (`!m (f:num->pde_jpoly) (G:real^N->real^N^N) y.
        jp_eval (jp_sum m f) G y = sum(1..m) (\p. jp_eval (f p) G y)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[jp_sum; jp_eval; SUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[ARITH_RULE `1 <= SUC m`; ARITH_RULE `~(1 = 0)`]);;

let jp_dx = new_recursive_definition pde_jpoly_RECURSION
 `(!n k c. jp_dx n k (JPconst c) = JPconst(&0)) /\
  (!n k l i j. jp_dx n k (JPvar l i j) = JPvar (CONS k l) i j) /\
  (!n k i j. jp_dx n k (JPinv i j) =
     JPmul (JPconst(--(&1)))
           (jp_sum n (\p. jp_sum n (\q. JPmul (JPinv i p)
                                              (JPmul (JPvar [k] p q) (JPinv q j)))))) /\
  (!n k e1 e2. jp_dx n k (JPadd e1 e2) = JPadd (jp_dx n k e1) (jp_dx n k e2)) /\
  (!n k e1 e2. jp_dx n k (JPmul e1 e2) =
     JPadd (JPmul (jp_dx n k e1) e2) (JPmul e1 (jp_dx n k e2)))`;;

(* Linear maps commute with partial derivatives. *)

let PDE_PARTIAL_LINEAR_COMPOSE = prove
 (`!(L:real^N->real^P) (f:real^M->real^N) i x.
        linear L /\ f differentiable (at x)
        ==> partial_derivative i (\z. L(f z)) x = L(partial_derivative i f x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z. (L:real^N->real^P)((f:real^M->real^N) z)) = L o f` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`i:num`; `f:real^M->real^N`; `L:real^N->real^P`; `x:real^M`]
                PARTIAL_DERIVATIVE_CHAIN) THEN
  ASM_SIMP_TAC[DIFFERENTIABLE_LINEAR] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`L:real^N->real^P`; `L:real^N->real^P`; `(f:real^M->real^N) x`]
                FRECHET_DERIVATIVE_AT) THEN
  ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC);;

(* The derivative rule.  For a smooth invertible matrix field G on an open   *)
(* set U every evaluation is smooth on U and its k-th partial is the         *)
(* evaluation of jp_dx (jp_good), proved constructor by constructor.         *)

let jp_good = new_definition
 `jp_good (U:real^N->bool) (G:real^N->real^N^N) e <=>
    smooth_map_on U (\z. lift(jp_eval e G z)) /\
    !k y. y IN U /\ 1 <= k /\ k <= dimindex(:N)
          ==> partial_derivative k (\z. lift(jp_eval e G z)) y =
              lift(jp_eval (jp_dx (dimindex(:N)) k e) G y)`;;

let JP_GOOD_CONST = prove
 (`!U (G:real^N->real^N^N) c. jp_good U G (JPconst c)`,
  REWRITE_TAC[jp_good; jp_eval; jp_dx; SMOOTH_MAP_ON_CONST; PARTIAL_DERIVATIVE_CONST;
              LIFT_NUM]);;

let JP_GOOD_VAR = prove
 (`!U (G:real^N->real^N^N) l i j.
        open U /\ smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o G)
        ==> jp_good U G (JPvar l i j)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[jp_good; jp_eval; jp_dx] THEN
  SUBGOAL_THEN
   `smooth_map_on U (iterated_partial l
                      ((vectorize:real^N^N->real^(N,N)finite_prod) o (G:real^N->real^N^N)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_ITERATED_PARTIAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `(\z. lift((matrify:real^(N,N)finite_prod->real^N^N)
                  (iterated_partial l ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                       (G:real^N->real^N^N)) z)$i$j)) =
      (\x. lift((matrify x:real^N^N)$i$j)) o
      iterated_partial l ((vectorize:real^N^N->real^(N,N)finite_prod) o G)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
    ASM_REWRITE_TAC[LRG_LINEAR_MATRIFY_ENTRY];
    MAP_EVERY X_GEN_TAC [`k:num`; `y:real^N`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\x:real^(N,N)finite_prod. lift((matrify x:real^N^N)$i$j)`;
                   `iterated_partial l ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                        (G:real^N->real^N^N))`;
                   `k:num`; `y:real^N`] PDE_PARTIAL_LINEAR_COMPOSE) THEN
    REWRITE_TAC[LRG_LINEAR_MATRIFY_ENTRY] THEN ANTS_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[iterated_partial]]]);;

let PDE_MATRIX_TRIPLE_ENTRY = prove
 (`!(A:real^N^N) (B:real^N^N) (C:real^N^N) i j.
        (A ** B ** C)$i$j =
        sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q. A$i$p * B$p$q * C$q$j))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:N) /\ !x:(real^N)^N. x$i = x$k`
  STRIP_ASSUME_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  SUBGOAL_THEN `?k'. 1 <= k' /\ k' <= dimindex(:N) /\ !z:real^N. z$j = z$k'`
  STRIP_ASSUME_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[matrix_mul; LAMBDA_BETA] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN REWRITE_TAC[GSYM SUM_LMUL; REAL_MUL_ASSOC]);;

let JP_GOOD_INV = prove
 (`!U (G:real^N->real^N^N) i j.
        open U /\ smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o G) /\
        (!z. z IN U ==> invertible(G z))
        ==> jp_good U G (JPinv i j)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[jp_good; jp_eval; jp_dx] THEN
  SUBGOAL_THEN `!z. z IN U ==> ~(det((G:real^N->real^N^N) z) = &0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[INVERTIBLE_DET_NZ]; ALL_TAC] THEN
  ABBREV_TAC `W = (vectorize:real^N^N->real^(N,N)finite_prod) o
                  (\z. matrix_inv((G:real^N->real^N^N) z))` THEN
  SUBGOAL_THEN
   `(\z. lift(matrix_inv((G:real^N->real^N^N) z)$i$j)) =
    (\z. (\x:real^(N,N)finite_prod. lift((matrify x:real^N^N)$i$j)) (W z))`
  SUBST1_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[FUN_EQ_THM; o_THM; MATRIFY_VECTORIZE]; ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `(\z. (\x:real^(N,N)finite_prod. lift((matrify x:real^N^N)$i$j)) (W z)) =
      (\x:real^(N,N)finite_prod. lift((matrify x:real^N^N)$i$j)) o
      (W:real^N->real^(N,N)finite_prod)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
    EXPAND_TAC "W" THEN ASM_SIMP_TAC[LRG_LINEAR_MATRIFY_ENTRY; LRG_SMOOTH_MATRIX_INV];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `y:real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:real^N->real^N^N`; `U:real^N->bool`; `y:real^N`]
                LRG_HAS_DERIVATIVE_MATRIX_INV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\x:real^(N,N)finite_prod. lift((matrify x:real^N^N)$i$j)`;
                 `W:real^N->real^(N,N)finite_prod`; `k:num`; `y:real^N`]
                PDE_PARTIAL_LINEAR_COMPOSE) THEN
  REWRITE_TAC[LRG_LINEAR_MATRIFY_ENTRY] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[differentiable]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[partial_derivative] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[MATRIFY_VECTORIZE; MATRIX_NEG_COMPONENT; PDE_MATRIX_TRIPLE_ENTRY] THEN
  REWRITE_TAC[JP_EVAL_SUM; jp_eval; iterated_partial; partial_derivative] THEN
  AP_TERM_TAC THEN REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_LID] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_MUL_ASSOC]);;

let JP_GOOD_ADD = prove
 (`!U (G:real^N->real^N^N) e1 e2.
        open U /\ jp_good U G e1 /\ jp_good U G e2 ==> jp_good U G (JPadd e1 e2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[jp_good; jp_eval; jp_dx; LIFT_ADD] THEN STRIP_TAC THEN
  CONJ_TAC THENL [MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) PARTIAL_DERIVATIVE_ADD (lhand w))) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[]]);;

let JP_GOOD_MUL = prove
 (`!U (G:real^N->real^N^N) e1 e2.
        open U /\ jp_good U G e1 /\ jp_good U G e2 ==> jp_good U G (JPmul e1 e2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[jp_good; jp_eval; jp_dx] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!e. (\z. lift(jp_eval e1 (G:real^N->real^N^N) z * jp_eval e G z)) =
        (\z. drop(lift(jp_eval e1 G z)) % lift(jp_eval e G z))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM; LIFT_DROP; LIFT_CMUL]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `\z. lift(jp_eval e1 (G:real^N->real^N^N) z)`;
                 `\z. lift(jp_eval e2 (G:real^N->real^N^N) z)`; `y:real^N`]
                PARTIAL_DERIVATIVE_MUL) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[LIFT_DROP; jp_eval; LIFT_ADD; LIFT_CMUL] THEN VECTOR_ARITH_TAC);;

let JP_DX = prove
 (`!U (G:real^N->real^N^N).
        open U /\ smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o G) /\
        (!z. z IN U ==> invertible(G z))
        ==> !e. jp_good U G e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC pde_jpoly_INDUCT THEN
  ASM_SIMP_TAC[JP_GOOD_CONST; JP_GOOD_VAR; JP_GOOD_INV; JP_GOOD_ADD; JP_GOOD_MUL]);;

(* ========================================================================= *)
(* Christoffel symbols and the Ricci form of a metric field as differential  *)
(* polynomials (JP_CHR, JP_RIC).                                             *)
(* ========================================================================= *)

let jp_neg = new_definition
 `jp_neg e = JPmul (JPconst(--(&1))) e`;;

let JP_EVAL_NEG = prove
 (`!e (G:real^N->real^N^N) y. jp_eval (jp_neg e) G y = --(jp_eval e G y)`,
  REWRITE_TAC[jp_neg; jp_eval] THEN REAL_ARITH_TAC);;

(* The k-th component of Gamma(e_a, e_b). *)

let jp_chr = new_definition
 `jp_chr n m a b =
    jp_sum n (\k. JPmul (JPinv m k)
                        (JPmul (JPconst(inv(&2)))
                               (JPadd (JPadd (JPvar [a] k b) (JPvar [b] k a))
                                      (jp_neg (JPvar [k] a b)))))`;;

let PDE_MDERIV_BASIS_ENTRY = prove
 (`!(G:real^N->real^N^N) y a p q.
        mderiv G y (basis a) $p$q =
        jp_eval (JPvar [a] p q) G y`,
  REWRITE_TAC[mderiv; jp_eval; iterated_partial; partial_derivative]);;

let JP_CHR = prove
 (`!(G:real^N->real^N^N) y m a b.
        1 <= m /\ m <= dimindex(:N) /\ 1 <= a /\ a <= dimindex(:N) /\
        1 <= b /\ b <= dimindex(:N)
        ==> christoffel G y (basis a) (basis b) $m =
            jp_eval (jp_chr (dimindex(:N)) m a b) G y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[christoffel; jp_chr; JP_EVAL_SUM] THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT] THEN GEN_REWRITE_TAC LAND_CONV [dot] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LAMBDA_BETA; jp_eval; JP_EVAL_NEG; MATRIX_VECTOR_MUL_BASIS; column;
               DOT_BASIS] THEN
  REWRITE_TAC[PDE_MDERIV_BASIS_ENTRY; jp_eval] THEN REAL_ARITH_TAC);;

let JP_METRIC_FIELD_GOOD = prove
 (`!U (G:real^N->real^N^N).
        metric_field U G ==> !e. jp_good U G e`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC JP_DX THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [metric_field]) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]);;

let JP_DCHR = prove
 (`!U (G:real^N->real^N^N) y m a b c.
        metric_field U G /\ y IN U /\
        1 <= m /\ m <= dimindex(:N) /\ 1 <= a /\ a <= dimindex(:N) /\
        1 <= b /\ b <= dimindex(:N) /\ 1 <= c /\ c <= dimindex(:N)
        ==> frechet_derivative (\z. christoffel G z (basis a) (basis b)) (at y) (basis c)$m =
            jp_eval (jp_dx (dimindex(:N)) c (jp_chr (dimindex(:N)) m a b)) G y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:num`; `m:num`; `\z. christoffel (G:real^N->real^N^N) z (basis a) (basis b)`;
                 `y:real^N`] PARTIAL_DERIVATIVE_COMPONENT) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC LRG_CHRISTOFFEL_DIFF THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `drop`) THEN
  REWRITE_TAC[LIFT_DROP; partial_derivative] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[JP_CHR] THEN REWRITE_TAC[GSYM partial_derivative] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] JP_METRIC_FIELD_GOOD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `jp_chr (dimindex(:N)) m a b`) THEN
  REWRITE_TAC[jp_good] THEN
  DISCH_THEN(MP_TAC o SPECL [`c:num`; `y:real^N`] o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LIFT_DROP]);;

let JP_CHR_CHR = prove
 (`!U (G:real^N->real^N^N) y m a b c.
        metric_field U G /\ y IN U /\
        1 <= m /\ m <= dimindex(:N) /\ 1 <= a /\ a <= dimindex(:N) /\
        1 <= b /\ b <= dimindex(:N) /\ 1 <= c /\ c <= dimindex(:N)
        ==> christoffel G y (basis c) (christoffel G y (basis a) (basis b))$m =
            sum(1..dimindex(:N))
               (\p. jp_eval (jp_chr (dimindex(:N)) p a b) G y *
                    jp_eval (jp_chr (dimindex(:N)) m c p) G y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
                LRG_CHRISTOFFEL_LINEAR) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `basis c:real^N` o CONJUNCT1) THEN DISCH_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
  ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL] THEN
  ASM_SIMP_TAC[VSUM_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[JP_CHR]);;

let jp_ric = new_definition
 `jp_ric n a b =
    jp_sum n (\c. JPadd (JPadd (jp_dx n c (jp_chr n c a b))
                               (jp_neg (jp_dx n a (jp_chr n c c b))))
                        (JPadd (jp_sum n (\p. JPmul (jp_chr n p a b) (jp_chr n c c p)))
                               (jp_neg (jp_sum n (\p. JPmul (jp_chr n p c b)
                                                            (jp_chr n c a p))))))`;;

let JP_RIC = prove
 (`!U (G:real^N->real^N^N) y a b.
        metric_field U G /\ y IN U /\
        1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
        ==> lricci G y (basis a) (basis b) = jp_eval (jp_ric (dimindex(:N)) a b) G y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lricci; jp_ric; JP_EVAL_SUM] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  ASM_SIMP_TAC[lriemann; VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT; jp_eval; JP_EVAL_NEG;
               JP_EVAL_SUM] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `c:num`; `a:num`;
                 `b:num`; `c:num`] JP_DCHR) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `c:num`; `c:num`;
                 `b:num`; `a:num`] JP_DCHR) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `c:num`; `a:num`;
                 `b:num`; `c:num`] JP_CHR_CHR) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `c:num`; `c:num`;
                 `b:num`; `a:num`] JP_CHR_CHR) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN REWRITE_TAC[jp_eval] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Space-time calculus, time first: the lemmas PDE_ST_BASIS_SPACE,           *)
(* PDE_ST_BASIS_TIME, PDE_ST_SLICE_PARTIAL, PDE_ST_TIME_DERIV,               *)
(* PDE_ST_TIME_REAL_DERIV, PDE_ST_SLICE_OPEN and PDE_ST_SLICE_ITERATED are   *)
(* in the shared unit pc_pde_st, loaded at the start.                        *)
(* ========================================================================= *)

(* ========================================================================= *)
(* The formal time derivative jp_dt along a local Ricci flow                 *)
(* (d/dt G = -2 Ric(G) = jp_rhs), validity of polynomials, iterated spatial  *)
(* derivatives (jp_dxl), and the time-derivative rule JP_DT.                 *)
(* ========================================================================= *)

let jp_dxl = define
 `(!n e. jp_dxl n [] e = e) /\
  (!n k l e. jp_dxl n (CONS k l) e = jp_dx n k (jp_dxl n l e))`;;

let jp_rhs = new_definition
 `jp_rhs n i j = JPmul (JPconst(--(&2))) (jp_ric n i j)`;;

let jp_dt = new_recursive_definition pde_jpoly_RECURSION
 `(!n c. jp_dt n (JPconst c) = JPconst(&0)) /\
  (!n l i j. jp_dt n (JPvar l i j) = jp_dxl n l (jp_rhs n i j)) /\
  (!n i j. jp_dt n (JPinv i j) =
     jp_neg (jp_sum n (\p. jp_sum n (\q. JPmul (JPinv i p)
                                              (JPmul (jp_rhs n p q) (JPinv q j)))))) /\
  (!n e1 e2. jp_dt n (JPadd e1 e2) = JPadd (jp_dt n e1) (jp_dt n e2)) /\
  (!n e1 e2. jp_dt n (JPmul e1 e2) =
     JPadd (JPmul (jp_dt n e1) e2) (JPmul e1 (jp_dt n e2)))`;;

let jp_valid = new_recursive_definition pde_jpoly_RECURSION
 `(!n c. jp_valid n (JPconst c) <=> T) /\
  (!n l i j. jp_valid n (JPvar l i j) <=>
             ALL (\k. 1 <= k /\ k <= n) l /\ 1 <= i /\ i <= n /\ 1 <= j /\ j <= n) /\
  (!n i j. jp_valid n (JPinv i j) <=> 1 <= i /\ i <= n /\ 1 <= j /\ j <= n) /\
  (!n e1 e2. jp_valid n (JPadd e1 e2) <=> jp_valid n e1 /\ jp_valid n e2) /\
  (!n e1 e2. jp_valid n (JPmul e1 e2) <=> jp_valid n e1 /\ jp_valid n e2)`;;

(* Linear maps commute with iterated partials of smooth maps. *)

let PDE_ITERATED_PARTIAL_LINEAR_COMPOSE = prove
 (`!l (L:real^N->real^P) (w:real^M->real^N) s x.
        linear L /\ open s /\ smooth_map_on s w /\ x IN s
        ==> iterated_partial l (\z. L(w z)) x = L(iterated_partial l w x)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[iterated_partial] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `partial_derivative h (\z. (L:real^N->real^P)
                                         (iterated_partial t (w:real^M->real^N) z)) x` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN EXISTS_TAC `s:real^M->bool` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC PDE_PARTIAL_LINEAR_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^M->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL]]);;

(* Iterated spatial partials of evaluations. *)

let JP_DXL = prove
 (`!l U (G:real^N->real^N^N) e y.
        metric_field U G /\ y IN U /\ ALL (\k. 1 <= k /\ k <= dimindex(:N)) l
        ==> iterated_partial l (\z. lift(jp_eval e G z)) y =
            lift(jp_eval (jp_dxl (dimindex(:N)) l e) G y)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[iterated_partial; jp_dxl; ALL] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [metric_field]) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `partial_derivative h
                (\z. lift(jp_eval (jp_dxl (dimindex(:N)) t e) (G:real^N->real^N^N) z)) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] JP_METRIC_FIELD_GOOD) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `jp_dxl (dimindex(:N)) t e`) THEN REWRITE_TAC[jp_good] THEN
    DISCH_THEN(MP_TAC o SPECL [`h:num`; `y:real^N`] o CONJUNCT2) THEN
    ASM_REWRITE_TAC[]]);;

(* Validity is preserved by the formal operations. *)

let JP_VALID_SUM = prove
 (`!n m (f:num->pde_jpoly).
        (!p. 1 <= p /\ p <= m ==> jp_valid n (f p)) ==> jp_valid n (jp_sum m f)`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[jp_sum; jp_valid] THEN
  REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC]);;

let JP_VALID_NEG = prove
 (`!n e. jp_valid n (jp_neg e) <=> jp_valid n e`,
  REWRITE_TAC[jp_neg; jp_valid]);;

let JP_VALID_DX_LEMMA = prove
 (`!n k. 1 <= k /\ k <= n ==> !e. jp_valid n e ==> jp_valid n (jp_dx n k e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC pde_jpoly_INDUCT THEN REWRITE_TAC[jp_dx; jp_valid; ALL] THEN
  ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC JP_VALID_SUM THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC JP_VALID_SUM THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[jp_valid; ALL]);;

let JP_VALID_DX = prove
 (`!n k e. 1 <= k /\ k <= n /\ jp_valid n e ==> jp_valid n (jp_dx n k e)`,
  MESON_TAC[JP_VALID_DX_LEMMA]);;

let JP_VALID_DXL = prove
 (`!n l e. ALL (\k. 1 <= k /\ k <= n) l /\ jp_valid n e ==> jp_valid n (jp_dxl n l e)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[jp_dxl; ALL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC JP_VALID_DX THEN ASM_SIMP_TAC[]);;

let JP_VALID_CHR = prove
 (`!n m a b. 1 <= m /\ m <= n /\ 1 <= a /\ a <= n /\ 1 <= b /\ b <= n
             ==> jp_valid n (jp_chr n m a b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[jp_chr] THEN MATCH_MP_TAC JP_VALID_SUM THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[jp_valid; JP_VALID_NEG; ALL]);;

let JP_VALID_RIC = prove
 (`!n a b. 1 <= a /\ a <= n /\ 1 <= b /\ b <= n ==> jp_valid n (jp_ric n a b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[jp_ric] THEN MATCH_MP_TAC JP_VALID_SUM THEN
  X_GEN_TAC `c:num` THEN STRIP_TAC THEN REWRITE_TAC[jp_valid; JP_VALID_NEG] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC JP_VALID_DX THEN ASM_SIMP_TAC[JP_VALID_CHR];
    MATCH_MP_TAC JP_VALID_DX THEN ASM_SIMP_TAC[JP_VALID_CHR];
    MATCH_MP_TAC JP_VALID_SUM THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[jp_valid; JP_VALID_CHR];
    MATCH_MP_TAC JP_VALID_SUM THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[jp_valid; JP_VALID_CHR]]);;

let JP_VALID_RHS = prove
 (`!n i j. 1 <= i /\ i <= n /\ 1 <= j /\ j <= n ==> jp_valid n (jp_rhs n i j)`,
  SIMP_TAC[jp_rhs; jp_valid; JP_VALID_RIC]);;

let JP_VALID_DT = prove
 (`!n e. jp_valid n e ==> jp_valid n (jp_dt n e)`,
  GEN_TAC THEN MATCH_MP_TAC pde_jpoly_INDUCT THEN REWRITE_TAC[jp_dt; jp_valid] THEN
  SIMP_TAC[] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC JP_VALID_DXL THEN ASM_SIMP_TAC[JP_VALID_RHS];
    REWRITE_TAC[JP_VALID_NEG] THEN MATCH_MP_TAC JP_VALID_SUM THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC JP_VALID_SUM THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[jp_valid; JP_VALID_RHS]]);;

(* The time partial of the space-time chart matrix of a local Ricci flow. *)

let PDE_LFLOW_TIME_PARTIAL = prove
 (`!U a b (FF:real->real^N->real^N^N) t y.
        lricci_flow U a b FF /\ a < t /\ t < b /\ y IN U
        ==> partial_derivative 1
              (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                   (FF (drop(fstcart z)) (sndcart z)))
              (pastecart (lift t) y) =
            vectorize((lambda p q. jp_eval (jp_rhs (dimindex(:N)) p q) (FF t) y):real^N^N)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [lricci_flow]) THEN
  ABBREV_TAC `Phi = \z:real^(1,N)finite_sum. (vectorize:real^N^N->real^(N,N)finite_prod)
                                              (FF (drop(fstcart z)) (sndcart z))` THEN
  SUBGOAL_THEN `(Phi:real^(1,N)finite_sum->real^(N,N)finite_prod) differentiable
                (at (pastecart (lift t) y))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `interval(lift a,lift b) PCROSS (U:real^N->bool)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM VECTORIZE_MATRIFY] THEN AP_TERM_TAC THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
  X_GEN_TAC `q:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
  EXISTS_TAC `\s. (FF:real->real^N->real^N^N) s y$p$q` THEN EXISTS_TAC `t:real` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`\z. (\x:real^(N,N)finite_prod. lift((matrify x:real^N^N)$p$q))
                          ((Phi:real^(1,N)finite_sum->real^(N,N)finite_prod) z)`;
                   `t:real`; `y:real^N`] PDE_ST_TIME_REAL_DERIV) THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN
       `(\z. (\x:real^(N,N)finite_prod. lift((matrify x:real^N^N)$p$q))
               ((Phi:real^(1,N)finite_sum->real^(N,N)finite_prod) z)) =
        (\x:real^(N,N)finite_prod. lift((matrify x:real^N^N)$p$q)) o Phi`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC DIFFERENTIABLE_LINEAR THEN REWRITE_TAC[LRG_LINEAR_MATRIFY_ENTRY];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\x:real^(N,N)finite_prod. lift((matrify x:real^N^N)$p$q)`;
                   `Phi:real^(1,N)finite_sum->real^(N,N)finite_prod`; `1`;
                   `pastecart (lift t) (y:real^N)`] PDE_PARTIAL_LINEAR_COMPOSE) THEN
    ASM_REWRITE_TAC[LRG_LINEAR_MATRIFY_ENTRY] THEN DISCH_THEN SUBST1_TAC THEN
    EXPAND_TAC "Phi" THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; MATRIFY_VECTORIZE];
    ASM_SIMP_TAC[jp_rhs; jp_eval] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `(FF:real->real^N->real^N^N) t`; `y:real^N`;
                   `p:num`; `q:num`] JP_RIC) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* Time derivatives of evaluations along a local Ricci flow. *)

let jp_tgood = new_definition
 `jp_tgood (U:real^N->bool) a b (FF:real->real^N->real^N^N) e <=>
    !t y. a < t /\ t < b /\ y IN U
          ==> ((\s. jp_eval e (FF s) y) has_real_derivative
               jp_eval (jp_dt (dimindex(:N)) e) (FF t) y) (atreal t)`;;

let JP_TGOOD_CONST = prove
 (`!U a b (FF:real->real^N->real^N^N) c. jp_tgood U a b FF (JPconst c)`,
  REWRITE_TAC[jp_tgood; jp_eval; jp_dt; HAS_REAL_DERIVATIVE_CONST]);;

let JP_TGOOD_ADD = prove
 (`!U a b (FF:real->real^N->real^N^N) e1 e2.
        jp_tgood U a b FF e1 /\ jp_tgood U a b FF e2
        ==> jp_tgood U a b FF (JPadd e1 e2)`,
  REWRITE_TAC[jp_tgood; jp_eval; jp_dt] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN ASM_SIMP_TAC[]);;

let JP_TGOOD_MUL = prove
 (`!U a b (FF:real->real^N->real^N^N) e1 e2.
        jp_tgood U a b FF e1 /\ jp_tgood U a b FF e2
        ==> jp_tgood U a b FF (JPmul e1 e2)`,
  REWRITE_TAC[jp_tgood; jp_eval; jp_dt] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\s. jp_eval e1 ((FF:real->real^N->real^N^N) s) y`;
                 `jp_eval (jp_dt (dimindex(:N)) e1) ((FF:real->real^N->real^N^N) t) y`;
                 `\s. jp_eval e2 ((FF:real->real^N->real^N^N) s) y`;
                 `jp_eval (jp_dt (dimindex(:N)) e2) ((FF:real->real^N->real^N^N) t) y`;
                 `t:real`] HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
  ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC(MESON[] `x = y ==> (f has_real_derivative x) net
                                 ==> (f has_real_derivative y) net`) THEN
  REAL_ARITH_TAC);;

let JP_TGOOD_VAR = prove
 (`!U a b (FF:real->real^N->real^N^N) l i j.
        lricci_flow U a b FF /\ ALL (\k. 1 <= k /\ k <= dimindex(:N)) l /\
        1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
        ==> jp_tgood U a b FF (JPvar l i j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[jp_tgood; jp_eval; jp_dt] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [lricci_flow]) THEN
  ABBREV_TAC `S = interval(lift a,lift b) PCROSS (U:real^N->bool)` THEN
  SUBGOAL_THEN `open(S:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL]; ALL_TAC] THEN
  SUBGOAL_THEN `!s. a < s /\ s < b ==> pastecart (lift s) (y:real^N) IN S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN ASM_SIMP_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP];
    ALL_TAC] THEN
  ABBREV_TAC `Phi = \z:real^(1,N)finite_sum. (vectorize:real^N^N->real^(N,N)finite_prod)
                                              (FF (drop(fstcart z)) (sndcart z))` THEN
  SUBGOAL_THEN `smooth_map_on S (Phi:real^(1,N)finite_sum->real^(N,N)finite_prod)`
  ASSUME_TAC THENL [MAP_EVERY EXPAND_TAC ["S"; "Phi"] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `l' = MAP (\k. 1 + k) (l:num list)` THEN
  SUBGOAL_THEN `ALL (\k. 1 <= k /\ k <= dimindex(:(1,N)finite_sum)) (l':num list)`
  ASSUME_TAC THENL
   [EXPAND_TAC "l'" THEN REWRITE_TAC[ALL_MAP; o_DEF; DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN
    UNDISCH_TAC `ALL (\k. 1 <= k /\ k <= dimindex(:N)) (l:num list)` THEN
    MATCH_MP_TAC MONO_ALL THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `L = \x:real^(N,N)finite_prod. lift((matrify x:real^N^N)$i$j)` THEN
  SUBGOAL_THEN `linear (L:real^(N,N)finite_prod->real^1)` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[LRG_LINEAR_MATRIFY_ENTRY]; ALL_TAC] THEN
  (* Step 1: the evaluation along time slices *)
  SUBGOAL_THEN
   `!s. a < s /\ s < b
        ==> (matrify:real^(N,N)finite_prod->real^N^N)
              (iterated_partial l ((vectorize:real^N^N->real^(N,N)finite_prod) o FF s) y)$i$j =
            drop((L:real^(N,N)finite_prod->real^1)
                   (iterated_partial l' (Phi:real^(1,N)finite_sum->real^(N,N)finite_prod)
                                     (pastecart (lift s) y)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "L" THEN REWRITE_TAC[LIFT_DROP] THEN
    SUBGOAL_THEN
     `iterated_partial l ((vectorize:real^N^N->real^(N,N)finite_prod) o
                          (FF:real->real^N->real^N^N) s) y =
      iterated_partial l' (Phi:real^(1,N)finite_sum->real^(N,N)finite_prod)
                       (pastecart (lift s) y)`
    (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `(vectorize:real^N^N->real^(N,N)finite_prod) o (FF:real->real^N->real^N^N) s =
                  (\y. (Phi:real^(1,N)finite_sum->real^(N,N)finite_prod) (pastecart (lift s) y))`
    SUBST1_TAC THENL
     [EXPAND_TAC "Phi" THEN
      REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
      ALL_TAC] THEN
    EXPAND_TAC "l'" THEN MATCH_MP_TAC PDE_ST_SLICE_ITERATED THEN
    EXISTS_TAC `S:real^(1,N)finite_sum->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC `\s. drop((L:real^(N,N)finite_prod->real^1)
                         (iterated_partial l' (Phi:real^(1,N)finite_sum->real^(N,N)finite_prod)
                                           (pastecart (lift s) y)))` THEN
  EXISTS_TAC `min (t - a) (b - t)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on S (iterated_partial l' (Phi:real^(1,N)finite_sum->real^(N,N)finite_prod))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL]; ALL_TAC] THEN
  SUBGOAL_THEN `pastecart (lift t) (y:real^N) IN S` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `iterated_partial l' (Phi:real^(1,N)finite_sum->real^(N,N)finite_prod) differentiable
      (at (pastecart (lift t) y))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `S:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z. (L:real^(N,N)finite_prod->real^1)
                        (iterated_partial l' (Phi:real^(1,N)finite_sum->real^(N,N)finite_prod) z)`;
                 `t:real`; `y:real^N`] PDE_ST_TIME_REAL_DERIV) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN
     `(\z. (L:real^(N,N)finite_prod->real^1)
            (iterated_partial l' (Phi:real^(1,N)finite_sum->real^(N,N)finite_prod) z)) =
      L o iterated_partial l' Phi`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN ASM_SIMP_TAC[DIFFERENTIABLE_LINEAR];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[] `x = y ==> (f has_real_derivative x) net
                                 ==> (f has_real_derivative y) net`) THEN
  MP_TAC(ISPECL [`L:real^(N,N)finite_prod->real^1`;
                 `iterated_partial l' (Phi:real^(1,N)finite_sum->real^(N,N)finite_prod)`;
                 `1`; `pastecart (lift t) (y:real^N)`] PDE_PARTIAL_LINEAR_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`S:real^(1,N)finite_sum->bool`;
                 `Phi:real^(1,N)finite_sum->real^(N,N)finite_prod`; `1`]
                TEXT_PARTIAL_COMMUTE_ITERATED) THEN
  ASM_REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1; LE_REFL] THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `l':num list`) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `ALL (\k. 1 <= k /\ k <= dimindex(:(1,N)finite_sum)) (l':num list)` THEN
    REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `pastecart (lift t) (y:real^N)`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC
   `Theta = \w:real^(1,N)finite_sum. (vectorize:real^N^N->real^(N,N)finite_prod)
              ((lambda p q. jp_eval (jp_rhs (dimindex(:N)) p q)
                                    ((FF:real->real^N->real^N^N) (drop(fstcart w)))
                                    (sndcart w)):real^N^N)` THEN
  SUBGOAL_THEN
   `!w. w IN S ==> partial_derivative 1 (Phi:real^(1,N)finite_sum->real^(N,N)finite_prod) w =
                   Theta w`
  ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[FORALL_IN_PCROSS; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `y':real^N`] THEN STRIP_TAC THEN
    MAP_EVERY EXPAND_TAC ["Theta"; "Phi"] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    MATCH_MP_TAC PDE_LFLOW_TIME_PARTIAL THEN EXISTS_TAC `U:real^N->bool` THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on S (Theta:real^(1,N)finite_sum->real^(N,N)finite_prod)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `partial_derivative 1 (Phi:real^(1,N)finite_sum->real^(N,N)finite_prod)` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `iterated_partial l' (partial_derivative 1 (Phi:real^(1,N)finite_sum->real^(N,N)finite_prod))
                    (pastecart (lift t) y) =
    iterated_partial l' (Theta:real^(1,N)finite_sum->real^(N,N)finite_prod) (pastecart (lift t) y)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN
    EXISTS_TAC `S:real^(1,N)finite_sum->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:num list`; `Theta:real^(1,N)finite_sum->real^(N,N)finite_prod`;
                 `S:real^(1,N)finite_sum->bool`; `lift t`; `y:real^N`]
                PDE_ST_SLICE_ITERATED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ABBREV_TAC
   `M = \y':real^N. ((lambda p q. jp_eval (jp_rhs (dimindex(:N)) p q)
                                         ((FF:real->real^N->real^N^N) t) y'):real^N^N)` THEN
  SUBGOAL_THEN
   `(\y':real^N. (Theta:real^(1,N)finite_sum->real^(N,N)finite_prod) (pastecart (lift t) y')) =
    (vectorize:real^N^N->real^(N,N)finite_prod) o M`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Theta"; "M"] THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o (M:real^N->real^N^N))`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[LRG_SMOOTH_VECTORIZE] THEN REPEAT STRIP_TAC THEN EXPAND_TAC "M" THEN
    ASM_SIMP_TAC[LAMBDA_BETA] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `(FF:real->real^N->real^N^N) t`] JP_METRIC_FIELD_GOOD) THEN
    ASM_SIMP_TAC[jp_good];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:num list`; `L:real^(N,N)finite_prod->real^1`;
                 `(vectorize:real^N^N->real^(N,N)finite_prod) o (M:real^N->real^N^N)`;
                 `U:real^N->bool`; `y:real^N`] PDE_ITERATED_PARTIAL_LINEAR_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MAP_EVERY EXPAND_TAC ["L"; "M"] THEN
  REWRITE_TAC[o_THM; MATRIFY_VECTORIZE] THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN
  MP_TAC(ISPECL [`l:num list`; `U:real^N->bool`; `(FF:real->real^N->real^N^N) t`;
                 `jp_rhs (dimindex(:N)) i j`; `y:real^N`] JP_DXL) THEN
  ASM_SIMP_TAC[LIFT_DROP]);;

let JP_TGOOD_INV = prove
 (`!U a b (FF:real->real^N->real^N^N) i j.
        lricci_flow U a b FF
        ==> jp_tgood U a b FF (JPinv i j)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[jp_tgood; jp_eval; jp_dt] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [lricci_flow]) THEN
  ABBREV_TAC `S = interval(lift a,lift b) PCROSS (U:real^N->bool)` THEN
  SUBGOAL_THEN `open(S:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL]; ALL_TAC] THEN
  SUBGOAL_THEN `pastecart (lift t) (y:real^N) IN S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN ASM_SIMP_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP];
    ALL_TAC] THEN
  ABBREV_TAC `A = \w:real^(1,N)finite_sum. (FF:real->real^N->real^N^N)
                                            (drop(fstcart w)) (sndcart w)` THEN
  SUBGOAL_THEN
   `smooth_map_on S ((vectorize:real^N^N->real^(N,N)finite_prod) o (A:real^(1,N)finite_sum->real^N^N))`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["S"; "A"] THEN REWRITE_TAC[o_DEF] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. w IN S ==> ~(det((A:real^(1,N)finite_sum->real^N^N) w) = &0)`
  ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[FORALL_IN_PCROSS; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `y':real^N`] THEN STRIP_TAC THEN EXPAND_TAC "A" THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `(FF:real->real^N->real^N^N) s`; `y':real^N`]
                  LRG_METRIC_INVERTIBLE) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`A:real^(1,N)finite_sum->real^N^N`; `S:real^(1,N)finite_sum->bool`;
                 `pastecart (lift t) (y:real^N)`] LRG_HAS_DERIVATIVE_MATRIX_INV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `W = (vectorize:real^N^N->real^(N,N)finite_prod) o
                  (\w. matrix_inv((A:real^(1,N)finite_sum->real^N^N) w))` THEN
  ABBREV_TAC `L = \x:real^(N,N)finite_prod. lift((matrify x:real^N^N)$i$j)` THEN
  SUBGOAL_THEN `linear (L:real^(N,N)finite_prod->real^1)` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[LRG_LINEAR_MATRIFY_ENTRY]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\s. matrix_inv((FF:real->real^N->real^N^N) s y)$i$j) =
    (\s. drop((L:real^(N,N)finite_prod->real^1)
                ((W:real^(1,N)finite_sum->real^(N,N)finite_prod) (pastecart (lift s) y))))`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["L"; "W"; "A"] THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP;
                MATRIFY_VECTORIZE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(W:real^(1,N)finite_sum->real^(N,N)finite_prod) differentiable
                (at (pastecart (lift t) y))` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN ASM_MESON_TAC[differentiable]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\w. (L:real^(N,N)finite_prod->real^1)
                        ((W:real^(1,N)finite_sum->real^(N,N)finite_prod) w)`;
                 `t:real`; `y:real^N`] PDE_ST_TIME_REAL_DERIV) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN
     `(\w. (L:real^(N,N)finite_prod->real^1)
            ((W:real^(1,N)finite_sum->real^(N,N)finite_prod) w)) = L o W`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN ASM_SIMP_TAC[DIFFERENTIABLE_LINEAR];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[] `x = y ==> (f has_real_derivative x) net
                                 ==> (f has_real_derivative y) net`) THEN
  MP_TAC(ISPECL [`L:real^(N,N)finite_prod->real^1`;
                 `W:real^(1,N)finite_sum->real^(N,N)finite_prod`;
                 `1`; `pastecart (lift t) (y:real^N)`] PDE_PARTIAL_LINEAR_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[partial_derivative] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT o
    check (fun th -> try is_comb(rator(concl th)) with Failure _ -> false)) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o
                        (A:real^(1,N)finite_sum->real^N^N))
                       (at (pastecart (lift t) y)) (basis 1) =
    vectorize((lambda p q. jp_eval (jp_rhs (dimindex(:N)) p q)
                                   ((FF:real->real^N->real^N^N) t) y):real^N^N)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM partial_derivative] THEN EXPAND_TAC "A" THEN REWRITE_TAC[o_DEF] THEN
    MATCH_MP_TAC PDE_LFLOW_TIME_PARTIAL THEN EXISTS_TAC `U:real^N->bool` THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXPAND_TAC "L" THEN
  REWRITE_TAC[MATRIFY_VECTORIZE; LIFT_DROP; MATRIX_NEG_COMPONENT; PDE_MATRIX_TRIPLE_ENTRY] THEN
  EXPAND_TAC "A" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  REWRITE_TAC[JP_EVAL_NEG; JP_EVAL_SUM; jp_eval] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC);;

let JP_DT = prove
 (`!U a b (FF:real->real^N->real^N^N).
        lricci_flow U a b FF
        ==> !e. jp_valid (dimindex(:N)) e ==> jp_tgood U a b FF e`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC pde_jpoly_INDUCT THEN
  REWRITE_TAC[jp_valid] THEN
  ASM_SIMP_TAC[JP_TGOOD_CONST; JP_TGOOD_VAR; JP_TGOOD_INV] THEN
  MESON_TAC[JP_TGOOD_ADD; JP_TGOOD_MUL]);;

(* ========================================================================= *)
(* Space-time smoothness of evaluations and the representation of every      *)
(* space-time partial of the chart matrices of a local Ricci flow by the     *)
(* polynomials jp_st (index 1 is time, index 1 + k is the space coordinate   *)
(* k).                                                                       *)
(* ========================================================================= *)

let JP_ST_SMOOTH = prove
 (`!S (FF:real->real^N->real^N^N).
        open S /\
        smooth_map_on S (\w. (vectorize:real^N^N->real^(N,N)finite_prod)
                             (FF (drop(fstcart w)) (sndcart w))) /\
        (!w. w IN S ==> invertible(FF (drop(fstcart w)) (sndcart w)))
        ==> !e. jp_valid (dimindex(:N)) e
                ==> smooth_map_on S (\w. lift(jp_eval e (FF (drop(fstcart w))) (sndcart w)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Phi = \w:real^(1,N)finite_sum. (vectorize:real^N^N->real^(N,N)finite_prod)
                                              (FF (drop(fstcart w)) (sndcart w))` THEN
  MATCH_MP_TAC pde_jpoly_INDUCT THEN REWRITE_TAC[jp_eval; jp_valid] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SMOOTH_MAP_ON_CONST];
    MAP_EVERY X_GEN_TAC [`l:num list`; `i:num`; `j:num`] THEN STRIP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `(\x:real^(N,N)finite_prod. lift((matrify x:real^N^N)$i$j)) o
                iterated_partial (MAP (\k. 1 + k) l)
                  (Phi:real^(1,N)finite_sum->real^(N,N)finite_prod)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `w:real^(1,N)finite_sum` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
      SUBGOAL_THEN
       `iterated_partial l ((vectorize:real^N^N->real^(N,N)finite_prod) o
                            (FF:real->real^N->real^N^N) (drop(fstcart w))) (sndcart w) =
        iterated_partial (MAP (\k. 1 + k) l)
          (Phi:real^(1,N)finite_sum->real^(N,N)finite_prod) w`
      (fun th -> REWRITE_TAC[th]) THEN
      SUBGOAL_THEN
       `(vectorize:real^N^N->real^(N,N)finite_prod) o (FF:real->real^N->real^N^N)
                                       (drop(fstcart(w:real^(1,N)finite_sum))) =
        (\y. (Phi:real^(1,N)finite_sum->real^(N,N)finite_prod)
               (pastecart (fstcart w) y))`
      SUBST1_TAC THENL
       [EXPAND_TAC "Phi" THEN
        REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`l:num list`; `Phi:real^(1,N)finite_sum->real^(N,N)finite_prod`;
                     `S:real^(1,N)finite_sum->bool`; `fstcart(w:real^(1,N)finite_sum)`;
                     `sndcart(w:real^(1,N)finite_sum)`] PDE_ST_SLICE_ITERATED) THEN
      ASM_REWRITE_TAC[PASTECART_FST_SND];
      MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
      ASM_SIMP_TAC[LRG_LINEAR_MATRIFY_ENTRY; SMOOTH_MAP_ON_ITERATED_PARTIAL]];
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(\w. lift(matrix_inv((FF:real->real^N->real^N^N) (drop(fstcart w)) (sndcart w))$i$j)) =
      (\x:real^(N,N)finite_prod. lift((matrify x:real^N^N)$i$j)) o
      ((vectorize:real^N^N->real^(N,N)finite_prod) o
       (\w. matrix_inv(FF (drop(fstcart w)) (sndcart w))))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; MATRIFY_VECTORIZE]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[LRG_LINEAR_MATRIFY_ENTRY] THEN
    MP_TAC(ISPECL [`S:real^(1,N)finite_sum->bool`;
                   `\w. (FF:real->real^N->real^N^N) (drop(fstcart w)) (sndcart w)`]
                  LRG_SMOOTH_MATRIX_INV) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[INVERTIBLE_DET_NZ];
    REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_ADD] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `(\w. lift(jp_eval a0 ((FF:real->real^N->real^N^N) (drop(fstcart w))) (sndcart w) *
                jp_eval a1 (FF (drop(fstcart w))) (sndcart w))) =
      (\w. lift(drop(lift(jp_eval a0 (FF (drop(fstcart w))) (sndcart w))) *
                drop(lift(jp_eval a1 (FF (drop(fstcart w))) (sndcart w)))))`
    SUBST1_TAC THENL [REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_LIFT_OPEN THEN ASM_SIMP_TAC[]]);;

(* The polynomials of the space-time partials. *)

let jp_st = define
 `(!n i j. jp_st n [] i j = JPvar [] i j) /\
  (!n h L i j. jp_st n (CONS h L) i j =
      if h = 1 then jp_dt n (jp_st n L i j) else jp_dx n (h - 1) (jp_st n L i j))`;;

let JP_VALID_ST = prove
 (`!L n i j. ALL (\h. 1 <= h /\ h <= n + 1) L /\ 1 <= i /\ i <= n /\ 1 <= j /\ j <= n
             ==> jp_valid n (jp_st n L i j)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[jp_st; jp_valid; ALL] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [MATCH_MP_TAC JP_VALID_DT THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC JP_VALID_DX THEN ASM_SIMP_TAC[] THEN ASM_ARITH_TAC]);;

let PDE_MATRIX_LAMBDA_ETA = prove
 (`!M:real^N^N. (lambda i j. M$i$j):real^N^N = M`,
  REWRITE_TAC[CART_EQ] THEN SIMP_TAC[LAMBDA_BETA]);;

let JP_ST_REP = prove
 (`!U a b (FF:real->real^N->real^N^N).
        lricci_flow U a b FF
        ==> !L s y. ALL (\h. 1 <= h /\ h <= dimindex(:N) + 1) L /\
                    a < s /\ s < b /\ y IN U
                    ==> iterated_partial L
                          (\w. (vectorize:real^N^N->real^(N,N)finite_prod)
                               (FF (drop(fstcart w)) (sndcart w)))
                          (pastecart (lift s) y) =
                        vectorize((lambda i j. jp_eval (jp_st (dimindex(:N)) L i j)
                                                       (FF s) y):real^N^N)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [lricci_flow]) THEN
  ABBREV_TAC `S = interval(lift a,lift b) PCROSS (U:real^N->bool)` THEN
  SUBGOAL_THEN `open(S:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. w IN S ==> invertible((FF:real->real^N->real^N^N) (drop(fstcart w)) (sndcart w))`
  ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[FORALL_IN_PCROSS; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP;
                                    FSTCART_PASTECART; SNDCART_PASTECART] THEN
    REPEAT STRIP_TAC THEN ASM_MESON_TAC[LRG_METRIC_INVERTIBLE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^(1,N)finite_sum->bool`; `FF:real->real^N->real^N^N`]
                JP_ST_SMOOTH) THEN
  ANTS_TAC THENL [EXPAND_TAC "S" THEN ASM_SIMP_TAC[]; DISCH_TAC] THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[iterated_partial; jp_st; jp_eval; FSTCART_PASTECART; SNDCART_PASTECART;
                LIFT_DROP] THEN
    REWRITE_TAC[o_DEF; MATRIFY_VECTORIZE] THEN
    REWRITE_TAC[PDE_MATRIX_LAMBDA_ETA];
    ALL_TAC] THEN
  REWRITE_TAC[ALL] THEN MAP_EVERY X_GEN_TAC [`s0:real`; `y0:real^N`] THEN STRIP_TAC THEN
  ABBREV_TAC
   `Psi = \w:real^(1,N)finite_sum. (vectorize:real^N^N->real^(N,N)finite_prod)
            ((lambda i j. jp_eval (jp_st (dimindex(:N)) t i j)
                                  ((FF:real->real^N->real^N^N) (drop(fstcart w)))
                                  (sndcart w)):real^N^N)` THEN
  SUBGOAL_THEN
   `!w. w IN S
        ==> iterated_partial t (\w. (vectorize:real^N^N->real^(N,N)finite_prod)
                                    ((FF:real->real^N->real^N^N) (drop(fstcart w))
                                                                (sndcart w))) w =
            (Psi:real^(1,N)finite_sum->real^(N,N)finite_prod) w`
  ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[FORALL_IN_PCROSS; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `y:real^N`] THEN STRIP_TAC THEN EXPAND_TAC "Psi" THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on S (Psi:real^(1,N)finite_sum->real^(N,N)finite_prod)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(Psi:real^(1,N)finite_sum->real^(N,N)finite_prod) =
      (vectorize:real^N^N->real^(N,N)finite_prod) o
      (\w. (lambda i j. jp_eval (jp_st (dimindex(:N)) t i j)
                                ((FF:real->real^N->real^N^N) (drop(fstcart w)))
                                (sndcart w)):real^N^N)`
    SUBST1_TAC THENL [EXPAND_TAC "Psi" THEN REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    ASM_SIMP_TAC[LRG_SMOOTH_VECTORIZE] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[LAMBDA_BETA] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC JP_VALID_ST THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pastecart (lift s0) (y0:real^N) IN S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN ASM_SIMP_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP];
    ALL_TAC] THEN
  REWRITE_TAC[iterated_partial] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `partial_derivative h (Psi:real^(1,N)finite_sum->real^(N,N)finite_prod)
                                 (pastecart (lift s0) y0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN
    EXISTS_TAC `S:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM VECTORIZE_MATRIFY] THEN AP_TERM_TAC THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  ABBREV_TAC `E = jp_st (dimindex(:N)) t i j` THEN
  SUBGOAL_THEN `jp_valid (dimindex(:N)) E` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN MATCH_MP_TAC JP_VALID_ST THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on S (\w. lift(jp_eval E ((FF:real->real^N->real^N^N) (drop(fstcart w)))
                                     (sndcart w)))`
  ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\w. lift(jp_eval E ((FF:real->real^N->real^N^N) (drop(fstcart w))) (sndcart w)))
    differentiable (at (pastecart (lift s0) y0))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `S:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(matrify:real^(N,N)finite_prod->real^N^N)
      (partial_derivative h (Psi:real^(1,N)finite_sum->real^(N,N)finite_prod)
                          (pastecart (lift s0) y0))$i$j =
    drop(partial_derivative h
           (\w. lift(jp_eval E ((FF:real->real^N->real^N^N) (drop(fstcart w))) (sndcart w)))
           (pastecart (lift s0) y0))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`\x:real^(N,N)finite_prod. lift((matrify x:real^N^N)$i$j)`;
                   `Psi:real^(1,N)finite_sum->real^(N,N)finite_prod`; `h:num`;
                   `pastecart (lift s0) (y0:real^N)`] PDE_PARTIAL_LINEAR_COMPOSE) THEN
    REWRITE_TAC[LRG_LINEAR_MATRIFY_ENTRY] THEN ANTS_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `S:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `drop`) THEN REWRITE_TAC[LIFT_DROP] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `w:real^(1,N)finite_sum` THEN
    EXPAND_TAC "Psi" THEN REWRITE_TAC[MATRIFY_VECTORIZE] THEN
    ASM_SIMP_TAC[LAMBDA_BETA];
    ALL_TAC] THEN
  REWRITE_TAC[jp_st] THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `h = 1` THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
    EXISTS_TAC `\s. jp_eval E ((FF:real->real^N->real^N^N) s) y0` THEN
    EXISTS_TAC `s0:real` THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`\w. lift(jp_eval E ((FF:real->real^N->real^N^N) (drop(fstcart w)))
                                        (sndcart w))`;
                     `s0:real`; `y0:real^N`] PDE_ST_TIME_REAL_DERIV) THEN
      ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
      MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`; `FF:real->real^N->real^N^N`]
                    JP_DT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `E:pde_jpoly`) THEN
      ASM_REWRITE_TAC[jp_tgood] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    MP_TAC(ISPECL [`\w. lift(jp_eval E ((FF:real->real^N->real^N^N) (drop(fstcart w)))
                                      (sndcart w))`;
                   `lift s0`; `y0:real^N`; `h - 1`] PDE_ST_SLICE_PARTIAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= h /\ ~(h = 1) ==> 1 + (h - 1) = h`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `(FF:real->real^N->real^N^N) s0`]
                  JP_METRIC_FIELD_GOOD) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `E:pde_jpoly`) THEN
    REWRITE_TAC[jp_good] THEN DISCH_THEN(MP_TAC o SPECL [`h - 1`; `y0:real^N`] o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LIFT_DROP]]);;

(* ========================================================================= *)
(* Uniform convergence of evaluations under uniform convergence of spatial   *)
(* jets on a compact set, with an invertible limit (JP_EVAL_UNIFORM_LIMIT).  *)
(* ========================================================================= *)

let PDE_MATRIX_INV_UNIFORM = prove
 (`!(A:real->real^N->real^N^N) (G:real^N->real^N^N) K b.
        compact K /\
        ((vectorize:real^N^N->real^(N,N)finite_prod) o G) continuous_on K /\
        (!y. y IN K ==> invertible(G y)) /\
        (!e. &0 < e
             ==> ?d. &0 < d /\
                     !t y. b - d < t /\ t < b /\ y IN K
                           ==> norm(vectorize(A t y) - vectorize(G y)) < e)
        ==> !e. &0 < e
                ==> ?d. &0 < d /\
                        !t y. b - d < t /\ t < b /\ y IN K
                              ==> norm((vectorize:real^N^N->real^(N,N)finite_prod)
                                         (matrix_inv(A t y)) -
                                       vectorize(matrix_inv(G y))) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  ABBREV_TAC `O = {v:real^(N,N)finite_prod | ~(det(matrify v:real^N^N) = &0)}` THEN
  SUBGOAL_THEN `open(O:real^(N,N)finite_prod->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN
    MP_TAC(ISPECL [`\v:real^(N,N)finite_prod. lift(det(matrify v:real^N^N))`;
                   `(:real^1) DIFF {vec 0}`] CONTINUOUS_OPEN_PREIMAGE_UNIV) THEN
    SIMP_TAC[OPEN_DIFF; OPEN_UNIV; CLOSED_SING; IN_DIFF; IN_UNIV; IN_SING] THEN
    REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP; DROP_VEC] THEN DISCH_THEN MATCH_MP_TAC THEN
    GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_DET_VECTORIZE THEN
    REWRITE_TAC[VECTORIZE_MATRIFY; CONTINUOUS_AT_ID];
    ALL_TAC] THEN
  ABBREV_TAC `f = \v:real^(N,N)finite_prod. (vectorize:real^N^N->real^(N,N)finite_prod)
                                              (matrix_inv(matrify v:real^N^N))` THEN
  SUBGOAL_THEN `(f:real^(N,N)finite_prod->real^(N,N)finite_prod) continuous_on O`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN EXPAND_TAC "f" THEN
    MP_TAC(ISPECL [`O:real^(N,N)finite_prod->bool`;
                   `matrify:real^(N,N)finite_prod->real^N^N`] LRG_SMOOTH_MATRIX_INV) THEN
    ASM_REWRITE_TAC[o_DEF; VECTORIZE_MATRIFY; ETA_AX; SMOOTH_MAP_ON_ID] THEN
    ANTS_TAC THENL [EXPAND_TAC "O" THEN SIMP_TAC[IN_ELIM_THM]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `compact(IMAGE ((vectorize:real^N^N->real^(N,N)finite_prod) o (G:real^N->real^N^N)) K) /\
    IMAGE ((vectorize:real^N^N->real^(N,N)finite_prod) o G) K SUBSET O`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_CONTINUOUS_IMAGE] THEN
    EXPAND_TAC "O" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; o_THM;
                                    MATRIFY_VECTORIZE] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[GSYM INVERTIBLE_DET_NZ] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `C0 = IMAGE ((vectorize:real^N^N->real^(N,N)finite_prod) o (G:real^N->real^N^N)) K` THEN
  MP_TAC(ISPECL [`C0:real^(N,N)finite_prod->bool`; `(:real^(N,N)finite_prod) DIFF O`]
                SEPARATE_COMPACT_CLOSED) THEN
  ASM_REWRITE_TAC[GSYM OPEN_CLOSED] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `(C0:real^(N,N)finite_prod->bool) SUBSET O` THEN SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `compact {x + z:real^(N,N)finite_prod | x IN C0 /\ z IN cball(vec 0,r / &2)} /\
    {x + z:real^(N,N)finite_prod | x IN C0 /\ z IN cball(vec 0,r / &2)} SUBSET O`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_SUMS; COMPACT_CBALL] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_CBALL_0] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x':real^(N,N)finite_prod`; `x' + z:real^(N,N)finite_prod`]) THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; dist; VECTOR_ARITH `x - (x + z):real^N = --z`;
                    NORM_NEG] THEN
    ASM_CASES_TAC `x' + z:real^(N,N)finite_prod IN O` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `C1 = {x + z:real^(N,N)finite_prod | x IN C0 /\ z IN cball(vec 0,r / &2)}` THEN
  MP_TAC(ISPECL [`f:real^(N,N)finite_prod->real^(N,N)finite_prod`;
                 `C1:real^(N,N)finite_prod->bool`] COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[uniformly_continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `min k (r / &2)`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `y:real^N`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `(vectorize:real^N^N->real^(N,N)finite_prod)(G(y:real^N)) IN C1 /\
    (vectorize:real^N^N->real^(N,N)finite_prod)((A:real->real^N->real^N^N) t y) IN C1`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "C1" THEN REWRITE_TAC[IN_ELIM_THM; IN_CBALL_0] THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`(vectorize:real^N^N->real^(N,N)finite_prod)(G(y:real^N))`;
                            `vec 0:real^(N,N)finite_prod`] THEN
      REWRITE_TAC[VECTOR_ADD_RID; NORM_0] THEN CONJ_TAC THENL
       [EXPAND_TAC "C0" THEN REWRITE_TAC[IN_IMAGE; o_THM] THEN ASM_MESON_TAC[];
        ASM_REAL_ARITH_TAC];
      MAP_EVERY EXISTS_TAC
       [`(vectorize:real^N^N->real^(N,N)finite_prod)(G(y:real^N))`;
        `(vectorize:real^N^N->real^(N,N)finite_prod)((A:real->real^N->real^N^N) t y) -
         vectorize(G(y:real^N))`] THEN
      REWRITE_TAC[VECTOR_ARITH `x + (y - x):real^N = y`] THEN CONJ_TAC THENL
       [EXPAND_TAC "C0" THEN REWRITE_TAC[IN_IMAGE; o_THM] THEN ASM_MESON_TAC[];
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`(vectorize:real^N^N->real^(N,N)finite_prod)(G(y:real^N))`;
    `(vectorize:real^N^N->real^(N,N)finite_prod)((A:real->real^N->real^N^N) t y)`]) THEN
  ASM_REWRITE_TAC[dist] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXPAND_TAC "f" THEN REWRITE_TAC[MATRIFY_VECTORIZE]);;

(* Uniform convergence on K of evaluations, by structural induction. *)

let jp_conv = new_definition
 `jp_conv (FF:real->real^N->real^N^N) (G:real^N->real^N^N) (K:real^N->bool) b e <=>
    !eps. &0 < eps
          ==> ?d. &0 < d /\
                  !t y. b - d < t /\ t < b /\ y IN K
                        ==> abs(jp_eval e (FF t) y - jp_eval e G y) < eps`;;

let PDE_MATRIFY_ENTRY_BOUND = prove
 (`!i j. ?C. &0 < C /\
             !v w:real^(N,N)finite_prod.
                abs((matrify v:real^N^N)$i$j - (matrify w:real^N^N)$i$j) <= C * norm(v - w)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `\x:real^(N,N)finite_prod. lift((matrify x:real^N^N)$i$j)`
               LINEAR_BOUNDED_POS) THEN
  REWRITE_TAC[LRG_LINEAR_MATRIFY_ENTRY] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `C:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v - w:real^(N,N)finite_prod`) THEN
  REWRITE_TAC[MATRIFY_SUB; MATRIX_SUB_COMPONENT; NORM_LIFT]);;

let JP_CONV_CONST = prove
 (`!(FF:real->real^N->real^N^N) G K b c. jp_conv FF G K b (JPconst c)`,
  REWRITE_TAC[jp_conv; jp_eval; REAL_SUB_REFL; REAL_ABS_NUM] THEN
  MESON_TAC[REAL_LT_01]);;

let JP_CONV_VAR = prove
 (`!(FF:real->real^N->real^N^N) G K b l i j.
        (!e. &0 < e
             ==> ?d. &0 < d /\
                     !t y. b - d < t /\ t < b /\ y IN K
                           ==> norm(iterated_partial l
                                      ((vectorize:real^N^N->real^(N,N)finite_prod) o FF t) y -
                                    iterated_partial l (vectorize o G) y) < e)
        ==> jp_conv FF G K b (JPvar l i j)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[jp_conv; jp_eval] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`i:num`; `j:num`] (INST_TYPE [`:N`,`:N`] PDE_MATRIFY_ENTRY_BOUND)) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / C`) THEN ASM_SIMP_TAC[REAL_LT_DIV] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `C * norm(iterated_partial l
                         ((vectorize:real^N^N->real^(N,N)finite_prod) o
                          (FF:real->real^N->real^N^N) t) y -
                       iterated_partial l (vectorize o (G:real^N->real^N^N)) y)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `e = C * e / C` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < C` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_LMUL THEN ASM_SIMP_TAC[]);;

let JP_CONV_INV = prove
 (`!(FF:real->real^N->real^N^N) G K b i j.
        compact K /\
        ((vectorize:real^N^N->real^(N,N)finite_prod) o G) continuous_on K /\
        (!y. y IN K ==> invertible(G y)) /\
        (!e. &0 < e
             ==> ?d. &0 < d /\
                     !t y. b - d < t /\ t < b /\ y IN K
                           ==> norm(vectorize(FF t y) - vectorize(G y)) < e)
        ==> jp_conv FF G K b (JPinv i j)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[jp_conv; jp_eval] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`i:num`; `j:num`] (INST_TYPE [`:N`,`:N`] PDE_MATRIFY_ENTRY_BOUND)) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`FF:real->real^N->real^N^N`; `G:real^N->real^N^N`; `K:real^N->bool`;
                 `b:real`] PDE_MATRIX_INV_UNIFORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e / C`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `y:real^N`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`(vectorize:real^N^N->real^(N,N)finite_prod)
       (matrix_inv((FF:real->real^N->real^N^N) t y))`;
    `(vectorize:real^N^N->real^(N,N)finite_prod) (matrix_inv((G:real^N->real^N^N) y))`]) THEN
  REWRITE_TAC[MATRIFY_VECTORIZE] THEN
  MATCH_MP_TAC(REAL_ARITH `b < e ==> a <= b ==> a < e`) THEN
  SUBGOAL_THEN `e = C * e / C` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < C` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_LMUL THEN ASM_SIMP_TAC[]);;

let JP_CONV_ADD = prove
 (`!(FF:real->real^N->real^N^N) G K b e1 e2.
        jp_conv FF G K b e1 /\ jp_conv FF G K b e2 ==> jp_conv FF G K b (JPadd e1 e2)`,
  REWRITE_TAC[jp_conv; jp_eval] THEN REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `eps / &2`)) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d1 d2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `y:real^N`])) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let PDE_PRODUCT_DIFF_BOUND = prove
 (`!a a' b b' B1 B2 eps.
        &0 < eps /\ abs a' <= B1 /\ abs b' <= B2 /\
        abs(a - a') < eps / (&2 * (abs B2 + &1)) /\
        abs(b - b') < min (&1) (eps / (&2 * (abs B1 + &1)))
        ==> abs(a * b - a' * b') < eps`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < abs B1 + &1 /\ &0 < abs B2 + &1` STRIP_ASSUME_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs(a - a') * abs b <= eps / (&2 * (abs B2 + &1)) * (abs B2 + &1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs a' * abs(b - b') < (abs B1 + &1) * (eps / (&2 * (abs B1 + &1)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `eps / (&2 * (abs B2 + &1)) * (abs B2 + &1) = eps / &2 /\
                (abs B1 + &1) * (eps / (&2 * (abs B1 + &1))) = eps / &2`
  STRIP_ASSUME_TAC THENL
   [ABBREV_TAC `c1 = abs B1 + &1` THEN ABBREV_TAC `c2 = abs B2 + &1` THEN
    UNDISCH_TAC `&0 < c1` THEN UNDISCH_TAC `&0 < c2` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `a * b - a' * b' = (a - a') * b + a' * (b - b')` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `abs(a - a') * abs b + abs a' * abs(b - b')` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_ABS_MUL] THEN REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

let JP_CONV_MUL = prove
 (`!(FF:real->real^N->real^N^N) G K b e1 e2 B1 B2.
        (!y. y IN K ==> abs(jp_eval e1 G y) <= B1) /\
        (!y. y IN K ==> abs(jp_eval e2 G y) <= B2) /\
        jp_conv FF G K b e1 /\ jp_conv FF G K b e2
        ==> jp_conv FF G K b (JPmul e1 e2)`,
  REWRITE_TAC[jp_conv; jp_eval] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `min (&1) (eps / (&2 * (abs B1 + &1)))`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `eps / (&2 * (abs B2 + &1))`) THEN
  SUBGOAL_THEN `&0 < eps / (&2 * (abs B2 + &1)) /\
                &0 < min (&1) (eps / (&2 * (abs B1 + &1)))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[REAL_LT_MIN; REAL_LT_01]] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d1 d2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
  MATCH_MP_TAC PDE_PRODUCT_DIFF_BOUND THEN
  MAP_EVERY EXISTS_TAC [`B1:real`; `B2:real`] THEN ASM_SIMP_TAC[] THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let JP_EVAL_BOUNDED = prove
 (`!U (G:real^N->real^N^N) K e.
        metric_field U G /\ compact K /\ K SUBSET U
        ==> ?B. !y. y IN K ==> abs(jp_eval e G y) <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] JP_METRIC_FIELD_GOOD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e:pde_jpoly`) THEN
  REWRITE_TAC[jp_good] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\y. lift(jp_eval e (G:real^N->real^N^N) y)`; `K:real^N->bool`]
                COMPACT_CONTINUOUS_IMAGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN MESON_TAC[]);;

let JP_EVAL_UNIFORM_LIMIT = prove
 (`!(FF:real->real^N->real^N^N) (G:real^N->real^N^N) U K b.
        compact K /\ K SUBSET U /\ metric_field U G /\
        (!l. ALL (\k. 1 <= k /\ k <= dimindex(:N)) l
             ==> !e. &0 < e
                     ==> ?d. &0 < d /\
                             !t y. b - d < t /\ t < b /\ y IN K
                                   ==> norm(iterated_partial l
                                              ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                               FF t) y -
                                            iterated_partial l (vectorize o G) y) < e)
        ==> !e. jp_valid (dimindex(:N)) e ==> jp_conv FF G K b e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC pde_jpoly_INDUCT THEN
  REWRITE_TAC[jp_valid; JP_CONV_CONST] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC JP_CONV_VAR THEN ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC JP_CONV_INV THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [metric_field]) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
      ASM_MESON_TAC[LRG_METRIC_INVERTIBLE; SUBSET];
      FIRST_X_ASSUM(MP_TAC o SPEC `[]:num list`) THEN
      REWRITE_TAC[ALL; iterated_partial; o_THM]];
    MESON_TAC[JP_CONV_ADD];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `K:real^N->bool`; `a0:pde_jpoly`]
                  JP_EVAL_BOUNDED) THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `K:real^N->bool`; `a1:pde_jpoly`]
                  JP_EVAL_BOUNDED) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `B2:real`) THEN DISCH_THEN(X_CHOOSE_TAC `B1:real`) THEN
    MATCH_MP_TAC JP_CONV_MUL THEN
    MAP_EVERY EXISTS_TAC [`B1:real`; `B2:real`] THEN ASM_SIMP_TAC[]]);;

(* ========================================================================= *)
(* Local flat gluing, time first.  A map that is smooth on (b - d,b) x B,    *)
(* B convex and open, and whose space-time partials all tend to zero         *)
(* uniformly on B as t tends to b from below, extended by zero, is smooth on *)
(* (b - d,b + d) x B (the local time-first form of SMOOTH_MAP_ON_GLUE_FLAT   *)
(* of the ns_time_ext part of pc_pde_seeley).                                *)
(* ========================================================================= *)

(* PDE_ST_OPEN_TIME_LT, PDE_ST_OPEN_TIME_GT, PDE_ST_TIME_DIST and           *)
(* PDE_ST_PASTECART_DIST are in the shared unit pc_pde_st.                   *)

(* The flat bound: o(b - t) below the hyperplane, by the mean value         *)
(* inequality on the convex slab (b - d',b) x B.                            *)

let PDE_FLAT_BOUND_ST = prove
 (`!(u:real^(1,N)finite_sum->real^K) b d (B:real^N->bool).
      convex B /\ open B /\ &0 < d /\
      smooth_map_on (interval(lift(b - d),lift b) PCROSS B) u /\
      (!e. &0 < e
           ==> ?d'. &0 < d' /\
                    !t y. b - d' < t /\ t < b /\ y IN B
                          ==> norm(u(pastecart (lift t) y)) < e) /\
      (!i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)
           ==> !e. &0 < e
                   ==> ?d'. &0 < d' /\
                            !t y. b - d' < t /\ t < b /\ y IN B
                                  ==> norm(partial_derivative i u (pastecart (lift t) y)) < e)
      ==> !e. &0 < e
              ==> ?d'. &0 < d' /\
                       !t y. b - d' < t /\ t < b /\ y IN B
                             ==> norm(u(pastecart (lift t) y)) <= e * (b - t)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "Z") (LABEL_TAC "P")))))) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < e / &2 / &(dimindex(:(1,N)finite_sum))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_SIMP_TAC[REAL_HALF; REAL_OF_NUM_LT; DIMINDEX_GE_1;
                 ARITH_RULE `1 <= n ==> 0 < n`];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\(i:num) (d':real). !t y. b - d' < t /\ t < b /\ y IN (B:real^N->bool)
       ==> norm(partial_derivative i (u:real^(1,N)finite_sum->real^K) (pastecart (lift t) y))
           < e / &2 / &(dimindex(:(1,N)finite_sum))`;
    `dimindex(:(1,N)finite_sum)`] TEXT_FINITE_DELTA_MIN) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      USE_THEN "P" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D")))] THEN
  EXISTS_TAC `min d d1` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!w w'. w IN interval(lift(b - min d d1),lift b) PCROSS (B:real^N->bool) /\
           w' IN interval(lift(b - min d d1),lift b) PCROSS B
           ==> norm((u:real^(1,N)finite_sum->real^K) w - u w') <= e / &2 * norm(w - w')`
  (LABEL_TAC "LIP") THENL
   [MATCH_MP_TAC DIFFERENTIABLE_BOUND THEN
    EXISTS_TAC `\w:real^(1,N)finite_sum.
                  frechet_derivative (u:real^(1,N)finite_sum->real^K) (at w)` THEN
    ASM_SIMP_TAC[CONVEX_PCROSS; CONVEX_INTERVAL] THEN
    REWRITE_TAC[FORALL_IN_PCROSS; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
    SUBGOAL_THEN
     `!s x. b - min d d1 < s /\ s < b /\ x IN B
            ==> (u:real^(1,N)finite_sum->real^K) differentiable (at (pastecart (lift s) x))`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `interval(lift(b - d),lift b) PCROSS (B:real^N->bool)` THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                   LIFT_DROP] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`s:real`; `x:real^N`] THEN STRIP_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
      REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(u:real^(1,N)finite_sum->real^K) differentiable (at (pastecart (lift s) x))` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP TEXT_HAS_DERIVATIVE_PARTIALS) THEN
    DISCH_THEN(fun th ->
      SUBST1_TAC(SYM(MATCH_MP FRECHET_DERIVATIVE_AT th)) THEN
      ASSUME_TAC(CONJUNCT1(REWRITE_RULE[has_derivative] th))) THEN
    FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2 o MATCH_MP ONORM) THEN
    X_GEN_TAC `v:real^(1,N)finite_sum` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&(dimindex(:(1,N)finite_sum)) *
                (e / &2 / &(dimindex(:(1,N)finite_sum))) * norm(v:real^(1,N)finite_sum)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC TEXT_NORM_VSUM_CMUL_BOUND THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      USE_THEN "D" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_MUL_ASSOC] THEN
      SIMP_TAC[REAL_DIV_LMUL; REAL_OF_NUM_EQ; DIMINDEX_NONZERO; REAL_LE_REFL]];
    ALL_TAC] THEN
  USE_THEN "Z" (MP_TAC o SPEC `e / &2 * (b - t)`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_HALF] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "E2")))] THEN
  ABBREV_TAC `t' = b - min d2 (b - t) / &2` THEN
  SUBGOAL_THEN `t < t' /\ t' < b /\ b - d2 < t'` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t'" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `norm((u:real^(1,N)finite_sum->real^K)(pastecart (lift t) y) - u(pastecart (lift t') y))
    <= e / &2 * (t' - t)`
  ASSUME_TAC THENL
   [USE_THEN "LIP" (MP_TAC o SPECL [`pastecart (lift t) (y:real^N)`;
                                    `pastecart (lift t') (y:real^N)`]) THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; PDE_ST_PASTECART_DIST] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `abs(t - t') = t' - t` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `norm((u:real^(1,N)finite_sum->real^K)(pastecart (lift t') y)) < e / &2 * (b - t)`
  ASSUME_TAC THENL
   [USE_THEN "E2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(u:real^(1,N)finite_sum->real^K)(pastecart (lift t) y)`;
                 `(u:real^(1,N)finite_sum->real^K)(pastecart (lift t') y)`]
    (NORM_ARITH `!x y:real^N. norm x <= norm y + norm(x - y)`)) THEN
  SUBGOAL_THEN `e / &2 * (t' - t) <= e / &2 * (b - t)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The derivative of the glued family at every point of the slab.           *)

let PDE_FLAT_GLUE_DERIV_ST = prove
 (`!(h:real^(1,N)finite_sum->real^K) b d (B:real^N->bool) l z.
      convex B /\ open B /\ &0 < d /\
      smooth_map_on (interval(lift(b - d),lift b) PCROSS B) h /\
      (!l. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l
           ==> !e. &0 < e
                   ==> ?d'. &0 < d' /\
                            !t y. b - d' < t /\ t < b /\ y IN B
                                  ==> norm(iterated_partial l h (pastecart (lift t) y)) < e) /\
      ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l /\
      z IN interval(lift(b - d),lift(b + d)) PCROSS B
      ==> ((\z. if drop(fstcart z) < b then iterated_partial l h z else vec 0)
           has_derivative
           (\v. vsum(1..dimindex(:(1,N)finite_sum))
                 (\i. v$i % (if drop(fstcart z) < b
                             then iterated_partial (CONS i l) h z else vec 0))))
          (at z)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "L") (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))))) THEN
  SPEC_TAC(`z:real^(1,N)finite_sum`,`z:real^(1,N)finite_sum`) THEN
  REWRITE_TAC[FORALL_IN_PCROSS; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
  MAP_EVERY X_GEN_TAC [`t0:real`; `y0:real^N`] THEN STRIP_TAC THEN
  REWRITE_TAC[FSTCART_PASTECART; LIFT_DROP] THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (REAL_ARITH `t0 < b \/ b < t0 \/ t0 = b`) THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    EXISTS_TAC `iterated_partial l (h:real^(1,N)finite_sum->real^K)` THEN
    EXISTS_TAC `interval(lift(b - d),lift b) PCROSS (B:real^N->bool)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                 LIFT_DROP] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_PCROSS; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP;
                  FSTCART_PASTECART] THEN SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[iterated_partial] THEN
    MATCH_MP_TAC TEXT_HAS_DERIVATIVE_PARTIALS THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `interval(lift(b - d),lift b) PCROSS (B:real^N->bool)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP;
                 SMOOTH_MAP_ON_ITERATED_PARTIAL];
    ASM_SIMP_TAC[REAL_ARITH `b < t ==> ~(t < b)`] THEN
    REWRITE_TAC[VECTOR_MUL_RZERO; VSUM_0] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    EXISTS_TAC `\z:real^(1,N)finite_sum. vec 0:real^K` THEN
    EXISTS_TAC `{z:real^(1,N)finite_sum | b < drop(fstcart z)}` THEN
    ASM_SIMP_TAC[PDE_ST_OPEN_TIME_GT; IN_ELIM_THM; HAS_DERIVATIVE_CONST;
                 FSTCART_PASTECART; LIFT_DROP; REAL_ARITH `b < t ==> ~(t < b)`];
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[REAL_LT_REFL; VECTOR_MUL_RZERO; VSUM_0] THEN
    REWRITE_TAC[HAS_DERIVATIVE_AT_ALT; LINEAR_ZERO] THEN
    REWRITE_TAC[FSTCART_PASTECART; LIFT_DROP; REAL_LT_REFL; VECTOR_SUB_RZERO] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`iterated_partial l (h:real^(1,N)finite_sum->real^K)`; `b:real`; `d:real`;
                   `B:real^N->bool`] PDE_FLAT_BOUND_ST) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL; OPEN_PCROSS; OPEN_INTERVAL] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      USE_THEN "L" (MP_TAC o SPEC `CONS (i:num) (l:num list)`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[ALL]; REWRITE_TAC[iterated_partial]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "FB"))) THEN
    MP_TAC(ISPEC `B:real^N->bool` OPEN_CONTAINS_BALL) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `y0:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min d1 r` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `w:real^(1,N)finite_sum` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`w:real^(1,N)finite_sum`; `pastecart (lift b) (y0:real^N)`]
                  PDE_ST_TIME_DIST) THEN
    REWRITE_TAC[FSTCART_PASTECART; LIFT_DROP] THEN DISCH_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[NORM_0] THENL
     [ALL_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE]] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `e * (b - drop(fstcart(w:real^(1,N)finite_sum)))` THEN CONJ_TAC THENL
     [ALL_TAC; MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC] THEN
    USE_THEN "FB" (MP_TAC o SPECL [`drop(fstcart(w:real^(1,N)finite_sum))`;
                                   `sndcart(w:real^(1,N)finite_sum)`]) THEN
    REWRITE_TAC[LIFT_DROP; PASTECART_FST_SND] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist] THEN
    MP_TAC(ISPEC `w - pastecart (lift b) (y0:real^N):real^(1,N)finite_sum` NORM_SNDCART) THEN
    REWRITE_TAC[SNDCART_SUB; SNDCART_PASTECART] THEN ASM_REAL_ARITH_TAC]);;

let PDE_FLAT_GLUE_ST = prove
 (`!(h:real^(1,N)finite_sum->real^K) b d (B:real^N->bool).
      convex B /\ open B /\ &0 < d /\
      smooth_map_on (interval(lift(b - d),lift b) PCROSS B) h /\
      (!l. ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) l
           ==> !e. &0 < e
                   ==> ?d'. &0 < d' /\
                            !t y. b - d' < t /\ t < b /\ y IN B
                                  ==> norm(iterated_partial l h (pastecart (lift t) y)) < e)
      ==> smooth_map_on (interval(lift(b - d),lift(b + d)) PCROSS B)
                        (\z. if drop(fstcart z) < b then h z else vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`interval(lift(b - d),lift(b + d)) PCROSS (B:real^N->bool)`;
    `\l (z:real^(1,N)finite_sum).
       if drop(fstcart z) < b then iterated_partial l (h:real^(1,N)finite_sum->real^K) z
       else vec 0`] SMOOTH_MAP_ON_PARTIAL_FAMILY) THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC PDE_FLAT_GLUE_DERIV_ST THEN
    EXISTS_TAC `d:real` THEN EXISTS_TAC `B:real^N->bool` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o SPEC `[]:num list`) THEN REWRITE_TAC[ALL; iterated_partial]]);;

(* ========================================================================= *)
(* Tools for the matching at t = b (locality of evaluations, one-sided       *)
(* limits, uniform continuity in time, entrywise bounds for vectorized       *)
(* matrices).                                                                *)
(* ========================================================================= *)

let JP_EVAL_LOCAL = prove
 (`!e U (G1:real^N->real^N^N) G2 y.
        open U /\ y IN U /\ (!x. x IN U ==> G1 x = G2 x)
        ==> jp_eval e G1 y = jp_eval e G2 y`,
  MATCH_MP_TAC pde_jpoly_INDUCT THEN REWRITE_TAC[jp_eval] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `iterated_partial a0 ((vectorize:real^N^N->real^(N,N)finite_prod) o
                           (G1:real^N->real^N^N)) (y:real^N) =
      iterated_partial a0 (vectorize o (G2:real^N->real^N^N)) y`
    (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[o_THM];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    MESON_TAC[];
    MESON_TAC[]]);;

let PDE_JP_LAMBDA_LOCAL = prove
 (`!(E:num->num->pde_jpoly) U (G1:real^N->real^N^N) G2 y.
        open U /\ y IN U /\ (!x. x IN U ==> G1 x = G2 x)
        ==> (lambda i j. jp_eval (E i j) G1 y):real^N^N =
            (lambda i j. jp_eval (E i j) G2 y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CART_EQ] THEN SIMP_TAC[LAMBDA_BETA] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC JP_EVAL_LOCAL THEN
  EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]);;

(* PDE_ST_RIGHT_EQ and PDE_ST_UNIFORM_LEFT are in the shared unit pc_pde_st. *)

(* Entrywise bounds for vectorized matrices.                                 *)

let PDE_NORM_VECTORIZE_LE = prove
 (`!(M:real^N^N) B.
        (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
               ==> abs(M$i$j) <= B)
        ==> norm((vectorize:real^N^N->real^(N,N)finite_prod) M) <=
            &(dimindex(:N) * dimindex(:N)) * B`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:(N,N)finite_prod))
                 (\k. abs(((vectorize:real^N^N->real^(N,N)finite_prod) M)$k))` THEN
  REWRITE_TAC[NORM_LE_L1] THEN
  MP_TAC(ISPECL [`1..dimindex(:(N,N)finite_prod)`;
                 `\k. abs(((vectorize:real^N^N->real^(N,N)finite_prod) M)$k)`; `B:real`]
                SUM_BOUND) THEN
  REWRITE_TAC[FINITE_NUMSEG; CARD_NUMSEG_1; DIMINDEX_FINITE_PROD; IN_NUMSEG] THEN
  DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`M:real^N^N`; `k:num`] VECTORIZE_COMPONENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[LE_ADD] THEN
  CONJ_TAC THEN MATCH_MP_TAC(ARITH_RULE `(a:num) < b ==> 1 + a <= b`) THEN
  SIMP_TAC[RDIV_LT_EQ; MOD_LT_EQ; DIMINDEX_NONZERO] THEN ASM_ARITH_TAC);;

let PDE_VECTORIZE_UNIFORM = prove
 (`!(X:real->real^N->num->num->real) (Y:real^N->num->num->real) K b.
        (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
               ==> !e. &0 < e
                       ==> ?d. &0 < d /\
                               !t y. b - d < t /\ t < b /\ y IN K
                                     ==> abs(X t y i j - Y y i j) < e)
        ==> !e. &0 < e
                ==> ?d. &0 < d /\
                        !t y. b - d < t /\ t < b /\ y IN K
                              ==> norm((vectorize:real^N^N->real^(N,N)finite_prod)
                                         ((lambda i j. X t y i j):real^N^N) -
                                       vectorize((lambda i j. Y y i j):real^N^N)) < e`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "H") THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &(dimindex(:N) * dimindex(:N))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ; MULT_EQ_0; DIMINDEX_NONZERO]; ALL_TAC] THEN
  ABBREV_TAC `e1 = e / &2 / &(dimindex(:N) * dimindex(:N))` THEN
  SUBGOAL_THEN `&0 < e1 /\ &(dimindex(:N) * dimindex(:N)) * e1 < e` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e1" THEN ASM_SIMP_TAC[REAL_LT_DIV; REAL_HALF; REAL_DIV_LMUL;
                                     REAL_LT_IMP_NZ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> ?d. &0 < d /\
                !j. 1 <= j /\ j <= dimindex(:N)
                    ==> !t y. b - d < t /\ t < b /\ y IN K
                              ==> abs((X:real->real^N->num->num->real) t y i j -
                                      (Y:real^N->num->num->real) y i j) < e1`
  (LABEL_TAC "I") THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL
     [`\(j:num) (d:real). !t y. b - d < t /\ t < b /\ y IN K
         ==> abs((X:real->real^N->num->num->real) t y i j -
                 (Y:real^N->num->num->real) y i j) < e1`;
      `dimindex(:N)`] TEXT_FINITE_DELTA_MIN) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      USE_THEN "H" (MP_TAC o SPECL [`i:num`; `j:num`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `e1:real`) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\(i:num) (d:real). !j. 1 <= j /\ j <= dimindex(:N)
       ==> !t y. b - d < t /\ t < b /\ y IN K
                 ==> abs((X:real->real^N->num->num->real) t y i j -
                         (Y:real^N->num->num->real) y i j) < e1`;
    `dimindex(:N)`] TEXT_FINITE_DELTA_MIN) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      USE_THEN "I" (fun th -> REWRITE_TAC[th])];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM VECTORIZE_SUB] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `&(dimindex(:N) * dimindex(:N)) * e1` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC PDE_NORM_VECTORIZE_LE THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MATRIX_SUB_COMPONENT; LAMBDA_BETA] THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* The set where a vectorized matrix field is invertible is open.           *)

let PDE_OPEN_INVERTIBLE_SET = prove
 (`!S (FE:real^M->real^(N,N)finite_prod).
        open S /\ FE continuous_on S
        ==> open {w | w IN S /\ invertible(matrify(FE w):real^N^N)}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\w. lift(det(matrify((FE:real^M->real^(N,N)finite_prod) w):real^N^N))`;
                 `S:real^M->bool`; `(:real^1) DIFF {vec 0}`] CONTINUOUS_OPEN_PREIMAGE) THEN
  REWRITE_TAC[IN_DIFF; IN_UNIV; IN_SING; GSYM DROP_EQ; LIFT_DROP; DROP_VEC;
              INVERTIBLE_DET_NZ] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[OPEN_DIFF; OPEN_UNIV; CLOSED_SING] THEN
  MATCH_MP_TAC CONTINUOUS_ON_DET_VECTORIZE THEN
  ASM_REWRITE_TAC[VECTORIZE_MATRIFY; ETA_AX]);;

(* ========================================================================= *)
(* The local gluing theorem.  Matching of all space-time partials at t = b,  *)
(* local smoothness near t = b by flat gluing, the equation at t = b, and    *)
(* PDE_GLUE.                                                                 *)
(* ========================================================================= *)

(* The space-time partials at t = b of the extension of a local flow from b *)
(* are the evaluations of jp_st at the metric of time b.                     *)

let PDE_LGLUE_MATCH = prove
 (`!W b c e (GG:real->real^N->real^N^N) (FE:real^(1,N)finite_sum->real^(N,N)finite_prod).
        lricci_flow W b c GG /\ metric_field W (GG b) /\ &0 < e /\
        smooth_map_on (interval(lift(b - e),lift c) PCROSS W) FE /\
        (!t y. b <= t /\ t < c /\ y IN W
               ==> FE(pastecart (lift t) y) = vectorize(GG t y))
        ==> !L y. ALL (\h. 1 <= h /\ h <= dimindex(:N) + 1) L /\ y IN W
                  ==> iterated_partial L FE (pastecart (lift b) y) =
                      vectorize((lambda i j. jp_eval (jp_st (dimindex(:N)) L i j) (GG b) y)
                                :real^N^N)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "RF") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "EQ"))))) THEN
  SUBGOAL_THEN `open(W:real^N->bool) /\ b < c` STRIP_ASSUME_TAC THENL
   [USE_THEN "RF" (MP_TAC o GEN_REWRITE_RULE I [lricci_flow]) THEN SIMP_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`L:num list`; `y:real^N`] THEN STRIP_TAC THEN
  ABBREV_TAC `GT = \s (x:real^N). (matrify:real^(N,N)finite_prod->real^N^N)
                                    ((FE:real^(1,N)finite_sum->real^(N,N)finite_prod)
                                     (pastecart (lift s) x))` THEN
  SUBGOAL_THEN `!s x. (GT:real->real^N->real^N^N) s x =
                      matrify((FE:real^(1,N)finite_sum->real^(N,N)finite_prod)
                              (pastecart (lift s) x))` (LABEL_TAC "GT") THENL
   [EXPAND_TAC "GT" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s x. b <= s /\ s < c /\ x IN W ==> (GT:real->real^N->real^N^N) s x = GG s x`
  (LABEL_TAC "GTE") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "GT" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "EQ" (fun th -> ASM_SIMP_TAC[th; MATRIFY_VECTORIZE]);
    ALL_TAC] THEN
  ABBREV_TAC `S = {w | w IN interval(lift(b - e),lift c) PCROSS (W:real^N->bool) /\
                       invertible(matrify((FE:real^(1,N)finite_sum->real^(N,N)finite_prod) w)
                                  :real^N^N)}` THEN
  SUBGOAL_THEN `open(S:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC PDE_OPEN_INVERTIBLE_SET THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN `(S:real^(1,N)finite_sum->bool) SUBSET interval(lift(b - e),lift c) PCROSS W`
  ASSUME_TAC THENL [EXPAND_TAC "S" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. w IN S ==> invertible(matrify((FE:real^(1,N)finite_sum->real^(N,N)finite_prod) w)
                              :real^N^N)`
  ASSUME_TAC THENL [EXPAND_TAC "S" THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `pastecart (lift b) (y:real^N) IN S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN
    REWRITE_TAC[IN_ELIM_THM; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    USE_THEN "EQ" (MP_TAC o SPECL [`b:real`; `y:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[MATRIFY_VECTORIZE] THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^(1,N)finite_sum->bool`; `GT:real->real^N->real^N^N`]
                JP_ST_SMOOTH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    USE_THEN "GT" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[LIFT_DROP; PASTECART_FST_SND; VECTORIZE_MATRIFY; ETA_AX] THEN
    ASM_MESON_TAC[SMOOTH_MAP_ON_SUBSET];
    DISCH_THEN(LABEL_TAC "SM")] THEN
  REMOVE_THEN "GT" (K ALL_TAC) THEN
  SUBGOAL_THEN
   `smooth_map_on S
      (\w. (vectorize:real^N^N->real^(N,N)finite_prod)
           ((lambda i j. jp_eval (jp_st (dimindex(:N)) L i j)
                                 ((GT:real->real^N->real^N^N) (drop(fstcart w))) (sndcart w))
            :real^N^N))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\w. (vectorize:real^N^N->real^(N,N)finite_prod)
           ((lambda i j. jp_eval (jp_st (dimindex(:N)) L i j)
                                 ((GT:real->real^N->real^N^N) (drop(fstcart w))) (sndcart w))
            :real^N^N)) =
      vectorize o
      (\w. (lambda i j. jp_eval (jp_st (dimindex(:N)) L i j)
                                ((GT:real->real^N->real^N^N) (drop(fstcart w))) (sndcart w))
           :real^N^N)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    ASM_SIMP_TAC[LRG_SMOOTH_VECTORIZE] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[LAMBDA_BETA] THEN USE_THEN "SM" MATCH_MP_TAC THEN
    MATCH_MP_TAC JP_VALID_ST THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`iterated_partial L (FE:real^(1,N)finite_sum->real^(N,N)finite_prod)`;
    `\w. (vectorize:real^N^N->real^(N,N)finite_prod)
         ((lambda i j. jp_eval (jp_st (dimindex(:N)) L i j)
                               ((GT:real->real^N->real^N^N) (drop(fstcart w))) (sndcart w))
          :real^N^N)`;
    `b:real`; `c:real`; `y:real^N`] PDE_ST_RIGHT_EQ) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `interval(lift(b - e),lift c) PCROSS (W:real^N->bool)` THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; SMOOTH_MAP_ON_ITERATED_PARTIAL;
                   PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `S:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `iterated_partial L
                    (\w. (vectorize:real^N^N->real^(N,N)finite_prod)
                         ((GG:real->real^N->real^N^N) (drop(fstcart w)) (sndcart w)))
                    (pastecart (lift s) (y:real^N))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN
        EXISTS_TAC `interval(lift b,lift c) PCROSS (W:real^N->bool)` THEN
        ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                     LIFT_DROP] THEN
        REWRITE_TAC[FORALL_IN_PCROSS; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP;
                    FSTCART_PASTECART; SNDCART_PASTECART] THEN
        REPEAT STRIP_TAC THEN USE_THEN "EQ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`W:real^N->bool`; `b:real`; `c:real`; `GG:real->real^N->real^N^N`]
                    JP_ST_REP) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPECL [`L:num list`; `s:real`; `y:real^N`]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      AP_TERM_TAC THEN MATCH_MP_TAC PDE_JP_LAMBDA_LOCAL THEN
      EXISTS_TAC `W:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN USE_THEN "GTE" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC PDE_JP_LAMBDA_LOCAL THEN
  EXISTS_TAC `W:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN USE_THEN "GTE" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]);;

(* The jets of the difference between the flow below b and the extension of *)
(* the flow from b tend to zero uniformly on compact sets as t -> b-.       *)

let PDE_LGLUE_JETS = prove
 (`!W a b c e (GG:real->real^N->real^N^N)
    (FE:real^(1,N)finite_sum->real^(N,N)finite_prod) K.
        lricci_flow W a b GG /\ lricci_flow W b c GG /\ metric_field W (GG b) /\ &0 < e /\
        smooth_map_on (interval(lift(b - e),lift c) PCROSS W) FE /\
        (!t y. b <= t /\ t < c /\ y IN W
               ==> FE(pastecart (lift t) y) = vectorize(GG t y)) /\
        (!K l eps. compact K /\ K SUBSET W /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l /\
                   &0 < eps
                   ==> ?d. &0 < d /\
                           !t y. b - d < t /\ t < b /\ y IN K
                                 ==> norm(iterated_partial l
                                            ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                             GG t) y -
                                          iterated_partial l (vectorize o GG b) y) < eps) /\
        compact K /\ K SUBSET W
        ==> !l. ALL (\h. 1 <= h /\ h <= dimindex(:N) + 1) l
                ==> !eps. &0 < eps
                          ==> ?d. &0 < d /\
                                  !t y. b - d < t /\ t < b /\ y IN K
                                        ==> norm(iterated_partial l
                                                  (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                                                       (GG (drop(fstcart z)) (sndcart z)) -
                                                       FE z)
                                                  (pastecart (lift t) y)) < eps`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "F1") (CONJUNCTS_THEN2 (LABEL_TAC "F2")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "EQ") (CONJUNCTS_THEN2 (LABEL_TAC "JET")
    STRIP_ASSUME_TAC))))))) THEN
  SUBGOAL_THEN `open(W:real^N->bool) /\ a < b /\ b < c /\
                smooth_map_on (interval(lift a,lift b) PCROSS W)
                  (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                       (GG (drop(fstcart z)) (sndcart z)))`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "F1" (MP_TAC o GEN_REWRITE_RULE I [lricci_flow]) THEN
    USE_THEN "F2" (MP_TAC o GEN_REWRITE_RULE I [lricci_flow]) THEN SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\t y i j. jp_eval (jp_st (dimindex(:N)) l i j)
                                    ((GG:real->real^N->real^N^N) t) y`;
                 `\y i j. jp_eval (jp_st (dimindex(:N)) l i j)
                                  ((GG:real->real^N->real^N^N) b) y`;
                 `K:real^N->bool`; `b:real`] PDE_VECTORIZE_UNIFORM) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`GG:real->real^N->real^N^N`; `(GG:real->real^N->real^N^N) b`;
                   `W:real^N->bool`; `K:real^N->bool`; `b:real`] JP_EVAL_UNIFORM_LIMIT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "JET" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `jp_st (dimindex(:N)) l i j`) THEN
    ANTS_TAC THENL [MATCH_MP_TAC JP_VALID_ST THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[jp_conv];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `eps / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D1"))) THEN
  MP_TAC(ISPECL [`iterated_partial l (FE:real^(1,N)finite_sum->real^(N,N)finite_prod)`;
                 `b:real`; `e:real`; `c:real`; `W:real^N->bool`; `K:real^N->bool`]
                PDE_ST_UNIFORM_LEFT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL; OPEN_PCROSS; OPEN_INTERVAL];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `eps / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D2"))) THEN
  EXISTS_TAC `min (min d1 d2) (min e (b - a))` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN W` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL
   [`l:num list`;
    `interval(lift(b - min e (b - a)),lift b) PCROSS (W:real^N->bool)`;
    `\z. (vectorize:real^N^N->real^(N,N)finite_prod)
         ((GG:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z))`;
    `FE:real^(1,N)finite_sum->real^(N,N)finite_prod`]
   TEXT_ITERATED_PARTIAL_SUB_OPEN)) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN CONJ_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THENL
     [EXISTS_TAC `interval(lift a,lift b) PCROSS (W:real^N->bool)`;
      EXISTS_TAC `interval(lift(b - e),lift c) PCROSS (W:real^N->bool)`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN
    REWRITE_TAC[SUBSET_REFL; SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `pastecart (lift t) (y:real^N)`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`W:real^N->bool`; `a:real`; `b:real`; `GG:real->real^N->real^N^N`]
                JP_ST_REP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`l:num list`; `t:real`; `y:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`W:real^N->bool`; `b:real`; `c:real`; `e:real`; `GG:real->real^N->real^N^N`;
                 `FE:real^(1,N)finite_sum->real^(N,N)finite_prod`] PDE_LGLUE_MATCH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`l:num list`; `y:real^N`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "M") THEN
  USE_THEN "D1" (MP_TAC o SPECL [`t:real`; `y:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "D2" (MP_TAC o SPECL [`t:real`; `y:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "M" (SUBST1_TAC o SYM) THEN
  MATCH_ACCEPT_TAC(NORM_ARITH
   `!a b c:real^N e. norm(c - b) < e / &2 ==> norm(a - b) < e / &2 ==> norm(a - c) < e`));;

(* Local smoothness of the concatenated chart family near (b,y0).          *)

let PDE_LGLUE_POINT = prove
 (`!W a b c e (GG:real->real^N->real^N^N)
    (FE:real^(1,N)finite_sum->real^(N,N)finite_prod) y0.
        lricci_flow W a b GG /\ lricci_flow W b c GG /\ metric_field W (GG b) /\ &0 < e /\
        smooth_map_on (interval(lift(b - e),lift c) PCROSS W) FE /\
        (!t y. b <= t /\ t < c /\ y IN W
               ==> FE(pastecart (lift t) y) = vectorize(GG t y)) /\
        (!K l eps. compact K /\ K SUBSET W /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l /\
                   &0 < eps
                   ==> ?d. &0 < d /\
                           !t y. b - d < t /\ t < b /\ y IN K
                                 ==> norm(iterated_partial l
                                            ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                             GG t) y -
                                          iterated_partial l (vectorize o GG b) y) < eps) /\
        y0 IN W
        ==> ?d r. &0 < d /\ &0 < r /\
                  smooth_map_on (interval(lift(b - d),lift(b + d)) PCROSS ball(y0,r))
                    (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                         (GG (drop(fstcart z)) (sndcart z)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "F1") (CONJUNCTS_THEN2 (LABEL_TAC "F2")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "EQ") (CONJUNCTS_THEN2 (LABEL_TAC "JET")
    ASSUME_TAC))))))) THEN
  SUBGOAL_THEN `open(W:real^N->bool) /\ a < b /\ b < c /\
                smooth_map_on (interval(lift a,lift b) PCROSS W)
                  (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                       (GG (drop(fstcart z)) (sndcart z)))`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "F1" (MP_TAC o GEN_REWRITE_RULE I [lricci_flow]) THEN
    USE_THEN "F2" (MP_TAC o GEN_REWRITE_RULE I [lricci_flow]) THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `W:real^N->bool` OPEN_CONTAINS_CBALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `y0:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?d. &0 < d /\ d <= e /\ d <= b - a /\ d <= c - b` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min e (min (b - a) (c - b))` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`d:real`; `r:real`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `ball(y0:real^N,r) SUBSET W` ASSUME_TAC THENL
   [ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET_TRANS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                      ((GG:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z)) -
                      (FE:real^(1,N)finite_sum->real^(N,N)finite_prod) z`;
                 `b:real`; `d:real`; `ball(y0:real^N,r)`] PDE_FLAT_GLUE_ST) THEN
  REWRITE_TAC[CONVEX_BALL; OPEN_BALL] THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
      SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_BALL] THEN CONJ_TAC THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THENL
       [EXISTS_TAC `interval(lift a,lift b) PCROSS (W:real^N->bool)`;
        EXISTS_TAC `interval(lift(b - e),lift c) PCROSS (W:real^N->bool)`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN
      ASM_REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `dimindex(:(1,N)finite_sum) = dimindex(:N) + 1` SUBST1_TAC THENL
     [REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `l:num list` THEN DISCH_TAC THEN X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`W:real^N->bool`; `a:real`; `b:real`; `c:real`; `e:real`;
                   `GG:real->real^N->real^N^N`;
                   `FE:real^(1,N)finite_sum->real^(N,N)finite_prod`;
                   `cball(y0:real^N,r)`] PDE_LGLUE_JETS) THEN
    ASM_REWRITE_TAC[COMPACT_CBALL] THEN
    DISCH_THEN(MP_TAC o SPEC `l:num list`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `eps:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d':real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET];
    DISCH_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `\z. (FE:real^(1,N)finite_sum->real^(N,N)finite_prod) z +
                  (if drop(fstcart z) < b
                   then (vectorize:real^N^N->real^(N,N)finite_prod)
                        ((GG:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z)) - FE z
                   else vec 0)` THEN
  SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_BALL] THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_PCROSS; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP;
                FSTCART_PASTECART; SNDCART_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN
    COND_CASES_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ADD_RID] THEN USE_THEN "EQ" MATCH_MP_TAC THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_BALL] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
  EXISTS_TAC `interval(lift(b - e),lift c) PCROSS (W:real^N->bool)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN
  ASM_REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC);;

(* The Ricci flow equation at t = b.                                         *)

let PDE_LGLUE_EQ_B = prove
 (`!W a b c e (GG:real->real^N->real^N^N)
    (FE:real^(1,N)finite_sum->real^(N,N)finite_prod) y i j.
        lricci_flow W b c GG /\ metric_field W (GG b) /\ &0 < e /\ a < b /\
        smooth_map_on (interval(lift(b - e),lift c) PCROSS W) FE /\
        (!t y. b <= t /\ t < c /\ y IN W
               ==> FE(pastecart (lift t) y) = vectorize(GG t y)) /\
        smooth_map_on (interval(lift a,lift c) PCROSS W)
          (\z. (vectorize:real^N^N->real^(N,N)finite_prod) (GG (drop(fstcart z)) (sndcart z))) /\
        y IN W /\ 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
        ==> ((\s. GG s y$i$j) has_real_derivative
             (--(&2) * lricci (GG b) y (basis i) (basis j))) (atreal b)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "RF") (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "EQ") (CONJUNCTS_THEN2 (LABEL_TAC "S")
   STRIP_ASSUME_TAC))))))) THEN
  SUBGOAL_THEN `open(W:real^N->bool) /\ b < c` STRIP_ASSUME_TAC THENL
   [USE_THEN "RF" (MP_TAC o GEN_REWRITE_RULE I [lricci_flow]) THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. (vectorize:real^N^N->real^(N,N)finite_prod)
         ((GG:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z)))
    differentiable (at (pastecart (lift b) y))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `interval(lift a,lift c) PCROSS (W:real^N->bool)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\w. lift((GG:real->real^N->real^N^N) (drop(fstcart w)) (sndcart w)$i$j))
    differentiable (at (pastecart (lift b) y))` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\w. lift((GG:real->real^N->real^N^N) (drop(fstcart w)) (sndcart w)$i$j)) =
      (\x:real^(N,N)finite_prod. lift((matrify x:real^N^N)$i$j)) o
      (\z. (vectorize:real^N^N->real^(N,N)finite_prod) (GG (drop(fstcart z)) (sndcart z)))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; MATRIFY_VECTORIZE]; ALL_TAC] THEN
    MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC DIFFERENTIABLE_LINEAR THEN REWRITE_TAC[LRG_LINEAR_MATRIFY_ENTRY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `drop(partial_derivative 1
          (\w. lift((GG:real->real^N->real^N^N) (drop(fstcart w)) (sndcart w)$i$j))
          (pastecart (lift b) y)) =
    --(&2) * lricci (GG b) y (basis i) (basis j)`
  (fun th -> REWRITE_TAC[GSYM th]) THENL
   [MP_TAC(ISPECL [`\x:real^(N,N)finite_prod. lift((matrify x:real^N^N)$i$j)`;
                   `\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                        ((GG:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z))`;
                   `1`; `pastecart (lift b) (y:real^N)`] PDE_PARTIAL_LINEAR_COMPOSE) THEN
    ASM_REWRITE_TAC[LRG_LINEAR_MATRIFY_ENTRY; MATRIFY_VECTORIZE] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
    SUBGOAL_THEN
     `partial_derivative 1 (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                                ((GG:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z)))
                         (pastecart (lift b) y) =
      partial_derivative 1 (FE:real^(1,N)finite_sum->real^(N,N)finite_prod)
                         (pastecart (lift b) y)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC PDE_ST_RIGHT_EQ THEN EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
        EXISTS_TAC `interval(lift a,lift c) PCROSS (W:real^N->bool)` THEN
        ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE;
                     PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP];
        MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
        EXISTS_TAC `interval(lift(b - e),lift c) PCROSS (W:real^N->bool)` THEN
        ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE;
                     PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN
        MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN
        EXISTS_TAC `interval(lift b,lift c) PCROSS (W:real^N->bool)` THEN
        ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                     LIFT_DROP] THEN
        REWRITE_TAC[FORALL_IN_PCROSS; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP;
                    FSTCART_PASTECART; SNDCART_PASTECART] THEN
        REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN USE_THEN "EQ" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`W:real^N->bool`; `b:real`; `c:real`; `e:real`;
                   `GG:real->real^N->real^N^N`;
                   `FE:real^(1,N)finite_sum->real^(N,N)finite_prod`] PDE_LGLUE_MATCH) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`[1]`; `y:real^N`]) THEN
    ASM_REWRITE_TAC[ALL; iterated_partial] THEN
    ANTS_TAC THENL [ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[MATRIFY_VECTORIZE; LAMBDA_BETA] THEN
    REWRITE_TAC[jp_st; jp_dt; jp_dxl; jp_rhs; jp_eval] THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC JP_RIC THEN
    EXISTS_TAC `W:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\w. lift((GG:real->real^N->real^N^N) (drop(fstcart w)) (sndcart w)$i$j)`;
                 `b:real`; `y:real^N`] PDE_ST_TIME_REAL_DERIV) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP]);;

(* The local gluing theorem: a local Ricci flow on (a,b) whose spatial jets *)
(* converge, as t -> b-, to those of a local Ricci flow from b (smooth up to *)
(* t = b) concatenates to a local Ricci flow on (a,c).                       *)

let PDE_LGLUE = prove
 (`!W a b c (GG:real->real^N->real^N^N).
        lricci_flow W a b GG /\ lricci_flow W b c GG /\ metric_field W (GG b) /\
        (?e FE. &0 < e /\
                smooth_map_on (interval(lift(b - e),lift c) PCROSS W) FE /\
                !t y. b <= t /\ t < c /\ y IN W
                      ==> FE(pastecart (lift t) y) =
                          (vectorize:real^N^N->real^(N,N)finite_prod)(GG t y)) /\
        (!K l eps. compact K /\ K SUBSET W /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l /\
                   &0 < eps
                   ==> ?d. &0 < d /\
                           !t y. b - d < t /\ t < b /\ y IN K
                                 ==> norm(iterated_partial l
                                            ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                             GG t) y -
                                          iterated_partial l (vectorize o GG b) y) < eps)
        ==> lricci_flow W a c GG`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "F1") (CONJUNCTS_THEN2 (LABEL_TAC "F2")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "JET"))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real`
   (X_CHOOSE_THEN `FE:real^(1,N)finite_sum->real^(N,N)finite_prod`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "EQ"))))) THEN
  SUBGOAL_THEN
   `open(W:real^N->bool) /\ a < b /\ b < c /\
    (!t. a < t /\ t < b ==> metric_field W ((GG:real->real^N->real^N^N) t)) /\
    (!t. b < t /\ t < c ==> metric_field W ((GG:real->real^N->real^N^N) t)) /\
    (!t y i j. a < t /\ t < b /\ y IN W /\
               1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
               ==> ((\s. GG s y$i$j) has_real_derivative
                    (--(&2) * lricci (GG t) y (basis i) (basis j))) (atreal t)) /\
    (!t y i j. b < t /\ t < c /\ y IN W /\
               1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
               ==> ((\s. GG s y$i$j) has_real_derivative
                    (--(&2) * lricci (GG t) y (basis i) (basis j))) (atreal t))`
  (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "M1") (CONJUNCTS_THEN2 (LABEL_TAC "M2")
   (CONJUNCTS_THEN2 (LABEL_TAC "E1") (LABEL_TAC "E2"))))))) THENL
   [USE_THEN "F1" (MP_TAC o GEN_REWRITE_RULE I [lricci_flow]) THEN
    USE_THEN "F2" (MP_TAC o GEN_REWRITE_RULE I [lricci_flow]) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (interval(lift a,lift c) PCROSS W)
      (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
           ((GG:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z)))`
  (LABEL_TAC "S") THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN
    REWRITE_TAC[FORALL_IN_PCROSS; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
    MAP_EVERY X_GEN_TAC [`t0:real`; `y0:real^N`] THEN STRIP_TAC THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (REAL_ARITH `t0 < b \/ t0 = b \/ b < t0`) THENL
     [EXISTS_TAC `interval(lift a,lift b) PCROSS (W:real^N->bool)` THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                   LIFT_DROP] THEN
      USE_THEN "F1" (MP_TAC o GEN_REWRITE_RULE I [lricci_flow]) THEN SIMP_TAC[];
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      MP_TAC(ISPECL [`W:real^N->bool`; `a:real`; `b:real`; `c:real`; `e:real`;
                     `GG:real->real^N->real^N^N`;
                     `FE:real^(1,N)finite_sum->real^(N,N)finite_prod`; `y0:real^N`]
                    PDE_LGLUE_POINT) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `interval(lift(b - d),lift(b + d)) PCROSS ball(y0:real^N,r)` THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_BALL; PASTECART_IN_PCROSS;
                   IN_INTERVAL_1; LIFT_DROP; CENTRE_IN_BALL] THEN ASM_REAL_ARITH_TAC;
      EXISTS_TAC `interval(lift b,lift c) PCROSS (W:real^N->bool)` THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                   LIFT_DROP] THEN
      USE_THEN "F2" (MP_TAC o GEN_REWRITE_RULE I [lricci_flow]) THEN SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[lricci_flow] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (REAL_ARITH `t < b \/ t = b \/ b < t`) THENL
     [USE_THEN "M1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      USE_THEN "M2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`; `i:num`; `j:num`] THEN STRIP_TAC THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (REAL_ARITH `t < b \/ t = b \/ b < t`) THENL
     [USE_THEN "E1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC PDE_LGLUE_EQ_B THEN
      MAP_EVERY EXISTS_TAC [`W:real^N->bool`; `a:real`; `c:real`; `e:real`;
                            `FE:real^(1,N)finite_sum->real^(N,N)finite_prod`] THEN
      ASM_REWRITE_TAC[];
      USE_THEN "E2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* PDE_GLUE_STATEMENT (MT Prop 3.12): gluing a Ricci flow on (a,b) to a     *)
(* Ricci flow from b when the spatial jets of the chart matrices converge.  *)

let PDE_GLUE = prove
 (`!(u:A->bool) (n:N->bool). PDE_GLUE_STATEMENT u n`,
  REWRITE_TAC[PDE_GLUE_STATEMENT] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "R1")
    (CONJUNCTS_THEN2 (LABEL_TAC "R2") (LABEL_TAC "JET"))) THEN
  USE_THEN "R2" (MP_TAC o GEN_REWRITE_RULE I [ricci_flow_from]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "R2ON")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "EXT"))) THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
                a < b /\ b < c`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "R1" (MP_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
    USE_THEN "R2ON" (MP_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!cc. cc IN atlas
         ==> lricci_flow (IMAGE (SND cc) (FST cc)) a c
               (\t. metric_local atlas cc ((g:real->A->real^N^N) t))`
  (LABEL_TAC "LOC") THENL
   [X_GEN_TAC `cc:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    MATCH_MP_TAC PDE_LGLUE THEN EXISTS_TAC `b:real` THEN REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PDE_RF_CHART_LOCAL THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC PDE_RF_CHART_LOCAL THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ASSUME `riemannian_metric atlas ((g:real->A->real^N^N) b)`) THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      USE_THEN "EXT" (fun th ->
        MP_TAC(MATCH_MP th (ASSUME `(cc:(A->bool)#(A->real^N)) IN atlas`))) THEN
      REWRITE_TAC[];
      REPEAT STRIP_TAC THEN USE_THEN "JET" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[ricci_flow_on] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (REAL_ARITH `t < b \/ t = b \/ b < t`) THENL
     [USE_THEN "R1" (MP_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      USE_THEN "R2ON" (MP_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `cc:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    USE_THEN "LOC" (fun th ->
      MP_TAC(MATCH_MP th (ASSUME `(cc:(A->bool)#(A->real^N)) IN atlas`))) THEN
    REWRITE_TAC[lricci_flow] THEN SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `i:num`; `j:num`] THEN STRIP_TAC THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (REAL_ARITH `t < b \/ t = b \/ b < t`) THENL
     [USE_THEN "R1" (MP_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
      DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC;
      USE_THEN "R2ON" (MP_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
      DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ABBREV_TAC `cc = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
                  PDE_CHART_AT_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!s. (g:real->A->real^N^N) s x = metric_local atlas cc (g s) (SND cc x)`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN EXPAND_TAC "cc" THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC METRIC_LOCAL_AT THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[RFB_MFD_RICCI_MATRIX_COMPONENT] THEN REWRITE_TAC[mfd_ricci] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "LOC" (fun th ->
      MP_TAC(MATCH_MP th (ASSUME `(cc:(A->bool)#(A->real^N)) IN atlas`))) THEN
    REWRITE_TAC[lricci_flow] THEN DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
    DISCH_THEN(MP_TAC o SPECL [`b:real`; `SND (cc:(A->bool)#(A->real^N)) x`;
                               `i:num`; `j:num`]) THEN
    ASM_REWRITE_TAC[]]);;

