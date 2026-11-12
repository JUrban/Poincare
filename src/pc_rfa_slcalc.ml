(* ========================================================================= *)
(* Unit pc_rfa_slcalc: local calculus for the local Shi estimates: first and *)
(* second partial derivatives of real functions, linearity, product and      *)
(* chain rules for the local Laplacian llap and the gradient inner product,  *)
(* the gradient bound for squared tensor norms, and the Bernstein inequality *)
(* (CLN Lemma 6.16 at every order).                                          *)
(* ========================================================================= *)

needs "src/pc_rfa_shi.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* First and second partials rfa_d1, rfa_d2 of real functions,               *)
(* their algebra (sum, product, constant, chain rule), and llap, lgrad2 in  *)
(* these terms; the gradient inner product rfa_lginner.                      *)
(* ========================================================================= *)

let rfa_d1 = new_definition
 `rfa_d1 (f:real^N->real) (y:real^N) (h:real^N) =
    drop(frechet_derivative (\z. lift(f z)) (at y) h)`;;

let rfa_d2 = new_definition
 `rfa_d2 (f:real^N->real) (y:real^N) (a:real^N) (b:real^N) =
    drop(frechet_derivative (\z. frechet_derivative (\w. lift(f w)) (at z) b) (at y) a)`;;

let rfa_lginner = new_definition
 `rfa_lginner (G:real^N->real^N^N) (f:real^N->real) (g:real^N->real) (y:real^N) =
    sum(1..dimindex(:N))
     (\i. sum(1..dimindex(:N))
       (\j. matrix_inv(G y)$i$j * rfa_d1 f y (basis i) * rfa_d1 g y (basis j)))`;;

let RFA_LLAP_D2 = prove
 (`!(G:real^N->real^N^N) f y.
     llap G f y =
     sum(1..dimindex(:N))
      (\i. sum(1..dimindex(:N))
        (\j. matrix_inv(G y)$i$j *
             (rfa_d2 f y (basis i) (basis j) -
              sum(1..dimindex(:N))
               (\k. (christoffel G y (basis i) (basis j))$k * rfa_d1 f y (basis k)))))`,
  REWRITE_TAC[llap; rfa_d1; rfa_d2]);;

let RFA_LGRAD2_D1 = prove
 (`!(G:real^N->real^N^N) f y. lgrad2 G f y = rfa_lginner G f f y`,
  REWRITE_TAC[lgrad2; rfa_lginner; rfa_d1]);;

let RFA_D2_AS_D1 = prove
 (`!(f:real^N->real) y a b. rfa_d2 f y a b = rfa_d1 (\z. rfa_d1 f z b) y a`,
  REWRITE_TAC[rfa_d1; rfa_d2; LIFT_DROP; ETA_AX]);;

let RFA_D1_LOCAL = prove
 (`!U (f:real^N->real) g y h.
     open U /\ y IN U /\ (!z. z IN U ==> f z = g z) ==> rfa_d1 f y h = rfa_d1 g y h`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_d1] THEN AP_TERM_TAC THEN AP_THM_TAC THEN
  MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_SIMP_TAC[]);;

let RFA_D1_SMOOTH = prove
 (`!U (f:real^N->real) h.
     open U /\ smooth_map_on U (\z. lift(f z))
     ==> smooth_map_on U (\z. lift(rfa_d1 f z h))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_d1; LIFT_DROP] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]);;

let RFA_D1_MUL_AT = prove
 (`!(f:real^N->real) g y h.
     (\z. lift(f z)) differentiable (at y) /\ (\z. lift(g z)) differentiable (at y)
     ==> rfa_d1 (\z. f z * g z) y h = rfa_d1 f y h * g y + f y * rfa_d1 g y h`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_d1] THEN
  MP_TAC(ISPECL
   [`f:real^N->real`;
    `\h. drop(frechet_derivative (\z. lift((f:real^N->real) z)) (at y) h)`;
    `\z. lift((g:real^N->real) z)`;
    `frechet_derivative (\z. lift((g:real^N->real) z)) (at y)`;
    `y:real^N`] HAS_DERIVATIVE_MUL_AT) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX] THEN
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM LIFT_CMUL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[DROP_ADD; DROP_CMUL; LIFT_DROP] THEN REAL_ARITH_TAC);;

let RFA_D1_ADD_AT = prove
 (`!(f:real^N->real) g y h.
     (\z. lift(f z)) differentiable (at y) /\ (\z. lift(g z)) differentiable (at y)
     ==> rfa_d1 (\z. f z + g z) y h = rfa_d1 f y h + rfa_d1 g y h`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_d1] THEN
  SUBGOAL_THEN
   `frechet_derivative (\z. lift((f:real^N->real) z + g z)) (at y) =
    (\h. frechet_derivative (\z. lift(f z)) (at y) h +
         frechet_derivative (\z. lift(g z)) (at y) h)`
  (fun th -> REWRITE_TAC[th; DROP_ADD]) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN
  ASM_REWRITE_TAC[ETA_AX; GSYM FRECHET_DERIVATIVE_WORKS]);;

let RFA_D1_CMUL_AT = prove
 (`!(f:real^N->real) c y h.
     (\z. lift(f z)) differentiable (at y)
     ==> rfa_d1 (\z. c * f z) y h = c * rfa_d1 f y h`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_d1] THEN
  SUBGOAL_THEN
   `frechet_derivative (\z. lift(c * (f:real^N->real) z)) (at y) =
    (\h. c % frechet_derivative (\z. lift(f z)) (at y) h)`
  (fun th -> REWRITE_TAC[th; DROP_CMUL]) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN
  ASM_REWRITE_TAC[ETA_AX; GSYM FRECHET_DERIVATIVE_WORKS]);;

let RFA_D1_CONST = prove
 (`!(c:real) (y:real^N) h. rfa_d1 (\z. c) y h = &0`,
  REWRITE_TAC[rfa_d1; FRECHET_DERIVATIVE_CONST_AT; DROP_VEC]);;

let RFA_D1_COMPOSE_AT = prove
 (`!(f:real^N->real) phi phi1 y h.
     (\z. lift(f z)) differentiable (at y) /\
     (phi has_real_derivative phi1) (atreal (f y))
     ==> rfa_d1 (\z. phi(f z)) y h = phi1 * rfa_d1 f y h`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_d1] THEN
  SUBGOAL_THEN
   `frechet_derivative (\z. lift(phi((f:real^N->real) z))) (at y) =
    (\h. phi1 % frechet_derivative (\z. lift(f z)) (at y) h)`
  (fun th -> REWRITE_TAC[th; DROP_CMUL]) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  SUBGOAL_THEN
   `(\z. lift(phi((f:real^N->real) z))) = (lift o phi o drop) o (\z. lift(f z))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\h. phi1 % frechet_derivative (\z. lift((f:real^N->real) z)) (at y) h) =
    (\x. phi1 % x) o frechet_derivative (\z. lift(f z)) (at y)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN
  ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS; GSYM HAS_REAL_FRECHET_DERIVATIVE_AT]);;

let RFA_COMPOSE_HAS_DERIVATIVE_AT = prove
 (`!(f:real^N->real) phi phi1 y.
     (\z. lift(f z)) differentiable (at y) /\
     (phi has_real_derivative phi1) (atreal (f y))
     ==> ((\z. lift(phi(f z))) has_derivative
          (\h. phi1 % frechet_derivative (\z. lift(f z)) (at y) h)) (at y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z. lift(phi((f:real^N->real) z))) = (lift o phi o drop) o (\z. lift(f z))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\h. phi1 % frechet_derivative (\z. lift((f:real^N->real) z)) (at y) h) =
    (\x. phi1 % x) o frechet_derivative (\z. lift(f z)) (at y)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN
  ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS; GSYM HAS_REAL_FRECHET_DERIVATIVE_AT]);;

let RFA_COMPOSE_DIFFERENTIABLE_AT = prove
 (`!(f:real^N->real) phi phi1 y.
     (\z. lift(f z)) differentiable (at y) /\
     (phi has_real_derivative phi1) (atreal (f y))
     ==> (\z. lift(phi(f z))) differentiable (at y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[differentiable] THEN
  EXISTS_TAC `\h. phi1 % frechet_derivative (\z. lift((f:real^N->real) z)) (at y) h` THEN
  MATCH_MP_TAC RFA_COMPOSE_HAS_DERIVATIVE_AT THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Second partials of sums, products and compositions; the                   *)
(* sum, product and chain rules for llap and lgrad2.                         *)
(* ========================================================================= *)

let RFA_D2_ADD = prove
 (`!U (f:real^N->real) g y a b.
     open U /\ smooth_map_on U (\z. lift(f z)) /\ smooth_map_on U (\z. lift(g z)) /\
     y IN U
     ==> rfa_d2 (\z. f z + g z) y a b = rfa_d2 f y a b + rfa_d2 g y a b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RFA_D2_AS_D1] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `rfa_d1 (\z. rfa_d1 (f:real^N->real) z b + rfa_d1 g z b) y a` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFA_D1_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC RFA_D1_ADD_AT THEN CONJ_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC RFA_D1_ADD_AT THEN CONJ_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_SIMP_TAC[RFA_D1_SMOOTH]]);;

let RFA_D2_MUL = prove
 (`!U (f:real^N->real) g y a b.
     open U /\ smooth_map_on U (\z. lift(f z)) /\ smooth_map_on U (\z. lift(g z)) /\
     y IN U
     ==> rfa_d2 (\z. f z * g z) y a b =
         rfa_d2 f y a b * g y + rfa_d1 f y b * rfa_d1 g y a +
         rfa_d1 f y a * rfa_d1 g y b + f y * rfa_d2 g y a b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RFA_D2_AS_D1] THEN
  SUBGOAL_THEN
   `smooth_map_on U (\z. lift(rfa_d1 (f:real^N->real) z b)) /\
    smooth_map_on U (\z. lift(rfa_d1 (g:real^N->real) z b)) /\
    smooth_map_on U (\z. lift(rfa_d1 (f:real^N->real) z b * g z)) /\
    smooth_map_on U (\z. lift((f:real^N->real) z * rfa_d1 g z b))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RFA_D1_SMOOTH] THEN CONJ_TAC THEN
    MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL_REAL THEN ASM_SIMP_TAC[RFA_D1_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!h:real^N->real. open U /\ smooth_map_on U (\z. lift(h z)) /\ (y:real^N) IN U
                     ==> (\z. lift(h z)) differentiable (at y)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `rfa_d1 (\z. rfa_d1 (f:real^N->real) z b * g z + f z * rfa_d1 g z b) y a` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFA_D1_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC RFA_D1_MUL_AT THEN CONJ_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z. rfa_d1 (f:real^N->real) z b * g z`;
                 `\z. (f:real^N->real) z * rfa_d1 g z b`; `y:real^N`; `a:real^N`]
         RFA_D1_ADD_AT) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
                  ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`\z. rfa_d1 (f:real^N->real) z b`; `g:real^N->real`; `y:real^N`;
                 `a:real^N`] RFA_D1_MUL_AT) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
                  ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`f:real^N->real`; `\z. rfa_d1 (g:real^N->real) z b`; `y:real^N`;
                 `a:real^N`] RFA_D1_MUL_AT) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
                  ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

let RFA_D2_COMPOSE = prove
 (`!U S (f:real^N->real) phi phi1 phi2 y a b.
     open U /\ smooth_map_on U (\z. lift(f z)) /\ y IN U /\
     (!z. z IN U ==> f z IN S) /\
     (!x. x IN S ==> (phi has_real_derivative phi1 x) (atreal x) /\
                     (phi1 has_real_derivative phi2 x) (atreal x))
     ==> rfa_d2 (\z. phi(f z)) y a b =
         phi2(f y) * rfa_d1 f y a * rfa_d1 f y b + phi1(f y) * rfa_d2 f y a b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RFA_D2_AS_D1] THEN
  SUBGOAL_THEN
   `!z. z IN U ==> (\z. lift((f:real^N->real) z)) differentiable (at z)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `rfa_d1 (\z. phi1((f:real^N->real) z) * rfa_d1 f z b) y a` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFA_D1_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC RFA_D1_COMPOSE_AT THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z. (phi1:real->real) ((f:real^N->real) z)`;
                 `\z. rfa_d1 (f:real^N->real) z b`; `y:real^N`; `a:real^N`]
         RFA_D1_MUL_AT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFA_COMPOSE_DIFFERENTIABLE_AT THEN
      EXISTS_TAC `(phi2:real->real) ((f:real^N->real) y)` THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_SIMP_TAC[RFA_D1_SMOOTH]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`f:real^N->real`; `phi1:real->real`;
                 `(phi2:real->real) ((f:real^N->real) y)`; `y:real^N`; `a:real^N`]
         RFA_D1_COMPOSE_AT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REAL_ARITH_TAC);;

let RFA_D2_CONST = prove
 (`!(c:real) (y:real^N) a b. rfa_d2 (\z. c) y a b = &0`,
  REWRITE_TAC[RFA_D2_AS_D1; RFA_D1_CONST]);;

let RFA_LLAP_CONST = prove
 (`!(G:real^N->real^N^N) c y. llap G (\z. c) y = &0`,
  REWRITE_TAC[RFA_LLAP_D2; RFA_D2_CONST; RFA_D1_CONST] THEN
  REWRITE_TAC[REAL_MUL_RZERO; SUM_0; REAL_SUB_REFL]);;

let RFA_LGRAD2_CONST = prove
 (`!(G:real^N->real^N^N) c y. lgrad2 G (\z. c) y = &0`,
  REWRITE_TAC[RFA_LGRAD2_D1; rfa_lginner; RFA_D1_CONST] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; SUM_0]);;

let RFA_LLAP_ADD = prove
 (`!U (G:real^N->real^N^N) f g y.
     open U /\ smooth_map_on U (\z. lift(f z)) /\ smooth_map_on U (\z. lift(g z)) /\
     y IN U
     ==> llap G (\z. f z + g z) y = llap G f y + llap G g y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RFA_LLAP_D2] THEN
  SUBGOAL_THEN
   `!a b. rfa_d2 (\z. (f:real^N->real) z + g z) y a b = rfa_d2 f y a b + rfa_d2 g y a b`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC RFA_D2_ADD THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!h. rfa_d1 (\z. (f:real^N->real) z + g z) y h = rfa_d1 f y h + rfa_d1 g y h`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC RFA_D1_ADD_AT THEN CONJ_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB; SUM_ADD_NUMSEG] THEN REAL_ARITH_TAC);;

let RFA_LLAP_SUB = prove
 (`!U (G:real^N->real^N^N) f g y.
     open U /\ smooth_map_on U (\z. lift(f z)) /\ smooth_map_on U (\z. lift(g z)) /\
     y IN U
     ==> llap G (\z. f z - g z) y = llap G f y - llap G g y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z. (f:real^N->real) z - g z) = (\z. f z + --(&1) * g z)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `f:real^N->real`;
                 `\z. --(&1) * (g:real^N->real) z`; `y:real^N`] RFA_LLAP_ADD) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL_REAL THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `g:real^N->real`; `--(&1)`;
                 `y:real^N`] RFA_LLAP_CMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

let RFA_LGINNER_SYM = prove
 (`!U (G:real^N->real^N^N) f g y.
     metric_field U G /\ y IN U ==> rfa_lginner G f g y = rfa_lginner G g f y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_lginner] THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `i:num`; `j:num`]
         LRG_MATRIX_INV_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

let RFA_LLAP_MUL = prove
 (`!U (G:real^N->real^N^N) f g y.
     metric_field U G /\ smooth_map_on U (\z. lift(f z)) /\
     smooth_map_on U (\z. lift(g z)) /\ y IN U
     ==> llap G (\z. f z * g z) y =
         llap G f y * g y + f y * llap G g y + &2 * rfa_lginner G f g y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `rfa_lginner G (g:real^N->real) f y = rfa_lginner (G:real^N->real^N^N) f g y`
  MP_TAC THENL
   [MATCH_MP_TAC RFA_LGINNER_SYM THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[RFA_LLAP_D2; rfa_lginner] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!a b. rfa_d2 (\z. (f:real^N->real) z * g z) y a b =
          rfa_d2 f y a b * g y + rfa_d1 f y b * rfa_d1 g y a +
          rfa_d1 f y a * rfa_d1 g y b + f y * rfa_d2 g y a b`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC RFA_D2_MUL THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!h. rfa_d1 (\z. (f:real^N->real) z * g z) y h = rfa_d1 f y h * g y + f y * rfa_d1 g y h`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC RFA_D1_MUL_AT THEN CONJ_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. sum(1..dimindex(:N))
            (\k. (christoffel (G:real^N->real^N^N) y (basis i) (basis j))$k *
                 (rfa_d1 (f:real^N->real) y (basis k) * g y + f y * rfa_d1 g y (basis k))) =
          g y * sum(1..dimindex(:N))
                  (\k. (christoffel G y (basis i) (basis j))$k * rfa_d1 f y (basis k)) +
          f y * sum(1..dimindex(:N))
                  (\k. (christoffel G y (basis i) (basis j))$k * rfa_d1 g y (basis k))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_ADD_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `X = \i j. matrix_inv((G:real^N->real^N^N) y)$i$j *
              (rfa_d2 (f:real^N->real) y (basis i) (basis j) -
               sum(1..dimindex(:N))
                (\k. (christoffel G y (basis i) (basis j))$k * rfa_d1 f y (basis k)))` THEN
  ABBREV_TAC
   `Y = \i j. matrix_inv((G:real^N->real^N^N) y)$i$j *
              (rfa_d2 (g:real^N->real) y (basis i) (basis j) -
               sum(1..dimindex(:N))
                (\k. (christoffel G y (basis i) (basis j))$k * rfa_d1 g y (basis k)))` THEN
  ABBREV_TAC
   `P = \i j. matrix_inv((G:real^N->real^N^N) y)$i$j *
              rfa_d1 (f:real^N->real) y (basis i) * rfa_d1 (g:real^N->real) y (basis j)` THEN
  ABBREV_TAC
   `Q = \i j. matrix_inv((G:real^N->real^N^N) y)$i$j *
              rfa_d1 (g:real^N->real) y (basis i) * rfa_d1 (f:real^N->real) y (basis j)` THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum(1..dimindex(:N))
     (\i. sum(1..dimindex(:N))
       (\j. (g:real^N->real) y * (X:num->num->real) i j +
            (f:real^N->real) y * (Y:num->num->real) i j +
            (Q:num->num->real) i j + (P:num->num->real) i j))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MAP_EVERY EXPAND_TAC ["X"; "Y"; "P"; "Q"] THEN BETA_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG; SUM_LMUL] THEN
  UNDISCH_TAC
   `sum(1..dimindex(:N))
     (\i. sum(1..dimindex(:N))
       (\j. matrix_inv((G:real^N->real^N^N) y)$i$j *
            rfa_d1 (g:real^N->real) y (basis i) * rfa_d1 (f:real^N->real) y (basis j))) =
    sum(1..dimindex(:N))
     (\i. sum(1..dimindex(:N))
       (\j. matrix_inv(G y)$i$j * rfa_d1 f y (basis i) * rfa_d1 g y (basis j)))` THEN
  MAP_EVERY EXPAND_TAC ["X"; "Y"; "P"; "Q"] THEN REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let RFA_LLAP_COMPOSE = prove
 (`!U S (G:real^N->real^N^N) f phi phi1 phi2 y.
     open U /\ smooth_map_on U (\z. lift(f z)) /\ y IN U /\
     (!z. z IN U ==> f z IN S) /\
     (!x. x IN S ==> (phi has_real_derivative phi1 x) (atreal x) /\
                     (phi1 has_real_derivative phi2 x) (atreal x))
     ==> llap G (\z. phi(f z)) y =
         phi1(f y) * llap G f y + phi2(f y) * lgrad2 G f y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RFA_LLAP_D2; RFA_LGRAD2_D1; rfa_lginner] THEN
  SUBGOAL_THEN
   `!a b. rfa_d2 (\z. (phi:real->real)((f:real^N->real) z)) y a b =
          phi2(f y) * rfa_d1 f y a * rfa_d1 f y b + phi1(f y) * rfa_d2 f y a b`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC RFA_D2_COMPOSE THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `S:real->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!h. rfa_d1 (\z. (phi:real->real)((f:real^N->real) z)) y h = phi1(f y) * rfa_d1 f y h`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC RFA_D1_COMPOSE_AT THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. sum(1..dimindex(:N))
            (\k. (christoffel (G:real^N->real^N^N) y (basis i) (basis j))$k *
                 ((phi1:real->real)((f:real^N->real) y) * rfa_d1 f y (basis k))) =
          phi1(f y) * sum(1..dimindex(:N))
                        (\k. (christoffel G y (basis i) (basis j))$k * rfa_d1 f y (basis k))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum(1..dimindex(:N))
     (\i. sum(1..dimindex(:N))
       (\j. (phi1:real->real)((f:real^N->real) y) *
            (matrix_inv((G:real^N->real^N^N) y)$i$j *
             (rfa_d2 f y (basis i) (basis j) -
              sum(1..dimindex(:N))
               (\k. (christoffel G y (basis i) (basis j))$k * rfa_d1 f y (basis k)))) +
            (phi2:real->real)(f y) *
            (matrix_inv(G y)$i$j * rfa_d1 f y (basis i) * rfa_d1 f y (basis j))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[SUM_ADD_NUMSEG; SUM_LMUL]]);;

let RFA_LGRAD2_COMPOSE = prove
 (`!U (G:real^N->real^N^N) f phi phi1 y.
     open U /\ smooth_map_on U (\z. lift(f z)) /\ y IN U /\
     (phi has_real_derivative phi1) (atreal (f y))
     ==> lgrad2 G (\z. phi(f z)) y = phi1 pow 2 * lgrad2 G f y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RFA_LGRAD2_D1; rfa_lginner] THEN
  SUBGOAL_THEN
   `!h. rfa_d1 (\z. (phi:real->real)((f:real^N->real) z)) y h = phi1 * rfa_d1 f y h`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC RFA_D1_COMPOSE_AT THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Cauchy-Schwarz for the gradient inner product, and the                    *)
(* gradient bound lgrad2 |T|^2 <= 4 |T|^2 |nabla T|^2 for tensor fields.     *)
(* ========================================================================= *)

let RFA_BILIN_SUM = prove
 (`!(A:real^N^N) (x:num->real) (z:num->real).
     sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j. A$i$j * x i * z j)) =
     ((lambda i. x i):real^N) dot (A ** ((lambda i. z i):real^N))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dot; matrix_vector_mul] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  BETA_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  BETA_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC);;

let RFA_LGINNER_CS = prove
 (`!U (G:real^N->real^N^N) f g y.
     metric_field U G /\ y IN U
     ==> abs(rfa_lginner G f g y) <= sqrt(lgrad2 G f y) * sqrt(lgrad2 G g y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
         LRG_METRIC_INV_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S:real^N^N` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[RFA_LGRAD2_D1; rfa_lginner; RFA_BILIN_SUM] THEN
  ASM_REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
  REWRITE_TAC[GSYM NORM_POW_2] THEN
  SIMP_TAC[POW_2_SQRT; NORM_POS_LE; NORM_CAUCHY_SCHWARZ_ABS]);;

let RFA_QUAD_FRAME = prove
 (`!(S:real^N^N) (x:num->real).
     sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b. (transp S ** S)$a$b * x a * x b)) =
     sum(1..dimindex(:N)) (\p. (sum(1..dimindex(:N)) (\a. S$p$a * x a)) pow 2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LRG_QUADFORM_SUM; GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
  REWRITE_TAC[dot; REAL_POW_2] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `p:num` THEN STRIP_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN
   `((S:real^N^N) ** ((lambda i. (x:num->real) i):real^N))$p =
    sum(1..dimindex(:N)) (\a. S$p$a * x a)`
  (fun th -> REWRITE_TAC[th]) THEN
  ASM_SIMP_TAC[matrix_vector_mul; LAMBDA_BETA] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[LAMBDA_BETA]);;

let RFA_FIX_SLOT_LINEAR = prove
 (`!k U (G:real^N->real^N^N) tf sf y (S:real^N^N) p.
     ltensor_field (k + 1) U sf /\ y IN U /\ 1 <= p /\ p <= dimindex(:N)
     ==> ltinner k G tf (\z u. sf z (\m. if m = k + 1 then transp S ** basis p else u m)) y =
         sum(1..dimindex(:N))
           (\a. S$p$a * ltinner k G tf (\z u. sf z (\m. if m = k + 1 then basis a else u m)) y)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `ltinner k (G:real^N->real^N^N) tf
      (\z u. sum(1..dimindex(:N))
               (\a. (S:real^N^N)$p$a *
                    (sf:real^N->(num->real^N)->real) z
                      (\m. if m = k + 1 then basis a else u m))) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFA_LTINNER_RLOCAL THEN X_GEN_TAC `u:num->real^N` THEN
    REWRITE_TAC[] THEN
    UNDISCH_TAC `ltensor_field (k + 1) U (sf:real^N->(num->real^N)->real)` THEN
    REWRITE_TAC[ltensor_field] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`k + 1`; `u:num->real^N`] o CONJUNCT2) THEN
    REWRITE_TAC[ARITH_RULE `1 <= k + 1 /\ k + 1 <= k + 1`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`(sf:real^N->(num->real^N)->real) y`; `k + 1`; `u:num->real^N`;
                   `transp(S:real^N^N) ** basis p`] LRG_SLOT_EXPAND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    BETA_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC LRG_TRANSP_BASIS_COMPONENT THEN ASM_REWRITE_TAC[];
    SIMP_TAC[RFA_LTINNER_RSUM; FINITE_NUMSEG; RFA_LTINNER_RCMUL]]);;

let RFA_FIX_SLOT_NORM_SUM = prove
 (`!k U (G:real^N->real^N^N) sf y (S:real^N^N).
     ltensor_field (k + 1) U sf /\ (!u. smooth_map_on U (\x. lift(sf x u))) /\ y IN U /\
     matrix_inv(G y) = transp S ** S
     ==> sum(1..dimindex(:N))
           (\p. ltnorm2 k G (\z u. sf z (\m. if m = k + 1 then transp S ** basis p
                                             else u m)) y) =
         ltnorm2 (k + 1) G sf y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k + 1`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `sf:real^N->(num->real^N)->real`; `y:real^N`; `S:real^N^N`]
         LRG_LTNORM2_SQUARES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[LRG_SUM_INDEX_TUPLES_SUC] THEN
  SUBGOAL_THEN
   `!p. ltnorm2 k (G:real^N->real^N^N)
          (\z u. (sf:real^N->(num->real^N)->real) z
                   (\m. if m = k + 1 then transp(S:real^N^N) ** basis p else u m)) y =
        sum (index_tuples k (:N))
            (\i. (sf y (\m. if m = k + 1 then transp(S:real^N^N) ** basis p
                            else transp S ** basis(i m))) pow 2)`
  (fun th -> REWRITE_TAC[th]) THENL
   [X_GEN_TAC `p:num` THEN
    MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                   `\z u. (sf:real^N->(num->real^N)->real) z
                            (\m. if m = k + 1 then transp(S:real^N^N) ** basis p
                                 else u m)`;
                   `y:real^N`; `S:real^N^N`] LRG_LTNORM2_SQUARES) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `sf:real^N->(num->real^N)->real`;
                     `transp(S:real^N^N) ** basis p`] RFA_FIX_SLOT_FIELD) THEN
      ASM_SIMP_TAC[];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV
   [MATCH_MP SUM_SWAP (CONJ (SPECL [`1`; `dimindex(:N)`] FINITE_NUMSEG)
                            (ISPEC `k:num` (INST_TYPE [`:N`,`:N`] LRG_INDEX_TUPLES_FINITE)))] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN BETA_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

let RFA_LGRAD2_LTNORM2_LE = prove
 (`!k U (G:real^N->real^N^N) tf y.
     metric_field U G /\ ltensor_field k U tf /\
     (!u. smooth_map_on U (\x. lift(tf x u))) /\ y IN U
     ==> lgrad2 G (ltnorm2 k G tf) y <=
         &4 * ltnorm2 k G tf y * ltnorm2 (k + 1) G (lnabla k G tf) y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`] LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
         LRG_METRIC_INV_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S:real^N^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!a. rfa_d1 (ltnorm2 k (G:real^N->real^N^N) tf) y (basis a) =
        &2 * ltinner k G tf
               (\z u. lnabla k G tf z (\m. if m = k + 1 then basis a else u m)) y`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[rfa_d1] THEN MATCH_MP_TAC RFA_DNORM2_FORM THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[RFA_LGRAD2_D1; rfa_lginner] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[BETA_RULE(ISPECL
   [`S:real^N^N`;
    `\a. &2 * ltinner k (G:real^N->real^N^N) tf
               (\z u. lnabla k G tf z (\m. if m = k + 1 then basis a else u m)) y`]
   RFA_QUAD_FRAME)] THEN
  SUBGOAL_THEN
   `!p. 1 <= p /\ p <= dimindex(:N)
        ==> sum(1..dimindex(:N))
              (\a. (S:real^N^N)$p$a *
                   &2 * ltinner k (G:real^N->real^N^N) tf
                          (\z u. lnabla k G tf z (\m. if m = k + 1 then basis a else u m))
                          y) =
            &2 * ltinner k G tf
                   (\z u. lnabla k G tf z (\m. if m = k + 1 then transp S ** basis p
                                               else u m)) y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                   `tf:real^N->(num->real^N)->real`;
                   `lnabla k (G:real^N->real^N^N) tf`; `y:real^N`; `S:real^N^N`; `p:num`]
           RFA_FIX_SLOT_LINEAR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    REPEAT STRIP_TAC THEN BETA_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(1..dimindex(:N))
     (\p. &4 * ltnorm2 k (G:real^N->real^N^N) tf y *
          ltnorm2 k G (\z u. lnabla k G tf z (\m. if m = k + 1
                                                   then transp(S:real^N^N) ** basis p
                                                   else u m)) y)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[REAL_POW_MUL] THEN
    CONV_TAC(LAND_CONV(LAND_CONV REAL_RAT_REDUCE_CONV)) THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC RFA_LTINNER_CAUCHY_SCHWARZ THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `lnabla k (G:real^N->real^N^N) tf`;
                   `transp(S:real^N^N) ** basis p`] RFA_FIX_SLOT_FIELD) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lnabla k (G:real^N->real^N^N) tf`; `y:real^N`; `S:real^N^N`]
         RFA_FIX_SLOT_NORM_SUM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

let RFA_LGRAD2_RMD_LE = prove
 (`!j U (G:real^N->real^N^N) y.
     metric_field U G /\ y IN U
     ==> lgrad2 G (lrm_deriv_norm2 j G) y <=
         &4 * lrm_deriv_norm2 j G y * lrm_deriv_norm2 (j + 1) G y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `lrm_deriv_norm2 j (G:real^N->real^N^N) =
    ltnorm2 (4 + j) G (lnabla_iter 4 j G (lrm4 G))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; lrm_deriv_norm2]; ALL_TAC] THEN
  REWRITE_TAC[lrm_deriv_norm2] THEN
  SUBGOAL_THEN
   `lnabla_iter 4 (j + 1) (G:real^N->real^N^N) (lrm4 G) =
    lnabla (4 + j) G (lnabla_iter 4 j G (lrm4 G))`
  SUBST1_TAC THENL [REWRITE_TAC[GSYM ADD1; lnabla_iter]; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `4 + j + 1 = (4 + j) + 1`] THEN
  MATCH_MP_TAC RFA_LGRAD2_LTNORM2_LE THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`4`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lrm4 (G:real^N->real^N^N)`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_SIMP_TAC[LRM4_TENSOR_FIELD]);;

(* ========================================================================= *)
(* The Bernstein quantity F = (B + |nabla^(m-1) Rm|^2)                       *)
(* |nabla^m Rm|^2 along a local Ricci flow satisfies                        *)
(* dF/dt <= Lap F - delta F^2 + D when the lower orders are bounded         *)
(* (CLN Lemma 6.16 for m = 1; the same computation at every order).         *)
(* ========================================================================= *)

let RFA_BERN_ALG = prove
 (`!u v w2 du dv Lu Lv Ig A2 B D1 D2.
     &0 <= u /\ u <= A2 /\ &0 <= v /\ &0 <= w2 /\ &0 <= D2 /\ &0 < B /\
     &8 * A2 <= B /\
     du <= Lu - &2 * v + D1 /\ dv <= Lv - &2 * w2 + D2 * (&1 + v) /\
     Ig pow 2 <= &16 * u * v pow 2 * w2
     ==> du * v + (B + u) * dv <=
         (Lu * v + (B + u) * Lv + &2 * Ig) -
         ((B + u) * v) pow 2 / (&2 * (B + A2) pow 2) +
         (D1 + (B + A2) * D2) pow 2 / &2 + (B + A2) * D2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < B + A2 /\ &0 <= B + u /\ B + u <= B + A2` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `du * v <= (Lu - &2 * v + D1) * v` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(B + u) * dv <= (B + u) * (Lv - &2 * w2 + D2 * (&1 + v))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `--(&2 * Ig) <= v pow 2 + &16 * u * w2` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `abs(&2 * Ig) <= x ==> --(&2 * Ig) <= x`) THEN
    SUBGOAL_THEN `&0 <= v pow 2 + &16 * u * w2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `abs x <= abs y /\ &0 <= y ==> abs x <= y`) THEN
    ASM_REWRITE_TAC[REAL_LE_SQUARE_ABS] THEN
    MP_TAC(SPEC `v pow 2 - &16 * u * w2` REAL_LE_POW_2) THEN
    UNDISCH_TAC `Ig pow 2 <= &16 * u * v pow 2 * w2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&14 * u - &2 * B) * w2 <= &0` ASSUME_TAC THENL
   [MP_TAC(SPECL [`&2 * B - &14 * u`; `w2:real`] REAL_LE_MUL) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(B + u) * D2 * (&1 + v) <= (B + A2) * D2 * (&1 + v)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(D1 + (B + A2) * D2) * v <= v pow 2 / &2 + (D1 + (B + A2) * D2) pow 2 / &2`
  ASSUME_TAC THENL
   [MP_TAC(SPEC `v - (D1 + (B + A2) * D2)` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `((B + u) * v) pow 2 / (&2 * (B + A2) pow 2) <= v pow 2 / &2` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &2 * (B + A2) pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONV_TAC(LAND_CONV REAL_RAT_REDUCE_CONV) THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REWRITE_TAC[REAL_POW_MUL] THEN
    SUBGOAL_THEN `(B + u) pow 2 * v pow 2 <= (B + A2) pow 2 * v pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC);;

(* Bounds of the reaction terms of the evolution of |nabla^j Rm|^2 at the   *)
(* orders m - 1 and m when the orders below m are bounded.                  *)

let RFA_REACT_LOW = prove
 (`!C (r:num->real) (A:num->real) m.
     &0 <= C /\ (!i. &0 <= r i) /\ (!i. i < m ==> r i <= A i) /\ 1 <= m
     ==> C * sqrt(r(m - 1)) * sum(0..m - 1) (\i. sqrt(r i) * sqrt(r(m - 1 - i))) <=
         C * sqrt(A(m - 1)) * sum(0..m - 1) (\i. sqrt(A i) * sqrt(A(m - 1 - i)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE];
    MATCH_MP_TAC SQRT_MONO_LE THEN ASM_SIMP_TAC[ARITH_RULE `1 <= m ==> m - 1 < m`];
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE];
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[SQRT_POS_LE] THEN CONJ_TAC THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let RFA_REACT_TOP = prove
 (`!C (r:num->real) (A:num->real) m.
     &0 <= C /\ (!i. &0 <= r i) /\ (!i. i < m ==> r i <= A i) /\ 1 <= m
     ==> C * sqrt(r m) * sum(0..m) (\i. sqrt(r i) * sqrt(r(m - i))) <=
         C * (&(m + 1) * sqrt(A 0) +
              sum(0..m) (\i. if 0 < i /\ i < m then sqrt(A i) * sqrt(A(m - i)) else &0)) *
         (&1 + r m)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= r 0 /\ r 0 <= A 0 /\ &0 <= A 0` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[ARITH_RULE `1 <= m ==> 0 < m`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(r:num->real) 0` THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= m ==> 0 < m`];
    ALL_TAC] THEN
  ABBREV_TAC `s = sqrt((r:num->real) m)` THEN
  SUBGOAL_THEN `&0 <= s /\ s pow 2 = (r:num->real) m` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2]; ALL_TAC] THEN
  ABBREV_TAC
   `S = sum(0..m) (\i. if 0 < i /\ i < m then sqrt((A:num->real) i) * sqrt(A(m - i))
                     else &0)` THEN
  SUBGOAL_THEN `!i. i < m ==> &0 <= (A:num->real) i` (LABEL_TAC "Apos") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(r:num->real) i` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    BETA_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LE THEN
    USE_THEN "Apos" MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(0..m) (\i. sqrt((r:num->real) i) * sqrt(r(m - i))) <=
    &(m + 1) * sqrt((A:num->real) 0) * s + S`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `sum(0..m) (\i. sqrt((A:num->real) 0) * s +
                     (if 0 < i /\ i < m then sqrt(A i) * sqrt(A(m - i)) else &0))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
      ASM_CASES_TAC `i = 0` THENL
       [ASM_REWRITE_TAC[SUB_0; LT_REFL] THEN
        MATCH_MP_TAC(REAL_ARITH `x <= y ==> x <= y + &0`) THEN EXPAND_TAC "s" THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[SQRT_POS_LE; SQRT_MONO_LE];
        ALL_TAC] THEN
      ASM_CASES_TAC `i:num = m` THENL
       [ASM_REWRITE_TAC[SUB_REFL; LT_REFL] THEN
        MATCH_MP_TAC(REAL_ARITH `x <= y ==> x <= y + &0`) THEN EXPAND_TAC "s" THEN
        GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[SQRT_POS_LE; SQRT_MONO_LE];
        ALL_TAC] THEN
      SUBGOAL_THEN `0 < i /\ i < m` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ x <= y ==> x <= a + y`) THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[SQRT_POS_LE] THEN CONJ_TAC THEN
      MATCH_MP_TAC SQRT_MONO_LE THEN ASM_SIMP_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "S" THEN REWRITE_TAC[SUM_ADD_NUMSEG; SUM_CONST_NUMSEG] THEN
    REWRITE_TAC[ARITH_RULE `(m + 1) - 0 = m + 1`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `s <= &1 + s pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `s - &1 / &2` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &(m + 1) * sqrt((A:num->real) 0)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POS; SQRT_POS_LE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `s * (&(m + 1) * sqrt((A:num->real) 0) * s + S)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `S * s <= S * (&1 + s pow 2)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(&(m + 1) * sqrt((A:num->real) 0)) * s pow 2 <=
                (&(m + 1) * sqrt(A 0)) * (&1 + s pow 2)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `s pow 2 = (r:num->real) m` THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

let RFA_RMD_SMOOTH = prove
 (`!j U (G:real^N->real^N^N).
     metric_field U G ==> smooth_map_on U (\z. lift(lrm_deriv_norm2 j G z))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lrm_deriv_norm2] THEN
  MATCH_MP_TAC LRG_LTNORM2_SMOOTH THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`4`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lrm4 (G:real^N->real^N^N)`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_SIMP_TAC[LRM4_TENSOR_FIELD]);;

let RFA_RMD_POS = prove
 (`!j U (G:real^N->real^N^N) y.
     metric_field U G /\ y IN U ==> &0 <= lrm_deriv_norm2 j G y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lrm_deriv_norm2] THEN
  MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`4`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lrm4 (G:real^N->real^N^N)`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_SIMP_TAC[LRM4_TENSOR_FIELD]);;

(* The product rule for llap applied to the Bernstein quantity.             *)

let RFA_LLAP_BERN = prove
 (`!U (G:real^N->real^N^N) u v B y.
     metric_field U G /\ smooth_map_on U (\z. lift(u z)) /\
     smooth_map_on U (\z. lift(v z)) /\ y IN U
     ==> llap G (\z. (B + u z) * v z) y =
         llap G u y * v y + (B + u y) * llap G v y + &2 * rfa_lginner G u v y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U (\z. lift(B + (u:real^N->real) z))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `\z:real^N. lift B`; `\z. lift((u:real^N->real) z)`]
           SMOOTH_MAP_ON_LIFT_ADD) THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; LIFT_DROP];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `\z. B + (u:real^N->real) z`;
                 `v:real^N->real`; `y:real^N`] RFA_LLAP_MUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `\z:real^N. B:real`;
                 `u:real^N->real`; `y:real^N`] RFA_LLAP_ADD) THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; RFA_LLAP_CONST] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `rfa_lginner G (\z. B + (u:real^N->real) z) v y = rfa_lginner (G:real^N->real^N^N) u v y`
  SUBST1_TAC THENL
   [REWRITE_TAC[rfa_lginner] THEN
    SUBGOAL_THEN `!h. rfa_d1 (\z. B + (u:real^N->real) z) y h = rfa_d1 u y h`
    (fun th -> REWRITE_TAC[th]) THEN
    GEN_TAC THEN
    MP_TAC(ISPECL [`\z:real^N. B:real`; `u:real^N->real`; `y:real^N`; `h:real^N`]
           RFA_D1_ADD_AT) THEN
    REWRITE_TAC[RFA_D1_CONST; REAL_ADD_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[DIFFERENTIABLE_CONST] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    REAL_ARITH_TAC]);;

(* The Bernstein inequality along a local Ricci flow at one point.          *)

let RFA_BERN_FLOW = prove
 (`!m (A:num->real) B.
     1 <= m /\ (!i. &0 <= A i) /\ &0 < B /\ &8 * A(m - 1) <= B
     ==> ?D. !U a b (G:real->real^N->real^N^N) t y.
               lricci_flow U a b G /\ a < t /\ t < b /\ y IN U /\
               (!i. i < m ==> lrm_deriv_norm2 i (G t) y <= A i)
               ==> ?dF. ((\s. (B + lrm_deriv_norm2 (m - 1) (G s) y) *
                              lrm_deriv_norm2 m (G s) y) has_real_derivative dF)
                        (atreal t) /\
                        dF <= llap (G t) (\z. (B + lrm_deriv_norm2 (m - 1) (G t) z) *
                                             lrm_deriv_norm2 m (G t) z) y -
                              ((B + lrm_deriv_norm2 (m - 1) (G t) y) *
                               lrm_deriv_norm2 m (G t) y) pow 2 /
                              (&2 * (B + A(m - 1)) pow 2) + D`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_CHOOSE_THEN `C1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ev1"))
    (SPEC `m - 1` RFA_LRM_DERIV_NORM2_EVOLUTION) THEN
  X_CHOOSE_THEN `C2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ev2"))
    (SPEC `m:num` RFA_LRM_DERIV_NORM2_EVOLUTION) THEN
  ABBREV_TAC
   `D1 = C1 * sqrt((A:num->real)(m - 1)) *
         sum(0..m - 1) (\i. sqrt(A i) * sqrt(A(m - 1 - i)))` THEN
  ABBREV_TAC
   `D2 = C2 * (&(m + 1) * sqrt((A:num->real) 0) +
               sum(0..m) (\i. if 0 < i /\ i < m then sqrt(A i) * sqrt(A(m - i))
                              else &0))` THEN
  SUBGOAL_THEN `&0 <= D2` ASSUME_TAC THENL
   [EXPAND_TAC "D2" THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POS; SQRT_POS_LE]; ALL_TAC] THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE];
    ALL_TAC] THEN
  EXISTS_TAC `(D1 + (B + (A:num->real)(m - 1)) * D2) pow 2 / &2 + (B + A(m - 1)) * D2` THEN
  MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `a:real`; `b:real`;
                       `G:real->real^N->real^N^N`; `t:real`; `y:real^N`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bnd"))))) THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t) /\ open U`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[lricci_flow]; ALL_TAC] THEN
  SUBGOAL_THEN `!j. &0 <= lrm_deriv_norm2 j ((G:real->real^N->real^N^N) t) y`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC RFA_RMD_POS THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. smooth_map_on U (\z. lift(lrm_deriv_norm2 j ((G:real->real^N->real^N^N) t) z))`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC RFA_RMD_SMOOTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `m - 1 + 1 = m` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "ev1" (MP_TAC o SPECL [`U:real^N->bool`; `a:real`; `b:real`;
                                  `G:real->real^N->real^N^N`; `t:real`; `y:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[ASSUME `m - 1 + 1 = m`]] THEN
  DISCH_THEN(X_CHOOSE_THEN `du:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "du"))) THEN
  USE_THEN "ev2" (MP_TAC o SPECL [`U:real^N->bool`; `a:real`; `b:real`;
                                  `G:real->real^N->real^N^N`; `t:real`; `y:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dv:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dv"))) THEN
  EXISTS_TAC
   `(B + lrm_deriv_norm2 (m - 1) ((G:real->real^N->real^N^N) t) y) * dv +
    du * lrm_deriv_norm2 m (G t) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_MUL_ATREAL THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM REAL_ADD_LID] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN
    ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                 `lrm_deriv_norm2 (m - 1) ((G:real->real^N->real^N^N) t)`;
                 `lrm_deriv_norm2 m ((G:real->real^N->real^N^N) t)`; `B:real`; `y:real^N`]
         RFA_LLAP_BERN) THEN
  ASM_REWRITE_TAC[ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(BETA_RULE(ISPECL [`C1:real`;
                           `\i. lrm_deriv_norm2 i ((G:real->real^N->real^N^N) t) y`;
                           `A:num->real`; `m:num`] RFA_REACT_LOW)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "rl")] THEN
  MP_TAC(BETA_RULE(ISPECL [`C2:real`;
                           `\i. lrm_deriv_norm2 i ((G:real->real^N->real^N^N) t) y`;
                           `A:num->real`; `m:num`] RFA_REACT_TOP)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "rt")] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                 `lrm_deriv_norm2 (m - 1) ((G:real->real^N->real^N^N) t)`;
                 `lrm_deriv_norm2 m ((G:real->real^N->real^N^N) t)`; `y:real^N`]
         RFA_LGINNER_CS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "cs") THEN
  MP_TAC(ISPECL [`m - 1`; `U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `y:real^N`]
         RFA_LGRAD2_RMD_LE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "k1") THEN
  MP_TAC(ISPECL [`m:num`; `U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `y:real^N`]
         RFA_LGRAD2_RMD_LE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "k2") THEN
  SUBGOAL_THEN
   `&0 <= lgrad2 ((G:real->real^N->real^N^N) t) (lrm_deriv_norm2 (m - 1) (G t)) y /\
    &0 <= lgrad2 (G t) (lrm_deriv_norm2 m (G t)) y`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LGRAD2_POS THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `du <= llap ((G:real->real^N->real^N^N) t) (lrm_deriv_norm2 (m - 1) (G t)) y -
          &2 * lrm_deriv_norm2 m (G t) y + D1 /\
    dv <= llap (G t) (lrm_deriv_norm2 m (G t)) y -
          &2 * lrm_deriv_norm2 (m + 1) (G t) y + D2 * (&1 + lrm_deriv_norm2 m (G t) y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "D1" THEN USE_THEN "du" MP_TAC THEN USE_THEN "rl" MP_TAC THEN
      REAL_ARITH_TAC;
      EXPAND_TAC "D2" THEN USE_THEN "dv" MP_TAC THEN USE_THEN "rt" MP_TAC THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= lrm_deriv_norm2 (m - 1) ((G:real->real^N->real^N^N) t) y /\
    lrm_deriv_norm2 (m - 1) (G t) y <= (A:num->real)(m - 1) /\
    &0 <= lrm_deriv_norm2 m (G t) y /\ &0 <= lrm_deriv_norm2 (m + 1) (G t) y`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "bnd" MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC
   `Ig = rfa_lginner ((G:real->real^N->real^N^N) t) (lrm_deriv_norm2 (m - 1) (G t))
                     (lrm_deriv_norm2 m (G t)) y` THEN
  ABBREV_TAC `u0 = lrm_deriv_norm2 (m - 1) ((G:real->real^N->real^N^N) t) y` THEN
  ABBREV_TAC `v0 = lrm_deriv_norm2 m ((G:real->real^N->real^N^N) t) y` THEN
  ABBREV_TAC `w0 = lrm_deriv_norm2 (m + 1) ((G:real->real^N->real^N^N) t) y` THEN
  ABBREV_TAC `l1 = lgrad2 ((G:real->real^N->real^N^N) t) (lrm_deriv_norm2 (m - 1) (G t)) y` THEN
  ABBREV_TAC `l2 = lgrad2 ((G:real->real^N->real^N^N) t) (lrm_deriv_norm2 m (G t)) y` THEN
  SUBGOAL_THEN `Ig pow 2 <= &16 * u0 * v0 pow 2 * w0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `l1 * l2` THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(sqrt l1 * sqrt l2) pow 2` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_ABS_POS];
        ASM_SIMP_TAC[REAL_POW_MUL; SQRT_POW_2; REAL_LE_REFL]];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&4 * u0 * v0) * (&4 * v0 * w0)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[];
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u0:real`; `v0:real`; `w0:real`; `du:real`; `dv:real`;
                 `llap ((G:real->real^N->real^N^N) t) (lrm_deriv_norm2 (m - 1) (G t)) y`;
                 `llap ((G:real->real^N->real^N^N) t) (lrm_deriv_norm2 m (G t)) y`;
                 `Ig:real`; `(A:num->real)(m - 1)`; `B:real`; `D1:real`; `D2:real`]
         RFA_BERN_ALG) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC]);;

