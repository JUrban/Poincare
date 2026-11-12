(* ========================================================================= *)
(* Unit pc_cmc_neck: relative almost harmonicity, the compactness argument *)
(* of CM Lemma B.31 (angular energy decay for relatively almost harmonic   *)
(* maps on fixed annuli), the covering argument of CM Prop B.29 for long   *)
(* necks, and the neck energy decay.  First the calculus of affine         *)
(* rescalings z -> y + rho z.                                              *)
(* ========================================================================= *)

needs "src/pc_cmc_remove.ml";;
needs "src/pc_cmc_cyl.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Partial derivatives of rescaled maps.                                     *)
(* ------------------------------------------------------------------------- *)

let CMC_PD_AFFINE = prove
 (`!(g:real^2->real^K) (y:real^2) rho z i.
     g differentiable at (y + rho % z)
     ==> partial_derivative i (\z. g(y + rho % z)) z =
         rho % partial_derivative i g (y + rho % z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z. (g:real^2->real^K)(y + rho % z)) = g o (\z. y + rho % z)` SUBST1_TAC
  THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `(\z:real^2. y + rho % z) differentiable at z` ASSUME_TAC THENL
   [MATCH_MP_TAC DIFFERENTIABLE_ADD THEN REWRITE_TAC[DIFFERENTIABLE_CONST] THEN
    MATCH_MP_TAC DIFFERENTIABLE_CMUL THEN REWRITE_TAC[DIFFERENTIABLE_ID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`i:num`; `\z:real^2. y + rho % z`; `g:real^2->real^K`; `z:real^2`]
                PARTIAL_DERIVATIVE_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `partial_derivative i (\z:real^2. y + rho % z) z = rho % basis i`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[PARTIAL_DERIVATIVE_ADD; DIFFERENTIABLE_CONST; DIFFERENTIABLE_CMUL;
                 DIFFERENTIABLE_ID; PARTIAL_DERIVATIVE_CONST; PARTIAL_DERIVATIVE_CMUL;
                 VECTOR_ADD_LID] THEN
    REWRITE_TAC[PARTIAL_DERIVATIVE_ID];
    ALL_TAC] THEN
  REWRITE_TAC[partial_derivative] THEN
  MP_TAC(MATCH_MP LINEAR_FRECHET_DERIVATIVE
    (ASSUME `(g:real^2->real^K) differentiable at (y + rho % z)`)) THEN
  SIMP_TAC[LINEAR_CMUL]);;

let CMC_SMOOTH_AFFINE = prove
 (`!s (g:real^2->real^K) (y:real^2) rho b p.
     open s /\ smooth_map_on s g
     ==> open {z:real^2 | y + rho % z IN s} /\
         smooth_map_on {z:real^2 | y + rho % z IN s} (\z. g(y + rho % z)) /\
         smooth_map_on {z:real^2 | y + rho % z IN s} (\z. b % (g(y + rho % z) - p))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open {z:real^2 | y + rho % z IN s}` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ADD THEN REWRITE_TAC[CONTINUOUS_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_CMUL THEN REWRITE_TAC[CONTINUOUS_AT_ID];
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `smooth_map_on {z:real^2 | y + rho % z IN s} (\z. (g:real^2->real^K)(y + rho % z))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\z. (g:real^2->real^K)(y + rho % z)) = g o (\z. y + rho % z)` SUBST1_TAC
    THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID];
    ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST]);;

let CMC_IPD_NORMAL = prove
 (`!s (g:real^2->real^K) (y:real^2) rho b p l z.
     open s /\ smooth_map_on s g /\ y + rho % z IN s
     ==> iterated_partial l (\z. b % (g(y + rho % z) - p)) z =
         if l = [] then b % (g(y + rho % z) - p)
         else (b * rho pow (LENGTH l)) % iterated_partial l g (y + rho % z)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `g:real^2->real^K`; `y:real^2`; `rho:real`; `b:real`;
                 `p:real^K`] CMC_SMOOTH_AFFINE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SPEC_TAC(`z:real^2`,`z:real^2`) THEN SPEC_TAC(`l:num list`,`l:num list`) THEN
  LIST_INDUCT_TAC THENL [REWRITE_TAC[iterated_partial]; ALL_TAC] THEN
  X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
  REWRITE_TAC[iterated_partial; NOT_CONS_NIL; LENGTH; real_pow] THEN
  ABBREV_TAC `Ts = {z:real^2 | y + rho % z IN s}` THEN
  SUBGOAL_THEN `(z:real^2) IN Ts` ASSUME_TAC THENL
   [EXPAND_TAC "Ts" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  ASM_CASES_TAC `t:num list = []` THENL
   [ASM_REWRITE_TAC[iterated_partial; LENGTH; real_pow; REAL_MUL_RID] THEN
    SUBGOAL_THEN `(\z. (g:real^2->real^K)(y + rho % z)) differentiable at z /\
                  (\z:real^2. (p:real^K)) differentiable at z /\
                  g differentiable at (y + rho % z)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[DIFFERENTIABLE_CONST] THEN CONJ_TAC THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
       [EXISTS_TAC `Ts:real^2->bool`; EXISTS_TAC `s:real^2->bool`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(\z. (g:real^2->real^K)(y + rho % z) - p) differentiable at z`
    ASSUME_TAC THENL [MATCH_MP_TAC DIFFERENTIABLE_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`h:num`; `b:real`; `\z. (g:real^2->real^K)(y + rho % z) - p`; `z:real^2`]
                  PARTIAL_DERIVATIVE_CMUL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`h:num`; `\z. (g:real^2->real^K)(y + rho % z)`; `\z:real^2. (p:real^K)`;
                   `z:real^2`] PARTIAL_DERIVATIVE_SUB) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[CMC_PD_AFFINE; PARTIAL_DERIVATIVE_CONST; VECTOR_SUB_RZERO;
                 VECTOR_MUL_ASSOC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `partial_derivative h (iterated_partial t (\z. b % ((g:real^2->real^K)(y + rho % z) - p))) z =
    partial_derivative h (\z. (b * rho pow LENGTH t) % iterated_partial t g (y + rho % z)) z`
  SUBST1_TAC THENL
   [MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN EXISTS_TAC `Ts:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z':real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z':real^2`) THEN
    ANTS_TAC THENL [UNDISCH_TAC `(z':real^2) IN Ts` THEN EXPAND_TAC "Ts" THEN
                    REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on s (iterated_partial t (g:real^2->real^K))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_ITERATED_PARTIAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `iterated_partial t (g:real^2->real^K)`; `y:real^2`;
                 `rho:real`; `b:real`; `p:real^K`] CMC_SMOOTH_AFFINE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\z. iterated_partial t (g:real^2->real^K) (y + rho % z)) differentiable at z /\
                iterated_partial t g differentiable at (y + rho % z)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `Ts:real^2->bool`; EXISTS_TAC `s:real^2->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:num`; `b * rho pow LENGTH (t:num list)`;
                 `\z. iterated_partial t (g:real^2->real^K) (y + rho % z)`; `z:real^2`]
                PARTIAL_DERIVATIVE_CMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[CMC_PD_AFFINE; VECTOR_MUL_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Change of variables under the similarities z -> y + rho z.              *)
(* ------------------------------------------------------------------------- *)

let CMC_SIM_IMAGE_INV = prove
 (`!(y:real^2) rho (E:real^2->bool).
     ~(rho = &0)
     ==> IMAGE (\x. inv rho % x + --(inv rho % y)) (IMAGE (\z. y + rho % z) E) = E`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM IMAGE_ID] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; VECTOR_MUL_LID] THEN VECTOR_ARITH_TAC);;

let CMC_SIM_INTEGRAL = prove
 (`!(f:real^2->real^N) (y:real^2) rho E.
     &0 < rho /\ f integrable_on (IMAGE (\z. y + rho % z) E)
     ==> (\z. f(y + rho % z)) integrable_on E /\
         integral E (\z. f(y + rho % z)) =
         inv(rho pow 2) % integral (IMAGE (\z. y + rho % z) E) f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP INTEGRABLE_INTEGRAL) THEN
  DISCH_THEN(MP_TAC o SPECL [`rho:real`; `y:real^2`] o
    MATCH_MP (REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_AFFINITY)) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NZ; CMC_SIM_IMAGE_INV; DIMINDEX_2;
               REAL_ARITH `&0 < rho ==> abs rho = rho`] THEN
  SUBGOAL_THEN `(\x. (f:real^2->real^N)(rho % x + y)) = (\z. f(y + rho % z))` SUBST1_TAC
  THENL [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN VECTOR_ARITH_TAC;
         ALL_TAC] THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[integrable_on] THEN EXISTS_TAC
     `inv(rho pow 2) % integral (IMAGE (\z. y + rho % z) E) (f:real^2->real^N)` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC INTEGRAL_UNIQUE THEN ASM_REWRITE_TAC[]]);;

let CMC_SIM_MEASURABLE = prove
 (`!(f:real^2->real^N) (y:real^2) rho E.
     &0 < rho /\ f measurable_on (IMAGE (\z. y + rho % z) E)
     ==> (\z. f(y + rho % z)) measurable_on E`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z. (f:real^2->real^N)(y + rho % z)) = (\x. f(y + x)) o (\z. rho % z)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\z:real^2. rho % z`; `\x. (f:real^2->real^N)(y + x)`; `E:real^2->bool`]
                MEASURABLE_ON_LINEAR_IMAGE_EQ) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LINEAR_SCALING] THEN REPEAT GEN_TAC THEN
    ASM_SIMP_TAC[VECTOR_MUL_LCANCEL; REAL_LT_IMP_NZ];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC MEASURABLE_ON_TRANSLATION THEN
  UNDISCH_TAC `(f:real^2->real^N) measurable_on IMAGE (\z. y + rho % z) E` THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF]);;

let CMC_SIM_LSPACE = prove
 (`!(f:real^2->real^N) (y:real^2) rho E.
     &0 < rho /\ f IN lspace (IMAGE (\z. y + rho % z) E) (&2)
     ==> (\z. f(y + rho % z)) IN lspace E (&2) /\
         lnorm E (&2) (\z. f(y + rho % z)) pow 2 =
         inv(rho pow 2) * lnorm (IMAGE (\z. y + rho % z) E) (&2) f pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x. lift(norm((f:real^2->real^N) x) pow 2)) integrable_on
                IMAGE (\z. y + rho % z) E` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. lift(norm((f:real^2->real^N) x) pow 2)`; `y:real^2`; `rho:real`;
                 `E:real^2->bool`] CMC_SIM_INTEGRAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\z. (f:real^2->real^N)(y + rho % z)) IN lspace E (&2)` ASSUME_TAC THENL
   [REWRITE_TAC[lspace; IN_ELIM_THM; RPOW_POW] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CMC_SIM_MEASURABLE THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(f:real^2->real^N) IN lspace (IMAGE (\z. y + rho % z) E) (&2)` THEN
    SIMP_TAC[lspace; IN_ELIM_THM];
    ASM_REWRITE_TAC[]] THEN
  ASM_SIMP_TAC[WAN_SOB_LNORM2_SQ] THEN ASM_REWRITE_TAC[DROP_CMUL]);;

let CMC_SIM_NORM = prove
 (`!(y:real^2) rho a z.
     &0 < rho ==> norm((y + rho % z) - (y + rho % a)) = rho * norm(z - a)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VECTOR_ARITH `((y:real^2) + rho % z) - (y + rho % a) = rho % (z - a)`] THEN
  ASM_SIMP_TAC[NORM_MUL; REAL_ARITH `&0 < rho ==> abs rho = rho`]);;

let CMC_SIM_SURJ = prove
 (`!(y:real^2) rho x. &0 < rho ==> y + rho % (inv rho % (x - y)) = x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN VECTOR_ARITH_TAC);;

let CMC_SIM_BALL = prove
 (`!(y:real^2) rho a r.
     &0 < rho ==> IMAGE (\z. y + rho % z) (ball(a,r)) = ball(y + rho % a,rho * r)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^2` THEN
  REWRITE_TAC[IN_IMAGE; IN_BALL] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `z:real^2` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist] THEN ASM_SIMP_TAC[CMC_SIM_NORM] THEN
    ASM_SIMP_TAC[REAL_LT_LMUL_EQ] THEN ASM_MESON_TAC[dist; DIST_SYM];
    DISCH_TAC THEN EXISTS_TAC `inv rho % ((x:real^2) - y)` THEN
    ASM_SIMP_TAC[CMC_SIM_SURJ] THEN
    MP_TAC(ISPECL [`y:real^2`; `rho:real`; `a:real^2`; `inv rho % ((x:real^2) - y)`]
                  CMC_SIM_NORM) THEN
    ASM_SIMP_TAC[CMC_SIM_SURJ] THEN DISCH_TAC THEN
    UNDISCH_TAC `dist(y + rho % a,x:real^2) < rho * r` THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[dist] THEN
    ASM_SIMP_TAC[REAL_LT_LMUL_EQ] THEN MESON_TAC[NORM_SUB]]);;

let CMC_SIM_ANN = prove
 (`!(y:real^2) rho a r1 r2.
     &0 < rho
     ==> IMAGE (\z. y + rho % z) (cmc_ann a r1 r2) = cmc_ann (y + rho % a) (rho * r1) (rho * r2)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^2` THEN
  REWRITE_TAC[IN_IMAGE; cmc_ann; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `z:real^2` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
    ASM_SIMP_TAC[CMC_SIM_NORM; REAL_LT_LMUL_EQ];
    DISCH_TAC THEN EXISTS_TAC `inv rho % ((x:real^2) - y)` THEN
    ASM_SIMP_TAC[CMC_SIM_SURJ] THEN
    MP_TAC(ISPECL [`y:real^2`; `rho:real`; `a:real^2`; `inv rho % ((x:real^2) - y)`]
                  CMC_SIM_NORM) THEN
    ASM_SIMP_TAC[CMC_SIM_SURJ] THEN DISCH_TAC THEN
    UNDISCH_TAC `rho * r1 < norm((x:real^2) - (y + rho % a)) /\
                 norm(x - (y + rho % a)) < rho * r2` THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_LT_LMUL_EQ]]);;

(* ------------------------------------------------------------------------- *)
(* Limits of the coefficients of the harmonic map equations.                 *)
(* ------------------------------------------------------------------------- *)

let CMC_LINEAR_EXPAND = prove
 (`!(f:real^K->real^M) x.
     linear f ==> f x = vsum(1..dimindex(:K)) (\k. x$k % f(basis k))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
  ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL]);;

let CMC_BILIN_EXPAND = prove
 (`!(B:real^K->real^K->real^M) a b.
     bilinear B
     ==> B a b = vsum(1..dimindex(:K))
                   (\k. a$k % vsum(1..dimindex(:K)) (\l. b$l % B (basis k) (basis l)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [bilinear]) THEN
  MP_TAC(ISPECL [`\x:real^K. (B:real^K->real^K->real^M) x b`; `a:real^K`]
                CMC_LINEAR_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC CMC_LINEAR_EXPAND THEN ASM_REWRITE_TAC[]);;

let CMC_BILIN_LIM = prove
 (`!(B:real^K->real^K->real^K->real^M) U (y:num->real^K) y0 u u0 v v0.
     open U /\ (!z. z IN U ==> bilinear (B z)) /\
     (!a b. (\z. B z a b) continuous_on U) /\
     y0 IN U /\ (y --> y0) sequentially /\ (u --> u0) sequentially /\
     (v --> v0) sequentially
     ==> ((\j. B (y j) (u j) (v j)) --> B y0 u0 v0) sequentially`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `eventually (\j. (y:num->real^K) j IN U) sequentially` ASSUME_TAC THENL
   [UNDISCH_TAC `((y:num->real^K) --> y0) sequentially` THEN
    REWRITE_TAC[tendsto] THEN
    MP_TAC(ISPEC `U:real^K->bool` OPEN_CONTAINS_BALL) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `y0:real^K`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
    X_GEN_TAC `j:num` THEN REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `ball(y0:real^K,e) SUBSET U` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\j. vsum(1..dimindex(:K))
                    (\k. ((u:num->real^K) j)$k %
                         vsum(1..dimindex(:K))
                           (\l. ((v:num->real^K) j)$l %
                                (B:real^K->real^K->real^K->real^M) (y j) (basis k) (basis l)))` THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `eventually (\j. (y:num->real^K) j IN U) sequentially` THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
    X_GEN_TAC `j:num` THEN REWRITE_TAC[] THEN DISCH_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC CMC_BILIN_EXPAND THEN ASM_SIMP_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(B:real^K->real^K->real^K->real^M) y0 u0 v0 =
    vsum(1..dimindex(:K))
      (\k. (u0:real^K)$k % vsum(1..dimindex(:K))
                             (\l. (v0:real^K)$l % B y0 (basis k) (basis l)))`
  SUBST1_TAC THENL [MATCH_MP_TAC CMC_BILIN_EXPAND THEN ASM_SIMP_TAC[ETA_AX]; ALL_TAC] THEN
  MATCH_MP_TAC LIM_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`sequentially`;
                 `\j. vsum(1..dimindex(:K))
                        (\l. ((v:num->real^K) j)$l %
                             (B:real^K->real^K->real^K->real^M) ((y:num->real^K) j)
                                (basis k) (basis l))`;
                 `vsum(1..dimindex(:K))
                    (\l. (v0:real^K)$l %
                         (B:real^K->real^K->real^K->real^M) y0 (basis k) (basis l))`;
                 `\j. ((u:num->real^K) j)$k`; `(u0:real^K)$k`]
                LIM_MUL) THEN
  REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC LIM_COMPONENT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC LIM_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `l:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`sequentially`;
                 `\j. (B:real^K->real^K->real^K->real^M) ((y:num->real^K) j) (basis k) (basis l)`;
                 `(B:real^K->real^K->real^K->real^M) y0 (basis k) (basis l)`;
                 `\j. ((v:num->real^K) j)$l`; `(v0:real^K)$l`]
                LIM_MUL) THEN
  REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC LIM_COMPONENT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\z. (B:real^K->real^K->real^K->real^M) z (basis k) (basis l)`;
                 `sequentially`; `y:num->real^K`; `y0:real^K`] LIM_CONTINUOUS_FUNCTION) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT]);;

let CMC_LIM_MATVEC = prove
 (`!(A:num->real^N^M) A0 (v:num->real^N) v0.
     ((\j. vectorize(A j)) --> vectorize A0) sequentially /\ (v --> v0) sequentially
     ==> ((\j. A j ** v j) --> A0 ** v0) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`sequentially`;
                 `\(m:real^(M,N)finite_prod) (x:real^N). matrify m ** x`;
                 `\j. vectorize((A:num->real^N^M) j)`; `v:num->real^N`;
                 `vectorize(A0:real^N^M)`; `v0:real^N`] LIM_BILINEAR) THEN
  ASM_REWRITE_TAC[BILINEAR_MATRIX_VECTOR_MUL; MATRIFY_VECTORIZE]);;

let CMC_TP_LIM = prove
 (`!S (G:real^K->real^K^K) d (q:num->real^K) q0 (a:num->real^K) a0.
     cm_target S G d /\ q0 IN S /\ (q --> q0) sequentially /\ (a --> a0) sequentially
     ==> ((\j. hmr_tp S (q j) ** a j) --> hmr_tp S q0 ** a0) sequentially`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  MATCH_MP_TAC CMC_LIM_MATVEC THEN ASM_REWRITE_TAC[hmr_tp] THEN
  MP_TAC(ISPECL [`(vectorize:real^K^K->real^(K,K)finite_prod) o
                  (\y. jacobian (closest_point S) (at y))`;
                 `sequentially`; `q:num->real^K`; `q0:real^K`] LIM_CONTINUOUS_FUNCTION) THEN
  REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(q0:real^K) IN cm_tube S d` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `((vectorize:real^K^K->real^(K,K)finite_prod) o
                 (\y. jacobian (closest_point S) (at y))) continuous_on cm_tube S d`
  MP_TAC THENL [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; o_DEF]);;

let CMC_CHRIS_LIM = prove
 (`!S (G:real^K->real^K^K) d (q:num->real^K) q0 (a:num->real^K) a0 (b:num->real^K) b0.
     cm_target S G d /\ (q --> q0) sequentially /\ (a --> a0) sequentially /\
     (b --> b0) sequentially
     ==> ((\j. christoffel G (q j) (a j) (b j)) --> christoffel G q0 a0 b0) sequentially`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HMR_METRIC_FIELD) THEN
  MATCH_MP_TAC CMC_BILIN_LIM THEN EXISTS_TAC `(:real^K)` THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CHRISTOFFEL_BILINEAR THEN EXISTS_TAC `(:real^K)` THEN
    ASM_REWRITE_TAC[IN_UNIV];
    REPEAT GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MATCH_MP_TAC LRG_CHRISTOFFEL_SMOOTH THEN ASM_REWRITE_TAC[]]);;

let CMC_BQ_LIM = prove
 (`!S (G:real^K->real^K^K) d (q:num->real^K) q0 (a:num->real^K) a0 (b:num->real^K) b0.
     cm_target S G d /\ q0 IN S /\ (q --> q0) sequentially /\ (a --> a0) sequentially /\
     (b --> b0) sequentially
     ==> ((\j. hmr_bq S G (q j) (a j) (b j)) --> hmr_bq S G q0 a0 b0) sequentially`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMR_BQ_FAMILY) THEN
  MATCH_MP_TAC CMC_BILIN_LIM THEN EXISTS_TAC `cm_tube (S:real^K->bool) d` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `(S:real^K->bool) SUBSET cm_tube S d` THEN
    UNDISCH_TAC `(q0:real^K) IN S` THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Normalized rescaled maps and the harmonic map equations.                  *)
(* ------------------------------------------------------------------------- *)

let cmc_nmap = new_definition
 `cmc_nmap (v:real^2->real^K) (y:real^2) rho c (p:real^K) =
    \z:real^2. inv c % (v(y + rho % z) - p)`;;

let CMC_NMAP_VALUE = prove
 (`!(v:real^2->real^K) y rho c p z.
     ~(c = &0) ==> p + c % cmc_nmap v y rho c p z = v(y + rho % z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cmc_nmap; VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; VECTOR_MUL_LID] THEN VECTOR_ARITH_TAC);;

let CMC_NMAP_IPD = prove
 (`!s (v:real^2->real^K) y rho c p l z.
     open s /\ smooth_map_on s v /\ y + rho % z IN s /\ ~(l = [])
     ==> iterated_partial l (cmc_nmap v y rho c p) z =
         (inv c * rho pow (LENGTH l)) % iterated_partial l v (y + rho % z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cmc_nmap] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `v:real^2->real^K`; `y:real^2`; `rho:real`; `inv c`;
                 `p:real^K`; `l:num list`; `z:real^2`] CMC_IPD_NORMAL) THEN
  ASM_REWRITE_TAC[]);;

let CMC_NMAP_PD = prove
 (`!s (v:real^2->real^K) y rho c p z.
     open s /\ smooth_map_on s v /\ y + rho % z IN s
     ==> (!i. partial_derivative i (cmc_nmap v y rho c p) z =
              (inv c * rho) % partial_derivative i v (y + rho % z)) /\
         hmr_vlap (cmc_nmap v y rho c p) z = (inv c * rho pow 2) % hmr_vlap v (y + rho % z)`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`s:real^2->bool`; `v:real^2->real^K`; `y:real^2`; `rho:real`; `c:real`;
                   `p:real^K`; `[i:num]`; `z:real^2`] CMC_NMAP_IPD) THEN
    ASM_REWRITE_TAC[NOT_CONS_NIL; iterated_partial; LENGTH; REAL_POW_1; ONE] THEN
    REWRITE_TAC[GSYM ONE; REAL_POW_1];
    REWRITE_TAC[hmr_vlap; GSYM VSUM_LMUL] THEN MATCH_MP_TAC VSUM_EQ THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `v:real^2->real^K`; `y:real^2`; `rho:real`; `c:real`;
                   `p:real^K`; `[i:num; i]`; `z:real^2`] CMC_NMAP_IPD) THEN
    ASM_REWRITE_TAC[NOT_CONS_NIL; iterated_partial; LENGTH] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[TWO; ONE]]);;

let CMC_NREP_EQS = prove
 (`!S (G:real^K->real^K^K) d s (v:real^2->real^K) (y:real^2) rho c p z.
     cm_target S G d /\ open s /\ cm_harmonic S G s v /\ &0 < c /\ y + rho % z IN s
     ==> (!i. hmr_tp S (p + c % cmc_nmap v y rho c p z) **
              partial_derivative i (cmc_nmap v y rho c p) z =
              partial_derivative i (cmc_nmap v y rho c p) z) /\
         hmr_tp S (p + c % cmc_nmap v y rho c p z) **
           (hmr_vlap (cmc_nmap v y rho c p) z +
            c % vsum(1..2) (\i. christoffel G (p + c % cmc_nmap v y rho c p z)
                                  (partial_derivative i (cmc_nmap v y rho c p) z)
                                  (partial_derivative i (cmc_nmap v y rho c p) z))) = vec 0 /\
         hmr_vlap (cmc_nmap v y rho c p) z =
           c % vsum(1..2) (\i. hmr_bq S G (p + c % cmc_nmap v y rho c p z)
                                  (partial_derivative i (cmc_nmap v y rho c p) z)
                                  (partial_derivative i (cmc_nmap v y rho c p) z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_harmonic]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  ASM_SIMP_TAC[CMC_NMAP_VALUE; REAL_LT_IMP_NZ] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `v:real^2->real^K`; `y:real^2`; `rho:real`; `c:real`;
                 `p:real^K`; `z:real^2`] CMC_NMAP_PD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (fun th -> REWRITE_TAC[th]) SUBST1_TAC) THEN
  ABBREV_TAC `x:real^2 = y + rho % z` THEN
  SUBGOAL_THEN `(v:real^2->real^K) x IN S` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL] THEN AP_TERM_TAC THEN
    REWRITE_TAC[hmr_tp] THEN MATCH_MP_TAC HMC_TANGENT_PARTIAL THEN
    MAP_EVERY EXISTS_TAC [`G:real^K->real^K^K`; `d:real`; `s:real^2->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HMR_METRIC_FIELD) THEN
  SUBGOAL_THEN `bilinear (christoffel G ((v:real^2->real^K) x)) /\
                bilinear (hmr_bq S G ((v:real^2->real^K) x))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CHRISTOFFEL_BILINEAR THEN EXISTS_TAC `(:real^K)` THEN
      ASM_REWRITE_TAC[IN_UNIV];
      FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o MATCH_MP HMR_BQ_FAMILY) THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!i. christoffel G ((v:real^2->real^K) x) ((inv c * rho) % partial_derivative i v x)
                       ((inv c * rho) % partial_derivative i v x) =
         ((inv c * rho) * (inv c * rho)) %
         christoffel G (v x) (partial_derivative i v x) (partial_derivative i v x)) /\
    (!i. hmr_bq S G ((v:real^2->real^K) x) ((inv c * rho) % partial_derivative i v x)
                    ((inv c * rho) % partial_derivative i v x) =
         ((inv c * rho) * (inv c * rho)) %
         hmr_bq S G (v x) (partial_derivative i v x) (partial_derivative i v x))`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN GEN_TAC THEN
    ASM_SIMP_TAC[BILINEAR_LMUL; BILINEAR_RMUL; VECTOR_MUL_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[VSUM_LMUL; FINITE_NUMSEG] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                   `v:real^2->real^K`; `x:real^2`] HMR_EL_STRONG) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(inv c * rho pow 2) % hmr_vlap (v:real^2->real^K) x +
      c % ((inv c * rho) * (inv c * rho)) %
          vsum(1..2) (\i. christoffel G (v x) (partial_derivative i v x)
                                             (partial_derivative i v x)) =
      (inv c * rho pow 2) %
      (hmr_vlap v x + vsum(1..2) (\i. christoffel G (v x) (partial_derivative i v x)
                                                         (partial_derivative i v x)))`
    SUBST1_TAC THENL
     [REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN AP_TERM_TAC THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD;
      SIMP_TAC[MATRIX_VECTOR_MUL_RMUL; VECTOR_MUL_RZERO]];
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                   `v:real^2->real^K`; `x:real^2`] HMR_PDE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD]);;

let CMC_PREIMAGE_BALL = prove
 (`!(y:real^2) rho a r.
     &0 < rho ==> {z:real^2 | y + rho % z IN ball(y + rho % a,rho * r)} = ball(a,r)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:real^2` THEN
  REWRITE_TAC[IN_ELIM_THM; IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
  REWRITE_TAC[dist] THEN ASM_SIMP_TAC[CMC_SIM_NORM; REAL_LT_LMUL_EQ]);;

let CMC_NREP_CLOSE0 = prove
 (`!(w:real^2->real^K) v (y:real^2) rho a R c mu.
     &0 < rho /\ &0 < R /\ &0 < c /\
     wan_w120 (ball(y + rho % a,rho * R / &8)) (\x. w x - v x) /\
     wan_dir (ball(y + rho % a,rho * R / &8)) (\x. w x - v x) <= mu * c pow 2
     ==> (\z. inv c % (w(y + rho % z) - v(y + rho % z))) IN lspace (ball(a,R / &8)) (&2) /\
         lnorm (ball(a,R / &8)) (&2) (\z. inv c % (w(y + rho % z) - v(y + rho % z))) pow 2
         <= &4 * (R / &8) pow 2 * mu`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x. (w:real^2->real^K) x - v x) IN lspace (ball(y + rho % a,rho * R / &8)) (&2)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `wan_w120 (ball(y + rho % a,rho * R / &8)) (\x. (w:real^2->real^K) x - v x)` THEN
    SIMP_TAC[wan_w120; wan_w12];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lnorm (ball(y + rho % a,rho * R / &8)) (&2) (\x. (w:real^2->real^K) x - v x) pow 2 <=
    &4 * (rho * R / &8) pow 2 * mu * c pow 2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&4 * (rho * R / &8) pow 2 *
                wan_dir (ball(y + rho % a,rho * R / &8)) (\x. (w:real^2->real^K) x - v x)` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`(:2)`; `(:K)`] WAN_POINCARE0) THEN
      REWRITE_TAC[WAN_POINCARE0_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
      EXISTS_TAC `y + rho % a:real^2` THEN ASM_REWRITE_TAC[OPEN_BALL; SUBSET_REFL];
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. (w:real^2->real^K) x - v x`; `y:real^2`; `rho:real`;
                 `ball(a:real^2,R / &8)`] CMC_SIM_LSPACE) THEN
  ASM_SIMP_TAC[CMC_SIM_BALL] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LSPACE_CMUL] THEN
  ASM_SIMP_TAC[LNORM_MUL; REAL_ARITH `~(&2 = &0)`; REAL_POW_MUL] THEN
  SUBGOAL_THEN `abs(inv c) = inv c` SUBST1_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs x = x`) THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv c pow 2 * inv(rho pow 2) * &4 * (rho * R / &8) pow 2 * mu * c pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LE_POW_2];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    UNDISCH_TAC `&0 < c` THEN UNDISCH_TAC `&0 < rho` THEN CONV_TAC REAL_FIELD]);;

let CMC_NREP_CLOSE1 = prove
 (`!S (w:real^2->real^K) v (y:real^2) rho a R c mu i.
     compact S /\ cmc_pmap S w /\ &0 < rho /\ &0 < R /\ &0 < c /\
     smooth_map_on (ball(y + rho % a,rho * R / &8)) v /\
     wan_w12 (ball(y + rho % a,rho * R / &8)) v /\
     wan_dir (ball(y + rho % a,rho * R / &8)) (\x. w x - v x) <= mu * c pow 2 /\
     1 <= i /\ i <= 2
     ==> (\z. (rho / c) % (wan_wd (:real^2) i w (y + rho % z) -
                          partial_derivative i v (y + rho % z)))
         IN lspace (ball(a,R / &8)) (&2) /\
         lnorm (ball(a,R / &8)) (&2)
           (\z. (rho / c) % (wan_wd (:real^2) i w (y + rho % z) -
                            partial_derivative i v (y + rho % z))) pow 2 <= mu`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `w:real^2->real^K`; `v:real^2->real^K`;
                 `ball(y + rho % a:real^2,rho * R / &8)`; `i:num`] CMC_WD_DIFF_SMOOTH) THEN
  ASM_REWRITE_TAC[OPEN_BALL; BOUNDED_BALL] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. wan_wd (:real^2) i (w:real^2->real^K) x - partial_derivative i v x`;
                 `y:real^2`; `rho:real`; `ball(a:real^2,R / &8)`] CMC_SIM_LSPACE) THEN
  ASM_SIMP_TAC[CMC_SIM_BALL] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LSPACE_CMUL] THEN
  ASM_SIMP_TAC[LNORM_MUL; REAL_ARITH `~(&2 = &0)`; REAL_POW_MUL] THEN
  SUBGOAL_THEN `abs(rho / c) = rho / c` SUBST1_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs x = x`) THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(rho / c) pow 2 * inv(rho pow 2) * mu * c pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LE_POW_2] THEN
    ASM_MESON_TAC[REAL_LE_TRANS];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    UNDISCH_TAC `&0 < c` THEN UNDISCH_TAC `&0 < rho` THEN CONV_TAC REAL_FIELD]);;

let CMC_SCALE_BOUND = prove
 (`!c rho R N Cn n.
     &0 < c /\ &0 < rho /\ &0 < R /\ (rho * R / &8) pow n * N <= Cn * c
     ==> (inv c * rho pow n) * N <= Cn * (&8 / R) pow n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (R / &8) pow n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&8 / R) pow n = inv((R / &8) pow n)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_INV; REAL_INV_DIV]; ALL_TAC] THEN
  SUBGOAL_THEN `(inv c * rho pow n) * N = ((rho * R / &8) pow n * N) * inv(c * (R / &8) pow n)`
  SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_MUL; REAL_INV_MUL] THEN
    UNDISCH_TAC `&0 < (R / &8) pow n` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `Cn * inv((R / &8) pow n) = (Cn * c) * inv(c * (R / &8) pow n)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_INV_MUL] THEN UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC);;

let CMC_ZERO_BOUND = prove
 (`!(V:real^2->real^K) a r B.
     &0 < r /\ smooth_map_on (ball(a,r)) V /\ V a = vec 0 /\
     (!x. x IN ball(a,r) ==> norm(partial_derivative 1 V x) <= B /\
                             norm(partial_derivative 2 V x) <= B)
     ==> !z. z IN ball(a,r) ==> norm(V z) <= &2 * B * r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`ball(a:real^2,r)`; `V:real^2->real^K`; `B:real`] CMC_LIP_FROM_PARTIALS) THEN
  ASM_REWRITE_TAC[OPEN_BALL; CONVEX_BALL] THEN
  DISCH_THEN(MP_TAC o SPECL [`z:real^2`; `a:real^2`]) THEN
  ASM_REWRITE_TAC[CENTRE_IN_BALL; VECTOR_SUB_RZERO] THEN
  SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(partial_derivative 1 (V:real^2->real^K) z)` THEN
    REWRITE_TAC[NORM_POS_LE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(z - a:real^2) < r` ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^2) IN ball(a,r)` THEN REWRITE_TAC[IN_BALL; dist] THEN
    MESON_TAC[NORM_SUB];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The normalized rescaled replacement on one ball (CM Lemma B.31, step    *)
(* 4): bounds, closeness to the normalized map, harmonic equations.        *)
(* ------------------------------------------------------------------------- *)

let CMC_NREP = prove
 (`!S (G:real^K->real^K^K) d eL (C:num->real) (w:real^2->real^K) (y:real^2) rho a R c mu.
     cm_target S G d /\ cmc_regc S G eL C /\ cmc_pmap S w /\
     &0 < rho /\ &0 < R /\ &0 < c /\ c pow 2 <= eL /\
     wan_gdir (ball(y + rho % a,rho * R / &8)) G w <= c pow 2 /\
     (!v. cm_minimizer S G (ball(y + rho % a,rho * R / &8)) v /\
          wan_w120 (ball(y + rho % a,rho * R / &8)) (\x. v x - w x)
          ==> wan_dir (ball(y + rho % a,rho * R / &8)) (\x. w x - v x) <= mu * c pow 2)
     ==> ?p (V:real^2->real^K).
           p IN S /\ smooth_map_on (ball(a,R / &8)) V /\ V a = vec 0 /\
           (!z. z IN ball(a,R / &8) ==> p + c % V z IN S) /\
           (!l z. ALL (\i. 1 <= i /\ i <= 2) l /\ ~(l = []) /\ z IN ball(a,R / &16)
                  ==> norm(iterated_partial l V z) <= C (LENGTH l) * (&8 / R) pow (LENGTH l)) /\
           (!z. z IN ball(a,R / &16) ==> norm(V z) <= C 1) /\
           (\z. inv c % (w(y + rho % z) - p) - V z) IN lspace (ball(a,R / &8)) (&2) /\
           lnorm (ball(a,R / &8)) (&2) (\z. inv c % (w(y + rho % z) - p) - V z) pow 2
             <= &4 * (R / &8) pow 2 * mu /\
           (!i. 1 <= i /\ i <= 2
                ==> (\z. (rho / c) % wan_wd (:real^2) i w (y + rho % z) -
                         partial_derivative i V z) IN lspace (ball(a,R / &8)) (&2) /\
                    lnorm (ball(a,R / &8)) (&2)
                      (\z. (rho / c) % wan_wd (:real^2) i w (y + rho % z) -
                           partial_derivative i V z) pow 2 <= mu) /\
           (!z. z IN ball(a,R / &8)
                ==> (!i. hmr_tp S (p + c % V z) ** partial_derivative i V z =
                         partial_derivative i V z) /\
                    hmr_tp S (p + c % V z) **
                      (hmr_vlap V z +
                       c % vsum(1..2) (\i. christoffel G (p + c % V z)
                                             (partial_derivative i V z)
                                             (partial_derivative i V z))) = vec 0 /\
                    hmr_vlap V z =
                      c % vsum(1..2) (\i. hmr_bq S G (p + c % V z)
                                             (partial_derivative i V z)
                                             (partial_derivative i V z)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cmc_regc]) THEN
  SUBGOAL_THEN `&0 < rho * R / &8` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `eL:real`; `C:num->real`;
                 `w:real^2->real^K`; `y + rho % a:real^2`; `rho * R / &8`] CMC_REP_ONE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[REAL_LE_TRANS]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^2->real^K` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `wan_dir (ball(y + rho % a,rho * R / &8)) (\x. (w:real^2->real^K) x - v x)
                <= mu * c pow 2` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `mu:real`)) (concl th))) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ASSUME `cm_harmonic S G (ball(y + rho % a,rho * R / &8)) (v:real^2->real^K)`) THEN
  REWRITE_TAC[cm_harmonic] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z:real^2. z IN ball(a,R / &8) ==> y + rho % z IN ball(y + rho % a,rho * R / &8)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`y:real^2`; `rho:real`; `a:real^2`; `R / &8`] CMC_PREIMAGE_BALL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> GEN_REWRITE_TAC (BINDER_CONV o LAND_CONV o
      RAND_CONV) [GSYM th]) THEN REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^2. z IN ball(a,R / &16) ==> z IN ball(a,R / &8)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL] THEN UNDISCH_TAC `&0 < R` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^2) IN ball(a,R / &8)` ASSUME_TAC THENL
   [REWRITE_TAC[CENTRE_IN_BALL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `p:real^K = v(y + rho % a:real^2)` THEN
  EXISTS_TAC `p:real^K` THEN EXISTS_TAC `cmc_nmap (v:real^2->real^K) y rho c p` THEN
  (* basic facts *)
  SUBGOAL_THEN `(p:real^K) IN S` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (ball(a,R / &8)) (cmc_nmap (v:real^2->real^K) y rho c p)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ball(y + rho % a:real^2,rho * R / &8)`; `v:real^2->real^K`; `y:real^2`;
                   `rho:real`; `inv c`; `p:real^K`] CMC_SMOOTH_AFFINE) THEN
    ASM_SIMP_TAC[OPEN_BALL; CMC_PREIMAGE_BALL; cmc_nmap; ETA_AX];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!z:real^2. z IN ball(a,R / &8)
                ==> p + c % cmc_nmap (v:real^2->real^K) y rho c p z = v(y + rho % z)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMC_NMAP_VALUE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!l z. ALL (\i. 1 <= i /\ i <= 2) l /\ ~(l = []) /\ z IN ball(a,R / &16)
                      ==> norm(iterated_partial l (cmc_nmap (v:real^2->real^K) y rho c p) z)
                          <= C (LENGTH l) * (&8 / R) pow (LENGTH l)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`ball(y + rho % a:real^2,rho * R / &8)`; `v:real^2->real^K`; `y:real^2`;
                   `rho:real`; `c:real`; `p:real^K`; `l:num list`; `z:real^2`] CMC_NMAP_IPD) THEN
    ASM_SIMP_TAC[OPEN_BALL] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[NORM_MUL] THEN
    SUBGOAL_THEN `abs(inv c * rho pow LENGTH (l:num list)) = inv c * rho pow LENGTH l`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs x = x`) THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE; REAL_POW_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC CMC_SCALE_BOUND THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `C (LENGTH (l:num list)) *
                sqrt(wan_gdir (ball(y + rho % a,rho * R / &8)) G (w:real^2->real^K))` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `iterated_partial:num list->(real^2->real^K)->real^2->real^K`))
          (concl th) && can (find_term ((=) `v:real^2->real^K`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`y:real^2`; `rho:real`; `a:real^2`; `R / &16`] CMC_PREIMAGE_BALL) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(rho * R / &8) / &2 = rho * R / &16` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(fun th -> UNDISCH_TAC `(z:real^2) IN ball(a,R / &16)` THEN
        GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM th]) THEN
      REWRITE_TAC[IN_ELIM_THM];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(c pow 2)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE; REAL_LE_REFL]]];
    ASM_REWRITE_TAC[]] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[cmc_nmap] THEN EXPAND_TAC "p" THEN
    REWRITE_TAC[VECTOR_SUB_REFL; VECTOR_MUL_RZERO];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [(* zeroth order *)
    MP_TAC(ISPECL [`cmc_nmap (v:real^2->real^K) y rho c p`; `a:real^2`; `R / &16`;
                   `C 1 * &8 / R`] CMC_ZERO_BOUND) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(a:real^2,R / &8)` THEN
        ASM_REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[];
        REWRITE_TAC[cmc_nmap] THEN EXPAND_TAC "p" THEN
        REWRITE_TAC[VECTOR_SUB_REFL; VECTOR_MUL_RZERO];
        X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN CONJ_TAC THENL
         [FIRST_X_ASSUM(MP_TAC o SPECL [`[1]`; `x:real^2`] o check (fun th ->
            is_forall(concl th) && can (find_term ((=) `C:num->real`)) (concl th) &&
            can (find_term ((=) `R:real`)) (concl th)));
          FIRST_X_ASSUM(MP_TAC o SPECL [`[2]`; `x:real^2`] o check (fun th ->
            is_forall(concl th) && can (find_term ((=) `C:num->real`)) (concl th) &&
            can (find_term ((=) `R:real`)) (concl th)))] THEN
        ASM_REWRITE_TAC[ALL; NOT_CONS_NIL; LENGTH; iterated_partial] THEN
        CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_1]];
      ALL_TAC] THEN
    DISCH_TAC THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^2`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `y = z ==> x <= y ==> x <= z`) THEN
    UNDISCH_TAC `&0 < R` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. inv c % ((w:real^2->real^K)(y + rho % z) - p) - cmc_nmap (v:real^2->real^K) y rho c p z)
    IN lspace (ball(a,R / &8)) (&2) /\
    lnorm (ball(a,R / &8)) (&2)
      (\z. inv c % (w(y + rho % z) - p) - cmc_nmap v y rho c p z) pow 2
    <= &4 * (R / &8) pow 2 * mu`
  (fun th -> REWRITE_TAC[th]) THENL
   [(* closeness of values *)
    SUBGOAL_THEN `(\z. inv c % ((w:real^2->real^K)(y + rho % z) - p) -
                       cmc_nmap (v:real^2->real^K) y rho c p z) =
                  (\z. inv c % (w(y + rho % z) - v(y + rho % z)))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; cmc_nmap] THEN GEN_TAC THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC CMC_NREP_CLOSE0 THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`ball(y + rho % a:real^2,rho * R / &8)`;
                   `\x. (v:real^2->real^K) x - w x`] WAN_W120_NEG) THEN
    ASM_REWRITE_TAC[OPEN_BALL; VECTOR_NEG_SUB];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* closeness of the partials *)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`ball(a:real^2,R / &8)`; `{}:real^2->bool`;
                   `\z. (rho / c) % wan_wd (:real^2) i (w:real^2->real^K) (y + rho % z) -
                        partial_derivative i (cmc_nmap (v:real^2->real^K) y rho c p) z`;
                   `\z. (rho / c) % (wan_wd (:real^2) i (w:real^2->real^K) (y + rho % z) -
                                    partial_derivative i (v:real^2->real^K) (y + rho % z))`;
                   `&2`] WAN_LSPACE_LNORM_SPIKE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[NEGLIGIBLE_EMPTY; DIFF_EMPTY] THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`ball(y + rho % a:real^2,rho * R / &8)`; `v:real^2->real^K`; `y:real^2`;
                     `rho:real`; `c:real`; `p:real^K`; `z:real^2`] CMC_NMAP_PD) THEN
      ASM_SIMP_TAC[OPEN_BALL] THEN DISCH_THEN(K ALL_TAC) THEN
      REWRITE_TAC[VECTOR_SUB_LDISTRIB; real_div] THEN
      REWRITE_TAC[REAL_MUL_SYM];
      DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
    MATCH_MP_TAC CMC_NREP_CLOSE1 THEN EXISTS_TAC `S:real^K->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* equations *)
  X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN MATCH_MP_TAC CMC_NREP_EQS THEN
  MAP_EVERY EXISTS_TAC [`d:real`; `ball(y + rho % a:real^2,rho * R / &8)`] THEN
  ASM_SIMP_TAC[OPEN_BALL]);;

(* ------------------------------------------------------------------------- *)
(* Local limits of the normalized replacements on one ball.                  *)
(* ------------------------------------------------------------------------- *)

let CMC_LIM_CMUL_SEQ = prove
 (`!(c:num->real) c0 (f:num->real^N) l.
     (c ---> c0) sequentially /\ (f --> l) sequentially
     ==> ((\j. c j % f j) --> c0 % l) sequentially`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_MUL THEN ASM_REWRITE_TAC[GSYM TENDSTO_REAL]);;

let CMC_NLOC_EQS = prove
 (`!S (G:real^K->real^K^K) d (V:num->real^2->real^K) U (P:num->real^K) p (c:num->real) c0 z.
     cm_target S G d /\ (P --> p) sequentially /\ (c ---> c0) sequentially /\
     ((\j. V j z) --> U z) sequentially /\
     (!i. 1 <= i /\ i <= 2
          ==> ((\j. partial_derivative i (V j) z) --> partial_derivative i U z) sequentially) /\
     ((\j. hmr_vlap (V j) z) --> hmr_vlap U z) sequentially /\
     (!j. P j + c j % V j z IN S /\
          (!i. hmr_tp S (P j + c j % V j z) ** partial_derivative i (V j) z =
               partial_derivative i (V j) z) /\
          hmr_tp S (P j + c j % V j z) **
            (hmr_vlap (V j) z +
             c j % vsum(1..2) (\i. christoffel G (P j + c j % V j z)
                                     (partial_derivative i (V j) z)
                                     (partial_derivative i (V j) z))) = vec 0 /\
          hmr_vlap (V j) z =
            c j % vsum(1..2) (\i. hmr_bq S G (P j + c j % V j z)
                                     (partial_derivative i (V j) z)
                                     (partial_derivative i (V j) z)))
     ==> p + c0 % U z IN S /\
         (!i. 1 <= i /\ i <= 2
              ==> hmr_tp S (p + c0 % U z) ** partial_derivative i U z =
                  partial_derivative i U z) /\
         hmr_tp S (p + c0 % U z) **
           (hmr_vlap U z +
            c0 % vsum(1..2) (\i. christoffel G (p + c0 % U z)
                                   (partial_derivative i U z) (partial_derivative i U z))) =
         vec 0 /\
         hmr_vlap U z =
           c0 % vsum(1..2) (\i. hmr_bq S G (p + c0 % U z)
                                  (partial_derivative i U z) (partial_derivative i U z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=)
    `hmr_bq:(real^K->bool)->(real^K->real^K^K)->real^K->real^K->real^K->real^K`)) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  SUBGOAL_THEN `((\j. (P:num->real^K) j + c j % (V:num->real^2->real^K) j z) -->
                 p + c0 % U z) sequentially` ASSUME_TAC THENL
   [MATCH_MP_TAC LIM_ADD THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC CMC_LIM_CMUL_SEQ THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> LABEL_TAC "EQ" th THEN MP_TAC th) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (MESON[] `(!j:num. A j /\ B j) ==> (!j. A j)`)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(p:real^K) + c0 % (U:real^2->real^K) z IN S` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPEC `sequentially` LIM_IN_CLOSED_SET) THEN
    EXISTS_TAC `\j. (P:num->real^K) j + c j % (V:num->real^2->real^K) j z` THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_TRUE];
    ALL_TAC] THEN
  REMOVE_THEN "EQ" MP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> ((\j. hmr_tp S ((P:num->real^K) j + c j % (V:num->real^2->real^K) j z) **
                   partial_derivative i (V j) z) -->
             hmr_tp S (p + c0 % U z) ** partial_derivative i U z) sequentially`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC CMC_TP_LIM THEN
    MAP_EVERY EXISTS_TAC [`G:real^K->real^K^K`; `d:real`] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\j. vsum(1..2) (\i. christoffel G ((P:num->real^K) j + c j % (V:num->real^2->real^K) j z)
                            (partial_derivative i (V j) z) (partial_derivative i (V j) z))) -->
     vsum(1..2) (\i. christoffel G (p + c0 % U z)
                       (partial_derivative i U z) (partial_derivative i U z))) sequentially /\
    ((\j. vsum(1..2) (\i. hmr_bq S G ((P:num->real^K) j + c j % (V:num->real^2->real^K) j z)
                            (partial_derivative i (V j) z) (partial_derivative i (V j) z))) -->
     vsum(1..2) (\i. hmr_bq S G (p + c0 % U z)
                       (partial_derivative i U z) (partial_derivative i U z))) sequentially`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LIM_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THENL
     [MATCH_MP_TAC CMC_CHRIS_LIM THEN MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`];
      MATCH_MP_TAC CMC_BQ_LIM THEN EXISTS_TAC `d:real`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\j. hmr_tp S ((P:num->real^K) j + c j % (V:num->real^2->real^K) j z) **
          (hmr_vlap (V j) z +
           c j % vsum(1..2) (\i. christoffel G (P j + c j % V j z)
                                   (partial_derivative i (V j) z)
                                   (partial_derivative i (V j) z)))) -->
     hmr_tp S (p + c0 % U z) **
          (hmr_vlap U z +
           c0 % vsum(1..2) (\i. christoffel G (p + c0 % U z)
                                  (partial_derivative i U z) (partial_derivative i U z))))
    sequentially`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMC_TP_LIM THEN MAP_EVERY EXISTS_TAC [`G:real^K->real^K^K`; `d:real`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC LIM_ADD THEN CONJ_TAC THENL [ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
    MATCH_MP_TAC CMC_LIM_CMUL_SEQ THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[ETA_AX]; FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
    EXISTS_TAC `\j. partial_derivative i ((V:num->real^2->real^K) j) z` THEN
    ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `hmr_tp:(real^K->bool)->real^K->real^K^K`)) (concl th) &&
      not(can (find_term ((=) `christoffel:(real^K->real^K^K)->real^K->real^K->real^K->real^K`))
           (concl th)) && can (find_term ((=) `p:real^K`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN AP_THM_TAC THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
    EXISTS_TAC
     `\j. hmr_tp S ((P:num->real^K) j + c j % (V:num->real^2->real^K) j z) **
          (hmr_vlap (V j) z +
           c j % vsum(1..2) (\i. christoffel G (P j + c j % V j z)
                                   (partial_derivative i (V j) z)
                                   (partial_derivative i (V j) z)))` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\j. hmr_tp S ((P:num->real^K) j + c j % (V:num->real^2->real^K) j z) **
          (hmr_vlap (V j) z +
           c j % vsum(1..2) (\i. christoffel G (P j + c j % V j z)
                                   (partial_derivative i (V j) z)
                                   (partial_derivative i (V j) z)))) = (\j. vec 0)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[LIM_CONST];
    MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
    EXISTS_TAC `\j. hmr_vlap ((V:num->real^2->real^K) j) z` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\j. hmr_vlap ((V:num->real^2->real^K) j) z) =
      (\j. c j % vsum(1..2) (\i. hmr_bq S G ((P:num->real^K) j + c j % V j z)
                                   (partial_derivative i (V j) z)
                                   (partial_derivative i (V j) z)))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CMC_LIM_CMUL_SEQ THEN ASM_REWRITE_TAC[]]);;

let CMC_L2_NEAR_UNIF = prove
 (`!s t (f:num->real^2->real^K) g h K mu.
     measurable t /\ t SUBSET s /\ (mu ---> &0) sequentially /\
     (!j. (\x. f j x - g j x) IN lspace s (&2) /\
          lnorm s (&2) (\x. f j x - g j x) pow 2 <= K * mu j) /\
     (!j. (\x. g j x - h x) measurable_on t) /\
     (!j. ?M. !x. x IN t ==> norm(g j x - h x) <= M) /\
     (!e. &0 < e ==> ?N. !j x. N <= j /\ x IN t ==> norm(g j x - h x) < e)
     ==> (!j. (\x. f j x - h x) IN lspace t (&2)) /\
         ((\j. lnorm t (&2) (\x. f j x - h x)) ---> &0) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `t:real^2->bool`;
                 `\j x. (f:num->real^2->real^K) j x - g j x`] CMC_L2_RESTRICT_NULL) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MEASURABLE_IMP_LEBESGUE_MEASURABLE; ETA_AX] THEN
    MATCH_MP_TAC CMC_SQ_NULL THEN
    MAP_EVERY EXISTS_TAC [`mu:num->real`; `K:real`] THEN ASM_SIMP_TAC[LNORM_POS_LE];
    REWRITE_TAC[ETA_AX] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`t:real^2->bool`; `\j x. (g:num->real^2->real^K) j x - h x`]
                CMC_UNIF_LNORM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[ETA_AX]; REWRITE_TAC[ETA_AX] THEN STRIP_TAC] THEN
  MATCH_MP_TAC CMC_L2_SUM_NULL THEN
  MAP_EVERY EXISTS_TAC [`\j x. (f:num->real^2->real^K) j x - g j x`;
                        `\j x. (g:num->real^2->real^K) j x - h x`] THEN
  ASM_REWRITE_TAC[ETA_AX] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN VECTOR_ARITH_TAC);;

let CMC_NLOC_EXTRACT = prove
 (`!S (V:num->real^2->real^K) (P:num->real^K) a R (B:num->real) (r:num->num).
     compact S /\ &0 < R /\ (!m n. m < n ==> r m < r n) /\
     (!j. P j IN S) /\ (!j. smooth_map_on (ball(a,R / &16)) (V j)) /\
     (!l j z. ALL (\i. 1 <= i /\ i <= 2) l /\ z IN ball(a,R / &16)
              ==> norm(iterated_partial l (V j) z) <= B (LENGTH l))
     ==> ?(k:num->num) U p.
           (!m n. m < n ==> k m < k n) /\ p IN S /\ smooth_map_on (ball(a,R / &32)) U /\
           ((\j. P (r (k j))) --> p) sequentially /\
           (!l. ALL (\i. 1 <= i /\ i <= 2) l
                ==> (!z. z IN ball(a,R / &32)
                         ==> norm(iterated_partial l U z) <= B (LENGTH l)) /\
                    !e. &0 < e
                        ==> ?N. !n z. N <= n /\ z IN ball(a,R / &32)
                                      ==> norm(iterated_partial l (V (r (k n))) z -
                                               iterated_partial l U z) < e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\n. (V:num->real^2->real^K) ((r:num->num) n)`; `a:real^2`; `R / &32`;
                 `B:num->real`] CMC_CINF_COMPACT) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `&2 * R / &32 = R / &16` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:num->num` (X_CHOOSE_THEN `U:real^2->real^K`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o SPEC `\n. (P:num->real^K) ((r:num->num) ((t1:num->num) n))` o
    GEN_REWRITE_RULE I [compact]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^K` (X_CHOOSE_THEN `t2:num->num` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `(t1:num->num) o (t2:num->num)` THEN
  MAP_EVERY EXISTS_TAC [`U:real^2->real^K`; `p:real^K`] THEN
  ASM_REWRITE_TAC[o_THM] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th) THEN
    FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th) THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `(((\n. (P:num->real^K) ((r:num->num) ((t1:num->num) n))) o t2) --> p)
                 sequentially` THEN REWRITE_TAC[o_DEF];
    X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `l:num list`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CMC_MONO_BIGGER THEN ASM_REWRITE_TAC[]]);;

let CMC_UNIF_PW = prove
 (`!(f:num->real^2->real^K) g s z.
     z IN s /\
     (!e. &0 < e ==> ?N. !n x. N <= n /\ x IN s ==> norm(f n x - g x) < e)
     ==> ((\n. f n z) --> g z) sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIM_SEQUENTIALLY; dist] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let CMC_NLOC = prove
 (`!S (G:real^K->real^K^K) d (C:num->real) (w:num->real^2->real^K) (y:num->real^2)
    (rho:num->real) (c:num->real) c0 (mu:num->real) (P:num->real^K)
    (V:num->real^2->real^K) a R (r:num->num).
     cm_target S G d /\ &0 < R /\ (!k. &0 < C k) /\
     (!j. &0 < c j) /\ (c ---> c0) sequentially /\ (mu ---> &0) sequentially /\
     (!m n. m < n ==> r m < r n) /\
     (!j. P j IN S /\ smooth_map_on (ball(a,R / &8)) (V j) /\
          (!l z. ALL (\i. 1 <= i /\ i <= 2) l /\ ~(l = []) /\ z IN ball(a,R / &16)
                 ==> norm(iterated_partial l (V j) z) <= C (LENGTH l) * (&8 / R) pow (LENGTH l)) /\
          (!z. z IN ball(a,R / &16) ==> norm(V j z) <= C 1) /\
          (\z. inv(c j) % (w j (y j + rho j % z) - P j) - V j z)
            IN lspace (ball(a,R / &8)) (&2) /\
          lnorm (ball(a,R / &8)) (&2) (\z. inv(c j) % (w j (y j + rho j % z) - P j) - V j z)
            pow 2 <= &4 * (R / &8) pow 2 * mu j /\
          (!i. 1 <= i /\ i <= 2
               ==> (\z. (rho j / c j) % wan_wd (:real^2) i (w j) (y j + rho j % z) -
                        partial_derivative i (V j) z) IN lspace (ball(a,R / &8)) (&2) /\
                   lnorm (ball(a,R / &8)) (&2)
                     (\z. (rho j / c j) % wan_wd (:real^2) i (w j) (y j + rho j % z) -
                          partial_derivative i (V j) z) pow 2 <= mu j) /\
          (!z. z IN ball(a,R / &8)
               ==> P j + c j % V j z IN S /\
                   (!i. hmr_tp S (P j + c j % V j z) ** partial_derivative i (V j) z =
                        partial_derivative i (V j) z) /\
                   hmr_tp S (P j + c j % V j z) **
                     (hmr_vlap (V j) z +
                      c j % vsum(1..2) (\i. christoffel G (P j + c j % V j z)
                                              (partial_derivative i (V j) z)
                                              (partial_derivative i (V j) z))) = vec 0 /\
                   hmr_vlap (V j) z =
                     c j % vsum(1..2) (\i. hmr_bq S G (P j + c j % V j z)
                                              (partial_derivative i (V j) z)
                                              (partial_derivative i (V j) z))))
     ==> ?(k:num->num) U p.
           (!m n. m < n ==> k m < k n) /\ p IN S /\ smooth_map_on (ball(a,R / &32)) U /\
           ((\j. P (r (k j))) --> p) sequentially /\
           (!z. z IN ball(a,R / &32) ==> norm(U z) <= C 1) /\
           (!i z. 1 <= i /\ i <= 2 /\ z IN ball(a,R / &32)
                  ==> norm(partial_derivative i U z) <= C 1 * &8 / R) /\
           (!j. (\z. inv(c (r (k j))) % (w (r (k j)) (y (r (k j)) + rho (r (k j)) % z) -
                                          P (r (k j))) - U z)
                IN lspace (ball(a,R / &32)) (&2)) /\
           ((\j. lnorm (ball(a,R / &32)) (&2)
                   (\z. inv(c (r (k j))) % (w (r (k j)) (y (r (k j)) + rho (r (k j)) % z) -
                                            P (r (k j))) - U z)) ---> &0) sequentially /\
           (!i. 1 <= i /\ i <= 2
                ==> (!j. (\z. (rho (r (k j)) / c (r (k j))) %
                              wan_wd (:real^2) i (w (r (k j))) (y (r (k j)) + rho (r (k j)) % z) -
                              partial_derivative i U z) IN lspace (ball(a,R / &32)) (&2)) /\
                    ((\j. lnorm (ball(a,R / &32)) (&2)
                            (\z. (rho (r (k j)) / c (r (k j))) %
                                 wan_wd (:real^2) i (w (r (k j)))
                                   (y (r (k j)) + rho (r (k j)) % z) -
                                 partial_derivative i U z)) ---> &0) sequentially) /\
           (!z. z IN ball(a,R / &32)
                ==> p + c0 % U z IN S /\
                    (!i. 1 <= i /\ i <= 2
                         ==> hmr_tp S (p + c0 % U z) ** partial_derivative i U z =
                             partial_derivative i U z) /\
                    hmr_tp S (p + c0 % U z) **
                      (hmr_vlap U z +
                       c0 % vsum(1..2) (\i. christoffel G (p + c0 % U z)
                                              (partial_derivative i U z)
                                              (partial_derivative i U z))) = vec 0 /\
                    hmr_vlap U z =
                      c0 % vsum(1..2) (\i. hmr_bq S G (p + c0 % U z)
                                              (partial_derivative i U z)
                                              (partial_derivative i U z)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  SUBGOAL_THEN `!z:real^2. z IN ball(a,R / &32) ==> z IN ball(a,R / &16)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL] THEN UNDISCH_TAC `&0 < R` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^2. z IN ball(a,R / &16) ==> z IN ball(a,R / &8)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL] THEN UNDISCH_TAC `&0 < R` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `V:num->real^2->real^K`; `P:num->real^K`; `a:real^2`;
                 `R:real`; `\n. if n = 0 then (C:num->real) 1 else C n * (&8 / R) pow n`;
                 `r:num->num`] CMC_NLOC_EXTRACT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `ball(a:real^2,R / &8)` THEN ASM_SIMP_TAC[SUBSET];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`l:num list`; `j:num`; `z:real^2`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `l:num list = []` THENL
     [ASM_REWRITE_TAC[LENGTH; iterated_partial] THEN ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[LENGTH_EQ_NIL] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num->num` (X_CHOOSE_THEN `U:real^2->real^K`
    (X_CHOOSE_THEN `p:real^K` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "UC")))))))) THEN
  MAP_EVERY EXISTS_TAC [`k:num->num`; `U:real^2->real^K`; `p:real^K`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!m n. m < n ==> (r:num->num) ((k:num->num) m) < r (k n)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th) THEN
    FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!l z. ALL (\i. 1 <= i /\ i <= 2) l /\ z IN ball(a,R / &32)
                      ==> norm(iterated_partial l (U:real^2->real^K) z) <=
                          (if LENGTH l = 0 then (C:num->real) 1
                           else C (LENGTH l) * (&8 / R) pow (LENGTH l))`
  (LABEL_TAC "UB") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "UC" (MP_TAC o SPEC `l:num list`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^2` o CONJUNCT1) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!l. ALL (\i. 1 <= i /\ i <= 2) l
                    ==> !e. &0 < e
                            ==> ?N. !n z. N <= n /\ z IN ball(a,R / &32)
                                          ==> norm(iterated_partial l
                                                     ((V:num->real^2->real^K)
                                                       ((r:num->num) ((k:num->num) n))) z -
                                                   iterated_partial l (U:real^2->real^K) z) < e`
  (LABEL_TAC "UCV") THENL
   [GEN_TAC THEN DISCH_TAC THEN USE_THEN "UC" (MP_TAC o SPEC `l:num list`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!l z. ALL (\i. 1 <= i /\ i <= 2) l /\ z IN ball(a,R / &32)
                      ==> ((\n. iterated_partial l ((V:num->real^2->real^K)
                                   ((r:num->num) ((k:num->num) n))) z) -->
                           iterated_partial l (U:real^2->real^K) z) sequentially`
  (LABEL_TAC "PW") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMC_UNIF_PW THEN
    EXISTS_TAC `ball(a:real^2,R / &32)` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "UCV" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\j. (mu:num->real) ((r:num->num) ((k:num->num) j))) ---> &0) sequentially`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`mu:num->real`; `&0`; `\j. (r:num->num) ((k:num->num) j)`]
                  HMD_REALLIM_SUBSEQ) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\j. (c:num->real) ((r:num->num) ((k:num->num) j))) ---> c0) sequentially`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:num->real`; `c0:real`; `\j. (r:num->num) ((k:num->num) j)`]
                  HMD_REALLIM_SUBSEQ) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(U:real^2->real^K) continuous_on ball(a,R / &32) /\
                !i. partial_derivative i U continuous_on ball(a,R / &32)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; CMC_PD_CONTINUOUS; OPEN_BALL]; ALL_TAC] THEN
  SUBGOAL_THEN `!j. (V:num->real^2->real^K) j continuous_on ball(a,R / &32) /\
                    !i. partial_derivative i (V j) continuous_on ball(a,R / &32)`
  ASSUME_TAC THENL
   [GEN_TAC THEN CONJ_TAC THENL [ALL_TAC; GEN_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(a:real^2,R / &8)` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; CMC_PD_CONTINUOUS; OPEN_BALL; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(a:real^2,R / &32) SUBSET ball(a,R / &8)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!l. ALL (\i. 1 <= i /\ i <= 2) l
        ==> (!j. (\x. iterated_partial l ((V:num->real^2->real^K) ((r:num->num) ((k:num->num) j))) x -
                      iterated_partial l (U:real^2->real^K) x) measurable_on ball(a,R / &32)) /\
            (!j. ?M. !x. x IN ball(a,R / &32)
                         ==> norm(iterated_partial l (V (r (k j))) x - iterated_partial l U x)
                             <= M)`
  (LABEL_TAC "MB") THENL
   [GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THEN GEN_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      REWRITE_TAC[LEBESGUE_MEASURABLE_BALL] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
      REWRITE_TAC[ETA_AX] THEN CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_ITERATED_PARTIAL THEN REWRITE_TAC[OPEN_BALL] THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(a:real^2,R / &8)` THEN
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]];
      EXISTS_TAC `(if LENGTH (l:num list) = 0 then (C:num->real) 1
                   else C (LENGTH l) * (&8 / R) pow (LENGTH l)) +
                  (if LENGTH (l:num list) = 0 then (C:num->real) 1
                   else C (LENGTH l) * (&8 / R) pow (LENGTH l))` THEN
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN MATCH_MP_TAC(NORM_ARITH
       `norm(u:real^K) <= a /\ norm v <= b ==> norm(u - v) <= a + b`) THEN
      CONJ_TAC THENL
       [ASM_CASES_TAC `l:num list = []` THENL
         [ASM_REWRITE_TAC[LENGTH; iterated_partial] THEN ASM_SIMP_TAC[];
          ASM_REWRITE_TAC[LENGTH_EQ_NIL] THEN ASM_SIMP_TAC[]];
        USE_THEN "UB" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!j. (\z. inv(c ((r:num->num) ((k:num->num) j))) %
             ((w:num->real^2->real^K) (r (k j)) ((y:num->real^2) (r (k j)) +
                                        (rho:num->real) (r (k j)) % z) -
              (P:num->real^K) (r (k j))) - (U:real^2->real^K) z)
         IN lspace (ball(a,R / &32)) (&2)) /\
    ((\j. lnorm (ball(a,R / &32)) (&2)
            (\z. inv(c ((r:num->num) ((k:num->num) j))) %
                 ((w:num->real^2->real^K) (r (k j)) ((y:num->real^2) (r (k j)) +
                                            (rho:num->real) (r (k j)) % z) -
                  (P:num->real^K) (r (k j))) - (U:real^2->real^K) z)) ---> &0) sequentially`
  (fun th -> REWRITE_TAC[th]) THENL
   [MP_TAC(ISPECL [`ball(a:real^2,R / &8)`; `ball(a:real^2,R / &32)`;
                   `\j z. inv(c ((r:num->num) ((k:num->num) j))) %
                          ((w:num->real^2->real^K) (r (k j)) ((y:num->real^2) (r (k j)) +
                                                     (rho:num->real) (r (k j)) % z) -
                           (P:num->real^K) (r (k j)))`;
                   `\j. (V:num->real^2->real^K) ((r:num->num) ((k:num->num) j))`;
                   `U:real^2->real^K`; `&4 * (R / &8) pow 2`;
                   `\j. (mu:num->real) ((r:num->num) ((k:num->num) j))`] CMC_L2_NEAR_UNIF) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    USE_THEN "MB" (MP_TAC o SPEC `[]:num list`) THEN
    USE_THEN "UCV" (MP_TAC o SPEC `[]:num list`) THEN
    REWRITE_TAC[ALL; iterated_partial] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[MEASURABLE_BALL; GSYM REAL_MUL_ASSOC] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> (!j. (\z. ((rho:num->real) ((r:num->num) ((k:num->num) j)) / c (r (k j))) %
                      wan_wd (:real^2) i ((w:num->real^2->real^K) (r (k j)))
                        ((y:num->real^2) (r (k j)) + rho (r (k j)) % z) -
                      partial_derivative i (U:real^2->real^K) z)
                 IN lspace (ball(a,R / &32)) (&2)) /\
            ((\j. lnorm (ball(a,R / &32)) (&2)
                    (\z. ((rho:num->real) ((r:num->num) ((k:num->num) j)) / c (r (k j))) %
                         wan_wd (:real^2) i ((w:num->real^2->real^K) (r (k j)))
                           ((y:num->real^2) (r (k j)) + rho (r (k j)) % z) -
                         partial_derivative i (U:real^2->real^K) z)) ---> &0) sequentially`
  (LABEL_TAC "PL2") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`ball(a:real^2,R / &8)`; `ball(a:real^2,R / &32)`;
                   `\j z. ((rho:num->real) ((r:num->num) ((k:num->num) j)) / c (r (k j))) %
                          wan_wd (:real^2) i ((w:num->real^2->real^K) (r (k j)))
                            ((y:num->real^2) (r (k j)) + rho (r (k j)) % z)`;
                   `\j. partial_derivative i
                          ((V:num->real^2->real^K) ((r:num->num) ((k:num->num) j)))`;
                   `partial_derivative i (U:real^2->real^K)`; `&1`;
                   `\j. (mu:num->real) ((r:num->num) ((k:num->num) j))`] CMC_L2_NEAR_UNIF) THEN
    REWRITE_TAC[REAL_MUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
    USE_THEN "MB" (MP_TAC o SPEC `[i:num]`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[ALL]; REWRITE_TAC[iterated_partial] THEN STRIP_TAC] THEN
    USE_THEN "UCV" (MP_TAC o SPEC `[i:num]`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[ALL]; REWRITE_TAC[iterated_partial] THEN DISCH_TAC] THEN
    ASM_REWRITE_TAC[MEASURABLE_BALL; ETA_AX] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* zeroth bound *)
    X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    USE_THEN "UB" (MP_TAC o SPECL [`[]:num list`; `z:real^2`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[ALL]; REWRITE_TAC[LENGTH; iterated_partial]];
    (* partial bound *)
    MAP_EVERY X_GEN_TAC [`i:num`; `z:real^2`] THEN STRIP_TAC THEN
    USE_THEN "UB" (MP_TAC o SPECL [`[i:num]`; `z:real^2`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[ALL]; ALL_TAC] THEN
    REWRITE_TAC[LENGTH; iterated_partial] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[REAL_POW_1; real_div; REAL_MUL_ASSOC];
    USE_THEN "PL2" ACCEPT_TAC;
    (* equations *)
    X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    MATCH_MP_TAC CMC_NLOC_EQS THEN
    MAP_EVERY EXISTS_TAC [`d:real`;
                          `\j. (V:num->real^2->real^K) ((r:num->num) ((k:num->num) j))`;
                          `\j. (P:num->real^K) ((r:num->num) ((k:num->num) j))`;
                          `\j. (c:num->real) ((r:num->num) ((k:num->num) j))`] THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      USE_THEN "PW" (MP_TAC o SPECL [`[]:num list`; `z:real^2`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[ALL]; REWRITE_TAC[iterated_partial]];
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      USE_THEN "PW" (MP_TAC o SPECL [`[i:num]`; `z:real^2`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[ALL]; REWRITE_TAC[iterated_partial]];
      REWRITE_TAC[hmr_vlap] THEN MATCH_MP_TAC LIM_VSUM THEN
      REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      USE_THEN "PW" (MP_TAC o SPECL [`[i:num; i]`; `z:real^2`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[ALL]; REWRITE_TAC[iterated_partial]];
      GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `(r:num->num) ((k:num->num) j)` o
        check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `hmr_bq:(real^K->bool)->(real^K->real^K^K)->real^K->real^K->real^K->real^K`)) (concl th))) THEN
      DISCH_THEN(MP_TAC o SPEC `z:real^2` o last o CONJUNCTS) THEN
      ASM_SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Offsets between the base points of overlapping balls.                   *)
(* ------------------------------------------------------------------------- *)

let CMC_LNORM_CONST = prove
 (`!s (q0:real^K).
     measurable s
     ==> (\x:real^2. q0) IN lspace s (&2) /\
         lnorm s (&2) (\x:real^2. q0) = norm q0 * sqrt(measure s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(\x:real^2. (q0:real^K)) IN lspace s (&2)` ASSUME_TAC THENL
   [REWRITE_TAC[lspace; IN_ELIM_THM; RPOW_POW] THEN
    ASM_SIMP_TAC[INTEGRABLE_ON_CONST; MEASURABLE_ON_CONST_EQ;
                 MEASURABLE_IMP_LEBESGUE_MEASURABLE];
    ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC(ISPEC `2` REAL_POW_EQ) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[LNORM_POS_LE; REAL_LE_MUL; NORM_POS_LE; SQRT_POS_LE; MEASURE_POS_LE] THEN
  ASM_SIMP_TAC[WAN_SOB_LNORM2_SQ; INTEGRAL_CONST_GEN; DROP_CMUL; LIFT_DROP] THEN
  REWRITE_TAC[REAL_POW_MUL] THEN ASM_SIMP_TAC[SQRT_POW_2; MEASURE_POS_LE] THEN
  REAL_ARITH_TAC);;

let CMC_OFFSET_NEAR = prove
 (`!(w:real^2->real^K) (y:real^2) rho c P1 P2 (V1:real^2->real^K) V2 s m B.
     measurable s /\ &0 < measure s /\ &0 <= m /\
     (\z. inv c % (w(y + rho % z) - P1) - V1 z) IN lspace s (&2) /\
     lnorm s (&2) (\z. inv c % (w(y + rho % z) - P1) - V1 z) pow 2 <= m /\
     (\z. inv c % (w(y + rho % z) - P2) - V2 z) IN lspace s (&2) /\
     lnorm s (&2) (\z. inv c % (w(y + rho % z) - P2) - V2 z) pow 2 <= m /\
     V1 measurable_on s /\ V2 measurable_on s /\
     (!z. z IN s ==> norm(V1 z) <= B /\ norm(V2 z) <= B)
     ==> norm(inv c % (P2 - P1)) <= &2 * sqrt(m / measure s) + &2 * B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `f1 = \z. inv c % ((w:real^2->real^K)(y + rho % z) - P1) - V1 z` THEN
  ABBREV_TAC `f2 = \z. inv c % ((w:real^2->real^K)(y + rho % z) - P2) - V2 z` THEN
  SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
   [SUBGOAL_THEN `?z:real^2. z IN s` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(SET_RULE `~((s:real^2->bool) = {}) ==> ?z. z IN s`) THEN DISCH_TAC THEN
      UNDISCH_TAC `&0 < measure(s:real^2->bool)` THEN
      ASM_REWRITE_TAC[MEASURE_EMPTY; REAL_LT_REFL];
      ASM_MESON_TAC[NORM_POS_LE; REAL_LE_TRANS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z. (V1:real^2->real^K) z - V2 z) IN lspace s (&2) /\
                lnorm s (&2) (\z. V1 z - V2 z) <= sqrt(measure s) * (&2 * B)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^2->bool`; `\z. (V1:real^2->real^K) z - V2 z`; `&2 * B`]
                  CMC_BOUNDED_LNORM) THEN
    ASM_SIMP_TAC[MEASURABLE_ON_SUB] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC(NORM_ARITH
       `norm(x:real^K) <= b /\ norm y <= b ==> norm(x - y) <= &2 * b`) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= B ==> abs(&2 * B) = &2 * B`] THEN
    SUBGOAL_THEN `measure(s:real^2->bool) rpow inv(&2) = sqrt(measure s)` SUBST1_TAC THENL
     [SUBGOAL_THEN `inv(&2) = &1 / &2` SUBST1_TAC THENL
       [CONV_TAC REAL_RAT_REDUCE_CONV; ASM_SIMP_TAC[RPOW_SQRT; MEASURE_POS_LE]];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `lnorm s (&2) (f1:real^2->real^K) <= sqrt m /\ lnorm s (&2) (f2:real^2->real^K) <= sqrt m`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RSQRT THEN EXPAND_TAC "f1" THEN EXPAND_TAC "f2" THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f1:real^2->real^K) IN lspace s (&2) /\ (f2:real^2->real^K) IN lspace s (&2)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "f1" THEN EXPAND_TAC "f2" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `inv c % ((P2:real^K) - P1)`] CMC_LNORM_CONST) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `lnorm s (&2) (\x:real^2. inv c % ((P2:real^K) - P1)) =
    lnorm s (&2) (\x. (f1 x - f2 x) + ((V1:real^2->real^K) x - V2 x))`
  ASSUME_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^2` THEN
    MAP_EVERY EXPAND_TAC ["f1"; "f2"] THEN REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lnorm s (&2) (\x. ((f1:real^2->real^K) x - f2 x) + ((V1:real^2->real^K) x - V2 x)) <=
    (sqrt m + sqrt m) + sqrt(measure s) * (&2 * B)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lnorm s (&2) (\x. (f1:real^2->real^K) x - f2 x) +
                lnorm s (&2) (\x. (V1:real^2->real^K) x - V2 x)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LNORM_TRIANGLE THEN ASM_SIMP_TAC[LSPACE_SUB; REAL_POS] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lnorm s (&2) (f1:real^2->real^K) + lnorm s (&2) (\x. --((f2:real^2->real^K) x))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[VECTOR_SUB] THEN
      MP_TAC(ISPECL [`s:real^2->bool`; `&2`; `f1:real^2->real^K`;
                     `\x. --((f2:real^2->real^K) x)`] LNORM_TRIANGLE) THEN
      ASM_SIMP_TAC[LSPACE_NEG; ETA_AX] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[];
      REWRITE_TAC[LNORM_NEG; ETA_AX] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(measure(s:real^2->bool))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(inv c % ((P2:real^K) - P1)) * sqrt(measure(s:real^2->bool)) <=
                (&2 * sqrt(m / measure s) + &2 * B) * sqrt(measure s)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(sqrt m + sqrt m) + sqrt(measure(s:real^2->bool)) * (&2 * B)` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
    SUBGOAL_THEN `(&2 * sqrt(m / measure(s:real^2->bool))) * sqrt(measure s) = sqrt m + sqrt m`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
      ASM_SIMP_TAC[GSYM SQRT_MUL; REAL_LE_DIV; MEASURE_POS_LE] THEN
      ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ASM_SIMP_TAC[REAL_LE_RMUL_EQ]]);;

let CMC_OFFSET_BOUNDED = prove
 (`!(w:num->real^2->real^K) (y:num->real^2) (rho:num->real) (c:num->real)
    (P:num->real^2->real^K) (V:num->real^2->real^2->real^K) Cs R m B.
     connected Cs /\ &0 < R /\ &0 <= m /\ (!j. &0 < c j) /\
     (!j a. a IN Cs
            ==> (\z. inv(c j) % (w j (y j + rho j % z) - P j a) - V j a z)
                  IN lspace (ball(a,R / &8)) (&2) /\
                lnorm (ball(a,R / &8)) (&2)
                  (\z. inv(c j) % (w j (y j + rho j % z) - P j a) - V j a z) pow 2 <= m /\
                V j a continuous_on ball(a,R / &16) /\
                (!z. z IN ball(a,R / &16) ==> norm(V j a z) <= B))
     ==> !a b. a IN Cs /\ b IN Cs ==> ?M. !j. norm(P j b - P j a) <= M * c j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC CONNECTED_EQUIVALENCE_RELATION THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:real^2`; `b:real^2`] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_FORALL THEN
    GEN_TAC THEN REWRITE_TAC[] THEN MESON_TAC[NORM_SUB];
    MAP_EVERY X_GEN_TAC [`a:real^2`; `b:real^2`; `e:real^2`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `M1:real`) (X_CHOOSE_TAC `M2:real`)) THEN
    EXISTS_TAC `M1 + M2:real` THEN X_GEN_TAC `j:num` THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm((P:num->real^2->real^K) j b - P j a) + norm(P j e - P j b)` THEN
    CONJ_TAC THENL [NORM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ADD_RDISTRIB] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `a:real^2` THEN DISCH_TAC THEN
  EXISTS_TAC `Cs INTER ball(a:real^2,R / &32)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[OPEN_BALL]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_INTER; IN_BALL] THEN STRIP_TAC THEN
  ABBREV_TAC `s = ball(a:real^2,R / &32)` THEN
  SUBGOAL_THEN `measurable(s:real^2->bool) /\ &0 < measure s` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[MEASURABLE_BALL; MEASURE_BALL_POS] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^2->bool) SUBSET ball(a,R / &16) /\ s SUBSET ball(a,R / &8) /\
                s SUBSET ball(x,R / &16) /\ s SUBSET ball(x,R / &8)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
    UNDISCH_TAC `dist(a:real^2,x) < R / &32` THEN UNDISCH_TAC `&0 < R` THEN
    CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  EXISTS_TAC `&2 * sqrt(m / measure(s:real^2->bool)) + &2 * B` THEN X_GEN_TAC `j:num` THEN
  MP_TAC(ISPECL [`(w:num->real^2->real^K) j`; `(y:num->real^2) j`; `(rho:num->real) j`;
                 `(c:num->real) j`; `(P:num->real^2->real^K) j a`; `(P:num->real^2->real^K) j x`;
                 `(V:num->real^2->real^2->real^K) j a`; `(V:num->real^2->real^2->real^K) j x`;
                 `s:real^2->bool`; `m:real`; `B:real`] CMC_OFFSET_NEAR) THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(fun th -> MP_TAC(SPECL [`j:num`; `a:real^2`] th) THEN
                            MP_TAC(SPECL [`j:num`; `x:real^2`] th)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `ball(a:real^2,R / &8)` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "s" THEN REWRITE_TAC[LEBESGUE_MEASURABLE_BALL];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `lnorm (ball(a,R / &8)) (&2)
                    (\z. inv((c:num->real) j) % ((w:num->real^2->real^K) j (y j + rho j % z) -
                         (P:num->real^2->real^K) j a) - (V:num->real^2->real^2->real^K) j a z)
                  pow 2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC LNORM_POS_LE THEN MATCH_MP_TAC LSPACE_SUBSET THEN
        EXISTS_TAC `ball(a:real^2,R / &8)` THEN ASM_REWRITE_TAC[] THEN
        EXPAND_TAC "s" THEN REWRITE_TAC[LEBESGUE_MEASURABLE_BALL];
        MATCH_MP_TAC WAN_LNORM2_SUBSET_LE THEN ASM_REWRITE_TAC[] THEN
        EXPAND_TAC "s" THEN REWRITE_TAC[LEBESGUE_MEASURABLE_BALL]];
      MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `ball(x:real^2,R / &8)` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "s" THEN REWRITE_TAC[LEBESGUE_MEASURABLE_BALL];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `lnorm (ball(x,R / &8)) (&2)
                    (\z. inv((c:num->real) j) % ((w:num->real^2->real^K) j (y j + rho j % z) -
                         (P:num->real^2->real^K) j x) - (V:num->real^2->real^2->real^K) j x z)
                  pow 2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC LNORM_POS_LE THEN MATCH_MP_TAC LSPACE_SUBSET THEN
        EXISTS_TAC `ball(x:real^2,R / &8)` THEN ASM_REWRITE_TAC[] THEN
        EXPAND_TAC "s" THEN REWRITE_TAC[LEBESGUE_MEASURABLE_BALL];
        MATCH_MP_TAC WAN_LNORM2_SUBSET_LE THEN ASM_REWRITE_TAC[] THEN
        EXPAND_TAC "s" THEN REWRITE_TAC[LEBESGUE_MEASURABLE_BALL]];
      MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(a:real^2,R / &16)` THEN
        ASM_REWRITE_TAC[];
        EXPAND_TAC "s" THEN REWRITE_TAC[LEBESGUE_MEASURABLE_BALL]];
      MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(x:real^2,R / &16)` THEN
        ASM_REWRITE_TAC[];
        EXPAND_TAC "s" THEN REWRITE_TAC[LEBESGUE_MEASURABLE_BALL]];
      ASM SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[NORM_MUL] THEN
  SUBGOAL_THEN `abs(inv((c:num->real) j)) = inv(c j)` SUBST1_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs x = x`) THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ; real_div; REAL_MUL_SYM] THEN
  REWRITE_TAC[REAL_MUL_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Vocabulary of CM Lemma B.31; uniqueness of L^2 limits; gluing of local    *)
(* smooth maps; finite diagonal subsequences.                                *)
(* ------------------------------------------------------------------------- *)

let cmc_angE = new_definition
 `cmc_angE (y:real^2) (E:real^2->bool) (w:real^2->real^K) =
    drop(integral E (\x. lift(norm(cmc_angd y x (wan_wd (:real^2) 1 w x)
                                               (wan_wd (:real^2) 2 w x)) pow 2)))`;;

let cmc_eE = new_definition
 `cmc_eE (E:real^2->bool) (w:real^2->real^K) =
    drop(integral E (\x. lift(norm(wan_wd (:real^2) 1 w x) pow 2 +
                              norm(wan_wd (:real^2) 2 w x) pow 2)))`;;

let cmc_srb = new_definition
 `cmc_srb (S:real^K->bool) (G:real^K->real^K^K) mu (A:real^2->bool) (w:real^2->real^K) <=>
    !c r v. &0 < r /\ cball(c,r) SUBSET A /\
            cm_minimizer S G (ball(c,r / &8)) v /\
            wan_w120 (ball(c,r / &8)) (\x. v x - w x)
            ==> wan_dir (ball(c,r / &8)) (\x. w x - v x) <= mu * cmc_pen G A w`;;

let cmc_cylp = new_definition
 `cmc_cylp (S:real^K->bool) (G:real^K->real^K^K) l g delta <=>
    !s (U:real^2->real^K) (p:real^K) c (y:real^2) rho M.
       open s /\ &0 < rho /\ &0 <= c /\ &0 <= M /\ c * M <= g /\
       {x:real^2 | rho * exp(--(&2 * l)) <= norm(x - y) /\
                   norm(x - y) <= rho * exp(&2 * l)} SUBSET s /\
       smooth_map_on s U /\
       (!x. x IN s ==> p + c % U x IN S) /\
       (!x i. x IN s /\ 1 <= i /\ i <= 2
              ==> hmr_tp S (p + c % U x) ** partial_derivative i U x =
                  partial_derivative i U x) /\
       (!x. x IN s
            ==> hmr_tp S (p + c % U x) **
                (hmr_vlap U x +
                 c % vsum(1..2)
                       (\i. christoffel G (p + c % U x)
                              (partial_derivative i U x)
                              (partial_derivative i U x))) = vec 0) /\
       (!x. x IN s
            ==> hmr_vlap U x =
                c % vsum(1..2)
                      (\i. hmr_bq S G (p + c % U x)
                             (partial_derivative i U x)
                             (partial_derivative i U x))) /\
       (!x. rho * exp(--(&2 * l)) <= norm(x - y) /\
            norm(x - y) <= rho * exp(&2 * l)
            ==> norm(x - y) * norm(partial_derivative 1 U x) <= M /\
                norm(x - y) * norm(partial_derivative 2 U x) <= M)
       ==> drop(integral (cmc_ann y (rho * exp(--l)) (rho * exp l))
                  (\x. lift(norm(cmc_angd y x (partial_derivative 1 U x)
                                             (partial_derivative 2 U x))
                            pow 2)))
           <= delta *
              drop(integral (cmc_ann y (rho * exp(--(&2 * l)))
                                       (rho * exp(&2 * l)))
                     (\x. lift(norm(partial_derivative 1 U x) pow 2 +
                               norm(partial_derivative 2 U x) pow 2)))`;;

let CMC_CYL_P = prove
 (`!S (G:real^K->real^K^K) d delta.
     cm_target S G d /\ &0 < delta
     ==> ?l g. &1 <= l /\ &0 < g /\ cmc_cylp S G l g delta`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPEC `(:K)` CMC_CYL) THEN
  REWRITE_TAC[CMC_CYL_STATEMENT; cmc_cylp] THEN
  DISCH_THEN(MP_TAC o SPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `delta:real`) THEN
  ASM_REWRITE_TAC[]);;

let CMC_L2_VALUE_UNIQUE = prove
 (`!E (f:num->real^2->real^K) u1 u2.
     (!j. (\x. f j x - u1 x) IN lspace E (&2)) /\
     ((\j. lnorm E (&2) (\x. f j x - u1 x)) ---> &0) sequentially /\
     (!j. (\x. f j x - u2 x) IN lspace E (&2)) /\
     ((\j. lnorm E (&2) (\x. f j x - u2 x)) ---> &0) sequentially
     ==> negligible {x | x IN E /\ ~(u1 x = u2 x)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x. (u1:real^2->real^K) x - u2 x) IN lspace E (&2)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(\x. (u1:real^2->real^K) x - u2 x) =
                  (\x. ((f:num->real^2->real^K) 0 x - u2 x) - (f 0 x - u1 x))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`E:real^2->bool`; `&2`; `\x. (u1:real^2->real^K) x - u2 x`] LNORM_EQ_0) THEN
  ASM_REWRITE_TAC[VECTOR_SUB_EQ] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &0 ==> x = &0`) THEN
  CONJ_TAC THENL [MATCH_MP_TAC LNORM_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LE) THEN
  EXISTS_TAC `\j:num. lnorm E (&2) (\x. (u1:real^2->real^K) x - u2 x)` THEN
  EXISTS_TAC `\j. lnorm E (&2) (\x. (f:num->real^2->real^K) j x - u2 x) +
                  lnorm E (&2) (\x. f j x - u1 x)` THEN
  REWRITE_TAC[REALLIM_CONST; TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`sequentially`;
                   `\j. lnorm E (&2) (\x. (f:num->real^2->real^K) j x - u2 x)`;
                   `\j. lnorm E (&2) (\x. (f:num->real^2->real^K) j x - u1 x)`;
                   `&0`; `&0`] REALLIM_ADD) THEN
    ASM_REWRITE_TAC[REAL_ADD_LID];
    ALL_TAC] THEN
  MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `j:num` THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\x. (u1:real^2->real^K) x - u2 x) =
                (\x. ((f:num->real^2->real^K) j x - u2 x) + --(f j x - u1 x))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `lnorm E (&2) (\x. (f:num->real^2->real^K) j x - u2 x) +
              lnorm E (&2) (\x. --(f j x - u1 x))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LNORM_TRIANGLE THEN ASM_SIMP_TAC[LSPACE_NEG] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    REWRITE_TAC[LNORM_NEG; REAL_LE_REFL]]);;

let CMC_LOCAL_EQ_DERIVS = prove
 (`!s (f:real^2->real^K) g x.
     open s /\ x IN s /\ (!y. y IN s ==> f y = g y)
     ==> f x = g x /\
         (!i. partial_derivative i f x = partial_derivative i g x) /\
         hmr_vlap f x = hmr_vlap g x`,
  REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[];
    MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[hmr_vlap] THEN MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `i:num` THEN
    DISCH_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN
    EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN
    EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[]]);;

let CMC_GLUE_LOCAL = prove
 (`!(k:A->bool) (B:A->real^2->bool) (g:A->real^2->real^K).
     (!a. a IN k ==> open(B a) /\ smooth_map_on (B a) (g a)) /\
     (!a b x. a IN k /\ b IN k /\ x IN B a /\ x IN B b ==> g a x = g b x)
     ==> ?U. smooth_map_on (UNIONS (IMAGE B k)) U /\
             !a x. a IN k /\ x IN B a ==> U x = g a x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  EXISTS_TAC `\x:real^2. (g:A->real^2->real^K) (@a. a IN k /\ x IN B a) x` THEN
  SUBGOAL_THEN `!a x. a IN k /\ x IN (B:A->real^2->bool) a
                      ==> (g:A->real^2->real^K) (@a. a IN k /\ x IN B a) x = g a x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\a:A. a IN k /\ (x:real^2) IN (B:A->real^2->bool) a`; `a:A`] SELECT_AX) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_UNIONS THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN X_GEN_TAC `x:real^2` THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(B:A->real^2->bool) a` THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN EXISTS_TAC `(g:A->real^2->real^K) a` THEN
  ASM_SIMP_TAC[]);;

let CMC_FINITE_DIAG = prove
 (`!(P:A->(num->num)->bool) k.
     FINITE k /\
     (!i (r:num->num). i IN k /\ (!m n. m < n ==> r m < r n)
            ==> ?q:num->num. (!m n. m < n ==> q m < q n) /\ P i (r o q)) /\
     (!i (r:num->num) (q:num->num).
              i IN k /\ (!m n. m < n ==> r m < r n) /\ (!m n. m < n ==> q m < q n) /\
              P i r
              ==> P i (r o q))
     ==> !r:num->num. (!m n. m < n ==> r m < r n)
             ==> ?q:num->num. (!m n. m < n ==> q m < q n) /\ !i. i IN k ==> P i (r o q)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[TAUT `a /\ b /\ c ==> d <=> a ==> (b /\ c ==> d)`] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `\n:num. n` THEN REWRITE_TAC[NOT_IN_EMPTY] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `k:A->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH") STRIP_ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "EX") (LABEL_TAC "ST")) THEN
  X_GEN_TAC `r:num->num` THEN DISCH_TAC THEN
  REMOVE_THEN "IH" MP_TAC THEN ANTS_TAC THENL
   [CONJ_TAC THEN REPEAT STRIP_TAC THENL
     [USE_THEN "EX" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INSERT];
      USE_THEN "ST" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INSERT]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `r:num->num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q1:num->num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!m n. m < n ==> ((r:num->num) o (q1:num->num)) m < (r o q1) n`
  ASSUME_TAC THENL
   [REWRITE_TAC[o_THM] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "EX" (MP_TAC o SPECL [`a:A`; `(r:num->num) o (q1:num->num)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q2:num->num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(q1:num->num) o (q2:num->num)` THEN CONJ_TAC THENL
   [REWRITE_TAC[o_THM] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `i:A` THEN REWRITE_TAC[IN_INSERT] THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[o_ASSOC];
    REWRITE_TAC[o_ASSOC] THEN USE_THEN "ST" MATCH_MP_TAC THEN
    ASM_SIMP_TAC[IN_INSERT]]);;

(* ------------------------------------------------------------------------- *)
(* The angular derivative: algebra, rescaling, L^2 facts; changes of       *)
(* variables for the angular and the Euclidean energy; convergence of the  *)
(* quadratic integrals.                                                    *)
(* ------------------------------------------------------------------------- *)

let CMC_ANGD_FACTS = prove
 (`(!(y:real^2) x (g1:real^K) g2 s.
      cmc_angd y x (s % g1) (s % g2) = s % cmc_angd y x g1 g2) /\
   (!(y:real^2) x (g1:real^K) g2 h1 h2.
      cmc_angd y x g1 g2 - cmc_angd y x h1 h2 = cmc_angd y x (g1 - h1) (g2 - h2)) /\
   (!(y:real^2) x (g1:real^K) g2. norm(cmc_angd y x g1 g2) <= norm g1 + norm g2) /\
   (!(y:real^2) rho z (g1:real^K) g2.
      &0 < rho ==> cmc_angd y (y + rho % z) g1 g2 = cmc_angd (vec 0) z g1 g2)`,
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[cmc_angd] THEN VECTOR_ARITH_TAC;
    REWRITE_TAC[cmc_angd] THEN VECTOR_ARITH_TAC;
    REPEAT GEN_TAC THEN REWRITE_TAC[cmc_angd] THEN
    ASM_CASES_TAC `x:real^2 = y` THENL
     [ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0; REAL_INV_0; VECTOR_MUL_LZERO] THEN
      SIMP_TAC[REAL_LE_ADD; NORM_POS_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < norm(x - y:real^2)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
    REWRITE_TAC[NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ABS_INV; REAL_ARITH `&0 < x ==> abs x = x`] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs((x - y:real^2)$2) * norm(g1:real^K) + abs((x - y)$1) * norm(g2:real^K)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(NORM_ARITH `norm(a:real^K) <= u /\ norm b <= v ==> norm(a + b) <= u + v`) THEN
      REWRITE_TAC[NORM_MUL; REAL_ABS_NEG; REAL_LE_REFL];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= n * n1 /\ b <= n * n2 ==> a + b <= (n1 + n2) * n`) THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[NORM_POS_LE; COMPONENT_LE_NORM];
    REPEAT STRIP_TAC THEN REWRITE_TAC[cmc_angd] THEN
    REWRITE_TAC[VECTOR_ARITH `((y:real^2) + rho % z) - y = rho % z`; VECTOR_SUB_RZERO] THEN
    ASM_SIMP_TAC[NORM_MUL; REAL_ARITH `&0 < rho ==> abs rho = rho`; VECTOR_MUL_COMPONENT] THEN
    ASM_CASES_TAC `z:real^2 = vec 0` THENL
     [ASM_REWRITE_TAC[NORM_0; REAL_MUL_RZERO; REAL_INV_0; VECTOR_MUL_LZERO]; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC; REAL_INV_MUL] THEN
    BINOP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN UNDISCH_TAC `&0 < rho` THEN
    CONV_TAC REAL_FIELD]);;

let CMC_ANGD_MEASURABLE = prove
 (`!s (y:real^2) (g1:real^2->real^K) g2.
     open s /\ ~(y IN s) /\ g1 measurable_on s /\ g2 measurable_on s
     ==> (\x. cmc_angd y x (g1 x) (g2 x)) measurable_on s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. cmc_angd y x ((g1:real^2->real^K) x) (g2 x)) =
    (\x. (inv(norm(x - y)) * --((x - y:real^2)$2)) % g1 x +
         (inv(norm(x - y)) * (x - y)$1) % g2 x)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; cmc_angd] THEN GEN_TAC THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!i. (\x:real^2. lift(inv(norm(x - y)) * (x - y)$i)) continuous_on s`
  ASSUME_TAC THENL
   [GEN_TAC THEN ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT] THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(x:real^2 = y)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC[o_DEF] THEN
      MP_TAC(ISPECL [`at (x:real^2)`; `\x:real^2. norm(x - y)`] CONTINUOUS_INV) THEN
      REWRITE_TAC[o_DEF; NETLIMIT_AT] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[NORM_EQ_0; VECTOR_SUB_EQ] THEN
      MATCH_MP_TAC CONTINUOUS_LIFT_NORM_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_SUB; CONTINUOUS_CONST; CONTINUOUS_AT_ID];
      MATCH_MP_TAC CONTINUOUS_LIFT_COMPONENT_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_SUB; CONTINUOUS_CONST; CONTINUOUS_AT_ID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. (\x:real^2. lift(inv(norm(x - y)) * --((x - y)$i))) continuous_on s`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_MUL_RNEG; LIFT_NEG] THEN MATCH_MP_TAC CONTINUOUS_ON_NEG THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MEASURABLE_ON_ADD THEN CONJ_TAC THEN MATCH_MP_TAC MEASURABLE_ON_MUL THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN]);;

let CMC_ANGD_LSPACE = prove
 (`!s (y:real^2) (g1:real^2->real^K) g2.
     open s /\ ~(y IN s) /\ g1 IN lspace s (&2) /\ g2 IN lspace s (&2)
     ==> (\x. cmc_angd y x (g1 x) (g2 x)) IN lspace s (&2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `&2`;
                 `\x. cmc_angd y x ((g1:real^2->real^K) x) (g2 x)`;
                 `\x. lift(norm((g1:real^2->real^K) x)) + lift(norm((g2:real^2->real^K) x))`]
                LSPACE_BOUNDED_MEASURABLE) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THENL
   [REAL_ARITH_TAC;
    MATCH_MP_TAC CMC_ANGD_MEASURABLE THEN
    ASM_MESON_TAC[lspace; IN_ELIM_THM];
    MATCH_MP_TAC LSPACE_ADD THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_SIMP_TAC[LSPACE_NORM];
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[GSYM LIFT_ADD; NORM_LIFT] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> a <= abs b`) THEN REWRITE_TAC[CMC_ANGD_FACTS]]);;

let CMC_CV_ANG = prove
 (`!(g1:real^2->real^K) g2 (y:real^2) rho c r1 r2.
     &0 < rho /\ &0 < c /\
     (\x. cmc_angd y x (g1 x) (g2 x)) IN lspace (cmc_ann y (rho * r1) (rho * r2)) (&2)
     ==> (\z. cmc_angd (vec 0) z ((rho / c) % g1 (y + rho % z))
                                 ((rho / c) % g2 (y + rho % z)))
           IN lspace (cmc_ann (vec 0) r1 r2) (&2) /\
         lnorm (cmc_ann (vec 0) r1 r2) (&2)
           (\z. cmc_angd (vec 0) z ((rho / c) % g1 (y + rho % z))
                                   ((rho / c) % g2 (y + rho % z))) pow 2 =
         lnorm (cmc_ann y (rho * r1) (rho * r2)) (&2) (\x. cmc_angd y x (g1 x) (g2 x)) pow 2 /
         c pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z. cmc_angd (vec 0) z ((rho / c) % (g1:real^2->real^K) (y + rho % z))
                            ((rho / c) % g2 (y + rho % z))) =
    (\z. (rho / c) % (\x. cmc_angd y x (g1 x) (g2 x)) (y + rho % z))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; CMC_ANGD_FACTS] THEN GEN_TAC THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC(last(CONJUNCTS CMC_ANGD_FACTS)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. cmc_angd y x ((g1:real^2->real^K) x) (g2 x)`; `y:real^2`; `rho:real`;
                 `cmc_ann (vec 0:real^2) r1 r2`] CMC_SIM_LSPACE) THEN
  ASM_SIMP_TAC[CMC_SIM_ANN; VECTOR_MUL_RZERO; VECTOR_ADD_RID] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LSPACE_CMUL; LNORM_MUL; REAL_ARITH `~(&2 = &0)`; REAL_POW_MUL] THEN
  SUBGOAL_THEN `abs(rho / c) = rho / c` SUBST1_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs x = x`) THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_DIV] THEN UNDISCH_TAC `&0 < rho` THEN UNDISCH_TAC `&0 < c` THEN
  CONV_TAC REAL_FIELD);;

let CMC_CV_EE = prove
 (`!(g1:real^2->real^K) (g2:real^2->real^K) (y:real^2) rho c r1 r2.
     &0 < rho /\ &0 < c /\
     (\x. pastecart (g1 x) (g2 x)) IN lspace (cmc_ann y (rho * r1) (rho * r2)) (&2)
     ==> (\z. pastecart ((rho / c) % g1 (y + rho % z)) ((rho / c) % g2 (y + rho % z)))
           IN lspace (cmc_ann (vec 0) r1 r2) (&2) /\
         lnorm (cmc_ann (vec 0) r1 r2) (&2)
           (\z. pastecart ((rho / c) % g1 (y + rho % z))
                          ((rho / c) % g2 (y + rho % z))) pow 2 =
         lnorm (cmc_ann y (rho * r1) (rho * r2)) (&2) (\x. pastecart (g1 x) (g2 x)) pow 2 /
         c pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z. pastecart ((rho / c) % (g1:real^2->real^K) (y + rho % z))
                   ((rho / c) % (g2:real^2->real^K) (y + rho % z))) =
    (\z. (rho / c) % (\x. pastecart (g1 x) (g2 x)) (y + rho % z))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; PASTECART_CMUL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. pastecart ((g1:real^2->real^K) x) ((g2:real^2->real^K) x)`;
                 `y:real^2`; `rho:real`;
                 `cmc_ann (vec 0:real^2) r1 r2`] CMC_SIM_LSPACE) THEN
  ASM_SIMP_TAC[CMC_SIM_ANN; VECTOR_MUL_RZERO; VECTOR_ADD_RID] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LSPACE_CMUL; LNORM_MUL; REAL_ARITH `~(&2 = &0)`; REAL_POW_MUL] THEN
  SUBGOAL_THEN `abs(rho / c) = rho / c` SUBST1_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs x = x`) THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_DIV] THEN UNDISCH_TAC `&0 < rho` THEN UNDISCH_TAC `&0 < c` THEN
  CONV_TAC REAL_FIELD);;

let CMC_LNORM_SQ_CONV = prove
 (`!E (f:num->real^2->real^N) f0.
     (!j. f j IN lspace E (&2)) /\ f0 IN lspace E (&2) /\
     ((\j. lnorm E (&2) (\x. f j x - f0 x)) ---> &0) sequentially
     ==> ((\j. lnorm E (&2) (f j) pow 2) ---> lnorm E (&2) f0 pow 2) sequentially`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REALLIM_POW THEN
  ONCE_REWRITE_TAC[REALLIM_NULL] THEN MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\j. lnorm E (&2) (\x. (f:num->real^2->real^N) j x - f0 x)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `j:num` THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\x. (f:num->real^2->real^N) j x - f0 x) IN lspace E (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`E:real^2->bool`; `&2`; `f0:real^2->real^N`;
                 `\x. (f:num->real^2->real^N) j x - f0 x`] LNORM_TRIANGLE) THEN
  MP_TAC(ISPECL [`E:real^2->bool`; `&2`; `(f:num->real^2->real^N) j`;
                 `\x. --((f:num->real^2->real^N) j x - f0 x)`] LNORM_TRIANGLE) THEN
  ASM_SIMP_TAC[LSPACE_NEG; LNORM_NEG; ETA_AX] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[VECTOR_ARITH `(a:real^N) + --(a - b) = b`;
              VECTOR_ARITH `(b:real^N) + (a - b) = a`; ETA_AX] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Geometry of the annuli in CM Lemma B.31; bounded real sequences; the    *)
(* energies as L^2 norms.                                                  *)
(* ------------------------------------------------------------------------- *)

let CMC_EXP_LADDER = prove
 (`!l. &1 <= l
       ==> &0 < exp(--(&3 * l)) /\ exp(--(&3 * l)) < exp(--(&2 * l)) /\
           exp(--(&2 * l)) < exp(--l) /\ exp(--l) < exp l /\ exp l < exp(&2 * l) /\
           exp(&2 * l) < exp(&3 * l) /\ &2 * exp(&2 * l) <= exp(&3 * l) /\
           exp(--(&2 * l)) <= &1 /\ &1 <= exp(&2 * l)`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_EXP_POS_LT; REAL_EXP_MONO_LT] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `exp(&3 * l) = exp l * exp(&2 * l)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    MP_TAC(SPEC `l:real` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC;
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    ASM_REAL_ARITH_TAC;
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    ASM_REAL_ARITH_TAC]);;

let CMC_B31_GEOM = prove
 (`!l a z.
     &1 <= l /\ exp(--(&2 * l)) <= norm a /\
     norm a < exp(&2 * l) + (exp(--(&2 * l)) - exp(--(&3 * l))) / &2 /\
     norm(z - a) <= (exp(--(&2 * l)) - exp(--(&3 * l))) / &2
     ==> z IN cmc_ann (vec 0) (exp(--(&3 * l))) (exp(&3 * l))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMC_EXP_LADDER) THEN
  REWRITE_TAC[cmc_ann; IN_ELIM_THM; VECTOR_SUB_RZERO] THEN
  MP_TAC(ISPECL [`z:real^2`; `a:real^2`] NORM_TRIANGLE_SUB) THEN
  MP_TAC(ISPECL [`a:real^2`; `z:real^2`] NORM_TRIANGLE_SUB) THEN
  REWRITE_TAC[NORM_SUB] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
  UNDISCH_TAC `norm(z - a:real^2) <= (exp(--(&2 * l)) - exp(--(&3 * l))) / &2` THEN
  UNDISCH_TAC `norm(a:real^2) < exp(&2 * l) + (exp(--(&2 * l)) - exp(--(&3 * l))) / &2` THEN
  UNDISCH_TAC `exp(--(&2 * l)) <= norm(a:real^2)` THEN
  UNDISCH_TAC `&2 * exp(&2 * l) <= exp(&3 * l)` THEN
  UNDISCH_TAC `exp(--(&2 * l)) <= &1` THEN UNDISCH_TAC `&1 <= exp(&2 * l)` THEN
  UNDISCH_TAC `&0 < exp(--(&3 * l))` THEN
  UNDISCH_TAC `exp(--(&3 * l)) < exp(--(&2 * l))` THEN
  REAL_ARITH_TAC);;

let CMC_SIM_CBALL_ANN = prove
 (`!(y:real^2) rho a R r1 r2.
     &0 < rho /\ cball(a,R) SUBSET cmc_ann (vec 0) r1 r2
     ==> cball(y + rho % a,rho * R) SUBSET cmc_ann y (rho * r1) (rho * r2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^2` THEN
  REWRITE_TAC[IN_CBALL] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^2) = y + rho % (inv rho % (x - y))` SUBST_ALL_TAC THENL
   [ASM_SIMP_TAC[CMC_SIM_SURJ]; ALL_TAC] THEN
  ABBREV_TAC `z:real^2 = inv rho % (x - y)` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^2` o REWRITE_RULE[SUBSET]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_CBALL] THEN UNDISCH_TAC `dist(y + rho % a,y + rho % (z:real^2)) <= rho * R` THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist] THEN
    ASM_SIMP_TAC[CMC_SIM_NORM; REAL_LE_LMUL_EQ] THEN MESON_TAC[NORM_SUB];
    ALL_TAC] THEN
  REWRITE_TAC[cmc_ann; IN_ELIM_THM; VECTOR_SUB_RZERO] THEN
  REWRITE_TAC[VECTOR_ARITH `((y:real^2) + rho % z) - y = rho % z`] THEN
  ASM_SIMP_TAC[NORM_MUL; REAL_ARITH `&0 < rho ==> abs rho = rho`; REAL_LT_LMUL_EQ]);;

let CMC_BOUNDED_SUBSEQ = prove
 (`!(c:num->real) B.
     (!j. &0 <= c j /\ c j <= B)
     ==> ?(t:num->num) c0. (!m n. m < n ==> t m < t n) /\ &0 <= c0 /\ c0 <= B /\
                          ((\j. c (t j)) ---> c0) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift(&0)`; `lift B`] COMPACT_INTERVAL) THEN REWRITE_TAC[compact] THEN
  DISCH_THEN(MP_TAC o SPEC `\j. lift((c:num->real) j)`) THEN
  REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^1` (X_CHOOSE_THEN `t:num->num` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`t:num->num`; `drop l`] THEN ASM_REWRITE_TAC[TENDSTO_REAL] THEN
  UNDISCH_TAC `(((\j. lift((c:num->real) j)) o (t:num->num)) --> l) sequentially` THEN
  REWRITE_TAC[o_DEF; LIFT_DROP]);;

(* ------------------------------------------------------------------------- *)
(* CM Lemma B.31, step 1: the normalized rescaled replacements on all balls  *)
(* of the cover, along the contradiction sequence.                           *)
(* ------------------------------------------------------------------------- *)

let cmc_nk = new_definition
 `cmc_nk (y:real^2) rho t = cmc_ann y (rho * exp(--t)) (rho * exp t)`;;

let cmc_r31 = new_definition
 `cmc_r31 l = (exp(--(&2 * l)) - exp(--(&3 * l))) / &2`;;

let cmc_cs = new_definition
 `cmc_cs l = {a:real^2 | exp(--(&2 * l)) <= norm a /\ norm a < exp(&2 * l) + cmc_r31 l}`;;

let CMC_ENERGIES_L2 = prove
 (`!S (w:real^2->real^K) (y:real^2) E.
     cmc_pmap S w /\ open E /\ ~(y IN E)
     ==> (\x. cmc_angd y x (wan_wd (:real^2) 1 w x) (wan_wd (:real^2) 2 w x))
           IN lspace E (&2) /\
         cmc_angE y E w =
         lnorm E (&2) (\x. cmc_angd y x (wan_wd (:real^2) 1 w x)
                                        (wan_wd (:real^2) 2 w x)) pow 2 /\
         (\x. pastecart (wan_wd (:real^2) 1 w x) (wan_wd (:real^2) 2 w x))
           IN lspace E (&2) /\
         cmc_eE E w =
         lnorm E (&2) (\x. pastecart (wan_wd (:real^2) 1 w x)
                                     (wan_wd (:real^2) 2 w x)) pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= 2 ==> wan_wd (:real^2) i (w:real^2->real^K) IN lspace E (&2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    ASM_SIMP_TAC[SUBSET_UNIV; LEBESGUE_MEASURABLE_OPEN] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `w:real^2->real^K`; `i:num`] CMC_PMAP_WD) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_wd (:real^2) 1 (w:real^2->real^K) IN lspace E (&2) /\
                wan_wd (:real^2) 2 (w:real^2->real^K) IN lspace E (&2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. cmc_angd y x (wan_wd (:real^2) 1 (w:real^2->real^K) x) (wan_wd (:real^2) 2 w x))
    IN lspace E (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC CMC_ANGD_LSPACE THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. pastecart (wan_wd (:real^2) 1 (w:real^2->real^K) x) (wan_wd (:real^2) 2 w x))
    IN lspace E (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC CMC_LSPACE2_PASTECART THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  ASM_SIMP_TAC[WAN_SOB_LNORM2_SQ; cmc_angE; cmc_eE; CMW_NORM_PASTECART_POW2]);;

let CMC_R31_FACTS = prove
 (`!l. &1 <= l
       ==> &0 < cmc_r31 l /\ cmc_r31 l <= &1 /\
           (!a. a IN cmc_cs l ==> cball(a,cmc_r31 l) SUBSET cmc_nk (vec 0) (&1) (&3 * l)) /\
           (!a. exp(--(&2 * l)) <= norm a /\ norm a <= exp(&2 * l) ==> a IN cmc_cs l)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMC_EXP_LADDER) THEN
  REWRITE_TAC[cmc_r31; cmc_cs; cmc_nk; IN_ELIM_THM; REAL_MUL_LID] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `a:real^2` THEN STRIP_TAC THEN REWRITE_TAC[SUBSET; IN_CBALL] THEN
    X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN MATCH_MP_TAC CMC_B31_GEOM THEN
    EXISTS_TAC `a:real^2` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[dist; NORM_SUB];
    REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC]);;

let CMC_OPEN_ANN = prove
 (`!(y:real^2) r1 r2. open(cmc_ann y r1 r2)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `cmc_ann (y:real^2) r1 r2 = ball(y,r2) DIFF cball(y,r1)` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; cmc_ann; IN_ELIM_THM; IN_DIFF; IN_BALL; IN_CBALL] THEN
    GEN_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist] THEN REAL_ARITH_TAC;
    SIMP_TAC[OPEN_DIFF; OPEN_BALL; CLOSED_CBALL]]);;

let CMC_B31_PREP = prove
 (`!S (G:real^K->real^K^K) d eL (C:num->real) l (w:num->real^2->real^K) (y:num->real^2)
    (rho:num->real) (mu:num->real).
     cm_target S G d /\ cmc_regc S G eL C /\ &1 <= l /\
     (!j. cmc_pmap S (w j) /\ &0 < rho j /\
          &0 < cmc_pen G (cmc_nk (y j) (rho j) (&3 * l)) (w j) /\
          cmc_pen G (cmc_nk (y j) (rho j) (&3 * l)) (w j) <= eL /\
          cmc_srb S G (mu j) (cmc_nk (y j) (rho j) (&3 * l)) (w j))
     ==> ?(P:num->real^2->real^K) (V:num->real^2->real^2->real^K).
           !j a. a IN cmc_cs l
                 ==> P j a IN S /\ smooth_map_on (ball(a,cmc_r31 l / &8)) (V j a) /\
                     V j a a = vec 0 /\
                     (!z. z IN ball(a,cmc_r31 l / &8)
                          ==> P j a + sqrt(cmc_pen G (cmc_nk (y j) (rho j) (&3 * l)) (w j)) %
                                      V j a z IN S) /\
                     (!l' z. ALL (\i. 1 <= i /\ i <= 2) l' /\ ~(l' = []) /\
                             z IN ball(a,cmc_r31 l / &16)
                             ==> norm(iterated_partial l' (V j a) z) <=
                                 C (LENGTH l') * (&8 / cmc_r31 l) pow (LENGTH l')) /\
                     (!z. z IN ball(a,cmc_r31 l / &16) ==> norm(V j a z) <= C 1) /\
                     (\z. inv(sqrt(cmc_pen G (cmc_nk (y j) (rho j) (&3 * l)) (w j))) %
                          (w j (y j + rho j % z) - P j a) - V j a z)
                       IN lspace (ball(a,cmc_r31 l / &8)) (&2) /\
                     lnorm (ball(a,cmc_r31 l / &8)) (&2)
                       (\z. inv(sqrt(cmc_pen G (cmc_nk (y j) (rho j) (&3 * l)) (w j))) %
                            (w j (y j + rho j % z) - P j a) - V j a z) pow 2
                       <= &4 * (cmc_r31 l / &8) pow 2 * mu j /\
                     (!i. 1 <= i /\ i <= 2
                          ==> (\z. (rho j / sqrt(cmc_pen G (cmc_nk (y j) (rho j) (&3 * l)) (w j))) %
                                   wan_wd (:real^2) i (w j) (y j + rho j % z) -
                                   partial_derivative i (V j a) z)
                                IN lspace (ball(a,cmc_r31 l / &8)) (&2) /\
                              lnorm (ball(a,cmc_r31 l / &8)) (&2)
                                (\z. (rho j / sqrt(cmc_pen G (cmc_nk (y j) (rho j) (&3 * l))
                                                            (w j))) %
                                     wan_wd (:real^2) i (w j) (y j + rho j % z) -
                                     partial_derivative i (V j a) z) pow 2 <= mu j) /\
                     (!z. z IN ball(a,cmc_r31 l / &8)
                          ==> (!i. hmr_tp S (P j a + sqrt(cmc_pen G (cmc_nk (y j) (rho j) (&3 * l))
                                                                 (w j)) % V j a z) **
                                   partial_derivative i (V j a) z =
                                   partial_derivative i (V j a) z) /\
                              hmr_tp S (P j a + sqrt(cmc_pen G (cmc_nk (y j) (rho j) (&3 * l)) (w j)) %
                                                V j a z) **
                                (hmr_vlap (V j a) z +
                                 sqrt(cmc_pen G (cmc_nk (y j) (rho j) (&3 * l)) (w j)) %
                                 vsum(1..2) (\i. christoffel G
                                                   (P j a + sqrt(cmc_pen G (cmc_nk (y j) (rho j)
                                                                   (&3 * l)) (w j)) % V j a z)
                                                   (partial_derivative i (V j a) z)
                                                   (partial_derivative i (V j a) z))) = vec 0 /\
                              hmr_vlap (V j a) z =
                                sqrt(cmc_pen G (cmc_nk (y j) (rho j) (&3 * l)) (w j)) %
                                vsum(1..2) (\i. hmr_bq S G
                                                  (P j a + sqrt(cmc_pen G (cmc_nk (y j) (rho j)
                                                                  (&3 * l)) (w j)) % V j a z)
                                                  (partial_derivative i (V j a) z)
                                                  (partial_derivative i (V j a) z)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMC_R31_FACTS) THEN
  REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
  MAP_EVERY X_GEN_TAC [`j:num`; `a:real^2`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `j:num`) THEN
  ABBREV_TAC `D = cmc_pen G (cmc_nk ((y:num->real^2) j) ((rho:num->real) j) (&3 * l))
                     ((w:num->real^2->real^K) j)` THEN
  SUBGOAL_THEN `&0 < sqrt D` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN

  SUBGOAL_THEN `cball((y:num->real^2) j + (rho:num->real) j % a,rho j * cmc_r31 l) SUBSET
                cmc_nk (y j) (rho j) (&3 * l)` ASSUME_TAC THENL
   [REWRITE_TAC[cmc_nk] THEN
    SUBGOAL_THEN `(rho:num->real) j * exp(--(&3 * l)) = rho j * (&1 * exp(--(&3 * l))) /\
                  rho j * exp(&3 * l) = rho j * (&1 * exp(&3 * l))` (fun th -> ONCE_REWRITE_TAC[th])
    THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC CMC_SIM_CBALL_ANN THEN ASM_REWRITE_TAC[GSYM cmc_nk] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `eL:real`; `C:num->real`;
                 `(w:num->real^2->real^K) j`; `(y:num->real^2) j`; `(rho:num->real) j`;
                 `a:real^2`; `cmc_r31 l`; `sqrt D`; `(mu:num->real) j`] CMC_NREP) THEN
  SUBGOAL_THEN `sqrt D pow 2 = D` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                     `(w:num->real^2->real^K) j`;
                     `ball((y:num->real^2) j + (rho:num->real) j % a,rho j * cmc_r31 l / &8)`]
                    CMC_GDIR_PEN) THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN DISCH_THEN SUBST1_TAC THEN
      EXPAND_TAC "D" THEN MATCH_MP_TAC CMC_PEN_MONO THEN
      MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_BALL; cmc_nk; LEBESGUE_MEASURABLE_OPEN; CMC_OPEN_ANN] THEN
      REWRITE_TAC[GSYM cmc_nk] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `cball((y:num->real^2) j + (rho:num->real) j % a,rho j * cmc_r31 l)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `ball((y:num->real^2) j + (rho:num->real) j % a,rho j * cmc_r31 l)` THEN
        REWRITE_TAC[BALL_SUBSET_CBALL] THEN MATCH_MP_TAC SUBSET_BALL THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[GSYM cmc_nk]];
      ALL_TAC] THEN
    X_GEN_TAC `v:real^2->real^K` THEN STRIP_TAC THEN
    UNDISCH_TAC `cmc_srb S G ((mu:num->real) j) (cmc_nk ((y:num->real^2) j) ((rho:num->real) j)
                   (&3 * l)) ((w:num->real^2->real^K) j)` THEN
    REWRITE_TAC[cmc_srb] THEN
    DISCH_THEN(MP_TAC o SPECL [`(y:num->real^2) j + (rho:num->real) j % a`;
                               `(rho:num->real) j * cmc_r31 l`; `v:real^2->real^K`]) THEN
    REWRITE_TAC[REAL_ARITH `(r * x) / &8 = r * x / &8`] THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* CM Lemma B.31, step 2: local limits on the centers of a finite cover,     *)
(* with the offsets of the base points.                                      *)
(* ------------------------------------------------------------------------- *)

let cmc_b31dat = new_definition
 `cmc_b31dat (S:real^K->bool) (G:real^K->real^K^K) (C:num->real) R
     (w:real^2->real^K) (y:real^2) rho c mu (p:real^K) (V:real^2->real^K) (a:real^2) <=>
    p IN S /\ smooth_map_on (ball(a,R / &8)) V /\ V a = vec 0 /\
    (!z. z IN ball(a,R / &8) ==> p + c % V z IN S) /\
    (!l z. ALL (\i. 1 <= i /\ i <= 2) l /\ ~(l = []) /\ z IN ball(a,R / &16)
           ==> norm(iterated_partial l V z) <= C (LENGTH l) * (&8 / R) pow (LENGTH l)) /\
    (!z. z IN ball(a,R / &16) ==> norm(V z) <= C 1) /\
    (\z. inv c % (w(y + rho % z) - p) - V z) IN lspace (ball(a,R / &8)) (&2) /\
    lnorm (ball(a,R / &8)) (&2) (\z. inv c % (w(y + rho % z) - p) - V z) pow 2
      <= &4 * (R / &8) pow 2 * mu /\
    (!i. 1 <= i /\ i <= 2
         ==> (\z. (rho / c) % wan_wd (:real^2) i w (y + rho % z) -
                  partial_derivative i V z) IN lspace (ball(a,R / &8)) (&2) /\
             lnorm (ball(a,R / &8)) (&2)
               (\z. (rho / c) % wan_wd (:real^2) i w (y + rho % z) -
                    partial_derivative i V z) pow 2 <= mu) /\
    (!z. z IN ball(a,R / &8)
         ==> (!i. hmr_tp S (p + c % V z) ** partial_derivative i V z =
                  partial_derivative i V z) /\
             hmr_tp S (p + c % V z) **
               (hmr_vlap V z +
                c % vsum(1..2) (\i. christoffel G (p + c % V z)
                                      (partial_derivative i V z)
                                      (partial_derivative i V z))) = vec 0 /\
             hmr_vlap V z =
               c % vsum(1..2) (\i. hmr_bq S G (p + c % V z)
                                      (partial_derivative i V z)
                                      (partial_derivative i V z)))`;;

let cmc_b31loc = new_definition
 `cmc_b31loc (S:real^K->bool) (G:real^K->real^K^K) (C:num->real) R c0
     (w:num->real^2->real^K) (y:num->real^2) (rho:num->real) (c:num->real)
     (P:num->real^2->real^K) (a0:real^2) (a:real^2) (s:num->num)
     (U:real^2->real^K) (p:real^K) (kap:real^K) <=>
    smooth_map_on (ball(a,R / &32)) U /\ p IN S /\
    (!i z. 1 <= i /\ i <= 2 /\ z IN ball(a,R / &32)
           ==> norm(partial_derivative i U z) <= C 1 * &8 / R) /\
    (!z. z IN ball(a,R / &32)
         ==> p + c0 % U z IN S /\
             (!i. 1 <= i /\ i <= 2
                  ==> hmr_tp S (p + c0 % U z) ** partial_derivative i U z =
                      partial_derivative i U z) /\
             hmr_tp S (p + c0 % U z) **
               (hmr_vlap U z +
                c0 % vsum(1..2) (\i. christoffel G (p + c0 % U z)
                                       (partial_derivative i U z)
                                       (partial_derivative i U z))) = vec 0 /\
             hmr_vlap U z =
               c0 % vsum(1..2) (\i. hmr_bq S G (p + c0 % U z)
                                       (partial_derivative i U z)
                                       (partial_derivative i U z))) /\
    ((\j. P (s j) a) --> p) sequentially /\
    ((\j. inv(c (s j)) % (P (s j) a - P (s j) a0)) --> kap) sequentially /\
    (!j. (\z. inv(c (s j)) % (w (s j) (y (s j) + rho (s j) % z) - P (s j) a) - U z)
         IN lspace (ball(a,R / &32)) (&2)) /\
    ((\j. lnorm (ball(a,R / &32)) (&2)
            (\z. inv(c (s j)) % (w (s j) (y (s j) + rho (s j) % z) - P (s j) a) - U z))
     ---> &0) sequentially /\
    (!i. 1 <= i /\ i <= 2
         ==> (!j. (\z. (rho (s j) / c (s j)) %
                       wan_wd (:real^2) i (w (s j)) (y (s j) + rho (s j) % z) -
                       partial_derivative i U z) IN lspace (ball(a,R / &32)) (&2)) /\
             ((\j. lnorm (ball(a,R / &32)) (&2)
                     (\z. (rho (s j) / c (s j)) %
                          wan_wd (:real^2) i (w (s j)) (y (s j) + rho (s j) % z) -
                          partial_derivative i U z)) ---> &0) sequentially)`;;

let CMC_B31LOC_SUBSEQ = prove
 (`!S (G:real^K->real^K^K) C R c0 (w:num->real^2->real^K) y rho c P a0 a s q U p kap.
     cmc_b31loc S G C R c0 w y rho c P a0 a s U p kap /\ (!m n. m < n ==> q m < q n)
     ==> cmc_b31loc S G C R c0 w y rho c P a0 a (s o q) U p kap`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmc_b31loc; o_THM] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`\j. (P:num->real^2->real^K) ((s:num->num) j) a`; `q:num->num`;
                   `p:real^K`] LIM_SUBSEQUENCE) THEN ASM_REWRITE_TAC[o_DEF];
    MP_TAC(ISPECL [`\j. inv((c:num->real) ((s:num->num) j)) %
                        ((P:num->real^2->real^K) (s j) a - P (s j) a0)`; `q:num->num`;
                   `kap:real^K`] LIM_SUBSEQUENCE) THEN ASM_REWRITE_TAC[o_DEF];
    MP_TAC(ISPECL [`\j. lnorm (ball(a,R / &32)) (&2)
                         (\z. inv((c:num->real) ((s:num->num) j)) %
                              ((w:num->real^2->real^K) (s j) ((y:num->real^2) (s j) +
                               (rho:num->real) (s j) % z) -
                               (P:num->real^2->real^K) (s j) a) - (U:real^2->real^K) z)`;
                   `&0`; `q:num->num`] HMD_REALLIM_SUBSEQ) THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `wan_wd:(real^2->bool)->num->(real^2->real^K)->real^2->real^K`))
        (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\j. lnorm (ball(a,R / &32)) (&2)
                         (\z. ((rho:num->real) ((s:num->num) j) / (c:num->real) (s j)) %
                              wan_wd (:real^2) i ((w:num->real^2->real^K) (s j))
                                ((y:num->real^2) (s j) + rho (s j) % z) -
                              partial_derivative i (U:real^2->real^K) z)`;
                   `&0`; `q:num->num`] HMD_REALLIM_SUBSEQ) THEN ASM_REWRITE_TAC[]]);;

let CMC_B31LOC_EXISTS = prove
 (`!S (G:real^K->real^K^K) d (C:num->real) R c0 (w:num->real^2->real^K) (y:num->real^2)
    (rho:num->real) (c:num->real) (mu:num->real) (P:num->real^2->real^K)
    (V:num->real^2->real^2->real^K) a0 a (s:num->num).
     cm_target S G d /\ &0 < R /\ (!k. &0 < C k) /\
     (!j. &0 < c j) /\ (c ---> c0) sequentially /\ (mu ---> &0) sequentially /\
     (!j. cmc_b31dat S G C R (w j) (y j) (rho j) (c j) (mu j) (P j a) (V j a) a) /\
     (?M. !j. norm(P j a - P j a0) <= M * c j) /\
     (!m n. m < n ==> s m < s n)
     ==> ?(q:num->num) U p kap.
           (!m n. m < n ==> q m < q n) /\
           cmc_b31loc S G C R c0 w y rho c P a0 a (s o q) U p kap`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "DAT")
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `M:real`) ASSUME_TAC)))))))) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `C:num->real`;
                 `w:num->real^2->real^K`; `y:num->real^2`; `rho:num->real`; `c:num->real`;
                 `c0:real`; `mu:num->real`; `\j. (P:num->real^2->real^K) j a`;
                 `\j. (V:num->real^2->real^2->real^K) j a`; `a:real^2`; `R:real`;
                 `s:num->num`] CMC_NLOC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN
    USE_THEN "DAT" (MP_TAC o SPEC `j:num`) THEN REWRITE_TAC[cmc_b31dat] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num->num` (X_CHOOSE_THEN `U:real^2->real^K`
    (X_CHOOSE_THEN `p:real^K` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `!m n. m < n ==> (s:num->num) ((k:num->num) m) < s (k n)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th) THEN
    FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`vec 0:real^K`; `M:real`] COMPACT_CBALL) THEN REWRITE_TAC[compact] THEN
  DISCH_THEN(MP_TAC o SPEC
    `\n. inv((c:num->real) ((s:num->num) ((k:num->num) n))) %
         ((P:num->real^2->real^K) (s (k n)) a - P (s (k n)) a0)`) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_CBALL_0; NORM_MUL] THEN
    ABBREV_TAC `jj = (s:num->num) ((k:num->num) n)` THEN
    SUBGOAL_THEN `abs(inv((c:num->real) jj)) = inv(c jj)` SUBST1_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs x = x`) THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `kap:real^K` (X_CHOOSE_THEN `k2:num->num` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`(k:num->num) o (k2:num->num)`; `U:real^2->real^K`; `p:real^K`;
                        `kap:real^K`] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[o_THM] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th) THEN
    FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[cmc_b31loc; o_THM] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`\j. (P:num->real^2->real^K) ((s:num->num) ((k:num->num) j)) a`;
                   `k2:num->num`; `p:real^K`] LIM_SUBSEQUENCE) THEN
    ASM_REWRITE_TAC[o_DEF];
    UNDISCH_TAC `(((\n. inv((c:num->real) ((s:num->num) ((k:num->num) n))) %
                         ((P:num->real^2->real^K) (s (k n)) a - P (s (k n)) a0)) o k2) --> kap)
                 sequentially` THEN REWRITE_TAC[o_DEF];
    MP_TAC(ISPECL [`\m. lnorm (ball(a,R / &32)) (&2)
                         (\z. inv((c:num->real) ((s:num->num) ((k:num->num) m))) %
                              ((w:num->real^2->real^K) (s (k m)) ((y:num->real^2) (s (k m)) +
                               (rho:num->real) (s (k m)) % z) -
                               (P:num->real^2->real^K) (s (k m)) a) - (U:real^2->real^K) z)`;
                   `&0`; `k2:num->num`] HMD_REALLIM_SUBSEQ) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `wan_wd:(real^2->bool)->num->(real^2->real^K)->real^2->real^K`))
        (concl th) && can (find_term ((=) `(--->):(num->real)->real->(num)net->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\m. lnorm (ball(a,R / &32)) (&2)
                         (\z. ((rho:num->real) ((s:num->num) ((k:num->num) m)) /
                               (c:num->real) (s (k m))) %
                              wan_wd (:real^2) i ((w:num->real^2->real^K) (s (k m)))
                                ((y:num->real^2) (s (k m)) + rho (s (k m)) % z) -
                              partial_derivative i (U:real^2->real^K) z)`;
                   `&0`; `k2:num->num`] HMD_REALLIM_SUBSEQ) THEN
    ASM_REWRITE_TAC[]]);;

let CMC_B31_FINEXT = prove
 (`!S (G:real^K->real^K^K) d (C:num->real) R c0 (w:num->real^2->real^K) (y:num->real^2)
    (rho:num->real) (c:num->real) (mu:num->real) (P:num->real^2->real^K)
    (V:num->real^2->real^2->real^K) a0 k.
     cm_target S G d /\ &0 < R /\ (!k. &0 < C k) /\
     (!j. &0 < c j) /\ (c ---> c0) sequentially /\ (mu ---> &0) sequentially /\
     FINITE k /\
     (!a j. a IN k
            ==> cmc_b31dat S G C R (w j) (y j) (rho j) (c j) (mu j) (P j a) (V j a) a) /\
     (!a. a IN k ==> ?M. !j. norm(P j a - P j a0) <= M * c j)
     ==> ?(q:num->num) (UU:real^2->real^2->real^K) (pp:real^2->real^K) (kk:real^2->real^K).
           (!m n. m < n ==> q m < q n) /\
           !a. a IN k
               ==> cmc_b31loc S G C R c0 w y rho c P a0 a q (UU a) (pp a) (kk a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\a (r:num->num). ?(U:real^2->real^K) (p:real^K) (kap:real^K).
                     cmc_b31loc S (G:real^K->real^K^K) C R c0 (w:num->real^2->real^K)
                       (y:num->real^2) (rho:num->real) (c:num->real)
                       (P:num->real^2->real^K) a0 a r U p kap`;
                 `k:real^2->bool`] CMC_FINITE_DIAG) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`a:real^2`; `r:num->num`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `C:num->real`;
                     `R:real`; `c0:real`; `w:num->real^2->real^K`; `y:num->real^2`;
                     `rho:num->real`; `c:num->real`; `mu:num->real`;
                     `P:num->real^2->real^K`; `V:num->real^2->real^2->real^K`;
                     `a0:real^2`; `a:real^2`; `r:num->num`] CMC_B31LOC_EXISTS) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[]; MESON_TAC[]];
      MAP_EVERY X_GEN_TAC [`a:real^2`; `r:num->num`; `q:num->num`] THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [`U:real^2->real^K`; `p:real^K`; `kap:real^K`] THEN
      MATCH_MP_TAC CMC_B31LOC_SUBSEQ THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `\n:num. n`) THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num->num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(\n:num. n) o (q:num->num) = q` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
  THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `UU:real^2->real^2->real^K` (X_CHOOSE_THEN `pp:real^2->real^K`
    (X_CHOOSE_TAC `kk:real^2->real^K`))) THEN
  MAP_EVERY EXISTS_TAC [`q:num->num`; `UU:real^2->real^2->real^K`; `pp:real^2->real^K`;
                        `kk:real^2->real^K`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* CM Lemma B.31, step 3: gluing the local limits into one map on a        *)
(* neighbourhood of the closed annulus.                                    *)
(* ------------------------------------------------------------------------- *)

let CMC_LNORM_COVER_GEN = prove
 (`!K (B:A->real^2->bool) ks (f:real^2->real^K).
     FINITE ks /\ f IN lspace K (&2) /\ (!m. m IN ks ==> f IN lspace (B m) (&2)) /\
     K SUBSET UNIONS (IMAGE B ks)
     ==> lnorm K (&2) f pow 2 <= sum ks (\m. lnorm (B m) (&2) f pow 2)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WAN_SOB_LNORM2_SQ] THEN
  ONCE_REWRITE_TAC[GSYM INTEGRAL_RESTRICT_UNIV] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `drop(integral (:real^2)
      (\x. vsum ks (\m. if x IN (B:A->real^2->bool) m
                       then lift(norm((f:real^2->real^K) x) pow 2) else vec 0)))` THEN
  SUBGOAL_THEN
   `!m. m IN ks
        ==> (\x. if x IN (B:A->real^2->bool) m
                 then lift(norm((f:real^2->real^K) x) pow 2) else vec 0)
            integrable_on (:real^2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV] THEN
    MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV] THEN
      MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC INTEGRABLE_VSUM THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[DROP_VSUM; o_DEF] THEN
      COND_CASES_TAC THENL
       [SUBGOAL_THEN `?m0:A. m0 IN ks /\ (x:real^2) IN (B:A->real^2->bool) m0`
        STRIP_ASSUME_TAC THENL
         [UNDISCH_TAC `K SUBSET UNIONS (IMAGE (B:A->real^2->bool) ks)` THEN
          REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN ASM_MESON_TAC[];
          ALL_TAC] THEN
        MP_TAC(ISPECL [`\m. drop(if (x:real^2) IN (B:A->real^2->bool) m
                                 then lift(norm((f:real^2->real^K) x) pow 2) else vec 0)`;
                       `ks:A->bool`; `m0:A`] SUM_DELETE) THEN
        ASM_REWRITE_TAC[LIFT_DROP] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= a ==> a = b - c ==> c <= b`) THEN
        MATCH_MP_TAC SUM_POS_LE THEN GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[] THEN
        COND_CASES_TAC THEN REWRITE_TAC[LIFT_DROP; DROP_VEC; REAL_LE_POW_2; REAL_LE_REFL];
        REWRITE_TAC[DROP_VEC] THEN MATCH_MP_TAC SUM_POS_LE THEN GEN_TAC THEN
        DISCH_TAC THEN REWRITE_TAC[] THEN
        COND_CASES_TAC THEN REWRITE_TAC[LIFT_DROP; DROP_VEC; REAL_LE_POW_2; REAL_LE_REFL]]];
    ASM_SIMP_TAC[INTEGRAL_VSUM; DROP_VSUM; o_DEF] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `m:A` THEN DISCH_TAC THEN REWRITE_TAC[INTEGRAL_RESTRICT_UNIV] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC WAN_SOB_LNORM2_SQ THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let CMC_NULL_COVER_GEN = prove
 (`!K (B:A->real^2->bool) ks (f:num->real^2->real^K).
     FINITE ks /\ (!j. f j IN lspace K (&2)) /\
     (!m. m IN ks ==> (!j. f j IN lspace (B m) (&2)) /\
                     ((\j. lnorm (B m) (&2) (f j)) ---> &0) sequentially) /\
     K SUBSET UNIONS (IMAGE B ks)
     ==> ((\j. lnorm K (&2) (f j)) ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CMC_SQ_NULL THEN
  MAP_EVERY EXISTS_TAC [`\j. sum ks (\m. lnorm ((B:A->real^2->bool) m) (&2)
                                         ((f:num->real^2->real^K) j) pow 2)`; `&1`] THEN
  REWRITE_TAC[REAL_MUL_LID] THEN CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN CONJ_TAC THENL
     [MATCH_MP_TAC LNORM_POS_LE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CMC_LNORM_COVER_GEN THEN ASM_SIMP_TAC[]];
    SUBGOAL_THEN `&0 = sum ks (\m:A. &0)` SUBST1_TAC THENL
     [REWRITE_TAC[SUM_0]; ALL_TAC] THEN
    MP_TAC(ISPECL [`sequentially`;
                   `\m j. lnorm ((B:A->real^2->bool) m) (&2)
                                ((f:num->real^2->real^K) j) pow 2`;
                   `\m:A. &0`; `ks:A->bool`] REALLIM_SUM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    X_GEN_TAC `m:A` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`sequentially`;
                   `\j. lnorm ((B:A->real^2->bool) m) (&2) ((f:num->real^2->real^K) j)`;
                   `2`] REALLIM_NULL_POW) THEN
    ASM_SIMP_TAC[ARITH_EQ]]);;


let CMC_DERIVS_ADD_CONST = prove
 (`!s (f:real^2->real^K) (k0:real^K) z.
     open s /\ smooth_map_on s f /\ z IN s
     ==> (!i. partial_derivative i (\x. f x + k0) z = partial_derivative i f z) /\
         hmr_vlap (\x. f x + k0) z = hmr_vlap f z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!i x. x IN s ==> partial_derivative i (\x. (f:real^2->real^K) x + k0) x =
                                  partial_derivative i f x` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(f:real^2->real^K) differentiable at x` ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`i:num`; `f:real^2->real^K`; `\x:real^2. (k0:real^K)`; `x:real^2`]
                  PARTIAL_DERIVATIVE_ADD) THEN
    ASM_REWRITE_TAC[DIFFERENTIABLE_CONST; PARTIAL_DERIVATIVE_CONST; VECTOR_ADD_RID];
    ASM_SIMP_TAC[]] THEN
  REWRITE_TAC[hmr_vlap] THEN MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `i:num` THEN
  DISCH_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN
  EXISTS_TAC `s:real^2->bool` THEN ASM_SIMP_TAC[]);;

let CMC_L2_ADD_CONST_NULL = prove
 (`!E (f:num->real^2->real^K) g (v:num->real^K) v0.
     measurable E /\
     (!j. (\x. f j x - g x) IN lspace E (&2)) /\
     ((\j. lnorm E (&2) (\x. f j x - g x)) ---> &0) sequentially /\
     (v --> v0) sequentially
     ==> (!j. (\x. (f j x + v j) - (g x + v0)) IN lspace E (&2)) /\
         ((\j. lnorm E (&2) (\x. (f j x + v j) - (g x + v0))) ---> &0) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CMC_L2_SUM_NULL THEN
  MAP_EVERY EXISTS_TAC [`\j x. (f:num->real^2->real^K) j x - g x`;
                        `\j x:real^2. (v:num->real^K) j - v0`] THEN
  ASM_REWRITE_TAC[ETA_AX] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN MP_TAC(ISPECL [`E:real^2->bool`; `(v:num->real^K) j - v0`] CMC_LNORM_CONST) THEN
    ASM_SIMP_TAC[];
    SUBGOAL_THEN `!j. lnorm E (&2) (\x:real^2. (v:num->real^K) j - v0) =
                      norm(v j - v0) * sqrt(measure(E:real^2->bool))`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN MP_TAC(ISPECL [`E:real^2->bool`; `(v:num->real^K) j - v0`]
                                 CMC_LNORM_CONST) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 = &0 * sqrt(measure(E:real^2->bool))` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REALLIM_RMUL THEN
    MP_TAC(ISPECL [`sequentially`; `\j. (v:num->real^K) j - v0`] LIM_NULL_NORM) THEN
    REWRITE_TAC[GSYM LIM_NULL] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[TENDSTO_REAL; o_DEF; LIFT_NUM];
    REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC]);;

let CMC_B31_BASES = prove
 (`!S (G:real^K->real^K^K) C R c0 (w:num->real^2->real^K) y rho (c:num->real) P a0 a
    (q:num->num) U p kap U0 p0 kap0.
     (!j. &0 < c j) /\ (c ---> c0) sequentially /\ (!m n. m < n ==> q m < q n) /\
     cmc_b31loc S G C R c0 w y rho c P a0 a q U p kap /\
     cmc_b31loc S G C R c0 w y rho c P a0 a0 q U0 p0 kap0
     ==> kap0 = vec 0 /\ p = p0 + c0 % kap`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmc_b31loc] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
    EXISTS_TAC `\j. inv((c:num->real) ((q:num->num) j)) %
                    ((P:num->real^2->real^K) (q j) a0 - P (q j) a0)` THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; VECTOR_SUB_REFL; VECTOR_MUL_RZERO; LIM_CONST];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\j. (c:num->real) ((q:num->num) j)) ---> c0) sequentially` ASSUME_TAC THENL
   [MATCH_MP_TAC HMD_REALLIM_SUBSEQ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `c0 % (kap:real^K) = p - p0` MP_TAC THENL
   [MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
    EXISTS_TAC `\j. (P:num->real^2->real^K) ((q:num->num) j) a - P (q j) a0` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LIM_TRANSFORM THEN
      EXISTS_TAC `\j. (c:num->real) ((q:num->num) j) %
                      (inv(c (q j)) % ((P:num->real^2->real^K) (q j) a - P (q j) a0))` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
        ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID; VECTOR_SUB_REFL; LIM_CONST];
        MATCH_MP_TAC CMC_LIM_CMUL_SEQ THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC LIM_SUB THEN ASM_REWRITE_TAC[]];
    VECTOR_ARITH_TAC]);;

let CMC_B31_OVERLAP = prove
 (`!S (G:real^K->real^K^K) C R c0 (w:num->real^2->real^K) (y:num->real^2) (rho:num->real)
    (c:num->real) (P:num->real^2->real^K) a0 a b (q:num->num) Ua pa ka Ub pb kb.
     &0 < R /\
     cmc_b31loc S G C R c0 w y rho c P a0 a q Ua pa ka /\
     cmc_b31loc S G C R c0 w y rho c P a0 b q Ub pb kb
     ==> !x. x IN ball(a,R / &32) /\ x IN ball(b,R / &32) ==> Ua x + ka = Ub x + kb`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmc_b31loc] THEN STRIP_TAC THEN
  ABBREV_TAC `O = ball(a:real^2,R / &32) INTER ball(b,R / &32)` THEN
  SUBGOAL_THEN `open(O:real^2->bool) /\ measurable O /\ lebesgue_measurable O /\
                O SUBSET ball(a,R / &32) /\ O SUBSET ball(b,R / &32)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN SIMP_TAC[OPEN_INTER; OPEN_BALL; INTER_SUBSET] THEN
    SIMP_TAC[MEASURABLE_INTER; MEASURABLE_BALL; LEBESGUE_MEASURABLE_INTER;
             LEBESGUE_MEASURABLE_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!(U:real^2->real^K) (p:real^K) (kap:real^K) e.
      (!j. (\z. inv(c ((q:num->num) j)) %
                ((w:num->real^2->real^K) (q j) ((y:num->real^2) (q j) + (rho:num->real) (q j) % z) -
                 (P:num->real^2->real^K) (q j) e) - U z) IN lspace (ball(e,R / &32)) (&2)) /\
      ((\j. lnorm (ball(e,R / &32)) (&2)
              (\z. inv(c (q j)) % (w (q j) (y (q j) + rho (q j) % z) - P (q j) e) - U z))
       ---> &0) sequentially /\
      ((\j. inv(c (q j)) % (P (q j) e - P (q j) a0)) --> kap) sequentially /\
      O SUBSET ball(e,R / &32)
      ==> (!j. (\z. inv(c (q j)) % (w (q j) (y (q j) + rho (q j) % z) - P (q j) a0) -
                    (U z + kap)) IN lspace O (&2)) /\
          ((\j. lnorm O (&2) (\z. inv(c (q j)) % (w (q j) (y (q j) + rho (q j) % z) - P (q j) a0) -
                                  (U z + kap))) ---> &0) sequentially`
  (LABEL_TAC "GEN") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`ball(e:real^2,R / &32)`; `O:real^2->bool`;
                   `\j z. inv((c:num->real) ((q:num->num) j)) %
                          ((w:num->real^2->real^K) (q j) ((y:num->real^2) (q j) +
                           (rho:num->real) (q j) % z) - (P:num->real^2->real^K) (q j) e) -
                          (U:real^2->real^K) z`] CMC_L2_RESTRICT_NULL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`O:real^2->bool`;
                   `\j z. inv((c:num->real) ((q:num->num) j)) %
                          ((w:num->real^2->real^K) (q j) ((y:num->real^2) (q j) +
                           (rho:num->real) (q j) % z) - (P:num->real^2->real^K) (q j) e)`;
                   `U:real^2->real^K`;
                   `\j. inv((c:num->real) ((q:num->num) j)) %
                        ((P:num->real^2->real^K) (q j) e - P (q j) a0)`;
                   `kap:real^K`] CMC_L2_ADD_CONST_NULL) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VECTOR_ARITH
     `(i % ((wz:real^K) - pe) + i % (pe - pa)) - (u + k) = i % (wz - pa) - (u + k)`];
    ALL_TAC] THEN
  REMOVE_THEN "GEN" (fun th ->
    MP_TAC(SPECL [`Ua:real^2->real^K`; `pa:real^K`; `ka:real^K`; `a:real^2`] th) THEN
    MP_TAC(SPECL [`Ub:real^2->real^K`; `pb:real^K`; `kb:real^K`; `b:real^2`] th)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  MP_TAC(ISPECL [`O:real^2->bool`;
                 `\j z. inv((c:num->real) ((q:num->num) j)) %
                        ((w:num->real^2->real^K) (q j) ((y:num->real^2) (q j) +
                         (rho:num->real) (q j) % z) - (P:num->real^2->real^K) (q j) a0)`;
                 `\z. (Ua:real^2->real^K) z + ka`; `\z. (Ub:real^2->real^K) z + kb`]
                CMC_L2_VALUE_UNIQUE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`O:real^2->bool`; `\z. (Ua:real^2->real^K) z + ka`;
                 `\z. (Ub:real^2->real^K) z + kb`] HMD_CONT_AE_EQ) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THENL
     [EXISTS_TAC `ball(a:real^2,R / &32)`; EXISTS_TAC `ball(b:real^2,R / &32)`] THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; ETA_AX];
    DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN EXPAND_TAC "O" THEN
    ASM_REWRITE_TAC[IN_INTER]]);;

let CMC_B31_GLUE = prove
 (`!S (G:real^K->real^K^K) d (C:num->real) R c0 (w:num->real^2->real^K) (y:num->real^2)
    (rho:num->real) (c:num->real) (P:num->real^2->real^K) a0 (k:real^2->bool) (q:num->num)
    (UU:real^2->real^2->real^K) pp kk.
     cm_target S G d /\ &0 < R /\ (!j. &0 < c j) /\ (c ---> c0) sequentially /\
     (!m n. m < n ==> q m < q n) /\ a0 IN k /\
     (!a. a IN k ==> cmc_b31loc S G C R c0 w y rho c P a0 a q (UU a) (pp a) (kk a))
     ==> ?U. smooth_map_on (UNIONS (IMAGE (\a. ball(a,R / &32)) k)) U /\
             (!x. x IN UNIONS (IMAGE (\a. ball(a,R / &32)) k)
                  ==> pp a0 + c0 % U x IN S /\
                      (!i. 1 <= i /\ i <= 2
                           ==> hmr_tp S (pp a0 + c0 % U x) ** partial_derivative i U x =
                               partial_derivative i U x) /\
                      hmr_tp S (pp a0 + c0 % U x) **
                        (hmr_vlap U x +
                         c0 % vsum(1..2) (\i. christoffel G (pp a0 + c0 % U x)
                                                (partial_derivative i U x)
                                                (partial_derivative i U x))) = vec 0 /\
                      hmr_vlap U x =
                        c0 % vsum(1..2) (\i. hmr_bq S G (pp a0 + c0 % U x)
                                                (partial_derivative i U x)
                                                (partial_derivative i U x))) /\
             (!a i x. a IN k /\ x IN ball(a,R / &32)
                      ==> partial_derivative i U x = partial_derivative i (UU a) x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!a. a IN k ==> (pp:real^2->real^K) a - pp a0 = c0 % kk a` ASSUME_TAC THENL
   [X_GEN_TAC `a:real^2` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `C:num->real`; `R:real`; `c0:real`;
                   `w:num->real^2->real^K`; `y:num->real^2`; `rho:num->real`; `c:num->real`;
                   `P:num->real^2->real^K`; `a0:real^2`; `a:real^2`; `q:num->num`;
                   `(UU:real^2->real^2->real^K) a`; `(pp:real^2->real^K) a`;
                   `(kk:real^2->real^K) a`; `(UU:real^2->real^2->real^K) a0`;
                   `(pp:real^2->real^K) a0`; `(kk:real^2->real^K) a0`] CMC_B31_BASES) THEN
    ASM_SIMP_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^2->bool`; `\a:real^2. ball(a,R / &32)`;
                 `\a z. (UU:real^2->real^2->real^K) a z + (kk:real^2->real^K) a`]
                CMC_GLUE_LOCAL) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `a:real^2` THEN DISCH_TAC THEN REWRITE_TAC[OPEN_BALL] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN REWRITE_TAC[OPEN_BALL; SMOOTH_MAP_ON_CONST] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `a:real^2` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `cmc_b31loc:(real^K->bool)->(real^K->real^K^K)->(num->real)->real->real->(num->real^2->real^K)->(num->real^2)->(num->real)->(num->real)->(num->real^2->real^K)->real^2->real^2->(num->num)->(real^2->real^K)->real^K->real^K->bool`)) (concl th))) THEN
      ASM_SIMP_TAC[cmc_b31loc; ETA_AX];
      MAP_EVERY X_GEN_TAC [`a:real^2`; `b:real^2`; `x:real^2`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `C:num->real`; `R:real`;
                     `c0:real`; `w:num->real^2->real^K`; `y:num->real^2`; `rho:num->real`;
                     `c:num->real`; `P:num->real^2->real^K`; `a0:real^2`; `a:real^2`;
                     `b:real^2`; `q:num->num`;
                     `(UU:real^2->real^2->real^K) a`; `(pp:real^2->real^K) a`;
                     `(kk:real^2->real^K) a`; `(UU:real^2->real^2->real^K) b`;
                     `(pp:real^2->real^K) b`; `(kk:real^2->real^K) b`] CMC_B31_OVERLAP) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:real^2->real^K` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `U:real^2->real^K` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!a x. a IN k /\ x IN ball(a,R / &32)
          ==> (U:real^2->real^K) x = UU a x + kk a /\
              (!i. partial_derivative i U x = partial_derivative i ((UU:real^2->real^2->real^K) a) x) /\
              hmr_vlap U x = hmr_vlap (UU a) x`
  (LABEL_TAC "LOC") THENL
   [MAP_EVERY X_GEN_TAC [`a:real^2`; `x:real^2`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `smooth_map_on (ball(a,R / &32)) ((UU:real^2->real^2->real^K) a)`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `a:real^2` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `cmc_b31loc:(real^K->bool)->(real^K->real^K^K)->(num->real)->real->real->(num->real^2->real^K)->(num->real^2)->(num->real)->(num->real)->(num->real^2->real^K)->real^2->real^2->(num->num)->(real^2->real^K)->real^K->real^K->bool`)) (concl th))) THEN
      ASM_SIMP_TAC[cmc_b31loc];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`ball(a:real^2,R / &32)`; `U:real^2->real^K`;
                   `\z. (UU:real^2->real^2->real^K) a z + (kk:real^2->real^K) a`; `x:real^2`]
                  CMC_LOCAL_EQ_DERIVS) THEN
    ASM_SIMP_TAC[OPEN_BALL] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`ball(a:real^2,R / &32)`; `(UU:real^2->real^2->real^K) a`;
                   `(kk:real^2->real^K) a`; `x:real^2`] CMC_DERIVS_ADD_CONST) THEN
    ASM_SIMP_TAC[OPEN_BALL];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^2` STRIP_ASSUME_TAC) THEN
    USE_THEN "LOC" (MP_TAC o SPECL [`a:real^2`; `x:real^2`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC (CONJUNCTS_THEN2 (fun th -> REWRITE_TAC[th])
      SUBST1_TAC)) THEN
    SUBGOAL_THEN `(pp:real^2->real^K) a0 + c0 % ((UU:real^2->real^2->real^K) a x + kk a) =
                  pp a + c0 % UU a x` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `a:real^2` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `pp:real^2->real^K`)) (concl th) &&
        not(can (find_term ((=) `UU:real^2->real^2->real^K`)) (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:real^2` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `cmc_b31loc:(real^K->bool)->(real^K->real^K^K)->(num->real)->real->real->(num->real^2->real^K)->(num->real^2)->(num->real)->(num->real)->(num->real^2->real^K)->real^2->real^2->(num->num)->(real^2->real^K)->real^K->real^K->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[cmc_b31loc] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN USE_THEN "LOC" (MP_TAC o SPECL [`a:real^2`; `x:real^2`]) THEN
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* CM Lemma B.31, step 4: the normalized angular and Euclidean energies      *)
(* converge to those of the glued limit.                                     *)
(* ------------------------------------------------------------------------- *)

let CMC_ANGD_L2_NULL = prove
 (`!E (y:real^2) (g1:num->real^2->real^K) g2 h1 h2.
     open E /\ ~(y IN E) /\
     (!j. g1 j IN lspace E (&2)) /\ (!j. g2 j IN lspace E (&2)) /\
     h1 IN lspace E (&2) /\ h2 IN lspace E (&2) /\
     ((\j. lnorm E (&2) (\x. g1 j x - h1 x)) ---> &0) sequentially /\
     ((\j. lnorm E (&2) (\x. g2 j x - h2 x)) ---> &0) sequentially
     ==> ((\j. lnorm E (&2) (\x. cmc_angd y x (g1 j x) (g2 j x) - cmc_angd y x (h1 x) (h2 x)))
          ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\j. lnorm E (&2) (\x. (g1:num->real^2->real^K) j x - h1 x) +
                  lnorm E (&2) (\x. (g2:num->real^2->real^K) j x - h2 x)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MP_TAC(ISPECL [`sequentially`;
                   `\j. lnorm E (&2) (\x. (g1:num->real^2->real^K) j x - h1 x)`;
                   `\j. lnorm E (&2) (\x. (g2:num->real^2->real^K) j x - h2 x)`;
                   `&0`; `&0`] REALLIM_ADD) THEN
    ASM_REWRITE_TAC[REAL_ADD_LID]] THEN
  MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `j:num` THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\x. (g1:num->real^2->real^K) j x - h1 x) IN lspace E (&2) /\
                (\x. (g2:num->real^2->real^K) j x - h2 x) IN lspace E (&2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[CMC_ANGD_FACTS] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ a <= b ==> abs a <= b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC LNORM_POS_LE THEN MATCH_MP_TAC CMC_ANGD_LSPACE THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `lnorm E (&2) (\x. lift(norm((g1:num->real^2->real^K) j x - h1 x)) +
                                lift(norm((g2:num->real^2->real^K) j x - h2 x)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LNORM_MONO THEN EXISTS_TAC `{}:real^2->bool` THEN
    REWRITE_TAC[NEGLIGIBLE_EMPTY; DIFF_EMPTY] THEN REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC CMC_ANGD_LSPACE THEN ASM_REWRITE_TAC[ETA_AX];
      MATCH_MP_TAC LSPACE_ADD THEN ASM_SIMP_TAC[LSPACE_NORM] THEN REAL_ARITH_TAC;
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[GSYM LIFT_ADD; NORM_LIFT] THEN
      MATCH_MP_TAC(REAL_ARITH `a <= b ==> a <= abs b`) THEN REWRITE_TAC[CMC_ANGD_FACTS]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `lnorm E (&2) (\x. lift(norm((g1:num->real^2->real^K) j x - h1 x))) +
              lnorm E (&2) (\x. lift(norm((g2:num->real^2->real^K) j x - h2 x)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LNORM_TRIANGLE THEN ASM_SIMP_TAC[LSPACE_NORM] THEN REAL_ARITH_TAC;
    REWRITE_TAC[LNORM_NORM; REAL_LE_REFL]]);;

let CMC_B31_CONV = prove
 (`!S (w:num->real^2->real^K) (y:num->real^2) (rho:num->real) (c:num->real)
    (U:real^2->real^K) r1 r2.
     (!j. cmc_pmap S (w j) /\ &0 < rho j /\ &0 < c j) /\ &0 < r1 /\
     (!i. 1 <= i /\ i <= 2
          ==> partial_derivative i U IN lspace (cmc_ann (vec 0) r1 r2) (&2) /\
              (!j. (\z. (rho j / c j) % wan_wd (:real^2) i (w j) (y j + rho j % z) -
                        partial_derivative i U z) IN lspace (cmc_ann (vec 0) r1 r2) (&2)) /\
              ((\j. lnorm (cmc_ann (vec 0) r1 r2) (&2)
                      (\z. (rho j / c j) % wan_wd (:real^2) i (w j) (y j + rho j % z) -
                           partial_derivative i U z)) ---> &0) sequentially)
     ==> ((\j. cmc_angE (y j) (cmc_ann (y j) (rho j * r1) (rho j * r2)) (w j) / c j pow 2)
          ---> lnorm (cmc_ann (vec 0) r1 r2) (&2)
                 (\x. cmc_angd (vec 0) x (partial_derivative 1 U x)
                                         (partial_derivative 2 U x)) pow 2) sequentially /\
         ((\j. cmc_eE (cmc_ann (y j) (rho j * r1) (rho j * r2)) (w j) / c j pow 2)
          ---> lnorm (cmc_ann (vec 0) r1 r2) (&2)
                 (\x. pastecart (partial_derivative 1 U x)
                                (partial_derivative 2 U x)) pow 2) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `E = cmc_ann (vec 0:real^2) r1 r2` THEN
  SUBGOAL_THEN `open(E:real^2->bool) /\ ~((vec 0:real^2) IN E)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN REWRITE_TAC[CMC_OPEN_ANN; cmc_ann; IN_ELIM_THM] THEN
    REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!j. ~((y:num->real^2) j IN cmc_ann (y j) ((rho:num->real) j * r1) (rho j * r2)) /\
                    open(cmc_ann (y j) (rho j * r1) (rho j * r2))`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[CMC_OPEN_ANN; cmc_ann; IN_ELIM_THM] THEN
    REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x < &0 /\ &0 < y)`) THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> !j. (\z. ((rho:num->real) j / (c:num->real) j) %
                     wan_wd (:real^2) i ((w:num->real^2->real^K) j) ((y:num->real^2) j + rho j % z))
                IN lspace E (&2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `wan_wd:(real^2->bool)->num->(real^2->real^K)->real^2->real^K`))
        (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(\z. ((rho:num->real) j / (c:num->real) j) %
           wan_wd (:real^2) i ((w:num->real^2->real^K) j) ((y:num->real^2) j + rho j % z)) =
      (\z. ((rho j / c j) % wan_wd (:real^2) i (w j) (y j + rho j % z) -
            partial_derivative i (U:real^2->real^K) z) + partial_derivative i U z)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC LSPACE_ADD THEN ASM_REWRITE_TAC[ETA_AX] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
    EXISTS_TAC `\j. lnorm E (&2)
                      (\z. cmc_angd (vec 0) z
                             (((rho:num->real) j / (c:num->real) j) %
                              wan_wd (:real^2) 1 ((w:num->real^2->real^K) j) ((y:num->real^2) j + rho j % z))
                             ((rho j / c j) % wan_wd (:real^2) 2 (w j) (y j + rho j % z))) pow 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `j:num` THEN REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`S:real^K->bool`; `(w:num->real^2->real^K) j`; `(y:num->real^2) j`;
                     `cmc_ann ((y:num->real^2) j) ((rho:num->real) j * r1) (rho j * r2)`]
                    CMC_ENERGIES_L2) THEN
      ASM_SIMP_TAC[] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`wan_wd (:real^2) 1 ((w:num->real^2->real^K) j)`;
                     `wan_wd (:real^2) 2 ((w:num->real^2->real^K) j)`; `(y:num->real^2) j`;
                     `(rho:num->real) j`; `(c:num->real) j`; `r1:real`; `r2:real`] CMC_CV_ANG) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CMC_LNORM_SQ_CONV THEN REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC CMC_ANGD_LSPACE THEN ASM_SIMP_TAC[ARITH; ETA_AX];
      MATCH_MP_TAC CMC_ANGD_LSPACE THEN ASM_SIMP_TAC[ARITH; ETA_AX];
      MATCH_MP_TAC CMC_ANGD_L2_NULL THEN ASM_SIMP_TAC[ARITH; ETA_AX]];
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\j. lnorm E (&2)
                    (\z. pastecart
                           (((rho:num->real) j / (c:num->real) j) %
                            wan_wd (:real^2) 1 ((w:num->real^2->real^K) j) ((y:num->real^2) j + rho j % z))
                           ((rho j / c j) % wan_wd (:real^2) 2 (w j) (y j + rho j % z))) pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `j:num` THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `(w:num->real^2->real^K) j`; `(y:num->real^2) j`;
                   `cmc_ann ((y:num->real^2) j) ((rho:num->real) j * r1) (rho j * r2)`]
                  CMC_ENERGIES_L2) THEN
    ASM_SIMP_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`wan_wd (:real^2) 1 ((w:num->real^2->real^K) j)`;
                   `wan_wd (:real^2) 2 ((w:num->real^2->real^K) j)`; `(y:num->real^2) j`;
                   `(rho:num->real) j`; `(c:num->real) j`; `r1:real`; `r2:real`] CMC_CV_EE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CMC_LNORM_SQ_CONV THEN REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CMC_LSPACE2_PASTECART THEN ASM_SIMP_TAC[ARITH; ETA_AX];
    MATCH_MP_TAC CMC_LSPACE2_PASTECART THEN ASM_SIMP_TAC[ARITH; ETA_AX];
    REWRITE_TAC[PASTECART_SUB] THEN
    MATCH_MP_TAC CMC_LNORM2_PASTECART_TOZERO THEN ASM_SIMP_TAC[ARITH; ETA_AX]]);;

(* ------------------------------------------------------------------------- *)
(* CM Lemma B.31: the sequence argument and the lemma.                       *)
(* ------------------------------------------------------------------------- *)

let CMC_CS_CONNECTED = prove
 (`!l. connected (cmc_cs l)`,
  GEN_TAC THEN REWRITE_TAC[cmc_cs] THEN
  MP_TAC(ISPECL [`vec 0:real^2`; `exp(--(&2 * l))`; `exp(&2 * l) + cmc_r31 l`]
                (el 2 (CONJUNCTS CONNECTED_ANNULUS))) THEN
  REWRITE_TAC[DIMINDEX_2; VECTOR_SUB_RZERO; LE_REFL]);;

let CMC_A2C_FACTS = prove
 (`!l. &1 <= l
       ==> compact {x:real^2 | exp(--(&2 * l)) <= norm x /\ norm x <= exp(&2 * l)} /\
           exp(--(&2 * l)) % basis 1 IN
             {x:real^2 | exp(--(&2 * l)) <= norm x /\ norm x <= exp(&2 * l)}`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMC_EXP_LADDER) THEN CONJ_TAC THENL
   [SUBGOAL_THEN `{x:real^2 | exp(--(&2 * l)) <= norm x /\ norm x <= exp(&2 * l)} =
                  cball(vec 0,exp(&2 * l)) DIFF ball(vec 0,exp(--(&2 * l)))` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN
      REAL_ARITH_TAC;
      SIMP_TAC[COMPACT_DIFF; COMPACT_CBALL; OPEN_BALL]];
    REWRITE_TAC[IN_ELIM_THM; NORM_MUL] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_2; LE_REFL; ARITH_RULE `1 <= 2`; REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_ABS_EXP; REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC]);;

let CMC_SIM_OPEN = prove
 (`!(y:real^2) rho s. open s /\ &0 < rho ==> open (IMAGE (\z. y + rho % z) s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z:real^2. y + rho % z) = (\x. rho % x + y)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC OPEN_AFFINITY THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ]);;

let CMC_B31_GRADL2 = prove
 (`!S (G:real^K->real^K^K) (C:num->real) R c0 (w:num->real^2->real^K) (y:num->real^2)
    (rho:num->real) (c:num->real) (P:num->real^2->real^K) a0 (k:real^2->bool) (q:num->num)
    (UU:real^2->real^2->real^K) pp kk (U:real^2->real^K) E.
     FINITE k /\ &0 < R /\ (!j. cmc_pmap S (w j) /\ &0 < rho j /\ &0 < c j) /\
     (!a. a IN k ==> cmc_b31loc S G C R c0 w y rho c P a0 a q (UU a) (pp a) (kk a)) /\
     smooth_map_on (UNIONS (IMAGE (\a. ball(a,R / &32)) k)) U /\
     (!a i x. a IN k /\ x IN ball(a,R / &32)
              ==> partial_derivative i U x = partial_derivative i (UU a) x) /\
     open E /\ bounded E /\ E SUBSET UNIONS (IMAGE (\a. ball(a,R / &32)) k)
     ==> !i. 1 <= i /\ i <= 2
             ==> partial_derivative i U IN lspace E (&2) /\
                 (!j. (\z. (rho (q j) / c (q j)) %
                           wan_wd (:real^2) i (w (q j)) (y (q j) + rho (q j) % z) -
                           partial_derivative i U z) IN lspace E (&2)) /\
                 ((\j. lnorm E (&2)
                         (\z. (rho (q j) / c (q j)) %
                              wan_wd (:real^2) i (w (q j)) (y (q j) + rho (q j) % z) -
                              partial_derivative i U z)) ---> &0) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ABBREV_TAC `O = UNIONS (IMAGE (\a:real^2. ball(a,R / &32)) k)` THEN
  SUBGOAL_THEN `measurable(E:real^2->bool) /\ lebesgue_measurable E` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MEASURABLE_OPEN; LEBESGUE_MEASURABLE_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN `open(O:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN MATCH_MP_TAC OPEN_UNIONS THEN
    REWRITE_TAC[FORALL_IN_IMAGE; OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN O ==> norm(partial_derivative i (U:real^2->real^K) x) <= C 1 * &8 / R`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN EXPAND_TAC "O" THEN
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^2` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^2`; `i:num`; `x:real^2`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `UU:real^2->real^2->real^K`)) (concl th) &&
      not(can (find_term ((=) `pp:real^2->real^K`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:real^2` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `pp:real^2->real^K`)) (concl th))) THEN
    ASM_REWRITE_TAC[cmc_b31loc] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `partial_derivative i (U:real^2->real^K) IN lspace E (&2)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`E:real^2->bool`; `partial_derivative i (U:real^2->real^K)`;
                   `(C:num->real) 1 * &8 / R`] CMC_BOUNDED_LNORM) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `O:real^2->bool` THEN ASM_SIMP_TAC[CMC_PD_CONTINUOUS];
      ASM SET_TAC[]];
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `!j. (\z. ((rho:num->real) ((q:num->num) j) / (c:num->real) (q j)) %
            wan_wd (:real^2) i ((w:num->real^2->real^K) (q j)) ((y:num->real^2) (q j) + rho (q j) % z))
        IN lspace E (&2)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC LSPACE_CMUL THEN
    MP_TAC(ISPECL [`wan_wd (:real^2) i ((w:num->real^2->real^K) ((q:num->num) j))`;
                   `(y:num->real^2) ((q:num->num) j)`; `(rho:num->real) ((q:num->num) j)`;
                   `E:real^2->bool`] CMC_SIM_LSPACE) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`S:real^K->bool`; `(w:num->real^2->real^K) ((q:num->num) j)`; `i:num`]
                    CMC_PMAP_WD) THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC LEBESGUE_MEASURABLE_OPEN THEN MATCH_MP_TAC CMC_SIM_OPEN THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. (\z. ((rho:num->real) ((q:num->num) j) / (c:num->real) (q j)) %
            wan_wd (:real^2) i ((w:num->real^2->real^K) (q j)) ((y:num->real^2) (q j) + rho (q j) % z) -
            partial_derivative i (U:real^2->real^K) z) IN lspace E (&2)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`E:real^2->bool`; `\a:real^2. ball(a,R / &32)`; `k:real^2->bool`;
                 `\j z. ((rho:num->real) ((q:num->num) j) / (c:num->real) (q j)) %
                        wan_wd (:real^2) i ((w:num->real^2->real^K) (q j))
                          ((y:num->real^2) (q j) + rho (q j) % z) -
                        partial_derivative i (U:real^2->real^K) z`] CMC_NULL_COVER_GEN) THEN
  REWRITE_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `a:real^2` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:real^2` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `pp:real^2->real^K`)) (concl th))) THEN
  ASM_REWRITE_TAC[cmc_b31loc] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `wan_wd:(real^2->bool)->num->(real^2->real^K)->real^2->real^K`))
      (concl th) && can (find_term ((=) `(--->):(num->real)->real->(num)net->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!j. (\z. ((rho:num->real) ((q:num->num) j) / (c:num->real) (q j)) %
            wan_wd (:real^2) i ((w:num->real^2->real^K) (q j)) ((y:num->real^2) (q j) + rho (q j) % z) -
            partial_derivative i (U:real^2->real^K) z) IN lspace (ball(a,R / &32)) (&2) /\
        lnorm (ball(a,R / &32)) (&2)
          (\z. (rho (q j) / c (q j)) %
               wan_wd (:real^2) i (w (q j)) (y (q j) + rho (q j) % z) -
               partial_derivative i U z) =
        lnorm (ball(a,R / &32)) (&2)
          (\z. (rho (q j) / c (q j)) %
               wan_wd (:real^2) i (w (q j)) (y (q j) + rho (q j) % z) -
               partial_derivative i ((UU:real^2->real^2->real^K) a) z)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`ball(a:real^2,R / &32)`; `{}:real^2->bool`;
                   `\z. ((rho:num->real) ((q:num->num) j) / (c:num->real) (q j)) %
                        wan_wd (:real^2) i ((w:num->real^2->real^K) (q j))
                          ((y:num->real^2) (q j) + rho (q j) % z) -
                        partial_derivative i (U:real^2->real^K) z`;
                   `\z. ((rho:num->real) ((q:num->num) j) / (c:num->real) (q j)) %
                        wan_wd (:real^2) i ((w:num->real^2->real^K) (q j))
                          ((y:num->real^2) (q j) + rho (q j) % z) -
                        partial_derivative i ((UU:real^2->real^2->real^K) a) z`;
                   `&2`] WAN_LSPACE_LNORM_SPIKE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[NEGLIGIBLE_EMPTY; DIFF_EMPTY] THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[] THEN AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      STRIP_TAC THEN ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[]]);;

let CMC_B31_CYLAPPLY = prove
 (`!S (G:real^K->real^K^K) l g delta' (O:real^2->bool) (U:real^2->real^K) (p:real^K) c0 B.
     cmc_cylp S G l g delta' /\ &1 <= l /\ open O /\ &0 <= c0 /\ &0 <= B /\
     c0 * (exp(&2 * l) * B) <= g /\
     {x:real^2 | exp(--(&2 * l)) <= norm x /\ norm x <= exp(&2 * l)} SUBSET O /\
     smooth_map_on O U /\
     (!x. x IN O
          ==> p + c0 % U x IN S /\
              (!i. 1 <= i /\ i <= 2
                   ==> hmr_tp S (p + c0 % U x) ** partial_derivative i U x =
                       partial_derivative i U x) /\
              hmr_tp S (p + c0 % U x) **
                (hmr_vlap U x +
                 c0 % vsum(1..2) (\i. christoffel G (p + c0 % U x)
                                        (partial_derivative i U x)
                                        (partial_derivative i U x))) = vec 0 /\
              hmr_vlap U x =
                c0 % vsum(1..2) (\i. hmr_bq S G (p + c0 % U x)
                                        (partial_derivative i U x)
                                        (partial_derivative i U x))) /\
     (!i x. 1 <= i /\ i <= 2 /\ x IN O ==> norm(partial_derivative i U x) <= B) /\
     (!i. 1 <= i /\ i <= 2
          ==> partial_derivative i U IN lspace (cmc_ann (vec 0) (exp(--l)) (exp l)) (&2) /\
              partial_derivative i U IN
                lspace (cmc_ann (vec 0) (exp(--(&2 * l))) (exp(&2 * l))) (&2))
     ==> lnorm (cmc_ann (vec 0) (exp(--l)) (exp l)) (&2)
           (\x. cmc_angd (vec 0) x (partial_derivative 1 U x) (partial_derivative 2 U x)) pow 2
         <= delta' *
            lnorm (cmc_ann (vec 0) (exp(--(&2 * l))) (exp(&2 * l))) (&2)
              (\x. pastecart (partial_derivative 1 U x) (partial_derivative 2 U x)) pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMC_EXP_LADDER) THEN
  SUBGOAL_THEN
   `(\x. cmc_angd (vec 0) x (partial_derivative 1 (U:real^2->real^K) x)
                            (partial_derivative 2 U x))
      IN lspace (cmc_ann (vec 0) (exp(--l)) (exp l)) (&2) /\
    (\x. pastecart (partial_derivative 1 (U:real^2->real^K) x) (partial_derivative 2 U x))
      IN lspace (cmc_ann (vec 0) (exp(--(&2 * l))) (exp(&2 * l))) (&2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CMC_ANGD_LSPACE THEN REWRITE_TAC[CMC_OPEN_ANN; ETA_AX] THEN
      ASM_SIMP_TAC[ARITH] THEN
      REWRITE_TAC[cmc_ann; IN_ELIM_THM; VECTOR_SUB_REFL; NORM_0] THEN
      MP_TAC(SPEC `--l` REAL_EXP_POS_LT) THEN REAL_ARITH_TAC;
      MATCH_MP_TAC CMC_LSPACE2_PASTECART THEN ASM_SIMP_TAC[ARITH; ETA_AX]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[WAN_SOB_LNORM2_SQ; CMW_NORM_PASTECART_POW2] THEN
  UNDISCH_TAC `cmc_cylp S (G:real^K->real^K^K) l g delta'` THEN REWRITE_TAC[cmc_cylp] THEN
  DISCH_THEN(MP_TAC o SPECL [`O:real^2->bool`; `U:real^2->real^K`; `p:real^K`; `c0:real`;
                             `vec 0:real^2`; `&1`; `exp(&2 * l) * B`]) THEN
  REWRITE_TAC[REAL_MUL_LID; VECTOR_SUB_RZERO; REAL_LT_01] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN O` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN ASM_REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[NORM_POS_LE; ARITH]]);;

let CMC_B31_CORE = prove
 (`!S (G:real^K->real^K^K) d (C:num->real) l g delta' (w:num->real^2->real^K)
    (y:num->real^2) (rho:num->real) (c:num->real) c0 (mu:num->real)
    (P:num->real^2->real^K) (V:num->real^2->real^2->real^K).
     cm_target S G d /\ (!k. &0 < C k) /\ &1 <= l /\ cmc_cylp S G l g delta' /\
     &0 <= c0 /\ c0 * (exp(&2 * l) * C 1 * &8 / cmc_r31 l) <= g /\
     (!j. cmc_pmap S (w j) /\ &0 < rho j /\ &0 < c j) /\ (c ---> c0) sequentially /\
     (mu ---> &0) sequentially /\ (!j. &0 <= mu j /\ mu j <= &1) /\
     (!j a. a IN cmc_cs l
            ==> cmc_b31dat S G C (cmc_r31 l) (w j) (y j) (rho j) (c j) (mu j) (P j a) (V j a) a)
     ==> ?(q:num->num). (!m n. m < n ==> q m < q n) /\
           ?alpha beta.
             ((\j. cmc_angE (y (q j)) (cmc_ann (y (q j)) (rho (q j) * exp(--l)) (rho (q j) * exp l))
                     (w (q j)) / c (q j) pow 2) ---> alpha) sequentially /\
             ((\j. cmc_eE (cmc_ann (y (q j)) (rho (q j) * exp(--(&2 * l))) (rho (q j) * exp(&2 * l)))
                     (w (q j)) / c (q j) pow 2) ---> beta) sequentially /\
             alpha <= delta' * beta`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `l:real` CMC_R31_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `l:real` CMC_EXP_LADDER) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `l:real` CMC_A2C_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `R = cmc_r31 l` THEN
  ABBREV_TAC `A2 = {x:real^2 | exp(--(&2 * l)) <= norm x /\ norm x <= exp(&2 * l)}` THEN
  ABBREV_TAC `a0:real^2 = exp(--(&2 * l)) % basis 1` THEN
  SUBGOAL_THEN `(A2:real^2->bool) SUBSET cmc_cs l` ASSUME_TAC THENL
   [EXPAND_TAC "A2" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  (* offsets *)
  SUBGOAL_THEN `!a. a IN cmc_cs l
                    ==> ?M. !j. norm((P:num->real^2->real^K) j a - P j a0) <= M * c j`
  (LABEL_TAC "OFF") THENL
   [X_GEN_TAC `a:real^2` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`w:num->real^2->real^K`; `y:num->real^2`; `rho:num->real`; `c:num->real`;
                   `P:num->real^2->real^K`; `V:num->real^2->real^2->real^K`; `cmc_cs l`;
                   `R:real`; `&4 * (R / &8) pow 2`; `(C:num->real) 1`] CMC_OFFSET_BOUNDED) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[CMC_CS_CONNECTED] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; REAL_LE_POW_2]; ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`j:num`; `b:real^2`] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `b:real^2`] o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `cmc_b31dat:(real^K->bool)->(real^K->real^K^K)->(num->real)->real->(real^2->real^K)->real^2->real->real->real->real^K->(real^2->real^K)->real^2->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[cmc_b31dat] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&4 * (R / &8) pow 2 * (mu:num->real) j` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(b:real^2,R / &8)` THEN
        ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN MATCH_MP_TAC SUBSET_BALL THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`a0:real^2`; `a:real^2`]) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(A2:real^2->bool) SUBSET cmc_cs l` THEN
    UNDISCH_TAC `(a0:real^2) IN A2` THEN SET_TAC[];
    ALL_TAC] THEN
  (* the finite cover *)
  MP_TAC(ISPEC `A2:real^2->bool` COMPACT_IMP_TOTALLY_BOUNDED) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `R / &32`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:real^2->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `k = (a0:real^2) INSERT k0` THEN
  SUBGOAL_THEN `FINITE(k:real^2->bool) /\ (a0:real^2) IN k /\ k SUBSET cmc_cs l /\
                (A2:real^2->bool) SUBSET UNIONS (IMAGE (\a. ball(a,R / &32)) k)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN REWRITE_TAC[FINITE_INSERT; IN_INSERT] THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `(A2:real^2->bool) SUBSET cmc_cs l` THEN
      UNDISCH_TAC `(a0:real^2) IN A2` THEN UNDISCH_TAC `(k0:real^2->bool) SUBSET A2` THEN
      SET_TAC[];
      UNDISCH_TAC `(A2:real^2->bool) SUBSET UNIONS (IMAGE (\x. ball(x,R / &32)) k0)` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  (* local limits along a common subsequence *)
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `C:num->real`; `R:real`;
                 `c0:real`; `w:num->real^2->real^K`; `y:num->real^2`; `rho:num->real`;
                 `c:num->real`; `mu:num->real`; `P:num->real^2->real^K`;
                 `V:num->real^2->real^2->real^K`; `a0:real^2`; `k:real^2->bool`]
                CMC_B31_FINEXT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN REPEAT STRIP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `cmc_b31dat:(real^K->bool)->(real^K->real^K^K)->(num->real)->real->(real^2->real^K)->real^2->real->real->real->real^K->(real^2->real^K)->real^2->bool`)) (concl th))) THEN
      UNDISCH_TAC `(k:real^2->bool) SUBSET cmc_cs l` THEN
      UNDISCH_TAC `(a:real^2) IN k` THEN SET_TAC[];
      USE_THEN "OFF" MATCH_MP_TAC THEN
      UNDISCH_TAC `(k:real^2->bool) SUBSET cmc_cs l` THEN
      UNDISCH_TAC `(a:real^2) IN k` THEN SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num->num` (X_CHOOSE_THEN `UU:real^2->real^2->real^K`
    (X_CHOOSE_THEN `pp:real^2->real^K` (X_CHOOSE_THEN `kk:real^2->real^K`
      STRIP_ASSUME_TAC)))) THEN
  (* gluing *)
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `C:num->real`; `R:real`;
                 `c0:real`; `w:num->real^2->real^K`; `y:num->real^2`; `rho:num->real`;
                 `c:num->real`; `P:num->real^2->real^K`; `a0:real^2`; `k:real^2->bool`;
                 `q:num->num`; `UU:real^2->real^2->real^K`; `pp:real^2->real^K`;
                 `kk:real^2->real^K`] CMC_B31_GLUE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:real^2->real^K` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `O = UNIONS (IMAGE (\a:real^2. ball(a,R / &32)) k)` THEN
  SUBGOAL_THEN `open(O:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN MATCH_MP_TAC OPEN_UNIONS THEN REWRITE_TAC[FORALL_IN_IMAGE; OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i x. 1 <= i /\ i <= 2 /\ x IN O
                      ==> norm(partial_derivative i (U:real^2->real^K) x) <= C 1 * &8 / R`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `x:real^2`] THEN EXPAND_TAC "O" THEN
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `a:real^2` STRIP_ASSUME_TAC))) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^2`; `i:num`; `x:real^2`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `UU:real^2->real^2->real^K`)) (concl th) &&
      not(can (find_term ((=) `pp:real^2->real^K`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:real^2` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `cmc_b31loc:(real^K->bool)->(real^K->real^K^K)->(num->real)->real->real->(num->real^2->real^K)->(num->real^2)->(num->real)->(num->real)->(num->real^2->real^K)->real^2->real^2->(num->num)->(real^2->real^K)->real^K->real^K->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[cmc_b31loc] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the two annuli and the L^2 convergence of the gradients *)
  SUBGOAL_THEN
   `!r. &0 < r /\ r <= &2 * l
        ==> open(cmc_ann (vec 0:real^2) (exp(--r)) (exp r)) /\
            bounded(cmc_ann (vec 0:real^2) (exp(--r)) (exp r)) /\
            cmc_ann (vec 0:real^2) (exp(--r)) (exp r) SUBSET O`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN REWRITE_TAC[CMC_OPEN_ANN] THEN CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `cball(vec 0:real^2,exp r)` THEN
      REWRITE_TAC[BOUNDED_CBALL; SUBSET; cmc_ann; IN_ELIM_THM; IN_CBALL_0; VECTOR_SUB_RZERO] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `A2:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "A2" THEN REWRITE_TAC[SUBSET; cmc_ann; IN_ELIM_THM; VECTOR_SUB_RZERO] THEN
    X_GEN_TAC `x:real^2` THEN
    SUBGOAL_THEN `exp(--(&2 * l)) <= exp(--r) /\ exp r <= exp(&2 * l)` MP_TAC THENL
     [REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. &0 < r /\ r <= &2 * l
        ==> !i. 1 <= i /\ i <= 2
                ==> partial_derivative i (U:real^2->real^K)
                      IN lspace (cmc_ann (vec 0) (exp(--r)) (exp r)) (&2) /\
                    (!j. (\z. ((rho:num->real) ((q:num->num) j) / (c:num->real) (q j)) %
                              wan_wd (:real^2) i ((w:num->real^2->real^K) (q j))
                                ((y:num->real^2) (q j) + rho (q j) % z) -
                              partial_derivative i U z)
                         IN lspace (cmc_ann (vec 0) (exp(--r)) (exp r)) (&2)) /\
                    ((\j. lnorm (cmc_ann (vec 0) (exp(--r)) (exp r)) (&2)
                            (\z. (rho (q j) / c (q j)) %
                                 wan_wd (:real^2) i (w (q j)) (y (q j) + rho (q j) % z) -
                                 partial_derivative i U z)) ---> &0) sequentially`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC CMC_B31_GRADL2 THEN
    MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `C:num->real`; `R:real`;
                          `c0:real`; `P:num->real^2->real^K`; `a0:real^2`; `k:real^2->bool`;
                          `UU:real^2->real^2->real^K`; `pp:real^2->real^K`;
                          `kk:real^2->real^K`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the limits of the normalized energies *)
  MP_TAC(ISPECL [`S:real^K->bool`; `\j. (w:num->real^2->real^K) ((q:num->num) j)`;
                 `\j. (y:num->real^2) ((q:num->num) j)`; `\j. (rho:num->real) ((q:num->num) j)`;
                 `\j. (c:num->real) ((q:num->num) j)`; `U:real^2->real^K`;
                 `exp(--l)`; `exp l`] CMC_B31_CONV) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LT] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `wan_wd:(real^2->bool)->num->(real^2->real^K)->real^2->real^K`))
        (concl th) && can (find_term ((=) `r:real`)) (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `\j. (w:num->real^2->real^K) ((q:num->num) j)`;
                 `\j. (y:num->real^2) ((q:num->num) j)`; `\j. (rho:num->real) ((q:num->num) j)`;
                 `\j. (c:num->real) ((q:num->num) j)`; `U:real^2->real^K`;
                 `exp(--(&2 * l))`; `exp(&2 * l)`] CMC_B31_CONV) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LT] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `wan_wd:(real^2->bool)->num->(real^2->real^K)->real^2->real^K`))
        (concl th) && can (find_term ((=) `r:real`)) (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[] THEN STRIP_TAC] THEN
  EXISTS_TAC `q:num->num` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC
   [`lnorm (cmc_ann (vec 0) (exp(--l)) (exp l)) (&2)
       (\x. cmc_angd (vec 0) x (partial_derivative 1 (U:real^2->real^K) x)
                               (partial_derivative 2 U x)) pow 2`;
    `lnorm (cmc_ann (vec 0) (exp(--(&2 * l))) (exp(&2 * l))) (&2)
       (\x. pastecart (partial_derivative 1 (U:real^2->real^K) x)
                      (partial_derivative 2 U x)) pow 2`] THEN
  ASM_REWRITE_TAC[] THEN
  (* the cylinder estimate for the glued limit *)
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> partial_derivative i (U:real^2->real^K)
              IN lspace (cmc_ann (vec 0) (exp(--l)) (exp l)) (&2) /\
            partial_derivative i U
              IN lspace (cmc_ann (vec 0) (exp(--(&2 * l))) (exp(&2 * l))) (&2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `l:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `wan_wd:(real^2->bool)->num->(real^2->real^K)->real^2->real^K`))
          (concl th) && can (find_term ((=) `r:real`)) (concl th)));
      FIRST_X_ASSUM(MP_TAC o SPEC `&2 * l` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `wan_wd:(real^2->bool)->num->(real^2->real^K)->real^2->real^K`))
          (concl th) && can (find_term ((=) `r:real`)) (concl th)))] THEN
    (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CMC_B31_CYLAPPLY THEN
  MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `g:real`; `O:real^2->bool`;
                        `(pp:real^2->real^K) a0`; `c0:real`; `(C:num->real) 1 * &8 / R`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Comparison of the energies; CM Lemma B.31 (angular energy decay on fixed  *)
(* annuli for relatively almost harmonic maps).                              *)
(* ------------------------------------------------------------------------- *)

let CMC_EE_INTEGRABLE = prove
 (`!S (w:real^2->real^K) E.
     cmc_pmap S w /\ lebesgue_measurable E
     ==> (\x. lift(norm(wan_wd (:real^2) 1 w x) pow 2 + norm(wan_wd (:real^2) 2 w x) pow 2))
         integrable_on E`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM CMW_NORM_PASTECART_POW2] THEN
  MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN
  MATCH_MP_TAC CMC_LSPACE2_PASTECART THEN REWRITE_TAC[ETA_AX] THEN CONJ_TAC THEN
  MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
  ASM_REWRITE_TAC[SUBSET_UNIV] THENL
   [MP_TAC(ISPECL [`S:real^K->bool`; `w:real^2->real^K`; `1`] CMC_PMAP_WD);
    MP_TAC(ISPECL [`S:real^K->bool`; `w:real^2->real^K`; `2`] CMC_PMAP_WD)] THEN
  ASM_SIMP_TAC[ARITH]);;

let CMC_EE_PEN = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> ?lam Lam. &0 < lam /\ lam <= Lam /\
                   !(w:real^2->real^K) E.
                      cmc_pmap S w /\ lebesgue_measurable E
                      ==> lam * cmc_eE E w <= cmc_pen G E w /\
                          cmc_pen G E w <= Lam * cmc_eE E w`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC) o
    MATCH_MP HMD_TARGET_ELLIPTIC) THEN
  MAP_EVERY EXISTS_TAC [`lam:real`; `Lam:real`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `w:real^2->real^K`;
                 `E:real^2->bool`] CMC_PEN_INTEGRABLE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `w:real^2->real^K`; `E:real^2->bool`] CMC_EE_INTEGRABLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[cmc_pen; cmc_eE] THEN
  ASM_SIMP_TAC[GSYM DROP_CMUL; GSYM INTEGRAL_CMUL] THEN CONJ_TAC THEN
  MATCH_MP_TAC INTEGRAL_DROP_LE THEN
  ASM_SIMP_TAC[INTEGRABLE_CMUL; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  REWRITE_TAC[DROP_CMUL; LIFT_DROP; CMC_TRACE_GRAM] THEN
  MP_TAC(SPECL [`(w:real^2->real^K) x`; `wan_wd (:real^2) 1 (w:real^2->real^K) x`]
         (ASSUME `!z xi. lam * norm xi pow 2 <= xi dot ((G:real^K->real^K^K) z ** xi) /\
                         xi dot (G z ** xi) <= Lam * norm xi pow 2`)) THEN
  MP_TAC(SPECL [`(w:real^2->real^K) x`; `wan_wd (:real^2) 2 (w:real^2->real^K) x`]
         (ASSUME `!z xi. lam * norm xi pow 2 <= xi dot ((G:real^K->real^K^K) z ** xi) /\
                         xi dot (G z ** xi) <= Lam * norm xi pow 2`)) THEN
  REAL_ARITH_TAC);;

let CMC_EE_MONO = prove
 (`!S (w:real^2->real^K) E E'.
     cmc_pmap S w /\ lebesgue_measurable E /\ lebesgue_measurable E' /\ E SUBSET E'
     ==> cmc_eE E w <= cmc_eE E' w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cmc_eE] THEN MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
  ASM_SIMP_TAC[LIFT_DROP; REAL_LE_ADD; REAL_LE_POW_2] THEN CONJ_TAC THEN
  MATCH_MP_TAC CMC_EE_INTEGRABLE THEN EXISTS_TAC `S:real^K->bool` THEN ASM_REWRITE_TAC[]);;

let CMC_EE_POS = prove
 (`!S (w:real^2->real^K) E.
     cmc_pmap S w /\ lebesgue_measurable E ==> &0 <= cmc_eE E w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cmc_eE] THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
  ASM_SIMP_TAC[LIFT_DROP; REAL_LE_ADD; REAL_LE_POW_2] THEN
  MATCH_MP_TAC CMC_EE_INTEGRABLE THEN EXISTS_TAC `S:real^K->bool` THEN ASM_REWRITE_TAC[]);;

let CMC_ANGE_LE_EE = prove
 (`!S (w:real^2->real^K) (y:real^2) E.
     cmc_pmap S w /\ open E /\ ~(y IN E) ==> cmc_angE y E w <= &2 * cmc_eE E w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `w:real^2->real^K`; `y:real^2`; `E:real^2->bool`]
                CMC_ENERGIES_L2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[cmc_angE; cmc_eE] THEN
  SUBGOAL_THEN `lebesgue_measurable(E:real^2->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `w:real^2->real^K`; `E:real^2->bool`] CMC_EE_INTEGRABLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[GSYM DROP_CMUL; GSYM INTEGRAL_CMUL] THEN
  MATCH_MP_TAC INTEGRAL_DROP_LE THEN
  ASM_SIMP_TAC[INTEGRABLE_CMUL; CMC_EE_INTEGRABLE] THEN CONJ_TAC THENL
   [MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[DROP_CMUL; LIFT_DROP] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(norm(wan_wd (:real^2) 1 (w:real^2->real^K) x) +
               norm(wan_wd (:real^2) 2 w x)) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE; CMC_ANGD_FACTS];
    MATCH_MP_TAC(REAL_ARITH `&0 <= (b - e) pow 2
                             ==> (b + e) pow 2 <= &2 * (b pow 2 + e pow 2)`) THEN
    REWRITE_TAC[REAL_LE_POW_2]]);;

let CMC_NK_FACTS = prove
 (`!(y:real^2) rho t t'.
     &0 < rho /\ &0 <= t /\ t <= t'
     ==> open(cmc_nk y rho t) /\ ~(y IN cmc_nk y rho t) /\
         lebesgue_measurable(cmc_nk y rho t) /\
         cmc_nk y rho t SUBSET cmc_nk y rho t'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[cmc_nk; CMC_OPEN_ANN] THEN
  SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; CMC_OPEN_ANN] THEN CONJ_TAC THENL
   [REWRITE_TAC[cmc_ann; IN_ELIM_THM; VECTOR_SUB_REFL; NORM_0] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x < &0 /\ &0 < y)`) THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT];
    REWRITE_TAC[SUBSET; cmc_ann; IN_ELIM_THM] THEN X_GEN_TAC `x:real^2` THEN
    SUBGOAL_THEN `rho * exp(--t') <= rho * exp(--t) /\ rho * exp t <= rho * exp t'`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC]]);;

let CMC_B31_RATIOS = prove
 (`!S (G:real^K->real^K^K) lam Lam l delta (w:real^2->real^K) (y:real^2) rho.
     &0 < lam /\ lam <= Lam /\ &1 <= l /\ &0 < delta /\
     (!(w:real^2->real^K) E. cmc_pmap S w /\ lebesgue_measurable E
                             ==> lam * cmc_eE E w <= cmc_pen G E w /\
                                 cmc_pen G E w <= Lam * cmc_eE E w) /\
     cmc_pmap S w /\ &0 < rho /\
     ~(cmc_angE y (cmc_nk y rho l) w <= delta * cmc_eE (cmc_nk y rho (&3 * l)) w)
     ==> &0 < cmc_pen G (cmc_nk y rho (&3 * l)) w /\
         delta / Lam <= cmc_angE y (cmc_nk y rho l) w / cmc_pen G (cmc_nk y rho (&3 * l)) w /\
         cmc_eE (cmc_nk y rho (&2 * l)) w / cmc_pen G (cmc_nk y rho (&3 * l)) w <= inv lam`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`y:real^2`; `rho:real`; `l:real`; `&3 * l`] CMC_NK_FACTS) THEN
  MP_TAC(ISPECL [`y:real^2`; `rho:real`; `&2 * l`; `&3 * l`] CMC_NK_FACTS) THEN
  MP_TAC(ISPECL [`y:real^2`; `rho:real`; `&3 * l`; `&3 * l`] CMC_NK_FACTS) THEN
  ASM_SIMP_TAC[REAL_LE_REFL; REAL_ARITH `&1 <= l ==> &0 <= l /\ l <= &3 * l /\
                                         &0 <= &2 * l /\ &2 * l <= &3 * l /\ &0 <= &3 * l`] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN
  ABBREV_TAC `D = cmc_pen G (cmc_nk y rho (&3 * l)) (w:real^2->real^K)` THEN
  ABBREV_TAC `E3 = cmc_eE (cmc_nk y rho (&3 * l)) (w:real^2->real^K)` THEN
  SUBGOAL_THEN `lam * E3 <= D /\ D <= Lam * E3` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["D"; "E3"] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= E3 /\ cmc_eE (cmc_nk y rho l) (w:real^2->real^K) <= E3 /\
                cmc_eE (cmc_nk y rho (&2 * l)) w <= E3 /\
                cmc_angE y (cmc_nk y rho l) w <= &2 * cmc_eE (cmc_nk y rho l) w`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "E3" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CMC_EE_POS THEN EXISTS_TAC `S:real^K->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CMC_EE_MONO THEN EXISTS_TAC `S:real^K->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CMC_EE_MONO THEN EXISTS_TAC `S:real^K->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CMC_ANGE_LE_EE THEN EXISTS_TAC `S:real^K->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < D` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < lam * E3 /\ lam * E3 <= D ==> &0 < D`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(x = &0) ==> &0 < x`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN UNDISCH_TAC `~(cmc_angE y (cmc_nk y rho l) (w:real^2->real^K) <= delta * E3)` THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `&0 < Lam` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `delta / Lam * (Lam * E3)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_DIV THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `delta / Lam * (Lam * E3) = delta * E3` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < Lam` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `E3:real` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `E3 = inv lam * (lam * E3)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]]);;

let CMC_B31 = prove
 (`!S (G:real^K->real^K^K) d eL (C:num->real) delta.
     cm_target S G d /\ cmc_regc S G eL C /\ &0 < delta
     ==> ?l e2 mu. &1 <= l /\ &0 < e2 /\ &0 < mu /\
           !(w:real^2->real^K) y rho.
              cmc_pmap S w /\ &0 < rho /\
              cmc_pen G (cmc_nk y rho (&3 * l)) w <= e2 /\
              cmc_srb S G mu (cmc_nk y rho (&3 * l)) w
              ==> cmc_angE y (cmc_nk y rho l) w <= delta * cmc_eE (cmc_nk y rho (&3 * l)) w`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cmc_regc]) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] CMC_EE_PEN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `&0 < delta * lam / (&2 * Lam)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                 `delta * lam / (&2 * Lam)`] CMC_CYL_P) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real` (X_CHOOSE_THEN `g:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPEC `l:real` CMC_R31_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `M = exp(&2 * l) * C 1 * &8 / cmc_r31 l` THEN
  SUBGOAL_THEN `&0 < M` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < min eL ((g / M) pow 2) /\ min eL ((g / M) pow 2) <= eL /\
                sqrt(min eL ((g / M) pow 2)) * M <= g` MP_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LT THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
      REAL_ARITH_TAC;
      ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sqrt((g / M) pow 2)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_MONO_LE THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC POW_2_SQRT THEN
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC]];
    ABBREV_TAC `e2 = min eL ((g / M) pow 2)` THEN STRIP_TAC] THEN
  MAP_EVERY EXISTS_TAC [`l:real`; `e2:real`] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; NOT_FORALL_THM; NOT_IMP]) THEN
  SUBGOAL_THEN
   `!j. ?(w:real^2->real^K) y rho.
          (cmc_pmap S w /\ &0 < rho /\
           cmc_pen G (cmc_nk y rho (&3 * l)) w <= e2 /\
           cmc_srb S G (inv(&j + &1)) (cmc_nk y rho (&3 * l)) w) /\
          ~(cmc_angE y (cmc_nk y rho l) w <= delta * cmc_eE (cmc_nk y rho (&3 * l)) w)`
  MP_TAC THENL
   [X_GEN_TAC `j:num` THEN FIRST_X_ASSUM(MP_TAC o SPEC `inv(&j + &1)`) THEN
    REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &j + &1`] THEN MESON_TAC[];
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:num->real^2->real^K` (X_CHOOSE_THEN `y:num->real^2`
      (X_CHOOSE_THEN `rho:num->real` (LABEL_TAC "SEQ"))))] THEN
  (* ratios along the sequence *)
  SUBGOAL_THEN
   `!j. &0 < cmc_pen G (cmc_nk ((y:num->real^2) j) ((rho:num->real) j) (&3 * l))
                       ((w:num->real^2->real^K) j) /\
        delta / Lam <= cmc_angE (y j) (cmc_nk (y j) (rho j) l) (w j) /
                       cmc_pen G (cmc_nk (y j) (rho j) (&3 * l)) (w j) /\
        cmc_eE (cmc_nk (y j) (rho j) (&2 * l)) (w j) /
        cmc_pen G (cmc_nk (y j) (rho j) (&3 * l)) (w j) <= inv lam`
  (LABEL_TAC "RAT") THENL
   [GEN_TAC THEN MATCH_MP_TAC CMC_B31_RATIOS THEN
    EXISTS_TAC `S:real^K->bool` THEN
    USE_THEN "SEQ" (MP_TAC o SPEC `j:num`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the normalized replacement data *)
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `eL:real`; `C:num->real`;
                 `l:real`; `w:num->real^2->real^K`; `y:num->real^2`; `rho:num->real`;
                 `\j. inv(&j + &1)`] CMC_B31_PREP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN
    USE_THEN "SEQ" (MP_TAC o SPEC `j:num`) THEN USE_THEN "RAT" (MP_TAC o SPEC `j:num`) THEN
    SIMP_TAC[] THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[REAL_LE_TRANS];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `P:num->real^2->real^K` (X_CHOOSE_THEN
    `V:num->real^2->real^2->real^K` (LABEL_TAC "DAT"))) THEN
  (* a convergent subsequence of the normalizers *)
  MP_TAC(ISPECL [`\j. sqrt(cmc_pen G (cmc_nk ((y:num->real^2) j) ((rho:num->real) j) (&3 * l))
                                     ((w:num->real^2->real^K) j))`; `sqrt e2`]
                CMC_BOUNDED_SUBSEQ) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `j:num` THEN REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN USE_THEN "RAT" (MP_TAC o SPEC `j:num`) THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_MONO_LE THEN USE_THEN "SEQ" (MP_TAC o SPEC `j:num`) THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:num->num` (X_CHOOSE_THEN `c0:real` STRIP_ASSUME_TAC)) THEN
  (* the compactness argument along the subsequence *)
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `C:num->real`; `l:real`;
                 `g:real`; `delta * lam / (&2 * Lam)`;
                 `\j. (w:num->real^2->real^K) ((t0:num->num) j)`;
                 `\j. (y:num->real^2) ((t0:num->num) j)`;
                 `\j. (rho:num->real) ((t0:num->num) j)`;
                 `\j. sqrt(cmc_pen G (cmc_nk ((y:num->real^2) ((t0:num->num) j))
                                       ((rho:num->real) (t0 j)) (&3 * l))
                                    ((w:num->real^2->real^K) (t0 j)))`;
                 `c0:real`; `\j. inv(&((t0:num->num) j) + &1)`;
                 `\j. (P:num->real^2->real^K) ((t0:num->num) j)`;
                 `\j. (V:num->real^2->real^2->real^K) ((t0:num->num) j)`] CMC_B31_CORE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt e2 * M` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      GEN_TAC THEN USE_THEN "SEQ" (MP_TAC o SPEC `(t0:num->num) j`) THEN
      USE_THEN "RAT" (MP_TAC o SPEC `(t0:num->num) j`) THEN SIMP_TAC[SQRT_POS_LT];
      FIRST_ASSUM(MP_TAC o check (fun th -> is_comb(concl th) &&
        can (find_term ((=) `(--->):(num->real)->real->(num)net->bool`)) (concl th) &&
        can (find_term ((=) `c0:real`)) (concl th))) THEN REWRITE_TAC[];
      MP_TAC(ISPECL [`\n. inv(&n + &1)`; `&0`; `t0:num->num`] HMD_REALLIM_SUBSEQ) THEN
      ASM_REWRITE_TAC[REALLIM_1_OVER_N_OFFSET];
      GEN_TAC THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN CONJ_TAC THENL
       [REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_INV_LE_1 THEN REAL_ARITH_TAC];
      MAP_EVERY X_GEN_TAC [`j:num`; `a:real^2`] THEN DISCH_TAC THEN
      REWRITE_TAC[cmc_b31dat] THEN USE_THEN "DAT" (MP_TAC o SPECL [`(t0:num->num) j`; `a:real^2`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num->num` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `alpha:real` (X_CHOOSE_THEN `beta:real` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `delta / Lam <= alpha /\ beta <= inv lam` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LBOUND) THEN
      EXISTS_TAC
       `\j. cmc_angE ((y:num->real^2) ((t0:num->num) ((q:num->num) j)))
              (cmc_ann (y (t0 (q j))) ((rho:num->real) (t0 (q j)) * exp(--l))
                                      (rho (t0 (q j)) * exp l))
              ((w:num->real^2->real^K) (t0 (q j))) /
            sqrt(cmc_pen G (cmc_nk (y (t0 (q j))) (rho (t0 (q j))) (&3 * l))
                           (w (t0 (q j)))) pow 2`;
      MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UBOUND) THEN
      EXISTS_TAC
       `\j. cmc_eE (cmc_ann ((y:num->real^2) ((t0:num->num) ((q:num->num) j)))
                       ((rho:num->real) (t0 (q j)) * exp(--(&2 * l)))
                       (rho (t0 (q j)) * exp(&2 * l)))
              ((w:num->real^2->real^K) (t0 (q j))) /
            sqrt(cmc_pen G (cmc_nk (y (t0 (q j))) (rho (t0 (q j))) (&3 * l))
                           (w (t0 (q j)))) pow 2`] THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `j:num` THEN REWRITE_TAC[] THEN
    USE_THEN "RAT" (MP_TAC o SPEC `(t0:num->num) ((q:num->num) j)`) THEN
    REWRITE_TAC[cmc_nk] THEN SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < Lam` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(delta * lam / (&2 * Lam)) * beta <= (delta * lam / (&2 * Lam)) * inv lam`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(delta * lam / (&2 * Lam)) * inv lam = delta / (&2 * Lam) /\
                delta / (&2 * Lam) < delta / Lam`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `&0 < lam` THEN UNDISCH_TAC `&0 < Lam` THEN CONV_TAC REAL_FIELD;
      SUBGOAL_THEN `delta / (&2 * Lam) = (delta / Lam) / &2` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < Lam` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < x ==> x / &2 < x`) THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `delta / Lam <= alpha` THEN
  UNDISCH_TAC `alpha <= (delta * lam / (&2 * Lam)) * beta` THEN
  UNDISCH_TAC `(delta * lam / (&2 * Lam)) * beta <= (delta * lam / (&2 * Lam)) * inv lam` THEN
  UNDISCH_TAC `(delta * lam / (&2 * Lam)) * inv lam = delta / (&2 * Lam)` THEN
  UNDISCH_TAC `delta / (&2 * Lam) < delta / Lam` THEN REAL_ARITH_TAC);;

