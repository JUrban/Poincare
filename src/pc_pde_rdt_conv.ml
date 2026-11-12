(* ========================================================================= *)
(* pc_pde_rdt_conv: the Ricci-DeTurck existence, part 8.  The                *)
(* frozen-coefficient iteration from g0, its iterates in the ball, the       *)
(* contraction for all pairs of iterates, interpolation of the chart norms   *)
(* and the uniform Cauchy property of the iterates at every level and of     *)
(* their space jets in the charts.                                           *)
(* ========================================================================= *)

needs "src/pc_pde_rdt_hi.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The iteration g_0 = g0, g_(k+1) = a step from g_k, and its                *)
(* iterates in the ball.                                                     *)
(* ------------------------------------------------------------------------- *)

let rdt_iter = define
 `(rdt_iter (top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (a:real) (b:real)
            (h:A->real^N^N) 0 = (\t:real. h)) /\
  (rdt_iter top atlas a b h (SUC k) =
     @v:real->A->real^N^N. pde_rdt_step (top,atlas) a b h (rdt_iter top atlas a b h k) v)`;;

let RDT_ITER_BALL = prove
 (`!(u:A->bool) (n:N->bool).
     PDE_MLIN_STATEMENT u n
     ==> !(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi s K tau g0 a.
           hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
           &0 < tau /\ riemannian_metric atlas g0 /\
           pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0 (\t. g0) /\
           (!g v. pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0 g /\
                  pde_rdt_step (top,atlas) a (a + tau) g0 g v
                  ==> pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0 v)
           ==> !k. pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0
                     (rdt_iter top atlas a (a + tau) g0 k) /\
                   pde_rdt_step (top,atlas) a (a + tau) g0
                     (rdt_iter top atlas a (a + tau) g0 k)
                     (rdt_iter top atlas a (a + tau) g0 (SUC k))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!k. pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0
          (rdt_iter top atlas a (a + tau) (g0:A->real^N^N) k)
        ==> pde_rdt_step (top,atlas) a (a + tau) g0
              (rdt_iter top atlas a (a + tau) g0 k)
              (rdt_iter top atlas a (a + tau) g0 (SUC k))`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV) [CONJUNCT2 rdt_iter] THEN CONV_TAC SELECT_CONV THEN
    MP_TAC(ISPECL [`u:A->bool`; `n:N->bool`] RDT_STEP_EXISTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0
                   (rdt_iter top atlas a (a + tau) (g0:A->real^N^N) k)` THEN
    REWRITE_TAC[pde_rdt_ball] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0
          (rdt_iter top atlas a (a + tau) (g0:A->real^N^N) k)`
  ASSUME_TAC THENL
   [INDUCT_TAC THENL
     [ASM_REWRITE_TAC[rdt_iter];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && rdt_has_const "pde_rdt_step" th &&
        not(rdt_has_const "rdt_iter" th))) THEN
      EXISTS_TAC `rdt_iter top atlas a (a + tau) (g0:A->real^N^N) k` THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[]);;

(* A ball of radius K lies in the ball of any larger radius. *)

let RDT_BALL_MONO = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi s K K' a tau g0 g.
     (!i. i < n0 ==> cs i IN atlas /\ ks i SUBSET IMAGE (SND(cs i)) (FST(cs i))) /\
     K <= K' /\ pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0 g
     ==> pde_rdt_ball (top,atlas) n0 cs ks psi s K' a tau g0 g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_rdt_ball] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  MATCH_MP_TAC RDT_CBOUND_MONO THEN
  MAP_EVERY EXISTS_TAC [`0`; `K:real`] THEN ASM_REWRITE_TAC[LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* |u - v|^2 <= 2 |u|^2 + 2 |v|^2 for the chart norms, and the               *)
(* contraction for all pairs of iterates: the quantity                       *)
(*   Dq(t) = |g_(j+k) - g_k|_0^2(t) + int_a^t |g_(j+k) - g_k|_1^2            *)
(* is at most D0 / 2^k.                                                      *)
(* ------------------------------------------------------------------------- *)

let RDT_MNORM2_SUB_LE = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi s
    (u:A->real^N^N) v.
     smooth_manifold_atlas top atlas /\ pde_cover (top,atlas) n0 cs ks /\
     pde_cutoffs (top,atlas) n0 cs psi /\
     (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
     pde_tensor_smooth atlas u /\ pde_tensor_smooth atlas v
     ==> pde_mnorm2 atlas n0 cs psi s (\x. u x - v x) <=
         &2 * pde_mnorm2 atlas n0 cs psi s u + &2 * pde_mnorm2 atlas n0 cs psi s v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`]
    RDT_COVER_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "cf") THEN
  REWRITE_TAC[RDT_MNORM2_HS] THEN
  SIMP_TAC[GSYM SUM_LMUL; GSYM SUM_ADD; FINITE_NUMSEG_LT] THEN
  MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  USE_THEN "cf" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `!w:A->real^N^N.
      pde_tensor_smooth atlas w
      ==> smooth_map_on (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i)))
            (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                   ((psi:num->A->real) i (chart_inv (cs i) z) %% metric_local atlas (cs i) w z)) /\
          (!z. z IN IMAGE (SND(cs i)) (FST(cs i)) /\ ~(z IN (ks:num->real^N->bool) i)
               ==> (vectorize:real^N^N->real^(N,N)finite_prod)
                     (psi i (chart_inv (cs i) z) %% metric_local atlas (cs i) w z) = vec 0)`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC RDT_PIECE THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `pde_tensor_smooth atlas (w:A->real^N^N)` THEN
    REWRITE_TAC[pde_tensor_smooth] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. (vectorize:real^N^N->real^(N,N)finite_prod)
           ((psi:num->A->real) i (chart_inv ((cs:num->(A->bool)#(A->real^N)) i) z) %%
            metric_local atlas (cs i) (\x. (u:A->real^N^N) x - v x) z)) =
    (\z. vectorize(psi i (chart_inv (cs i) z) %% metric_local atlas (cs i) u z) -
         vectorize(psi i (chart_inv (cs i) z) %% metric_local atlas (cs i) v z))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; METRIC_LOCAL_SUB; MATRIX_CMUL_SUB_LDISTRIB; VECTORIZE_SUB];
    ALL_TAC] THEN
  MATCH_MP_TAC RDT_HS_SUB2 THEN EXISTS_TAC `(ks:num->real^N->bool) i` THEN
  ASM_SIMP_TAC[ETA_AX]);;

(* The contraction quantity of two families. *)

let RDT_DQ_NONNEG = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi a b
    (g:real->A->real^N^N) g' t.
     smooth_manifold_atlas top atlas /\ pde_cover (top,atlas) n0 cs ks /\
     pde_cutoffs (top,atlas) n0 cs psi /\
     (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
     pde_tfam_from atlas a b g /\ pde_tfam_from atlas a b g' /\ a <= t /\ t < b
     ==> &0 <= pde_mnorm2 atlas n0 cs psi 0 (\x. g t x - g' t x) /\
         &0 <= real_integral (real_interval[a,t])
                 (\r. pde_mnorm2 atlas n0 cs psi 1 (\x. g r x - g' r x)) /\
         (\r. pde_mnorm2 atlas n0 cs psi 1 (\x. g r x - g' r x)) real_integrable_on
           real_interval[a,t]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `pde_tfam_from atlas a b (\t x. (g:real->A->real^N^N) t x - g' t x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_ME_TFAM_SUB THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. a <= r /\ r < b
        ==> pde_tensor_smooth atlas (\x. (g:real->A->real^N^N) r x - g' r x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[PDM_TENSOR_SMOOTH_EQ] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`;
                   `b:real`; `\t x. (g:real->A->real^N^N) t x - g' t x`; `r:real`]
      PDE_ML_TFAM_SLICE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\r. pde_mnorm2 atlas n0 cs psi 1 (\x. (g:real->A->real^N^N) r x - g' r x))
      real_integrable_on real_interval[a,t]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                   `a:real`; `b:real`; `t:real`; `\t x. (g:real->A->real^N^N) t x - g' t x`;
                   `1`] RDT_MNORM2_CONT) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PDE_ME_MNORM2_POS THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `ks:num->real^N->bool`] THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC REAL_INTEGRAL_POS THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
    X_GEN_TAC `r:real` THEN STRIP_TAC THEN MATCH_MP_TAC PDE_ME_MNORM2_POS THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `ks:num->real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

let RDT_DIV_POW2_SUC = prove
 (`!x k. x / &2 pow (SUC k) = (x / &2 pow k) / &2`,
  REWRITE_TAC[real_pow; real_div; REAL_INV_MUL] THEN REAL_ARITH_TAC);;

let RDT_ITER_CAUCHY0 = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi s K a tau g0
    (g:num->real->A->real^N^N).
     smooth_manifold_atlas top atlas /\ pde_cover (top,atlas) n0 cs ks /\
     pde_cutoffs (top,atlas) n0 cs psi /\
     (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
     1 <= s /\ &0 < K /\ &0 < tau /\
     (!k. pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0 (g k)) /\
     (!k. pde_rdt_step (top,atlas) a (a + tau) g0 (g k) (g (SUC k))) /\
     (!g g' v v' D.
        pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0 g /\
        pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0 g' /\
        pde_rdt_ball (top,atlas) n0 cs ks psi s K a tau g0 v' /\
        pde_rdt_step (top,atlas) a (a + tau) g0 g v /\
        pde_rdt_step (top,atlas) a (a + tau) g0 g' v' /\
        (!t. a <= t /\ t < a + tau
             ==> pde_mnorm2 atlas n0 cs psi 0 (\x. g t x - g' t x) +
                 real_integral (real_interval[a,t])
                   (\r. pde_mnorm2 atlas n0 cs psi 1 (\x. g r x - g' r x)) <= D)
        ==> !t. a <= t /\ t < a + tau
                ==> pde_mnorm2 atlas n0 cs psi 0 (\x. v t x - v' t x) +
                    real_integral (real_interval[a,t])
                      (\r. pde_mnorm2 atlas n0 cs psi 1 (\x. v r x - v' r x)) <= D / &2)
     ==> !j k t. a <= t /\ t < a + tau
                 ==> pde_mnorm2 atlas n0 cs psi 0 (\x. g (j + k) t x - g k t x) +
                     real_integral (real_interval[a,t])
                       (\r. pde_mnorm2 atlas n0 cs psi 1 (\x. g (j + k) r x - g k r x))
                     <= (&4 * K * (&1 + tau)) / &2 pow k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!k t. a <= t /\ t < a + tau
          ==> pde_tensor_smooth atlas ((g:num->real->A->real^N^N) k t) /\
              pde_mnorm2 atlas n0 cs psi 0 (g k t) <= K /\
              pde_mnorm2 atlas n0 cs psi 1 (g k t) <= K`
  (LABEL_TAC "gk") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
      is_forall(concl th) && rdt_has_const "pde_rdt_ball" th &&
      not(rdt_has_const "pde_rdt_step" th))) THEN
    REWRITE_TAC[pde_rdt_ball] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
      is_forall(concl th) && rdt_has_const "pde_cbound" th)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `pde_tensor_smooth atlas ((g:num->real->A->real^N^N) k t)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[PDM_TENSOR_SMOOTH_EQ; RIEMANNIAN_METRIC_TENSOR2_SMOOTH]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `pde_mnorm2 atlas n0 cs psi s ((g:num->real->A->real^N^N) k t)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RDT_MNORM2_MONO THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `ks:num->real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. pde_tfam_from atlas a (a + tau) ((g:num->real->A->real^N^N) k)`
  (LABEL_TAC "tf") THENL
   [GEN_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
      is_forall(concl th) && rdt_has_const "pde_rdt_ball" th &&
      not(rdt_has_const "pde_rdt_step" th))) THEN
    SIMP_TAC[pde_rdt_ball];
    ALL_TAC] THEN
  (* the base: any two iterates *)
  SUBGOAL_THEN
   `!j k t. a <= t /\ t < a + tau
            ==> pde_mnorm2 atlas n0 cs psi 0 (\x. (g:num->real->A->real^N^N) j t x - g k t x) +
                real_integral (real_interval[a,t])
                  (\r. pde_mnorm2 atlas n0 cs psi 1 (\x. g j r x - g k r x))
                <= &4 * K * (&1 + tau)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                   `a:real`; `a + tau:real`; `(g:num->real->A->real^N^N) j`;
                   `(g:num->real->A->real^N^N) k`; `t:real`] RDT_DQ_NONNEG) THEN
    ASM_SIMP_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!r. a <= r /\ r < a + tau
          ==> pde_mnorm2 atlas n0 cs psi 0 (\x. (g:num->real->A->real^N^N) j r x - g k r x)
              <= &4 * K /\
              pde_mnorm2 atlas n0 cs psi 1 (\x. g j r x - g k r x) <= &4 * K`
    ASSUME_TAC THENL
     [GEN_TAC THEN STRIP_TAC THEN
      USE_THEN "gk" (MP_TAC o SPECL [`j:num`; `r:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      USE_THEN "gk" (MP_TAC o SPECL [`k:num`; `r:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
       [EXISTS_TAC `&2 * pde_mnorm2 atlas n0 cs psi 0 ((g:num->real->A->real^N^N) j r) +
                    &2 * pde_mnorm2 atlas n0 cs psi 0 (g k r)`;
        EXISTS_TAC `&2 * pde_mnorm2 atlas n0 cs psi 1 ((g:num->real->A->real^N^N) j r) +
                    &2 * pde_mnorm2 atlas n0 cs psi 1 (g k r)`] THEN
      (CONJ_TAC THENL
        [MATCH_MP_TAC RDT_MNORM2_SUB_LE THEN EXISTS_TAC `top:A topology` THEN
         EXISTS_TAC `ks:num->real^N->bool` THEN ASM_REWRITE_TAC[];
         ASM_REAL_ARITH_TAC]);
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `!x y. x <= &4 * K /\ y <= &4 * K * tau
                                   ==> x + y <= &4 * K * (&1 + tau)`) THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `real_integral (real_interval[a,t]) (\r:real. &4 * K)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_LE THEN ASM_REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `&4 * K`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      ASM_SIMP_TAC[REAL_INTEGRAL_CONST] THEN
      SUBGOAL_THEN `&0 <= &4 * K` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `t - a <= tau` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= t - a` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REPEAT DISCH_TAC THEN
      SUBGOAL_THEN `(&4 * K) * (t - a) <= (&4 * K) * tau` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES; real_pow; REAL_DIV_1] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ADD_CLAUSES; RDT_DIV_POW2_SUC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    is_forall(concl th) && rdt_has_const "pde_rdt_ball" th &&
    rdt_has_const "pde_rdt_step" th)) THEN
  MAP_EVERY EXISTS_TAC [`(g:num->real->A->real^N^N) (j + k)`; `(g:num->real->A->real^N^N) k`] THEN
  ASM_REWRITE_TAC[ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* Interpolation of the chart norms (integration by parts and                *)
(* Young): for eps > 0,                                                      *)
(*   |u|_(j+1)^2 <= |u|_0^2 + N (eps |u|_j^2 + |u|_(j+2)^2 / eps),           *)
(* for functions with compact support in a chart, and for the manifold      *)
(* norms.                                                                    *)
(* ------------------------------------------------------------------------- *)

let RDT_HS_INTERP = prove
 (`!U K (u:real^N->real^Q) j eps.
     open U /\ compact K /\ K SUBSET U /\ smooth_map_on U u /\
     (!y. y IN U /\ ~(y IN K) ==> u y = vec 0) /\ &0 < eps
     ==> rdt_hs U (SUC j) u <=
         rdt_hs U 0 u + &(dimindex(:N)) * (eps * rdt_hs U j u + rdt_hs U (j + 2) u / eps)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`; `u:real^N->real^Q`; `j:num`] RDT_HS_SUC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[RDT_HS_0; REAL_LE_LADD] THEN
  SUBGOAL_THEN
   `!l. smooth_map_on U (iterated_partial l (u:real^N->real^Q)) /\
        (!y. y IN U /\ ~(y IN K) ==> iterated_partial l u y = vec 0)`
  ASSUME_TAC THENL
   [GEN_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_ITERATED_PARTIAL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RDT_PARTIAL_CS THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* one term *)
  SUBGOAL_THEN
   `!i l. 1 <= i /\ i <= dimindex(:N)
          ==> rdt_int U (\y. norm(partial_derivative i (iterated_partial l (u:real^N->real^Q)) y)
                             pow 2) <=
              eps * rdt_int U (\y. norm(iterated_partial l u y) pow 2) +
              inv eps * rdt_int U (\y. norm(iterated_partial (CONS i (CONS i l)) u y) pow 2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `rdt_int U (\y. norm(partial_derivative i (iterated_partial l (u:real^N->real^Q)) y) pow 2) =
      --(rdt_int U (\y. iterated_partial l u y dot
                        iterated_partial (CONS i (CONS i l)) u y))`
    SUBST1_TAC THENL
     [REWRITE_TAC[NORM_POW_2; iterated_partial] THEN MATCH_MP_TAC RDT_INT_IBP THEN
      EXISTS_TAC `K:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!l'. rdt_cs U K (\y. norm(iterated_partial l' (u:real^N->real^Q) y) pow 2)`
    ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC RDT_CS_SQNORM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `rdt_cs U K (\y. iterated_partial l (u:real^N->real^Q) y dot
                      iterated_partial (CONS i (CONS i l)) u y)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC RDT_CS_SMOOTH_DOT THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`;
                   `\y. iterated_partial l (u:real^N->real^Q) y dot
                        iterated_partial (CONS i (CONS i l)) u y`] RDT_INT_NEG) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`;
                   `\y. norm(iterated_partial l (u:real^N->real^Q) y) pow 2`; `eps:real`]
      RDT_INT_CMUL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`;
                   `\y. norm(iterated_partial (CONS i (CONS i l)) (u:real^N->real^Q) y) pow 2`;
                   `inv eps`] RDT_INT_CMUL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`;
                   `\y. eps * norm(iterated_partial l (u:real^N->real^Q) y) pow 2`;
                   `\y. inv eps * norm(iterated_partial (CONS i (CONS i l)) (u:real^N->real^Q) y)
                                  pow 2`] RDT_INT_ADD) THEN
    ASM_SIMP_TAC[RDT_CS_CMUL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC RDT_INT_LE THEN EXISTS_TAC `K:real^N->bool` THEN
    ASM_SIMP_TAC[RDT_CS_NEG; RDT_CS_ADD; RDT_CS_CMUL] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`inv eps`; `iterated_partial l (u:real^N->real^Q) y`;
                   `iterated_partial (CONS i (CONS i l)) (u:real^N->real^Q) y`]
      (INST_TYPE [`:Q`,`:N`] RDT_YOUNG)) THEN
    ASM_REWRITE_TAC[REAL_LT_INV_EQ; REAL_INV_INV] THEN
    SUBGOAL_THEN `&0 <= eps * norm(iterated_partial l (u:real^N->real^Q) y) pow 2 /\
                  &0 <= inv eps * norm(iterated_partial (CONS i (CONS i l)) u y) pow 2`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LE_POW_2; REAL_LT_IMP_LE; REAL_LE_INV_EQ];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the sum *)
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> sum (pde_index_lists j (:N))
              (\l. rdt_int U (\y. norm(iterated_partial (CONS i (CONS i l)) (u:real^N->real^Q) y)
                                 pow 2)) <=
            sum (pde_index_lists (j + 2) (:N))
              (\l. rdt_int U (\y. norm(iterated_partial l u y) pow 2))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `sum (pde_index_lists j (:N))
        (\l. rdt_int U (\y. norm(iterated_partial (CONS i (CONS i l)) (u:real^N->real^Q) y)
                            pow 2)) =
      sum (IMAGE (\l. CONS i (CONS i l)) (pde_index_lists j (:N)))
        (\l. rdt_int U (\y. norm(iterated_partial l u y) pow 2))`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN
      W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o lhand o snd) THEN
      ANTS_TAC THENL [REWRITE_TAC[CONS_11] THEN MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[o_DEF];
      ALL_TAC] THEN
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `l:num list` THEN
      REWRITE_TAC[pde_index_lists; IN_ELIM_THM; LENGTH; ALL] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC RDT_HS_TERM_POS THEN
      EXISTS_TAC `K:real^N->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(1..dimindex(:N))
      (\i. eps * rdt_hs U j (u:real^N->real^Q) + inv eps * rdt_hs U (j + 2) u)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `sum (pde_index_lists j (:N))
        (\l. eps * rdt_int U (\y. norm(iterated_partial l (u:real^N->real^Q) y) pow 2) +
             inv eps * rdt_int U (\y. norm(iterated_partial (CONS i (CONS i l)) u y) pow 2))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SIMP_TAC[SUM_ADD; SUM_LMUL; PDE_INDEX_LISTS_FINITE] THEN
    REWRITE_TAC[rdt_hs; REAL_LE_LADD] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; real_div] THEN
  REWRITE_TAC[REAL_MUL_AC; REAL_LE_REFL]);;

let RDT_MNORM2_INTERP = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi (w:A->real^N^N) j eps.
     smooth_manifold_atlas top atlas /\ pde_cover (top,atlas) n0 cs ks /\
     pde_cutoffs (top,atlas) n0 cs psi /\
     (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
     pde_tensor_smooth atlas w /\ &0 < eps
     ==> pde_mnorm2 atlas n0 cs psi (SUC j) w <=
         pde_mnorm2 atlas n0 cs psi 0 w +
         &(dimindex(:N)) * (eps * pde_mnorm2 atlas n0 cs psi j w +
                            pde_mnorm2 atlas n0 cs psi (j + 2) w / eps)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`]
    RDT_COVER_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "cf") THEN
  REWRITE_TAC[RDT_MNORM2_HS; real_div] THEN
  SIMP_TAC[GSYM SUM_LMUL; GSYM SUM_RMUL; GSYM SUM_ADD; FINITE_NUMSEG_LT] THEN
  MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[GSYM real_div] THEN
  USE_THEN "cf" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) i`; `(psi:num->A->real) i`;
                 `(ks:num->real^N->bool) i`; `w:A->real^N^N`] RDT_PIECE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `pde_tensor_smooth atlas (w:A->real^N^N)` THEN
    REWRITE_TAC[pde_tensor_smooth] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  MATCH_MP_TAC RDT_HS_INTERP THEN EXISTS_TAC `(ks:num->real^N->bool) i` THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The iterates are uniformly Cauchy at every level: from the                *)
(* contraction at level 0, the uniform bounds at every level and the         *)
(* interpolation inequality, by induction on the level.                      *)
(* ------------------------------------------------------------------------- *)

let RDT_POW2_SMALL = prove
 (`!D0 e. &0 <= D0 /\ &0 < e ==> ?k0. !k. k0 <= k ==> D0 / &2 pow k <= e`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`&2`; `D0 / e`] REAL_ARCH_POW) THEN
  REWRITE_TAC[REAL_ARITH `&1 < &2`] THEN DISCH_THEN(X_CHOOSE_TAC `k0:num`) THEN
  EXISTS_TAC `k0:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &2 pow k0 /\ &2 pow k0 <= &2 pow k` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 pow k` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  SUBGOAL_THEN `D0 < e * &2 pow k0` MP_TAC THENL
   [UNDISCH_TAC `D0 / e < &2 pow k0` THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `e * &2 pow k0 <= e * &2 pow k` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let RDT_ITER_CAUCHY_LEVELS = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi a b D0
    (g:num->real->A->real^N^N).
     smooth_manifold_atlas top atlas /\ pde_cover (top,atlas) n0 cs ks /\
     pde_cutoffs (top,atlas) n0 cs psi /\
     (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
     &0 <= D0 /\
     (!k t. a <= t /\ t < b ==> pde_tensor_smooth atlas (g k t)) /\
     (!j k t. a <= t /\ t < b
              ==> pde_mnorm2 atlas n0 cs psi 0 (\x. g (j + k) t x - g k t x) <= D0 / &2 pow k) /\
     (!l. ?M. !k t. a <= t /\ t < b ==> pde_mnorm2 atlas n0 cs psi l (g k t) <= M)
     ==> !l e. &0 < e
               ==> ?k0. !m k t. k0 <= k /\ k <= m /\ a <= t /\ t < b
                                ==> pde_mnorm2 atlas n0 cs psi l (\x. g m t x - g k t x) <= e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!m k t. a <= t /\ t < b
            ==> pde_tensor_smooth atlas (\x. (g:num->real->A->real^N^N) m t x - g k t x)`
  (LABEL_TAC "ts") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[PDM_TENSOR_SMOOTH_EQ] THEN
    MATCH_MP_TAC MFD_TENSOR2_SMOOTH_SUB THEN EXISTS_TAC `top:A topology` THEN
    REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[GSYM PDM_TENSOR_SMOOTH_EQ];
    ALL_TAC] THEN
  INDUCT_TAC THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`D0:real`; `e:real`] RDT_POW2_SMALL) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `k0:num`) THEN EXISTS_TAC `k0:num` THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `k:num`; `t:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `m = (m - k) + k:num` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `D0 / &2 pow k` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(LABEL_TAC "ih") THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `M:real` o SPEC `l + 2` o check (fun th ->
    is_forall(concl th) && is_exists(snd(dest_forall(concl th))))) THEN
  ABBREV_TAC `M' = abs M` THEN
  SUBGOAL_THEN `&0 <= M'` ASSUME_TAC THENL [EXPAND_TAC "M'" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `dN = &(dimindex(:N))` THEN
  SUBGOAL_THEN `&1 <= dN` ASSUME_TAC THENL
   [EXPAND_TAC "dN" THEN REWRITE_TAC[REAL_OF_NUM_LE; DIMINDEX_GE_1]; ALL_TAC] THEN
  ABBREV_TAC `eps = (&12 * dN * (M' + &1)) / e + &1` THEN
  SUBGOAL_THEN `&0 < eps /\ &12 * dN * (M' + &1) <= eps * e` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eps" THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN
      MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL [RDT_NN_TAC THEN ASM_REAL_ARITH_TAC;
                                                    ASM_REAL_ARITH_TAC];
      REWRITE_TAC[REAL_ADD_RDISTRIB; REAL_MUL_LID] THEN
      ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `d' = e / (&3 * (&1 + dN * eps))` THEN
  SUBGOAL_THEN `&0 < d' /\ (&1 + dN * eps) * d' = e / &3` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d'" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 <= dN * eps` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      SUBGOAL_THEN `~(&1 + dN * eps = &0)` MP_TAC THENL
       [SUBGOAL_THEN `&0 <= dN * eps` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
        CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  USE_THEN "ih" (MP_TAC o SPEC `d':real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_TAC `k0:num`)] THEN
  EXISTS_TAC `k0:num` THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `k:num`; `t:real`] THEN STRIP_TAC THEN
  ABBREV_TAC `w = \x. (g:num->real->A->real^N^N) m t x - g k t x` THEN
  SUBGOAL_THEN `pde_tensor_smooth atlas (w:A->real^N^N)` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN USE_THEN "ts" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `pde_mnorm2 atlas n0 cs psi l (w:A->real^N^N) <= d' /\
    pde_mnorm2 atlas n0 cs psi 0 w <= d' /\
    pde_mnorm2 atlas n0 cs psi (l + 2) w <= &4 * M'`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `pde_mnorm2 atlas n0 cs psi l (w:A->real^N^N) <= d'` ASSUME_TAC THENL
     [EXPAND_TAC "w" THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `k0:num`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `pde_mnorm2 atlas n0 cs psi l (w:A->real^N^N)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC RDT_MNORM2_MONO THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `ks:num->real^N->bool`] THEN
      ASM_REWRITE_TAC[LE_0];
      ALL_TAC] THEN
    EXPAND_TAC "w" THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 * pde_mnorm2 atlas n0 cs psi (l + 2) ((g:num->real->A->real^N^N) m t) +
                &2 * pde_mnorm2 atlas n0 cs psi (l + 2) (g k t)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RDT_MNORM2_SUB_LE THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `ks:num->real^N->bool`] THEN ASM_SIMP_TAC[];
      SUBGOAL_THEN
       `pde_mnorm2 atlas n0 cs psi (l + 2) ((g:num->real->A->real^N^N) m t) <= M /\
        pde_mnorm2 atlas n0 cs psi (l + 2) (g k t) <= M`
      MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "M'" THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `w:A->real^N^N`; `l:num`; `eps:real`] RDT_MNORM2_INTERP) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `dN * (pde_mnorm2 atlas n0 cs psi (l + 2) (w:A->real^N^N) / eps) <= e / &3`
  MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `x * y / z = (x * y) / z`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `dN * &4 * M'` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(eps * e) / &3` THEN CONJ_TAC THENL
       [SUBGOAL_THEN `&0 <= dN * M'` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `&0 <= dN` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `dN * eps * pde_mnorm2 atlas n0 cs psi l (w:A->real^N^N) <= dN * eps * d'`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  UNDISCH_TAC `(&1 + dN * eps) * d' = e / &3` THEN
  UNDISCH_TAC `pde_mnorm2 atlas n0 cs psi 0 (w:A->real^N^N) <= d'` THEN
  UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The space jets of the iterates in the charts are uniformly                *)
(* Cauchy on the pieces (homogeneous Sobolev PDE_MNORM_SOBOLEV for the       *)
(* differences).                                                             *)
(* ------------------------------------------------------------------------- *)

let RDT_ITER_CAUCHY_JETS = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi a b D0
    (g:num->real->A->real^N^N).
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     pde_cover (top,atlas) n0 cs ks /\ pde_cutoffs (top,atlas) n0 cs psi /\
     (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
     &0 <= D0 /\
     (!k t. a <= t /\ t < b ==> pde_tensor_smooth atlas (g k t)) /\
     (!j k t. a <= t /\ t < b
              ==> pde_mnorm2 atlas n0 cs psi 0 (\x. g (j + k) t x - g k t x) <= D0 / &2 pow k) /\
     (!l. ?M. !k t. a <= t /\ t < b ==> pde_mnorm2 atlas n0 cs psi l (g k t) <= M)
     ==> !i l e. i < n0 /\ ALL (\j. 1 <= j /\ j <= dimindex(:N)) l /\ &0 < e
                 ==> ?k0. !m k t y. k0 <= k /\ k <= m /\ a <= t /\ t < b /\ y IN ks i
                                    ==> norm(iterated_partial l
                                               ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                                metric_local atlas (cs i) (g m t)) y -
                                             iterated_partial l
                                               ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                                metric_local atlas (cs i) (g k t)) y) <= e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`]
    RDT_COVER_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `LENGTH(l:num list)`] PDE_MNORM_SOBOLEV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `CS:real`) THEN
  ABBREV_TAC `C1 = abs CS + &1` THEN
  SUBGOAL_THEN `&0 < C1` ASSUME_TAC THENL [EXPAND_TAC "C1" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `a:real`; `b:real`; `D0:real`; `g:num->real->A->real^N^N`]
    RDT_ITER_CAUCHY_LEVELS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`LENGTH(l:num list) + dimindex(:N)`; `e pow 2 / C1`]) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `k0:num`) THEN EXISTS_TAC `k0:num` THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `k:num`; `t:real`; `y:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pde_tensor_smooth atlas (\x. (g:num->real->A->real^N^N) m t x - g k t x)`
  ASSUME_TAC THENL
   [REWRITE_TAC[PDM_TENSOR_SMOOTH_EQ] THEN
    MATCH_MP_TAC MFD_TENSOR2_SMOOTH_SUB THEN EXISTS_TAC `top:A topology` THEN
    REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[GSYM PDM_TENSOR_SMOOTH_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i)))
      ((vectorize:real^N^N->real^(N,N)finite_prod) o
       metric_local atlas (cs i) ((g:num->real->A->real^N^N) m t)) /\
    smooth_map_on (IMAGE (SND(cs i)) (FST(cs i)))
      ((vectorize:real^N^N->real^(N,N)finite_prod) o metric_local atlas (cs i) (g k t))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `pde_tensor_smooth atlas ((g:num->real->A->real^N^N) m t)` MP_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC];
      SUBGOAL_THEN `pde_tensor_smooth atlas ((g:num->real->A->real^N^N) k t)` MP_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC]] THEN
    REWRITE_TAC[pde_tensor_smooth] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `iterated_partial l ((vectorize:real^N^N->real^(N,N)finite_prod) o
                         metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                           ((g:num->real->A->real^N^N) m t)) y -
    iterated_partial l ((vectorize:real^N^N->real^(N,N)finite_prod) o
                         metric_local atlas (cs i) (g k t)) y =
    iterated_partial l ((vectorize:real^N^N->real^(N,N)finite_prod) o
                         metric_local atlas (cs i) (\x. g m t x - g k t x)) y`
  SUBST1_TAC THENL
   [REWRITE_TAC[METRIC_LOCAL_SUB; ETA_AX] THEN
    SUBGOAL_THEN
     `(vectorize:real^N^N->real^(N,N)finite_prod) o
      (\y. metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
             ((g:num->real->A->real^N^N) m t) y - metric_local atlas (cs i) (g k t) y) =
      (\y. ((vectorize:real^N^N->real^(N,N)finite_prod) o metric_local atlas (cs i) (g m t)) y -
           (vectorize o metric_local atlas (cs i) (g k t)) y)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; VECTORIZE_SUB]; ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`l:num list`; `IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))`;
                   `(vectorize:real^N^N->real^(N,N)finite_prod) o
                    metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                      ((g:num->real->A->real^N^N) m t)`;
                   `(vectorize:real^N^N->real^(N,N)finite_prod) o
                    metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                      ((g:num->real->A->real^N^N) k t)`]
      TEXT_ITERATED_PARTIAL_SUB_OPEN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; ARITH_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `CS * pde_mnorm2 atlas n0 cs psi (LENGTH(l:num list) + dimindex(:N))
                     (\x. (g:num->real->A->real^N^N) m t x - g k t x)` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `CS:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[pde_index_lists; IN_ELIM_THM; LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pde_mnorm2 atlas n0 cs psi (LENGTH(l:num list) + dimindex(:N))
      (\x. (g:num->real->A->real^N^N) m t x - g k t x) <= e pow 2 / C1 /\
    &0 <= pde_mnorm2 atlas n0 cs psi (LENGTH(l:num list) + dimindex(:N))
      (\x. (g:num->real->A->real^N^N) m t x - g k t x)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `k0:num`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC PDE_ME_MNORM2_POS THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `ks:num->real^N->bool`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `E = pde_mnorm2 atlas n0 cs psi (LENGTH(l:num list) + dimindex(:N))
                    (\x. (g:num->real->A->real^N^N) m t x - g k t x)` THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C1 * E` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "C1" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C1 * e pow 2 / C1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ; REAL_LE_REFL]]);;

