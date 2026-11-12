(* ========================================================================= *)
(* Unit pc_p2b_p946f: the soliton flow of MT Prop 9.46, (9.19).  The         *)
(* gradient grad f in preferred coordinates (p2bx46_gradf, the local         *)
(* gradient p3s_cgrad of pc_p3_s13conf) is represented in every chart by the *)
(* local gradient (P2BX46_GRADF_VREP); the field grad f / |t| on t < 0 is    *)
(* smooth in charts and f is an escape function for it (P2BX46_SOL_ESCAPE),  *)
(* so the flow of pc_mfd_cflow exists (P2BX46_SOL_MCF_HYP).  The chart       *)
(* lemmas of pc_pde_gauge for cflow flows (P2BX46_MCF_METRIC_LOCAL,          *)
(* _RF_VALUE, _TIME_DERIV); the Lie derivative of G along grad F is 2 Hess F *)
(* in charts (P2BX46_LLIE_CGRAD); the time derivative of the pullback of a   *)
(* static metric along a cflow flow (P2BX46_PULLBACK_STATIC_DERIV).          *)
(* ========================================================================= *)

needs "src/pc_p2b_p946s.ml";;
needs "src/pc_p3_s13conf.ml";;
needs "src/pc_pde_gauge.ml";;

prioritize_real();;
type_invention_error := true;;


(* ========================================================================= *)
(* The gradient grad f in charts and the smoothness of grad f / |t|.         *)
(* ========================================================================= *)

(* grad f at x, in the coordinates of chart_at x (p3s_cgrad of pc_p3_s13conf). *)

let p2bx46_gradf = new_definition
 `p2bx46_gradf (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (f:A->real) (x:A) =
    p3s_cgrad (metric_local atlas (chart_at atlas x) g)
              (\y. f(chart_inv (chart_at atlas x) y)) (SND(chart_at atlas x) x)`;;

(* Uniqueness of the gradient: w.(G v) = dF(w) for all w determines v. *)

let P2BX46_CGRAD_UNIQUE = prove
 (`!U (G:real^N->real^N^N) cf y v.
     metric_field U G /\ y IN U /\ (\z. lift(cf z)) differentiable at y /\
     (!w. w dot (G y ** v) = p3s_cdf cf y w)
     ==> v = p3s_cgrad G cf y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `cf:real^N->real`; `y:real^N`]
    P3S_CGRAD_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_METRIC_INVERTIBLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(G:real^N->real^N^N) y ** v = G y ** p3s_cgrad G cf y` MP_TAC THENL
   [ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
    REWRITE_TAC[GSYM DOT_EQ_0] THEN
    ASM_REWRITE_TAC[DOT_RSUB] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `\z:real^N. matrix_inv((G:real^N->real^N^N) y) ** z`) THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID]);;

(* The chain rule for the chart representatives of a function. *)

let P2BX46_CDF_CHART = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) V psi (f:A->real) x w.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\ (V,psi) IN atlas /\
        x IN U INTER V /\
        smooth_map_on (IMAGE psi V) (\y. lift(f(chart_inv (V,psi) y)))
        ==> p3s_cdf (\y. f(chart_inv (U,phi) y)) (phi x) w =
            p3s_cdf (\y. f(chart_inv (V,psi) y)) (psi x) (chart_jac (U,phi) (V,psi) x w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `V:A->bool`; `psi:A->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(IMAGE (phi:A->real^N) (U INTER V))` ASSUME_TAC THENL
   [ASM_MESON_TAC[CHART_OVERLAP_IMAGE_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (psi:A->real^N) V)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART; CHART_IMAGE_OPEN; SUBSET_REFL]; ALL_TAC] THEN
  REWRITE_TAC[p3s_cdf] THEN
  SUBGOAL_THEN
   `frechet_derivative (\z. lift((f:A->real)(chart_inv (U:A->bool,phi:A->real^N) z)))
      (at (phi x)) =
    frechet_derivative (\z. lift(f(chart_inv (V,psi) z))) (at ((psi:A->real^N) x)) o
    chart_jac (U,phi) (V,psi) x`
  (fun th -> REWRITE_TAC[th; o_THM]) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `(\z. lift((f:A->real)(chart_inv (V:A->bool,psi:A->real^N) z))) o
              chart_trans (U:A->bool,phi:A->real^N) (V,psi)` THEN
  MP_TAC(ISPEC `IMAGE (phi:A->real^N) (U INTER V)` OPEN_CONTAINS_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `(phi:A->real^N) x`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^N) IN IMAGE (phi:A->real^N) (U INTER V)` MP_TAC THENL
     [UNDISCH_TAC `ball((phi:A->real^N) x,e) SUBSET IMAGE phi (U INTER V)` THEN
      REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_MESON_TAC[DIST_SYM];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:A` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[o_THM; chart_trans; SND] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
   [MATCH_MP_TAC CHART_TRANS_HAS_DERIVATIVE THEN EXISTS_TAC `top:A topology` THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`; `x:A`]
    CHART_TRANS_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `IMAGE (psi:A->real^N) V` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* The representation of grad f in any chart is the local gradient there. *)

let P2BX46_GRADF_VREP = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f c y.
     p2b_shrinker (top,atlas) g f /\ c IN atlas /\ y IN IMAGE (SND c) (FST c)
     ==> mfd_vrep atlas (p2bx46_gradf atlas g f) c y =
         p3s_cgrad (metric_local atlas c g) (\z. f(chart_inv c z)) y`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `y:real^N`] MCF_CHART_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `x = chart_inv (c:(A->bool)#(A->real^N)) y` THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  REWRITE_TAC[mfd_vrep] THEN ASM_REWRITE_TAC[p2bx46_gradf] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `f:A->real`; `c:(A->bool)#(A->real^N)`] RFA_SH_CHART_DATA) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `f:A->real`; `c0:(A->bool)#(A->real^N)`] RFA_SH_CHART_DATA) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC P2BX46_CGRAD_UNIQUE THEN
  EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
    ASM_MESON_TAC[metric_field];
    ALL_TAC] THEN
  X_GEN_TAC `w:real^N` THEN
  SUBGOAL_THEN `(c0:(A->bool)#(A->real^N)) IN atlas /\ (x:A) IN FST c0` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                 `g:A->real^N^N`; `x:A`] METRIC_LOCAL_JAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                 `x:A`] CHART_JAC_LINEAR) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `x:A`] CHART_JAC_INVERSE) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                 `f:A->real`; `x:A`; `w:real^N`] P2BX46_CDF_CHART) THEN
  REWRITE_TAC[PAIR] THEN ASM_REWRITE_TAC[IN_INTER] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN(LABEL_TAC "inv") THEN
  DISCH_THEN(LABEL_TAC "lin") THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
  USE_THEN "lin" (fun th -> REWRITE_TAC[MATCH_MP MATRIX_WORKS th]) THEN
  USE_THEN "inv" (fun th -> REWRITE_TAC[REWRITE_RULE[FUN_EQ_THM; o_THM] th]) THEN
  MATCH_MP_TAC P3S_CGRAD_DOT THEN
  EXISTS_TAC `IMAGE (SND (c0:(A->bool)#(A->real^N))) (FST c0)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `IMAGE (SND (c0:(A->bool)#(A->real^N))) (FST c0)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[metric_field]; MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]);;

(* The soliton field grad f / |t| on t < 0 is smooth in every chart. *)

let P2BX46_SOLFIELD_SMOOTH = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f c.
     p2b_shrinker (top,atlas) g f /\ c IN atlas
     ==> smooth_map_on ({t:real^1 | drop t < &0} PCROSS IMAGE (SND c) (FST c))
           (mfl_field atlas (\t x. inv(abs t) % p2bx46_gradf atlas g f x) c)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `f:A->real`; `c:(A->bool)#(A->real^N)`] RFA_SH_CHART_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `open {t:real^1 | drop t < &0}` ASSUME_TAC THENL
   [REWRITE_TAC[drop; OPEN_HALFSPACE_COMPONENT_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `open({t:real^1 | drop t < &0} PCROSS IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[OPEN_PCROSS]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC
   `\z:real^(1,N)finite_sum.
       drop(lift(inv(--drop(fstcart z)))) %
       p3s_cgrad (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))
                 (\y. (f:A->real)(chart_inv c y)) (sndcart z)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_ELIM_THM;
                FSTCART_PASTECART; SNDCART_PASTECART; MFL_FIELD_PASTECART; LIFT_DROP] THEN
    MAP_EVERY X_GEN_TAC [`t:real^1`; `y:real^N`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `\x:A. inv(abs(drop t))`; `p2bx46_gradf atlas (g:A->real^N^N) f`;
                   `c:(A->bool)#(A->real^N)`; `y:real^N`] MCF_VREP_CMUL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `f:A->real`; `c:(A->bool)#(A->real^N)`; `y:real^N`]
      P2BX46_GRADF_VREP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM DROP_NEG] THEN MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_INV THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC GEOL_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[linear; FSTCART_ADD; FSTCART_CMUL] THEN VECTOR_ARITH_TAC;
      REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_ELIM_THM; FSTCART_PASTECART;
                  DROP_NEG] THEN
      REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z:real^(1,N)finite_sum.
       p3s_cgrad (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))
                 (\y. (f:A->real)(chart_inv c y)) (sndcart z)) =
    (\y. p3s_cgrad (metric_local atlas c g) (\y. f(chart_inv c y)) y) o sndcart`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
                SNDCART_PASTECART] THEN SIMP_TAC[];
    MATCH_MP_TAC GEOL_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[LINEAR_SNDCART];
    MATCH_MP_TAC P3S_CGRAD_SMOOTH THEN ASM_REWRITE_TAC[]]);;


(* ========================================================================= *)
(* The escape function and the flow hypotheses.                              *)
(* ========================================================================= *)

(* dF(grad F) = |dF|^2 for the local gradient. *)

let P2BX46_CDF_RFA_D1 = prove
 (`!cf (y:real^N) a. p3s_cdf cf y a = rfa_d1 cf y a`,
  REWRITE_TAC[p3s_cdf; rfa_d1]);;

let P2BX46_CDF_CGRAD = prove
 (`!U (G:real^N->real^N^N) cf y.
     metric_field U G /\ y IN U /\ smooth_map_on U (\z. lift(cf z))
     ==> p3s_cdf cf y (p3s_cgrad G cf y) = lgrad2 G cf y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `cf:real^N->real`; `y:real^N`] P2BX46_D1_DOT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  REWRITE_TAC[P2BX46_CDF_RFA_D1] THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[GSYM(CONJUNCT2(SPEC `p3s_cgrad (G:real^N->real^N^N) cf y` th))]) THEN
  REWRITE_TAC[p3s_cgrad; P3S_JAC_ROW1; lgrad2; RFA_BILIN_SUM; rfa_d1]);;

(* f is an escape function for grad f / |t| on t < 0. *)

let P2BX46_SOL_ESCAPE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f K.
     hausdorff_space top /\ connected_space top /\ p2b_shrinker (top,atlas) g f /\
     mfd_complete (top,atlas) g /\ &0 <= K /\
     (!x. x IN topspace top ==> &0 <= mfd_scalar atlas g x) /\
     (!y w. y IN topspace top ==> &0 <= mfd_ricci atlas g y w w) /\
     (!y w. y IN topspace top
            ==> mfd_ricci atlas g y w w <= &(dimindex(:N) - 1) * K * (w dot (g y ** w)))
     ==> mcf_escape top atlas (\t x. inv(abs t) % p2bx46_gradf atlas g f x)
                    {t:real^1 | drop t < &0} f`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  SUBGOAL_THEN `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x:A. lift((f:A->real) x))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `\x:A. lift((f:A->real) x)`] MFD_SMOOTH_ON_TOPSPACE) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (top,euclideanreal) (f:A->real)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `\x:A. lift((f:A->real) x)`] GRGE_MFD_SMOOTH_CONTINUOUS) THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_EQ_DROP; o_DEF; LIFT_DROP; ETA_AX];
    ALL_TAC] THEN
  REWRITE_TAC[mcf_escape] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `c:real` THEN MATCH_MP_TAC CLOSED_COMPACT_IN THEN
    EXISTS_TAC `{x:A | x IN topspace top /\ (f:A->real) x <= c}` THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                     `f:A->real`; `K:real`] P2BX46_F_PROPER) THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN GEN_TAC THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`\x:A. abs((f:A->real) x)`; `top:A topology`; `euclideanreal`;
                     `{r:real | r <= c}`] CLOSED_IN_CONTINUOUS_MAP_PREIMAGE) THEN
      REWRITE_TAC[GSYM REAL_CLOSED_IN; REAL_CLOSED_HALFSPACE_LE; IN_ELIM_THM] THEN
      DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC CONTINUOUS_MAP_REAL_ABS THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`] P2BX46_HAMILTON_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `C0:real` (LABEL_TAC "hb")) THEN
  MAP_EVERY X_GEN_TAC [`a:real^1`; `b:real^1`] THEN DISCH_TAC THEN
  ASM_CASES_TAC `drop a <= drop b` THENL
   [ALL_TAC;
    EXISTS_TAC `&0` THEN REWRITE_TAC[REAL_LE_REFL; IN_INTERVAL_1] THEN ASM_REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `drop b < &0` ASSUME_TAC THENL
   [UNDISCH_TAC `interval[a:real^1,b] SUBSET {t:real^1 | drop t < &0}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[IN_INTERVAL_1] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `inv(abs(drop b)) * (&1 + abs C0)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_ABS_POS] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real^1`; `x:A`] THEN
  REWRITE_TAC[IN_INTERVAL_1] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`]
    RFA_SH_CHART_DATA) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[CHART_AT]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`] CMPF_LOCAL_METRIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  SUBGOAL_THEN
   `linear(frechet_derivative (\y. lift((f:A->real)(chart_inv (c0:(A->bool)#(A->real^N)) y)))
                              (at (SND c0 (x:A))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (SND (c0:(A->bool)#(A->real^N))) (FST c0)` THEN
    ASM_MESON_TAC[metric_field];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
  ASM_REWRITE_TAC[DROP_CMUL; p2bx46_gradf] THEN
  MP_TAC(ISPECL [`IMAGE (SND (c0:(A->bool)#(A->real^N))) (FST c0)`;
                 `metric_local atlas (c0:(A->bool)#(A->real^N)) (g:A->real^N^N)`;
                 `\y. (f:A->real)(chart_inv (c0:(A->bool)#(A->real^N)) y)`;
                 `SND (c0:(A->bool)#(A->real^N)) (x:A)`] P2BX46_CDF_CGRAD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[p3s_cdf]] THEN
  DISCH_THEN SUBST1_TAC THEN
  USE_THEN "hb" (MP_TAC o C MATCH_MP (ASSUME `(x:A) IN topspace top`)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `q = lgrad2 (metric_local atlas (c0:(A->bool)#(A->real^N)) (g:A->real^N^N))
                         (\y. (f:A->real)(chart_inv c0 y)) (SND c0 (x:A))` THEN
  SUBGOAL_THEN `&0 <= q` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN MATCH_MP_TAC LGRAD2_POS THEN
    EXISTS_TAC `IMAGE (SND (c0:(A->bool)#(A->real^N))) (FST c0)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(abs(drop t)) <= inv(abs(drop b))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `q <= (&1 + abs C0) * (&1 + abs((f:A->real) x))` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= abs C0 * abs((f:A->real) x)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_ABS] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= q ==> abs q = q`] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_REWRITE_TAC[REAL_LE_INV_EQ; REAL_ABS_POS]);;

(* The soliton field satisfies the hypotheses of pc_mfd_cflow on t < 0. *)

let P2BX46_SOL_MCF_HYP = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f K.
     hausdorff_space top /\ connected_space top /\ p2b_shrinker (top,atlas) g f /\
     mfd_complete (top,atlas) g /\ &0 <= K /\
     (!x. x IN topspace top ==> &0 <= mfd_scalar atlas g x) /\
     (!y w. y IN topspace top ==> &0 <= mfd_ricci atlas g y w w) /\
     (!y w. y IN topspace top
            ==> mfd_ricci atlas g y w w <= &(dimindex(:N) - 1) * K * (w dot (g y ** w)))
     ==> mcf_hyp top atlas (\t x. inv(abs t) % p2bx46_gradf atlas g f x)
                 {t:real^1 | drop t < &0} f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mcf_hyp] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[drop; OPEN_HALFSPACE_COMPONENT_LT];
    REWRITE_TAC[IS_INTERVAL_1; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BX46_SOLFIELD_SMOOTH THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2BX46_SOL_ESCAPE THEN EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[]]);;


(* ========================================================================= *)
(* The chart lemmas of pc_pde_gauge for the flows of                         *)
(* pc_mfd_cflow (the proofs of PDG_FLOW_METRIC_LOCAL, PDG_RF_VALUE and       *)
(* PDG_FLOW_TIME_DERIV with MCF_FLOW_DIFFEO, MCF_JOINT_SMOOTH and             *)
(* MCF_FLOW_DERIV for their mfl_hyp counterparts).                            *)
(* ========================================================================= *)

let P2BX46_MCF_METRIC_LOCAL = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (Y:real->A->real^N) J (Fe:A->real) s t
    (gm:A->real^N^N) c c' y.
        mcf_hyp top atlas Y J Fe /\ s IN J /\ t IN J /\ c IN atlas /\ c' IN atlas /\
        y IN IMAGE (SND c) (FST c) /\ mfl_flow top atlas Y s t (chart_inv c y) IN FST c'
        ==> metric_local atlas c
              (mfd_pullback_metric atlas atlas (mfl_flow top atlas Y s t) gm) y =
            mpullback (SND c' o mfl_flow top atlas Y s t o chart_inv c)
                      (metric_local atlas c' gm) y`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [mcf_hyp]) THEN
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
   [MATCH_MP_TAC MCF_FLOW_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `Fe:A->real`] THEN ASM_REWRITE_TAC[];
    DISCH_THEN(fun th -> REWRITE_TAC[th])]);;

let P2BX46_MCF_RF_VALUE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (Y:real->A->real^N) J (Fe:A->real) s0 t
    (gm:A->real^N^N) c0 c' x i j.
        mcf_hyp top atlas Y J Fe /\ s0 IN J /\ t IN J /\ riemannian_metric atlas gm /\
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
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [mcf_hyp]) THEN
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
   [MATCH_MP_TAC MCF_FLOW_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `Fe:A->real`] THEN ASM_REWRITE_TAC[];
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
                   `Y:real->A->real^N`; `J:real^1->bool`; `Fe:A->real`; `s0:real^1`; `t:real^1`;
                   `gm:A->real^N^N`; `c0:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`;
                   `SND (c0:(A->bool)#(A->real^N)) (x':A)`] P2BX46_MCF_METRIC_LOCAL) THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE]]);;

let P2BX46_MCF_TIME_DERIV = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (Y:real->A->real^N) J (Fe:A->real) s0 c c' s z.
        mcf_hyp top atlas Y J Fe /\ s0 IN J /\ c IN atlas /\ c' IN atlas /\
        pastecart s z IN {pastecart t y | t IN J /\ y IN IMAGE (SND c) (FST c) /\
                                         mfl_flow top atlas Y s0 t (chart_inv c y) IN FST c'}
        ==> frechet_derivative
              (\w. SND c' (mfl_flow top atlas Y s0 (fstcart w) (chart_inv c (sndcart w))))
              (at (pastecart s z)) (pastecart (lift(&1)) (vec 0)) =
            mfl_field atlas Y c'
              (pastecart s (SND c' (mfl_flow top atlas Y s0 s (chart_inv c z))))`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[IN_ELIM_PASTECART_THM] (last(CONJUNCTS th)))) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [mcf_hyp]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `Y:real->A->real^N`; `J:real^1->bool`; `Fe:A->real`;
                 `c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`; `s0:real^1`]
                MCF_JOINT_SMOOTH) THEN
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
  MATCH_MP_TAC MCF_FLOW_DERIV THEN
  MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `Fe:A->real`] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `z:real^N` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;


(* ========================================================================= *)
(* The soliton identity in charts: the Lie derivative of the                 *)
(* metric along grad F is twice the Hessian of F.                           *)
(* ========================================================================= *)

let P2BX46_LLIE_CGRAD = prove
 (`!U (G:real^N->real^N^N) cf y a b.
     metric_field U G /\ smooth_map_on U (\z. lift(cf z)) /\ y IN U
     ==> a dot (llie (\z. p3s_cgrad G cf z) G y ** b) = &2 * p3s_chess G cf y a b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `transp((G:real^N->real^N^N) y) = G y` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN
   `linear(frechet_derivative (\z. p3s_cgrad (G:real^N->real^N^N) cf z) (at y))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[P3S_CGRAD_SMOOTH];
    ALL_TAC] THEN
  REWRITE_TAC[llie; MATRIX_VECTOR_MUL_ADD_RDISTRIB; DOT_RADD;
              GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MATRIX_WORKS th]) THEN
  SUBGOAL_THEN
   `frechet_derivative (\z. p3s_cgrad (G:real^N->real^N^N) cf z) (at y) a dot (G y ** b) =
    b dot (G y ** frechet_derivative (\z. p3s_cgrad G cf z) (at y) a)`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM DOT_MATRIX_TRANSP_LMUL] THEN ASM_REWRITE_TAC[] THEN
    MATCH_ACCEPT_TAC DOT_SYM;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `cf:real^N->real`; `y:real^N`;
                 `a:real^N`; `b:real^N`] P3S_CGRAD_DERIV) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `cf:real^N->real`; `y:real^N`;
                 `b:real^N`; `a:real^N`] P3S_CGRAD_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[p3s_chess] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `cf:real^N->real`; `y:real^N`;
                 `a:real^N`; `b:real^N`] P3S_CDF_CHRISTOFFEL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `cf:real^N->real`; `y:real^N`; `a:real^N`; `b:real^N`]
    P3S_CD2F_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `a:real^N`;
                 `b:real^N`; `p3s_cgrad (G:real^N->real^N^N) cf y`] LRG_MDERIV_SYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `b:real^N`;
                 `a:real^N`; `p3s_cgrad (G:real^N->real^N^N) cf y`] LRG_MDERIV_SYM) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;


(* ========================================================================= *)
(* The time derivative of the pullback of a static metric                    *)
(* along a cflow flow (the generic part of PDG_GAUGE_RF_EQ).                 *)
(* ========================================================================= *)

let P2BX46_STATIC_TDERIV_ZERO = prove
 (`!U (Gp:real^N->real^N^N) (t:real^1) z.
     open U /\ z IN U /\ smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o Gp)
     ==> (matrify:real^(N,N)finite_prod->real^N^N)
           (frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                (\w:real^(1,N)finite_sum. Gp(sndcart w)))
              (at (pastecart t z)) (pastecart (lift(&1)) (vec 0))) = mat 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((vectorize:real^N^N->real^(N,N)finite_prod) o (Gp:real^N->real^N^N)) differentiable at (z:real^N)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o
                        (\w:real^(1,N)finite_sum. Gp(sndcart w))) (at (pastecart t z)) =
    frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o (Gp:real^N->real^N^N)) (at (z:real^N)) o sndcart`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    SUBGOAL_THEN
     `(vectorize:real^N^N->real^(N,N)finite_prod) o (\w:real^(1,N)finite_sum. Gp(sndcart w)) =
      (vectorize o Gp) o sndcart`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_SNDCART];
      REWRITE_TAC[SNDCART_PASTECART; GSYM FRECHET_DERIVATIVE_WORKS] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[o_THM; SNDCART_PASTECART] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_0 (MATCH_MP LINEAR_FRECHET_DERIVATIVE th)]) THEN
  REWRITE_TAC[MATRIFY_0]);;

let P2BX46_PULLBACK_STATIC_DERIV = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (X:real->A->real^N) J (Fe:A->real)
    (g:A->real^N^N) s0 t x i j.
     mcf_hyp top atlas X J Fe /\ riemannian_metric atlas g /\ s0 IN J /\ lift t IN J /\
     x IN topspace top /\ 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
     ==> ((\s. mfd_pullback_metric atlas atlas (mfl_flow top atlas X s0 (lift s)) g x$i$j)
          has_real_derivative
          (mpullback (SND (chart_at atlas (mfl_flow top atlas X s0 (lift t) x)) o
                      mfl_flow top atlas X s0 (lift t) o chart_inv (chart_at atlas x))
             (llie (\z. mfl_field atlas X (chart_at atlas (mfl_flow top atlas X s0 (lift t) x))
                          (pastecart (lift t) z))
                   (metric_local atlas (chart_at atlas (mfl_flow top atlas X s0 (lift t) x)) g))
             (SND (chart_at atlas x) x))$i$j) (atreal t)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mcf_hyp]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c0 = chart_at atlas (x:A):(A->bool)#(A->real^N)` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c0:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `x1 = mfl_flow top atlas (X:real->A->real^N) s0 (lift t) (x:A)` THEN
  SUBGOAL_THEN `(x1:A) IN topspace top` ASSUME_TAC THENL
   [EXPAND_TAC "x1" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `X:real->A->real^N`; `J:real^1->bool`; `Fe:A->real`; `s0:real^1`;
                   `lift t`; `x:A`] MCF_FLOW_CURVE_EXISTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x1:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c' = chart_at atlas (x1:A):(A->bool)#(A->real^N)` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c':(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `X:real->A->real^N`; `J:real^1->bool`; `Fe:A->real`;
                 `c0:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`; `s0:real^1`]
                MCF_JOINT_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `O1 = {pastecart r y | r IN J /\
                          y IN IMAGE (SND (c0:(A->bool)#(A->real^N))) (FST c0) /\
                          mfl_flow top atlas (X:real->A->real^N) s0 r (chart_inv c0 y) IN
                          FST (c':(A->bool)#(A->real^N))}` THEN
  ABBREV_TAC
   `Fm = \w:real^(1,N)finite_sum.
           SND (c':(A->bool)#(A->real^N))
             (mfl_flow top atlas (X:real->A->real^N) s0 (fstcart w)
                (chart_inv (c0:(A->bool)#(A->real^N)) (sndcart w)))` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `pastecart (lift t) (SND (c0:(A->bool)#(A->real^N)) x) IN O1` ASSUME_TAC THENL
   [EXPAND_TAC "O1" THEN REWRITE_TAC[IN_ELIM_PASTECART_THM] THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN `open ((J:real^1->bool) PCROSS IMAGE (SND (c':(A->bool)#(A->real^N))) (FST c'))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_PCROSS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND (c':(A->bool)#(A->real^N))) (FST c'))
                 (metric_local atlas c' (g:A->real^N^N))`
  ASSUME_TAC THENL [ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on ((J:real^1->bool) PCROSS IMAGE (SND (c':(A->bool)#(A->real^N))) (FST c'))
      ((vectorize:real^N^N->real^(N,N)finite_prod) o
       (\w:real^(1,N)finite_sum. metric_local atlas c' (g:A->real^N^N) (sndcart w)))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(vectorize:real^N^N->real^(N,N)finite_prod) o
      (\w:real^(1,N)finite_sum. metric_local atlas (c':(A->bool)#(A->real^N))
                                  (g:A->real^N^N) (sndcart w)) =
      (vectorize o metric_local atlas c' g) o sndcart`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `IMAGE (SND (c':(A->bool)#(A->real^N))) (FST c')` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
                  SNDCART_PASTECART] THEN SIMP_TAC[];
      MATCH_MP_TAC GEOL_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[LINEAR_SNDCART];
      ASM_MESON_TAC[metric_field]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`O1:real^(1,N)finite_sum->bool`;
    `(J:real^1->bool) PCROSS IMAGE (SND (c':(A->bool)#(A->real^N))) (FST c')`;
    `Fm:real^(1,N)finite_sum->real^N`;
    `mfl_field atlas (X:real->A->real^N) (c':(A->bool)#(A->real^N))`;
    `\w:real^(1,N)finite_sum. metric_local atlas (c':(A->bool)#(A->real^N))
                                (g:A->real^N^N) (sndcart w)`;
    `t:real`; `SND (c0:(A->bool)#(A->real^N)) x`; `i:num`; `j:num`]
   PDG_MPULLBACK_FLOW_DERIV) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`r:real^1`; `z:real^N`] THEN
      EXPAND_TAC "O1" THEN REWRITE_TAC[IN_ELIM_PASTECART_THM; PASTECART_IN_PCROSS] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "Fm" THEN
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
      MAP_EVERY X_GEN_TAC [`r:real^1`; `z:real^N`] THEN DISCH_TAC THEN
      EXPAND_TAC "Fm" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
      MATCH_MP_TAC P2BX46_MCF_TIME_DERIV THEN
      MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `Fe:A->real`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. (\z. (Fm:real^(1,N)finite_sum->real^N) (pastecart (lift s) z)) =
        SND (c':(A->bool)#(A->real^N)) o mfl_flow top atlas (X:real->A->real^N) s0 (lift s) o
        chart_inv (c0:(A->bool)#(A->real^N))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN EXPAND_TAC "Fm" THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART];
    ALL_TAC] THEN
  REWRITE_TAC[SNDCART_PASTECART; ETA_AX] THEN
  MATCH_MP_TAC PDG_DERIV_TRANSFER THEN CONJ_TAC THENL
   [MP_TAC(ISPEC `O1:real^(1,N)finite_sum->bool` OPEN_CONTAINS_BALL) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `pastecart (lift t) (SND (c0:(A->bool)#(A->real^N)) x)`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `pastecart (lift s) (SND (c0:(A->bool)#(A->real^N)) x) IN O1` MP_TAC THENL
     [UNDISCH_TAC `ball(pastecart (lift t) (SND (c0:(A->bool)#(A->real^N)) x),r) SUBSET O1` THEN
      REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[DIST_PASTECART_CANCEL; DIST_LIFT] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "O1" THEN REWRITE_TAC[IN_ELIM_PASTECART_THM] THEN STRIP_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `X:real->A->real^N`; `J:real^1->bool`; `Fe:A->real`; `s0:real^1`; `lift s`;
                   `g:A->real^N^N`; `c0:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`;
                   `SND (c0:(A->bool)#(A->real^N)) x`] P2BX46_MCF_METRIC_LOCAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    EXPAND_TAC "c0" THEN MATCH_MP_TAC METRIC_LOCAL_AT THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC PDG_MPULLBACK_AT THEN REWRITE_TAC[o_THM] THEN
    MP_TAC(ISPECL [`IMAGE (SND (c':(A->bool)#(A->real^N))) (FST c')`;
                   `metric_local atlas (c':(A->bool)#(A->real^N)) (g:A->real^N^N)`;
                   `lift t`;
                   `SND (c':(A->bool)#(A->real^N))
                      (mfl_flow top atlas (X:real->A->real^N) s0 (lift t)
                         (chart_inv (c0:(A->bool)#(A->real^N)) (SND c0 x)))`]
      P2BX46_STATIC_TDERIV_ZERO) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_SIMP_TAC[]; ASM_MESON_TAC[metric_field]];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MATRIX_ADD_LID]]]);;


(* ========================================================================= *)
(* Algebra of llie, and the soliton field's Lie derivative of                *)
(* the metric in a chart: the Lie derivative of G along grad F / abs t is *)
(* (G - 2 Ric) / abs t.                                                     *)
(* ========================================================================= *)

let P2BX46_LLIE_LOCAL = prove
 (`!U (X:real^N->real^N) X' (G:real^N->real^N^N) y.
     open U /\ y IN U /\ (!z. z IN U ==> X z = X' z) /\ X differentiable at y
     ==> llie X G y = llie X' G y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[llie] THEN
  SUBGOAL_THEN `(X:real^N->real^N) y = X' y` SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `frechet_derivative (X:real^N->real^N) (at y) = frechet_derivative X' (at y)`
  (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `X:real^N->real^N` THEN
  MP_TAC(ISPEC `U:real^N->bool` OPEN_CONTAINS_BALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
  X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `ball(y:real^N,d) SUBSET U` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[DIST_SYM]);;

let P2BX46_LLIE_CMUL = prove
 (`!(X:real^N->real^N) (G:real^N->real^N^N) c y.
     X differentiable at y /\
     ((vectorize:real^N^N->real^(N,N)finite_prod) o G) differentiable at y
     ==> llie (\z. c % X z) G y = c %% llie X G y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[llie; mderiv] THEN
  SUBGOAL_THEN `frechet_derivative (\z. c % (X:real^N->real^N) z) (at y) =
                (\h. c % frechet_derivative X (at y) h)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN
    ASM_REWRITE_TAC[ETA_AX; GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `linear(frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o (G:real^N->real^N^N)) (at (y:real^N)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `linear(frechet_derivative (X:real^N->real^N) (at (y:real^N)))` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[LINEAR_CMUL; MATRIFY_CMUL; MATRIX_CMUL_ADD_LDISTRIB] THEN
  REWRITE_TAC[MATCH_MP MATRIX_CMUL
    (ASSUME `linear (frechet_derivative (X:real^N->real^N) (at (y:real^N)))`)] THEN
  REWRITE_TAC[TRANSP_MATRIX_CMUL; MATRIX_MUL_LMUL; MATRIX_MUL_RMUL]);;

(* The Hessian p3s_chess is the lnabla Hessian of rfa_sh_df, with the two    *)
(* arguments exchanged.                                                      *)

let P2BX46_CHESS_LNABLA = prove
 (`!(G:real^N->real^N^N) cf y a b.
     p3s_chess G cf y a b = lnabla 1 G (rfa_sh_df cf) y (\m. if m = 1 then b else a)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[p3s_chess; p3s_cd2f; p3s_cdf; lnabla; rfa_sh_df; SUM_SING_NUMSEG] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[LIFT_DROP; ETA_AX]);;

(* On a shrinker, in any chart: the Lie derivative of G along grad F is   *)
(* G - 2 Ric (as matrices).                                                  *)

let P2BX46_LLIE_SOLITON = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f c y.
     p2b_shrinker (top,atlas) g f /\ c IN atlas /\ y IN IMAGE (SND c) (FST c)
     ==> llie (\z. p3s_cgrad (metric_local atlas c g) (\w. f(chart_inv c w)) z)
              (metric_local atlas c g) y =
         metric_local atlas c g y - &2 %% pde_lricci_matrix (metric_local atlas c g) y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `f:A->real`; `c:(A->bool)#(A->real^N)`] RFA_SH_CHART_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `G = metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)` THEN
  ABBREV_TAC `F0 = \w. (f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) w)` THEN
  REWRITE_TAC[MATRIX_EQ] THEN X_GEN_TAC `b:real^N` THEN
  REWRITE_TAC[GSYM VECTOR_EQ_LDOT] THEN X_GEN_TAC `a:real^N` THEN
  MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`; `G:real^N->real^N^N`;
                 `F0:real^N->real`; `y:real^N`; `a:real^N`; `b:real^N`] P2BX46_LLIE_CGRAD) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "F0" THEN EXPAND_TAC "G" THEN ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[P2BX46_CHESS_LNABLA] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^N`; `\m:num. if m = 1 then b else a:real^N`] o
    REWRITE_RULE[rfa_eqon] o
    check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "rfa_eqon"
                                               with Failure _ -> false)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[lmetric2; lric2] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB; MATRIX_VECTOR_LMUL; DOT_RSUB; DOT_RMUL] THEN
  MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`; `G:real^N->real^N^N`;
                 `y:real^N`; `a:real^N`; `b:real^N`] PDE_LRICCI_MATRIX_DOT) THEN
  MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`; `G:real^N->real^N^N`;
                 `y:real^N`; `a:real^N`; `b:real^N`] LRICCI_SYM) THEN
  SUBGOAL_THEN `transp((G:real^N->real^N^N) y) = G y` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `b dot ((G:real^N->real^N^N) y ** a) = a dot (G y ** b)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [DOT_SYM] THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o LAND_CONV) [GSYM th]) THEN
    REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;


(* ========================================================================= *)
(* The soliton flow G(t) = |t| phi_t^* g, t < 0, with phi_t the              *)
(* flow of grad f / |t| from time -1 (MT (9.19)), and its Ricci flow         *)
(* equation in preferred coordinates.                                        *)
(* ========================================================================= *)

let p2bx46_solX = new_definition
 `p2bx46_solX (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (f:A->real) =
    \t x. inv(abs t) % p2bx46_gradf atlas g f x`;;

let p2bx46_G = new_definition
 `p2bx46_G (top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
           (f:A->real) =
    \t x. abs t %% mfd_pullback_metric atlas atlas
                    (mfl_flow top atlas (p2bx46_solX atlas g f) (lift(--(&1))) (lift t)) g x`;;

(* The Lie derivative of the metric along the soliton field at time t < 0,  *)
(* in a chart.                                                                *)

let P2BX46_LLIE_SOLFIELD = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f c t y.
     p2b_shrinker (top,atlas) g f /\ c IN atlas /\ y IN IMAGE (SND c) (FST c)
     ==> llie (\z. mfl_field atlas (p2bx46_solX atlas g f) c (pastecart (lift t) z))
              (metric_local atlas c g) y =
         inv(abs t) %%
         (metric_local atlas c g y - &2 %% pde_lricci_matrix (metric_local atlas c g) y)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `f:A->real`; `c:(A->bool)#(A->real^N)`] RFA_SH_CHART_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `(\z. p3s_cgrad (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))
                   (\w. (f:A->real)(chart_inv c w)) z) differentiable at y /\
    ((vectorize:real^N^N->real^(N,N)finite_prod) o metric_local atlas c g) differentiable at y`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC P3S_CGRAD_SMOOTH THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[metric_field]];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `llie (\z. inv(abs t) % p3s_cgrad (metric_local atlas (c:(A->bool)#(A->real^N))
                                       (g:A->real^N^N)) (\w. (f:A->real)(chart_inv c w)) z)
         (metric_local atlas c g) y` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2BX46_LLIE_LOCAL THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[MFL_FIELD_PASTECART; LIFT_DROP; p2bx46_solX] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `\x:A. inv(abs t)`; `p2bx46_gradf atlas (g:A->real^N^N) f`;
                     `c:(A->bool)#(A->real^N)`; `z:real^N`] MCF_VREP_CMUL) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `f:A->real`; `c:(A->bool)#(A->real^N)`; `z:real^N`]
        P2BX46_GRADF_VREP) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN REFL_TAC;
      MATCH_MP_TAC DIFFERENTIABLE_CMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z. p3s_cgrad (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))
                                (\w. (f:A->real)(chart_inv c w)) z`;
                 `metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)`;
                 `inv(abs t)`; `y:real^N`] P2BX46_LLIE_CMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC P2BX46_LLIE_SOLITON THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]);;

(* d/dt G(t) = -2 Ric(G(t)) in preferred coordinates, t < 0. *)

let P2BX46_SOL_TDERIV = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f K t x i j.
     hausdorff_space top /\ connected_space top /\ p2b_shrinker (top,atlas) g f /\
     mfd_complete (top,atlas) g /\ &0 <= K /\
     (!x. x IN topspace top ==> &0 <= mfd_scalar atlas g x) /\
     (!y w. y IN topspace top ==> &0 <= mfd_ricci atlas g y w w) /\
     (!y w. y IN topspace top
            ==> mfd_ricci atlas g y w w <= &(dimindex(:N) - 1) * K * (w dot (g y ** w))) /\
     t < &0 /\ x IN topspace top /\
     1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
     ==> ((\s. p2bx46_G top atlas g f s x$i$j) has_real_derivative
          (--(&2) * mfd_ricci_matrix atlas (p2bx46_G top atlas g f t) x$i$j)) (atreal t)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  SUBGOAL_THEN `mcf_hyp top atlas (p2bx46_solX atlas (g:A->real^N^N) f)
                        {t:real^1 | drop t < &0} (f:A->real)` ASSUME_TAC THENL
   [REWRITE_TAC[p2bx46_solX] THEN MATCH_MP_TAC P2BX46_SOL_MCF_HYP THEN
    EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `X = p2bx46_solX atlas (g:A->real^N^N) f` THEN
  ABBREV_TAC `J = {t:real^1 | drop t < &0}` THEN
  SUBGOAL_THEN `lift(--(&1)) IN J /\ lift t IN J` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN REWRITE_TAC[IN_ELIM_THM; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `phi = mfl_flow top atlas (X:real->A->real^N) (lift(--(&1))) (lift t)` THEN
  SUBGOAL_THEN
   `mfd_diffeo top atlas (topspace top) top atlas (topspace top) phi
      (mfl_flow top atlas (X:real->A->real^N) (lift t) (lift(--(&1))))`
  ASSUME_TAC THENL
   [EXPAND_TAC "phi" THEN MATCH_MP_TAC MCF_FLOW_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `f:A->real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas (mfd_pullback_metric atlas atlas phi (g:A->real^N^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RIEMANNIAN_METRIC_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `top:A topology`;
                          `mfl_flow top atlas (X:real->A->real^N) (lift t) (lift(--(&1)))`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2bx46_G] THEN ASM_REWRITE_TAC[MATRIX_CMUL_COMPONENT] THEN
  SUBGOAL_THEN
   `mfd_ricci_matrix atlas
      (\x. abs t %% mfd_pullback_metric atlas atlas phi (g:A->real^N^N) x) x$i$j =
    mfd_ricci atlas (mfd_pullback_metric atlas atlas phi g) (x:A) (basis i) (basis j)`
  SUBST1_TAC THENL
   [REWRITE_TAC[mfd_ricci_matrix] THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `mfd_pullback_metric atlas atlas phi (g:A->real^N^N)`; `abs t`; `x:A`]
      RFB_MFD_RICCI_CMUL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `X:real->A->real^N`; `J:real^1->bool`; `f:A->real`; `g:A->real^N^N`;
                 `lift(--(&1))`; `t:real`; `x:A`; `i:num`; `j:num`]
    P2BX46_PULLBACK_STATIC_DERIV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]] THEN
  ABBREV_TAC `c0 = chart_at atlas (x:A):(A->bool)#(A->real^N)` THEN
  ABBREV_TAC `x1 = (phi:A->A) x` THEN
  ABBREV_TAC `c' = chart_at atlas (x1:A):(A->bool)#(A->real^N)` THEN
  SUBGOAL_THEN `(c0:(A->bool)#(A->real^N)) IN atlas /\ x IN FST c0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c0" THEN ASM_MESON_TAC[CHART_AT]; ALL_TAC] THEN
  SUBGOAL_THEN `(x1:A) IN topspace top` ASSUME_TAC THENL
   [EXPAND_TAC "x1" THEN EXPAND_TAC "phi" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `X:real->A->real^N`; `J:real^1->bool`; `f:A->real`; `lift(--(&1))`;
                   `lift t`; `x:A`] MCF_FLOW_CURVE_EXISTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c':(A->bool)#(A->real^N)) IN atlas /\ x1 IN FST c'` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c'" THEN ASM_MESON_TAC[CHART_AT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c0:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `(SND (c':(A->bool)#(A->real^N)) o (phi:A->A) o chart_inv (c0:(A->bool)#(A->real^N)))
      (SND c0 x) = SND c' (x1:A)`
  ASSUME_TAC THENL [REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `h = SND (c':(A->bool)#(A->real^N)) o (phi:A->A) o
                  chart_inv (c0:(A->bool)#(A->real^N))` THEN
  SUBGOAL_THEN
   `mpullback h (llie (\z. mfl_field atlas (X:real->A->real^N) (c':(A->bool)#(A->real^N))
                             (pastecart (lift t) z))
                     (metric_local atlas c' (g:A->real^N^N)))
              (SND (c0:(A->bool)#(A->real^N)) x) =
    inv(abs t) %%
    (mpullback h (metric_local atlas c' g) (SND c0 x) -
     &2 %% (transp(matrix(frechet_derivative h (at (SND c0 x)))) **
            pde_lricci_matrix (metric_local atlas c' g) (h(SND c0 x)) **
            matrix(frechet_derivative h (at (SND c0 x)))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[mpullback] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `f:A->real`; `c':(A->bool)#(A->real^N)`; `t:real`;
                   `SND (c':(A->bool)#(A->real^N)) (x1:A)`] P2BX46_LLIE_SOLFIELD) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
    EXPAND_TAC "X" THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[MATRIX_MUL_LMUL; MATRIX_MUL_RMUL; MATRIX_SUB_LDISTRIB; MATRIX_SUB_RDISTRIB;
                MATRIX_CMUL_SUB_LDISTRIB];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_CMUL_COMPONENT; MATRIX_SUB_COMPONENT] THEN
  SUBGOAL_THEN
   `mpullback h (metric_local atlas (c':(A->bool)#(A->real^N)) (g:A->real^N^N))
              (SND (c0:(A->bool)#(A->real^N)) x) =
    mfd_pullback_metric atlas atlas (phi:A->A) g x`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `X:real->A->real^N`; `J:real^1->bool`; `f:A->real`; `lift(--(&1))`;
                   `lift t`; `g:A->real^N^N`; `c0:(A->bool)#(A->real^N)`;
                   `c':(A->bool)#(A->real^N)`; `SND (c0:(A->bool)#(A->real^N)) x`]
      P2BX46_MCF_METRIC_LOCAL) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ASM_REWRITE_TAC[]] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    EXPAND_TAC "c0" THEN MATCH_MP_TAC METRIC_LOCAL_AT THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(transp(matrix(frechet_derivative h (at (SND (c0:(A->bool)#(A->real^N)) x)))) **
     pde_lricci_matrix (metric_local atlas (c':(A->bool)#(A->real^N)) (g:A->real^N^N))
       (h(SND c0 x)) **
     matrix(frechet_derivative h (at (SND c0 x))))$i$j =
    mfd_ricci atlas (mfd_pullback_metric atlas atlas (phi:A->A) g) x (basis i) (basis j)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `X:real->A->real^N`; `J:real^1->bool`; `f:A->real`; `lift(--(&1))`;
                   `lift t`; `g:A->real^N^N`; `c0:(A->bool)#(A->real^N)`;
                   `c':(A->bool)#(A->real^N)`; `x:A`; `i:num`; `j:num`] P2BX46_MCF_RF_VALUE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]] THEN
    DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "c0" THEN REWRITE_TAC[mfd_ricci];
    ALL_TAC] THEN
  ABBREV_TAC `Pt = mfd_pullback_metric atlas atlas (phi:A->A) (g:A->real^N^N) x$i$j` THEN
  ABBREV_TAC `R = mfd_ricci atlas (mfd_pullback_metric atlas atlas (phi:A->A) (g:A->real^N^N))
                    x (basis i) (basis j)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `((\s. --s * mfd_pullback_metric atlas atlas
                  (mfl_flow top atlas (X:real->A->real^N) (lift(--(&1))) (lift s))
                  (g:A->real^N^N) x$i$j) has_real_derivative
     (--t * (inv(abs t) * (Pt - &2 * R)) + --(&1) * Pt)) (atreal t)`
  MP_TAC THENL
   [MP_TAC(ISPECL [`\s:real. --s`; `--(&1)`;
                   `\s. mfd_pullback_metric atlas atlas
                          (mfl_flow top atlas (X:real->A->real^N) (lift(--(&1))) (lift s))
                          (g:A->real^N^N) x$i$j`;
                   `inv(abs t) * (Pt - &2 * R)`; `t:real`] HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REAL_DIFF_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC PDG_DERIV_TRANSFER THEN CONJ_TAC THENL
   [EXISTS_TAC `--t` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `--t * inv(abs t) = &1` MP_TAC THENL
     [SUBGOAL_THEN `abs t = --t` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONV_TAC REAL_RING]);;


(* ========================================================================= *)
(* G is jointly smooth in charts and is a Ricci flow on every                *)
(* (a,0), a < 0.                                                              *)
(* ========================================================================= *)

let P2BX46_SOL_JOINT_SMOOTH = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f K c.
     hausdorff_space top /\ connected_space top /\ p2b_shrinker (top,atlas) g f /\
     mfd_complete (top,atlas) g /\ &0 <= K /\
     (!x. x IN topspace top ==> &0 <= mfd_scalar atlas g x) /\
     (!y w. y IN topspace top ==> &0 <= mfd_ricci atlas g y w w) /\
     (!y w. y IN topspace top
            ==> mfd_ricci atlas g y w w <= &(dimindex(:N) - 1) * K * (w dot (g y ** w))) /\
     c IN atlas
     ==> smooth_map_on ({t:real^1 | drop t < &0} PCROSS IMAGE (SND c) (FST c))
           (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                  (metric_local atlas c (p2bx46_G top atlas g f (drop(fstcart z))) (sndcart z)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  SUBGOAL_THEN `mcf_hyp top atlas (p2bx46_solX atlas (g:A->real^N^N) f)
                        {t:real^1 | drop t < &0} (f:A->real)` ASSUME_TAC THENL
   [REWRITE_TAC[p2bx46_solX] THEN MATCH_MP_TAC P2BX46_SOL_MCF_HYP THEN
    EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `X = p2bx46_solX atlas (g:A->real^N^N) f` THEN
  ABBREV_TAC `J = {t:real^1 | drop t < &0}` THEN
  SUBGOAL_THEN `open(J:real^1->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN REWRITE_TAC[drop; OPEN_HALFSPACE_COMPONENT_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `lift(--(&1)) IN J` ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN REWRITE_TAC[IN_ELIM_THM; LIFT_DROP] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[OPEN_PCROSS]; ALL_TAC] THEN
  REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
  MAP_EVERY X_GEN_TAC [`t0:real^1`; `y0:real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `y0:real^N`] MCF_CHART_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `x1 = mfl_flow top atlas (X:real->A->real^N) (lift(--(&1))) t0
                     (chart_inv (c:(A->bool)#(A->real^N)) y0)` THEN
  SUBGOAL_THEN `(x1:A) IN topspace top` ASSUME_TAC THENL
   [EXPAND_TAC "x1" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `X:real->A->real^N`; `J:real^1->bool`; `f:A->real`; `lift(--(&1))`;
                   `t0:real^1`; `chart_inv (c:(A->bool)#(A->real^N)) y0`]
      MCF_FLOW_CURVE_EXISTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `c' = chart_at atlas (x1:A):(A->bool)#(A->real^N)` THEN
  SUBGOAL_THEN `(c':(A->bool)#(A->real^N)) IN atlas /\ x1 IN FST c'` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c'" THEN ASM_MESON_TAC[CHART_AT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c':(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `X:real->A->real^N`; `J:real^1->bool`; `f:A->real`;
                 `c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`; `lift(--(&1))`]
                MCF_JOINT_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `O1 = {pastecart r y | r IN J /\
                          y IN IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c) /\
                          mfl_flow top atlas (X:real->A->real^N) (lift(--(&1))) r
                            (chart_inv c y) IN FST (c':(A->bool)#(A->real^N))}` THEN
  ABBREV_TAC
   `Fm = \w:real^(1,N)finite_sum.
           SND (c':(A->bool)#(A->real^N))
             (mfl_flow top atlas (X:real->A->real^N) (lift(--(&1))) (fstcart w)
                (chart_inv (c:(A->bool)#(A->real^N)) (sndcart w)))` THEN
  STRIP_TAC THEN
  EXISTS_TAC `O1:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [EXPAND_TAC "O1" THEN REWRITE_TAC[IN_ELIM_PASTECART_THM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `GG = \w:real^(1,N)finite_sum. (vectorize:real^N^N->real^(N,N)finite_prod)
           (metric_local atlas (c':(A->bool)#(A->real^N)) (g:A->real^N^N) (sndcart w))` THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC
   `\w:real^(1,N)finite_sum.
      drop(lift(--drop(fstcart w))) %
      (vectorize:real^N^N->real^(N,N)finite_prod)
        (mpullback (\z. (Fm:real^(1,N)finite_sum->real^N) (pastecart (fstcart w) z))
           (\z. (matrify:real^(N,N)finite_prod->real^N^N)
                  ((GG:real^(1,N)finite_sum->real^(N,N)finite_prod) (pastecart (fstcart w) z)))
           (sndcart w))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FORALL_PASTECART] THEN MAP_EVERY X_GEN_TAC [`r:real^1`; `y:real^N`] THEN
    EXPAND_TAC "O1" THEN
    REWRITE_TAC[IN_ELIM_PASTECART_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    STRIP_TAC THEN EXPAND_TAC "GG" THEN
    REWRITE_TAC[SNDCART_PASTECART; MATRIFY_VECTORIZE; ETA_AX] THEN
    REWRITE_TAC[p2bx46_G; METRIC_LOCAL_CMUL; VECTORIZE_CMUL; LIFT_DROP] THEN
    REWRITE_TAC[ETA_AX] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `abs(drop r) = --drop r` SUBST1_TAC THENL
     [UNDISCH_TAC `(r:real^1) IN J` THEN EXPAND_TAC "J" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN
     `(\z. (Fm:real^(1,N)finite_sum->real^N) (pastecart r z)) =
      SND (c':(A->bool)#(A->real^N)) o
      mfl_flow top atlas (X:real->A->real^N) (lift(--(&1))) r o
      chart_inv (c:(A->bool)#(A->real^N))`
    SUBST1_TAC THENL
     [EXPAND_TAC "Fm" THEN REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART];
      ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2BX46_MCF_METRIC_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `f:A->real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC GEOL_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[linear; FSTCART_ADD; FSTCART_CMUL; DROP_ADD; DROP_CMUL; LIFT_ADD;
                LIFT_CMUL; LIFT_NEG] THEN
    CONJ_TAC THEN REPEAT GEN_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC PDG_MPULLBACK_SMOOTH_TD THEN
  EXISTS_TAC `(J:real^1->bool) PCROSS IMAGE (SND (c':(A->bool)#(A->real^N))) (FST c')` THEN
  ASM_SIMP_TAC[OPEN_PCROSS] THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `(GG:real^(1,N)finite_sum->real^(N,N)finite_prod) =
      ((vectorize:real^N^N->real^(N,N)finite_prod) o
       metric_local atlas (c':(A->bool)#(A->real^N)) (g:A->real^N^N)) o
      (sndcart:real^(1,N)finite_sum->real^N)`
    SUBST1_TAC THENL
     [EXPAND_TAC "GG" THEN REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `IMAGE (SND (c':(A->bool)#(A->real^N))) (FST c')` THEN
    ASM_SIMP_TAC[OPEN_PCROSS] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
                  SNDCART_PASTECART] THEN SIMP_TAC[];
      MATCH_MP_TAC GEOL_SMOOTH_LINEAR THEN ASM_SIMP_TAC[OPEN_PCROSS; LINEAR_SNDCART];
      ASM_MESON_TAC[riemannian_metric; metric_field]];
    REWRITE_TAC[FORALL_PASTECART; FSTCART_PASTECART; PASTECART_IN_PCROSS] THEN
    MAP_EVERY X_GEN_TAC [`r:real^1`; `y:real^N`] THEN EXPAND_TAC "O1" THEN
    REWRITE_TAC[IN_ELIM_PASTECART_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "Fm" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]);;

(* G is a Ricci flow on every (a,0). *)

let P2BX46_SOL_RICCI_FLOW = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f K a.
     hausdorff_space top /\ connected_space top /\ p2b_shrinker (top,atlas) g f /\
     mfd_complete (top,atlas) g /\ &0 <= K /\
     (!x. x IN topspace top ==> &0 <= mfd_scalar atlas g x) /\
     (!y w. y IN topspace top ==> &0 <= mfd_ricci atlas g y w w) /\
     (!y w. y IN topspace top
            ==> mfd_ricci atlas g y w w <= &(dimindex(:N) - 1) * K * (w dot (g y ** w))) /\
     a < &0
     ==> ricci_flow_on (top,atlas) a (&0) (p2bx46_G top atlas g f)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  SUBGOAL_THEN `mcf_hyp top atlas (p2bx46_solX atlas (g:A->real^N^N) f)
                        {t:real^1 | drop t < &0} (f:A->real)` ASSUME_TAC THENL
   [REWRITE_TAC[p2bx46_solX] THEN MATCH_MP_TAC P2BX46_SOL_MCF_HYP THEN
    EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[ricci_flow_on] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN REWRITE_TAC[p2bx46_G] THEN
    MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC RIEMANNIAN_METRIC_PULLBACK THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `top:A topology`;
      `mfl_flow top atlas (p2bx46_solX atlas (g:A->real^N^N) f) (lift t) (lift(--(&1)))`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MCF_FLOW_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`{t:real^1 | drop t < &0}`; `f:A->real`] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `{t:real^1 | drop t < &0} PCROSS IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL] THEN
      REWRITE_TAC[SUBSET; IN_INTERVAL_1; IN_ELIM_THM; LIFT_DROP] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[o_DEF] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `f:A->real`; `K:real`; `c:(A->bool)#(A->real^N)`] P2BX46_SOL_JOINT_SMOOTH) THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BX46_SOL_TDERIV THEN EXISTS_TAC `K:real` THEN
    ASM_REWRITE_TAC[]]);;

