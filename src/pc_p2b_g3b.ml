(* ========================================================================= *)
(* Unit pc_p2b_g3b: local facts on the chart boxes of the limit for the weak *)
(* equation of G3 (MT Prop 9.20, Section 2.6): the subsolution property of   *)
(* U = t^(-3/2) e^(-linf) (P2BW_LIMIT on the cdata of G1), the evolution     *)
(* of the chart density, the monotonicity of t^2 linf and the resulting      *)
(* lower bound of the time derivative of linf, and the properness of linf    *)
(* (Gaussian lower bound in the limit).                                      *)
(* ========================================================================= *)

needs "src/pc_p2b_g3a.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The subsolution property on chart boxes; directional derivatives; the     *)
(* evolution of the chart density.                                           *)
(* ========================================================================= *)

let P2BX_CDATA_CSUB = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau (top':B topology) atlas' g'
    phi c om ix linf.
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     (!a. a < &1 ==> ricci_flow_on (top',atlas') a (&1) g') /\ c IN atlas' /\
     p2bg_cbox c om /\
     p2bg_cdata (top,atlas) g p tau atlas' g' phi c om ix linf
     ==> p2bw_csub om
           (\z. sqrt(det(p2bw_cmet atlas' c (&1) g' z)) %% matrix_inv(p2bw_cmet atlas' c (&1) g' z))
           (\z. sqrt(det(p2bw_cmet atlas' c (&1) g' z)))
           (p2bw_cscal atlas' c (&1) g')
           (p2bw_uof (p2bw_cfun c linf))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(om:real^(3,1)finite_sum->bool) /\ bounded om /\
                om SUBSET {z | fstcart z IN IMAGE (SND c) (FST (c:(B->bool)#(B->real^3))) /\
                               &0 < drop(sndcart z)}`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2bg_cbox (c:(B->bool)#(B->real^3)) om` THEN
    REWRITE_TAC[p2bg_cbox] THEN MESON_TAC[CLOSURE_SUBSET; SUBSET_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^(3,1)finite_sum. z IN om ==> &0 < drop(sndcart z)` ASSUME_TAC THENL
   [UNDISCH_TAC `om SUBSET {z | fstcart z IN IMAGE (SND c) (FST (c:(B->bool)#(B->real^3))) /\
                               &0 < drop(sndcart z)}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `c:(B->bool)#(B->real^3)`;
                 `om:real^(3,1)finite_sum->bool`] P2BX_LIMIT_CHART_DATA) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `p2bg_cdata (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                (g:real->A->real^3^3) (p:A) (tau:num->real)
                (atlas':((B->bool)#(B->real^3))->bool) (g':real->B->real^3^3)
                (phi:num->B->A) (c:(B->bool)#(B->real^3)) (om:real^(3,1)finite_sum->bool)
                (ix:num->num) (linf:real->B->real)` THEN
  REWRITE_TAC[p2bg_cdata; FORALL_AND_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`om:real^(3,1)finite_sum->bool`;
                 `p2bg_smet (atlas:((A->bool)#(A->real^3))->bool) g tau (phi:num->B->A) c ix`;
                 `p2bw_cmet (atlas':((B->bool)#(B->real^3))->bool) c (&1) g'`]
     (REWRITE_RULE[P2BW_COEFF_BRIDGE_STATEMENT] (ISPEC `(:3)` P2BW_COEFF_BRIDGE))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON o
      check (fun th -> can (find_term ((=) `vectorize:real^3^3->real^(3,3)finite_prod`))
                           (concl th) && is_comb(concl th) &&
                       fst(dest_const(fst(strip_comb(concl th)))) = "smooth_map_on")) THEN
    REWRITE_TAC[o_DEF];
    STRIP_TAC] THEN
  MP_TAC(ISPECL
    [`om:real^(3,1)finite_sum->bool`;
     `\m z. sqrt(det(p2bg_smet (atlas:((A->bool)#(A->real^3))->bool) g tau
                               (phi:num->B->A) c ix m z)) %%
            matrix_inv(p2bg_smet atlas g tau phi c ix m z)`;
     `\m z. sqrt(det(p2bg_smet (atlas:((A->bool)#(A->real^3))->bool) g tau
                               (phi:num->B->A) c ix m z))`;
     `p2bg_sscal (atlas:((A->bool)#(A->real^3))->bool) g tau (phi:num->B->A) c ix`;
     `p2bg_sfun (top:A topology,atlas:((A->bool)#(A->real^3))->bool) g p tau
                (phi:num->B->A) c ix`;
     `\z. sqrt(det(p2bw_cmet (atlas':((B->bool)#(B->real^3))->bool) c (&1) g' z)) %%
          matrix_inv(p2bw_cmet atlas' c (&1) g' z)`;
     `\z. sqrt(det(p2bw_cmet (atlas':((B->bool)#(B->real^3))->bool) c (&1) g' z))`;
     `p2bw_cscal (atlas':((B->bool)#(B->real^3))->bool) c (&1) g'`;
     `p2bw_cfun (c:(B->bool)#(B->real^3)) (linf:real->B->real)`]
    (REWRITE_RULE[P2BW_LIMIT_STATEMENT] (ISPEC `(:3)` P2BW_LIMIT))) THEN
  BETA_TAC THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `smooth_map_on om (\z. lift(p2bw_cscal atlas' c (&1) (g':real->B->real^3^3) z))` THEN
    SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    SIMP_TAC[]]);;

(* The subsolution property on every chart box of the limit. *)

let P2BX_BOX_CSUB = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf c om.
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     c IN atlas' /\ p2bg_cbox c om
     ==> wan_loclip om (p2bw_cfun c linf) /\
         p2bw_csub om
           (\z. sqrt(det(p2bw_cmet atlas' c (&1) g' z)) %% matrix_inv(p2bw_cmet atlas' c (&1) g' z))
           (\z. sqrt(det(p2bw_cmet atlas' c (&1) g' z)))
           (p2bw_cscal atlas' c (&1) g')
           (p2bw_uof (p2bw_cfun c linf))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_LIMIT) THEN
  SUBGOAL_THEN
   `?m0. p2bg_cdata (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
           (g:real->A->real^3^3) (p:A) (tau:num->real)
           (atlas':((B->bool)#(B->real^3))->bool) (g':real->B->real^3^3)
           (phi:num->B->A) (c:(B->bool)#(B->real^3)) (om:real^(3,1)finite_sum->bool)
           (\j. (sub:num->num)(m0 + j)) (linf:real->B->real)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2bg_g1out (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                   (g:real->A->real^3^3) (p:A) (tau:num->real)
                   (top':B topology,atlas':((B->bool)#(B->real^3))->bool)
                   (g':real->B->real^3^3) (W:num->B->bool) (phi:num->B->A)
                   (sub:num->num) (linf:real->B->real)` THEN
    REWRITE_TAC[p2bg_g1out] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `top':B topology`;
                   `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`;
                   `phi:num->B->A`; `c:(B->bool)#(B->real^3)`;
                   `om:real^(3,1)finite_sum->bool`; `\j. (sub:num->num)(m0 + j)`;
                   `linf:real->B->real`] P2BX_CDATA_LIMIT) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    MATCH_MP_TAC P2BX_CDATA_CSUB THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `top':B topology`;
                          `phi:num->B->A`; `\j. (sub:num->num)(m0 + j)`] THEN
    ASM_REWRITE_TAC[]]);;

(* Directional derivatives of differentiable functions. *)

let P2BX_DIRDERIV = prove
 (`!(f:real^M->real) z v.
     (\w. lift(f w)) differentiable at z
     ==> ((\h. f(z + h % v)) has_real_derivative
          drop(frechet_derivative (\w. lift(f w)) (at z) v)) (atreal (&0))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FRECHET_DERIVATIVE_WORKS]) THEN
  ABBREV_TAC `f' = frechet_derivative (\w. lift((f:real^M->real) w)) (at z)` THEN
  DISCH_TAC THEN
  REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT] THEN
  SUBGOAL_THEN `lift o (\h. (f:real^M->real)(z + h % v)) o drop =
                (\w. lift(f w)) o (\x:real^1. z + drop x % v)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `(\x:real^1. drop((f':real^M->real^1) v) % x) =
                (f':real^M->real^1) o (\x:real^1. drop x % v)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `x:real^1` THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
    REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(\x:real^1. drop x % (v:real^M)) = (\h. vec 0 + drop h % v)` SUBST1_TAC THENL
     [REWRITE_TAC[VECTOR_ADD_LID]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
    REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN CONJ_TAC THEN VECTOR_ARITH_TAC;
    REWRITE_TAC[LIFT_DROP; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The chart density evolves by d/dtau rho = R rho along the backward time   *)
(* of the limit flow.                                                        *)
(* ========================================================================= *)

let P2BX_BOX_RHO_TDER = prove
 (`!(top':B topology) atlas' (g':real->B->real^3^3) c z.
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     (!a. a < &1 ==> ricci_flow_on (top',atlas') a (&1) g') /\ c IN atlas' /\
     fstcart z IN IMAGE (SND c) (FST c) /\ &0 < drop(sndcart z)
     ==> (\w. lift(sqrt(det(p2bw_cmet atlas' c (&1) g' w)))) differentiable at z /\
         wan_tder (\w. sqrt(det(p2bw_cmet atlas' c (&1) g' w))) z =
         p2bw_cscal atlas' c (&1) g' z * sqrt(det(p2bw_cmet atlas' c (&1) g' z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^3))->bool)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `&0` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "ricci_flow_on")) (concl th))) THEN
    REWRITE_TAC[REAL_LT_01; ricci_flow_on] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(B->bool)#(B->real^3)`; `z:real^(3,1)finite_sum`] P2BX_CBOX_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `g':real->B->real^3^3`; `c:(B->bool)#(B->real^3)`;
                 `ball(z:real^(3,1)finite_sum,r)`] P2BX_LIMIT_CHART_DATA) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[BOUNDED_BALL] THEN
    UNDISCH_TAC `p2bg_cbox (c:(B->bool)#(B->real^3)) (ball(z:real^(3,1)finite_sum,r))` THEN
    REWRITE_TAC[p2bg_cbox] THEN MESON_TAC[CLOSURE_SUBSET; SUBSET_TRANS];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`ball(z:real^(3,1)finite_sum,r)`;
                 `p2bw_cmet (atlas':((B->bool)#(B->real^3))->bool) c (&1) g'`]
                P2BW_SQRTDET_SMOOTH) THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(\w. lift(sqrt(det(p2bw_cmet atlas' c (&1) (g':real->B->real^3^3) w))))
                differentiable at z` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `ball(z:real^(3,1)finite_sum,r)` THEN ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\w. sqrt(det(p2bw_cmet atlas' c (&1) (g':real->B->real^3^3) w))`;
                 `z:real^(3,1)finite_sum`; `pastecart (vec 0:real^3) (lift(&1))`]
                P2BX_DIRDERIV) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM wan_tder] THEN
  SUBGOAL_THEN
   `(\h. sqrt(det(p2bw_cmet atlas' c (&1) (g':real->B->real^3^3)
                   (z + h % pastecart (vec 0:real^3) (lift(&1)))))) =
    (\s. mfd_density atlas' c (g' s) (fstcart z)) o (\h. &1 - (drop(sndcart z) + h))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; p2bw_cmet; mfd_density; FSTCART_ADD; FSTCART_CMUL;
                SNDCART_ADD; SNDCART_CMUL; FSTCART_PASTECART; SNDCART_PASTECART;
                VECTOR_MUL_RZERO; VECTOR_ADD_RID; DROP_ADD; DROP_CMUL; LIFT_DROP;
                REAL_MUL_RID];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
  EXISTS_TAC `(\s. mfd_density atlas' c ((g':real->B->real^3^3) s) (fstcart z)) o
              (\h. &1 - (drop(sndcart (z:real^(3,1)finite_sum)) + h))` THEN
  EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `p2bw_cscal atlas' c (&1) (g':real->B->real^3^3) z * sqrt(det(p2bw_cmet atlas' c (&1) g' z)) =
    (--mfd_scalar atlas' (g'(&1 - drop(sndcart z))) (chart_inv c (fstcart z)) *
     mfd_density atlas' c (g'(&1 - drop(sndcart z))) (fstcart z)) * --(&1)`
  SUBST1_TAC THENL
   [REWRITE_TAC[p2bw_cscal; p2bw_cmet; mfd_density] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_DIFF_CHAIN_ATREAL THEN CONJ_TAC THENL
   [REAL_DIFF_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_RID] THEN
  MATCH_MP_TAC GRGT_CHART_DENSITY_EVOLUTION THEN
  MAP_EVERY EXISTS_TAC [`top':B topology`; `--drop(sndcart(z:real^(3,1)finite_sum))`;
                        `&1`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Pointwise limits at one point of the limit; t^2 linf(t,y) is              *)
(* nondecreasing in t (COR_9_10 (3) in the limit); the time derivative of    *)
(* linf in a chart is at least -2 linf / t.                                  *)
(* ========================================================================= *)

let P2BX_LIMIT_POINT = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf y t1 t2 e.
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     y IN topspace top' /\ &0 < t1 /\ t1 <= t2 /\ &0 < e
     ==> ?k. phi k y IN topspace top /\
             !t. t1 <= t /\ t <= t2
                 ==> abs(p2b_klx (top,atlas) g p (tau k * t) (phi k y) - linf t y) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `t1:real`; `{y:B}`; `&1`] P2BX_QF_VIEW) THEN
  ASM_REWRITE_TAC[COMPACT_IN_SING; REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (LABEL_TAC "QF")) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2BX_G1OUT_SUBSEQ) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`{y:B}`; `t1:real`; `t2:real`; `e:real`] o CONJUNCT1 o
    CONJUNCT2 o REWRITE_RULE[p2bg_g1out; p2bg_conv] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2bg_g1out")) (concl th))) THEN
  ASM_REWRITE_TAC[COMPACT_IN_SING; IN_SING] THEN
  DISCH_THEN(X_CHOOSE_THEN `m1:num` (MP_TAC o SPEC `m1 + k0:num`)) THEN
  REWRITE_TAC[LE_ADD] THEN DISCH_THEN(ASSUME_TAC o SPEC `y:B`) THEN
  EXISTS_TAC `(sub:num->num)(m1 + k0)` THEN
  REMOVE_THEN "QF" (MP_TAC o SPEC `(sub:num->num)(m1 + k0)`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `m1 + k0:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SING_SUBSET] THEN STRIP_TAC THEN CONJ_TAC THENL
   [UNDISCH_TAC `IMAGE ((phi:num->B->A) ((sub:num->num)(m1 + k0))) (W((sub:num->num)(m1 + k0)))
                 SUBSET topspace top` THEN
    UNDISCH_TAC `(y:B) IN W((sub:num->num)(m1 + k0))` THEN SET_TAC[];
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `m1:num`)) (concl th))) THEN
    ASM_SIMP_TAC[]]);;

let P2BX_LINF_TMONO = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf y t1 t2.
     P2B_COR_9_10_STATEMENT (u:A->bool) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     y IN topspace top' /\ &0 < t1 /\ t1 <= t2
     ==> t1 pow 2 * linf t1 y <= t2 pow 2 * linf t2 y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `e = (t1 pow 2 * (linf:real->B->real) t1 y - t2 pow 2 * linf t2 y) /
                  (&2 * (t1 pow 2 + t2 pow 2))` THEN
  SUBGOAL_THEN `&0 < t1 pow 2 + t2 pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < a /\ &0 <= b ==> &0 < a + b`) THEN
    ASM_SIMP_TAC[REAL_POW_LT; REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `y:B`; `t1:real`; `t2:real`; `e:real`] P2BX_LIMIT_POINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `t1:real` th) THEN MP_TAC(SPEC `t2:real` th)) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`kappa:real`; `top:A topology`;
                                `atlas:((A->bool)#(A->real^3))->bool`;
                                `g:real->A->real^3^3`; `p:A`] o
    GEN_REWRITE_RULE I [P2B_COR_9_10_STATEMENT] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "P2B_COR_9_10_STATEMENT"))
        (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`(phi:num->B->A) k y`; `(tau:num->real) k * t1`;
                             `(tau:num->real) k * t2`] o CONJUNCT2 o CONJUNCT2) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  ABBREV_TAC `l1 = p2b_klx (top,atlas) (g:real->A->real^3^3) p ((tau:num->real) k * t1)
                     ((phi:num->B->A) k y)` THEN
  ABBREV_TAC `l2 = p2b_klx (top,atlas) (g:real->A->real^3^3) p ((tau:num->real) k * t2)
                     ((phi:num->B->A) k y)` THEN
  REWRITE_TAC[REAL_POW_MUL; GSYM REAL_MUL_ASSOC] THEN
  SUBGOAL_THEN `&0 < (tau:num->real) k pow 2` (fun th -> REWRITE_TAC[MATCH_MP REAL_LE_LMUL_EQ th])
  THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `t1 pow 2 * abs(l1 - (linf:real->B->real) t1 y) <= t1 pow 2 * e /\
                t2 pow 2 * abs(l2 - linf t2 y) <= t2 pow 2 * e`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LE_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(t1 pow 2 + t2 pow 2) * e =
                (t1 pow 2 * (linf:real->B->real) t1 y - t2 pow 2 * linf t2 y) / &2`
  MP_TAC THENL
   [EXPAND_TAC "e" THEN UNDISCH_TAC `&0 < t1 pow 2 + t2 pow 2` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(t1 pow 2 * (l1 - (linf:real->B->real) t1 y)) =
                t1 pow 2 * abs(l1 - linf t1 y) /\
                abs(t2 pow 2 * (l2 - linf t2 y)) = t2 pow 2 * abs(l2 - linf t2 y)`
  MP_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW; REAL_POW2_ABS]; ALL_TAC] THEN
  UNDISCH_TAC `t2 pow 2 * linf t2 y < t1 pow 2 * (linf:real->B->real) t1 y` THEN
  UNDISCH_TAC `t1 pow 2 * l1 <= t2 pow 2 * l2` THEN
  REAL_ARITH_TAC);;

(* At a point of differentiability, the time derivative of linf read in a  *)
(* chart is at least -2 linf / t.                                            *)

let P2BX_CFUN_TDER_LB = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf c z.
     P2B_COR_9_10_STATEMENT (u:A->bool) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     c IN atlas' /\ fstcart z IN IMAGE (SND c) (FST c) /\ &0 < drop(sndcart z) /\
     (\w. lift(p2bw_cfun c linf w)) differentiable at z
     ==> --(&2 * p2bw_cfun c linf z / drop(sndcart z)) <= wan_tder (p2bw_cfun c linf) z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `chart_inv (c:(B->bool)#(B->real^3)) (fstcart (z:real^(3,1)finite_sum)) IN
                topspace top'` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o check (fun th ->
      concl th = `open_in (top':B topology) (FST (c:(B->bool)#(B->real^3)))`)) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2bw_cfun (c:(B->bool)#(B->real^3)) (linf:real->B->real)`;
                 `z:real^(3,1)finite_sum`; `pastecart (vec 0:real^3) (lift(&1))`]
                P2BX_DIRDERIV) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM wan_tder] THEN REWRITE_TAC[ETA_AX] THEN
  ABBREV_TAC `x = chart_inv (c:(B->bool)#(B->real^3)) (fstcart (z:real^(3,1)finite_sum))` THEN
  ABBREV_TAC `t = drop(sndcart (z:real^(3,1)finite_sum))` THEN
  ABBREV_TAC `D = wan_tder (p2bw_cfun (c:(B->bool)#(B->real^3)) (linf:real->B->real)) z` THEN
  SUBGOAL_THEN `(\h. p2bw_cfun (c:(B->bool)#(B->real^3)) (linf:real->B->real)
                       (z + h % pastecart (vec 0:real^3) (lift(&1)))) =
                (\h. linf (t + h) (x:B))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; p2bw_cfun; FSTCART_ADD; FSTCART_CMUL; SNDCART_ADD; SNDCART_CMUL;
                FSTCART_PASTECART; SNDCART_PASTECART; VECTOR_MUL_RZERO; VECTOR_ADD_RID;
                DROP_ADD; DROP_CMUL; LIFT_DROP; REAL_MUL_RID] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `p2bw_cfun (c:(B->bool)#(B->real^3)) (linf:real->B->real) z = linf t (x:B)`
  SUBST1_TAC THENL [REWRITE_TAC[p2bw_cfun] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `((\h. (t + h) pow 2) has_real_derivative &2 * t) (atreal (&0))` ASSUME_TAC THENL
   [REAL_DIFF_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`\h. (t + h) pow 2`; `&2 * t`; `\h. (linf:real->B->real) (t + h) x`; `D:real`;
                 `&0`] HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN REWRITE_TAC[REAL_ADD_RID] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= t pow 2 * D + (&2 * t) * (linf:real->B->real) t x` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPEC `atreal (&0)` REALLIM_LBOUND) THEN
    EXISTS_TAC `\h. ((t + h) pow 2 * (linf:real->B->real) (t + h) x -
                     (t + &0) pow 2 * linf (t + &0) x) / (h - &0)` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_ATREAL] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HAS_REAL_DERIVATIVE_ATREAL] o check (fun th ->
        can (find_term ((=) `D:real`)) (concl th))) THEN
      REWRITE_TAC[REAL_ADD_RID];
      ALL_TAC] THEN
    REWRITE_TAC[EVENTUALLY_ATREAL; REAL_ADD_RID; REAL_SUB_RZERO] THEN
    EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `h:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `&0 < h` THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      REWRITE_TAC[REAL_SUB_LE] THEN MATCH_MP_TAC P2BX_LINF_TMONO THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                            `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                            `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`;
                            `phi:num->B->A`; `sub:num->num`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[real_div] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= --a * --b ==> &0 <= a * b`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ALL_TAC;
        REWRITE_TAC[GSYM REAL_INV_NEG] THEN MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC] THEN
      REWRITE_TAC[REAL_NEG_SUB; REAL_SUB_LE] THEN MATCH_MP_TAC P2BX_LINF_TMONO THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                            `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                            `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`;
                            `phi:num->B->A`; `sub:num->num`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= t * D + &2 * (linf:real->B->real) t x` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:real`; `t * D + &2 * (linf:real->B->real) t x`]
      (CONJUNCT1 REAL_LE_MUL_EQ)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `&0 <= t pow 2 * D + (&2 * t) * (linf:real->B->real) t x` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `D + &2 * (linf:real->B->real) t x / t = (t * D + &2 * linf t x) / t`
  ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (t * D + &2 * (linf:real->B->real) t x) / t` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  UNDISCH_TAC `D + &2 * (linf:real->B->real) t x / t = (t * D + &2 * linf t x) / t` THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The Gaussian lower bound of linf (MT Cor 9.26 in the limit, with the      *)
(* error 1 of LIM_DIST and of the convergence): linf grows quadratically in  *)
(* the distance to xl, so its sublevel sets lie in balls about xl.           *)
(* ========================================================================= *)

let P2BX_GAUSS_ALG = prove
 (`!c1 t TT s dk D lq lp li C.
     &0 < c1 /\ &0 < t /\ &0 < TT /\ s pow 2 = inv TT /\ &0 <= s /\ &0 <= dk /\ &1 <= D /\
     abs(s * dk - D) < &1 /\ (c1 * dk pow 2) / (TT * t) - lq - &1 <= lp /\ lq <= C /\
     abs(lp - li) < &1
     ==> (c1 * (D - &1) pow 2) / t - C - &2 <= li`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(D - &1) pow 2 <= (s * dk) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(c1 * dk pow 2) / (TT * t) = (c1 * (s * dk) pow 2) / t` SUBST_ALL_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_MUL] THEN UNDISCH_TAC `&0 < TT` THEN UNDISCH_TAC `&0 < t` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `(c1 * (D - &1) pow 2) / t <= (c1 * (s * dk) pow 2) / t` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2BX_LINF_GAUSS = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf c1 t y.
     P2B_COR_9_10_STATEMENT (u:A->bool) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     &0 < c1 /\
     (!kappa top atlas (g:real->A->real^3^3) p t p1 q1.
        p2b_kappa_solution kappa (top,atlas) g /\ p IN topspace top /\ &0 < t /\
        p1 IN topspace top /\ q1 IN topspace top
        ==> (c1 * mfd_dist (top,atlas) (g(--t)) p1 q1 pow 2) / t -
            p2b_klx (top,atlas) g p t q1 - &1
            <= p2b_klx (top,atlas) g p t p1) /\
     &0 < t /\ y IN topspace top' /\ &1 <= mfd_dist (top',atlas') (g'(&1 - t)) xl y
     ==> (c1 * (mfd_dist (top',atlas') (g'(&1 - t)) xl y - &1) pow 2) / t -
         &3 / &2 * (t + inv(t pow 2)) - &2 <= linf t y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "L925") STRIP_ASSUME_TAC))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_KSOL_FACTS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2BX_G1OUT_SUBSEQ) THEN
  SUBGOAL_THEN `!k. --((tau:num->real) k) + (&1 - t) / inv(tau k) = --(tau k * t)`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[real_div; REAL_INV_INV] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!k. --((tau:num->real) k * t) <= &0` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 < x ==> --x <= &0`) THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas' ((g':real->B->real^3^3)(&1 - t))` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX_LIMIT_RIEM THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                          `top':B topology`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`kappa:real`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:real->A->real^3^3`] P2BX_KVIEW_HYP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bg_setup] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2bg_setup")) (concl th))) THEN
  (* rescaled distances on the pair {xl, y} *)
  MP_TAC(ISPECL [`u:A->bool`; `w:B->bool`] LIM_DIST) THEN REWRITE_TAC[LIM_DIST_STATEMENT] THEN
  DISCH_THEN(MP_TAC o ISPECL
   [`\k:num. p2b_kview (top,atlas) (g:real->A->real^3^3)`; `q:num->A`;
    `\k:num. --((tau:num->real) k)`; `\k:num. inv((tau:num->real) k)`;
    `{s:real | s < &1}`; `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
    `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`;
    `&1 - t`; `{xl:B, y}`; `&1`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[P2BX_KVIEW_SLICE; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC THEN NO_TAC) THEN
    TRY(FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC THEN NO_TAC) THEN
    MATCH_MP_TAC FINITE_IMP_COMPACT_IN THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; INSERT_SUBSET; EMPTY_SUBSET] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[P2BX_KVIEW_SLICE] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `k1:num`) THEN
  (* the members of the subsequence near y *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `t:real`; `{y:B}`; `&1`] P2BX_QF_VIEW) THEN
  ASM_REWRITE_TAC[COMPACT_IN_SING; REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `k2:num` (LABEL_TAC "QF")) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`{y:B}`; `t:real`; `t:real`; `&1`] o CONJUNCT1 o
    CONJUNCT2 o REWRITE_RULE[p2bg_g1out; p2bg_conv] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2bg_g1out")) (concl th))) THEN
  ASM_REWRITE_TAC[COMPACT_IN_SING; IN_SING; REAL_LT_01; REAL_LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `m1:num` (MP_TAC o SPECL [`m1 + k1 + k2:num`; `y:B`; `t:real`])) THEN
  REWRITE_TAC[LE_ADD; REAL_LE_REFL] THEN STRIP_TAC THEN
  ABBREV_TAC `k = (sub:num->num)(m1 + k1 + k2)` THEN
  SUBGOAL_THEN `k1 <= k /\ k2 <= (k:num)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m1 + k1 + k2:num` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `sub:num->num`)) (concl th) &&
      not(can (find_term ((=) `linf:real->B->real`)) (concl th)))) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "QF" (MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[SING_SUBSET] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(phi:num->B->A) k y IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE ((phi:num->B->A) k) (W k) SUBSET topspace top` THEN
    UNDISCH_TAC `(y:B) IN W (k:num)` THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `xl:B`; `y:B`] o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `k1:num`)) (concl th))) THEN
  ASM_REWRITE_TAC[IN_INSERT] THEN STRIP_TAC THEN
  (* the flow bound at tau_k t with q1 = q k and Claim 9.15 *)
  USE_THEN "L925" (MP_TAC o SPECL [`kappa:real`; `top:A topology`;
                                   `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                                   `p:A`; `(tau:num->real) k * t`; `(phi:num->B->A) k y`;
                                   `(q:num->A) k`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`u:A->bool`; `kappa:real`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`; `p:A`;
                 `(tau:num->real) k`; `(q:num->A) k`; `t:real`] P2BX_CLAIM_9_15) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `mfd_dist (top,atlas) ((g:real->A->real^3^3)(--((tau:num->real) k * t))) ((phi:num->B->A) k y)
             ((q:num->A) k) =
    mfd_dist (top,atlas) (g(--(tau k * t))) (q k) (phi k y)`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [MATCH_MP_TAC MFD_DIST_SYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC P2BX_GAUSS_ALG THEN
  MAP_EVERY EXISTS_TAC
   [`(tau:num->real) k`; `sqrt(inv((tau:num->real) k))`;
    `mfd_dist (top,atlas) ((g:real->A->real^3^3)(--((tau:num->real) k * t))) ((q:num->A) k)
              ((phi:num->B->A) k y)`;
    `p2b_klx (top,atlas) (g:real->A->real^3^3) p ((tau:num->real) k * t) ((q:num->A) k)`;
    `p2b_klx (top,atlas) (g:real->A->real^3^3) p ((tau:num->real) k * t)
             ((phi:num->B->A) k y)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_POW_2 THEN MATCH_MP_TAC REAL_LE_INV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_INV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The C^1 cubic step chi (1 on s <= 0, 0 on s >= 1, 1 - 3 s^2 + 2 s^3       *)
(* between) used in the cutoffs chi(linf - R).                               *)
(* ========================================================================= *)

let p2bx_chi = new_definition
 `p2bx_chi (s:real) = if s <= &0 then &1 else if &1 <= s then &0
                      else &1 - &3 * s pow 2 + &2 * s pow 3`;;

let p2bx_dchi = new_definition
 `p2bx_dchi (s:real) = if s <= &0 \/ &1 <= s then &0 else &6 * s pow 2 - &6 * s`;;

let P2BX_CHI_BOUNDS = prove
 (`!s. &0 <= p2bx_chi s /\ p2bx_chi s <= &1 /\
       --(&3 / &2) <= p2bx_dchi s /\ p2bx_dchi s <= &0 /\
       (s <= &0 ==> p2bx_chi s = &1) /\ (&1 <= s ==> p2bx_chi s = &0) /\
       (s <= &0 \/ &1 <= s ==> p2bx_dchi s = &0)`,
  GEN_TAC THEN REWRITE_TAC[p2bx_chi; p2bx_dchi] THEN
  ASM_CASES_TAC `s <= &0` THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&1 <= s` THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < s /\ s < &1` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= s pow 2 * (&3 - &2 * s) /\ &0 <= s * (&1 - s) /\
                &0 <= (&2 * s - &1) pow 2 /\ &0 <= (&1 - s) pow 2 * (&1 + &2 * s)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LE_MUL) THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC);;

(* Near the junctions the step is quadratically close to its value there. *)

let P2BX_CHI_JUNCTIONS = prove
 (`!x. (abs x < &1 / &2 ==> abs(p2bx_chi x - &1) <= &3 * x pow 2) /\
       (abs(x - &1) < &1 / &2 ==> abs(p2bx_chi x) <= &3 * (x - &1) pow 2)`,
  GEN_TAC THEN REWRITE_TAC[p2bx_chi] THEN CONJ_TAC THEN DISCH_TAC THENL
   [COND_CASES_TAC THENL
     [REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    COND_CASES_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= x pow 3 /\ x pow 3 <= x pow 2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_ARITH `x pow 3 = x * x pow 2`] THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    COND_CASES_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THENL
     [REWRITE_TAC[REAL_ABS_0] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&1 - &3 * x pow 2 + &2 * x pow 3 = (x - &1) pow 2 * (&1 + &2 * x)`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (x - &1) pow 2` ASSUME_TAC THENL [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (x - &1) pow 2 * (&1 + &2 * x) /\
                  (x - &1) pow 2 * (&1 + &2 * x) <= (x - &1) pow 2 * &3`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC]);;

let P2BX_CHI_DERIV = prove
 (`!s. (p2bx_chi has_real_derivative p2bx_dchi s) (atreal s)`,
  GEN_TAC THEN
  ASM_CASES_TAC `s < &0` THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    MAP_EVERY EXISTS_TAC [`\x:real. &1`; `--s`] THEN ASM_REWRITE_TAC[REAL_NEG_GT0] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:real` THEN DISCH_TAC THEN REWRITE_TAC[p2bx_chi] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `p2bx_dchi s = &0` SUBST1_TAC THENL
     [REWRITE_TAC[p2bx_dchi] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST]];
    ALL_TAC] THEN
  ASM_CASES_TAC `&1 < s` THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    MAP_EVERY EXISTS_TAC [`\x:real. &0`; `s - &1`] THEN ASM_REWRITE_TAC[REAL_SUB_LT] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:real` THEN DISCH_TAC THEN REWRITE_TAC[p2bx_chi] THEN
      COND_CASES_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `p2bx_dchi s = &0` SUBST1_TAC THENL
     [REWRITE_TAC[p2bx_dchi] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST]];
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 < s /\ s < &1` THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    MAP_EVERY EXISTS_TAC [`\x:real. &1 - &3 * x pow 2 + &2 * x pow 3`; `min s (&1 - s)`] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real` THEN DISCH_TAC THEN REWRITE_TAC[p2bx_chi] THEN
      COND_CASES_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      COND_CASES_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `p2bx_dchi s = &6 * s pow 2 - &6 * s` SUBST1_TAC THENL
     [REWRITE_TAC[p2bx_dchi] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REAL_DIFF_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the junctions s = 0 and s = 1 *)
  SUBGOAL_THEN `p2bx_dchi s = &0` SUBST1_TAC THENL
   [REWRITE_TAC[p2bx_dchi] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_ATREAL; REAL_SUB_RZERO] THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\x. &3 * abs(x - s)` THEN CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_ATREAL] THEN EXISTS_TAC `&1 / &2` THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ABS_DIV] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    SUBGOAL_THEN `(&3 * abs(x - s)) * abs(x - s) = &3 * (x - s) pow 2` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_MUL_ASSOC; GSYM REAL_POW_2; REAL_POW2_ABS]; ALL_TAC] THEN
    SUBGOAL_THEN `s = &0 \/ s = &1` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC)] THEN
    MP_TAC(SPEC `x:real` P2BX_CHI_JUNCTIONS) THEN
    SUBGOAL_THEN `p2bx_chi(&0) = &1 /\ p2bx_chi(&1) = &0` (fun th -> REWRITE_TAC[th]) THEN
    TRY(REWRITE_TAC[p2bx_chi] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN NO_TAC) THEN
    REWRITE_TAC[REAL_SUB_RZERO] THEN ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REALLIM_NULL_LMUL THEN REWRITE_TAC[REALLIM_NULL_ABS] THEN
    REWRITE_TAC[GSYM REALLIM_NULL; REALLIM_ATREAL_ID]]);;

