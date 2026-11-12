(* ========================================================================= *)
(* Unit pc_p2b_g3f: G3, the weak equation.  Compact sublevel sets of linf    *)
(* (Gaussian lower bound and completeness), slices of U and their limits     *)
(* (the reduced volume V), the smooth time cutoff, and the assembly:         *)
(* W(psi) = 0 for every test in every chart box (p2bg_weq).                  *)
(* ========================================================================= *)

needs "src/pc_p2b_g3e.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Functions continuous in charts are continuous; sublevel sets of linf(t,.) *)
(* are compact.                                                              *)
(* ========================================================================= *)

let P2BX_MFD_CHARTCONT_MAP = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) f.
     smooth_manifold_atlas top atlas /\
     (!c. c IN atlas ==> (\y. lift(f(chart_inv c y))) continuous_on IMAGE (SND c) (FST c))
     ==> continuous_map (top,euclidean) (\x. lift(f x))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(INST_TYPE [`:(A->bool)#(A->real^N)`,`:K`] PASTING_LEMMA) THEN
  MAP_EVERY EXISTS_TAC [`\c:(A->bool)#(A->real^N). \x:A. lift(f x)`;
                        `FST:(A->bool)#(A->real^N)->A->bool`;
                        `atlas:((A->bool)#(A->real^N))->bool`] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
    EXISTS_TAC `(\y. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y))) o SND c` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:A` THEN REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; o_THM] THEN
      STRIP_TAC THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean (IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))` THEN
    REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN] THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `c:(A->bool)#(A->real^N)`] MFDD_CHART_CONTINUOUS) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[]];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN EXISTS_TAC `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
    ASM_SIMP_TAC[]]);;

let P2BX_MFD_SUBLEVEL = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) f C.
     smooth_manifold_atlas top atlas /\
     (!c. c IN atlas ==> (\y. lift(f(chart_inv c y))) continuous_on IMAGE (SND c) (FST c))
     ==> closed_in top {x | x IN topspace top /\ f x <= C} /\
         open_in top {x | x IN topspace top /\ f x < C}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2BX_MFD_CHARTCONT_MAP) THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`\x:A. lift(f x)`; `top:A topology`; `euclidean:(real^1)topology`;
                   `{y:real^1 | y$1 <= C}`] CLOSED_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    ASM_REWRITE_TAC[GSYM CLOSED_IN; CLOSED_HALFSPACE_COMPONENT_LE; IN_ELIM_THM; GSYM drop;
                    LIFT_DROP];
    MP_TAC(ISPECL [`\x:A. lift(f x)`; `top:A topology`; `euclidean:(real^1)topology`;
                   `{y:real^1 | y$1 < C}`] OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    ASM_REWRITE_TAC[GSYM OPEN_IN; OPEN_HALFSPACE_COMPONENT_LT; IN_ELIM_THM; GSYM drop;
                    LIFT_DROP]]);;

(* Sublevel sets of linf(t,.) are compact (Lemma 9.25 in the limit). *)

let P2BX_LINF_SUBLEVEL = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf t C.
     P2B_LEMMA_9_25_STATEMENT (u:A->bool) /\ P2B_COR_9_10_STATEMENT u /\
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\ &0 < t
     ==> compact_in top' {x | x IN topspace top' /\ linf t x <= C} /\
         closed_in top' {x | x IN topspace top' /\ linf t x <= C} /\
         open_in top' {x | x IN topspace top' /\ linf t x < C}`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(linf:real->B->real) t`; `C:real`] P2BX_MFD_SUBLEVEL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `c:(B->bool)#(B->real^3)` THEN DISCH_TAC THEN
    MATCH_MP_TAC P2BX_LINF_SLICE_CONT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                          `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                          `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`;
                          `phi:num->B->A`; `sub:num->num`] THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `c1:real` STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [P2B_LEMMA_9_25_STATEMENT]) THEN
  ABBREV_TAC `E = max (&0) (((C + &3 / &2 * (t + inv(t pow 2)) + &2) * t) / c1)` THEN
  MATCH_MP_TAC CLOSED_COMPACT_IN THEN
  EXISTS_TAC `mfd_cball (top',atlas') ((g':real->B->real^3^3)(&1 - t)) xl (&1 + sqrt E)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `mfd_complete (top',atlas') ((g':real->B->real^3^3)(&1 - t))` MP_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; mfd_cball] THEN X_GEN_TAC `y:B` THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `&1 <= mfd_dist (top',atlas') ((g':real->B->real^3^3)(&1 - t)) xl y` THENL
   [ALL_TAC;
    MATCH_MP_TAC(REAL_ARITH `d < &1 /\ &0 <= s ==> d <= &1 + s`) THEN
    ASM_REWRITE_TAC[GSYM REAL_NOT_LE] THEN MATCH_MP_TAC SQRT_POS_LE THEN
    EXPAND_TAC "E" THEN REAL_ARITH_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `c1:real`; `t:real`; `y:B`] P2BX_LINF_GAUSS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `d - &1 <= s ==> d <= &1 + s`) THEN
  MATCH_MP_TAC REAL_LE_RSQRT THEN EXPAND_TAC "E" THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> x <= max (&0) y`) THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  SUBGOAL_THEN `(c1 * (mfd_dist (top',atlas') ((g':real->B->real^3^3)(&1 - t)) xl y - &1) pow 2) / t <=
                C + &3 / &2 * (t + inv(t pow 2)) + &2` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Slices of U = t^(-3/2) e^(-linf): the reduced volume integrand, the       *)
(* cut slices I_S(t) (integrable, between the integral over {linf < m} and   *)
(* V), and I_S(t) -> V as S -> infinity.                                     *)
(* ========================================================================= *)

let P2BX_UF_RVOL_EQ = prove
 (`!(linf:real->B->real) t x.
     &0 < t ==> p2bx_uf linf t x = exp(--(linf t x)) / sqrt t pow 3`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2bx_uf; REAL_NEG_ADD; REAL_EXP_ADD; real_div] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `sqrt t = exp(log t / &2)` SUBST1_TAC THENL
   [MATCH_MP_TAC SQRT_UNIQUE THEN REWRITE_TAC[REAL_EXP_POS_LE; GSYM REAL_EXP_N] THEN
    REWRITE_TAC[REAL_ARITH `&2 * x / &2 = x`] THEN ASM_SIMP_TAC[EXP_LOG];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_EXP_N; GSYM REAL_EXP_NEG] THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

(* Functions on the limit continuous in charts with compact support are      *)
(* integrable.                                                                *)

let P2BX_MFD_INTEGRABLE_CS = prove
 (`!top atlas (g:A->real^N^N) f K.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     compact_in top K /\ closed_in top K /\
     (!c. c IN atlas ==> (\y. lift(f(chart_inv c y))) continuous_on IMAGE (SND c) (FST c)) /\
     (!x. x IN topspace top /\ ~(x IN K) ==> f x = &0) /\
     mfd_has_integral (top,atlas) g (\x. &0) (topspace top) (&0)
     ==> mfd_integrable_on (top,atlas) g f (topspace top)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `mfd_lebesgue_measurable (top,atlas:((A->bool)#(A->real^N))->bool) (K:A->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_LEBESGUE_MEASURABLE_CLOSED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `K:A->bool`] P2BX_MFD_INTEGRABLE_CHARTCONT) THEN
  ASM_REWRITE_TAC[mfd_integrable_on] THEN DISCH_THEN(X_CHOOSE_TAC `v:real`) THEN
  EXISTS_TAC `v + &0` THEN
  SUBGOAL_THEN `topspace top = (K:A->bool) UNION (topspace top DIFF K)` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `K:A->bool`] COMPACT_IN_SUBSET_TOPSPACE) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MFD_HAS_INTEGRAL_UNION THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `\x:A. &0`; `f:A->real`; `topspace top DIFF K:A->bool`; `&0`]
                  MFD_HAS_INTEGRAL_EQ) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_DIFF] THEN REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC P2BX_MFD_ZERO_SUBSET THEN EXISTS_TAC `topspace top:A->bool` THEN
    ASM_REWRITE_TAC[SUBSET_DIFF] THEN
    MATCH_MP_TAC MFD_LEBESGUE_MEASURABLE_OPEN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[OPEN_IN_TOPSPACE];
    SET_TAC[]]);;

let P2BX_UH_GCONT = prove
 (`!k S. !s. (\s. exp(--(s + k)) * p2bx_chi(s / S - &1)) real_continuous atreal s`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_MUL THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(\s. exp(--(s + k))) = exp o (\s. --(s + k))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_COMPOSE THEN REWRITE_TAC[REAL_CONTINUOUS_AT_EXP] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_NEG THEN MATCH_MP_TAC REAL_CONTINUOUS_ADD THEN
    REWRITE_TAC[REAL_CONTINUOUS_AT_ID; REAL_CONTINUOUS_CONST];
    SUBGOAL_THEN `(\s. p2bx_chi(s / S - &1)) = p2bx_chi o (\s. s / S - &1)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN REWRITE_TAC[REAL_CONTINUOUS_CONST; real_div] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_RMUL THEN REWRITE_TAC[REAL_CONTINUOUS_AT_ID];
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
      MESON_TAC[P2BX_CHI_DERIV]]]);;

(* Zero has integral zero on the limit at positive times (from the reduced   *)
(* volume integrand).                                                         *)

let P2BX_RVOL_ZERO = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi linf V t.
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_rvol (top',atlas') g' linf V /\ &0 < t
     ==> mfd_has_integral (top',atlas') (g'(&1 - t)) (\x. &0) (topspace top') (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o GEN_REWRITE_RULE I [p2bg_rvol]) THEN
  ASM_REWRITE_TAC[mfd_integrable_on] THEN
  DISCH_THEN(X_CHOOSE_TAC `v:real` o CONJUNCT1) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(g':real->B->real^3^3)(&1 - t)`;
                 `\y:B. exp(--((linf:real->B->real) t y)) / sqrt t pow 3`;
                 `topspace top':B->bool`; `v:real`; `&0`] MFD_HAS_INTEGRAL_CMUL) THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO]);;

(* The cut slices I_S(t). *)

let P2BX_UH_SLICE = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf V t S.
     P2B_LEMMA_9_25_STATEMENT (u:A->bool) /\ P2B_COR_9_10_STATEMENT u /\
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     p2bg_rvol (top',atlas') g' linf V /\ &0 < t /\ &0 < S
     ==> mfd_integrable_on (top',atlas') (g'(&1 - t))
           (\x. p2bx_uf linf t x * p2bx_hcut S linf t x) (topspace top') /\
         &0 <= mfd_integral (top',atlas') (g'(&1 - t)) (topspace top')
                 (\x. p2bx_uf linf t x * p2bx_hcut S linf t x) /\
         mfd_integral (top',atlas') (g'(&1 - t)) (topspace top')
           (\x. p2bx_uf linf t x * p2bx_hcut S linf t x) <= V /\
         (!m. m <= S
              ==> mfd_integral (top',atlas') (g'(&1 - t)) {x | x IN topspace top' /\ linf t x < m}
                    (\x. exp(--(linf t x)) / sqrt t pow 3) <=
                  mfd_integral (top',atlas') (g'(&1 - t)) (topspace top')
                    (\x. p2bx_uf linf t x * p2bx_hcut S linf t x))`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  SUBGOAL_THEN `riemannian_metric atlas' ((g':real->B->real^3^3)(&1 - t))` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX_LIMIT_RIEM THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                          `top':B topology`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `linf:real->B->real`; `V:real`; `t:real`]
                P2BX_RVOL_ZERO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `t:real` o GEN_REWRITE_RULE I [p2bg_rvol] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2bg_rvol")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* integrability *)
  SUBGOAL_THEN `mfd_integrable_on (top',atlas') ((g':real->B->real^3^3)(&1 - t))
                  (\x. p2bx_uf (linf:real->B->real) t x * p2bx_hcut S linf t x) (topspace top')`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX_MFD_INTEGRABLE_CS THEN
    EXISTS_TAC `{x | x IN topspace top' /\ (linf:real->B->real) t x <= &2 * S}` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                   `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                   `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                   `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                   `t:real`; `&2 * S`] P2BX_LINF_SUBLEVEL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `c:(B->bool)#(B->real^3)` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`\s. exp(--(s + &3 / &2 * log t)) * p2bx_chi(s / S - &1)`;
                     `\y. (linf:real->B->real) t (chart_inv (c:(B->bool)#(B->real^3)) y)`;
                     `IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c)`] P2BX_REAL_COMPOSE_CONT) THEN
      REWRITE_TAC[P2BX_UH_GCONT] THEN ANTS_TAC THENL
       [MATCH_MP_TAC P2BX_LINF_SLICE_CONT THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                              `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                              `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                              `g':real->B->real^3^3`; `xl:B`; `W:num->B->bool`;
                              `phi:num->B->A`; `sub:num->num`] THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[p2bx_uf; p2bx_hcut]];
      X_GEN_TAC `x:B` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      SUBGOAL_THEN `&2 * S < (linf:real->B->real) t x` ASSUME_TAC THENL
       [UNDISCH_TAC `~((x:B) IN topspace top' /\ (linf:real->B->real) t x <= &2 * S)` THEN
        ASM_REWRITE_TAC[REAL_NOT_LE];
        ALL_TAC] THEN
      REWRITE_TAC[p2bx_hcut] THEN
      SUBGOAL_THEN `p2bx_chi((linf:real->B->real) t x / S - &1) = &0` (fun th -> REWRITE_TAC[th; REAL_MUL_RZERO]) THEN
      MP_TAC(SPEC `(linf:real->B->real) t x / S - &1` P2BX_CHI_BOUNDS) THEN
      DISCH_THEN(MATCH_MP_TAC o el 5 o CONJUNCTS) THEN
      ASM_SIMP_TAC[REAL_LE_SUB_LADD; REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[MFD_INTEGRABLE_INTEGRAL] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2bx_hcut")) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_integrable_on")) (concl th))) THEN
  ABBREV_TAC `Iv = mfd_integral (top',atlas') ((g':real->B->real^3^3)(&1 - t)) (topspace top')
                    (\x. p2bx_uf (linf:real->B->real) t x * p2bx_hcut S linf t x)` THEN
  SUBGOAL_THEN `!x. &0 <= p2bx_uf (linf:real->B->real) t x * p2bx_hcut S linf t x /\
                    p2bx_uf linf t x * p2bx_hcut S linf t x <= exp(--(linf t x)) / sqrt t pow 3`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`linf:real->B->real`; `t:real`; `x:B`] P2BX_UF_RVOL_EQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    REWRITE_TAC[p2bx_hcut] THEN
    MP_TAC(SPEC `(linf:real->B->real) t x / S - &1` P2BX_CHI_BOUNDS) THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= p2bx_uf (linf:real->B->real) t x` ASSUME_TAC THENL
     [REWRITE_TAC[p2bx_uf; REAL_EXP_POS_LE]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(INST_TYPE [`:B`,`:A`; `:3`,`:N`] MFD_HAS_INTEGRAL_LE) THEN
    MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                          `(g':real->B->real^3^3)(&1 - t)`; `\x:B. &0`;
                          `\x. p2bx_uf (linf:real->B->real) t x * p2bx_hcut S linf t x`;
                          `topspace top':B->bool`] THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC(INST_TYPE [`:B`,`:A`; `:3`,`:N`] MFD_HAS_INTEGRAL_LE) THEN
    MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                          `(g':real->B->real^3^3)(&1 - t)`;
                          `\x. p2bx_uf (linf:real->B->real) t x * p2bx_hcut S linf t x`;
                          `\y:B. exp(--((linf:real->B->real) t y)) / sqrt t pow 3`;
                          `topspace top':B->bool`] THEN
    ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `mfd_integrable_on (top',atlas') ((g':real->B->real^3^3)(&1 - t))
                   (\y:B. exp(--((linf:real->B->real) t y)) / sqrt t pow 3) (topspace top')` THEN
    ASM_REWRITE_TAC[MFD_INTEGRABLE_INTEGRAL];
    ALL_TAC] THEN
  X_GEN_TAC `m:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `t:real`; `m:real`] P2BX_LINF_SUBLEVEL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(g':real->B->real^3^3)(&1 - t)`;
                 `\x. p2bx_uf (linf:real->B->real) t x * p2bx_hcut S linf t x`;
                 `{x | x IN topspace top' /\ (linf:real->B->real) t x < m}`;
                 `topspace top':B->bool`] P2BX_MFD_INTEGRAL_SUBSET_LE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MFD_LEBESGUE_MEASURABLE_OPEN] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `mfd_integral (top',atlas') ((g':real->B->real^3^3)(&1 - t))
                {x | x IN topspace top' /\ (linf:real->B->real) t x < m}
                (\x. p2bx_uf linf t x * p2bx_hcut S linf t x)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  REWRITE_TAC[mfd_integral] THEN AP_TERM_TAC THEN ABS_TAC THEN
  MATCH_MP_TAC MFD_HAS_INTEGRAL_EQ THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `x:B` THEN STRIP_TAC THEN
  REWRITE_TAC[p2bx_hcut] THEN
  SUBGOAL_THEN `p2bx_chi((linf:real->B->real) t x / S - &1) = &1`
  (fun th -> REWRITE_TAC[th; REAL_MUL_RID]) THENL
   [MP_TAC(SPEC `(linf:real->B->real) t x / S - &1` P2BX_CHI_BOUNDS) THEN
    DISCH_THEN(MATCH_MP_TAC o el 4 o CONJUNCTS) THEN
    ASM_SIMP_TAC[REAL_LE_SUB_RADD; REAL_LE_LDIV_EQ; REAL_ADD_LID] THEN ASM_REAL_ARITH_TAC;
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2BX_UF_RVOL_EQ THEN ASM_REWRITE_TAC[]]);;

(* I_S(t) -> V as S -> infinity. *)

let P2BX_IS_LIMIT = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf V t.
     P2B_LEMMA_9_25_STATEMENT (u:A->bool) /\ P2B_COR_9_10_STATEMENT u /\
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     p2bg_rvol (top',atlas') g' linf V /\ &0 < t
     ==> !e. &0 < e
             ==> ?N. !S. &N <= S /\ &0 < S
                         ==> V - e <= mfd_integral (top',atlas') (g'(&1 - t)) (topspace top')
                                        (\x. p2bx_uf linf t x * p2bx_hcut S linf t x)`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  SUBGOAL_THEN `riemannian_metric atlas' ((g':real->B->real^3^3)(&1 - t))` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX_LIMIT_RIEM THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                          `top':B topology`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `t:real` o GEN_REWRITE_RULE I [p2bg_rvol] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2bg_rvol")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. open_in top' {x | x IN topspace top' /\ (linf:real->B->real) t x < &n}`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                   `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                   `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                   `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                   `t:real`; `&n`] P2BX_LINF_SUBLEVEL) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                 `(g':real->B->real^3^3)(&1 - t)`;
                 `\y:B. exp(--((linf:real->B->real) t y)) / sqrt t pow 3`;
                 `\n. {x | x IN topspace top' /\ (linf:real->B->real) t x < &n}`; `V:real`]
                P2BX_MFD_MONO_UNIONS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[MFD_LEBESGUE_MEASURABLE_OPEN] THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
      GEN_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; GSYM REAL_OF_NUM_SUC] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      GEN_TAC THEN MATCH_MP_TAC MFD_INTEGRABLE_SUBSET THEN
      EXISTS_TAC `topspace top':B->bool` THEN
      ASM_SIMP_TAC[MFD_LEBESGUE_MEASURABLE_OPEN] THEN SET_TAC[];
      GEN_TAC THEN FIRST_ASSUM((fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) o check (fun th ->
        is_eq(concl th) && rand(concl th) = `V:real`)) THEN
      MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                     `(g':real->B->real^3^3)(&1 - t)`;
                     `\y:B. exp(--((linf:real->B->real) t y)) / sqrt t pow 3`;
                     `{x | x IN topspace top' /\ (linf:real->B->real) t x < &n}`;
                     `topspace top':B->bool`] P2BX_MFD_INTEGRAL_SUBSET_LE) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      ASM_SIMP_TAC[MFD_LEBESGUE_MEASURABLE_OPEN] THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS {{x | x IN topspace top' /\ (linf:real->B->real) t x < &n} | n IN (:num)} =
                topspace top'` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN X_GEN_TAC `x:B` THEN
    EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
    MP_TAC(SPEC `(linf:real->B->real) t x + &1` REAL_ARCH_SIMPLE) THEN
    DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
    EXISTS_TAC `{x | x IN topspace top' /\ (linf:real->B->real) t x < &n}` THEN
    CONJ_TAC THENL [EXISTS_TAC `n:num` THEN REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN STRIP_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
  X_GEN_TAC `S:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN REWRITE_TAC[LE_REFL] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `V:real`; `t:real`; `S:real`] P2BX_UH_SLICE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `&N` o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `!a. abs(a - V) < e /\ a <= i ==> V - e <= i`) THEN
  EXISTS_TAC `mfd_integral (top',atlas') ((g':real->B->real^3^3)(&1 - t))
                {x | x IN topspace top' /\ (linf:real->B->real) t x < &N}
                (\x. exp(--(linf t x)) / sqrt t pow 3)` THEN
  CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* ========================================================================= *)
(* Dominated convergence of the time integrals of the slices; the integral   *)
(* of the derivative of the time cutoff vanishes.                            *)
(* ========================================================================= *)

let P2BX_TIME_DOM = prove
 (`!(e:real->real) (Fn:num->real->real) V a b.
     (!s. e real_continuous atreal s) /\ &0 <= V /\
     (!n. (\y. lift(e(drop y) * Fn n (drop y))) integrable_on interval[lift a,lift b]) /\
     (!n t. a <= t /\ t <= b ==> &0 <= Fn n t /\ Fn n t <= V) /\
     (!t. a <= t /\ t <= b ==> ((\n. Fn n t) ---> V) sequentially)
     ==> ((\n. drop(integral (interval[lift a,lift b]) (\y. lift(e(drop y) * Fn n (drop y))))) --->
          drop(integral (interval[lift a,lift b]) (\y. lift(e(drop y) * V)))) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\n y. lift((e:real->real)(drop y) * (Fn:num->real->real) n (drop y))`;
                 `\y. lift((e:real->real)(drop y) * V)`;
                 `\y. lift(abs((e:real->real)(drop y)) * V)`;
                 `interval[lift a,lift b]`] DOMINATED_CONVERGENCE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
      SUBGOAL_THEN `(\y. lift(abs((e:real->real)(drop y)) * V)) =
                    (\y. lift((\s. abs(e s) * V) (drop y)))` SUBST1_TAC THENL
       [REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC P2BX_REAL_COMPOSE_CONT THEN CONJ_TAC THENL
       [GEN_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_RMUL THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ABS THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[LIFT_DROP; ETA_AX; CONTINUOUS_ON_ID]];
      MAP_EVERY X_GEN_TAC [`n:num`; `y:real^1`] THEN
      REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; NORM_LIFT; REAL_ABS_MUL; DROP_VEC] THEN
      STRIP_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `drop y`] o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `V:real`)) (concl th) &&
        not(can (find_term (fun t -> is_const t && fst(dest_const t) = "sequentially")) (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      X_GEN_TAC `y:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN STRIP_TAC THEN
      REWRITE_TAC[GSYM o_DEF; GSYM TENDSTO_REAL] THEN REWRITE_TAC[o_DEF] THEN
      MATCH_MP_TAC REALLIM_LMUL THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[REAL_TENDSTO; o_DEF]);;

let P2BX_DETA_INTEGRAL = prove
 (`!(eta:real->real) deta a b.
     (!t. (eta has_real_derivative deta t) (atreal t)) /\ a <= b /\ eta a = &0 /\ eta b = &0
     ==> integral (interval[lift a,lift b]) (\y. lift(deta(drop y))) = vec 0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MP_TAC(ISPECL [`lift o (eta:real->real) o drop`; `\y. lift((deta:real->real)(drop y))`;
                 `lift a`; `lift b`] FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  ASM_REWRITE_TAC[LIFT_DROP; o_THM; VECTOR_SUB_REFL; LIFT_NUM] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `y:real^1` THEN DISCH_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
  ONCE_REWRITE_TAC[GSYM LIFT_DROP] THEN REWRITE_TAC[GSYM HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

(* ========================================================================= *)
(* The lower integrand compared on each slice with the cut slices (-chi' <=  *)
(* 3/2 (1 - h_(R/2))); continuity in charts of time-weighted cut slices.     *)
(* ========================================================================= *)

let P2BX_DCHI_CUT_BOUND = prove
 (`!l R. &0 < R
         ==> --(p2bx_dchi(l / R - &1)) <= &3 / &2 * (&1 - p2bx_chi(l / (R / &2) - &1))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `l / R - &1` P2BX_CHI_BOUNDS) THEN
  MP_TAC(SPEC `l / (R / &2) - &1` P2BX_CHI_BOUNDS) THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `l / R - &1 <= &0 \/ &1 <= l / R - &1` THENL
   [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p2bx_chi(l / (R / &2) - &1) = &0` (fun th -> REWRITE_TAC[th]) THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_imp(concl th) &&
      can (find_term ((=) `R / &2`)) (concl th) &&
      can (find_term ((=) `&0`)) (rand(concl th)) &&
      not(can (find_term (fun t -> is_const t && fst(dest_const t) = "p2bx_dchi")) (concl th)) &&
      is_comb(lhand(concl th)) && fst(dest_comb(lhand(concl th))) = `(<=) (&1)`)) THEN
    SUBGOAL_THEN `l / (R / &2) = &2 * (l / R)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < R` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let P2BX_LOWF_PT = prove
 (`!a e d U hR hR2 dc.
     &0 < a /\ &0 <= e /\ &0 <= U /\ --dc <= &3 / &2 * (&1 - hR2)
     ==> --d * (U * hR) - &6 / a * (e * U - e * (U * hR2)) <=
         --(d * U * hR) - &4 / a * e * U * --dc`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `!z. y - x = z /\ &0 <= z ==> x <= y`) THEN
  EXISTS_TAC `&2 / a * (e * (U * (&3 * (&1 - hR2) + &2 * dc)))` THEN CONJ_TAC THENL
   [UNDISCH_TAC `&0 < a` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P2BX_EUH_CONT = prove
 (`!(om:real^(3,1)finite_sum->bool) (c:(B->bool)#(B->real^3)) linf (e:real->real) S.
     open om /\ &0 < S /\ wan_loclip om (p2bw_cfun c linf) /\
     wan_loclip om (p2bw_cfun c (p2bx_uf linf)) /\ (!s. e real_continuous atreal s)
     ==> (\z. lift(p2bw_cfun c (\t x. e t * (p2bx_uf linf t x * p2bx_hcut S linf t x)) z))
         continuous_on om`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p2bw_cfun (c:(B->bool)#(B->real^3))
                  (\t x. (e:real->real) t * (p2bx_uf linf t x * p2bx_hcut S (linf:real->B->real) t x)) =
                (\z. e(drop(sndcart z)) * (p2bw_cfun c (p2bx_uf linf) z * p2bw_cfun c (p2bx_hcut S linf) z))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; p2bw_cfun]; ALL_TAC] THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC WAN_CONT_LIFT_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2BX_REAL_COMPOSE_CONT THEN ASM_REWRITE_TAC[LIFT_DROP; ETA_AX] THEN
    MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_SNDCART];
    MATCH_MP_TAC WAN_CONT_LIFT_MUL THEN CONJ_TAC THEN
    MATCH_MP_TAC WAN_LOCLIP_CONTINUOUS_ON THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC P2BX_HCUT_LOCLIP THEN ASM_REWRITE_TAC[]]);;

(* The slice inequality for the lower integrand. *)

let P2BX_LOWF_SLICE_LB = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf V eta deta a R t.
     P2B_LEMMA_9_25_STATEMENT (u:A->bool) /\ P2B_COR_9_10_STATEMENT u /\
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     p2bg_rvol (top',atlas') g' linf V /\ &0 < a /\ a <= t /\ &0 < R /\ &0 <= eta t /\
     mfd_integrable_on (top',atlas') (g'(&1 - t)) (p2bx_lowf eta deta a R linf t) (topspace top')
     ==> --deta t * mfd_integral (top',atlas') (g'(&1 - t)) (topspace top')
                      (\x. p2bx_uf linf t x * p2bx_hcut R linf t x) -
         &6 / a * (eta t * V -
                   eta t * mfd_integral (top',atlas') (g'(&1 - t)) (topspace top')
                             (\x. p2bx_uf linf t x * p2bx_hcut (R / &2) linf t x)) <=
         mfd_integral (top',atlas') (g'(&1 - t)) (topspace top') (p2bx_lowf eta deta a R linf t)`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas' ((g':real->B->real^3^3)(&1 - t))` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX_LIMIT_RIEM THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                          `top':B topology`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `V:real`; `t:real`; `R:real`] P2BX_UH_SLICE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o REWRITE_RULE[MFD_INTEGRABLE_INTEGRAL] o CONJUNCT1) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `V:real`; `t:real`; `R / &2`] P2BX_UH_SLICE) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[MFD_INTEGRABLE_INTEGRAL] o CONJUNCT1) THEN
  FIRST_ASSUM(MP_TAC o SPEC `t:real` o GEN_REWRITE_RULE I [p2bg_rvol] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2bg_rvol")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_has_integral (top',atlas') ((g':real->B->real^3^3)(&1 - t))
                  (\y. exp(--((linf:real->B->real) t y)) / sqrt t pow 3) (topspace top') V`
  ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_integrable_on (top',atlas') ((g':real->B->real^3^3)(&1 - t))
                   (\y. exp(--((linf:real->B->real) t y)) / sqrt t pow 3) (topspace top')` THEN
    ASM_REWRITE_TAC[MFD_INTEGRABLE_INTEGRAL];
    ALL_TAC] THEN
  UNDISCH_TAC `mfd_integrable_on (top',atlas') ((g':real->B->real^3^3)(&1 - t))
                 (p2bx_lowf eta deta a R (linf:real->B->real) t) (topspace top')` THEN
  REWRITE_TAC[MFD_INTEGRABLE_INTEGRAL] THEN DISCH_TAC THEN
  MATCH_MP_TAC(INST_TYPE [`:B`,`:A`; `:3`,`:N`] MFD_HAS_INTEGRAL_LE) THEN
  MAP_EVERY EXISTS_TAC
   [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `(g':real->B->real^3^3)(&1 - t)`;
    `\x. --(deta:real->real) t * (p2bx_uf (linf:real->B->real) t x * p2bx_hcut R linf t x) -
         &6 / a * ((eta:real->real) t * (exp(--(linf t x)) / sqrt t pow 3) -
                   eta t * (p2bx_uf linf t x * p2bx_hcut (R / &2) linf t x))`;
    `p2bx_lowf eta deta a R (linf:real->B->real) t`; `topspace top':B->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(INST_TYPE [`:B`,`:A`; `:3`,`:N`] MFD_HAS_INTEGRAL_SUB) THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_HAS_INTEGRAL_CMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MFD_HAS_INTEGRAL_CMUL THEN
      MATCH_MP_TAC(INST_TYPE [`:B`,`:A`; `:3`,`:N`] MFD_HAS_INTEGRAL_SUB) THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THEN MATCH_MP_TAC MFD_HAS_INTEGRAL_CMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `x:B` THEN DISCH_TAC THEN REWRITE_TAC[p2bx_lowf] THEN
  SUBGOAL_THEN `exp(--((linf:real->B->real) t x)) / sqrt t pow 3 = p2bx_uf linf t x` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2BX_UF_RVOL_EQ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC P2BX_LOWF_PT THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[p2bx_uf; REAL_EXP_POS_LE];
    REWRITE_TAC[p2bx_hcut] THEN MATCH_MP_TAC P2BX_DCHI_CUT_BOUND THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Time-weighted cut slices are integrable in time; the global functional at *)
(* F_R is bounded below by an explicit combination of time integrals of cut  *)
(* slices.                                                                   *)
(* ========================================================================= *)

let P2BX_EUH_SLICE = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf V K a b k c om Ks rho e S R.
     P2B_LEMMA_9_25_STATEMENT (u:A->bool) /\ P2B_COR_9_10_STATEMENT u /\
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     p2bg_rvol (top',atlas') g' linf V /\
     p2bx_pdata atlas' K a b k c om Ks rho /\ &0 < a /\ &0 < S /\ S <= R /\
     (!s. e real_continuous atreal s) /\ (!t. ~(e t = &0) ==> a <= t /\ t <= b) /\
     (!t x. x IN topspace top' /\ a <= t /\ t <= b /\ linf t x < &2 * R ==> x IN K)
     ==> (\y. lift(e(drop y) * mfd_integral (top',atlas') (g'(&1 - drop y)) (topspace top')
                                 (\x. p2bx_uf linf (drop y) x * p2bx_hcut S linf (drop y) x)))
         integrable_on interval[lift a,lift b]`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `K:B->bool`; `a:real`; `b:real`; `k:num`;
                 `c:num->(B->bool)#(B->real^3)`; `om:num->real^(3,1)finite_sum->bool`;
                 `Ks:num->real^3->bool`; `rho:num->B->real`;
                 `\t x. (e:real->real) t * (p2bx_uf (linf:real->B->real) t x * p2bx_hcut S linf t x)`]
                P2BX_SLICE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`t:real`; `x:B`] THEN REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM] THEN
      STRIP_TAC THEN ASM_SIMP_TAC[];
      MAP_EVERY X_GEN_TAC [`t:real`; `x:B`] THEN REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM] THEN
      STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `t:real` THEN
      ASM_SIMP_TAC[] THEN
      UNDISCH_TAC `~(p2bx_hcut S (linf:real->B->real) t x = &0)` THEN
      REWRITE_TAC[p2bx_hcut] THEN
      ASM_CASES_TAC `&2 * S <= (linf:real->B->real) t x` THENL
       [ALL_TAC; DISCH_TAC THEN ASM_REAL_ARITH_TAC] THEN
      SUBGOAL_THEN `&1 <= (linf:real->B->real) t x / S - &1` ASSUME_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_SUB_LADD; REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPEC `(linf:real->B->real) t x / S - &1` P2BX_CHI_BOUNDS) THEN ASM_SIMP_TAC[];
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`; `K:B->bool`;
                     `a:real`; `b:real`; `k:num`; `c:num->(B->bool)#(B->real^3)`;
                     `om:num->real^(3,1)finite_sum->bool`; `Ks:num->real^3->bool`;
                     `rho:num->B->real`; `j:num`] P2BX_PDATA_MEMBER) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                     `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                     `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                     `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                     `(c:num->(B->bool)#(B->real^3)) j`; `(om:num->real^(3,1)finite_sum->bool) j`]
                    P2BX_BOX_UF) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MATCH_MP_TAC P2BX_EUH_CONT THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN MATCH_MP_TAC P2BX_RVOL_ZERO THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                            `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `linf:real->B->real`;
                            `V:real`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o MATCH_MP HAS_INTEGRAL_INTEGRABLE)) THEN
  MATCH_MP_TAC INTEGRABLE_EQ THEN
  EXISTS_TAC `\y. lift(mfd_integral (top',atlas') ((g':real->B->real^3^3)(&1 - drop y)) (topspace top')
                    ((\t x. (e:real->real) t * (p2bx_uf (linf:real->B->real) t x * p2bx_hcut S linf t x))
                     (drop y)))` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
  STRIP_TAC THEN REWRITE_TAC[LIFT_EQ] THEN
  SUBGOAL_THEN `&0 < drop y` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas' ((g':real->B->real^3^3)(&1 - drop y))` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX_LIMIT_RIEM THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                          `top':B topology`; `xl:B`; `W:num->B->bool`; `phi:num->B->A`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `V:real`; `drop y`; `S:real`] P2BX_UH_SLICE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MFD_HAS_INTEGRAL_CMUL o REWRITE_RULE[MFD_INTEGRABLE_INTEGRAL] o
    CONJUNCT1) THEN
  DISCH_THEN(ASSUME_TAC o BETA_RULE o SPEC `(e:real->real)(drop y)`) THEN
  MATCH_MP_TAC(INST_TYPE [`:B`,`:A`; `:3`,`:N`] MFD_HAS_INTEGRAL_UNIQUE) THEN
  MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                        `(g':real->B->real^3^3)(&1 - drop y)`;
                        `\x. (e:real->real)(drop y) *
                             (p2bx_uf (linf:real->B->real) (drop y) x * p2bx_hcut S linf (drop y) x)`;
                        `topspace top':B->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM MFD_INTEGRABLE_INTEGRAL] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `drop y` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_integrable_on")) (concl th))) THEN
  ASM_REWRITE_TAC[]);;

(* The cut slices as a function of time. *)

let p2bx_islice = new_definition
 `p2bx_islice (top':B topology,atlas':((B->bool)#(B->real^3))->bool) (g':real->B->real^3^3)
              (linf:real->B->real) (S:real) (t:real) =
    mfd_integral (top',atlas') (g'(&1 - t)) (topspace top')
      (\x. p2bx_uf linf t x * p2bx_hcut S linf t x)`;;

let P2BX_CUT_SEQ_BOUND = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf V K a b k c om Ks rho eta deta R.
     P2B_LEMMA_9_25_STATEMENT (u:A->bool) /\ P2B_COR_9_10_STATEMENT u /\
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     p2bg_rvol (top',atlas') g' linf V /\
     p2bx_pdata atlas' K a b k c om Ks rho /\ &0 < a /\ &0 < R /\
     smooth_map_on (:real^1) (\s. lift(eta(drop s))) /\
     (!t. (eta has_real_derivative deta t) (atreal t)) /\
     (!s. deta real_continuous atreal s) /\
     (!t. ~(eta t = &0) ==> a <= t /\ t <= b) /\ (!t. ~(deta t = &0) ==> a <= t /\ t <= b) /\
     (!t. &0 <= eta t) /\
     (!t x. x IN topspace top' /\ a <= t /\ t <= b /\ linf t x < &2 * R ==> x IN K)
     ==> --drop(integral (interval[lift a,lift b])
                  (\y. lift(deta(drop y) * p2bx_islice (top',atlas') g' linf R (drop y)))) -
         &6 / a * (V * drop(integral (interval[lift a,lift b]) (\y. lift(eta(drop y)))) -
                   drop(integral (interval[lift a,lift b])
                     (\y. lift(eta(drop y) * p2bx_islice (top',atlas') g' linf (R / &2) (drop y))))) <=
         sum(1..k) (\j. drop(integral (om j)
           (\z. lift(p2bw_cfun (c j) (\t:real. rho j) z *
                     p2bx_wint atlas' g' (c j) (p2bx_uf linf)
                               (p2bw_cfun (c j) (p2bx_fcut top' eta R linf)) z))))`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS) THEN
  SUBGOAL_THEN `!s. (eta:real->real) real_continuous atreal s` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
    EXISTS_TAC `(deta:real->real) s` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `K:B->bool`; `a:real`; `b:real`; `k:num`;
                 `c:num->(B->bool)#(B->real^3)`; `om:num->real^(3,1)finite_sum->bool`;
                 `Ks:num->real^3->bool`; `rho:num->B->real`; `eta:real->real`; `deta:real->real`;
                 `R:real`] P2BX_GFUN_CUT_LB) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN MATCH_MP_TAC P2BX_RVOL_ZERO THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                          `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `linf:real->B->real`;
                          `V:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (interval[lift a,lift b])
               (\y. lift(mfd_integral (top',atlas') ((g':real->B->real^3^3)(&1 - drop y))
                       (topspace top') (p2bx_lowf eta deta a R (linf:real->B->real) (drop y)))))` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `V:real`; `K:B->bool`; `a:real`; `b:real`; `k:num`;
                 `c:num->(B->bool)#(B->real^3)`; `om:num->real^(3,1)finite_sum->bool`;
                 `Ks:num->real^3->bool`; `rho:num->B->real`; `deta:real->real`; `R:real`; `R:real`]
                P2BX_EUH_SLICE) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; GSYM p2bx_islice] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `V:real`; `K:B->bool`; `a:real`; `b:real`; `k:num`;
                 `c:num->(B->bool)#(B->real^3)`; `om:num->real^(3,1)finite_sum->bool`;
                 `Ks:num->real^3->bool`; `rho:num->B->real`; `eta:real->real`; `R / &2`; `R:real`]
                P2BX_EUH_SLICE) THEN
  ASM_REWRITE_TAC[REAL_HALF; GSYM p2bx_islice] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `(\y. lift((eta:real->real)(drop y))) integrable_on interval[lift a,lift b]` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC P2BX_REAL_COMPOSE_CONT THEN ASM_REWRITE_TAC[LIFT_DROP; ETA_AX; CONTINUOUS_ON_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\y. lift(--(deta:real->real)(drop y) * p2bx_islice (top',atlas') g' (linf:real->B->real) R (drop y) -
              &6 / a * (eta(drop y) * V - eta(drop y) * p2bx_islice (top',atlas') g' linf (R / &2) (drop y)))) =
    (\y. --(lift(deta(drop y) * p2bx_islice (top',atlas') g' linf R (drop y))) -
         &6 / a % (V % lift(eta(drop y)) - lift(eta(drop y) * p2bx_islice (top',atlas') g' linf (R / &2) (drop y))))`
  ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    REWRITE_TAC[GSYM LIFT_NEG; GSYM LIFT_CMUL; GSYM LIFT_SUB; LIFT_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (interval[lift a,lift b])
    (\y. lift(--(deta:real->real)(drop y) * p2bx_islice (top',atlas') g' (linf:real->B->real) R (drop y) -
              &6 / a * (eta(drop y) * V - eta(drop y) * p2bx_islice (top',atlas') g' linf (R / &2) (drop y)))))` THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `integral (interval[lift a,lift b])
        (\y. --(lift((deta:real->real)(drop y) * p2bx_islice (top',atlas') g' (linf:real->B->real) R (drop y))) -
             &6 / a % (V % lift((eta:real->real)(drop y)) -
                       lift(eta(drop y) * p2bx_islice (top',atlas') g' linf (R / &2) (drop y)))) =
      --integral (interval[lift a,lift b])
          (\y. lift(deta(drop y) * p2bx_islice (top',atlas') g' linf R (drop y))) -
      &6 / a % (V % integral (interval[lift a,lift b]) (\y. lift(eta(drop y))) -
                integral (interval[lift a,lift b])
                  (\y. lift(eta(drop y) * p2bx_islice (top',atlas') g' linf (R / &2) (drop y))))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC INTEGRAL_UNIQUE THEN
      MATCH_MP_TAC HAS_INTEGRAL_SUB THEN CONJ_TAC THENL
       [MATCH_MP_TAC HAS_INTEGRAL_NEG THEN MATCH_MP_TAC INTEGRABLE_INTEGRAL THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC HAS_INTEGRAL_CMUL THEN MATCH_MP_TAC HAS_INTEGRAL_SUB THEN CONJ_TAC THENL
         [MATCH_MP_TAC HAS_INTEGRAL_CMUL THEN MATCH_MP_TAC INTEGRABLE_INTEGRAL THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC INTEGRABLE_INTEGRAL THEN ASM_REWRITE_TAC[]]];
      REWRITE_TAC[DROP_SUB; DROP_NEG; DROP_CMUL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_SUB THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_NEG THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC INTEGRABLE_CMUL THEN MATCH_MP_TAC INTEGRABLE_SUB THEN
      ASM_SIMP_TAC[INTEGRABLE_CMUL]];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN STRIP_TAC THEN
  REWRITE_TAC[p2bx_islice] THEN
  MATCH_MP_TAC P2BX_LOWF_SLICE_LB THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                        `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                        `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`] THEN
  ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* The lower bounds of the global functional at the cutoffs tend to 0        *)
(* (R -> infinity).                                                          *)
(* ========================================================================= *)

let P2BX_ISLICE_CONV = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf V t (S:num->real).
     P2B_LEMMA_9_25_STATEMENT (u:A->bool) /\ P2B_COR_9_10_STATEMENT u /\
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     p2bg_rvol (top',atlas') g' linf V /\ &0 < t /\
     (!n. &0 < S n) /\ (!M. ?N. !n. N <= n ==> M <= S n)
     ==> ((\n. p2bx_islice (top',atlas') g' linf (S n) t) ---> V) sequentially`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY; p2bx_islice] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `V:real`; `t:real`] P2BX_IS_LIMIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&N0` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `S:num->real`)) (concl th) && is_exists(snd(dest_forall(concl th))))) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                 `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                 `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                 `V:real`; `t:real`; `(S:num->real) n`] P2BX_UH_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(S:num->real) n` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `e / &2`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2BX_CUT_SEQ_LIMIT = prove
 (`!(top:A topology) atlas (g:real->A->real^3^3) p tau q
    (top':B topology) atlas' g' xl W phi sub linf V a b eta deta R0.
     P2B_LEMMA_9_25_STATEMENT (u:A->bool) /\ P2B_COR_9_10_STATEMENT u /\
     P2B_FLOW_CHART_STATEMENT (w:B->bool) (:3) /\
     p2bg_setup (top,atlas) g p tau q (top',atlas') g' xl W phi /\
     p2bg_g1out (top,atlas) g p tau (top',atlas') g' W phi sub linf /\
     p2bg_rvol (top',atlas') g' linf V /\ &0 < a /\ a <= b /\ &0 < R0 /\
     (!t. (eta has_real_derivative deta t) (atreal t)) /\ (!s. deta real_continuous atreal s) /\
     eta a = &0 /\ eta b = &0 /\
     (!n. (\y. lift(deta(drop y) * p2bx_islice (top',atlas') g' linf (R0 + &n) (drop y)))
          integrable_on interval[lift a,lift b]) /\
     (!n. (\y. lift(eta(drop y) * p2bx_islice (top',atlas') g' linf ((R0 + &n) / &2) (drop y)))
          integrable_on interval[lift a,lift b])
     ==> ((\n. --drop(integral (interval[lift a,lift b])
                        (\y. lift(deta(drop y) * p2bx_islice (top',atlas') g' linf (R0 + &n) (drop y)))) -
               &6 / a * (V * drop(integral (interval[lift a,lift b]) (\y. lift(eta(drop y)))) -
                         drop(integral (interval[lift a,lift b])
                           (\y. lift(eta(drop y) *
                                     p2bx_islice (top',atlas') g' linf ((R0 + &n) / &2) (drop y))))))
          ---> &0) sequentially`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `!s. (eta:real->real) real_continuous atreal s` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
    EXISTS_TAC `(deta:real->real) s` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2BX_SETUP_FACTS o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2bg_setup")) (concl th))) THEN
  SUBGOAL_THEN `&0 <= V` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                   `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                   `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                   `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                   `V:real`; `a:real`; `&1`] P2BX_UH_SLICE) THEN
    ASM_REWRITE_TAC[REAL_LT_01] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the two time-dominated limits *)
  SUBGOAL_THEN
   `!(e:real->real) (S:num->real).
       (!s. e real_continuous atreal s) /\ (!n. &0 < S n) /\ (!M. ?N. !n. N <= n ==> M <= S n) /\
       (!n. (\y. lift(e(drop y) * p2bx_islice (top',atlas') g' (linf:real->B->real) (S n) (drop y)))
            integrable_on interval[lift a,lift b])
       ==> ((\n. drop(integral (interval[lift a,lift b])
                   (\y. lift(e(drop y) * p2bx_islice (top',atlas') g' linf (S n) (drop y))))) --->
            V * drop(integral (interval[lift a,lift b]) (\y. lift(e(drop y))))) sequentially`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`e:real->real`; `\n t. p2bx_islice (top',atlas') g' (linf:real->B->real) ((S:num->real) n) t`;
                   `V:real`; `a:real`; `b:real`] P2BX_TIME_DOM) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MAP_EVERY X_GEN_TAC [`n:num`; `t:real`] THEN STRIP_TAC THEN
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:real->A->real^3^3`;
                       `p:A`; `tau:num->real`; `q:num->A`; `top':B topology`;
                       `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`; `xl:B`;
                       `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`; `linf:real->B->real`;
                       `V:real`; `t:real`; `(S:num->real) n`] P2BX_UH_SLICE) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        SIMP_TAC[p2bx_islice];
        X_GEN_TAC `t:real` THEN STRIP_TAC THEN MATCH_MP_TAC P2BX_ISLICE_CONV THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                              `g:real->A->real^3^3`; `p:A`; `tau:num->real`; `q:num->A`;
                              `xl:B`; `W:num->B->bool`; `phi:num->B->A`; `sub:num->num`] THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `(\y. lift((e:real->real)(drop y) * V)) = (\y. V % lift(e(drop y)))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_CMUL; REAL_MUL_SYM]; ALL_TAC] THEN
    SUBGOAL_THEN `(\y. lift((e:real->real)(drop y))) integrable_on interval[lift a,lift b]` ASSUME_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
      MATCH_MP_TAC P2BX_REAL_COMPOSE_CONT THEN ASM_REWRITE_TAC[LIFT_DROP; ETA_AX; CONTINUOUS_ON_ID];
      ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!M. ?N. !n. N <= n ==> M <= R0 + &n` ASSUME_TAC THENL
   [GEN_TAC THEN MP_TAC(SPEC `M:real` REAL_ARCH_SIMPLE) THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
    EXISTS_TAC `N:num` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REPEAT STRIP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`deta:real->real`; `\n. R0 + &n`]) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`eta:real->real`; `\n. (R0 + &n) / &2`]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `&2 * M`) THEN
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
      MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN REAL_ARITH_TAC];
    DISCH_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `drop(integral (interval[lift a,lift b]) (\y. lift((deta:real->real)(drop y)))) = &0`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`eta:real->real`; `deta:real->real`; `a:real`; `b:real`] P2BX_DETA_INTEGRAL) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[DROP_VEC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 = --(V * &0) - &6 / a * (V * drop(integral (interval[lift a,lift b])
                                                    (\y. lift((eta:real->real)(drop y)))) -
                                           V * drop(integral (interval[lift a,lift b])
                                                    (\y. lift(eta(drop y)))))`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_SUB THEN CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_NEG THEN FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term ((=) `deta:real->real`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "sequentially")) (concl th) &&
      not(is_forall(concl th)))) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REALLIM_LMUL THEN MATCH_MP_TAC REALLIM_SUB THEN
    REWRITE_TAC[REALLIM_CONST] THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The smooth time cutoff eta (= 1 on the time range of a test, supported in *)
(* (a,b)), its derivative.                                                   *)
(* ========================================================================= *)

let P2BX_ETA_EXISTS = prove
 (`!a b t1 t2.
     a < t1 /\ t1 <= t2 /\ t2 < b
     ==> ?eta deta.
           smooth_map_on (:real^1) (\s. lift(eta(drop s))) /\
           (!t. (eta has_real_derivative deta t) (atreal t)) /\
           (!s. deta real_continuous atreal s) /\
           (!t. ~(eta t = &0) ==> a <= t /\ t <= b) /\
           (!t. ~(deta t = &0) ==> a <= t /\ t <= b) /\
           (!t. &0 <= eta t /\ eta t <= &1) /\
           (!t. t1 <= t /\ t <= t2 ==> eta t = &1) /\ eta a = &0 /\ eta b = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`interval(lift a,lift b)`; `interval[lift t1,lift t2]`] WAN_SMOOTH_URYSOHN) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[OPEN_INTERVAL; COMPACT_INTERVAL; SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:real^1->real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_test]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `kk:real^1->bool` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `\t. (psi:real^1->real)(lift t)` THEN
  EXISTS_TAC `\t. drop(frechet_derivative (\y. lift((psi:real^1->real) y)) (at (lift t)) (lift(&1)))` THEN
  REWRITE_TAC[LIFT_DROP; ETA_AX] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!t. lift t IN kk ==> a <= t /\ t <= b` ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `lift t IN interval(lift a,lift b)` MP_TAC THENL
     [ASM SET_TAC[]; REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(lift a IN kk) /\ ~(lift b IN kk)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `!y. y IN kk ==> y IN interval(lift a,lift b)` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THEN DISCH_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `lift a IN kk`));
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `lift b IN kk`))] THEN
    REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* the derivative *)
    X_GEN_TAC `t:real` THEN REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT] THEN
    SUBGOAL_THEN `(lift o (\t. (psi:real^1->real)(lift t)) o drop) = (\y. lift(psi y))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
    SUBGOAL_THEN `(\y. lift((psi:real^1->real) y)) differentiable at (lift t)` ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^1)` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\x. drop(frechet_derivative (\y. lift((psi:real^1->real) y)) (at (lift t)) (lift(&1))) % x) =
      frechet_derivative (\y. lift(psi y)) (at (lift t))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^1` THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM LIFT_DROP] THEN
      SUBGOAL_THEN `lift(drop x) = drop x % lift(&1)` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM LIFT_CMUL; REAL_MUL_RID]; ALL_TAC] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM LIFT_DROP] THEN
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM LIFT_DROP] THEN
      REWRITE_TAC[GSYM LIFT_CMUL; LIFT_EQ] THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]];
    (* continuity of the derivative *)
    X_GEN_TAC `s:real` THEN REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS_ATREAL] THEN
    MP_TAC(ISPECL [`psi:real^1->real`; `lift(&1)`] WAN_TEST_DERIV_TEST) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[wan_test; SUBSET_UNIV] THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `kk:real^1->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[wan_test] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON) THEN
    DISCH_THEN(MP_TAC o SPEC `lift s` o REWRITE_RULE[IN_UNIV] o
      GEN_REWRITE_RULE I [MATCH_MP CONTINUOUS_ON_EQ_CONTINUOUS_AT OPEN_UNIV]) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP];
    (* support of eta *)
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
    UNDISCH_TAC `~((psi:real^1->real)(lift t) = &0)` THEN ASM_SIMP_TAC[];
    (* support of the derivative *)
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(drop(frechet_derivative (\y. lift((psi:real^1->real) y)) (at (lift t))
                    (lift(&1))) = &0)` THEN
    MP_TAC(ISPECL [`psi:real^1->real`; `kk:real^1->bool`; `lift(&1)`; `lift t`] WAN_TEST_DERIV_ZERO) THEN
    ASM_SIMP_TAC[DROP_VEC];
    (* values *)
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP];
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[]]);;

(* ========================================================================= *)
(* Facts about the guarded cutoffs F_R and about combinations M F_R - Psi in *)
(* charts.                                                                   *)
(* ========================================================================= *)

let P2BX_LOCLIP_LINCOMB = prove
 (`!(s:real^M->bool) f h (M:real).
     wan_loclip s f /\ wan_loclip s h ==> wan_loclip s (\x. M * f x - h x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_loclip] THEN STRIP_TAC THEN
  X_GEN_TAC `k:real^M->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `L2:real`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `L1:real`) THEN
  EXISTS_TAC `abs M * abs L1 + abs L2` THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^M`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^M`; `y:real^M`]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^M`; `y:real^M`]) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `x - y:real^M` NORM_POS_LE) THEN
  SUBGOAL_THEN `M * (f:real^M->real) x - h x - (M * f y - h y) = M * (f x - f y) - (h x - h y)`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs M * abs((f:real^M->real) x - f y) + abs(h x - h y)` THEN
  CONJ_TAC THENL [REWRITE_TAC[GSYM REAL_ABS_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `L1 * norm(x - y:real^M)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `L2 * norm(x - y:real^M)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* The guarded cutoffs. *)

let P2BX_FCUT_FACTS = prove
 (`!(top':B topology) (eta:real->real) R linf a b.
     &0 < R /\ (!t. &0 <= eta t) /\ (!t. ~(eta t = &0) ==> a <= t /\ t <= b)
     ==> (!t x. &0 <= p2bx_fcut top' eta R linf t x) /\
         (!t x. ~(p2bx_fcut top' eta R linf t x = &0)
                ==> x IN topspace top' /\ a <= t /\ t <= b /\ linf t x < &2 * R)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[p2bx_fcut; p2bx_hcut] THEN COND_CASES_TAC THEN
    REWRITE_TAC[REAL_LE_REFL] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[P2BX_CHI_BOUNDS];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bx_fcut; p2bx_hcut] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN
  ASM_CASES_TAC `&2 * R <= (linf:real->B->real) t x` THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `&1 <= (linf:real->B->real) t x / R - &1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_SUB_LADD; REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `~(p2bx_chi((linf:real->B->real) t x / R - &1) = &0)` THEN
  MP_TAC(SPEC `(linf:real->B->real) t x / R - &1` P2BX_CHI_BOUNDS) THEN ASM_SIMP_TAC[]);;

let P2BX_FCUT_LOCLIP = prove
 (`!(top':B topology) atlas' (c:(B->bool)#(B->real^3)) om (eta:real->real) R linf.
     smooth_manifold_atlas top' atlas' /\ c IN atlas' /\ open om /\
     om SUBSET {z | fstcart z IN IMAGE (SND c) (FST c)} /\
     wan_loclip om (p2bw_cfun c linf) /\ &0 < R /\
     smooth_map_on (:real^1) (\s. lift(eta(drop s)))
     ==> wan_loclip om (p2bw_cfun c (p2bx_fcut top' eta R linf))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BX_LOCLIP_EQ THEN
  EXISTS_TAC `\w. (eta:real->real)(drop(sndcart w)) * p2bw_cfun (c:(B->bool)#(B->real^3))
                    (p2bx_hcut R (linf:real->B->real)) w` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2BW_LOCLIP_MUL THEN ASM_REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2BX_LOCLIP_SUBSET THEN EXISTS_TAC `(:real^(3,1)finite_sum)` THEN
      REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC P2BX_SMOOTH_LOCLIP THEN
      ASM_SIMP_TAC[OPEN_UNIV; P2BX_ETA_SMOOTH];
      MATCH_MP_TAC P2BX_HCUT_LOCLIP THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `z:real^(3,1)finite_sum` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                   `c:(B->bool)#(B->real^3)`; `eta:real->real`; `R:real`; `linf:real->B->real`;
                   `z:real^(3,1)finite_sum`] P2BX_FCUT_CFUN) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[p2bw_cfun]]);;

let P2BX_MFUN_LOCLIP = prove
 (`!(top':B topology) atlas' (c0:(B->bool)#(B->real^3)) c om psi kp.
     hausdorff_space top' /\ smooth_manifold_atlas top' atlas' /\ c0 IN atlas' /\ c IN atlas' /\
     om SUBSET {z | fstcart z IN IMAGE (SND c) (FST c)} /\
     smooth_map_on (:real^(3,1)finite_sum) (\z. lift(psi z)) /\
     compact kp /\ IMAGE fstcart kp SUBSET IMAGE (SND c0) (FST c0) /\
     (!z. ~(z IN kp) ==> psi z = &0)
     ==> wan_loclip om (p2bw_cfun c (p2bx_mfun c0 psi))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BX_LOCLIP_SUBSET THEN
  EXISTS_TAC `{z:real^(3,1)finite_sum | fstcart z IN IMAGE (SND(c:(B->bool)#(B->real^3))) (FST c)}` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BX_SMOOTH_LOCLIP THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2BX_OPEN_CHART_CYL THEN
    MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2BX_MFUN_SMOOTH THEN
    MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                          `kp:real^(3,1)finite_sum->bool`] THEN
    ASM_REWRITE_TAC[]]);;

