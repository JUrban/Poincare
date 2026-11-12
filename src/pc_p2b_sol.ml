(* ========================================================================= *)
(* pc_p2b_sol: the leaf P2B_SOLITON_FROM_LINF of the THM_9_11 route (MT     *)
(* Sections 2.7-2.8, Prop 9.32 with Lemma 9.33, Claims 9.34-9.36), in the   *)
(* corrected form P2B_SOLITON_FROM_LINF_FIX (pc_p2b_gaussreq: the original  *)
(* statement plus ~(topspace top = {})) and in route form:                  *)
(*   P2B_SOLITON_FROM_LINF_FIX_ROUTE |- !w. P2B_REQ_FLAT_GAUSS_STATEMENT w   *)
(*                                ==> P2B_SOLITON_FROM_LINF_FIX_STATEMENT w. *)
(*                                                                           *)
(* Part A (the shrinker equation at every time).  In a chart, in forward    *)
(* time t = 1 - tau on the local Ricci flow G of the chart metric, F(t,y) = *)
(* linf(1 - t)(chart_inv c y) satisfies dF/dt = |grad F|^2 - Lap F - R +    *)
(* n/(2(1 - t)) ((9.4)) and W = (1 - t)(2 Lap F - |grad F|^2 + R) + F = n   *)
(* ((9.5)).  The heat calculus of pc_rfa_hcalc and pc_rfa_htens gives the   *)
(* heat defects of F, dF, Hess F, |dF|^2, Lap F, R and W; W constant gives   *)
(* zero defect, and the defect is 2(1 - t)|Ric + Hess F - G/(2(1 - t))|^2   *)
(* (P2BS_LOCAL_SOLITON: MT Lemma 9.33 in a chart, general N).  The tau-     *)
(* chart data of the statement are converted (P2BS_CHART_EQS) and the       *)
(* equation passes to p2b_shrinker of g(s)/(1 - s) by scale invariance      *)
(* (P2BS_SHRINKER).                                                          *)
(*                                                                           *)
(* Part B (no flat slice).  A flat slice has Ric = 0 (APX_CONST_CURV_       *)
(* RIEMANN), Hess f = g/(2 tau) and |grad f|^2 = f/tau ((9.5) with Lap f =  *)
(* 3/(2 tau)) (P2BS_FLAT_SLICE), so the route input FLAT_GAUSS gives a       *)
(* reduced volume at least (4 pi)^(3/2), contradicting V < (4 pi)^(3/2)      *)
(* (P2BS_NONFLAT).                                                           *)
(* ========================================================================= *)

needs "src/pc_p2b_gaussreq.ml";;
needs "src/pc_rfa_htens.ml";;
needs "src/pc_p2b_fchart.ml";;
needs "src/pc_p2c_cdiff.ml";;
needs "src/pc_rfa_rmnorm.ml";;
needs "src/pc_rfa_slcalc.ml";;
needs "src/pc_rfa_ricid.ml";;
needs "src/pc_lrg_constcurv.ml";;
needs "src/pc_lrg_stab.ml";;
needs "src/pc_rfa_maxp.ml";;
needs "src/pc_cmp_pull.ml";;
needs "src/pc_rfa_lalg.ml";;
needs "src/pc_rfa_talg.ml";;

prioritize_real();;
type_invention_error := true;;

(* SOL.A1 Heat calculus for functions along a local Ricci flow: slices of  *)
(* jointly smooth functions, smoothness of llap and lgrad2, the covariant  *)
(* derivative of a function, and the heat equation of a jointly smooth     *)
(* function Ff with defect dF/dt - Lap Ff (rfa_heat 0 of pc_rfa_hcalc).      *)

let P2BS_LNABLA0 = prove
 (`!(G:real^N->real^N^N) (f:real^N->real) y u.
     lnabla 0 G (\z u. f z) y u = drop(frechet_derivative (\x. lift(f x)) (at y) (u 1))`,
  REWRITE_TAC[lnabla; ADD_CLAUSES; SUM_CLAUSES_NUMSEG; ARITH; REAL_SUB_RZERO]);;

let P2BS_SLICE_SMOOTH = prove
 (`!U a b (Ff:real->real^N->real) t.
     open U /\ a < t /\ t < b /\
     smooth_map_on (interval(lift a,lift b) PCROSS U)
       (\z. lift(Ff (drop(fstcart z)) (sndcart z)))
     ==> smooth_map_on U (\y. lift(Ff t y))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z:real^(1,N)finite_sum. lift((Ff:real->real^N->real) (drop(fstcart z)) (sndcart z))`;
                 `a:real`; `b:real`; `U:real^N->bool`; `t:real`] RFA_SMOOTH_MAP_ON_SLICE) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP]);;

let P2BS_DF_FIELD = prove
 (`!U (G:real^N->real^N^N) (f:real^N->real).
     metric_field U G /\ smooth_map_on U (\y. lift(f y))
     ==> ltensor_field 1 U (lnabla 0 G (\z u. f z)) /\
         (!u. smooth_map_on U (\y. lift(lnabla 0 G (\z u. f z) y u)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`0`; `U:real^N->bool`; `G:real^N->real^N^N`; `\z:real^N u:num->real^N. (f:real^N->real) z`]
                LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[RFA_TENSOR_FIELD_0; ADD_CLAUSES; ETA_AX]);;

let P2BS_LLAP_SMOOTH = prove
 (`!U (G:real^N->real^N^N) (f:real^N->real).
     metric_field U G /\ smooth_map_on U (\y. lift(f y))
     ==> smooth_map_on U (\y. lift(llap G f y))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `\y. lift(ltlap 0 (G:real^N->real^N^N) (\x u. (f:real^N->real) x) y (\m. vec 0))` THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC RFA_LTLAP_0 THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`0`; `U:real^N->bool`; `G:real^N->real^N^N`; `\z:real^N u:num->real^N. (f:real^N->real) z`]
                  RFA_LTLAP_FIELD) THEN
    ASM_REWRITE_TAC[RFA_TENSOR_FIELD_0; ETA_AX] THEN SIMP_TAC[]]);;

let P2BS_LGRAD2_SMOOTH = prove
 (`!U (G:real^N->real^N^N) (f:real^N->real).
     metric_field U G /\ smooth_map_on U (\y. lift(f y))
     ==> smooth_map_on U (\y. lift(lgrad2 G f y))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[P2C_LGRAD2_LTNORM2] THEN
  MATCH_MP_TAC LRG_LTNORM2_SMOOTH THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `f:real^N->real`] P2BS_DF_FIELD) THEN
  ASM_SIMP_TAC[]);;

let P2BS_HEAT_FUN = prove
 (`!U a b (G:real->real^N->real^N^N) (Ff:real->real^N->real) (DFf:real->real^N->real).
     lricci_flow U a b G /\
     smooth_map_on (interval(lift a,lift b) PCROSS U)
       (\z. lift(Ff (drop(fstcart z)) (sndcart z))) /\
     (!t. a < t /\ t < b ==> smooth_map_on U (\y. lift(DFf t y))) /\
     (!t y. a < t /\ t < b /\ y IN U
            ==> ((\s. Ff s y) has_real_derivative DFf t y) (atreal t))
     ==> rfa_heat 0 U a b G (\t y u. Ff t y)
                            (\t y u. DFf t y - llap (G t) (Ff t) y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
  SUBGOAL_THEN `!t. a < t /\ t < b ==> smooth_map_on U (\y. lift((Ff:real->real^N->real) t y))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BS_SLICE_SMOOTH THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[rfa_heat; RFA_TENSOR_FIELD_0] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `\y. lift((DFf:real->real^N->real) t y)`;
                   `\y. lift(llap ((G:real->real^N->real^N^N) t) ((Ff:real->real^N->real) t) y)`]
                  SMOOTH_MAP_ON_LIFT_SUB) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC P2BS_LLAP_SMOOTH THEN ASM_SIMP_TAC[];
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`; `u:num->real^N`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `(Ff:real->real^N->real) t`;
                   `y:real^N`; `u:num->real^N`] RFA_LTLAP_0) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[ETA_AX]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[rfa_rcact; SUM_CLAUSES_NUMSEG; ARITH] THEN
    REWRITE_TAC[REAL_ARITH `l - &0 + (d - l) = d`] THEN ASM_SIMP_TAC[]]);;

(* SOL.A2 Heat equations of dF, Hess F, Lap F and |grad F|^2 for a function *)
(* F solving the heat equation with defect along a local Ricci flow (rules *)
(* RFA_HEAT_LNABLA, RFA_HEAT_LTPROD, RFA_HEAT_LTCONTR of pc_rfa_hcalc), and *)
(* the identification of the contracted fields with llap and lgrad2.       *)

let P2BS_HEAT_DF = prove
 (`!U a b (G:real->real^N->real^N^N) (Ff:real->real^N->real) Hf.
     lricci_flow U a b G /\ rfa_heat 0 U a b G (\t y u. Ff t y) Hf
     ==> rfa_heat 1 U a b G (\t. lnabla 0 (G t) (\y u. Ff t y))
                            (\t. lnabla 0 (G t) (Hf t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`0`; `U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `\t:real y:real^N u:num->real^N. (Ff:real->real^N->real) t y`;
                 `Hf:real->real^N->(num->real^N)->real`] RFA_HEAT_LNABLA) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; RFA_RMCOMM_0; REAL_ADD_RID; ETA_AX]);;

let P2BS_HEAT_HESS = prove
 (`!U a b (G:real->real^N->real^N^N) (Ff:real->real^N->real) Hf.
     lricci_flow U a b G /\ rfa_heat 0 U a b G (\t y u. Ff t y) Hf
     ==> rfa_heat 2 U a b G (\t. lnabla 1 (G t) (lnabla 0 (G t) (\y u. Ff t y)))
           (\t y u. lnabla 1 (G t) (lnabla 0 (G t) (Hf t)) y u +
                    rfa_rmcomm 1 (G t) (lnabla 0 (G t) (\y u. Ff t y)) y u)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `Ff:real->real^N->real`; `Hf:real->real^N->(num->real^N)->real`]
                P2BS_HEAT_DF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`1`; `U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `\t. lnabla 0 ((G:real->real^N->real^N^N) t) (\y u. (Ff:real->real^N->real) t y)`;
                 `\t. lnabla 0 ((G:real->real^N->real^N^N) t) ((Hf:real->real^N->(num->real^N)->real) t)`]
                RFA_HEAT_LNABLA) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let P2BS_CONTR_HESS = prove
 (`!U (G:real^N->real^N^N) (f:real^N->real) y u.
     metric_field U G /\ smooth_map_on U (\z. lift(f z)) /\ y IN U
     ==> ltcontr G (lnabla 1 G (lnabla 0 G (\z u. f z))) y u = llap G f y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `f:real^N->real`; `y:real^N`]
                LRG_LLAP_LNABLA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `lnabla 0 (G:real^N->real^N^N) (\z u. (f:real^N->real) z) =
                (\z u. drop(frechet_derivative (\w. lift(f w)) (at z) (u 1)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; P2BS_LNABLA0]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ltensor_field 2 U (lnabla 1 (G:real^N->real^N^N)
      (\z u. drop(frechet_derivative (\w. lift((f:real^N->real) w)) (at z) (u 1))))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `f:real^N->real`] P2BS_DF_FIELD) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `lnabla 0 (G:real^N->real^N^N) (\z u. (f:real^N->real) z) =
                  (\z u. drop(frechet_derivative (\w. lift(f w)) (at z) (u 1)))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; P2BS_LNABLA0]; ALL_TAC] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`1`; `U:real^N->bool`; `G:real^N->real^N^N`;
                   `\z u. drop(frechet_derivative (\w. lift((f:real^N->real) w)) (at z) (u 1))`]
                  LNABLA_TENSOR_FIELD) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[ltcontr] THEN
  GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
  BINOP_TAC THENL
   [MATCH_MP_TAC LRG_MATRIX_INV_SYM THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC RFA_TF_AGREE THEN MAP_EVERY EXISTS_TAC [`2`; `U:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `m = 1 \/ m = 2` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV]);;

let P2BS_CONTR_GRAD = prove
 (`!(G:real^N->real^N^N) (f:real^N->real) y u.
     ltcontr G (ltprod 1 (lnabla 0 G (\z u. f z)) (lnabla 0 G (\z u. f z))) y u =
     lgrad2 G f y`,
  REWRITE_TAC[ltcontr; ltprod; P2BS_LNABLA0; lgrad2] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[REAL_MUL_ASSOC]);;

(* SOL.A3 Heat equations of Lap F and |grad F|^2 with explicit defects:    *)
(*   d/dt Lap F = Lap(Lap F) + Lap h + contr(rmcomm(dF)),                   *)
(*   d/dt |grad F|^2 = Lap |grad F|^2 + 2 <grad h,grad F> - 2 |Hess F|^2,   *)
(* for dF/dt = Lap F + h (h the heat defect of F).                          *)

let P2BS_LTCONTR_ADD = prove
 (`!(G:real^N->real^N^N) S T y u.
     ltcontr G (\y u. S y u + T y u) y u = ltcontr G S y u + ltcontr G T y u`,
  REWRITE_TAC[ltcontr; REAL_ADD_LDISTRIB; SUM_ADD_NUMSEG]);;

let P2BS_LTCONTR_SUB = prove
 (`!(G:real^N->real^N^N) S T y u.
     ltcontr G (\y u. S y u - T y u) y u = ltcontr G S y u - ltcontr G T y u`,
  REWRITE_TAC[ltcontr; REAL_SUB_LDISTRIB; SUM_SUB_NUMSEG]);;

let P2BS_LTCONTR_CMUL = prove
 (`!(G:real^N->real^N^N) c S y u.
     ltcontr G (\y u. c * S y u) y u = c * ltcontr G S y u`,
  REWRITE_TAC[ltcontr; GSYM SUM_LMUL] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN REAL_ARITH_TAC);;

let P2BS_LTCONTR_LIN3 = prove
 (`!(G:real^N->real^N^N) A B C y u.
     ltcontr G (\y u. A y u + B y u - &2 * C y u) y u =
     ltcontr G A y u + ltcontr G B y u - &2 * ltcontr G C y u`,
  REWRITE_TAC[ltcontr; GSYM SUM_ADD_NUMSEG; GSYM SUM_SUB_NUMSEG; GSYM SUM_LMUL] THEN
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN REAL_ARITH_TAC);;

let P2BS_CONTR_LTPROD = prove
 (`!(G:real^N->real^N^N) (f:real^N->real) g y u.
     ltcontr G (ltprod 1 (lnabla 0 G (\z u. f z)) (lnabla 0 G (\z u. g z))) y u =
     rfa_lginner G f g y`,
  REWRITE_TAC[ltcontr; ltprod; P2BS_LNABLA0; rfa_lginner; rfa_d1] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_MUL_ASSOC]);;

let P2BS_HEAT_DEFECT_SMOOTH = prove
 (`!U a b (G:real->real^N->real^N^N) (Tf:real->real^N->(num->real^N)->real)
    (h:real->real^N->real) t.
     rfa_heat 0 U a b G Tf (\t y u. h t y) /\ a < t /\ t < b
     ==> smooth_map_on U (\y. lift(h t y))`,
  REWRITE_TAC[rfa_heat] THEN MESON_TAC[]);;

let P2BS_HEAT_FUN_SMOOTH = prove
 (`!U a b (G:real->real^N->real^N^N) (Ff:real->real^N->real) Hf t.
     rfa_heat 0 U a b G (\t y u. Ff t y) Hf /\ open U /\ a < t /\ t < b
     ==> smooth_map_on U (\y. lift(Ff t y))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`0`; `U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `\t:real y:real^N u:num->real^N. (Ff:real->real^N->real) t y`;
                 `Hf:real->real^N->(num->real^N)->real`; `t:real`] RFA_HEAT_SLICE) THEN
  ASM_REWRITE_TAC[]);;

let P2BS_HEAT_LAP = prove
 (`!U a b (G:real->real^N->real^N^N) (Ff:real->real^N->real) (h:real->real^N->real).
     lricci_flow U a b G /\ rfa_heat 0 U a b G (\t y u. Ff t y) (\t y u. h t y)
     ==> rfa_heat 0 U a b G (\t y u. llap (G t) (Ff t) y)
           (\t y u. llap (G t) (h t) y +
                    ltcontr (G t) (rfa_rmcomm 1 (G t) (lnabla 0 (G t) (\y u. Ff t y))) y u)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `Ff:real->real^N->real`;
                 `\t:real y:real^N u:num->real^N. (h:real->real^N->real) t y`]
                P2BS_HEAT_HESS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`0`; `U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
    `\t. lnabla 1 ((G:real->real^N->real^N^N) t)
           (lnabla 0 (G t) (\y u. (Ff:real->real^N->real) t y))`;
    `\t y u. lnabla 1 ((G:real->real^N->real^N^N) t)
               (lnabla 0 (G t) (\y u. (h:real->real^N->real) t y)) y u +
             rfa_rmcomm 1 (G t) (lnabla 0 (G t) (\y u. (Ff:real->real^N->real) t y)) y u`]
   RFA_HEAT_LTCONTR) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC RFA_HEAT_CONG THEN
  MAP_EVERY EXISTS_TAC
   [`\t. ltcontr ((G:real->real^N->real^N^N) t)
           (lnabla 1 (G t) (lnabla 0 (G t) (\y u. (Ff:real->real^N->real) t y)))`;
    `\t. ltcontr ((G:real->real^N->real^N^N) t)
           (\y u. lnabla 1 (G t) (lnabla 0 (G t) (\y u. (h:real->real^N->real) t y)) y u +
                  rfa_rmcomm 1 (G t) (lnabla 0 (G t) (\y u. (Ff:real->real^N->real) t y)) y u)`] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`; `u:num->real^N`] THEN STRIP_TAC THEN
  REWRITE_TAC[P2BS_LTCONTR_ADD] THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U (\y. lift((Ff:real->real^N->real) t y)) /\
                smooth_map_on U (\y. lift((h:real->real^N->real) t y))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC P2BS_HEAT_FUN_SMOOTH THEN
      MAP_EVERY EXISTS_TAC [`a:real`; `b:real`; `G:real->real^N->real^N^N`;
                            `\t:real y:real^N u:num->real^N. (h:real->real^N->real) t y`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2BS_HEAT_DEFECT_SMOOTH THEN
      MAP_EVERY EXISTS_TAC [`a:real`; `b:real`; `G:real->real^N->real^N^N`;
                            `\t:real y:real^N u:num->real^N. (Ff:real->real^N->real) t y`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `(Ff:real->real^N->real) t`;
                 `y:real^N`; `u:num->real^N`] P2BS_CONTR_HESS) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `(h:real->real^N->real) t`;
                 `y:real^N`; `u:num->real^N`] P2BS_CONTR_HESS) THEN
  ASM_REWRITE_TAC[ETA_AX] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN REWRITE_TAC[]);;

let P2BS_HEAT_GRAD2 = prove
 (`!U a b (G:real->real^N->real^N^N) (Ff:real->real^N->real) (h:real->real^N->real).
     lricci_flow U a b G /\ rfa_heat 0 U a b G (\t y u. Ff t y) (\t y u. h t y)
     ==> rfa_heat 0 U a b G (\t y u. lgrad2 (G t) (Ff t) y)
           (\t y u. &2 * rfa_lginner (G t) (h t) (Ff t) y -
                    &2 * ltcontr (G t)
                           (rfa_xgrad 1 1 (G t) (lnabla 0 (G t) (\y u. Ff t y))
                                                (lnabla 0 (G t) (\y u. Ff t y))) y u)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `Ff:real->real^N->real`;
                 `\t:real y:real^N u:num->real^N. (h:real->real^N->real) t y`]
                P2BS_HEAT_DF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`1`; `1`; `U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
    `\t. lnabla 0 ((G:real->real^N->real^N^N) t) (\y u. (Ff:real->real^N->real) t y)`;
    `\t. lnabla 0 ((G:real->real^N->real^N^N) t) (\y u. (h:real->real^N->real) t y)`;
    `\t. lnabla 0 ((G:real->real^N->real^N^N) t) (\y u. (Ff:real->real^N->real) t y)`;
    `\t. lnabla 0 ((G:real->real^N->real^N^N) t) (\y u. (h:real->real^N->real) t y)`]
   RFA_HEAT_LTPROD) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`0`; `U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
    `\t. ltprod 1 (lnabla 0 ((G:real->real^N->real^N^N) t) (\y u. (Ff:real->real^N->real) t y))
                  (lnabla 0 (G t) (\y u. Ff t y))`;
    `\t y u. ltprod 1 (lnabla 0 ((G:real->real^N->real^N^N) t) (\y u. (h:real->real^N->real) t y))
                      (lnabla 0 (G t) (\y u. (Ff:real->real^N->real) t y)) y u +
             ltprod 1 (lnabla 0 (G t) (\y u. Ff t y)) (lnabla 0 (G t) (\y u. h t y)) y u -
             &2 * rfa_xgrad 1 1 (G t) (lnabla 0 (G t) (\y u. Ff t y))
                                      (lnabla 0 (G t) (\y u. Ff t y)) y u`]
   RFA_HEAT_LTCONTR) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC RFA_HEAT_CONG THEN
  MAP_EVERY EXISTS_TAC
   [`\t. ltcontr ((G:real->real^N->real^N^N) t)
           (ltprod 1 (lnabla 0 (G t) (\y u. (Ff:real->real^N->real) t y))
                     (lnabla 0 (G t) (\y u. Ff t y)))`;
    `\t. ltcontr ((G:real->real^N->real^N^N) t)
           (\y u. ltprod 1 (lnabla 0 (G t) (\y u. (h:real->real^N->real) t y))
                           (lnabla 0 (G t) (\y u. (Ff:real->real^N->real) t y)) y u +
                  ltprod 1 (lnabla 0 (G t) (\y u. Ff t y)) (lnabla 0 (G t) (\y u. h t y)) y u -
                  &2 * rfa_xgrad 1 1 (G t) (lnabla 0 (G t) (\y u. Ff t y))
                                           (lnabla 0 (G t) (\y u. Ff t y)) y u)`] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`; `u:num->real^N`] THEN STRIP_TAC THEN
  REWRITE_TAC[P2BS_LTCONTR_LIN3; P2BS_CONTR_LTPROD; P2BS_CONTR_GRAD; ETA_AX] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `(Ff:real->real^N->real) t`;
                 `(h:real->real^N->real) t`; `y:real^N`] RFA_LGINNER_SYM) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

(* SOL.A4 The heat equation of the scalar curvature with defect 2|Ric|^2   *)
(* (RFA_HEAT_SC, its defect identified with LSCALAR_EVOLUTION by           *)
(* uniqueness of derivatives), the time coefficient b - t, and the heat    *)
(* equation of W = (b - t)(2 Lap F - |grad F|^2 + R) + F.                   *)

let P2BS_HEAT_SCAL = prove
 (`!U a b (G:real->real^N->real^N^N).
     lricci_flow U a b G
     ==> rfa_heat 0 U a b G (\t y u. lscalar (G t) y)
                            (\t y u. &2 * ltnorm2 2 (G t) (lric2 (G t)) y)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`] RFA_HEAT_SC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC RFA_HEAT_CONG THEN
  MAP_EVERY EXISTS_TAC [`\t. rfa_sc ((G:real->real^N->real^N^N) t)`;
                        `\t. ltcontr ((G:real->real^N->real^N^N) t) (rfa_hric (G t))`] THEN
  ASM_REWRITE_TAC[rfa_sc] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`; `u:num->real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `t:real`; `y:real^N`] LSCALAR_EVOLUTION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `rfa_heat 0 U a b (G:real->real^N->real^N^N) (\t. rfa_sc (G t))
                 (\t. ltcontr (G t) (rfa_hric (G t)))` THEN
  REWRITE_TAC[rfa_heat] THEN
  DISCH_THEN(MP_TAC o SPECL [`t:real`; `y:real^N`; `u:num->real^N`] o el 2 o CONJUNCTS) THEN
  ASM_REWRITE_TAC[rfa_sc] THEN
  SUBGOAL_THEN `rfa_sc ((G:real->real^N->real^N^N) t) = (\x u. lscalar (G t) x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; rfa_sc]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                 `lscalar ((G:real->real^N->real^N^N) t)`; `y:real^N`; `u:num->real^N`]
                RFA_LTLAP_0) THEN
  ASM_SIMP_TAC[LRG_LSCALAR_SMOOTH; ETA_AX] THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[rfa_rcact; SUM_CLAUSES_NUMSEG; ARITH; REAL_SUB_RZERO] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\s. lscalar ((G:real->real^N->real^N^N) s) y`; `t:real`]
                REAL_DERIVATIVE_UNIQUE_ATREAL) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`llap ((G:real->real^N->real^N^N) t) (lscalar (G t)) y +
     ltcontr (G t) (rfa_hric (G t)) y u`;
    `llap ((G:real->real^N->real^N^N) t) (lscalar (G t)) y +
     &2 * ltnorm2 2 (G t) (lric2 (G t)) y`]) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let P2BS_TCOEF = prove
 (`!a b c. (!t. ((\t. c - t) has_real_derivative --(&1)) (atreal t)) /\
           smooth_map_on (interval(lift a,lift b)) (\x. lift(c - drop x))`,
  REPEAT GEN_TAC THEN CONJ_TAC THENL
   [GEN_TAC THEN REAL_DIFF_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`interval(lift a,lift b)`; `\x:real^1. lift c`; `\x:real^1. x`]
                SMOOTH_MAP_ON_LIFT_SUB) THEN
  REWRITE_TAC[LIFT_DROP; OPEN_INTERVAL; SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST]);;

(* SOL.A5 The heat equation of W = (b - t)(2 Lap F - |grad F|^2 + R) + F    *)
(* with its defect in terms of the defect h of F (RFA_HEAT_LINCOMB,          *)
(* RFA_HEAT_TMUL of pc_rfa_hcalc).                                           *)

let P2BS_HEAT_W = prove
 (`!U a b (G:real->real^N->real^N^N) (Ff:real->real^N->real) (h:real->real^N->real).
     lricci_flow U a b G /\ rfa_heat 0 U a b G (\t y u. Ff t y) (\t y u. h t y)
     ==> rfa_heat 0 U a b G
           (\t y u. (b - t) * (&2 * llap (G t) (Ff t) y - lgrad2 (G t) (Ff t) y +
                               lscalar (G t) y) + Ff t y)
           (\t y u. --(&2 * llap (G t) (Ff t) y - lgrad2 (G t) (Ff t) y + lscalar (G t) y) +
                    (b - t) *
                    (&2 * (llap (G t) (h t) y +
                           ltcontr (G t) (rfa_rmcomm 1 (G t) (lnabla 0 (G t) (\y u. Ff t y)))
                             y u) -
                     (&2 * rfa_lginner (G t) (h t) (Ff t) y -
                      &2 * ltcontr (G t) (rfa_xgrad 1 1 (G t) (lnabla 0 (G t) (\y u. Ff t y))
                                                         (lnabla 0 (G t) (\y u. Ff t y))) y u) +
                     &2 * ltnorm2 2 (G t) (lric2 (G t)) y) +
                    h t y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fl") (LABEL_TAC "hf")) THEN
  USE_THEN "fl" (STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
  SUBGOAL_THEN `!t. a < t /\ t < b
                    ==> ((\t. b - t) has_real_derivative (\t:real. --(&1)) t) (atreal t)`
  (LABEL_TAC "dc") THENL [REWRITE_TAC[P2BS_TCOEF]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (interval(lift a,lift b)) (\x. lift((\t. b - t) (drop x)))`
  (LABEL_TAC "sc") THENL [REWRITE_TAC[P2BS_TCOEF]; ALL_TAC] THEN
  USE_THEN "fl" (fun fl -> USE_THEN "hf" (fun hf -> USE_THEN "dc" (fun dc ->
    USE_THEN "sc" (fun sc ->
      let ha = MATCH_MP P2BS_HEAT_LAP (CONJ fl hf) in
      let hb = MATCH_MP P2BS_HEAT_GRAD2 (CONJ fl hf) in
      let hr = MATCH_MP P2BS_HEAT_SCAL fl in
      let l1 = SPECL [`&2`; `--(&1)`] (MATCH_MP RFA_HEAT_LINCOMB (CONJ fl (CONJ ha hb))) in
      let l2 = SPECL [`&1`; `&1`] (MATCH_MP RFA_HEAT_LINCOMB (CONJ fl (CONJ l1 hr))) in
      let l3 = MATCH_MP RFA_HEAT_TMUL (CONJ fl (CONJ l2 (CONJ dc sc))) in
      let l4 = SPECL [`&1`; `&1`] (MATCH_MP RFA_HEAT_LINCOMB (CONJ fl (CONJ l3 hf))) in
      MP_TAC l4)))) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] RFA_HEAT_CONG)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* SOL.A6 Algebra of 2-tensors at a point: the four-sum form of ltinner 2, *)
(* a six-fold sum exchange, the trace of the curvature tensor in slots 2   *)
(* and 4 (the Ricci tensor), and the symmetry of the Hessian.              *)

let P2BS_LTINNER2_EXPAND = prove
 (`!U (G:real^N->real^N^N) Ss Tt y.
     ltensor_field 2 U Ss /\ ltensor_field 2 U Tt /\ y IN U
     ==> ltinner 2 G Ss Tt y =
         sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
           sum(1..dimindex(:N)) (\r. sum(1..dimindex(:N)) (\s.
             matrix_inv(G y)$p$r * matrix_inv(G y)$q$s *
             Ss y (\m. if m = 1 then basis p else basis q) *
             Tt y (\m. if m = 1 then basis r else basis s)))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ltinner; LRG_SUM_INDEX_TUPLES_2] THEN
  REWRITE_TAC[num_CONV `2`; num_CONV `1`; PRODUCT_CLAUSES_NUMSEG] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[PRODUCT_CLAUSES_NUMSEG] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `s:num` THEN STRIP_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN
   `!(W:real^N->(num->real^N)->real) a b.
      ltensor_field 2 U W
      ==> W y (\m. basis(if m = 2 then b else if m = 1 then a else 0)) =
          W y (\m. if m = 1 then basis a else basis b)`
  (fun th -> ASM_SIMP_TAC[th]) THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_TF_AGREE THEN
    MAP_EVERY EXISTS_TAC [`2`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `m = 1 \/ m = 2` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* SOL.A7 A six-fold exchange of finite sums: the contraction over the     *)
(* first pair of indices moves inside the other two.                        *)

let p2bs_swap_at k =
  funpow k (fun c -> RAND_CONV(ABS_CONV c))
    (GEN_REWRITE_CONV I [SUM_SWAP_NUMSEG] THENC REDEPTH_CONV BETA_CONV);;

let P2BS_SUM6_SWAP = prove
 (`!n (g:num->num->real) (Fz:num->num->num->num->num->num->real).
     sum(1..n) (\c. sum(1..n) (\d. g c d *
       sum(1..n) (\a. sum(1..n) (\b. g a b *
         sum(1..n) (\p. sum(1..n) (\q. g p q * Fz c d a b p q)))))) =
     sum(1..n) (\a. sum(1..n) (\b. g a b *
       sum(1..n) (\p. sum(1..n) (\q. g p q *
         sum(1..n) (\c. sum(1..n) (\d. g c d * Fz c d a b p q))))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  CONV_TAC(LAND_CONV(p2bs_swap_at 1 THENC p2bs_swap_at 0 THENC
                     p2bs_swap_at 2 THENC p2bs_swap_at 1 THENC
                     p2bs_swap_at 3 THENC p2bs_swap_at 2 THENC
                     p2bs_swap_at 4 THENC p2bs_swap_at 3)) THEN
  REPEAT(MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC) THEN
  REAL_ARITH_TAC);;

(* A tactic applying P2BS_SUM6_SWAP to the left side of the goal, with the  *)
(* six-place summand read off the goal (no higher-order matching).          *)

let P2BS_SUM6_TAC : tactic = fun (asl,w as gl) ->
  let lhs = lhand w in
  let dsum t = dest_abs(rand t) in
  let c,t1 = dsum lhs in let d,t2 = dsum t1 in
  let gcd = lhand t2 and t3 = rand t2 in
  let a,t4 = dsum t3 in let b,t5 = dsum t4 in
  let t6 = rand t5 in let p,t7 = dsum t6 in let q,t8 = dsum t7 in
  let body = rand t8 in
  let n = rand(rand(rator lhs)) in
  let gf = list_mk_abs([c;d],gcd) in
  let fz = list_mk_abs([c;d;a;b;p;q],body) in
  let th = CONV_RULE(DEPTH_CONV BETA_CONV) (ISPECL [n;gf;fz] P2BS_SUM6_SWAP) in
  GEN_REWRITE_TAC LAND_CONV [th] gl;;

let P2BS_SUM4_RICHESS = prove
 (`!n (g:num->num->real) (r:num->num->real) (h:num->num->real).
     (!i j. g i j = g j i) /\ (!i j. h i j = h j i)
     ==> sum(1..n) (\a. sum(1..n) (\b. g a b *
           sum(1..n) (\p. sum(1..n) (\q. g p q * (r b p * h q a + r a p * h q b))))) =
         &2 * sum(1..n) (\x. sum(1..n) (\y. sum(1..n) (\z. sum(1..n) (\w.
                g x z * g y w * r x y * h z w))))`,
  REPEAT STRIP_TAC THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[REAL_ADD_LDISTRIB; SUM_ADD_NUMSEG; GSYM SUM_LMUL])) THEN
  MATCH_MP_TAC(REAL_ARITH `t1 = s /\ t2 = s ==> t1 + t2 = &2 * s`) THEN CONJ_TAC THENL
   [CONV_TAC(LAND_CONV(p2bs_swap_at 0 THENC p2bs_swap_at 1));
    CONV_TAC(LAND_CONV(p2bs_swap_at 1))] THEN
  REPEAT(MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* SOL.A8 The Hessian of a smooth function is symmetric (RFA_RICCI_IDENTITY *)
(* with k = 0), the trace of the curvature tensor in slots 2 and 4 is the   *)
(* Ricci tensor, and the contraction of the cross term rfa_xgrad of dF with *)
(* itself is |Hess F|^2.                                                     *)

let P2BS_HESS_SYM = prove
 (`!U (G:real^N->real^N^N) (f:real^N->real) y z1 z2.
     metric_field U G /\ smooth_map_on U (\x. lift(f x)) /\ y IN U
     ==> lnabla 1 G (lnabla 0 G (\x u. f x)) y (\m. if m = 1 then z1 else z2) =
         lnabla 1 G (lnabla 0 G (\x u. f x)) y (\m. if m = 1 then z2 else z1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`0`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `\x:real^N u:num->real^N. (f:real^N->real) x`; `y:real^N`;
                 `\m:num. if m = 1 then z1:real^N else z2`] RFA_RICCI_IDENTITY) THEN
  ASM_REWRITE_TAC[RFA_TENSOR_FIELD_0; ETA_AX] THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH; RFA_LNABLA_ITER_2; ADD_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[REAL_SUB_0] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC LRG_LNABLA_AGREE THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `f:real^N->real`] P2BS_DF_FIELD) THEN
    ASM_SIMP_TAC[ETA_AX];
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `m = 1 \/ m = 2` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV]);;

let P2BS_RM_TRACE24 = prove
 (`!U (G:real^N->real^N^N) y v w.
     metric_field U G /\ y IN U
     ==> sum(1..dimindex(:N)) (\c. sum(1..dimindex(:N)) (\d.
           matrix_inv(G y)$c$d *
           lrm4 G y (\m. if m = 1 then v else if m = 2 then basis d
                         else if m = 3 then w else basis c))) =
         lricci G y v w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!c d. lrm4 (G:real^N->real^N^N) y
            (\m. if m = 1 then v else if m = 2 then basis d else if m = 3 then w
                 else basis c) =
          --(lrm4 G y (\m. if m = 1 then basis d else if m = 2 then v else if m = 3 then w
                           else basis c))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[lrm4] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `basis d:real^N`;
                   `v:real^N`; `basis c:real^N`] LRIEMANN_ANTISYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_RNEG; DOT_RNEG];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_RNEG; SUM_NEG] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `v:real^N`; `w:real^N`]
                RFA_RM_TRACE14) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_NEG_NEG]);;

(* SOL.A9 The contraction of the cross term rfa_xgrad 1 1 of dF with itself *)
(* is |Hess F|^2 (ltinner 2 of the Hessian with itself).                    *)

let P2BS_HESS_FIELD = prove
 (`!U (G:real^N->real^N^N) (f:real^N->real).
     metric_field U G /\ smooth_map_on U (\y. lift(f y))
     ==> ltensor_field 2 U (lnabla 1 G (lnabla 0 G (\z u. f z))) /\
         (!u. smooth_map_on U (\y. lift(lnabla 1 G (lnabla 0 G (\z u. f z)) y u)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `f:real^N->real`] P2BS_DF_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`1`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lnabla 0 (G:real^N->real^N^N) (\z u. (f:real^N->real) z)`] LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let P2BS_CONTR_XGRAD = prove
 (`!U (G:real^N->real^N^N) (f:real^N->real) y u.
     metric_field U G /\ smooth_map_on U (\z. lift(f z)) /\ y IN U
     ==> ltcontr G (rfa_xgrad 1 1 G (lnabla 0 G (\z u. f z)) (lnabla 0 G (\z u. f z))) y u =
         ltinner 2 G (lnabla 1 G (lnabla 0 G (\z u. f z)))
                     (lnabla 1 G (lnabla 0 G (\z u. f z))) y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `f:real^N->real`] P2BS_DF_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `f:real^N->real`] P2BS_HESS_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                 `lnabla 1 (G:real^N->real^N^N) (lnabla 0 G (\z u. (f:real^N->real) z))`;
                 `lnabla 1 (G:real^N->real^N^N) (lnabla 0 G (\z u. (f:real^N->real) z))`;
                 `y:real^N`] P2BS_LTINNER2_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ltcontr; rfa_xgrad] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  CONV_TAC(LAND_CONV(p2bs_swap_at 1)) THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN
   `!v1 v2 (w:num->real^N).
      (!m. 1 <= m /\ m <= 2 ==> w m = (if m = 1 then v1 else v2))
      ==> lnabla 1 (G:real^N->real^N^N) (lnabla 0 G (\z u. (f:real^N->real) z)) y w =
          lnabla 1 G (lnabla 0 G (\z u. f z)) y (\m. if m = 1 then v1 else v2)`
  (LABEL_TAC "agree") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LRG_LNABLA_AGREE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lnabla 1 (G:real^N->real^N^N) (lnabla 0 G (\z u. (f:real^N->real) z)) y
      (\m. if m = 2 then basis a
           else if m = 1 then basis c else if m = 2 then basis d else u (m - 2)) =
    lnabla 1 G (lnabla 0 G (\z u. f z)) y (\m. if m = 1 then basis c else basis a) /\
    lnabla 1 (G:real^N->real^N^N) (lnabla 0 G (\z u. (f:real^N->real) z)) y
      (\m. if m = 2 then basis b
           else if m + 1 = 1 then basis c else if m + 1 = 2 then basis d
           else u ((m + 1) - 2)) =
    lnabla 1 G (lnabla 0 G (\z u. f z)) y (\m. if m = 1 then basis d else basis b)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    (USE_THEN "agree" MATCH_MP_TAC THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
     SUBGOAL_THEN `m = 1 \/ m = 2` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* SOL.A10 The contraction of the commutator term rfa_rmcomm 1 of dF is    *)
(* 2 <Ric, Hess F> (ltinner 2), by the trace P2BS_RM_TRACE24, the sum       *)
(* exchange P2BS_SUM6_SWAP and the symmetry of the Hessian.                 *)

let P2BS_RMCOMM1_VAL = prove
 (`!U (G:real^N->real^N^N) (f:real^N->real) y.
     metric_field U G /\ smooth_map_on U (\z. lift(f z)) /\ y IN U
     ==> !v. rfa_rmcomm 1 G (lnabla 0 G (\z u. f z)) y v =
         sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b. matrix_inv(G y)$a$b *
           sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q. matrix_inv(G y)$p$q *
             (lrm4 G y (\m. if m = 1 then basis b else if m = 2 then v 2
                            else if m = 3 then basis p else v 1) *
              lnabla 1 G (lnabla 0 G (\z u. f z)) y (\m. if m = 1 then basis q else basis a) +
              lrm4 G y (\m. if m = 1 then basis a else if m = 2 then v 2
                            else if m = 3 then basis p else v 1) *
              lnabla 1 G (lnabla 0 G (\z u. f z)) y (\m. if m = 1 then basis q else basis b))))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `f:real^N->real`] P2BS_DF_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[rfa_rmcomm; SUM_SING_NUMSEG] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  AP_TERM_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN BETA_TAC THEN
  AP_TERM_TAC THEN BINOP_TAC THEN
  (AP_TERM_TAC THEN
   MATCH_MP_TAC LRG_LNABLA_AGREE THEN EXISTS_TAC `U:real^N->bool` THEN
   ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
   SUBGOAL_THEN `m = 1 \/ m = 2` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]));;

let P2BS_CONTR_RMCOMM = prove
 (`!U (G:real^N->real^N^N) (f:real^N->real) y u.
     metric_field U G /\ smooth_map_on U (\z. lift(f z)) /\ y IN U
     ==> ltcontr G (rfa_rmcomm 1 G (lnabla 0 G (\z u. f z))) y u =
         &2 * ltinner 2 G (lric2 G) (lnabla 1 G (lnabla 0 G (\z u. f z))) y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `f:real^N->real`] P2BS_HESS_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRG_LRIC2_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the left side as a six-fold sum *)
  REWRITE_TAC[ltcontr] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `f:real^N->real`; `y:real^N`]
                P2BS_RMCOMM1_VAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  P2BS_SUM6_TAC THEN
  (* the inner contraction gives the Ricci tensor *)
  SUBGOAL_THEN
   `!a b p q.
      sum(1..dimindex(:N)) (\c. sum(1..dimindex(:N)) (\d.
        matrix_inv((G:real^N->real^N^N) y)$c$d *
        (lrm4 G y (\m. if m = 1 then basis b else if m = 2 then basis d
                       else if m = 3 then basis p else basis c) *
         lnabla 1 G (lnabla 0 G (\z u. (f:real^N->real) z)) y
           (\m. if m = 1 then basis q else basis a) +
         lrm4 G y (\m. if m = 1 then basis a else if m = 2 then basis d
                       else if m = 3 then basis p else basis c) *
         lnabla 1 G (lnabla 0 G (\z u. f z)) y (\m. if m = 1 then basis q else basis b)))) =
      lricci G y (basis b) (basis p) *
      lnabla 1 G (lnabla 0 G (\z u. f z)) y (\m. if m = 1 then basis q else basis a) +
      lricci G y (basis a) (basis p) *
      lnabla 1 G (lnabla 0 G (\z u. f z)) y (\m. if m = 1 then basis q else basis b)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[REAL_ADD_LDISTRIB; SUM_ADD_NUMSEG; REAL_MUL_ASSOC; SUM_RMUL] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `basis b:real^N`;
                   `basis p:real^N`] P2BS_RM_TRACE24) THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `basis a:real^N`;
                   `basis p:real^N`] P2BS_RM_TRACE24) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  (* the right side *)
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `lric2 (G:real^N->real^N^N)`;
                 `lnabla 1 (G:real^N->real^N^N) (lnabla 0 G (\z u. (f:real^N->real) z))`;
                 `y:real^N`] P2BS_LTINNER2_EXPAND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[lric2] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL
   [`dimindex(:N)`; `\i j. matrix_inv((G:real^N->real^N^N) y)$i$j`;
    `\i j. lricci (G:real^N->real^N^N) y (basis i) (basis j)`;
    `\i j. lnabla 1 (G:real^N->real^N^N) (lnabla 0 G (\z u. (f:real^N->real) z)) y
                  (\m. if m = 1 then basis i else basis j)`] P2BS_SUM4_RICHESS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THEN REPEAT GEN_TAC THENL
     [MATCH_MP_TAC LRG_MATRIX_INV_SYM THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2BS_HESS_SYM THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]];
    DISCH_THEN ACCEPT_TAC]);;

(* SOL.A11 A heat solution that is constant in space and time has zero     *)
(* defect; and for h = F / tau + k on an open set, tau Lap h = Lap F and    *)
(* tau <grad h, grad F> = |grad F|^2.                                       *)

let P2BS_HEAT_CONST_DEFECT = prove
 (`!U a b (G:real->real^N->real^N^N) (Wf:real->real^N->(num->real^N)->real) Hf c.
     lricci_flow U a b G /\ rfa_heat 0 U a b G Wf Hf /\
     (!s z u. a < s /\ s < b /\ z IN U ==> Wf s z u = c)
     ==> !t y u. a < t /\ t < b /\ y IN U ==> Hf t y u = &0`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "heat") (LABEL_TAC "const"))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`; `u:num->real^N`] THEN STRIP_TAC THEN
  USE_THEN "heat" (MP_TAC o SPECL [`t:real`; `y:real^N`; `u:num->real^N`] o el 2 o
                   CONJUNCTS o REWRITE_RULE[rfa_heat]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `ltlap 0 ((G:real->real^N->real^N^N) t)
                  ((Wf:real->real^N->(num->real^N)->real) t) y u = &0` SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `ltlap 0 ((G:real->real^N->real^N^N) t) (\x:real^N u:num->real^N. c:real) y u` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RFA_LTLAP_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `\x:real^N. (c:real)`;
                     `y:real^N`; `u:num->real^N`] RFA_LTLAP_0) THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONST; RFA_LLAP_CONST]];
    ALL_TAC] THEN
  REWRITE_TAC[rfa_rcact; SUM_CLAUSES_NUMSEG; ARITH; REAL_SUB_RZERO; REAL_ADD_LID] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC(ISPECL [`\s. (Wf:real->real^N->(num->real^N)->real) s y u`; `t:real`]
                      REAL_DERIVATIVE_UNIQUE_ATREAL) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  MAP_EVERY EXISTS_TAC [`\s:real. (c:real)`; `min (t - a) (b - t)`] THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST; REAL_LT_MIN] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
  USE_THEN "const" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P2BS_AFFINE_RELATIONS = prove
 (`!U (G:real^N->real^N^N) (Ff:real^N->real) (h:real^N->real) tau k y.
     open U /\ smooth_map_on U (\z. lift(Ff z)) /\ y IN U /\ ~(tau = &0) /\
     (!z. z IN U ==> h z = inv tau * Ff z + k)
     ==> tau * llap G h y = llap G Ff y /\
         tau * rfa_lginner G h Ff y = lgrad2 G Ff y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on U (\z. lift(inv tau * (Ff:real^N->real) z))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `inv tau`; `\z. lift((Ff:real^N->real) z)`]
                  SMOOTH_MAP_ON_LIFT_CMUL) THEN
    ASM_REWRITE_TAC[LIFT_DROP; ETA_AX];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `tau * llap (G:real^N->real^N^N) (\z. inv tau * (Ff:real^N->real) z + k) y` THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN MATCH_MP_TAC LLAP_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `\z. inv tau * (Ff:real^N->real) z`;
                   `\z:real^N. (k:real)`; `y:real^N`] RFA_LLAP_ADD) THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; RFA_LLAP_CONST; REAL_ADD_RID] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `Ff:real^N->real`; `inv tau`;
                   `y:real^N`] RFA_LLAP_CMUL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `~(tau = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `!e. rfa_d1 (h:real^N->real) y e = inv tau * rfa_d1 (Ff:real^N->real) y e`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `rfa_d1 (\z. inv tau * (Ff:real^N->real) z + k) y e` THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFA_D1_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(BETA_RULE(ISPECL [`\z. inv tau * (Ff:real^N->real) z`; `\z:real^N. (k:real)`;
                             `y:real^N`; `e:real^N`] RFA_D1_ADD_AT)) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[DIFFERENTIABLE_CONST] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[RFA_D1_CONST; REAL_ADD_RID] THEN
    MATCH_MP_TAC RFA_D1_CMUL_AT THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[RFA_LGRAD2_D1; rfa_lginner; GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
  UNDISCH_TAC `~(tau = &0)` THEN CONV_TAC REAL_FIELD);;

(* SOL.A12 The inner product of a 2-tensor with the metric is its trace,   *)
(* and the expansion of |Ric + Hess F - c G|^2.                             *)

let P2BS_GINV_G_GINV = prove
 (`!U (G:real^N->real^N^N) y p q.
     metric_field U G /\ y IN U /\
     1 <= p /\ p <= dimindex(:N) /\ 1 <= q /\ q <= dimindex(:N)
     ==> sum(1..dimindex(:N)) (\r. sum(1..dimindex(:N)) (\s.
           matrix_inv(G y)$p$r * matrix_inv(G y)$q$s * (G y)$r$s)) =
         matrix_inv(G y)$p$q`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `invertible((G:real^N->real^N^N) y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. 1 <= r /\ r <= dimindex(:N)
        ==> sum(1..dimindex(:N)) (\s. matrix_inv((G:real^N->real^N^N) y)$p$r *
                                      matrix_inv(G y)$q$s * (G y)$r$s) =
            matrix_inv(G y)$p$r * (if r = q then &1 else &0)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC; SUM_LMUL] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `((G:real^N->real^N^N) y ** matrix_inv(G y))$r$q` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[LRG_MATRIX_MUL_COMPONENT] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      X_GEN_TAC `s:num` THEN STRIP_TAC THEN BETA_TAC THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `q:num`; `s:num`]
                    LRG_MATRIX_INV_SYM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[MATRIX_INV; MAT_COMPONENT] THEN REWRITE_TAC[REAL_OF_NUM_EQ]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:N)) (\r. if r = q then matrix_inv((G:real^N->real^N^N) y)$p$q
                                        else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN BETA_TAC THEN
    ASM_SIMP_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO];
    REWRITE_TAC[SUM_DELTA; IN_NUMSEG] THEN ASM_REWRITE_TAC[]]);;

let P2BS_LTINNER2_METRIC = prove
 (`!U (G:real^N->real^N^N) Ss y.
     metric_field U G /\ ltensor_field 2 U Ss /\ y IN U
     ==> ltinner 2 G Ss (lmetric2 G) y =
         sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
           matrix_inv(G y)$p$q * Ss y (\m. if m = 1 then basis p else basis q)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRG_LMETRIC2_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `Ss:real^N->(num->real^N)->real`;
                 `lmetric2 (G:real^N->real^N^N)`; `y:real^N`] P2BS_LTINNER2_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:N)) (\r. sum(1..dimindex(:N)) (\s.
                matrix_inv((G:real^N->real^N^N) y)$p$r * matrix_inv(G y)$q$s * (G y)$r$s)) *
              (Ss:real^N->(num->real^N)->real) y (\m. if m = 1 then basis p else basis q)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_RMUL] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `s:num` THEN STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[lmetric2] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[LRG_BASIS_DOT_MATRIX] THEN REAL_ARITH_TAC;
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `p:num`; `q:num`]
                  P2BS_GINV_G_GINV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]);;

(* SOL.A13 Expansion of the norm of S1 + S2 - c M (pure algebra of ltinner). *)

let P2BS_LTNORM2_LIN3_RAW = prove
 (`!k (G:real^N->real^N^N) S1 S2 M c y.
     ltnorm2 k G (\y u. S1 y u + S2 y u - c * M y u) y =
     ltinner k G S1 S1 y + ltinner k G S1 S2 y + ltinner k G S2 S1 y + ltinner k G S2 S2 y -
     c * ltinner k G S1 M y - c * ltinner k G M S1 y -
     c * ltinner k G S2 M y - c * ltinner k G M S2 y + c pow 2 * ltinner k G M M y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ltnorm2; ltinner] THEN
  SIMP_TAC[LRG_INDEX_TUPLES_FINITE; GSYM SUM_ADD; GSYM SUM_SUB; GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `j:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
  REAL_ARITH_TAC);;

let P2BS_LTINNER_RIC_METRIC = prove
 (`!U (G:real^N->real^N^N) y.
     metric_field U G /\ y IN U
     ==> ltinner 2 G (lric2 G) (lmetric2 G) y = lscalar G y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `lric2 (G:real^N->real^N^N)`;
                 `y:real^N`] P2BS_LTINNER2_METRIC) THEN
  ASM_SIMP_TAC[LRG_LRIC2_FIELD] THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[lric2; lscalar] THEN CONV_TAC NUM_REDUCE_CONV);;

let P2BS_LTINNER_HESS_METRIC = prove
 (`!U (G:real^N->real^N^N) (f:real^N->real) y.
     metric_field U G /\ smooth_map_on U (\z. lift(f z)) /\ y IN U
     ==> ltinner 2 G (lnabla 1 G (lnabla 0 G (\z u. f z))) (lmetric2 G) y = llap G f y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `f:real^N->real`] P2BS_HESS_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                 `lnabla 1 (G:real^N->real^N^N) (lnabla 0 G (\z u. (f:real^N->real) z))`;
                 `y:real^N`] P2BS_LTINNER2_METRIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `f:real^N->real`; `y:real^N`;
                 `\m:num. vec 0:real^N`] P2BS_CONTR_HESS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[ltcontr] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN BETA_TAC THEN
  AP_TERM_TAC THEN MATCH_MP_TAC RFA_TF_AGREE THEN
  MAP_EVERY EXISTS_TAC [`2`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `m = 1 \/ m = 2` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let P2BS_T_NORM = prove
 (`!U (G:real^N->real^N^N) (f:real^N->real) c y.
     metric_field U G /\ smooth_map_on U (\z. lift(f z)) /\ y IN U
     ==> ltnorm2 2 G (\y u. lric2 G y u + lnabla 1 G (lnabla 0 G (\z u. f z)) y u -
                            c * lmetric2 G y u) y =
         ltnorm2 2 G (lric2 G) y +
         &2 * ltinner 2 G (lric2 G) (lnabla 1 G (lnabla 0 G (\z u. f z))) y +
         ltinner 2 G (lnabla 1 G (lnabla 0 G (\z u. f z)))
                     (lnabla 1 G (lnabla 0 G (\z u. f z))) y -
         &2 * c * (lscalar G y + llap G f y) + c pow 2 * &(dimindex(:N))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[P2BS_LTNORM2_LIN3_RAW; ETA_AX] THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lnabla 1 (G:real^N->real^N^N) (lnabla 0 G (\z u. (f:real^N->real) z))`;
                 `lric2 (G:real^N->real^N^N)`; `y:real^N`] RFA_LTINNER_SYM) THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lmetric2 (G:real^N->real^N^N)`;
                 `lric2 (G:real^N->real^N^N)`; `y:real^N`] RFA_LTINNER_SYM) THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lmetric2 (G:real^N->real^N^N)`;
                 `lnabla 1 (G:real^N->real^N^N) (lnabla 0 G (\z u. (f:real^N->real) z))`;
                 `y:real^N`] RFA_LTINNER_SYM) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] P2BS_LTINNER_RIC_METRIC) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `f:real^N->real`; `y:real^N`]
                P2BS_LTINNER_HESS_METRIC) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_LTNORM2_METRIC) THEN
  ASM_REWRITE_TAC[RFA_LTNORM2_LTINNER] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REAL_ARITH_TAC);;

(* SOL.A14 The defect of W vanishes when W is the constant n, and the      *)
(* smoothness of the time derivative of F given by (9.4).                   *)

let P2BS_W_DEFECT_ZERO = prove
 (`!U a b (G:real->real^N->real^N^N) (Ff:real->real^N->real) (h:real->real^N->real).
     lricci_flow U a b G /\ rfa_heat 0 U a b G (\t y u. Ff t y) (\t y u. h t y) /\
     (!t y. a < t /\ t < b /\ y IN U
            ==> (b - t) * (&2 * llap (G t) (Ff t) y - lgrad2 (G t) (Ff t) y +
                           lscalar (G t) y) + Ff t y = &(dimindex(:N)))
     ==> !t y u. a < t /\ t < b /\ y IN U
                 ==> --(&2 * llap (G t) (Ff t) y - lgrad2 (G t) (Ff t) y + lscalar (G t) y) +
                     (b - t) *
                     (&2 * (llap (G t) (h t) y +
                            ltcontr (G t) (rfa_rmcomm 1 (G t) (lnabla 0 (G t) (\y u. Ff t y)))
                              y u) -
                      (&2 * rfa_lginner (G t) (h t) (Ff t) y -
                       &2 * ltcontr (G t) (rfa_xgrad 1 1 (G t) (lnabla 0 (G t) (\y u. Ff t y))
                                                          (lnabla 0 (G t) (\y u. Ff t y))) y u) +
                      &2 * ltnorm2 2 (G t) (lric2 (G t)) y) +
                     h t y = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `Ff:real->real^N->real`; `h:real->real^N->real`] P2BS_HEAT_W) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
    `\t y u:num->real^N. (b - t) * (&2 * llap ((G:real->real^N->real^N^N) t)
                                             ((Ff:real->real^N->real) t) y -
                                    lgrad2 (G t) (Ff t) y + lscalar (G t) y) + Ff t y`;
    `\t y u. --(&2 * llap ((G:real->real^N->real^N^N) t) ((Ff:real->real^N->real) t) y -
                lgrad2 (G t) (Ff t) y + lscalar (G t) y) +
             (b - t) *
             (&2 * (llap (G t) ((h:real->real^N->real) t) y +
                    ltcontr (G t) (rfa_rmcomm 1 (G t) (lnabla 0 (G t) (\y u. Ff t y))) y u) -
              (&2 * rfa_lginner (G t) (h t) (Ff t) y -
               &2 * ltcontr (G t) (rfa_xgrad 1 1 (G t) (lnabla 0 (G t) (\y u. Ff t y))
                                                  (lnabla 0 (G t) (\y u. Ff t y))) y u) +
              &2 * ltnorm2 2 (G t) (lric2 (G t)) y) +
             h t y`;
    `&(dimindex(:N))`] P2BS_HEAT_CONST_DEFECT) THEN
  ASM_SIMP_TAC[]);;

let P2BS_DF_SMOOTH = prove
 (`!U (G:real^N->real^N^N) (f:real^N->real) c.
     metric_field U G /\ smooth_map_on U (\y. lift(f y))
     ==> smooth_map_on U (\y. lift(lgrad2 G f y - llap G f y - lscalar G y + c))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `f:real^N->real`] P2BS_LGRAD2_SMOOTH) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `f:real^N->real`] P2BS_LLAP_SMOOTH) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRG_LSCALAR_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `\y. lift(lgrad2 (G:real^N->real^N^N) f y)`;
                 `\y. lift(llap (G:real^N->real^N^N) f y)`] SMOOTH_MAP_ON_LIFT_SUB) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `\y. lift(lgrad2 (G:real^N->real^N^N) f y - llap G f y)`;
                 `\y. lift(lscalar (G:real^N->real^N^N) y)`] SMOOTH_MAP_ON_LIFT_SUB) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`;
                 `\y. lift(lgrad2 (G:real^N->real^N^N) f y - llap G f y - lscalar G y)`;
                 `\y:real^N. lift c`] SMOOTH_MAP_ON_LIFT_ADD) THEN
  ASM_REWRITE_TAC[LIFT_DROP; SMOOTH_MAP_ON_CONST]);;

(* SOL.A15 MT Lemma 9.33 / Prop 9.32 in a chart: on a local Ricci flow on  *)
(* (a,b) x U, a jointly smooth F with dF/dt = |grad F|^2 - Lap F - R +     *)
(* n/(2(b - t)) (MT (9.4) in t = b - tau) and 2 Lap F - |grad F|^2 + R +    *)
(* (F - n)/(b - t) = 0 (MT (9.5)) satisfies Ric + Hess F = G/(2(b - t)).    *)

let P2BS_SOL_ALG = prove
 (`!tau A B R LH LG RH HH Ric2 NT n.
     ~(tau = &0) /\ tau * LH = A /\ tau * LG = B /\
     --(&2 * A - B + R) +
     tau * (&2 * (LH + &2 * RH) - (&2 * LG - &2 * HH) + &2 * Ric2) +
     ((B - A - R + n / (&2 * tau)) - A) = &0 /\
     NT = Ric2 + &2 * RH + HH - &2 * inv(&2 * tau) * (R + A) + inv(&2 * tau) pow 2 * n
     ==> NT = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&2 * tau * (Ric2 + &2 * RH + HH) = &2 * A + &2 * R - n / (&2 * tau)`
  MP_TAC THENL
   [UNDISCH_TAC `--(&2 * A - B + R) +
                 tau * (&2 * (LH + &2 * RH) - (&2 * LG - &2 * HH) + &2 * Ric2) +
                 ((B - A - R + n / (&2 * tau)) - A) = &0` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) && rhs(concl th) = `B:real`)) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) && rhs(concl th) = `A:real`)) THEN
    REAL_ARITH_TAC;
    UNDISCH_TAC `~(tau = &0)` THEN CONV_TAC REAL_FIELD]);;

let P2BS_LOCAL_SOLITON = prove
 (`!U a b (G:real->real^N->real^N^N) (Ff:real->real^N->real).
     lricci_flow U a b G /\
     smooth_map_on (interval(lift a,lift b) PCROSS U)
       (\z. lift(Ff (drop(fstcart z)) (sndcart z))) /\
     (!t y. a < t /\ t < b /\ y IN U
            ==> ((\s. Ff s y) has_real_derivative
                 lgrad2 (G t) (Ff t) y - llap (G t) (Ff t) y - lscalar (G t) y +
                 &(dimindex(:N)) / (&2 * (b - t))) (atreal t)) /\
     (!t y. a < t /\ t < b /\ y IN U
            ==> &2 * llap (G t) (Ff t) y - lgrad2 (G t) (Ff t) y + lscalar (G t) y +
                (Ff t y - &(dimindex(:N))) / (b - t) = &0)
     ==> !t y u v. a < t /\ t < b /\ y IN U
                   ==> lricci (G t) y u v +
                       lnabla 1 (G t) (lnabla 0 (G t) (\z w. Ff t z)) y
                         (\m. if m = 1 then u else v) =
                       inv(&2 * (b - t)) * (u dot (G t y ** v))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fl") (CONJUNCTS_THEN2 (LABEL_TAC "sm")
    (CONJUNCTS_THEN2 (LABEL_TAC "e94") (LABEL_TAC "e95")))) THEN
  USE_THEN "fl" (STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
  SUBGOAL_THEN `!t. a < t /\ t < b ==> smooth_map_on U (\y. lift((Ff:real->real^N->real) t y))`
  (LABEL_TAC "slice") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BS_SLICE_SMOOTH THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the heat equation of F *)
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `Ff:real->real^N->real`;
                 `\t y. lgrad2 ((G:real->real^N->real^N^N) t) ((Ff:real->real^N->real) t) y -
                        llap (G t) (Ff t) y - lscalar (G t) y +
                        &(dimindex(:N)) / (&2 * (b - t))`]
                P2BS_HEAT_FUN) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC P2BS_DF_SMOOTH THEN ASM_SIMP_TAC[];
    DISCH_TAC] THEN
  (* W = (b - t)(2 Lap F - |grad F|^2 + R) + F is the constant n, so its defect is 0 *)
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `Ff:real->real^N->real`;
                 `\t y. (lgrad2 ((G:real->real^N->real^N^N) t) ((Ff:real->real^N->real) t) y -
                         llap (G t) (Ff t) y - lscalar (G t) y +
                         &(dimindex(:N)) / (&2 * (b - t))) - llap (G t) (Ff t) y`]
                P2BS_W_DEFECT_ZERO) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    USE_THEN "e95" (MP_TAC o SPECL [`t:real`; `y:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < b - t` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    DISCH_THEN(LABEL_TAC "hw")] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`; `u:real^N`; `v:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t) /\
                smooth_map_on U (\y. lift((Ff:real->real^N->real) t y))` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(b - t = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the affine relations of the defect h of F with F *)
  MP_TAC(ISPECL
   [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `(Ff:real->real^N->real) t`;
    `\y. (lgrad2 ((G:real->real^N->real^N^N) t) ((Ff:real->real^N->real) t) y -
          llap (G t) (Ff t) y - lscalar (G t) y +
          &(dimindex(:N)) / (&2 * (b - t))) - llap (G t) (Ff t) y`;
    `b - t`; `--(&(dimindex(:N)) / (&2 * (b - t)))`; `y:real^N`] P2BS_AFFINE_RELATIONS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    USE_THEN "e95" (MP_TAC o SPECL [`t:real`; `z:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `~(b - t = &0)` THEN CONV_TAC REAL_FIELD;
    STRIP_TAC] THEN
  (* the vanishing defect of W at (t,y) *)
  USE_THEN "hw" (MP_TAC o SPECL [`t:real`; `y:real^N`; `\m:num. vec 0:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `(Ff:real->real^N->real) t`;
                 `y:real^N`; `\m:num. vec 0:real^N`] P2BS_CONTR_RMCOMM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `(Ff:real->real^N->real) t`;
                 `y:real^N`; `\m:num. vec 0:real^N`] P2BS_CONTR_XGRAD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  DISCH_TAC THEN
  (* the norm of T = Ric + Hess F - G/(2(b - t)) *)
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `(Ff:real->real^N->real) t`;
                 `inv(&2 * (b - t))`; `y:real^N`] P2BS_T_NORM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "tn")] THEN
  SUBGOAL_THEN
   `ltnorm2 2 ((G:real->real^N->real^N^N) t)
      (\y u. lric2 (G t) y u + lnabla 1 (G t) (lnabla 0 (G t) (\z u. (Ff:real->real^N->real) t z)) y u -
             inv(&2 * (b - t)) * lmetric2 (G t) y u) y = &0`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BS_SOL_ALG THEN
    MAP_EVERY EXISTS_TAC
     [`b - t`; `llap ((G:real->real^N->real^N^N) t) ((Ff:real->real^N->real) t) y`;
      `lgrad2 ((G:real->real^N->real^N^N) t) ((Ff:real->real^N->real) t) y`;
      `lscalar ((G:real->real^N->real^N^N) t) y`;
      `llap ((G:real->real^N->real^N^N) t)
         (\y. (lgrad2 (G t) ((Ff:real->real^N->real) t) y - llap (G t) (Ff t) y -
               lscalar (G t) y + &(dimindex(:N)) / (&2 * (b - t))) - llap (G t) (Ff t) y) y`;
      `rfa_lginner ((G:real->real^N->real^N^N) t)
         (\y. (lgrad2 (G t) ((Ff:real->real^N->real) t) y - llap (G t) (Ff t) y -
               lscalar (G t) y + &(dimindex(:N)) / (&2 * (b - t))) - llap (G t) (Ff t) y)
         (Ff t) y`;
      `ltinner 2 ((G:real->real^N->real^N^N) t) (lric2 (G t))
         (lnabla 1 (G t) (lnabla 0 (G t) (\z u. (Ff:real->real^N->real) t z))) y`;
      `ltinner 2 ((G:real->real^N->real^N^N) t)
         (lnabla 1 (G t) (lnabla 0 (G t) (\z u. (Ff:real->real^N->real) t z)))
         (lnabla 1 (G t) (lnabla 0 (G t) (\z u. Ff t z))) y`;
      `ltnorm2 2 ((G:real->real^N->real^N^N) t) (lric2 (G t)) y`;
      `&(dimindex(:N))`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "tn" (K ALL_TAC) THEN
  (* T = 0 *)
  MP_TAC(ISPECL
   [`2`; `U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
    `\y u. lric2 ((G:real->real^N->real^N^N) t) y u +
           lnabla 1 (G t) (lnabla 0 (G t) (\z u. (Ff:real->real^N->real) t z)) y u -
           inv(&2 * (b - t)) * lmetric2 (G t) y u`; `y:real^N`] LTNORM2_EQ_0) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFA_TENSOR_FIELD_LIN3 THEN REWRITE_TAC[ETA_AX] THEN
    ASM_SIMP_TAC[LRG_LRIC2_FIELD; LRG_LMETRIC2_FIELD; P2BS_HESS_FIELD];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `\m:num. if m = 1 then u:real^N else v`) THEN
  REWRITE_TAC[lric2; lmetric2] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `a + b - c = &0 <=> a + b = c`] THEN DISCH_THEN ACCEPT_TAC);;

(* SOL.A16 The time derivative of a space-time function along the path    *)
(* s -> (y, 1 - s) is minus its tau-derivative wan_tder.                    *)

let P2BS_TDER_PATH = prove
 (`!(f:real^(N,1)finite_sum->real) S (y:real^N) t.
     open S /\ smooth_map_on S (\w. lift(f w)) /\ pastecart y (lift(&1 - t)) IN S
     ==> ((\s. f(pastecart y (lift(&1 - s)))) has_real_derivative
          --(wan_tder f (pastecart y (lift(&1 - t))))) (atreal t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\w. lift((f:real^(N,1)finite_sum->real) w)) differentiable
                (at (pastecart y (lift(&1 - t))))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `S:real^(N,1)finite_sum->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `D = frechet_derivative (\w. lift((f:real^(N,1)finite_sum->real) w))
                                     (at (pastecart y (lift(&1 - t))))` THEN
  SUBGOAL_THEN `linear (D:real^(N,1)finite_sum->real^1) /\
                ((\w. lift((f:real^(N,1)finite_sum->real) w)) has_derivative D)
                (at (pastecart y (lift(&1 - t))))` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN ASM_SIMP_TAC[LINEAR_FRECHET_DERIVATIVE; GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\x:real^1. pastecart (y:real^N) (lift(&1) - x)) has_derivative
                 (\h. pastecart (vec 0) (--h))) (at (lift t))` ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
    MP_TAC(ISPECL [`\x:real^1. lift(&1)`; `\h:real^1. vec 0:real^1`; `\x:real^1. x`;
                   `\h:real^1. h`; `at(lift t)`] HAS_DERIVATIVE_SUB) THEN
    REWRITE_TAC[HAS_DERIVATIVE_CONST; HAS_DERIVATIVE_ID; VECTOR_SUB_LZERO; ETA_AX];
    ALL_TAC] THEN
  REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT] THEN
  SUBGOAL_THEN
   `(lift o (\s. (f:real^(N,1)finite_sum->real) (pastecart y (lift(&1 - s)))) o drop) =
    (\w. lift(f w)) o (\x:real^1. pastecart (y:real^N) (lift(&1) - x))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_SUB; LIFT_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x:real^1. --(wan_tder (f:real^(N,1)finite_sum->real) (pastecart y (lift(&1 - t)))) % x) =
    (D:real^(N,1)finite_sum->real^1) o (\h. pastecart (vec 0) (--h))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; wan_tder] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `h:real^1` THEN
    SUBGOAL_THEN `pastecart (vec 0:real^N) (--h:real^1) =
                  (--(drop h)) % pastecart (vec 0) (lift(&1))` SUBST1_TAC THENL
     [REWRITE_TAC[PASTECART_EQ; FSTCART_PASTECART; SNDCART_PASTECART; FSTCART_CMUL;
                  SNDCART_CMUL; VECTOR_MUL_RZERO] THEN
      REWRITE_TAC[GSYM DROP_EQ; DROP_NEG; DROP_CMUL; LIFT_DROP] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[LINEAR_CMUL] THEN REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[GSYM LIFT_SUB]);;

(* SOL.A17x The scalar curvature at chart_inv c y read in the chart c.      *)

let P2BS_MFD_SCALAR_CHART_INV = prove
 (`!top atlas (g:B->real^N^N) c y.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ c IN atlas /\
     y IN IMAGE (SND c) (FST c)
     ==> mfd_scalar atlas g (chart_inv c y) = lscalar (metric_local atlas c g) y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `c:(B->bool)#(B->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `c:(B->bool)#(B->real^N)` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:B->bool`; `phi:B->real^N`] THEN DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `U:B->bool`; `phi:B->real^N`; `g:B->real^N^N`;
                 `chart_inv (U:B->bool,phi:B->real^N) y`] MFD_SCALAR_CHART) THEN
  ASM_SIMP_TAC[]);;


(* SOL.A17a From the space-first chart data in tau to (time, space): the   *)
(* flip map, joint smoothness of linf(1 - t)(chart_inv c y), and the time   *)
(* derivative in terms of wan_tder.                                         *)

let P2BS_FLIP2_SMOOTH = prove
 (`!s:real^(1,N)finite_sum->bool.
     open s ==> smooth_map_on s (\z. pastecart (sndcart z) (lift(&1) - fstcart z))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`s:real^(1,N)finite_sum->bool`; `\z:real^(1,N)finite_sum. z`;
                   `sndcart:real^(1,N)finite_sum->real^N`] SMOOTH_MAP_ON_LINEAR_O) THEN
    ASM_REWRITE_TAC[LINEAR_SNDCART; SMOOTH_MAP_ON_ID; o_DEF; ETA_AX];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
    MP_TAC(ISPECL [`s:real^(1,N)finite_sum->bool`; `\z:real^(1,N)finite_sum. z`;
                   `fstcart:real^(1,N)finite_sum->real^1`] SMOOTH_MAP_ON_LINEAR_O) THEN
    ASM_REWRITE_TAC[LINEAR_FSTCART; SMOOTH_MAP_ON_ID; o_DEF; ETA_AX]]);;

let P2BS_CFUN_JOINT = prove
 (`!(c:(B->bool)#(B->real^N)) (linf:real->B->real) a tmax.
     open(IMAGE (SND c) (FST c)) /\ &1 - a <= tmax /\
     smooth_map_on (p2bw_cdom c tmax) (\z. lift(p2bw_cfun c linf z))
     ==> smooth_map_on (interval(lift a,lift(&1)) PCROSS IMAGE (SND c) (FST c))
           (\z. lift(linf (&1 - drop(fstcart z)) (chart_inv c (sndcart z))))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `(\w. lift(p2bw_cfun (c:(B->bool)#(B->real^N)) (linf:real->B->real) w)) o
              (\z:real^(1,N)finite_sum. pastecart (sndcart z) (lift(&1) - fstcart z))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[o_THM; p2bw_cfun; FSTCART_PASTECART; SNDCART_PASTECART; DROP_SUB; LIFT_DROP];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `p2bw_cdom (c:(B->bool)#(B->real^N)) tmax` THEN
  ASM_SIMP_TAC[P2BX_CDOM_OPEN; OPEN_PCROSS; OPEN_INTERVAL; P2BS_FLIP2_SMOOTH] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
              FSTCART_PASTECART; SNDCART_PASTECART; p2bw_cdom; IN_ELIM_THM; IN_INTERVAL_1;
              DROP_SUB; LIFT_DROP] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P2BS_CHART_EQS = prove
 (`!top atlas (g:real->B->real^3^3) (linf:real->B->real) c t y tmax.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas (g t) /\ c IN atlas /\
     y IN IMAGE (SND c) (FST c) /\ t < &1 /\ &1 - t < tmax /\
     smooth_map_on (p2bw_cdom c tmax) (\z. lift(p2bw_cfun c linf z)) /\
     (!c z. c IN atlas /\ fstcart z IN IMAGE (SND c) (FST c) /\ &0 < drop(sndcart z)
            ==> wan_tder (p2bw_cfun c linf) z +
                lgrad2 (p2bw_slice (p2bw_cmet atlas c (&1) g) z)
                       (p2bw_fslice (p2bw_cfun c linf) z) (fstcart z) -
                p2bw_cscal atlas c (&1) g z + &3 / (&2 * drop(sndcart z)) -
                llap (p2bw_slice (p2bw_cmet atlas c (&1) g) z)
                     (p2bw_fslice (p2bw_cfun c linf) z) (fstcart z) = &0 /\
                &2 * llap (p2bw_slice (p2bw_cmet atlas c (&1) g) z)
                          (p2bw_fslice (p2bw_cfun c linf) z) (fstcart z) -
                lgrad2 (p2bw_slice (p2bw_cmet atlas c (&1) g) z)
                       (p2bw_fslice (p2bw_cfun c linf) z) (fstcart z) +
                p2bw_cscal atlas c (&1) g z +
                (p2bw_cfun c linf z - &3) / drop(sndcart z) = &0)
     ==> ((\s. linf (&1 - s) (chart_inv c y)) has_real_derivative
          lgrad2 (metric_local atlas c (g t)) (\y. linf (&1 - t) (chart_inv c y)) y -
          llap (metric_local atlas c (g t)) (\y. linf (&1 - t) (chart_inv c y)) y -
          lscalar (metric_local atlas c (g t)) y + &3 / (&2 * (&1 - t))) (atreal t) /\
         &2 * llap (metric_local atlas c (g t)) (\y. linf (&1 - t) (chart_inv c y)) y -
         lgrad2 (metric_local atlas c (g t)) (\y. linf (&1 - t) (chart_inv c y)) y +
         lscalar (metric_local atlas c (g t)) y +
         (linf (&1 - t) (chart_inv c y) - &3) / (&1 - t) = &0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "sm") (LABEL_TAC "eqs")))))))) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "eqs" (MP_TAC o SPECL [`c:(B->bool)#(B->real^3)`;
                                  `pastecart (y:real^3) (lift(&1 - t))`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[p2bw_slice; p2bw_fslice; p2bw_cmet; p2bw_cfun; p2bw_cscal; FSTCART_PASTECART;
              SNDCART_PASTECART; LIFT_DROP; REAL_ARITH `&1 - (&1 - t) = t`; ETA_AX] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) t`; `c:(B->bool)#(B->real^3)`; `y:real^3`]
                P2BS_MFD_SCALAR_CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`p2bw_cfun (c:(B->bool)#(B->real^3)) (linf:real->B->real)`;
                 `p2bw_cdom (c:(B->bool)#(B->real^3)) tmax`; `y:real^3`; `t:real`]
                P2BS_TDER_PATH) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[P2BX_CDOM_OPEN] THEN
    REWRITE_TAC[p2bw_cdom; IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[p2bw_cfun; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  DISCH_TAC THEN MATCH_MP_TAC RFA_HC_HRD_EQ THEN
  EXISTS_TAC `--(wan_tder (p2bw_cfun (c:(B->bool)#(B->real^3)) (linf:real->B->real))
                          (pastecart y (lift(&1 - t))))` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `w + a - b + c - d = &0 ==> --w = a - d - b + c`) THEN
  FIRST_ASSUM ACCEPT_TAC);;

(* SOL.A17 The statement's chart data in tau (p2bw coordinates) as a local *)
(* flow in t = 1 - tau: the scalar curvature in a chart, and the local       *)
(* soliton equation in every chart (P2BS_LOCAL_SOLITON).                     *)

let P2BS_CHART_SOLITON = prove
 (`!top atlas (g:real->B->real^3^3) (linf:real->B->real) c s.
     (!a. a < &1 ==> ricci_flow_on (top,atlas) a (&1) g) /\
     (!c tmax. c IN atlas
               ==> smooth_map_on (p2bw_cdom c tmax) (\z. lift(p2bw_cfun c linf z))) /\
     (!c z. c IN atlas /\ fstcart z IN IMAGE (SND c) (FST c) /\ &0 < drop(sndcart z)
            ==> wan_tder (p2bw_cfun c linf) z +
                lgrad2 (p2bw_slice (p2bw_cmet atlas c (&1) g) z)
                       (p2bw_fslice (p2bw_cfun c linf) z) (fstcart z) -
                p2bw_cscal atlas c (&1) g z + &3 / (&2 * drop(sndcart z)) -
                llap (p2bw_slice (p2bw_cmet atlas c (&1) g) z)
                     (p2bw_fslice (p2bw_cfun c linf) z) (fstcart z) = &0 /\
                &2 * llap (p2bw_slice (p2bw_cmet atlas c (&1) g) z)
                          (p2bw_fslice (p2bw_cfun c linf) z) (fstcart z) -
                lgrad2 (p2bw_slice (p2bw_cmet atlas c (&1) g) z)
                       (p2bw_fslice (p2bw_cfun c linf) z) (fstcart z) +
                p2bw_cscal atlas c (&1) g z +
                (p2bw_cfun c linf z - &3) / drop(sndcart z) = &0) /\
     c IN atlas /\ s < &1
     ==> !y u v. y IN IMAGE (SND c) (FST c)
                 ==> lricci (metric_local atlas c (g s)) y u v +
                     lnabla 1 (metric_local atlas c (g s))
                       (lnabla 0 (metric_local atlas c (g s))
                          (\z w. linf (&1 - s) (chart_inv c z))) y
                       (\m. if m = 1 then u else v) =
                     inv(&2 * (&1 - s)) * (u dot (metric_local atlas c (g s) y ** v))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rf") (CONJUNCTS_THEN2 (LABEL_TAC "sm")
    (CONJUNCTS_THEN2 (LABEL_TAC "eqs") STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `ricci_flow_on (top,atlas) (s - &1) (&1) (g:real->B->real^3^3)` ASSUME_TAC THENL
   [USE_THEN "rf" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:B topology) (atlas:((B->bool)#(B->real^3))->bool)`
  ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `s - &1`; `&1`;
                 `g:real->B->real^3^3`; `c:(B->bool)#(B->real^3)`] LRG_RICCI_FLOW_ON_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c)`; `s - &1`; `&1`;
                 `\t. metric_local atlas (c:(B->bool)#(B->real^3)) ((g:real->B->real^3^3) t)`;
                 `\t y. (linf:real->B->real) (&1 - t) (chart_inv (c:(B->bool)#(B->real^3)) y)`]
                P2BS_LOCAL_SOLITON) THEN
  SUBGOAL_THEN `!t. s - &1 < t /\ t < &1 ==> riemannian_metric atlas ((g:real->B->real^3^3) t)`
  (LABEL_TAC "riem") THENL
   [UNDISCH_TAC `ricci_flow_on (top,atlas) (s - &1) (&1) (g:real->B->real^3^3)` THEN
    REWRITE_TAC[ricci_flow_on] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_3] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2BS_CFUN_JOINT THEN EXISTS_TAC `&2 - s` THEN
      ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`t:real`; `y:real^3`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:real->B->real^3^3`; `linf:real->B->real`; `c:(B->bool)#(B->real^3)`;
                   `t:real`; `y:real^3`; `&2 - s`] P2BS_CHART_EQS) THEN
    (ANTS_TAC THENL
      [ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THEN TRY(USE_THEN "eqs" ACCEPT_TAC) THEN
       ASM_REAL_ARITH_TAC;
       SIMP_TAC[]]);
    DISCH_THEN(fun th -> MAP_EVERY X_GEN_TAC [`y:real^3`; `u:real^3`; `v:real^3`] THEN
                         DISCH_TAC THEN
                         MP_TAC(SPECL [`s:real`; `y:real^3`; `u:real^3`; `v:real^3`] th)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]] THEN
  ALL_TAC);;

(* SOL.A18 The shrinker equation for g(s)/(1 - s) with potential           *)
(* linf(1 - s) (p2b_shrinker), from the chart equation by scale invariance  *)
(* of Ric and of the Hessian.                                               *)

let P2BS_LNABLA_SCALE = prove
 (`!U (G:real^N->real^N^N) c k tf y u.
     metric_field U G /\ y IN U /\ &0 < c
     ==> lnabla k (\z. c %% G z) tf y u = lnabla k G tf y u`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!v w. christoffel (\z. c %% (G:real^N->real^N^N) z) y v w =
                      christoffel G y v w` (fun th -> REWRITE_TAC[lnabla; th]) THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC CHRISTOFFEL_SCALE THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

let P2BS_SLICE_CFUN_SMOOTH = prove
 (`!(c:(B->bool)#(B->real^N)) (linf:real->B->real) tau tmax.
     open(IMAGE (SND c) (FST c)) /\ &0 < tau /\ tau < tmax /\
     smooth_map_on (p2bw_cdom c tmax) (\z. lift(p2bw_cfun c linf z))
     ==> smooth_map_on (IMAGE (SND c) (FST c)) (\y. lift(linf tau (chart_inv c y)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `(\w. lift(p2bw_cfun (c:(B->bool)#(B->real^N)) (linf:real->B->real) w)) o
              (\y:real^N. pastecart y (lift tau))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[o_THM; p2bw_cfun; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `p2bw_cdom (c:(B->bool)#(B->real^N)) tmax` THEN
  ASM_SIMP_TAC[P2BX_CDOM_OPEN] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; p2bw_cdom; IN_ELIM_THM; FSTCART_PASTECART;
                SNDCART_PASTECART; LIFT_DROP] THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST]]);;

let P2BS_LFLOW_METRIC_FIELD = prove
 (`!U a b (G:real->real^N->real^N^N).
     lricci_flow U a b G ==> !t. a < t /\ t < b ==> metric_field U (G t)`,
  MESON_TAC[LRG_FLOW_BASIC]);;

let P2BS_SHRINKER = prove
 (`!top atlas (g:real->B->real^3^3) (linf:real->B->real) s.
     (!a. a < &1 ==> ricci_flow_on (top,atlas) a (&1) g) /\
     (!c tmax. c IN atlas
               ==> smooth_map_on (p2bw_cdom c tmax) (\z. lift(p2bw_cfun c linf z))) /\
     (!c z. c IN atlas /\ fstcart z IN IMAGE (SND c) (FST c) /\ &0 < drop(sndcart z)
            ==> wan_tder (p2bw_cfun c linf) z +
                lgrad2 (p2bw_slice (p2bw_cmet atlas c (&1) g) z)
                       (p2bw_fslice (p2bw_cfun c linf) z) (fstcart z) -
                p2bw_cscal atlas c (&1) g z + &3 / (&2 * drop(sndcart z)) -
                llap (p2bw_slice (p2bw_cmet atlas c (&1) g) z)
                     (p2bw_fslice (p2bw_cfun c linf) z) (fstcart z) = &0 /\
                &2 * llap (p2bw_slice (p2bw_cmet atlas c (&1) g) z)
                          (p2bw_fslice (p2bw_cfun c linf) z) (fstcart z) -
                lgrad2 (p2bw_slice (p2bw_cmet atlas c (&1) g) z)
                       (p2bw_fslice (p2bw_cfun c linf) z) (fstcart z) +
                p2bw_cscal atlas c (&1) g z +
                (p2bw_cfun c linf z - &3) / drop(sndcart z) = &0) /\
     s < &1
     ==> p2b_shrinker (top,atlas) (\x. inv(&1 - s) %% g s x) (linf (&1 - s))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rf") (CONJUNCTS_THEN2 (LABEL_TAC "sm")
    (CONJUNCTS_THEN2 (LABEL_TAC "eqs") ASSUME_TAC))) THEN
  SUBGOAL_THEN `ricci_flow_on (top,atlas) (s - &1) (&1) (g:real->B->real^3^3)` ASSUME_TAC THENL
   [USE_THEN "rf" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:B topology) (atlas:((B->bool)#(B->real^3))->bool) /\
                riemannian_metric atlas ((g:real->B->real^3^3) s)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ricci_flow_on (top,atlas) (s - &1) (&1) (g:real->B->real^3^3)` THEN
    REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(&1 - s)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[p2b_shrinker] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[mfd_smooth_on] THEN X_GEN_TAC `c:(B->bool)#(B->real^3)` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `FST (c:(B->bool)#(B->real^3)) INTER topspace top = FST c` SUBST1_TAC THENL
     [MP_TAC(ISPECL [`top:B topology`; `FST (c:(B->bool)#(B->real^3))`] OPEN_IN_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `\y. lift((linf:real->B->real) (&1 - s) (chart_inv (c:(B->bool)#(B->real^3)) y))` THEN
    CONJ_TAC THENL [REWRITE_TAC[o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC P2BS_SLICE_CFUN_SMOOTH THEN EXISTS_TAC `&2 - s` THEN
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:B`; `u:real^3`; `v:real^3`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `x:B`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B)) x IN
                IMAGE (SND(chart_at atlas x)) (FST(chart_at atlas x))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B)))
                                    (FST(chart_at atlas x)))
                             (metric_local atlas (chart_at atlas x) ((g:real->B->real^3^3) s))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `s - &1`; `&1`;
                   `g:real->B->real^3^3`; `chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B)`]
                  LRG_RICCI_FLOW_ON_CHART) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP P2BS_LFLOW_METRIC_FIELD) THEN
    DISCH_THEN(MP_TAC o SPEC `s:real`) THEN REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[mfd_ricci; p2b_mfd_hess; METRIC_LOCAL_CMUL; ETA_AX] THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B)))
                        (FST(chart_at atlas x))`;
                 `metric_local atlas (chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B))
                               ((g:real->B->real^3^3) s)`;
                 `inv(&1 - s)`; `SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B)) x`;
                 `u:real^3`; `v:real^3`] LRICCI_SCALE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B)))
                        (FST(chart_at atlas x))`;
                 `metric_local atlas (chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B))
                               ((g:real->B->real^3^3) s)`;
                 `inv(&1 - s)`; `1`] P2BS_LNABLA_SCALE) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
                 `linf:real->B->real`; `chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B)`;
                 `s:real`] P2BS_CHART_SOLITON) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B)) x`;
                             `u:real^3`; `v:real^3`]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `lnabla 0 (metric_local atlas (chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B))
                ((g:real->B->real^3^3) s))
      (\z w. (linf:real->B->real) (&1 - s) (chart_inv (chart_at atlas x) z)) =
    (\z w. drop(frechet_derivative (\y. lift(linf (&1 - s) (chart_inv (chart_at atlas x) y)))
                                   (at z) (w 1)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; P2BS_LNABLA0]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) s`; `x:B`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL; REAL_INV_MUL] THEN REAL_ARITH_TAC);;

(* SOL.A19 A flat point has zero Ricci and scalar curvature, and at a flat  *)
(* slice the potential satisfies Hess f = g/(2 tau) and |grad f|^2 = f/tau.  *)

let P2BS_FLAT_RIC_ZERO = prove
 (`!U (G:real^N->real^N^N) y.
     metric_field U G /\ y IN U /\
     (!u v. ~collinear {vec 0,u,v} ==> lsectional G y u v = &0)
     ==> (!u v. lricci G y u v = &0) /\ lscalar G y = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!u v w. lriemann (G:real^N->real^N^N) y u v w = vec 0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `&0`]
                  APX_CONST_CURV_RIEMANN) THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u v. lricci (G:real^N->real^N^N) y u v = &0` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[lricci; VEC_COMPONENT; SUM_0]; ALL_TAC] THEN
  ASM_REWRITE_TAC[lscalar; REAL_MUL_RZERO; SUM_0]);;

let P2BS_HESS_CONST_LAP = prove
 (`!U (G:real^N->real^N^N) (f:real^N->real) c y.
     metric_field U G /\ smooth_map_on U (\z. lift(f z)) /\ y IN U /\
     (!u v. lnabla 1 G (lnabla 0 G (\z w. f z)) y (\m. if m = 1 then u else v) =
            c * (u dot (G y ** v)))
     ==> llap G f y = c * &(dimindex(:N))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `f:real^N->real`; `y:real^N`]
                P2BS_LTINNER_HESS_METRIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `f:real^N->real`] P2BS_HESS_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lnabla 1 (G:real^N->real^N^N) (lnabla 0 G (\z u. (f:real^N->real) z))`;
                 `lmetric2 (G:real^N->real^N^N)`; `y:real^N`] RFA_LTINNER_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `ltinner 2 (G:real^N->real^N^N) (lmetric2 G) (\z u. c * lmetric2 G z u) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFA_LTINNER_RLOCAL THEN X_GEN_TAC `w:num->real^N` THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `lnabla 1 (G:real^N->real^N^N) (lnabla 0 G (\z u. (f:real^N->real) z)) y
                  (\m. if m = 1 then w 1 else w 2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RFA_TF_AGREE THEN MAP_EVERY EXISTS_TAC [`2`; `U:real^N->bool`] THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `m = 1 \/ m = 2` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
      ASM_REWRITE_TAC[lmetric2]];
    REWRITE_TAC[RFA_LTINNER_RCMUL; ETA_AX] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_LTNORM2_METRIC) THEN
    ASM_REWRITE_TAC[RFA_LTNORM2_LTINNER] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]);;

(* SOL.A20 At a flat slice s the potential f = linf(1 - s) satisfies       *)
(* Hess f = g(s)/(2(1 - s)) and |grad f|^2 = f/(1 - s) (Part A and (9.5)).   *)

let P2BS_FLAT_SLICE = prove
 (`!top atlas (g:real->B->real^3^3) (linf:real->B->real) s.
     (!a. a < &1 ==> ricci_flow_on (top,atlas) a (&1) g) /\
     (!c tmax. c IN atlas
               ==> smooth_map_on (p2bw_cdom c tmax) (\z. lift(p2bw_cfun c linf z))) /\
     (!c z. c IN atlas /\ fstcart z IN IMAGE (SND c) (FST c) /\ &0 < drop(sndcart z)
            ==> wan_tder (p2bw_cfun c linf) z +
                lgrad2 (p2bw_slice (p2bw_cmet atlas c (&1) g) z)
                       (p2bw_fslice (p2bw_cfun c linf) z) (fstcart z) -
                p2bw_cscal atlas c (&1) g z + &3 / (&2 * drop(sndcart z)) -
                llap (p2bw_slice (p2bw_cmet atlas c (&1) g) z)
                     (p2bw_fslice (p2bw_cfun c linf) z) (fstcart z) = &0 /\
                &2 * llap (p2bw_slice (p2bw_cmet atlas c (&1) g) z)
                          (p2bw_fslice (p2bw_cfun c linf) z) (fstcart z) -
                lgrad2 (p2bw_slice (p2bw_cmet atlas c (&1) g) z)
                       (p2bw_fslice (p2bw_cfun c linf) z) (fstcart z) +
                p2bw_cscal atlas c (&1) g z +
                (p2bw_cfun c linf z - &3) / drop(sndcart z) = &0) /\
     s < &1 /\
     (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
              ==> mfd_sectional atlas (g s) x u v = &0)
     ==> !x. x IN topspace top
             ==> (!u v. p2b_mfd_hess atlas (g s) (linf (&1 - s)) x u v =
                        inv(&2 * (&1 - s)) * (u dot (g s x ** v))) /\
                 lgrad2 (metric_local atlas (chart_at atlas x) (g s))
                        (linf (&1 - s) o chart_inv (chart_at atlas x))
                        (SND(chart_at atlas x) x) =
                 linf (&1 - s) x / (&1 - s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rf") (CONJUNCTS_THEN2 (LABEL_TAC "sm")
    (CONJUNCTS_THEN2 (LABEL_TAC "eqs") (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "flat"))))) THEN
  X_GEN_TAC `x:B` THEN DISCH_TAC THEN
  SUBGOAL_THEN `ricci_flow_on (top,atlas) (s - &1) (&1) (g:real->B->real^3^3)` ASSUME_TAC THENL
   [USE_THEN "rf" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:B topology) (atlas:((B->bool)#(B->real^3))->bool) /\
                riemannian_metric atlas ((g:real->B->real^3^3) s)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ricci_flow_on (top,atlas) (s - &1) (&1) (g:real->B->real^3^3)` THEN
    REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `x:B`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B)) x IN
                IMAGE (SND(chart_at atlas x)) (FST(chart_at atlas x))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B)))
                                    (FST(chart_at atlas x)))
                             (metric_local atlas (chart_at atlas x) ((g:real->B->real^3^3) s))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `s - &1`; `&1`;
                   `g:real->B->real^3^3`; `chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B)`]
                  LRG_RICCI_FLOW_ON_CHART) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP P2BS_LFLOW_METRIC_FIELD) THEN
    DISCH_THEN(MP_TAC o SPEC `s:real`) THEN REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* flat: Ric = 0 and R = 0 in the chart *)
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B)))
                        (FST(chart_at atlas x))`;
                 `metric_local atlas (chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B))
                               ((g:real->B->real^3^3) s)`;
                 `SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B)) x`]
                P2BS_FLAT_RIC_ZERO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    USE_THEN "flat" (MP_TAC o SPECL [`x:B`; `u:real^3`; `v:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[mfd_sectional]];
    STRIP_TAC] THEN
  (* the chart soliton equation at x *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
                 `linf:real->B->real`; `chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B)`;
                 `s:real`] P2BS_CHART_SOLITON) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B)) x`) THEN
  ASM_REWRITE_TAC[REAL_ADD_LID] THEN DISCH_THEN(LABEL_TAC "h1") THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) s`; `x:B`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "gloc") THEN
  SUBGOAL_THEN
   `lnabla 0 (metric_local atlas (chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B))
                ((g:real->B->real^3^3) s))
      (\z w. (linf:real->B->real) (&1 - s) (chart_inv (chart_at atlas x) z)) =
    (\z w. drop(frechet_derivative (\y. lift(linf (&1 - s) (chart_inv (chart_at atlas x) y)))
                                   (at z) (w 1)))`
  (LABEL_TAC "l0") THENL [REWRITE_TAC[FUN_EQ_THM; P2BS_LNABLA0]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[p2b_mfd_hess] THEN REPEAT GEN_TAC THEN
    USE_THEN "h1" (MP_TAC o SPECL [`u:real^3`; `v:real^3`]) THEN
    USE_THEN "l0" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "gloc" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  (* |grad f|^2 = f / tau from (9.5) with Lap f = 3/(2 tau) and R = 0 *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
                 `linf:real->B->real`; `chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B)`;
                 `s:real`; `SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B)) x`;
                 `&2 - s`] P2BS_CHART_EQS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THEN TRY(USE_THEN "eqs" ACCEPT_TAC) THEN
    ASM_REAL_ARITH_TAC;
    DISCH_THEN(MP_TAC o CONJUNCT2)] THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B)))
                        (FST(chart_at atlas x))`;
                 `metric_local atlas (chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B))
                               ((g:real->B->real^3^3) s)`;
                 `\y. (linf:real->B->real) (&1 - s)
                        (chart_inv (chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B)) y)`;
                 `inv(&2 * (&1 - s))`;
                 `SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B)) x`]
                P2BS_HESS_CONST_LAP) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2BS_SLICE_CFUN_SMOOTH THEN EXISTS_TAC `&2 - s` THEN
      ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[];
      USE_THEN "h1" ACCEPT_TAC];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `(linf:real->B->real) (&1 - s) o chart_inv (chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B)) =
    (\y. linf (&1 - s) (chart_inv (chart_at atlas x) y))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  ASM_SIMP_TAC[DIMINDEX_3] THEN
  SUBGOAL_THEN `~(&1 - s = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

(* SOL.A21 No slice is flat (MT Claim 9.36): a flat slice would be the     *)
(* Gaussian soliton, whose reduced volume is at least (4 pi)^(3/2) by the   *)
(* route input P2B_REQ_FLAT_GAUSS, while V < (4 pi)^(3/2).  The route       *)
(* theorem P2B_SOLITON_FROM_LINF_FIX_ROUTE.                                  *)

let P2BS_NONFLAT = prove
 (`!(w:B->bool) top atlas (g:real->B->real^3^3) (linf:real->B->real) V s.
     P2B_REQ_FLAT_GAUSS_STATEMENT w /\
     ~(topspace top = {}) /\ hausdorff_space top /\ connected_space top /\
     (!a. a < &1 ==> ricci_flow_on (top,atlas) a (&1) g) /\
     (!s. s < &1 ==> mfd_complete (top,atlas) (g s)) /\
     (!c tmax. c IN atlas
               ==> smooth_map_on (p2bw_cdom c tmax) (\z. lift(p2bw_cfun c linf z))) /\
     (!c z. c IN atlas /\ fstcart z IN IMAGE (SND c) (FST c) /\ &0 < drop(sndcart z)
            ==> wan_tder (p2bw_cfun c linf) z +
                lgrad2 (p2bw_slice (p2bw_cmet atlas c (&1) g) z)
                       (p2bw_fslice (p2bw_cfun c linf) z) (fstcart z) -
                p2bw_cscal atlas c (&1) g z + &3 / (&2 * drop(sndcart z)) -
                llap (p2bw_slice (p2bw_cmet atlas c (&1) g) z)
                     (p2bw_fslice (p2bw_cfun c linf) z) (fstcart z) = &0 /\
                &2 * llap (p2bw_slice (p2bw_cmet atlas c (&1) g) z)
                          (p2bw_fslice (p2bw_cfun c linf) z) (fstcart z) -
                lgrad2 (p2bw_slice (p2bw_cmet atlas c (&1) g) z)
                       (p2bw_fslice (p2bw_cfun c linf) z) (fstcart z) +
                p2bw_cscal atlas c (&1) g z +
                (p2bw_cfun c linf z - &3) / drop(sndcart z) = &0) /\
     p2bg_rvol (top,atlas) g linf V /\ V < sqrt(&4 * pi) pow 3 /\ s < &1
     ==> ?x. x IN topspace top /\ &0 < mfd_rm_norm atlas (g s) x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "req") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "rf") (CONJUNCTS_THEN2 (LABEL_TAC "comp")
    (CONJUNCTS_THEN2 (LABEL_TAC "sm") (CONJUNCTS_THEN2 (LABEL_TAC "eqs")
    (CONJUNCTS_THEN2 (LABEL_TAC "rvol") (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))))))))) THEN
  SUBGOAL_THEN `ricci_flow_on (top,atlas) (s - &1) (&1) (g:real->B->real^3^3)` ASSUME_TAC THENL
   [USE_THEN "rf" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:B topology) (atlas:((B->bool)#(B->real^3))->bool) /\
                riemannian_metric atlas ((g:real->B->real^3^3) s)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ricci_flow_on (top,atlas) (s - &1) (&1) (g:real->B->real^3^3)` THEN
    REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(fun th -> LABEL_TAC "rmz"
    (REWRITE_RULE[NOT_EXISTS_THM; TAUT `~(p /\ q) <=> p ==> ~q`; REAL_NOT_LT] th)) THEN
  SUBGOAL_THEN `!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                        ==> mfd_sectional atlas ((g:real->B->real^3^3) s) x u v = &0`
  (LABEL_TAC "flat") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(g:real->B->real^3^3) s`; `x:B`; `u:real^3`; `v:real^3`]
                  MFD_SECTIONAL_LE_RM_NORM) THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "rmz" (MP_TAC o SPEC `x:B`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
                 `linf:real->B->real`; `s:real`] P2BS_FLAT_SLICE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "fd")] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
                 `linf:real->B->real`; `s:real`] P2BS_SHRINKER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[p2b_shrinker] THEN STRIP_TAC] THEN
  USE_THEN "rvol" (MP_TAC o SPEC `&1 - s` o REWRITE_RULE[p2bg_rvol]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_ARITH `&1 - (&1 - s) = s`]] THEN
  STRIP_TAC THEN
  USE_THEN "req" (MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                                  `(g:real->B->real^3^3) s`; `(linf:real->B->real) (&1 - s)`;
                                  `&1 - s`] o REWRITE_RULE[P2B_REQ_FLAT_GAUSS_STATEMENT]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P2B_SOLITON_FROM_LINF_FIX_ROUTE = prove
 (`!w:B->bool. P2B_SOLITON_FROM_LINF_FIX_ROUTE_STATEMENT w`,
  GEN_TAC THEN
  REWRITE_TAC[P2B_SOLITON_FROM_LINF_FIX_ROUTE_STATEMENT; P2B_SOLITON_FROM_LINF_FIX_STATEMENT] THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THENL
   [MATCH_MP_TAC P2BS_SHRINKER THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2BS_NONFLAT THEN
    MAP_EVERY EXISTS_TAC [`w:B->bool`; `linf:real->B->real`; `V:real`] THEN
    ASM_REWRITE_TAC[]]);;

