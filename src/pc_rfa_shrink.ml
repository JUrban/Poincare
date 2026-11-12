(* ========================================================================= *)
(* Unit pc_rfa_shrink: compact gradient shrinkers of positive curvature are  *)
(* round (the statement P2B_REQ_RFA_SHRINKER_ROUND_STATEMENT of              *)
(* pc_p2b_shrinkreq, reduced here to its 2-d clause).  The 3-d clause by     *)
(* Hamilton's pinching at a maximum point of |Ric|^2 / R^2 (elliptic, no     *)
(* flow): the soliton identities                                             *)
(*   <Ric, Lap_f Ric> = |Ric|^2 - 2 <Ric, Rm(Ric)>,                          *)
(*   Lap_f R = R - 2 |Ric|^2                                                 *)
(* from frame jets, the Schur inequality in a Ricci eigenframe, Einstein,    *)
(* constant curvature (RFA_SHRINKER_ROUND_3D).                               *)
(* ========================================================================= *)

needs "src/pc_rfa_htrace.ml";;
needs "src/pc_rfa_cone.ml";;
needs "src/pc_p2b_shrinkreq.ml";;
needs "src/pc_apx_scal.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The shrinker equation in every chart (RFA_SHRINKER_CHART),                *)
(* the derivative of the contracted Bianchi identity in frames               *)
(* (RFA_SH_DCB_FRAME), the Ricci identity for df in generator form           *)
(* (RFA_SH_F3_RICCI), and the shrinker equation with its first two           *)
(* covariant derivatives as field identities (RFA_SH_SOL_EQON, _D2).         *)
(* ========================================================================= *)

let RFA_SHRINKER_CHART = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (f:A->real) c.
     p2b_shrinker (top,atlas) g f /\ c IN atlas
     ==> !y u. y IN IMAGE (SND c) (FST c)
               ==> lric2 (metric_local atlas c g) y u +
                   lnabla 1 (metric_local atlas c g)
                     (\z w. drop(frechet_derivative (\y. lift(f(chart_inv c y))) (at z) (w 1)))
                     y u =
                   inv(&2) * lmetric2 (metric_local atlas c g) y u`,
  REWRITE_TAC[FORALL_PAIR_THM; p2b_shrinker] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `g:A->real^N^N`; `f:A->real`; `U1:A->bool`; `phi:A->real^N`] THEN
  STRIP_TAC THEN REWRITE_TAC[FST; SND] THEN
  X_GEN_TAC `y:real^N` THEN X_GEN_TAC `uu:num->real^N` THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U1:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (IMAGE (phi:A->real^N) U1)
                  (\y. lift((f:A->real)(chart_inv (U1,phi) y)))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_smooth_on (atlas:((A->bool)#(A->real^N))->bool) (topspace top)
                   (\x. lift((f:A->real) x))` THEN
    REWRITE_TAC[mfd_smooth_on] THEN DISCH_THEN(MP_TAC o SPEC `(U1:A->bool,phi:A->real^N)`) THEN
    ASM_REWRITE_TAC[FST; SND; o_DEF] THEN
    SUBGOAL_THEN `U1 INTER topspace top = (U1:A->bool)` SUBST1_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET; SET_RULE `!s t:A->bool. s SUBSET t ==> s INTER t = s`];
      SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^N) U1`;
                 `\y. (f:A->real)(chart_inv (U1:A->bool,phi:A->real^N) y)`]
         LRG_DF_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`1`; `IMAGE (phi:A->real^N) U1`;
                 `metric_local atlas (U1:A->bool,phi:A->real^N) (g:A->real^N^N)`;
                 `\z w. drop(frechet_derivative
                          (\y. lift((f:A->real)(chart_inv (U1:A->bool,phi:A->real^N) y)))
                          (at z) (w 1))`;
                 `(phi:A->real^N) x`; `uu:num->real^N`;
                 `\m:num. if m = 1 then (uu:num->real^N) 1 else uu 2`] LRG_LNABLA_AGREE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `m = 1 \/ m = 2` MP_TAC THENL
     [ASM_ARITH_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[ARITH]];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[lric2; lmetric2] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `(U1:A->bool,phi:A->real^N)`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`; `x:A`;
                 `(uu:num->real^N) 1`; `(uu:num->real^N) 2`] RFA_HESS_CHART_TRANS) THEN
  ASM_REWRITE_TAC[FST; SND] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`x:A`; `chart_jac (U1:A->bool,phi:A->real^N) (chart_at atlas (x:A)) x ((uu:num->real^N) 1)`;
     `chart_jac (U1:A->bool,phi:A->real^N) (chart_at atlas (x:A)) x ((uu:num->real^N) 2)`] o
     check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "mfd_ricci"
                                              with Failure _ -> false)) (concl th))) THEN
  ASM_REWRITE_TAC[mfd_ricci; p2b_mfd_hess] THEN DISCH_THEN(fun th ->
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `x:A`] METRIC_LOCAL_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN MP_TAC th) THEN
  MP_TAC(ISPEC `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`V2:A->bool`; `psi:A->real^N`] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN REWRITE_TAC[FST; SND] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U1:A->bool`; `phi:A->real^N`; `V2:A->bool`; `psi:A->real^N`;
                 `g:A->real^N^N`; `x:A`; `(uu:num->real^N) 1`; `(uu:num->real^N) 2`]
                LRG_LRICCI_CHART_TRANS) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U1:A->bool`; `phi:A->real^N`; `V2:A->bool`; `psi:A->real^N`;
                 `g:A->real^N^N`; `x:A`] METRIC_LOCAL_JAC) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN DISCH_THEN SUBST1_TAC THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `linear(chart_jac (U1:A->bool,phi:A->real^N) (V2,psi) x)` ASSUME_TAC THENL
   [REWRITE_TAC[chart_jac] THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    REWRITE_TAC[differentiable; SND] THEN
    EXISTS_TAC `chart_jac (U1:A->bool,phi:A->real^N) (V2,psi) x` THEN
    MATCH_MP_TAC CHART_TRANS_HAS_DERIVATIVE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
  ASM_SIMP_TAC[MATRIX_WORKS]);;

let RFA_SH_DCB_FRAME = prove
 (`!U (G:real^N->real^N^N) y (S:real^N^N) j l.
     metric_field U G /\ y IN U /\ matrix_inv(G y) = transp S ** S
     ==> sum(1..dimindex(:N))
           (\i. lnabla 3 G (lnabla 2 G (lric2 G)) y (rfa_ft S [i; j; i; l])) =
         inv(&2) * sum(1..dimindex(:N))
           (\i. lnabla 3 G (lnabla 2 G (lric2 G)) y (rfa_ft S [i; i; j; l]))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `rfa_sf 3 U (lnabla 2 G (lric2 (G:real^N->real^N^N))) /\
                rfa_sf 4 U (lnabla 3 G (lnabla 2 G (lric2 G))) /\
                rfa_sf 3 U (ltperm (swap(2,3)) (lnabla 2 G (lric2 G)))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`; `lric2 (G:real^N->real^N^N)`]
           RFA_SF_LNABLA) THEN
    MP_TAC(ISPECL [`3`; `U:real^N->bool`; `G:real^N->real^N^N`;
                   `lnabla 2 G (lric2 (G:real^N->real^N^N))`] RFA_SF_LNABLA) THEN
    ASM_SIMP_TAC[RFA_SF_LRIC2; ARITH] THEN REPEAT DISCH_TAC THEN
    MATCH_MP_TAC RFA_SF_LTPERM THEN ASM_SIMP_TAC[RFA_HT_SWAP23_PERMUTES; ARITH];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] RFA_CBIANCHI_EQON) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`1`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `ltcontr G (ltperm (swap(2,3)) (lnabla 2 G (lric2 (G:real^N->real^N^N))))`;
                 `\y u. inv(&2) * ltcontr G (lnabla 2 G (lric2 (G:real^N->real^N^N))) y u`]
                RFA_EQON_LNABLA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `rfa_sf 1 U (ltcontr G (lnabla 2 G (lric2 (G:real^N->real^N^N))))` ASSUME_TAC
  THENL
   [MP_TAC(CONV_RULE NUM_REDUCE_CONV (ISPECL [`1`; `U:real^N->bool`; `G:real^N->real^N^N`;
             `lnabla 2 G (lric2 (G:real^N->real^N^N))`] RFA_SF_LTCONTR)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`1`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `ltcontr G (lnabla 2 G (lric2 (G:real^N->real^N^N)))`; `inv(&2)`] RFA_LNE_CMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `ltensor_field 3 U (lnabla 2 G (lric2 (G:real^N->real^N^N))) /\
    (!u. smooth_map_on U (\y. lift(lnabla 2 G (lric2 G) y u))) /\
    ltensor_field 3 U (ltperm (swap(2,3)) (lnabla 2 G (lric2 G))) /\
    (!u. smooth_map_on U (\y. lift(ltperm (swap(2,3)) (lnabla 2 G (lric2 G)) y u)))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfa_sf 3 U (lnabla 2 G (lric2 (G:real^N->real^N^N)))` THEN
    UNDISCH_TAC `rfa_sf 3 U (ltperm (swap(2,3)) (lnabla 2 G (lric2 (G:real^N->real^N^N))))` THEN
    REWRITE_TAC[rfa_sf] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lnabla 1 G (ltcontr G (ltperm (swap(2,3)) (lnabla 2 G (lric2 (G:real^N->real^N^N)))))
      y (rfa_ft (S:real^N^N) [j; l]) =
    inv(&2) * lnabla 1 G (ltcontr G (lnabla 2 G (lric2 G))) y (rfa_ft S [j; l])`
  MP_TAC THENL
   [UNDISCH_TAC
     `rfa_eqon U (lnabla 1 G (ltcontr G (ltperm (swap(2,3)) (lnabla 2 G (lric2 (G:real^N->real^N^N))))))
                 (lnabla 1 G (\y u. inv(&2) * ltcontr G (lnabla 2 G (lric2 G)) y u))` THEN
    UNDISCH_TAC
     `rfa_eqon U (lnabla 1 G (\y u. inv(&2) * ltcontr G (lnabla 2 G (lric2 (G:real^N->real^N^N))) y u))
                 (\y u. inv(&2) * lnabla 1 G (ltcontr G (lnabla 2 G (lric2 G))) y u)` THEN
    REWRITE_TAC[rfa_eqon] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV
   (ISPECL [`1`; `U:real^N->bool`; `G:real^N->real^N^N`;
            `ltperm (swap(2,3)) (lnabla 2 G (lric2 (G:real^N->real^N^N)))`; `y:real^N`;
            `rfa_ft (S:real^N^N) [j; l]`] RFA_LNABLA_LTCONTR)) THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV
   (ISPECL [`1`; `U:real^N->bool`; `G:real^N->real^N^N`;
            `lnabla 2 G (lric2 (G:real^N->real^N^N))`; `y:real^N`;
            `rfa_ft (S:real^N^N) [j; l]`] RFA_LNABLA_LTCONTR)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `ltensor_field 4 U (lnabla 3 G (lnabla 2 G (lric2 (G:real^N->real^N^N)))) /\
                ltensor_field 4 U (lnabla 3 G (ltperm (swap(2,3)) (lnabla 2 G (lric2 G))))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `rfa_sf 4 U (lnabla 3 G (lnabla 2 G (lric2 (G:real^N->real^N^N))))` THEN
      SIMP_TAC[rfa_sf];
      MP_TAC(ISPECL [`3`; `U:real^N->bool`; `G:real^N->real^N^N`;
                     `ltperm (swap(2,3)) (lnabla 2 G (lric2 (G:real^N->real^N^N)))`]
                    RFA_SF_LNABLA) THEN
      ASM_SIMP_TAC[rfa_sf; ARITH]];
    ALL_TAC] THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV
   (ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`;
            `lnabla 3 G (lnabla 2 G (lric2 (G:real^N->real^N^N)))`; `y:real^N`; `S:real^N^N`;
            `rfa_ft (S:real^N^N) [j; l]`] RFA_LTCONTR_FRAMEV)) THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV
   (ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`;
            `lnabla 3 G (ltperm (swap(2,3)) (lnabla 2 G (lric2 (G:real^N->real^N^N))))`;
            `y:real^N`; `S:real^N^N`; `rfa_ft (S:real^N^N) [j; l]`] RFA_LTCONTR_FRAMEV)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `a = c /\ b = d ==> a = inv(&2) * b ==> c = inv(&2) * d`) THEN
  CONJ_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `s:num` THEN STRIP_TAC THEN
  BETA_TAC THENL
   [MP_TAC(ISPECL [`3`; `swap(2,3)`; `G:real^N->real^N^N`;
                   `lnabla 2 G (lric2 (G:real^N->real^N^N))`] RFA_LNABLA_LTPERM) THEN
    SIMP_TAC[RFA_HT_SWAP23_PERMUTES; ARITH] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[ltperm];
    ALL_TAC] THEN
  MATCH_MP_TAC RFA_N3_AGREE THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  (SUBGOAL_THEN `m = 1 \/ m = 2 \/ m = 3 \/ m = 4` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[rfa_ft; swap] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[EL_CONS; ARITH]);;

let RFA_SH_SIGMA_PERMUTES = RFA_PERMUTES_FAST
 `(\m. if m = 1 then 4 else if m = 2 then 5 else if m = 3 then 1 else if m = 4 then 3
       else if m = 5 then 2 else m) permutes 1..5`;;

let RFA_SH_F3_RICCI = prove
 (`!U (G:real^N->real^N^N) (pf:real^N->real).
     metric_field U G /\ smooth_map_on U (\z. lift(pf z))
     ==> rfa_eqon U
          (\y u. lnabla 2 G (lnabla 1 G (\z w. drop(frechet_derivative (\x. lift(pf x))
                                                    (at z) (w 1)))) y u -
                 ltperm (swap(2,3))
                   (lnabla 2 G (lnabla 1 G (\z w. drop(frechet_derivative (\x. lift(pf x))
                                                         (at z) (w 1))))) y u)
          (ltcontr G (ltperm (\m. if m = 1 then 4 else if m = 2 then 5 else if m = 3 then 1
                                  else if m = 4 then 3 else if m = 5 then 2 else m)
                       (ltprod 4 (lrm4 G)
                          (\z w. drop(frechet_derivative (\x. lift(pf x)) (at z) (w 1))))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `pf:real^N->real`] LRG_DF_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[rfa_eqon] THEN MAP_EVERY X_GEN_TAC [`y:real^N`; `u:num->real^N`] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`1`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `\z w. drop(frechet_derivative (\x. lift((pf:real^N->real) x)) (at z) (w 1))`;
                 `y:real^N`; `u:num->real^N`] RFA_RICCI_IDENTITY) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SUM_SING_NUMSEG; RFA_LNABLA_ITER_2] THEN CONV_TAC NUM_REDUCE_CONV THEN
  BETA_TAC THEN
  SUBGOAL_THEN
   `(\m. if m = 2 then (u:num->real^N) 3 else if m = 3 then u 2 else u m) =
    (\m. u(swap(2,3) m))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; swap] THEN X_GEN_TAC `x:num` THEN
    ASM_CASES_TAC `x = 2` THEN ASM_REWRITE_TAC[ARITH] THEN
    ASM_CASES_TAC `x = 3` THEN ASM_REWRITE_TAC[ARITH];
    ALL_TAC] THEN
  REWRITE_TAC[ltperm] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`1`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `\z w. drop(frechet_derivative (\x. lift((pf:real^N->real) x)) (at z) (w 1))`;
                 `y:real^N`; `1`; `u:num->real^N`;
                 `lriemann (G:real^N->real^N^N) y (u 2) (u 3) ((u:num->real^N) 1)`]
                RFA_METRIC_EXPAND) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN BETA_TAC THEN REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ltcontr; ltperm; ltprod; lrm4] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[REAL_MUL_ASSOC]);;

let RFA_SH_SOL_EQON = prove
 (`!U (G:real^N->real^N^N) (pf:real^N->real).
     metric_field U G /\
     (!y u. y IN U
            ==> lric2 G y u +
                lnabla 1 G (\z w. drop(frechet_derivative (\x. lift(pf x)) (at z) (w 1))) y u =
                inv(&2) * lmetric2 G y u)
     ==> rfa_eqon U (lnabla 1 G (\z w. drop(frechet_derivative (\x. lift(pf x)) (at z) (w 1))))
                    (\y u. inv(&2) * lmetric2 G y u - lric2 G y u)`,
  REWRITE_TAC[rfa_eqon] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^N`; `u:num->real^N`]) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let RFA_SH_SOL_D2 = prove
 (`!U (G:real^N->real^N^N) (pf:real^N->real).
     metric_field U G /\
     rfa_eqon U (lnabla 1 G (\z w. drop(frechet_derivative (\x. lift(pf x)) (at z) (w 1))))
                (\y u. inv(&2) * lmetric2 G y u - lric2 G y u)
     ==> rfa_eqon U
           (lnabla 2 G (lnabla 1 G (\z w. drop(frechet_derivative (\x. lift(pf x)) (at z) (w 1)))))
           (\y u. --(lnabla 2 G (lric2 G) y u)) /\
         rfa_eqon U
           (lnabla 3 G (lnabla 2 G (lnabla 1 G
              (\z w. drop(frechet_derivative (\x. lift(pf x)) (at z) (w 1))))))
           (\y u. --(lnabla 3 G (lnabla 2 G (lric2 G)) y u))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN
   `rfa_eqon U
     (lnabla 2 G (lnabla 1 G (\z w. drop(frechet_derivative (\x. lift((pf:real^N->real) x)) (at z) (w 1)))))
     (\y u. --(lnabla 2 G (lric2 (G:real^N->real^N^N)) y u))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_EQON_TRANS THEN
    EXISTS_TAC `lnabla 2 G (\y u. inv(&2) * lmetric2 G y u - lric2 (G:real^N->real^N^N) y u)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC RFA_EQON_LNABLA THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC RFA_EQON_TRANS THEN
    EXISTS_TAC `\y u. lnabla 2 G (\y u. inv(&2) * lmetric2 G y u) y u -
                      lnabla 2 G (lric2 (G:real^N->real^N^N)) y u` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`;
                     `\y u. inv(&2) * lmetric2 (G:real^N->real^N^N) y u`;
                     `lric2 (G:real^N->real^N^N)`] RFA_LNE_SUB) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[RFA_SF_LRIC2] THEN
        MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`;
                       `lmetric2 (G:real^N->real^N^N)`; `inv(&2)`] RFA_SF_CMUL) THEN
        ASM_SIMP_TAC[RFA_SF_LMETRIC2];
        BETA_TAC THEN REWRITE_TAC[ETA_AX]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`;
                   `lmetric2 (G:real^N->real^N^N)`; `inv(&2)`] RFA_LNE_CMUL) THEN
    ASM_SIMP_TAC[RFA_SF_LMETRIC2] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] RFA_LNE_METRIC) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[rfa_eqon] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC RFA_EQON_TRANS THEN
  EXISTS_TAC `lnabla 3 G (\y u. --(lnabla 2 G (lric2 (G:real^N->real^N^N)) y u))` THEN
  CONJ_TAC THENL [MATCH_MP_TAC RFA_EQON_LNABLA THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`3`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lnabla 2 G (lric2 (G:real^N->real^N^N))`; `--(&1)`] RFA_LNE_CMUL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`; `lric2 (G:real^N->real^N^N)`]
           RFA_SF_LNABLA) THEN ASM_SIMP_TAC[RFA_SF_LRIC2; ARITH];
    REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_LID; ETA_AX]]);;


(* ========================================================================= *)
(* The 1-form df as a named field (rfa_sh_df), frame values of               *)
(* the contracted Bianchi identity and of Hess f (RFA_SH_CB_FRAME,           *)
(* RFA_SH_F2_FRAME), the identity P = df(R(.,.).) as fields (RFA_SH_P_EQON). *)
(* ========================================================================= *)

let rfa_sh_df = new_definition
 `rfa_sh_df (pf:real^N->real) =
    \z (w:num->real^N). drop(frechet_derivative (\x. lift(pf x)) (at z) (w 1))`;;

let RFA_SH_DF_SF = prove
 (`!U (pf:real^N->real). open U /\ smooth_map_on U (\z. lift(pf z)) ==> rfa_sf 1 U (rfa_sh_df pf)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_sf; rfa_sh_df] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `pf:real^N->real`] LRG_DF_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[]);;

let RFA_SH_CB_FRAME = prove
 (`!U (G:real^N->real^N^N) y (S:real^N^N) j.
     metric_field U G /\ y IN U /\ matrix_inv(G y) = transp S ** S
     ==> sum(1..dimindex(:N)) (\i. lnabla 2 G (lric2 G) y (rfa_ft S [i; j; i])) =
         inv(&2) * sum(1..dimindex(:N)) (\i. lnabla 2 G (lric2 G) y (rfa_ft S [i; i; j]))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `S:real^N^N`; `j:num`]
                RFA_HT_BIANCHI_FRAME) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `S:real^N^N`; `j:num`]
                RFA_HT_DSC_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC RFA_FT_DRIC_SYM THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let RFA_SH_F2_FRAME = prove
 (`!U (G:real^N->real^N^N) y (S:real^N^N) (pf:real^N->real) r l.
     metric_field U G /\ y IN U /\ invertible S /\ matrix_inv(G y) = transp S ** S /\
     rfa_eqon U (lnabla 1 G (rfa_sh_df pf)) (\y u. inv(&2) * lmetric2 G y u - lric2 G y u) /\
     1 <= r /\ r <= dimindex(:N) /\ 1 <= l /\ l <= dimindex(:N)
     ==> lnabla 1 G (rfa_sh_df pf) y (rfa_ft S [r; l]) =
         inv(&2) * (if r = l then &1 else &0) - lric2 G y (rfa_ft S [r; l])`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`y:real^N`; `rfa_ft (S:real^N^N) [r; l]`] o
              REWRITE_RULE[rfa_eqon]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `S:real^N^N`;
                 `r:num`; `l:num`] RFA_FT_METRIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

let RFA_SH_P_EQON = prove
 (`!U (G:real^N->real^N^N) (pf:real^N->real).
     metric_field U G /\ smooth_map_on U (\z. lift(pf z)) /\
     rfa_eqon U (lnabla 1 G (rfa_sh_df pf)) (\y u. inv(&2) * lmetric2 G y u - lric2 G y u)
     ==> rfa_eqon U
           (\y u. ltperm (swap(2,3)) (lnabla 2 G (lric2 G)) y u - lnabla 2 G (lric2 G) y u)
           (ltcontr G (ltperm (\m. if m = 1 then 4 else if m = 2 then 5 else if m = 3 then 1
                                   else if m = 4 then 3 else if m = 5 then 2 else m)
                        (ltprod 4 (lrm4 G) (rfa_sh_df pf))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `pf:real^N->real`] RFA_SH_SOL_D2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM rfa_sh_df]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[GSYM rfa_sh_df] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `pf:real^N->real`] RFA_SH_F3_RICCI) THEN
  ASM_REWRITE_TAC[GSYM rfa_sh_df] THEN
  UNDISCH_TAC `rfa_eqon U (lnabla 2 G (lnabla 1 G (rfa_sh_df (pf:real^N->real))))
                 (\y u. --(lnabla 2 G (lric2 (G:real^N->real^N^N)) y u))` THEN
  REWRITE_TAC[rfa_eqon; ltperm] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM(MATCH_MP th (ASSUME `(y:real^N) IN U`))]) THEN
  ASM_SIMP_TAC[] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The soliton identity Lap_f Ric = Ric - 2 Rm(Ric) in frames                *)
(* (RFA_SH_LAPF_RIC), by linear certificates over frame atoms: for each      *)
(* component (a,b) the instances of the contracted Bianchi identity and its  *)
(* derivative, the symmetry and Ricci identity of nabla^2 Ric and the        *)
(* derivative of the df Ricci identity (evaluated at numeral frame tuples by *)
(* the frame engine of pc_rfa_h3d), with coefficients found by an external   *)
(* linear-algebra computation, then REAL_ARITH.  The context is assumed with *)
(* fixed variable names U G y S pf; the lemma states it explicitly.          *)
(* ========================================================================= *)

let rfa_sh_mf = ASSUME `metric_field U (G:real^3->real^3^3)`;;
let rfa_sh_yth = ASSUME `(y:real^3) IN U`;;
let rfa_sh_invS = ASSUME `invertible (S:real^3^3)`;;
let rfa_sh_sth = ASSUME `matrix_inv((G:real^3->real^3^3) y) = transp (S:real^3^3) ** S`;;
let rfa_sh_sm = ASSUME `smooth_map_on U (\z. lift((pf:real^3->real) z))`;;
let rfa_sh_sol = ASSUME `rfa_eqon U (lnabla 1 (G:real^3->real^3^3) (rfa_sh_df (pf:real^3->real)))
                       (\y u. inv(&2) * lmetric2 G y u - lric2 G y u)`;;
let rfa_sh_openU = CONJUNCT1(REWRITE_RULE[metric_field] rfa_sh_mf);;
let rfa_sh_sfd = MATCH_MP (ISPECL [`U:real^3->bool`; `pf:real^3->real`] RFA_SH_DF_SF) (CONJ rfa_sh_openU rfa_sh_sm);;
let rfa_sh_peq = MATCH_MP (ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `pf:real^3->real`] RFA_SH_P_EQON)
                (CONJ rfa_sh_mf (CONJ rfa_sh_sm rfa_sh_sol));;
let rfa_sh_dp = MATCH_MP (ISPECL [`3`; `U:real^3->bool`; `G:real^3->real^3^3`] RFA_EQON_LNABLA)
                (CONJ rfa_sh_openU rfa_sh_peq);;
let rfa_sh_hall = end_itlist CONJ [rfa_sh_mf; rfa_sh_yth; rfa_sh_invS; rfa_sh_sth];;
let rfa_sh_hook tm =
  match (try Some(dest_comb(rator tm), rand tm) with Failure _ -> None) with
    Some((f, yy), wt) when f = `lmetric2 (G:real^3->real^3^3)` && yy = `y:real^3` ->
      let [i; j] = dest_list (rand wt) in
      MP (REWRITE_RULE[DIMINDEX_3; ARITH]
            (ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`; i; j]
                    RFA_FT_METRIC)) rfa_sh_hall
  | _ -> failwith "atom";;
let rfa_sh_engine_setup () =
  RFA_ENGINE_RESET ();
  rfa_sf_bases := [rfa_sh_sfd; RFA_SF_LRIC2; RFA_SF_LMETRIC2; RFA_SF_LRM4];
  rfa_sf_unfolds := [];
  rfa_lnf_unfolds := [RFA_EQON_LRM4_3D];
  rfa_frv_unfolds := [RFA_EQON_LRM4_3D];
  rfa_mp_hook := (fun t -> try rfa_sh_hook t with Failure s -> failwith s
                                           | Match_failure _ -> failwith "atom");;
let rfa_sh_eval_app th_eq =
  (* th_eq : |- F y w = ...;  evaluate the lhs field application with the engine *)
  let t = lhs(concl th_eq) in
  let fld = rator(rator t) and w = rand t in
  let thl = RFA_LNF rfa_sh_mf fld in
  let th1 = MATCH_MP (ISPECL [`U:real^3->bool`; fld; rand(concl thl); `y:real^3`; w] RFA_EQON_APP)
                     (CONJ thl rfa_sh_yth) in
  let th2 = RFA_FRV_CONV rfa_sh_mf rfa_sh_yth rfa_sh_sth (rand(concl th1)) in
  TRANS th1 th2;;
let RFA_SH_DF3_INST (i,j,k,l) =
  let nm = mk_small_numeral in
  let w = mk_comb(`rfa_ft (S:real^3^3)`, mk_list(map nm [i;j;k;l], `:num`)) in
  let fl = lhand(concl rfa_sh_dp) and fr = rand(concl rfa_sh_dp) in
  let inst = MATCH_MP (ISPECL [`U:real^3->bool`; fl; fr; `y:real^3`; w] RFA_EQON_APP)
                      (CONJ rfa_sh_dp rfa_sh_yth) in
  let evl = rfa_sh_eval_app (REFL (lhs(concl inst))) and evr = rfa_sh_eval_app (REFL (rhs(concl inst))) in
  TRANS (TRANS (SYM evl) inst) evr;;

let rfa_sh_certs = [
  ((1, 1), [("cb", [2], Some 2); ("cb", [3], Some 3); ("df3", [1; 1; 2; 2], None); ("df3", [1; 1; 3; 3], None); ("ric2", [1; 2; 1; 2], None); ("sym", [1; 2; 2; 1], None); ("ric2", [1; 3; 1; 3], None); ("sym", [1; 3; 3; 1], None); ("df3", [2; 1; 2; 1], None); ("df3", [3; 1; 3; 1], None); ("dcb", [1; 1], None)]);
  ((1, 2), [("cb", [2], Some 1); ("ric2", [1; 1; 1; 2], None); ("sym", [1; 2; 2; 2], None); ("sym", [1; 2; 3; 3], None); ("df3", [2; 1; 3; 3], None); ("ric2", [2; 2; 1; 2], None); ("ric2", [2; 3; 1; 3], None); ("sym", [2; 3; 3; 1], None); ("df3", [3; 1; 3; 2], None); ("ric2", [3; 3; 1; 2], None); ("dcb", [1; 2], None); ("dcb", [2; 1], None)]);
  ((1, 3), [("cb", [3], Some 1); ("ric2", [1; 1; 1; 3], None); ("sym", [1; 3; 2; 2], None); ("sym", [1; 3; 3; 3], None); ("df3", [2; 1; 2; 3], None); ("ric2", [2; 2; 1; 3], None); ("sym", [2; 3; 1; 2], None); ("ric2", [2; 3; 1; 2], None); ("df3", [3; 1; 2; 2], None); ("ric2", [3; 3; 1; 3], None); ("dcb", [1; 3], None); ("dcb", [3; 1], None)]);
  ((2, 1), [("cb", [1], Some 2); ("ric2", [1; 1; 1; 2], None); ("sym", [1; 2; 1; 1], None); ("sym", [1; 2; 3; 3], None); ("df3", [1; 2; 3; 3], None); ("ric2", [1; 3; 2; 3], None); ("sym", [1; 3; 3; 2], None); ("ric2", [2; 2; 1; 2], None); ("df3", [3; 2; 3; 1], None); ("ric2", [3; 3; 1; 2], None); ("dcb", [1; 2], None); ("dcb", [2; 1], None)]);
  ((2, 2), [("cb", [1], Some 1); ("cb", [3], Some 3); ("df3", [1; 1; 2; 2], None); ("ric2", [1; 2; 1; 2], None); ("sym", [1; 2; 2; 1], None); ("df3", [2; 1; 2; 1], None); ("df3", [2; 2; 3; 3], None); ("ric2", [2; 3; 2; 3], None); ("sym", [2; 3; 3; 2], None); ("df3", [3; 2; 3; 2], None); ("dcb", [2; 2], None)]);
  ((2, 3), [("cb", [3], Some 2); ("ric2", [1; 1; 2; 3], None); ("df3", [1; 1; 2; 3], None); ("ric2", [1; 3; 1; 2], None); ("sym", [1; 3; 2; 1], None); ("ric2", [2; 2; 2; 3], None); ("sym", [2; 3; 1; 1], None); ("sym", [2; 3; 3; 3], None); ("df3", [3; 1; 2; 1], None); ("ric2", [3; 3; 2; 3], None); ("dcb", [2; 3], None); ("dcb", [3; 2], None)]);
  ((3, 1), [("cb", [1], Some 3); ("ric2", [1; 1; 1; 3], None); ("sym", [1; 2; 2; 3], None); ("ric2", [1; 2; 2; 3], None); ("df3", [1; 2; 3; 2], None); ("sym", [1; 3; 1; 1], None); ("sym", [1; 3; 2; 2], None); ("ric2", [2; 2; 1; 3], None); ("df3", [2; 2; 3; 1], None); ("ric2", [3; 3; 1; 3], None); ("dcb", [1; 3], None); ("dcb", [3; 1], None)]);
  ((3, 2), [("cb", [2], Some 3); ("ric2", [1; 1; 2; 3], None); ("df3", [1; 1; 3; 2], None); ("ric2", [1; 2; 1; 3], None); ("sym", [1; 2; 3; 1], None); ("df3", [2; 1; 3; 1], None); ("ric2", [2; 2; 2; 3], None); ("sym", [2; 3; 1; 1], None); ("sym", [2; 3; 2; 2], None); ("ric2", [3; 3; 2; 3], None); ("dcb", [2; 3], None); ("dcb", [3; 2], None)]);
  ((3, 3), [("cb", [1], Some 1); ("cb", [2], Some 2); ("df3", [1; 1; 3; 3], None); ("ric2", [1; 3; 1; 3], None); ("sym", [1; 3; 3; 1], None); ("df3", [2; 2; 3; 3], None); ("ric2", [2; 3; 2; 3], None); ("sym", [2; 3; 3; 2], None); ("df3", [3; 1; 3; 1], None); ("df3", [3; 2; 3; 2], None); ("dcb", [3; 3], None)])
];;

let rfa_sh_nm = mk_small_numeral;;
let rfa_sh_ft l = mk_comb(`rfa_ft (S:real^3^3)`, mk_list(map rfa_sh_nm l, `:num`));;
let rfa_sh_ctx3 = CONJ rfa_sh_mf (CONJ rfa_sh_yth rfa_sh_sth);;
let rfa_sh_ctx4 = CONJ rfa_sh_mf (CONJ rfa_sh_yth (CONJ rfa_sh_invS rfa_sh_sth));;
let rfa_sh_ric_sym =
  map (fun (i,j) -> MP (ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`;
                                 rfa_sh_nm i; rfa_sh_nm j] RFA_FT_RIC_SYM) (CONJ rfa_sh_mf rfa_sh_yth))
      [(2,1); (3,1); (3,2)];;
let rfa_sh_metric_vals =
  map (fun (i,j) -> MP (REWRITE_RULE[DIMINDEX_3; ARITH]
                         (ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`;
                                  rfa_sh_nm i; rfa_sh_nm j] RFA_FT_METRIC)) rfa_sh_hall)
      (allpairs (fun i j -> (i,j)) [1;2;3] [1;2;3]);;
let rfa_sh_f2_vals =
  map (fun (r,l) -> MP (REWRITE_RULE[DIMINDEX_3; ARITH]
                         (ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`;
                                  `pf:real^3->real`; rfa_sh_nm r; rfa_sh_nm l] RFA_SH_F2_FRAME))
                      (end_itlist CONJ [rfa_sh_mf; rfa_sh_yth; rfa_sh_invS; rfa_sh_sth; rfa_sh_sol]))
      (allpairs (fun i j -> (i,j)) [1;2;3] [1;2;3]);;
let rfa_sh_lrm4_vals =
  map (fun [a;b;c;d] -> MP (REWRITE_RULE[ARITH]
                         (ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`;
                                  rfa_sh_nm a; rfa_sh_nm b; rfa_sh_nm c; rfa_sh_nm d] RFA_LRM4_ARR)) rfa_sh_ctx4)
      (let r = [1;2;3] in itlist (fun a acc -> itlist (fun b acc -> itlist (fun c acc ->
          itlist (fun d acc -> [a;b;c;d]::acc) r acc) r acc) r acc) r []);;
let RFA_SH_EXPAND_CONV =
  REWRITE_CONV([DIMINDEX_3; SUM_3] @ rfa_sh_lrm4_vals @ rfa_sh_metric_vals @ rfa_sh_f2_vals) THENC
  REWRITE_CONV[rfa_arr_r; rfa_kd; rfa_ric_a; SUM_3] THENC DEPTH_CONV BETA_CONV THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV rfa_sh_ric_sym;;
let rfa_sh_expand th = CONV_RULE RFA_SH_EXPAND_CONV th;;
let rfa_sh_f1 r = mk_comb(mk_comb(`rfa_sh_df (pf:real^3->real)`, `y:real^3`), rfa_sh_ft [r]);;
let rfa_sh_inst (kind, idx, f1) =
  let th =
    match kind, idx with
      "cb", [j] -> MP (ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`;
                                rfa_sh_nm j] RFA_SH_CB_FRAME) rfa_sh_ctx3
    | "sym", [i;j;k;l] -> MP (ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`;
                                      `S:real^3^3`; rfa_sh_nm i; rfa_sh_nm j; rfa_sh_nm k; rfa_sh_nm l]
                                     RFA_FT_DDRIC_SYM) (CONJ rfa_sh_mf rfa_sh_yth)
    | "ric2", [i;j;k;l] -> MP (ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`;
                                       `S:real^3^3`; rfa_sh_nm i; rfa_sh_nm j; rfa_sh_nm k; rfa_sh_nm l]
                                      RFA_FT_RICCI_ID) rfa_sh_ctx4
    | "dcb", [j;l] -> MP (ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`;
                                   `S:real^3^3`; rfa_sh_nm j; rfa_sh_nm l] RFA_SH_DCB_FRAME) rfa_sh_ctx3
    | "df3", [i;j;k;l] -> RFA_SH_DF3_INST (i,j,k,l)
    | _ -> failwith "rfa_sh_inst" in
  let th' = match f1 with None -> th | Some r -> AP_TERM (mk_comb(`( * ):real->real->real`, rfa_sh_f1 r)) th in
  rfa_sh_expand th';;

let RFA_SH_COMP_TAC (asl, w) =
  let l = rand(rand(lhand(rand w))) in
  let [a; b] = map dest_small_numeral (dest_list l) in
  let saved = RFA_ENGINE_SAVE () in
  rfa_sh_engine_setup ();
  let insts = try map rfa_sh_inst (assoc (a,b) rfa_sh_certs)
              with e -> (RFA_ENGINE_RESTORE saved; raise e) in
  RFA_ENGINE_RESTORE saved;
  (CONV_TAC RFA_SH_EXPAND_CONV THEN MAP_EVERY MP_TAC insts THEN REAL_ARITH_TAC) (asl, w);;

let RFA_SH_LAPF_RIC = prove
 (`!U (G:real^3->real^3^3) y (S:real^3^3) (pf:real^3->real) a b.
         metric_field U G /\ y IN U /\ invertible S /\
         matrix_inv(G y) = transp S ** S /\ smooth_map_on U (\z. lift(pf z)) /\
         rfa_eqon U (lnabla 1 G (rfa_sh_df pf)) (\y u. inv(&2) * lmetric2 G y u - lric2 G y u) /\
         1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3
         ==> sum(1..3) (\c. lnabla 3 G (lnabla 2 G (lric2 G)) y (rfa_ft S [a; b; c; c])) -
             sum(1..3) (\c. rfa_sh_df pf y (rfa_ft S [c]) *
                            lnabla 2 G (lric2 G) y (rfa_ft S [a; b; c])) =
             lric2 G y (rfa_ft S [a; b]) -
             &2 * sum(1..3) (\c. sum(1..3) (\d. rfa_arr_r (rfa_ric_a G y S) a c d b *
                                                lric2 G y (rfa_ft S [c; d])))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN RFA_INDEX_CASES_TAC [`a:num`; `b:num`] THEN RFA_SH_COMP_TAC);;

(* ========================================================================= *)
(* The pointwise algebra of the pinching argument.  Schur's                  *)
(* inequality for t = 2 with its equality case (RFA_SH_SCHUR), the gradient  *)
(* Cauchy-Schwarz step at a critical point of |Ric|^2 / R^2                  *)
(* (RFA_SH_GRAD_CS), the core estimate (RFA_SH_PINCH_CORE: the Laplacian of  *)
(* R^2 |Ric|^2 - |Ric|^2(x0) R^2 at x0 is 4 R (|Ric|^4 - R <Ric,Rm(Ric)>) /  *)
(* R + nonnegative terms), the 3-d curvature contraction in a Ricci          *)
(* eigenframe (RFA_SH_ARR_P_DIAG), and the assembled frame-array form        *)
(* (RFA_SH_PINCH_SUMS): a local maximum point of |Ric|^2 / R^2 with Ric > 0  *)
(* is Einstein, 3 |Ric|^2 = R^2.                                             *)
(* ========================================================================= *)

let RFA_SH_SCHUR_ORD = prove
 (`!a b c. &0 < c /\ c <= b /\ b <= a
           ==> &0 <= a pow 2 * (a - b) * (a - c) + b pow 2 * (b - a) * (b - c) +
                     c pow 2 * (c - a) * (c - b) /\
               (a pow 2 * (a - b) * (a - c) + b pow 2 * (b - a) * (b - c) +
                c pow 2 * (c - a) * (c - b) = &0 ==> a = b /\ b = c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (a - b) * (a pow 2 * (a - c) - b pow 2 * (b - c))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_LE] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_POW_LE) THEN TRY(MATCH_MP_TAC REAL_POW_LE2) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c pow 2 * (c - a) * (c - b)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `(c - a) * (c - b) = (a - c) * (b - c)`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `a pow 2 * (a - b) * (a - c) + b pow 2 * (b - a) * (b - c) +
                c pow 2 * (c - a) * (c - b) =
                (a - b) * (a pow 2 * (a - c) - b pow 2 * (b - c)) +
                c pow 2 * (c - a) * (c - b)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(a - b) * (a pow 2 * (a - c) - b pow 2 * (b - c)) = &0 /\
                c pow 2 * (c - a) * (c - b) = &0` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c pow 2 /\ &0 < a pow 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(c:real) = a \/ c = b` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `c pow 2 * (c - a) * (c - b) = &0` THEN REWRITE_TAC[REAL_ENTIRE] THEN
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `(a - b) * (a pow 2 * (a - c) - b pow 2 * (b - c)) = &0` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `(a - b) * (a pow 2 * (a - b) - b pow 2 * (b - b)) =
                          a pow 2 * (a - b) pow 2`] THEN
  REWRITE_TAC[REAL_ENTIRE; REAL_POW_EQ_0; ARITH_EQ] THEN ASM_REAL_ARITH_TAC);;

let RFA_SH_SCHUR = prove
 (`!a b c. &0 < a /\ &0 < b /\ &0 < c
           ==> &0 <= a pow 2 * (a - b) * (a - c) + b pow 2 * (b - a) * (b - c) +
                     c pow 2 * (c - a) * (c - b) /\
               (a pow 2 * (a - b) * (a - c) + b pow 2 * (b - a) * (b - c) +
                c pow 2 * (c - a) * (c - b) = &0 ==> a = b /\ b = c)`,
  let branch (x,y,z) =
    MP_TAC(SPECL [x; y; z] RFA_SH_SCHUR_ORD) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]] in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISJ_CASES_TAC(REAL_ARITH `(c <= b /\ b <= a) \/ (b <= c /\ c <= a) \/ (c <= a /\ a <= b) \/
                             (a <= c /\ c <= b) \/ (b <= a /\ a <= c) \/ (a <= b /\ b <= c)`) THENL
   [branch (`a:real`,`b:real`,`c:real`); ALL_TAC] THEN
  FIRST_X_ASSUM DISJ_CASES_TAC THENL [branch (`a:real`,`c:real`,`b:real`); ALL_TAC] THEN
  FIRST_X_ASSUM DISJ_CASES_TAC THENL [branch (`b:real`,`a:real`,`c:real`); ALL_TAC] THEN
  FIRST_X_ASSUM DISJ_CASES_TAC THENL [branch (`b:real`,`c:real`,`a:real`); ALL_TAC] THEN
  FIRST_X_ASSUM DISJ_CASES_TAC THENL
   [branch (`c:real`,`a:real`,`b:real`); branch (`c:real`,`b:real`,`a:real`)]);;

let RFA_SH_LAGRANGE3 = prove
 (`!l1 l2 l3 x1 x2 x3.
     (l1 * x1 + l2 * x2 + l3 * x3) pow 2 <=
     (l1 pow 2 + l2 pow 2 + l3 pow 2) * (x1 pow 2 + x2 pow 2 + x3 pow 2)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPEC `l1 * x2 - l2 * x1` REAL_LE_POW_2) THEN
  MP_TAC(SPEC `l1 * x3 - l3 * x1` REAL_LE_POW_2) THEN
  MP_TAC(SPEC `l2 * x3 - l3 * x2` REAL_LE_POW_2) THEN
  REAL_ARITH_TAC);;

let RFA_SH_GRAD_CS = prove
 (`!l1 l2 l3 x1 x2 x3 R Q.
     &0 < Q /\ R * (l1 * x1 + l2 * x2 + l3 * x3) = Q * (x1 + x2 + x3) /\
     Q = l1 pow 2 + l2 pow 2 + l3 pow 2
     ==> Q * (x1 + x2 + x3) pow 2 <= R pow 2 * (x1 pow 2 + x2 pow 2 + x3 pow 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`l1:real`; `l2:real`; `l3:real`; `x1:real`; `x2:real`; `x3:real`]
               RFA_SH_LAGRANGE3) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> lhs(concl th) = `Q:real`)) THEN
  DISCH_TAC THEN
  ABBREV_TAC `S = l1 * x1 + l2 * x2 + l3 * x3` THEN
  ABBREV_TAC `D = x1 + x2 + x3` THEN
  ABBREV_TAC `X = x1 pow 2 + x2 pow 2 + x3 pow 2` THEN
  SUBGOAL_THEN `R pow 2 * S pow 2 <= R pow 2 * (Q * X)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN `Q * (Q * D pow 2) = R pow 2 * S pow 2` ASSUME_TAC THENL
   [UNDISCH_TAC `R * S = Q * D` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `Q * (Q * D pow 2) <= Q * (R pow 2 * X)` MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `R pow 2 * S pow 2 <= R pow 2 * (Q * X)` THEN
    REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ]]);;

let RFA_SH_PINCH_CORE = prove
 (`!R Q P A B N G Dr1 Dr2.
     &0 < R /\ &0 < Q /\
     A = Dr1 + Q - &2 * P /\ B = Dr2 + R - &2 * Q /\
     R * Dr1 = Q * Dr2 /\ Q * G <= R pow 2 * N /\
     R pow 2 * (&2 * A + &2 * N) - Q * (&2 * R * B + &2 * G) <= &0
     ==> Q pow 2 - R * P <= &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `R pow 2 * (&2 * (Dr1 + Q - &2 * P) + &2 * N) -
                Q * (&2 * R * (Dr2 + R - &2 * Q) + &2 * G) =
                &2 * R * (R * Dr1 - Q * Dr2) + &4 * R * (Q pow 2 - R * P) +
                &2 * (R pow 2 * N - Q * G)` MP_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> try lhs(concl th) = `A:real` with Failure _ -> false)) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> try lhs(concl th) = `B:real` with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_ADD_LID] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`Q pow 2 - R * P`; `&0`; `&4 * R`] REAL_LE_LMUL_EQ) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[REAL_MUL_RZERO] THEN ASM_REAL_ARITH_TAC);;

let RFA_SH_ARR_P_DIAG = prove
 (`!r:num->num->real.
     (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3 /\ ~(i = j) ==> r i j = &0)
     ==> sum(1..3) (\c. sum(1..3) (\d. rfa_arr_r r 1 c d 1 * r c d)) =
         (r 1 1 + r 2 2 - r 3 3) / &2 * r 2 2 + (r 1 1 + r 3 3 - r 2 2) / &2 * r 3 3 /\
         sum(1..3) (\c. sum(1..3) (\d. rfa_arr_r r 2 c d 2 * r c d)) =
         (r 2 2 + r 1 1 - r 3 3) / &2 * r 1 1 + (r 2 2 + r 3 3 - r 1 1) / &2 * r 3 3 /\
         sum(1..3) (\c. sum(1..3) (\d. rfa_arr_r r 3 c d 3 * r c d)) =
         (r 3 3 + r 1 1 - r 2 2) / &2 * r 1 1 + (r 3 3 + r 2 2 - r 1 1) / &2 * r 2 2`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(r:num->num->real) 1 2 = &0 /\ r 1 3 = &0 /\ r 2 1 = &0 /\ r 2 3 = &0 /\
                r 3 1 = &0 /\ r 3 2 = &0` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUM_3; rfa_arr_r; rfa_kd; ARITH_EQ] THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let RFA_SH_PINCH_ALG = prove
 (`!l1 l2 l3 L1 L2 L3 D1 D2 D3 A B N Gr Dr1 Dr2.
     &0 < l1 /\ &0 < l2 /\ &0 < l3 /\
     L1 - D1 = l1 - &2 * ((l1 + l2 - l3) / &2 * l2 + (l1 + l3 - l2) / &2 * l3) /\
     L2 - D2 = l2 - &2 * ((l2 + l1 - l3) / &2 * l1 + (l2 + l3 - l1) / &2 * l3) /\
     L3 - D3 = l3 - &2 * ((l3 + l1 - l2) / &2 * l1 + (l3 + l2 - l1) / &2 * l2) /\
     A = l1 * L1 + l2 * L2 + l3 * L3 /\ B = L1 + L2 + L3 /\
     Dr1 = l1 * D1 + l2 * D2 + l3 * D3 /\ Dr2 = D1 + D2 + D3 /\
     (l1 + l2 + l3) * Dr1 = (l1 pow 2 + l2 pow 2 + l3 pow 2) * Dr2 /\
     (l1 pow 2 + l2 pow 2 + l3 pow 2) * Gr <= (l1 + l2 + l3) pow 2 * N /\
     (l1 + l2 + l3) pow 2 * (&2 * A + &2 * N) -
     (l1 pow 2 + l2 pow 2 + l3 pow 2) * (&2 * (l1 + l2 + l3) * B + &2 * Gr) <= &0
     ==> l1 = l2 /\ l2 = l3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Pp = l1 * ((l1 + l2 - l3) / &2 * l2 + (l1 + l3 - l2) / &2 * l3) +
                   l2 * ((l2 + l1 - l3) / &2 * l1 + (l2 + l3 - l1) / &2 * l3) +
                   l3 * ((l3 + l1 - l2) / &2 * l1 + (l3 + l2 - l1) / &2 * l2)` THEN
  SUBGOAL_THEN `&0 < l1 pow 2 + l2 pow 2 + l3 pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < a /\ &0 < b /\ &0 < c ==> &0 < a + b + c`) THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `L1 = D1 + l1 - &2 * ((l1 + l2 - l3) / &2 * l2 + (l1 + l3 - l2) / &2 * l3) /\
                L2 = D2 + l2 - &2 * ((l2 + l1 - l3) / &2 * l1 + (l2 + l3 - l1) / &2 * l3) /\
                L3 = D3 + l3 - &2 * ((l3 + l1 - l2) / &2 * l1 + (l3 + l2 - l1) / &2 * l2)`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`l1 + l2 + l3`; `l1 pow 2 + l2 pow 2 + l3 pow 2`; `Pp:real`; `A:real`; `B:real`;
                `N:real`; `Gr:real`; `Dr1:real`; `Dr2:real`] RFA_SH_PINCH_CORE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `A = l1 * L1 + l2 * L2 + l3 * L3` THEN
      UNDISCH_TAC `Dr1 = l1 * D1 + l2 * D2 + l3 * D3` THEN
      ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "Pp" THEN REAL_ARITH_TAC;
      UNDISCH_TAC `B = L1 + L2 + L3` THEN UNDISCH_TAC `Dr2 = D1 + D2 + D3` THEN
      ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(l1 pow 2 + l2 pow 2 + l3 pow 2) pow 2 - (l1 + l2 + l3) * Pp =
                l1 pow 2 * (l1 - l2) * (l1 - l3) + l2 pow 2 * (l2 - l1) * (l2 - l3) +
                l3 pow 2 * (l3 - l1) * (l3 - l2)` SUBST1_TAC THENL
   [EXPAND_TAC "Pp" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`l1:real`; `l2:real`; `l3:real`] RFA_SH_SCHUR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REAL_ARITH_TAC);;

let RFA_SH_DIV_2R = prove
 (`!R Q t s. &0 < R /\ R pow 2 * (&2 * t) + --Q * (&2 * R * s) = &0 ==> R * t = Q * s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(&2 * R) * (R * t - Q * s) = &0` MP_TAC THENL
   [UNDISCH_TAC `R pow 2 * (&2 * t) + --Q * (&2 * R * s) = &0` THEN REAL_ARITH_TAC;
    REWRITE_TAC[REAL_ENTIRE] THEN ASM_REAL_ARITH_TAC]);;

let rfa_sh_xoff =
  let nm = mk_small_numeral and xv = `X:num->num->num->real` in
  List.concat (map (fun a -> List.concat (map (fun b ->
    if a = b then [] else map (fun c -> list_mk_comb(xv,[nm a; nm b; nm c])) [1;2;3])
    [1;2;3])) [1;2;3]);;

let RFA_SH_PINCH_SUMS = prove
 (`!(r:num->num->real) (X:num->num->num->real) (Y:num->num->num->num->real)
    (df:num->real) A B N Gr Q0 R0 (dQ:num->real) (dR:num->real).
     (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3 /\ ~(i = j) ==> r i j = &0) /\
     &0 < r 1 1 /\ &0 < r 2 2 /\ &0 < r 3 3 /\
     (!a. 1 <= a /\ a <= 3
          ==> sum(1..3) (\c. Y a a c c) - sum(1..3) (\c. df c * X a a c) =
              r a a - &2 * sum(1..3) (\c. sum(1..3) (\d. rfa_arr_r r a c d a * r c d))) /\
     Q0 = sum(1..3) (\a. sum(1..3) (\b. r a b pow 2)) /\
     R0 = sum(1..3) (\a. r a a) /\
     A = sum(1..3) (\a. sum(1..3) (\b. r a b * sum(1..3) (\c. Y a b c c))) /\
     B = sum(1..3) (\a. sum(1..3) (\c. Y a a c c)) /\
     N = sum(1..3) (\a. sum(1..3) (\b. sum(1..3) (\c. X a b c pow 2))) /\
     Gr = sum(1..3) (\c. dR c pow 2) /\
     (!c. 1 <= c /\ c <= 3 ==> dR c = sum(1..3) (\a. X a a c)) /\
     (!c. 1 <= c /\ c <= 3
          ==> dQ c = &2 * sum(1..3) (\a. sum(1..3) (\b. r a b * X a b c))) /\
     (!c. 1 <= c /\ c <= 3 ==> R0 pow 2 * dQ c + --Q0 * (&2 * R0 * dR c) = &0) /\
     R0 pow 2 * (&2 * A + &2 * N) + --Q0 * (&2 * R0 * B + &2 * Gr) <= &0
     ==> &3 * Q0 = R0 pow 2`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "offd p1 p2 p3 lapf q0 r0 hA hB hN hGr hdR hdQ grad lap" THEN
  USE_THEN "offd" (fun th -> LABEL_TAC "pdiag" (MATCH_MP RFA_SH_ARR_P_DIAG th)) THEN
  SUBGOAL_THEN `(r:num->num->real) 1 2 = &0 /\ r 1 3 = &0 /\ r 2 1 = &0 /\ r 2 3 = &0 /\
                r 3 1 = &0 /\ r 3 2 = &0` (LABEL_TAC "zs") THENL
   [REPEAT CONJ_TAC THEN USE_THEN "offd" MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  REMOVE_THEN "offd" (K ALL_TAC) THEN
  USE_THEN "lapf" (fun th -> MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th) THEN
                             MP_TAC(SPEC `3` th)) THEN
  REWRITE_TAC[ARITH] THEN USE_THEN "pdiag" (fun pd -> REWRITE_TAC[pd]) THEN
  REWRITE_TAC[SUM_3] THEN
  DISCH_THEN(LABEL_TAC "L3") THEN DISCH_THEN(LABEL_TAC "L2") THEN
  DISCH_THEN(LABEL_TAC "L1") THEN
  REMOVE_THEN "lapf" (K ALL_TAC) THEN REMOVE_THEN "pdiag" (K ALL_TAC) THEN
  USE_THEN "zs" (fun zs ->
    let simp = REWRITE_RULE[SUM_3; zs; REAL_ARITH `&0 pow 2 = &0`; REAL_MUL_LZERO;
                            REAL_ADD_LID; REAL_ADD_RID] in
    MAP_EVERY (fun l -> REMOVE_THEN l (SUBST_ALL_TAC o simp))
      ["q0"; "r0"; "hA"; "hB"; "hGr"] THEN
    MAP_EVERY (fun l -> USE_THEN l (fun th ->
       MAP_EVERY (fun n -> LABEL_TAC (l ^ string_of_int n)
                    (simp (REWRITE_RULE[ARITH] (SPEC (mk_small_numeral n) th)))) [1;2;3]))
      ["hdR"; "hdQ"]) THEN
  SUBGOAL_THEN `&0 < (r:num->num->real) 1 1 + r 2 2 + r 3 3 /\
                &0 < (r:num->num->real) 1 1 pow 2 + r 2 2 pow 2 + r 3 3 pow 2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN REWRITE_TAC[REAL_POW_2] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < a /\ &0 < b /\ &0 < c ==> &0 < a + b + c`) THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY (fun n ->
    let c = mk_small_numeral n and sn = string_of_int n in
    SUBGOAL_THEN (subst [c, `c:num`]
      `((r:num->num->real) 1 1 + r 2 2 + r 3 3) *
       (r 1 1 * (X:num->num->num->real) 1 1 c + r 2 2 * X 2 2 c + r 3 3 * X 3 3 c) =
       (r 1 1 pow 2 + r 2 2 pow 2 + r 3 3 pow 2) * (X 1 1 c + X 2 2 c + X 3 3 c)`)
    (LABEL_TAC ("t" ^ sn)) THENL
     [MATCH_MP_TAC RFA_SH_DIV_2R THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "grad" (MP_TAC o SPEC c) THEN REWRITE_TAC[ARITH] THEN
      USE_THEN ("hdQ" ^ sn) SUBST1_TAC THEN USE_THEN ("hdR" ^ sn) SUBST1_TAC THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`(r:num->num->real) 1 1`; `(r:num->num->real) 2 2`; `(r:num->num->real) 3 3`;
                  subst [c, `c:num`] `(X:num->num->num->real) 1 1 c`;
                  subst [c, `c:num`] `(X:num->num->num->real) 2 2 c`;
                  subst [c, `c:num`] `(X:num->num->num->real) 3 3 c`;
                  `(r:num->num->real) 1 1 + r 2 2 + r 3 3`;
                  `(r:num->num->real) 1 1 pow 2 + r 2 2 pow 2 + r 3 3 pow 2`] RFA_SH_GRAD_CS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN ("t" ^ sn) ACCEPT_TAC;
      DISCH_THEN(LABEL_TAC ("cs" ^ sn))]) [1;2;3] THEN
  SUBGOAL_THEN
   `((X:num->num->num->real) 1 1 1 pow 2 + X 2 2 1 pow 2 + X 3 3 1 pow 2) +
    (X 1 1 2 pow 2 + X 2 2 2 pow 2 + X 3 3 2 pow 2) +
    (X 1 1 3 pow 2 + X 2 2 3 pow 2 + X 3 3 3 pow 2) <= N`
  ASSUME_TAC THENL
   [REMOVE_THEN "hN" SUBST1_TAC THEN REWRITE_TAC[SUM_3] THEN
    MAP_EVERY (fun t -> MP_TAC(SPEC t REAL_LE_POW_2)) rfa_sh_xoff THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((r:num->num->real) 1 1 + r 2 2 + r 3 3) pow 2 *
    (((X:num->num->num->real) 1 1 1 pow 2 + X 2 2 1 pow 2 + X 3 3 1 pow 2) +
     (X 1 1 2 pow 2 + X 2 2 2 pow 2 + X 3 3 2 pow 2) +
     (X 1 1 3 pow 2 + X 2 2 3 pow 2 + X 3 3 3 pow 2)) <=
    (r 1 1 + r 2 2 + r 3 3) pow 2 * N`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  MP_TAC(SPECL
   [`(r:num->num->real) 1 1`; `(r:num->num->real) 2 2`; `(r:num->num->real) 3 3`;
    `(Y:num->num->num->num->real) 1 1 1 1 + Y 1 1 2 2 + Y 1 1 3 3`;
    `(Y:num->num->num->num->real) 2 2 1 1 + Y 2 2 2 2 + Y 2 2 3 3`;
    `(Y:num->num->num->num->real) 3 3 1 1 + Y 3 3 2 2 + Y 3 3 3 3`;
    `(df:num->real) 1 * (X:num->num->num->real) 1 1 1 + df 2 * X 1 1 2 + df 3 * X 1 1 3`;
    `(df:num->real) 1 * (X:num->num->num->real) 2 2 1 + df 2 * X 2 2 2 + df 3 * X 2 2 3`;
    `(df:num->real) 1 * (X:num->num->num->real) 3 3 1 + df 2 * X 3 3 2 + df 3 * X 3 3 3`;
    `(r:num->num->real) 1 1 * ((Y:num->num->num->num->real) 1 1 1 1 + Y 1 1 2 2 + Y 1 1 3 3) +
     r 2 2 * (Y 2 2 1 1 + Y 2 2 2 2 + Y 2 2 3 3) + r 3 3 * (Y 3 3 1 1 + Y 3 3 2 2 + Y 3 3 3 3)`;
    `((Y:num->num->num->num->real) 1 1 1 1 + Y 1 1 2 2 + Y 1 1 3 3) +
     (Y 2 2 1 1 + Y 2 2 2 2 + Y 2 2 3 3) + (Y 3 3 1 1 + Y 3 3 2 2 + Y 3 3 3 3)`;
    `N:real`;
    `(dR:num->real) 1 pow 2 + dR 2 pow 2 + dR 3 pow 2`;
    `(r:num->num->real) 1 1 * ((df:num->real) 1 * (X:num->num->num->real) 1 1 1 +
                               df 2 * X 1 1 2 + df 3 * X 1 1 3) +
     r 2 2 * (df 1 * X 2 2 1 + df 2 * X 2 2 2 + df 3 * X 2 2 3) +
     r 3 3 * (df 1 * X 3 3 1 + df 2 * X 3 3 2 + df 3 * X 3 3 3)`;
    `((df:num->real) 1 * (X:num->num->num->real) 1 1 1 + df 2 * X 1 1 2 + df 3 * X 1 1 3) +
     (df 1 * X 2 2 1 + df 2 * X 2 2 2 + df 3 * X 2 2 3) +
     (df 1 * X 3 3 1 + df 2 * X 3 3 2 + df 3 * X 3 3 3)`]
   RFA_SH_PINCH_ALG) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      USE_THEN "L1" ACCEPT_TAC; USE_THEN "L2" ACCEPT_TAC; USE_THEN "L3" ACCEPT_TAC;
      REWRITE_TAC[]; REWRITE_TAC[]; REWRITE_TAC[]; REWRITE_TAC[];
      MAP_EVERY (fun n -> USE_THEN ("t" ^ string_of_int n)
                   (MP_TAC o AP_TERM (mk_comb(`( * ):real->real->real`,
                                              mk_comb(`df:num->real`, mk_small_numeral n)))))
                [1;2;3] THEN
      REAL_ARITH_TAC;
      USE_THEN "hdR1" SUBST1_TAC THEN USE_THEN "hdR2" SUBST1_TAC THEN
      USE_THEN "hdR3" SUBST1_TAC THEN
      MAP_EVERY (fun l -> USE_THEN l MP_TAC) ["cs1"; "cs2"; "cs3"] THEN
      UNDISCH_TAC
       `((r:num->num->real) 1 1 + r 2 2 + r 3 3) pow 2 *
        (((X:num->num->num->real) 1 1 1 pow 2 + X 2 2 1 pow 2 + X 3 3 1 pow 2) +
         (X 1 1 2 pow 2 + X 2 2 2 pow 2 + X 3 3 2 pow 2) +
         (X 1 1 3 pow 2 + X 2 2 3 pow 2 + X 3 3 3 pow 2)) <=
        (r 1 1 + r 2 2 + r 3 3) pow 2 * N` THEN
      REAL_ARITH_TAC;
      USE_THEN "lap" MP_TAC THEN REAL_ARITH_TAC];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Frame expansions of the chart tensors at a point (inner                   *)
(* products, norms, Laplacian, gradients of |Ric|^2 and R), the critical     *)
(* point of Psi = a |Ric|^2 + b R^2 (RFA_SH_PSI_CRIT: Laplacian <= 0 and     *)
(* gradient zero), Ricci positivity in an eigenframe from sec > 0            *)
(* (RFA_SH_RIC_POS), and the chart form of the pinching step                *)
(* (RFA_SH_PINCH_CHART): for a soliton chart field (Hess f = g/2 - Ric) with *)
(* sec > 0 at y and R(y)^2 |Ric|^2 <= |Ric|^2(y) R^2 on U, 3 |Ric|^2(y) =    *)
(* R(y)^2.                                                                    *)
(* ========================================================================= *)

let RFA_SH_FT2_EVAL = prove
 (`!(S:real^N^N) a b m.
     1 <= m /\ m <= 2
     ==> rfa_ft S [a; b] m = (if m = 1 then transp S ** basis a else transp S ** basis b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `m = 1 \/ m = 2` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[rfa_ft] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[EL_CONS; ARITH]);;

let RFA_SH_LTINNER2_FT = prove
 (`!U (G:real^N->real^N^N) (f:real^N->(num->real^N)->real) g y (S:real^N^N).
     ltensor_field 2 U f /\ ltensor_field 2 U g /\ y IN U /\
     matrix_inv(G y) = transp S ** S
     ==> ltinner 2 G f g y =
         sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
           f y (rfa_ft S [a; b]) * g y (rfa_ft S [a; b])))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `f:real^N->(num->real^N)->real`; `g:real^N->(num->real^N)->real`;
                 `y:real^N`; `S:real^N^N`] RFA_LTINNER_SQUARES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[LRG_SUM_INDEX_TUPLES_2] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  BINOP_TAC THEN
  (MATCH_MP_TAC RFA_TF_AGREE THEN
   MAP_EVERY EXISTS_TAC [`2`; `U:real^N->bool`] THEN
   ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
   ASM_SIMP_TAC[RFA_SH_FT2_EVAL] THEN
   SUBGOAL_THEN `m = 1 \/ m = 2` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV));;

let RFA_SH_LTNORM2_3_FT = prove
 (`!U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y (S:real^N^N).
     ltensor_field 3 U tf /\ y IN U /\ matrix_inv(G y) = transp S ** S
     ==> ltnorm2 3 G tf y =
         sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b. sum(1..dimindex(:N)) (\c.
           tf y (rfa_ft S [a; b; c]) pow 2)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`3`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`; `y:real^N`; `S:real^N^N`]
         LRG_LTNORM2_SQUARES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ARITH_RULE `3 = 2 + 1`; LRG_SUM_INDEX_TUPLES_SUC] THEN
  REWRITE_TAC[LRG_SUM_INDEX_TUPLES_2] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN BETA_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC RFA_TF_AGREE THEN
  MAP_EVERY EXISTS_TAC [`3`; `U:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[RFA_HT_FT3_EVAL] THEN
  SUBGOAL_THEN `m = 1 \/ m = 2 \/ m = 3` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let RFA_SH_LTLAP2_FT = prove
 (`!U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y (S:real^N^N) a b.
     metric_field U G /\ rfa_sf 2 U tf /\ y IN U /\ matrix_inv(G y) = transp S ** S
     ==> ltlap 2 G tf y (rfa_ft S [a; b]) =
         sum(1..dimindex(:N)) (\c. lnabla 3 G (lnabla 2 G tf) y (rfa_ft S [a; b; c; c]))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ltensor_field 4 U (lnabla 3 G (lnabla 2 G (tf:real^N->(num->real^N)->real)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`3`; `U:real^N->bool`; `G:real^N->real^N^N`;
                   `lnabla 2 G (tf:real^N->(num->real^N)->real)`] RFA_SF_LNABLA) THEN
    MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`;
                   `tf:real^N->(num->real^N)->real`] RFA_SF_LNABLA) THEN
    ASM_SIMP_TAC[ARITH; rfa_sf];
    ALL_TAC] THEN
  REWRITE_TAC[ltlap; RFA_LNABLA_ITER_2] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ABBREV_TAC `T4 = lnabla 3 G (lnabla 2 G (tf:real^N->(num->real^N)->real))` THEN
  SUBGOAL_THEN
   `!p q. (T4:real^N->(num->real^N)->real) y
            (\m. if m = 3 then p else if m = 4 then q else rfa_ft (S:real^N^N) [a; b] m) =
          T4 y (\m. if m = 1 then transp S ** basis a else if m = 2 then transp S ** basis b
                    else if m = 3 then p else q)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC RFA_TF_AGREE THEN
    MAP_EVERY EXISTS_TAC [`4`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `m = 1 \/ m = 2 \/ m = 3 \/ m = 4` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[rfa_ft] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[EL_CONS; ARITH];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `S:real^N^N`;
    `\p q. (T4:real^N->(num->real^N)->real) y
             (\m. if m = 1 then transp (S:real^N^N) ** basis a
                  else if m = 2 then transp S ** basis b else if m = 3 then p else q)`]
    RFA_TRACE_FRAME) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN GEN_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `T4:real^N->(num->real^N)->real`; `y:real^N`]
           RFA_HT_LIN4) THEN
    ASM_SIMP_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC RFA_TF_AGREE THEN MAP_EVERY EXISTS_TAC [`4`; `U:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[RFA_HT_FT4_EVAL]);;

let RFA_SH_DQ_FT = prove
 (`!U (G:real^N->real^N^N) y (S:real^N^N) c.
     metric_field U G /\ y IN U /\ matrix_inv(G y) = transp S ** S
     ==> drop(frechet_derivative (\x. lift(ltnorm2 2 G (lric2 G) x)) (at y)
                                 (transp S ** basis c)) =
         &2 * sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
                lric2 G y (rfa_ft S [a; b]) * lnabla 2 G (lric2 G) y (rfa_ft S [a; b; c])))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`; `lric2 (G:real^N->real^N^N)`;
                 `y:real^N`; `transp (S:real^N^N) ** basis c`] RFA_DNORM2_FORM) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[LRG_LRIC2_FIELD]; DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `rfa_sf 3 U (lnabla 2 G (lric2 (G:real^N->real^N^N)))` MP_TAC THENL
   [MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`;
                   `lric2 (G:real^N->real^N^N)`] RFA_SF_LNABLA) THEN
    ASM_SIMP_TAC[RFA_SF_LRIC2; ARITH];
    REWRITE_TAC[rfa_sf] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `lnabla 2 G (lric2 (G:real^N->real^N^N))`;
                 `transp (S:real^N^N) ** basis c`] RFA_FIX_SLOT_FIELD) THEN
  ASM_REWRITE_TAC[ARITH] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `lric2 (G:real^N->real^N^N)`;
     `\z' u. lnabla 2 G (lric2 (G:real^N->real^N^N)) z'
               (\m. if m = 3 then transp (S:real^N^N) ** basis c else u m)`;
     `y:real^N`; `S:real^N^N`] RFA_SH_LTINNER2_FT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[LRG_LRIC2_FIELD]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  AP_TERM_TAC THEN MATCH_MP_TAC RFA_TF_AGREE THEN
  MAP_EVERY EXISTS_TAC [`3`; `U:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[RFA_HT_FT3_EVAL] THEN
  SUBGOAL_THEN `m = 1 \/ m = 2 \/ m = 3` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[RFA_SH_FT2_EVAL; ARITH] THEN CONV_TAC NUM_REDUCE_CONV);;

let RFA_SH_D1_LINEAR = prove
 (`!U (f:real^N->real) y.
     open U /\ smooth_map_on U (\z. lift(f z)) /\ y IN U
     ==> linear (\v. lift(rfa_d1 f y v))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_d1; LIFT_DROP; ETA_AX] THEN
  MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

let RFA_SH_GR_FT = prove
 (`!U (G:real^N->real^N^N) (f:real^N->real) y (S:real^N^N).
     open U /\ y IN U /\ smooth_map_on U (\z. lift(f z)) /\ matrix_inv(G y) = transp S ** S
     ==> rfa_lginner G f f y =
         sum(1..dimindex(:N)) (\c. rfa_d1 f y (transp S ** basis c) pow 2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_lginner] THEN
  MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `S:real^N^N`;
                 `\v w. rfa_d1 (f:real^N->real) y v * rfa_d1 f y w`] RFA_TRACE_FRAME) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN GEN_TAC THENL
     [MATCH_MP_TAC RFA_LIN_MUL_CONST; MATCH_MP_TAC RFA_LIN_CONST_MUL] THEN
    MATCH_MP_TAC RFA_SH_D1_LINEAR THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_POW_2]]);;

let RFA_SH_SMOOTH_LIN2 = prove
 (`!U (f:real^N->real) g a b.
     open U /\ smooth_map_on U (\z. lift(f z)) /\ smooth_map_on U (\z. lift(g z))
     ==> smooth_map_on U (\z. lift(a * f z + b * g z))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[]);;

let RFA_SH_SMOOTH_CMUL = prove
 (`!U (f:real^N->real) a.
     open U /\ smooth_map_on U (\z. lift(f z))
     ==> smooth_map_on U (\z. lift(a * f z))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_CMUL] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[]);;

let RFA_SH_LLAP_LIN2 = prove
 (`!U (G:real^N->real^N^N) (f:real^N->real) g a b y.
     open U /\ smooth_map_on U (\z. lift(f z)) /\ smooth_map_on U (\z. lift(g z)) /\
     y IN U
     ==> llap G (\z. a * f z + b * g z) y = a * llap G f y + b * llap G g y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `\z. a * (f:real^N->real) z`;
                 `\z. b * (g:real^N->real) z`; `y:real^N`] RFA_LLAP_ADD) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[RFA_SH_SMOOTH_CMUL]; DISCH_THEN SUBST1_TAC] THEN
  BINOP_TAC THEN MATCH_MP_TAC RFA_LLAP_CMUL THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

let RFA_SH_D1_LIN2 = prove
 (`!U (f:real^N->real) g a b y h.
     open U /\ smooth_map_on U (\z. lift(f z)) /\ smooth_map_on U (\z. lift(g z)) /\
     y IN U
     ==> rfa_d1 (\z. a * f z + b * g z) y h = a * rfa_d1 f y h + b * rfa_d1 g y h`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!k:real^N->real. smooth_map_on U (\z. lift(k z))
                                 ==> (\z. lift(k z)) differentiable (at y)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z. a * (f:real^N->real) z`; `\z. b * (g:real^N->real) z`;
                 `y:real^N`; `h:real^N`] RFA_D1_ADD_AT) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC RFA_SH_SMOOTH_CMUL THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  BINOP_TAC THEN MATCH_MP_TAC RFA_D1_CMUL_AT THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

let RFA_SH_PSI_CRIT = prove
 (`!U (G:real^N->real^N^N) y a0 b0.
     metric_field U G /\ y IN U /\
     (!z. z IN U
          ==> a0 * ltnorm2 2 G (lric2 G) z + b0 * (lscalar G z * lscalar G z) <=
              a0 * ltnorm2 2 G (lric2 G) y + b0 * (lscalar G y * lscalar G y))
     ==> a0 * (&2 * ltinner 2 G (lric2 G) (ltlap 2 G (lric2 G)) y +
               &2 * ltnorm2 3 G (lnabla 2 G (lric2 G)) y) +
         b0 * (&2 * lscalar G y * llap G (lscalar G) y +
               &2 * rfa_lginner G (lscalar G) (lscalar G) y) <= &0 /\
         !v. a0 * rfa_d1 (ltnorm2 2 G (lric2 G)) y v +
             b0 * (&2 * lscalar G y * rfa_d1 (lscalar G) y v) = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U (\z. lift(ltnorm2 2 (G:real^N->real^N^N) (lric2 G) z)) /\
                smooth_map_on U (\z. lift(lscalar (G:real^N->real^N^N) z)) /\
                smooth_map_on U (\z. lift(lscalar (G:real^N->real^N^N) z * lscalar G z))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LRG_LTNORM2_SMOOTH THEN ASM_SIMP_TAC[LRG_LRIC2_FIELD];
      ASM_SIMP_TAC[LRG_LSCALAR_SMOOTH];
      MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL_REAL THEN ASM_SIMP_TAC[LRG_LSCALAR_SMOOTH]];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U (\z. lift(a0 * ltnorm2 2 (G:real^N->real^N^N) (lric2 G) z +
                                         b0 * (lscalar G z * lscalar G z)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_SH_SMOOTH_LIN2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `U:real^N->bool`; `G:real^N->real^N^N`;
                   `\z. a0 * ltnorm2 2 (G:real^N->real^N^N) (lric2 G) z +
                        b0 * (lscalar G z * lscalar G z)`;
                   `y:real^N`] RFA_LLAP_LOCAL_MAX) THEN
    BETA_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                   `ltnorm2 2 (G:real^N->real^N^N) (lric2 G)`;
                   `\z. lscalar (G:real^N->real^N^N) z * lscalar G z`;
                   `a0:real`; `b0:real`; `y:real^N`] RFA_SH_LLAP_LIN2) THEN
    BETA_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `lscalar (G:real^N->real^N^N)`;
                   `lscalar (G:real^N->real^N^N)`; `y:real^N`] RFA_LLAP_MUL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`;
                   `lric2 (G:real^N->real^N^N)`; `y:real^N`] RFA_LLAP_LTNORM2) THEN
    ASM_SIMP_TAC[LRG_LRIC2_FIELD] THEN DISCH_THEN SUBST1_TAC THEN
    CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (\z. lift(a0 * ltnorm2 2 (G:real^N->real^N^N) (lric2 G) z +
                                 b0 * (lscalar G z * lscalar G z))) (at y) = (\v. vec 0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC DIFFERENTIAL_ZERO_MAXMIN THEN
    MAP_EVERY EXISTS_TAC
     [`\z. lift(a0 * ltnorm2 2 (G:real^N->real^N^N) (lric2 G) z +
                b0 * (lscalar G z * lscalar G z))`; `y:real^N`; `U:real^N->bool`] THEN
    ASM_REWRITE_TAC[LIFT_DROP; GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `v:real^N` THEN
  SUBGOAL_THEN `rfa_d1 (\z. a0 * ltnorm2 2 (G:real^N->real^N^N) (lric2 G) z +
                            b0 * (lscalar G z * lscalar G z)) y v = &0`
  MP_TAC THENL
   [REWRITE_TAC[rfa_d1] THEN ASM_REWRITE_TAC[DROP_VEC]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `ltnorm2 2 (G:real^N->real^N^N) (lric2 G)`;
                 `\z. lscalar (G:real^N->real^N^N) z * lscalar G z`;
                 `a0:real`; `b0:real`; `y:real^N`; `v:real^N`] RFA_SH_D1_LIN2) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`lscalar (G:real^N->real^N^N)`; `lscalar (G:real^N->real^N^N)`;
                 `y:real^N`; `v:real^N`] RFA_D1_MUL_AT) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC]);;

let RFA_SH_RIC_POS = prove
 (`!U (G:real^3->real^3^3) y (S:real^3^3).
     metric_field U G /\ y IN U /\ invertible S /\ matrix_inv(G y) = transp S ** S /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 < lsectional G y u v)
     ==> &0 < lricci G y (transp S ** basis 1) (transp S ** basis 1) /\
         &0 < lricci G y (transp S ** basis 2) (transp S ** basis 2) /\
         &0 < lricci G y (transp S ** basis 3) (transp S ** basis 3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!b. 1 <= b /\ b <= 3
                    ==> &0 < lscalar G y / &2 -
                             lricci G y (transp S ** basis b) (transp (S:real^3^3) ** basis b)`
  MP_TAC THENL
   [X_GEN_TAC `b:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(transp (S:real^3^3) ** basis b) dot
                  ((G:real^3->real^3^3) y ** (transp S ** basis b)) = &1`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`(G:real^3->real^3^3) y`; `S:real^3^3`; `b:num`; `b:num`]
                    RFA_GFRAME_ORTHO) THEN
      ASM_REWRITE_TAC[DIMINDEX_3] THEN
      MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`]
                    LRG_METRIC_INVERTIBLE) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`;
                   `transp (S:real^3^3) ** basis b`] RFA_PCURV_AS_SEC) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^3` (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^3`; `v:real^3`]) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[lpcurv; lmetric2; lric2] THEN ASM_REWRITE_TAC[REAL_MUL_RID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`]
                RFA_SCAL_FRAME) THEN
  ASM_REWRITE_TAC[DIMINDEX_3; SUM_3] THEN DISCH_TAC THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th) THEN
                       MP_TAC(SPEC `3` th)) THEN
  ASM_REWRITE_TAC[ARITH] THEN REAL_ARITH_TAC);;

let RFA_SH_LRIC2_FT = prove
 (`!(G:real^N->real^N^N) y (S:real^N^N) i j.
     lric2 G y (rfa_ft S [i; j]) = lricci G y (transp S ** basis i) (transp S ** basis j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lric2; rfa_ft] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[EL_CONS; ARITH]);;

let RFA_SH_PINCH_CHART = prove
 (`!U (G:real^3->real^3^3) (pf:real^3->real) y.
     metric_field U G /\ y IN U /\ smooth_map_on U (\z. lift(pf z)) /\
     rfa_eqon U (lnabla 1 G (rfa_sh_df pf))
                (\y u. inv(&2) * lmetric2 G y u - lric2 G y u) /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 < lsectional G y u v) /\
     (!z. z IN U ==> lscalar G y pow 2 * ltnorm2 2 G (lric2 G) z <=
                     ltnorm2 2 G (lric2 G) y * lscalar G z pow 2)
     ==> &3 * ltnorm2 2 G (lric2 G) y = lscalar G y pow 2`,
  REPEAT GEN_TAC THEN INTRO_TAC "mf yU sm sol sec max" THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] RFA_RIC_EIGENFRAME) THEN
  ASM_REWRITE_TAC[DIMINDEX_3] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` (CONJUNCTS_THEN2 (LABEL_TAC "invS")
     (CONJUNCTS_THEN2 (LABEL_TAC "Sth") (LABEL_TAC "offd")))) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`]
                RFA_SH_RIC_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "pos") THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`;
                 `lscalar (G:real^3->real^3^3) y pow 2`;
                 `--(ltnorm2 2 (G:real^3->real^3^3) (lric2 G) y)`] RFA_SH_PSI_CRIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    USE_THEN "max" (MP_TAC o SPEC `z:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lap") (LABEL_TAC "grad"))] THEN
  SUBGOAL_THEN `rfa_sf 3 U (lnabla 2 G (lric2 (G:real^3->real^3^3)))` MP_TAC THENL
   [MP_TAC(ISPECL [`2`; `U:real^3->bool`; `G:real^3->real^3^3`;
                   `lric2 (G:real^3->real^3^3)`] RFA_SF_LNABLA) THEN
    ASM_SIMP_TAC[RFA_SF_LRIC2; ARITH];
    REWRITE_TAC[rfa_sf] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "tf3") (LABEL_TAC "sm3"))] THEN
  MP_TAC(ISPECL
   [`\i j. lricci (G:real^3->real^3^3) y (transp (S:real^3^3) ** basis i) (transp S ** basis j)`;
    `\a b c. lnabla 2 (G:real^3->real^3^3) (lric2 G) y (rfa_ft (S:real^3^3) [a; b; c])`;
    `\a b c d. lnabla 3 (G:real^3->real^3^3) (lnabla 2 G (lric2 G)) y
                 (rfa_ft (S:real^3^3) [a; b; c; d])`;
    `\c. rfa_sh_df (pf:real^3->real) y (rfa_ft (S:real^3^3) [c])`;
    `ltinner 2 (G:real^3->real^3^3) (lric2 G) (ltlap 2 G (lric2 G)) y`;
    `llap (G:real^3->real^3^3) (lscalar G) y`;
    `ltnorm2 3 (G:real^3->real^3^3) (lnabla 2 G (lric2 G)) y`;
    `rfa_lginner (G:real^3->real^3^3) (lscalar G) (lscalar G) y`;
    `ltnorm2 2 (G:real^3->real^3^3) (lric2 G) y`;
    `lscalar (G:real^3->real^3^3) y`;
    `\c. rfa_d1 (ltnorm2 2 (G:real^3->real^3^3) (lric2 G)) y (transp (S:real^3^3) ** basis c)`;
    `\c. rfa_d1 (lscalar (G:real^3->real^3^3)) y (transp (S:real^3^3) ** basis c)`]
   RFA_SH_PINCH_SUMS) THEN
  BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
  SUBGOAL_THEN `open(U:real^3->bool)` (LABEL_TAC "oU") THENL
   [USE_THEN "mf" (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE[metric_field]); ALL_TAC] THEN
  SUBGOAL_THEN `ltensor_field 2 U (ltlap 2 (G:real^3->real^3^3) (lric2 G))` (LABEL_TAC "tfl")
  THENL
   [MP_TAC(ISPECL [`2`; `U:real^3->bool`; `G:real^3->real^3^3`;
                   `lric2 (G:real^3->real^3^3)`] RFA_LTLAP_FIELD) THEN
    ASM_SIMP_TAC[LRG_LRIC2_FIELD];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "offd" ACCEPT_TAC;
    USE_THEN "pos" (fun th -> REWRITE_TAC[th]);
    USE_THEN "pos" (fun th -> REWRITE_TAC[th]);
    USE_THEN "pos" (fun th -> REWRITE_TAC[th]);
    X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`;
                   `pf:real^3->real`; `a:num`; `a:num`] RFA_SH_LAPF_RIC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[rfa_ric_a; RFA_SH_LRIC2_FT] THEN DISCH_THEN ACCEPT_TAC;
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`]
                  RFA_RICNORM_FRAME) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[DIMINDEX_3] THEN DISCH_THEN ACCEPT_TAC];
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`]
                  RFA_SCAL_FRAME) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[DIMINDEX_3] THEN DISCH_THEN ACCEPT_TAC];
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `lric2 (G:real^3->real^3^3)`;
                   `ltlap 2 (G:real^3->real^3^3) (lric2 G)`; `y:real^3`; `S:real^3^3`]
                  RFA_SH_LTINNER2_FT) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[LRG_LRIC2_FIELD]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[DIMINDEX_3; RFA_SH_LRIC2_FT] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
    AP_TERM_TAC THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `lric2 (G:real^3->real^3^3)`;
                   `y:real^3`; `S:real^3^3`; `a:num`; `b:num`] RFA_SH_LTLAP2_FT) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[RFA_SF_LRIC2]; REWRITE_TAC[DIMINDEX_3] THEN DISCH_THEN ACCEPT_TAC];
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`]
                  RFA_HT_LAP_FRAME) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; REWRITE_TAC[DIMINDEX_3] THEN DISCH_THEN(ACCEPT_TAC o SYM)];
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`;
                   `lnabla 2 (G:real^3->real^3^3) (lric2 G)`; `y:real^3`; `S:real^3^3`]
                  RFA_SH_LTNORM2_3_FT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[DIMINDEX_3] THEN DISCH_THEN ACCEPT_TAC];
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `lscalar (G:real^3->real^3^3)`;
                   `y:real^3`; `S:real^3^3`] RFA_SH_GR_FT) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[LRG_LSCALAR_SMOOTH]; REWRITE_TAC[DIMINDEX_3] THEN DISCH_THEN ACCEPT_TAC];
    X_GEN_TAC `c:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`; `c:num`]
                  RFA_HT_DSC_FRAME) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[];
      REWRITE_TAC[DIMINDEX_3; rfa_d1] THEN DISCH_THEN(ACCEPT_TAC o SYM)];
    X_GEN_TAC `c:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`; `c:num`]
                  RFA_SH_DQ_FT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[];
      REWRITE_TAC[DIMINDEX_3; rfa_d1; RFA_SH_LRIC2_FT] THEN DISCH_THEN ACCEPT_TAC];
    X_GEN_TAC `c:num` THEN STRIP_TAC THEN
    USE_THEN "grad" (ACCEPT_TAC o SPEC `transp (S:real^3^3) ** basis c`);
    USE_THEN "lap" ACCEPT_TAC]);;

(* ========================================================================= *)
(* Chart independence of |Ric|^2 and its continuity                          *)
(* (RFA_SH_RICNORM_CHART, RFA_SH_RICN2_EQ, RFA_SH_RICN2_CONTINUOUS); the     *)
(* pointwise equality case R^2 <= 3 |Ric|^2 with equality iff Einstein      *)
(* (RFA_SH_EINSTEIN_PT); R > 0 from sec > 0 (RFA_SH_SCAL_POS); the Leibniz   *)
(* rule for lnabla of h times T (RFA_SH_LNABLA_FMUL); the Riemannian Schur  *)
(* lemma in a 3-d chart (RFA_SH_SCHUR_CHART: Einstein on an open set gives   *)
(* dR = 0, by the contracted Bianchi identity); constant curvature R/6 of an *)
(* Einstein point (RFA_SH_SEC_EINSTEIN); locally constant functions on a     *)
(* connected space are constant (RFA_SH_LOCCONST_CONNECTED); R is locally    *)
(* constant when dR = 0 in every chart (RFA_SH_SCAL_LOCCONST).               *)
(* ========================================================================= *)

let RFA_SH_RICNORM_CHART = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) c x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     c IN atlas /\ x IN FST c
     ==> ltnorm2 2 (metric_local atlas c g) (lric2 (metric_local atlas c g)) (SND c x) =
         ltnorm2 2 (metric_local atlas (chart_at atlas x) g)
                   (lric2 (metric_local atlas (chart_at atlas x) g))
                   (SND(chart_at atlas x) x)`,
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `g:A->real^N^N`; `U:A->bool`; `phi:A->real^N`; `x:A`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`,
           `cc:(A->bool)#(A->real^N)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `psi:A->real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in top (U:A->bool) /\ open_in top (V:A->bool)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART);
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `V:A->bool`; `psi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART)] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (phi:A->real^N) (U INTER V)) /\
                open(IMAGE (psi:A->real^N) (U INTER V))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THENL
     [EXISTS_TAC `U:A->bool`; EXISTS_TAC `V:A->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_INTER] THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `h = chart_trans (U:A->bool,phi:A->real^N) (V,psi)` THEN
  ABBREV_TAC `G' = metric_local atlas (V:A->bool,psi:A->real^N) (g:A->real^N^N)` THEN
  SUBGOAL_THEN `metric_field (IMAGE (psi:A->real^N) (U INTER V)) (G':real^N->real^N^N)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (psi:A->real^N) V` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "G'" THEN
      UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)` THEN
      REWRITE_TAC[riemannian_metric] THEN
      DISCH_THEN(MP_TAC o SPEC `(V:A->bool,psi:A->real^N)`) THEN
      ASM_REWRITE_TAC[FST; SND];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `diffeomorphism_on (IMAGE (phi:A->real^N) (U INTER V))
                  (IMAGE (psi:A->real^N) (U INTER V)) h (chart_trans (V,psi) (U,phi))`
  ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN MATCH_MP_TAC CHART_TRANS_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:A->real^N) x IN IMAGE phi (U INTER V)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN IMAGE (phi:A->real^N) (U INTER V)
                    ==> metric_local atlas (U,phi) (g:A->real^N^N) z = mpullback h G' z`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `x':A` THEN STRIP_TAC THEN
    MAP_EVERY EXPAND_TAC ["h"; "G'"] THEN MATCH_MP_TAC METRIC_LOCAL_TRANS THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `ltnorm2 2 (mpullback h (G':real^N->real^N^N)) (ltpullback h (lric2 G'))
                (phi(x:A))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_LTNORM2_EQ THEN ASM_SIMP_TAC[] THEN X_GEN_TAC `u:num->real^N` THEN
    REWRITE_TAC[lric2; ltpullback] THEN
    MP_TAC(ISPECL [`IMAGE (psi:A->real^N) (U INTER V)`; `IMAGE (phi:A->real^N) (U INTER V)`;
                   `h:real^N->real^N`; `chart_trans (V:A->bool,psi:A->real^N) (U,phi)`;
                   `G':real^N->real^N^N`; `(phi:A->real^N) x`;
                   `(u:num->real^N) 1`; `(u:num->real^N) 2`] LRICCI_PULLBACK) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC LRICCI_LOCAL THEN EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER V)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`2`; `IMAGE (psi:A->real^N) (U INTER V)`; `IMAGE (phi:A->real^N) (U INTER V)`;
                 `h:real^N->real^N`; `chart_trans (V:A->bool,psi:A->real^N) (U,phi)`;
                 `G':real^N->real^N^N`; `lric2 (G':real^N->real^N^N)`; `(phi:A->real^N) x`]
                LTNORM2_PULLBACK) THEN
  ASM_SIMP_TAC[LRG_LRIC2_FIELD] THEN DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN EXPAND_TAC "h" THEN
  MATCH_MP_TAC CHART_TRANS_AT THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
  ASM_REWRITE_TAC[]);;

let RFA_SH_RICN2_EQ = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) x.
     rfs_ric_norm2 atlas g x =
     ltnorm2 2 (metric_local atlas (chart_at atlas x) g)
               (lric2 (metric_local atlas (chart_at atlas x) g)) (SND(chart_at atlas x) x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_ric_norm2] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; lric2]);;

let RFA_SH_RICN2_CONTINUOUS = prove
 (`!top atlas (g:A->real^N^N).
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g
        ==> continuous_map (top,euclideanreal) (rfs_ric_norm2 atlas g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TOPC_CONTINUOUS_MAP_LOCAL THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`,
           `c:(A->bool)#(A->real^N)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [smooth_manifold_atlas]) THEN
  DISCH_THEN(MP_TAC o SPECL [`U:A->bool`; `phi:A->real^N`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
  EXISTS_TAC `\z:A. ltnorm2 2 (metric_local atlas (U,phi) (g:A->real^N^N))
                      (lric2 (metric_local atlas (U,phi) g)) (phi z)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    BETA_TAC THEN REWRITE_TAC[RFA_SH_RICN2_EQ] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `(U:A->bool,phi:A->real^N)`; `z:A`] RFA_SH_RICNORM_CHART) THEN
    ASM_REWRITE_TAC[FST; SND];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z:A. ltnorm2 2 (metric_local atlas (U,phi) (g:A->real^N^N))
                    (lric2 (metric_local atlas (U,phi) g)) (phi z)) =
    (\y. ltnorm2 2 (metric_local atlas (U,phi) g) (lric2 (metric_local atlas (U,phi) g)) y) o
    (phi:A->real^N)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology euclidean (IMAGE (phi:A->real^N) U)` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[HOMEOMORPHIC_IMP_CONTINUOUS_MAP]; ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUS_MAP_EQ_LIFT; CONTINUOUS_MAP_EUCLIDEAN; o_DEF] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN
  SUBGOAL_THEN `metric_field (IMAGE (phi:A->real^N) U)
                             (metric_local atlas (U,phi) (g:A->real^N^N))` ASSUME_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
    REWRITE_TAC[riemannian_metric] THEN
    DISCH_THEN(MP_TAC o SPEC `(U:A->bool,phi:A->real^N)`) THEN
    ASM_REWRITE_TAC[FST; SND];
    ALL_TAC] THEN
  MATCH_MP_TAC LRG_LTNORM2_SMOOTH THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^N) U`; `metric_local atlas (U,phi) (g:A->real^N^N)`]
                RFA_SF_LRIC2) THEN
  ASM_SIMP_TAC[rfa_sf]);;


let RFA_SH_EINSTEIN_PT = prove
 (`!U (G:real^3->real^3^3) y.
     metric_field U G /\ y IN U
     ==> lscalar G y pow 2 <= &3 * ltnorm2 2 G (lric2 G) y /\
         (&3 * ltnorm2 2 G (lric2 G) y = lscalar G y pow 2
          ==> !v w. lricci G y v w = lscalar G y / &3 * (v dot (G y ** w)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] RFA_RIC_EIGENFRAME) THEN
  ASM_REWRITE_TAC[DIMINDEX_3] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "offd")))) THEN
  SUBGOAL_THEN
   `lricci (G:real^3->real^3^3) y (transp (S:real^3^3) ** basis 1) (transp S ** basis 2) = &0 /\
    lricci G y (transp S ** basis 1) (transp S ** basis 3) = &0 /\
    lricci G y (transp S ** basis 2) (transp S ** basis 1) = &0 /\
    lricci G y (transp S ** basis 2) (transp S ** basis 3) = &0 /\
    lricci G y (transp S ** basis 3) (transp S ** basis 1) = &0 /\
    lricci G y (transp S ** basis 3) (transp S ** basis 2) = &0`
  (LABEL_TAC "zs") THENL
   [REPEAT CONJ_TAC THEN USE_THEN "offd" MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`]
                RFA_RICNORM_FRAME) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`]
                RFA_SCAL_FRAME) THEN
  ASM_REWRITE_TAC[DIMINDEX_3; SUM_3] THEN
  USE_THEN "zs" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[REAL_ARITH `&0 pow 2 = &0`; REAL_ADD_LID; REAL_ADD_RID] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `l1 = lricci (G:real^3->real^3^3) y (transp (S:real^3^3) ** basis 1) (transp S ** basis 1)` THEN
  ABBREV_TAC `l2 = lricci (G:real^3->real^3^3) y (transp (S:real^3^3) ** basis 2) (transp S ** basis 2)` THEN
  ABBREV_TAC `l3 = lricci (G:real^3->real^3^3) y (transp (S:real^3^3) ** basis 3) (transp S ** basis 3)` THEN
  CONJ_TAC THENL
   [MP_TAC(SPEC `l1 - l2:real` REAL_LE_POW_2) THEN MP_TAC(SPEC `l1 - l3:real` REAL_LE_POW_2) THEN
    MP_TAC(SPEC `l2 - l3:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(l1:real) = l2 /\ l2 = l3` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `l1 - l2:real` REAL_LE_POW_2) THEN MP_TAC(SPEC `l1 - l3:real` REAL_LE_POW_2) THEN
    MP_TAC(SPEC `l2 - l3:real` REAL_LE_POW_2) THEN
    SUBGOAL_THEN `(l1 - l2) pow 2 + (l1 - l3) pow 2 + (l2 - l3) pow 2 = &0` MP_TAC THENL
     [UNDISCH_TAC `&3 * (l1 pow 2 + l2 pow 2 + l3 pow 2) = (l1 + l2 + l3) pow 2` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `(l1 - l2) pow 2 = &0 /\ (l2 - l3) pow 2 = &0` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_POW_EQ_0; ARITH_EQ] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `invertible((G:real^3->real^3^3) y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`(G:real^3->real^3^3) y`; `S:real^3^3`; `lricci (G:real^3->real^3^3) y`;
                 `\v w. (l1 + l2 + l3) / &3 * (v dot ((G:real^3->real^3^3) y ** w))`;
                 `v:real^3`; `w:real^3`] RFA_BILIN_FRAME_EQ) THEN
  BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] LRG_LRICCI_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC RFA_LIN_CONST_MUL THEN ONCE_REWRITE_TAC[DOT_SYM] THEN
    REWRITE_TAC[LINEAR_LIFT_DOT];
    GEN_TAC THEN MATCH_MP_TAC RFA_LIN_CONST_MUL THEN REWRITE_TAC[RFA_LIFT_DOT_GMUL_LINEAR];
    ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_3] THEN MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(G:real^3->real^3^3) y`; `S:real^3^3`; `a:num`; `b:num`] RFA_GFRAME_ORTHO) THEN
  ASM_REWRITE_TAC[DIMINDEX_3] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_CASES_TAC `a:num = b` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `b = 1 \/ b = 2 \/ b = 3` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN USE_THEN "offd" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

let RFA_SH_SCAL_POS = prove
 (`!U (G:real^3->real^3^3) y.
     metric_field U G /\ y IN U /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 < lsectional G y u v)
     ==> &0 < lscalar G y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] LRG_METRIC_INV_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`]
                RFA_SH_RIC_POS) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`]
                RFA_SCAL_FRAME) THEN
  ASM_REWRITE_TAC[DIMINDEX_3; SUM_3] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

let RFA_SH_LNABLA_FMUL = prove
 (`!k U (G:real^N->real^N^N) (h:real^N->real) (tf:real^N->(num->real^N)->real) y u.
     open U /\ y IN U /\ smooth_map_on U (\z. lift(h z)) /\
     (!u. smooth_map_on U (\z. lift(tf z u)))
     ==> lnabla k G (\z u. h z * tf z u) y u =
         rfa_d1 h y (u(k + 1)) * tf y u + h y * lnabla k G tf y u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lnabla] THEN
  MP_TAC(ISPECL [`h:real^N->real`; `\z. (tf:real^N->(num->real^N)->real) z u`; `y:real^N`;
                 `(u:num->real^N)(k + 1)`] RFA_D1_MUL_AT) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[rfa_d1] THEN DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[SUM_LMUL] THEN REAL_ARITH_TAC);;

let RFA_SH_SCHUR_CHART = prove
 (`!U (G:real^3->real^3^3).
     metric_field U G /\
     (!z. z IN U ==> !v w. lricci G z v w = lscalar G z / &3 * (v dot (G z ** w)))
     ==> !y. y IN U ==> frechet_derivative (\x. lift(lscalar G x)) (at y) = (\v. vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `open(U:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U (\z. lift(lscalar (G:real^3->real^3^3) z))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LRG_LSCALAR_SMOOTH]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U (\z. lift(lscalar (G:real^3->real^3^3) z / &3))` ASSUME_TAC THENL
   [SUBGOAL_THEN `!z. lscalar (G:real^3->real^3^3) z / &3 = inv(&3) * lscalar G z`
    (fun th -> REWRITE_TAC[th]) THENL [GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC RFA_SH_SMOOTH_CMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v. rfa_d1 (\z. lscalar (G:real^3->real^3^3) z / &3) y v =
                    inv(&3) * rfa_d1 (lscalar G) y v`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `(\z. lscalar (G:real^3->real^3^3) z / &3) = (\z. inv(&3) * lscalar G z)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC RFA_D1_CMUL_AT THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`2`; `U:real^3->bool`; `G:real^3->real^3^3`; `lric2 (G:real^3->real^3^3)`;
                 `\z u. lscalar (G:real^3->real^3^3) z / &3 * lmetric2 G z u`]
                RFA_EQON_LNABLA) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[rfa_eqon; lric2; lmetric2] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[rfa_eqon] THEN DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "eqd") THEN
  SUBGOAL_THEN
   `!u. lnabla 2 G (lric2 (G:real^3->real^3^3)) y u =
        inv(&3) * rfa_d1 (lscalar G) y (u 3) * lmetric2 G y u`
  (LABEL_TAC "dric") THENL
   [GEN_TAC THEN USE_THEN "eqd" (fun th -> REWRITE_TAC[th]) THEN
    MP_TAC(ISPECL [`2`; `U:real^3->bool`; `G:real^3->real^3^3`;
                   `\z. lscalar (G:real^3->real^3^3) z / &3`; `lmetric2 (G:real^3->real^3^3)`;
                   `y:real^3`; `u:num->real^3`] RFA_SH_LNABLA_FMUL) THEN
    BETA_TAC THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[LRG_LMETRIC2_FIELD]; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `u:num->real^3`]
                  LNABLA_METRIC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "eqd" (K ALL_TAC) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] LRG_METRIC_INV_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `invertible((G:real^3->real^3^3) y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  SUBGOAL_THEN `!b. 1 <= b /\ b <= 3
                    ==> rfa_d1 (lscalar (G:real^3->real^3^3)) y (transp (S:real^3^3) ** basis b) =
                        &0`
  ASSUME_TAC THENL
   [X_GEN_TAC `b:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`; `b:num`]
                  RFA_HT_BIANCHI_FRAME) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[DIMINDEX_3; SUM_3] THEN USE_THEN "dric" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[GSYM rfa_d1; lmetric2; ETA_AX] THEN
    SIMP_TAC[RFA_HT_FT3_EVAL; ARITH] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC(ISPECL [`(G:real^3->real^3^3) y`; `S:real^3^3`] RFA_GFRAME_ORTHO) THEN
    ASM_SIMP_TAC[DIMINDEX_3; ARITH] THEN DISCH_TAC THEN
    SUBGOAL_THEN `b = 1 \/ b = 2 \/ b = 3` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `v:real^3` THEN
  REWRITE_TAC[GSYM DROP_EQ; DROP_VEC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`; `v:real^3`]
                RFA_HT_DSC_EXPAND) THEN
  ASM_REWRITE_TAC[DIMINDEX_3; SUM_3] THEN DISCH_THEN SUBST1_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[rfa_d1]) THEN
  FIRST_ASSUM(fun th -> MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th) THEN MP_TAC(SPEC `3` th)) THEN
  REWRITE_TAC[ARITH] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let RFA_SH_SEC_EINSTEIN = prove
 (`!U (G:real^3->real^3^3) y.
     metric_field U G /\ y IN U /\
     (!v w. lricci G y v w = lscalar G y / &3 * (v dot (G y ** w)))
     ==> !u v. ~collinear {vec 0,u,v} ==> lsectional G y u v = lscalar G y / &6`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `u:real^3`; `v:real^3`]
                RFA_SEC_AS_PCURV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[lpcurv; lmetric2; lric2] THEN REAL_ARITH_TAC);;

let RFA_SH_LOCCONST_CONNECTED = prove
 (`!top (h:A->real).
     connected_space top /\
     (!x. x IN topspace top
          ==> ?W. open_in top W /\ x IN W /\ !x'. x' IN W ==> h x' = h x)
     ==> !x y. x IN topspace top /\ y IN topspace top ==> h y = h x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x0:A` THEN X_GEN_TAC `y0:A` THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONNECTED_SPACE_CLOPEN_IN]) THEN
  DISCH_THEN(MP_TAC o SPEC `{x:A | x IN topspace top /\ (h:A->real) x = h x0}`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN X_GEN_TAC `x:A` THEN REWRITE_TAC[IN_ELIM_THM] THEN
      STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `W:A->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `W:A->bool` THEN ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      X_GEN_TAC `z:A` THEN DISCH_TAC THEN CONJ_TAC THENL
       [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ASM_MESON_TAC[]];
      REWRITE_TAC[closed_in] THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN X_GEN_TAC `x:A` THEN
      REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `W:A->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `W:A->bool` THEN ASM_REWRITE_TAC[SUBSET; IN_DIFF; IN_ELIM_THM] THEN
      X_GEN_TAC `z:A` THEN DISCH_TAC THEN CONJ_TAC THENL
       [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ASM_MESON_TAC[]]];
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN ASM_MESON_TAC[]]);;

let RFA_SH_SCAL_LOCCONST = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N).
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     (!c y. c IN atlas /\ y IN IMAGE (SND c) (FST c)
            ==> frechet_derivative (\x. lift(lscalar (metric_local atlas c g) x)) (at y) =
                (\v. vec 0))
     ==> !x. x IN topspace top
             ==> ?W. open_in top W /\ x IN W /\
                     !x'. x' IN W ==> mfd_scalar atlas g x' = mfd_scalar atlas g x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?U phi. chart_at atlas (x:A) = (U:A->bool,phi:A->real^N)`
  STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[FST] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_scalar atlas (g:A->real^N^N) x =
                lscalar (metric_local atlas (U,phi) g) ((phi:A->real^N) x)`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[mfd_scalar; SND]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field (IMAGE (phi:A->real^N) U) (metric_local atlas (U,phi) (g:A->real^N^N))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `(U:A->bool,phi:A->real^N)` o
      GEN_REWRITE_RULE I [riemannian_metric]) THEN ASM_REWRITE_TAC[FST; SND];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:A->real^N) x IN IMAGE phi U` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `(phi:A->real^N) x` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL] o
    check (fun th -> try fst(dest_const(rator(concl th))) = "open" with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!z. z IN ball((phi:A->real^N) x,r)
        ==> lscalar (metric_local atlas (U,phi) (g:A->real^N^N)) z =
            lscalar (metric_local atlas (U,phi) g) (phi x)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\z. lift(lscalar (metric_local atlas (U,phi) (g:A->real^N^N)) z)`;
                   `ball((phi:A->real^N) x,r)`] HAS_DERIVATIVE_ZERO_CONSTANT) THEN
    REWRITE_TAC[CONVEX_BALL] THEN ANTS_TAC THENL
     [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
      SUBGOAL_THEN `(z:real^N) IN IMAGE (phi:A->real^N) U` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`(U:A->bool,phi:A->real^N)`; `z:real^N`]) THEN
      ASM_REWRITE_TAC[FST; SND] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `IMAGE (phi:A->real^N) U` THEN ASM_SIMP_TAC[LRG_LSCALAR_SMOOTH];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `C:real^1`) THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    MP_TAC(SPEC `(phi:A->real^N) x` (ASSUME
      `!x'. x' IN ball((phi:A->real^N) x,r)
            ==> lift(lscalar (metric_local atlas (U,phi) (g:A->real^N^N)) x') = C`)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N`) THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN REWRITE_TAC[GSYM LIFT_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `{x':A | x' IN U /\ (phi:A->real^N) x' IN ball(phi x,r)}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`phi:A->real^N`; `subtopology top (U:A->bool)`; `euclidean:(real^N)topology`;
                   `ball((phi:A->real^N) x,r)`] OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    REWRITE_TAC[OPEN_IN_EUCLIDEAN; OPEN_BALL] THEN ANTS_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP) THEN
      SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; EXTENSION; IN_ELIM_THM; IN_INTER] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `x':A` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x':A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x':A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[mfd_scalar] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x':A))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x':A))`;
                 `g:A->real^N^N`; `x':A`] LSCALAR_CHART_TRANS) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The manifold-level argument and the 3-d headline.  A                      *)
(* continuous function on a nonempty compact space attains its maximum      *)
(* (RFA_SH_GLOBAL_MAX); the soliton data in every chart (RFA_SH_CHART_DATA); *)
(* |Ric|^2 and R in any chart (RFA_SH_QR_CHART); R > 0 (RFA_SH_MFD_SCAL_POS);*)
(* at a maximum point of |Ric|^2 / R^2, 3 |Ric|^2 = R^2 (RFA_SH_MAX_PINCH);  *)
(* then Einstein everywhere (RFA_SH_EINSTEIN_ALL), R constant                *)
(* (RFA_SH_SCAL_CONST), and every sectional curvature is R/6 > 0:           *)
(* RFA_SHRINKER_ROUND_3D, the 3-d clause of the shrinker statement.          *)
(* ========================================================================= *)

let RFA_SH_GLOBAL_MAX = prove
 (`!top (h:A->real).
     compact_space top /\ ~(topspace top = {}) /\ continuous_map (top,euclideanreal) h
     ==> ?x0. x0 IN topspace top /\ !x. x IN topspace top ==> h x <= h x0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `euclideanreal`; `h:A->real`; `topspace top:A->bool`]
                IMAGE_COMPACT_IN) THEN
  ASM_REWRITE_TAC[GSYM compact_space; GSYM real_compact_def] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `IMAGE (h:A->real) (topspace top)` REAL_COMPACT_ATTAINS_SUP) THEN
  ASM_REWRITE_TAC[IMAGE_EQ_EMPTY] THEN REWRITE_TAC[EXISTS_IN_IMAGE; FORALL_IN_IMAGE] THEN
  MESON_TAC[]);;

let RFA_SH_CHART_DATA = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (f:A->real) c.
     p2b_shrinker (top,atlas) g f /\ c IN atlas
     ==> metric_field (IMAGE (SND c) (FST c)) (metric_local atlas c g) /\
         smooth_map_on (IMAGE (SND c) (FST c)) (\y. lift(f(chart_inv c y))) /\
         rfa_eqon (IMAGE (SND c) (FST c))
           (lnabla 1 (metric_local atlas c g) (rfa_sh_df (\y. f(chart_inv c y))))
           (\y u. inv(&2) * lmetric2 (metric_local atlas c g) y u -
                  lric2 (metric_local atlas c g) y u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `mfd_smooth_on (atlas:((A->bool)#(A->real^N))->bool) (topspace top)
                   (\x. lift((f:A->real) x))` THEN
    REWRITE_TAC[mfd_smooth_on] THEN
    DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN ASM_REWRITE_TAC[o_DEF] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
                  SMOOTH_MANIFOLD_ATLAS_CHART) THEN
    ASM_REWRITE_TAC[PAIR] THEN STRIP_TAC THEN
    SUBGOAL_THEN `FST(c:(A->bool)#(A->real^N)) INTER topspace top = FST c` SUBST1_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET; SET_RULE `!s t:A->bool. s SUBSET t ==> s INTER t = s`];
      SIMP_TAC[]];
    REWRITE_TAC[rfa_eqon; rfa_sh_df] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `f:A->real`; `c:(A->bool)#(A->real^N)`] RFA_SHRINKER_CHART) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`y:real^N`; `u:num->real^N`]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(ACCEPT_TAC o MATCH_MP (REAL_ARITH `a + b = c ==> b = c - a`))]);;

let RFA_SH_QR_CHART = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) c x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     c IN atlas /\ x IN FST c
     ==> rfs_ric_norm2 atlas g x =
         ltnorm2 2 (metric_local atlas c g) (lric2 (metric_local atlas c g)) (SND c x) /\
         mfd_scalar atlas g x = lscalar (metric_local atlas c g) (SND c x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[RFA_SH_RICN2_EQ] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC RFA_SH_RICNORM_CHART THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_scalar] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
                SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[PAIR] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                 `g:A->real^N^N`; `x:A`] LSCALAR_CHART_TRANS) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER] THEN DISCH_THEN(ACCEPT_TAC o SYM));;

let RFA_SH_MFD_SCAL_POS = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top /\
     (!u v. ~collinear {vec 0,u,v} ==> &0 < mfd_sectional atlas g x u v)
     ==> &0 < mfd_scalar atlas g x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mfd_scalar] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC RFA_SH_SCAL_POS THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                    (FST(chart_at atlas x))` THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)` THEN
    REWRITE_TAC[riemannian_metric] THEN
    DISCH_THEN(MP_TAC o SPEC `chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)`) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `!u v. ~collinear {vec 0,u,v}
                       ==> &0 < mfd_sectional atlas (g:A->real^3^3) (x:A) u v` THEN
    REWRITE_TAC[mfd_sectional]]);;

let RFA_SH_DIV_LE = prove
 (`!a b c d. &0 < b /\ &0 < d /\ a / b <= c / d ==> a * d <= c * b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a / b) * (b * d) <= (c / d) * (b * d)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(a / b) * (b * d) = a * d /\ (c / d) * (b * d) = c * b`
  (fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_FIELD `~(b = &0) ==> (a / b) * (b * d) = a * d`);
    MATCH_MP_TAC(REAL_FIELD `~(d = &0) ==> (c / d) * (b * d) = c * b`)] THEN
  ASM_REAL_ARITH_TAC);;

let RFA_SH_MAX_PINCH = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f x0.
     p2b_shrinker (top,atlas) g f /\
     (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
              ==> &0 < mfd_sectional atlas g x u v) /\
     x0 IN topspace top /\
     (!x. x IN topspace top
          ==> rfs_ric_norm2 atlas g x / mfd_scalar atlas g x pow 2 <=
              rfs_ric_norm2 atlas g x0 / mfd_scalar atlas g x0 pow 2)
     ==> &3 * rfs_ric_norm2 atlas g x0 = mfd_scalar atlas g x0 pow 2`,
  REPEAT GEN_TAC THEN INTRO_TAC "shr sec x0 max" THEN
  USE_THEN "shr" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  SUBGOAL_THEN `!x. x IN topspace top ==> &0 < mfd_scalar atlas (g:A->real^3^3) x`
  (LABEL_TAC "Rpos") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_SH_MFD_SCAL_POS THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x0:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `chart_at (atlas:((A->bool)#(A->real^3))->bool) (x0:A)`]
                RFA_SH_CHART_DATA) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) (x0:A)` THEN
  SUBGOAL_THEN
   `!x. x IN FST c
        ==> rfs_ric_norm2 atlas (g:A->real^3^3) x =
            ltnorm2 2 (metric_local atlas c g) (lric2 (metric_local atlas c g)) (SND c x) /\
            mfd_scalar atlas g x =
            lscalar (metric_local atlas c g) (SND (c:(A->bool)#(A->real^3)) x)`
  (LABEL_TAC "qr") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC RFA_SH_QR_CHART THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN FST (c:(A->bool)#(A->real^3)) ==> x IN topspace top`
  (LABEL_TAC "fstc") THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `FST(c:(A->bool)#(A->real^3))`; `SND(c:(A->bool)#(A->real^3))`]
                  SMOOTH_MANIFOLD_ATLAS_CHART) THEN
    ASM_REWRITE_TAC[PAIR] THEN STRIP_TAC THEN ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  USE_THEN "qr" (MP_TAC o SPEC `x0:A`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
  MATCH_MP_TAC RFA_SH_PINCH_CHART THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (SND c) (FST (c:(A->bool)#(A->real^3)))`;
                        `\y. (f:A->real)(chart_inv (c:(A->bool)#(A->real^3)) y)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    USE_THEN "sec" (MP_TAC o SPECL [`x0:A`; `u:real^3`; `v:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[mfd_sectional] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [USE_THEN "fstc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "qr" (MP_TAC o SPEC `x:A`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
  USE_THEN "qr" (MP_TAC o SPEC `x0:A`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
  MATCH_MP_TAC(REAL_ARITH `a * d <= c * b ==> d * a <= c * b`) THEN
  MATCH_MP_TAC RFA_SH_DIV_LE THEN
  REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_POW_LT) THEN
  TRY(USE_THEN "Rpos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  USE_THEN "max" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let RFA_SH_EINSTEIN_ALL = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3).
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     (!x. x IN topspace top ==> &3 * rfs_ric_norm2 atlas g x = mfd_scalar atlas g x pow 2)
     ==> !c x. c IN atlas /\ x IN FST c
               ==> !v w. lricci (metric_local atlas c g) (SND c x) v w =
                         lscalar (metric_local atlas c g) (SND c x) / &3 *
                         (v dot (metric_local atlas c g (SND c x) ** w))`,
  REPEAT GEN_TAC THEN INTRO_TAC "sma rm ein" THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `FST(c:(A->bool)#(A->real^3))`; `SND(c:(A->bool)#(A->real^3))`]
                  SMOOTH_MANIFOLD_ATLAS_CHART) THEN
    ASM_REWRITE_TAC[PAIR] THEN STRIP_TAC THEN ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `c:(A->bool)#(A->real^3)`; `x:A`] RFA_SH_QR_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (SND c) (FST (c:(A->bool)#(A->real^3)))`;
                 `metric_local atlas c (g:A->real^3^3)`; `SND (c:(A->bool)#(A->real^3)) x`]
                RFA_SH_EINSTEIN_PT) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "rm" (MP_TAC o SPEC `c:(A->bool)#(A->real^3)` o
                     GEN_REWRITE_RULE I [riemannian_metric]) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
  USE_THEN "ein" (MP_TAC o SPEC `x:A`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

let RFA_SH_SCAL_CONST = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3).
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ connected_space top /\
     (!c x. c IN atlas /\ x IN FST c
            ==> !v w. lricci (metric_local atlas c g) (SND c x) v w =
                      lscalar (metric_local atlas c g) (SND c x) / &3 *
                      (v dot (metric_local atlas c g (SND c x) ** w)))
     ==> !x y. x IN topspace top /\ y IN topspace top
               ==> mfd_scalar atlas g y = mfd_scalar atlas g x`,
  REPEAT GEN_TAC THEN INTRO_TAC "sma rm conn ein" THEN
  MATCH_MP_TAC RFA_SH_LOCCONST_CONNECTED THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC RFA_SH_SCAL_LOCCONST THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^3)`; `y:real^3`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (SND c) (FST (c:(A->bool)#(A->real^3)))`;
                 `metric_local atlas c (g:A->real^3^3)`] RFA_SH_SCHUR_CHART) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "rm" (MP_TAC o SPEC `c:(A->bool)#(A->real^3)` o
                     GEN_REWRITE_RULE I [riemannian_metric]) THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      USE_THEN "ein" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let RFA_SHRINKER_ROUND_3D = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f.
     hausdorff_space top /\ compact_space top /\ connected_space top /\
     p2b_shrinker (top,atlas) g f /\
     (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
              ==> &0 < mfd_sectional atlas g x u v)
     ==> p2b_round (top,atlas) g`,
  REPEAT GEN_TAC THEN INTRO_TAC "haus cpt conn shr sec" THEN
  USE_THEN "shr" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  REWRITE_TAC[p2b_round] THEN
  ASM_CASES_TAC `topspace top:A->bool = {}` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN topspace top ==> &0 < mfd_scalar atlas (g:A->real^3^3) x`
  (LABEL_TAC "Rpos") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_SH_MFD_SCAL_POS THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `continuous_map (top,euclideanreal)
      (\x. rfs_ric_norm2 atlas (g:A->real^3^3) x / mfd_scalar atlas g x pow 2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_REAL_DIV THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC RFA_SH_RICN2_CONTINUOUS THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_MAP_REAL_POW THEN REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC MFD_SCALAR_CONTINUOUS THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN REWRITE_TAC[REAL_POW_EQ_0; ARITH_EQ] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x = &0)`) THEN
      USE_THEN "Rpos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`;
                 `\x. rfs_ric_norm2 atlas (g:A->real^3^3) x / mfd_scalar atlas g x pow 2`]
                RFA_SH_GLOBAL_MAX) THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:A` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "max"))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `f:A->real`; `x0:A`] RFA_SH_MAX_PINCH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "q0")] THEN
  SUBGOAL_THEN
   `!x. x IN topspace top
        ==> &3 * rfs_ric_norm2 atlas (g:A->real^3^3) x = mfd_scalar atlas g x pow 2`
  (LABEL_TAC "ein") THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`]
                  CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                          (FST(chart_at atlas x))`;
                   `metric_local atlas (chart_at atlas (x:A)) (g:A->real^3^3)`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) x`]
                  RFA_SH_EINSTEIN_PT) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)` THEN
        REWRITE_TAC[riemannian_metric] THEN
        DISCH_THEN(MP_TAC o SPEC `chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)`) THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM mfd_scalar; GSYM RFA_SH_RICN2_EQ] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) x /\ &0 < mfd_scalar atlas g x0`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN USE_THEN "Rpos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "max" (MP_TAC o SPEC `x:A`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "q0" MP_TAC THEN
    ABBREV_TAC `Q = rfs_ric_norm2 atlas (g:A->real^3^3) x` THEN
    ABBREV_TAC `R = mfd_scalar atlas (g:A->real^3^3) x` THEN
    ABBREV_TAC `Q0 = rfs_ric_norm2 atlas (g:A->real^3^3) x0` THEN
    ABBREV_TAC `R0 = mfd_scalar atlas (g:A->real^3^3) x0` THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `Q * R0 pow 2 <= Q0 * R pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC RFA_SH_DIV_LE THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `R0 pow 2 * (&3 * Q) <= R0 pow 2 * R pow 2` MP_TAC THENL
     [SUBGOAL_THEN `(&3 * Q0) * R pow 2 = R0 pow 2 * R pow 2` MP_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `Q * R0 pow 2 <= Q0 * R pow 2` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_POW_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`]
                RFA_SH_EINSTEIN_ALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "einc")] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`]
                RFA_SH_SCAL_CONST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "const")] THEN
  EXISTS_TAC `mfd_scalar atlas (g:A->real^3^3) x0 / &6` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> &0 < x / &6`) THEN
    USE_THEN "Rpos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "const" (MP_TAC o SPECL [`x0:A`; `x:A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[mfd_sectional; mfd_scalar] THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                        (FST(chart_at atlas x))`;
                 `metric_local atlas (chart_at atlas (x:A)) (g:A->real^3^3)`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) x`]
                RFA_SH_SEC_EINSTEIN) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)` THEN
      REWRITE_TAC[riemannian_metric] THEN
      DISCH_THEN(MP_TAC o SPEC `chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)`) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      USE_THEN "einc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* The statement P2B_REQ_RFA_SHRINKER_ROUND_STATEMENT reduces to its 2-d    *)
(* clause.                                                                  *)

let RFA_P2B_REQ_SHRINKER_ROUND_2D_ONLY = prove
 (`!w:B->bool.
     P2B_REQ_RFA_SHRINKER_ROUND_STATEMENT w <=>
     (!top atlas g f.
        hausdorff_space top /\ compact_space top /\ connected_space top /\
        p2b_shrinker (top,atlas:((B->bool)#(B->real^2))->bool) g f /\
        (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                 ==> &0 < mfd_sectional atlas g x u v)
        ==> p2b_round (top,atlas) g)`,
  GEN_TAC THEN REWRITE_TAC[P2B_REQ_RFA_SHRINKER_ROUND_STATEMENT] THEN
  MATCH_MP_TAC(TAUT `p ==> (p /\ q <=> q)`) THEN
  MATCH_ACCEPT_TAC RFA_SHRINKER_ROUND_3D);;

