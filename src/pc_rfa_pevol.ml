(* ========================================================================= *)
(* Unit pc_rfa_pevol: evolution of the Ricci tensor under a local Ricci flow *)
(* (RFA_LRICCI_EVOLUTION: d/dt Ric = Lap Ric + 2 Rm(Ric) - 2 Ric^2) and, in  *)
(* dimension 3, its explicit form (RFA_LRICCI_EVOLUTION_3D) and the          *)
(* curvature operator P = (R/2) g - Ric, whose values at unit normals are    *)
(* the sectional curvatures (RFA_LSECTIONAL_PCURV_3D).                       *)
(* ========================================================================= *)

needs "src/pc_rfa_rmevol.ml";;

prioritize_real();;
type_invention_error := true;;


(* ========================================================================= *)
(* Contractions of Rm against Ric and their symmetries.                      *)
(* ========================================================================= *)

let RFA_SUM2_GINV_SWAP = prove
 (`!U (G:real^N->real^N^N) y (f:num->num->real).
     metric_field U G /\ y IN U
     ==> sum(1..dimindex(:N)) (\k. sum(1..dimindex(:N))
           (\l. matrix_inv(G y)$k$l * f k l)) =
         sum(1..dimindex(:N)) (\k. sum(1..dimindex(:N))
           (\l. matrix_inv(G y)$k$l * f l k))`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN
  BETA_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC LRG_MATRIX_INV_SYM THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

let RFA_RIC_SHARP = prove
 (`!U (G:real^N->real^N^N) y v z.
     metric_field U G /\ y IN U
     ==> sum(1..dimindex(:N))
          (\k. sum(1..dimindex(:N))
            (\l. matrix_inv(G y)$k$l *
                 (z dot (G y ** lriemann G y v (basis k) (basis l))))) =
         lricci G y z v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!k l. z dot ((G:real^N->real^N^N) y ** lriemann G y v (basis k) (basis l)) =
          lrm4 G y (\m. if m = 1 then basis l else if m = 2 then z
                        else if m = 3 then basis k else v)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[lrm4] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `v:real^N`;
                   `basis k:real^N`; `basis l:real^N`; `z:real^N`] LRIEMANN_PAIR_SYM) THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `z:real^N`;
                   `basis l:real^N`; `basis k:real^N`; `v:real^N`]
           LRIEMANN_METRIC_ANTISYM) THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `basis l:real^N`;
                   `z:real^N`; `v:real^N`] LRIEMANN_ANTISYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_RNEG; DOT_RNEG] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `\k l. lrm4 (G:real^N->real^N^N) y
                          (\m. if m = 1 then basis l else if m = 2 then z
                               else if m = 3 then basis k else v)`] RFA_SUM2_GINV_SWAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC LRG_LRM4_CONTRACT13 THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

let RFA_SUM4_REARRANGE = prove
 (`!n (c:num->num->real) (d:num->num->real) (X:num->num->num->real) (Y:num->real).
     sum(1..n) (\k. sum(1..n) (\l. c k l *
        sum(1..n) (\a. sum(1..n) (\b. d a b * X a k l * Y b)))) =
     sum(1..n) (\a. sum(1..n) (\b. d a b * Y b *
        sum(1..n) (\k. sum(1..n) (\l. c k l * X a k l))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o BINDER_CONV) [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REAL_ARITH_TAC);;

let RFA_RIC_SLOT2_EXPAND = prove
 (`!U (G:real^N->real^N^N) y w Z.
     metric_field U G /\ y IN U
     ==> lricci G y w Z =
         sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
           matrix_inv(G y)$a$b * (basis a dot (G y ** Z)) * lricci G y w (basis b)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`; `lric2 (G:real^N->real^N^N)`;
                 `y:real^N`; `2`; `\m:num. (w:real^N)`; `Z:real^N`] RFA_METRIC_EXPAND) THEN
  ASM_SIMP_TAC[LRG_LRIC2_FIELD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[lric2] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let RFA_RIC_SLOT1_EXPAND = prove
 (`!U (G:real^N->real^N^N) y w Z.
     metric_field U G /\ y IN U
     ==> lricci G y Z w =
         sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
           matrix_inv(G y)$a$b * (basis a dot (G y ** Z)) * lricci G y (basis b) w))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`; `lric2 (G:real^N->real^N^N)`;
                 `y:real^N`; `1`; `\m:num. (w:real^N)`; `Z:real^N`] RFA_METRIC_EXPAND) THEN
  ASM_SIMP_TAC[LRG_LRIC2_FIELD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[lric2] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let RFA_RIC_RIEM_SLOT2 = prove
 (`!U (G:real^N->real^N^N) y v w.
     metric_field U G /\ y IN U
     ==> sum(1..dimindex(:N)) (\k. sum(1..dimindex(:N)) (\l.
           matrix_inv(G y)$k$l * lricci G y w (lriemann G y v (basis k) (basis l)))) =
         sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
           matrix_inv(G y)$p$q * lricci G y w (basis p) * lricci G y (basis q) v))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `w:real^N`]
                RFA_RIC_SLOT2_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC
    (LAND_CONV o BINDER_CONV o BINDER_CONV o RAND_CONV) [th]) THEN
  MP_TAC(ISPECL [`dimindex(:N)`; `\k l. matrix_inv((G:real^N->real^N^N) y)$k$l`;
                 `\a b. matrix_inv((G:real^N->real^N^N) y)$a$b`;
                 `\a k l. basis a dot ((G:real^N->real^N^N) y **
                                       lriemann G y v (basis k) (basis l))`;
                 `\b. lricci (G:real^N->real^N^N) y w (basis b)`] RFA_SUM4_REARRANGE) THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `v:real^N`]
                RFA_RIC_SHARP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `\a b. lricci (G:real^N->real^N^N) y w (basis b) * lricci G y (basis a) v`]
         RFA_SUM2_GINV_SWAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_MUL_ASSOC]);;

let RFA_RIC_RIEM_SLOT1 = prove
 (`!U (G:real^N->real^N^N) y v w.
     metric_field U G /\ y IN U
     ==> sum(1..dimindex(:N)) (\k. sum(1..dimindex(:N)) (\l.
           matrix_inv(G y)$k$l * lricci G y (lriemann G y v (basis k) w) (basis l))) =
         --(sum(1..dimindex(:N)) (\k. sum(1..dimindex(:N)) (\l.
              sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
                matrix_inv(G y)$k$l * matrix_inv(G y)$p$q *
                lrm4 G y (\m. if m = 1 then basis k else if m = 2 then v
                              else if m = 3 then basis p else w) *
                lricci G y (basis l) (basis q))))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
                RFA_RIC_SLOT1_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC
    (LAND_CONV o BINDER_CONV o BINDER_CONV o RAND_CONV) [th]) THEN
  REWRITE_TAC[GSYM SUM_NEG; GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[lrm4] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `basis k:real^N`;
                 `v:real^N`; `w:real^N`] LRIEMANN_ANTISYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `basis q:real^N`;
                 `basis l:real^N`] LRICCI_SYM) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RNEG; DOT_RNEG] THEN REAL_ARITH_TAC);;

let RFA_SUM4_PAIRSWAP = prove
 (`!n (FF:num->num->num->num->real).
     sum(1..n) (\k. sum(1..n) (\l. sum(1..n) (\p. sum(1..n) (\q. FF k l p q)))) =
     sum(1..n) (\k. sum(1..n) (\l. sum(1..n) (\p. sum(1..n) (\q. FF p q k l))))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o BINDER_CONV) [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN
  REFL_TAC);;

let RFA_RMRIC_SYM = prove
 (`!U (G:real^N->real^N^N) y v w.
     metric_field U G /\ y IN U
     ==> sum(1..dimindex(:N)) (\k. sum(1..dimindex(:N)) (\l.
           sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
             matrix_inv(G y)$k$l * matrix_inv(G y)$p$q *
             lrm4 G y (\m. if m = 1 then basis k else if m = 2 then w
                           else if m = 3 then basis p else v) *
             lricci G y (basis l) (basis q))))) =
         sum(1..dimindex(:N)) (\k. sum(1..dimindex(:N)) (\l.
           sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
             matrix_inv(G y)$k$l * matrix_inv(G y)$p$q *
             lrm4 G y (\m. if m = 1 then basis k else if m = 2 then v
                           else if m = 3 then basis p else w) *
             lricci G y (basis l) (basis q)))))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [RFA_SUM4_PAIRSWAP] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[lrm4] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `basis p:real^N`;
                 `w:real^N`; `v:real^N`; `basis k:real^N`] LRIEMANN_PAIR_SYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `basis q:real^N`;
                 `basis l:real^N`] LRICCI_SYM) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REAL_ARITH_TAC);;

let RFA_RIC2_SYM = prove
 (`!U (G:real^N->real^N^N) y v w.
     metric_field U G /\ y IN U
     ==> sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
           matrix_inv(G y)$p$q * lricci G y w (basis p) * lricci G y (basis q) v)) =
         sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
           matrix_inv(G y)$p$q * lricci G y v (basis p) * lricci G y (basis q) w))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `\p q. lricci (G:real^N->real^N^N) y w (basis p) * lricci G y (basis q) v`]
         RFA_SUM2_GINV_SWAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `w:real^N`;
                 `basis q:real^N`] LRICCI_SYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `basis p:real^N`;
                 `v:real^N`] LRICCI_SYM) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN REAL_ARITH_TAC);;


(* ========================================================================= *)
(* Traces and commutators of nabla^2 Ric.                                    *)
(* ========================================================================= *)

let RFA_DSCAL_LNABLA0 = prove
 (`!(G:real^N->real^N^N) z u.
     lnabla 0 G (\x u. lscalar G x) z u =
     drop(frechet_derivative (\x. lift(lscalar G x)) (at z) (u 1))`,
  REWRITE_TAC[LRG_LNABLA_EQ; ADD_CLAUSES; SUM_CLAUSES_NUMSEG; ARITH; REAL_SUB_RZERO]);;

(* The three traces of nabla^2 Ric that occur in d/dt Ric.                *)

let RFA_N3_TRACE12 = prove
 (`!U (G:real^N->real^N^N) y z1 z2.
     metric_field U G /\ y IN U
     ==> sum(1..dimindex(:N)) (\k. sum(1..dimindex(:N)) (\l. matrix_inv(G y)$k$l *
           lnabla 3 G (lnabla 2 G (lric2 G)) y
             (\m. if m = 1 then basis k else if m = 2 then basis l
                  else if m = 3 then z1 else z2))) =
         lnabla 1 G (lnabla 0 G (\x u. lscalar G x)) y
           (\m. if m = 1 then z1 else z2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`1`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lnabla 2 (G:real^N->real^N^N) (lric2 G)`; `1`; `2`; `y:real^N`;
                 `\m:num. if m = 1 then z1:real^N else z2`] RFA_LNABLA_CTR_AT) THEN
  ASM_SIMP_TAC[LRG_N2_FIELD; ARITH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b. matrix_inv((G:real^N->real^N^N) y)$a$b *
      lnabla 3 G (lnabla 2 G (lric2 G)) y
        (rfa_ins 1 2 (basis a) (basis b) (\m. if m = 1 then z1 else z2))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC RFA_N3_AGREE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[rfa_ins] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `m = 1 \/ m = 2 \/ m = 3 \/ m = 4` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`z:real^N`; `w:num->real^N`] THEN
  DISCH_TAC THEN REWRITE_TAC[RFA_DSCAL_LNABLA0] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`; `w:num->real^N`]
         LRG_DSCALAR_CONTRACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  AP_TERM_TAC THEN MATCH_MP_TAC RFA_N2_AGREE THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[rfa_ins] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `m = 1 \/ m = 2 \/ m = 3` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let RFA_DSCAL_DIFFERENTIABLE = prove
 (`!U (G:real^N->real^N^N) y u.
     metric_field U G /\ y IN U
     ==> (\x. lift(lnabla 0 G (\x u. lscalar G x) x u)) differentiable at y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RFA_DSCAL_LNABLA0; LIFT_DROP] THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN
  ASM_SIMP_TAC[LRG_LSCALAR_SMOOTH]);;

let RFA_N3_TRACE13 = prove
 (`!U (G:real^N->real^N^N) y z1 z2.
     metric_field U G /\ y IN U
     ==> sum(1..dimindex(:N)) (\k. sum(1..dimindex(:N)) (\l. matrix_inv(G y)$k$l *
           lnabla 3 G (lnabla 2 G (lric2 G)) y
             (\m. if m = 1 then basis k else if m = 2 then z1
                  else if m = 3 then basis l else z2))) =
         inv(&2) * lnabla 1 G (lnabla 0 G (\x u. lscalar G x)) y
                     (\m. if m = 1 then z1 else z2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`1`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lnabla 2 (G:real^N->real^N^N) (lric2 G)`; `1`; `3`; `y:real^N`;
                 `\m:num. if m = 1 then z1:real^N else z2`] RFA_LNABLA_CTR_AT) THEN
  ASM_SIMP_TAC[LRG_N2_FIELD; ARITH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b. matrix_inv((G:real^N->real^N^N) y)$a$b *
      lnabla 3 G (lnabla 2 G (lric2 G)) y
        (rfa_ins 1 3 (basis a) (basis b) (\m. if m = 1 then z1 else z2))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC RFA_N3_AGREE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[rfa_ins] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `m = 1 \/ m = 2 \/ m = 3 \/ m = 4` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lnabla 1 (G:real^N->real^N^N)
                (\z w. inv(&2) * lnabla 0 G (\x u. lscalar G x) z w) y
                (\m. if m = 1 then z1 else z2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`z:real^N`; `w:num->real^N`] THEN
    DISCH_TAC THEN REWRITE_TAC[RFA_DSCAL_LNABLA0] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`;
                   `(w:num->real^N) 1`] LRG_CONTRACTED_BIANCHI) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC RFA_N2_AGREE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[rfa_ins] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `m = 1 \/ m = 2 \/ m = 3` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  MATCH_MP_TAC LRG_LNABLA_CMUL THEN
  MATCH_MP_TAC RFA_DSCAL_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

let RFA_N3_TRACE23 = prove
 (`!U (G:real^N->real^N^N) y z1 z2.
     metric_field U G /\ y IN U
     ==> sum(1..dimindex(:N)) (\k. sum(1..dimindex(:N)) (\l. matrix_inv(G y)$k$l *
           lnabla 3 G (lnabla 2 G (lric2 G)) y
             (\m. if m = 1 then z1 else if m = 2 then basis k
                  else if m = 3 then basis l else z2))) =
         inv(&2) * lnabla 1 G (lnabla 0 G (\x u. lscalar G x)) y
                     (\m. if m = 1 then z1 else z2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`1`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lnabla 2 (G:real^N->real^N^N) (lric2 G)`; `2`; `3`; `y:real^N`;
                 `\m:num. if m = 1 then z1:real^N else z2`] RFA_LNABLA_CTR_AT) THEN
  ASM_SIMP_TAC[LRG_N2_FIELD; ARITH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b. matrix_inv((G:real^N->real^N^N) y)$a$b *
      lnabla 3 G (lnabla 2 G (lric2 G)) y
        (rfa_ins 2 3 (basis a) (basis b) (\m. if m = 1 then z1 else z2))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC RFA_N3_AGREE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[rfa_ins] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `m = 1 \/ m = 2 \/ m = 3 \/ m = 4` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lnabla 1 (G:real^N->real^N^N)
                (\z w. inv(&2) * lnabla 0 G (\x u. lscalar G x) z w) y
                (\m. if m = 1 then z1 else z2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`z:real^N`; `w:num->real^N`] THEN
    DISCH_TAC THEN REWRITE_TAC[RFA_DSCAL_LNABLA0] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`;
                   `(w:num->real^N) 1`] LRG_CONTRACTED_BIANCHI) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
    AP_TERM_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`] LRG_N2_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
    MATCH_MP_TAC RFA_N2_AGREE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[rfa_ins] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `m = 1 \/ m = 2 \/ m = 3` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[swap] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  MATCH_MP_TAC LRG_LNABLA_CMUL THEN
  MATCH_MP_TAC RFA_DSCAL_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

let RFA_HESS_SCAL_SYM = prove
 (`!U (G:real^N->real^N^N) y z1 z2.
     metric_field U G /\ y IN U
     ==> lnabla 1 G (lnabla 0 G (\x u. lscalar G x)) y (\m. if m = 1 then z1 else z2) =
         lnabla 1 G (lnabla 0 G (\x u. lscalar G x)) y (\m. if m = 1 then z2 else z1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `ltensor_field 0 U (\x:real^N u:num->real^N. lscalar (G:real^N->real^N^N) x) /\
                (!u. smooth_map_on U (\x. lift((\x:real^N u:num->real^N. lscalar G x) x u)))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ltensor_field] THEN ASM_SIMP_TAC[LRG_LSCALAR_SMOOTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`0`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `\x:real^N u:num->real^N. lscalar (G:real^N->real^N^N) x`; `y:real^N`;
                 `\m:num. if m = 1 then z1:real^N else z2`] RFA_RICCI_IDENTITY) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH; RFA_LNABLA_ITER_2; ADD_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[REAL_SUB_0] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC LRG_LNABLA_AGREE THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`0`; `U:real^N->bool`; `G:real^N->real^N^N`;
                   `\x:real^N u:num->real^N. lscalar (G:real^N->real^N^N) x`]
           LNABLA_TENSOR_FIELD) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN SIMP_TAC[];
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `m = 1 \/ m = 2` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV]);;

let RFA_N3_COMM = prove
 (`!U (G:real^N->real^N^N) y z1 z2 z3 z4.
     metric_field U G /\ y IN U
     ==> lnabla 3 G (lnabla 2 G (lric2 G)) y
           (\m. if m = 1 then z1 else if m = 2 then z2 else if m = 3 then z3 else z4) =
         lnabla 3 G (lnabla 2 G (lric2 G)) y
           (\m. if m = 1 then z1 else if m = 2 then z2 else if m = 3 then z4 else z3) +
         lricci G y (lriemann G y z3 z4 z1) z2 + lricci G y z1 (lriemann G y z3 z4 z2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`; `lric2 (G:real^N->real^N^N)`;
                 `y:real^N`;
                 `\m:num. if m = 1 then z1:real^N else if m = 2 then z2
                          else if m = 3 then z3 else z4`] RFA_RICCI_IDENTITY) THEN
  ASM_SIMP_TAC[LRG_LRIC2_FIELD] THEN
  REWRITE_TAC[RFA_LNABLA_ITER_2; ARITH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SUM_2; lric2] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC(REAL_ARITH `b = b' ==> a - b = c ==> a = b' + c`) THEN
  MATCH_MP_TAC RFA_N3_AGREE THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `m = 1 \/ m = 2 \/ m = 3 \/ m = 4` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let RFA_N3_LTLAP = prove
 (`!U (G:real^N->real^N^N) y v w.
     metric_field U G /\ y IN U
     ==> sum(1..dimindex(:N)) (\k. sum(1..dimindex(:N)) (\l. matrix_inv(G y)$k$l *
           lnabla 3 G (lnabla 2 G (lric2 G)) y
             (\m. if m = 1 then v else if m = 2 then w
                  else if m = 3 then basis l else basis k))) =
         ltlap 2 G (lric2 G) y (\m. if m = 1 then v else w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `\k l. lnabla 3 (G:real^N->real^N^N) (lnabla 2 G (lric2 G)) y
                          (\m. if m = 1 then v else if m = 2 then w
                               else if m = 3 then basis k else basis l)`]
         RFA_SUM2_GINV_SWAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[ltlap; RFA_LNABLA_ITER_2; ARITH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  AP_TERM_TAC THEN MATCH_MP_TAC RFA_N3_AGREE THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `m = 1 \/ m = 2 \/ m = 3 \/ m = 4` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;


(* ========================================================================= *)
(* The evolution of the Ricci tensor (RFA_LRICCI_EVOLUTION).                 *)
(* ========================================================================= *)

let RFA_LRICCI_EVOLUTION = prove
 (`!U a b (G:real->real^N->real^N^N) t y v w.
        lricci_flow U a b G /\ a < t /\ t < b /\ y IN U
        ==> ((\s. lricci (G s) y v w) has_real_derivative
             ltlap 2 (G t) (lric2 (G t)) y (\m. if m = 1 then v else w) +
             &2 * sum(1..dimindex(:N))
                   (\k. sum(1..dimindex(:N))
                     (\l. sum(1..dimindex(:N))
                       (\p. sum(1..dimindex(:N))
                         (\q. matrix_inv(G t y)$k$l * matrix_inv(G t y)$p$q *
                              lrm4 (G t) y
                                (\m. if m = 1 then basis k else if m = 2 then v
                                     else if m = 3 then basis p else w) *
                              lricci (G t) y (basis l) (basis q))))) -
             &2 * sum(1..dimindex(:N))
                   (\p. sum(1..dimindex(:N))
                     (\q. matrix_inv(G t y)$p$q * lricci (G t) y v (basis p) *
                          lricci (G t) y (basis q) w))) (atreal t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_FLOW_BASIC]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `t:real`; `y:real^N`; `v:real^N`; `w:real^N`] LRG_FLOW_DRICCI) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[]
   `(x:real) = y ==> (f has_real_derivative x) net ==> (f has_real_derivative y) net`) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `t:real`; `y:real^N`] LRG_FLOW_NQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ABBREV_TAC `G0 = (G:real->real^N->real^N^N) t` THEN
  SUBGOAL_THEN
   `!k l. lnabla 3 (G0:real^N->real^N^N) (lnabla 2 G0 (lric2 G0)) (y:real^N)
            (\m. if m = 1 then (w:real^N) else if m = 2 then basis l
                 else if m = 3 then (v:real^N) else basis k) =
          lnabla 3 G0 (lnabla 2 G0 (lric2 G0)) y
            (\m. if m = 1 then w else if m = 2 then basis l
                 else if m = 3 then basis k else v) +
          lricci G0 y (lriemann G0 y v (basis k) w) (basis l) +
          lricci G0 y w (lriemann G0 y v (basis k) (basis l)) /\
          lnabla 3 G0 (lnabla 2 G0 (lric2 G0)) y
            (\m. if m = 1 then v else if m = 2 then basis l
                 else if m = 3 then w else basis k) =
          lnabla 3 G0 (lnabla 2 G0 (lric2 G0)) y
            (\m. if m = 1 then v else if m = 2 then basis l
                 else if m = 3 then basis k else w) +
          lricci G0 y (lriemann G0 y w (basis k) v) (basis l) +
          lricci G0 y v (lriemann G0 y w (basis k) (basis l))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`U:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`; `w:real^N`;
                     `basis l:real^N`; `v:real^N`; `basis k:real^N`] RFA_N3_COMM);
      MP_TAC(ISPECL [`U:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`; `v:real^N`;
                     `basis l:real^N`; `w:real^N`; `basis k:real^N`] RFA_N3_COMM)] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH
   `--((x1 + a1 + b1) + (x2 + a2 + b2) - c) -
    --(x1 + d - e) =
    --a1 + --b1 + --(x2 + a2 + b2) + c + d - e`] THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_SUB_LDISTRIB; REAL_MUL_RNEG] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG; SUM_SUB_NUMSEG; SUM_NEG] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N)) (\k. sum(1..dimindex(:N)) (\l. matrix_inv((G0:real^N->real^N^N) y)$k$l *
      lnabla 3 G0 (lnabla 2 G0 (lric2 G0)) y
        (\m. if m = 1 then v else if m = 2 then basis l
             else if m = 3 then basis k else w))) =
    inv(&2) * lnabla 1 G0 (lnabla 0 G0 (\x u. lscalar G0 x)) y
                (\m. if m = 1 then v else w)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`;
                   `\k l. lnabla 3 (G0:real^N->real^N^N) (lnabla 2 G0 (lric2 G0)) y
                            (\m. if m = 1 then v else if m = 2 then basis k
                                 else if m = 3 then basis l else w)`]
           RFA_SUM2_GINV_SWAP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC RFA_N3_TRACE23 THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`; `v:real^N`;
                 `w:real^N`] RFA_RIC_RIEM_SLOT1) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`; `w:real^N`;
                 `v:real^N`] RFA_RIC_RIEM_SLOT1) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`; `v:real^N`;
                 `w:real^N`] RFA_RIC_RIEM_SLOT2) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`; `w:real^N`;
                 `v:real^N`] RFA_RIC_RIEM_SLOT2) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`; `v:real^N`;
                 `w:real^N`] RFA_N3_LTLAP) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`; `w:real^N`;
                 `v:real^N`] RFA_N3_TRACE12) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`; `w:real^N`;
                 `v:real^N`] RFA_N3_TRACE13) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`; `v:real^N`;
                 `w:real^N`] RFA_HESS_SCAL_SYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`; `v:real^N`;
                 `w:real^N`] RFA_RMRIC_SYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`; `v:real^N`;
                 `w:real^N`] RFA_RIC2_SYM) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN REAL_ARITH_TAC);;


(* ========================================================================= *)
(* G-orthonormal frames: expansions, traces, eigenframe of Ric.              *)
(* ========================================================================= *)

let RFA_FRAME_SGS = prove
 (`!(G0:real^N^N) (S:real^N^N).
     invertible G0 /\ invertible S /\ matrix_inv G0 = transp S ** S
     ==> S ** G0 ** transp S = mat 1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `G0 = matrix_inv(S:real^N^N) ** transp(matrix_inv S)` SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `matrix_inv(matrix_inv(G0:real^N^N))` THEN
    CONJ_TAC THENL [REWRITE_TAC[MATRIX_INV_INV]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[MATRIX_INV_MUL; INVERTIBLE_TRANSP; MATRIX_INV_TRANSP];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_MUL_ASSOC] THEN
  ASM_SIMP_TAC[MATRIX_INV; MATRIX_MUL_LID] THEN
  REWRITE_TAC[GSYM MATRIX_TRANSP_MUL] THEN
  ASM_SIMP_TAC[MATRIX_INV; TRANSP_MAT]);;

let RFA_GFRAME_ORTHO = prove
 (`!(G0:real^N^N) (S:real^N^N) i j.
     invertible G0 /\ invertible S /\ matrix_inv G0 = transp S ** S /\
     1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
     ==> (transp S ** basis i) dot (G0 ** (transp S ** basis j)) =
         if i = j then &1 else &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; GSYM MATRIX_MUL_ASSOC] THEN
  MP_TAC(ISPECL [`G0:real^N^N`; `S:real^N^N`] RFA_FRAME_SGS) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[MATRIX_MUL_ASSOC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LID] THEN
  ASM_SIMP_TAC[DOT_BASIS_BASIS]);;

let RFA_FRAME_EXPAND = prove
 (`!k U (G:real^N->real^N^N) tf y (S:real^N^N) w.
     metric_field U G /\ ltensor_field k U tf /\ y IN U /\ invertible S /\
     matrix_inv(G y) = transp S ** S
     ==> tf y w =
         sum (index_tuples k (:N))
           (\i. product(1..k) (\m. (transp S ** basis(i m)) dot (G y ** w m)) *
                tf y (\m. transp S ** basis(i m)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `invertible((G:real^N->real^N^N) y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  ABBREV_TAC `tf' = \z:real^N u:num->real^N.
                      (tf:real^N->(num->real^N)->real) y (\m. transp (S:real^N^N) ** u m)` THEN
  SUBGOAL_THEN `ltensor_field k U (tf':real^N->(num->real^N)->real)` ASSUME_TAC THENL
   [UNDISCH_TAC `ltensor_field k U (tf:real^N->(num->real^N)->real)` THEN
    REWRITE_TAC[ltensor_field] THEN DISCH_TAC THEN X_GEN_TAC `z:real^N` THEN
    DISCH_TAC THEN EXPAND_TAC "tf'" THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `(\v. lift((tf:real^N->(num->real^N)->real) y
                (\m. transp (S:real^N^N) ** (if m = i then v else u m)))) =
      (\v. lift(tf y (\j. if j = i then v else (\m. transp S ** u m) j))) o
      (\v:real^N. transp S ** v)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `v:real^N` THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
      X_GEN_TAC `j:num` THEN COND_CASES_TAC THEN REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC LINEAR_COMPOSE THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `tf':real^N->(num->real^N)->real`;
                 `y:real^N`] LRG_TENSOR_FIELD_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `\m. (S:real^N^N) ** (G:real^N->real^N^N) y ** (w:num->real^N) m`) THEN
  EXPAND_TAC "tf'" THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\m. transp S ** (S:real^N^N) ** (G:real^N->real^N^N) y ** (w:num->real^N) m) = w`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `m:num` THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
    FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM th] THEN ASSUME_TAC th) THEN
    ASM_SIMP_TAC[MATRIX_INV; MATRIX_VECTOR_MUL_LID] THEN
    UNDISCH_TAC `matrix_inv((G:real^N->real^N^N) y) = transp (S:real^N^N) ** S` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[MATRIX_INV; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num->num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`i:num->num`; `k:num`; `m:num`] LRG_INDEX_TUPLES_RANGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM DOT_BASIS] THEN REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL] THEN
  REWRITE_TAC[DOT_SYM; MATRIX_VECTOR_MUL_ASSOC]);;

let RFA_LINEAR_SUM_EXPAND = prove
 (`!(f:real^N->real) (s:A->bool) (c:A->real) (u:A->real^N).
     linear (\x. lift(f x)) /\ FINITE s
     ==> f (vsum s (\a. c a % u a)) = sum s (\a. c a * f (u a))`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM LIFT_EQ] THEN REWRITE_TAC[LIFT_SUM; o_DEF] THEN
  MP_TAC(ISPECL [`\x:real^N. lift((f:real^N->real) x)`; `\a:A. (c:A->real) a % (u:A->real^N) a`;
                 `s:A->bool`] LINEAR_VSUM) THEN
  ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `a:A` THEN DISCH_TAC THEN BETA_TAC THEN
  REWRITE_TAC[LIFT_CMUL] THEN
  MP_TAC(ISPECL [`\x:real^N. lift((f:real^N->real) x)`; `(c:A->real) a`; `(u:A->real^N) a`]
         LINEAR_CMUL) THEN
  ASM_REWRITE_TAC[]);;

let RFA_FRAME_VEXPAND = prove
 (`!(G0:real^N^N) (S:real^N^N) v.
     invertible G0 /\ invertible S /\ matrix_inv G0 = transp S ** S
     ==> v = vsum(1..dimindex(:N))
               (\r. ((transp S ** basis r) dot (G0 ** v)) % (transp S ** basis r))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `transp (S:real^N^N) **
              vsum(1..dimindex(:N)) (\r. ((S ** (G0:real^N^N) ** v)$r) % basis r)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BASIS_EXPANSION; MATRIX_VECTOR_MUL_ASSOC; MATRIX_MUL_ASSOC] THEN
    UNDISCH_TAC `matrix_inv (G0:real^N^N) = transp (S:real^N^N) ** S` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[MATRIX_INV; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^N. transp (S:real^N^N) ** x`;
                 `\r. (((S:real^N^N) ** (G0:real^N^N) ** (v:real^N))$r) % (basis r:real^N)`;
                 `1..dimindex(:N)`] LINEAR_VSUM) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR; FINITE_NUMSEG; o_DEF] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL] THEN ASM_SIMP_TAC[DOT_BASIS] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC]);;

let RFA_TRANSP_BASIS_EXPAND = prove
 (`!(S:real^N^N) s.
     1 <= s /\ s <= dimindex(:N)
     ==> transp S ** basis s = vsum(1..dimindex(:N)) (\p. S$s$p % basis p)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM BASIS_EXPANSION] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_BASIS; column; transp; LAMBDA_BETA]);;

let RFA_TRACE_FRAME = prove
 (`!(G0:real^N^N) (S:real^N^N) (B:real^N->real^N->real).
     matrix_inv G0 = transp S ** S /\
     (!z. linear (\x. lift(B x z))) /\ (!x. linear (\z. lift(B x z)))
     ==> sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
           matrix_inv G0$p$q * B (basis p) (basis q))) =
         sum(1..dimindex(:N)) (\s. B (transp S ** basis s) (transp S ** basis s))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
                sum(1..dimindex(:N)) (\s. (S:real^N^N)$s$p * S$s$q) *
                (B:real^N->real^N->real) (basis p) (basis q)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN BETA_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[matrix_mul; transp; LAMBDA_BETA];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_RMUL] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `s:num` THEN STRIP_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[RFA_TRANSP_BASIS_EXPAND] THEN
  MP_TAC(ISPECL [`\x:real^N. (B:real^N->real^N->real) x
                   (vsum(1..dimindex(:N)) (\q. (S:real^N^N)$s$q % basis q))`;
                 `1..dimindex(:N)`; `\p. (S:real^N^N)$s$p`; `\p. basis p:real^N`]
         RFA_LINEAR_SUM_EXPAND) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MP_TAC(ISPECL [`\z:real^N. (B:real^N->real^N->real) (basis p) z`;
                 `1..dimindex(:N)`; `\q. (S:real^N^N)$s$q`; `\q. basis q:real^N`]
         RFA_LINEAR_SUM_EXPAND) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `q:num` THEN STRIP_TAC THEN BETA_TAC THEN REAL_ARITH_TAC);;

let RFA_BILIN_FRAME = prove
 (`!(G0:real^N^N) (S:real^N^N) (B:real^N->real^N->real) v w.
     invertible G0 /\ invertible S /\ matrix_inv G0 = transp S ** S /\
     (!z. linear (\x. lift(B x z))) /\ (!x. linear (\z. lift(B x z)))
     ==> B v w =
         sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
           ((transp S ** basis a) dot (G0 ** v)) * ((transp S ** basis b) dot (G0 ** w)) *
           B (transp S ** basis a) (transp S ** basis b)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G0:real^N^N`; `S:real^N^N`; `v:real^N`] RFA_FRAME_VEXPAND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [th]) THEN
  MP_TAC(ISPECL [`\x:real^N. (B:real^N->real^N->real) x w`; `1..dimindex(:N)`;
                 `\r. (transp (S:real^N^N) ** basis r) dot ((G0:real^N^N) ** v)`;
                 `\r. transp (S:real^N^N) ** basis r`] RFA_LINEAR_SUM_EXPAND) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MP_TAC(ISPECL [`G0:real^N^N`; `S:real^N^N`; `w:real^N`] RFA_FRAME_VEXPAND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [th]) THEN
  MP_TAC(ISPECL [`\z:real^N. (B:real^N->real^N->real) (transp (S:real^N^N) ** basis a) z`;
                 `1..dimindex(:N)`;
                 `\r. (transp (S:real^N^N) ** basis r) dot ((G0:real^N^N) ** w)`;
                 `\r. transp (S:real^N^N) ** basis r`] RFA_LINEAR_SUM_EXPAND) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN REAL_ARITH_TAC);;

let RFA_BASIS_MUL_EXPAND = prove
 (`!(P:real^N^N) i. 1 <= i /\ i <= dimindex(:N)
     ==> P ** basis i = vsum(1..dimindex(:N)) (\a. P$a$i % basis a)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM BASIS_EXPANSION] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_BASIS; column; LAMBDA_BETA]);;

let RFA_TPMP_COMPONENT = prove
 (`!(P:real^N^N) (M:real^N^N) i j.
     1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
     ==> (transp P ** M ** P)$i$j =
         sum(1..dimindex(:N)) (\a. P$a$i * sum(1..dimindex(:N)) (\b. M$a$b * P$b$j))`,
  SIMP_TAC[matrix_mul; transp; LAMBDA_BETA]);;

let RFA_RIC_EIGENFRAME = prove
 (`!U (G:real^N->real^N^N) y.
     metric_field U G /\ y IN U
     ==> ?S:real^N^N. invertible S /\ matrix_inv(G y) = transp S ** S /\
             !i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
                   ~(i = j)
                   ==> lricci G y (transp S ** basis i) (transp S ** basis j) = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
         LRG_METRIC_INV_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S0:real^N^N` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `M = (lambda i j. lricci (G:real^N->real^N^N) y (transp (S0:real^N^N) ** basis i)
                                      (transp (S0:real^N^N) ** basis j)):real^N^N` THEN
  SUBGOAL_THEN `symmetric_matrix(M:real^N^N)` ASSUME_TAC THENL
   [REWRITE_TAC[symmetric_matrix] THEN EXPAND_TAC "M" THEN
    SIMP_TAC[CART_EQ; LAMBDA_BETA; TRANSP_COMPONENT] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC LRICCI_SYM THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SYMMETRIC_MATRIX_DIAGONALIZABLE_EXPLICIT) THEN
  DISCH_THEN(X_CHOOSE_THEN `P:real^N^N` (X_CHOOSE_THEN `d:num->real` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `transp (P:real^N^N) ** (S0:real^N^N)` THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[INVERTIBLE_MATRIX_MUL; INVERTIBLE_TRANSP; ORTHOGONAL_MATRIX_IMP_INVERTIBLE];
    ASM_REWRITE_TAC[MATRIX_TRANSP_MUL; TRANSP_TRANSP] THEN
    REWRITE_TAC[MATRIX_MUL_ASSOC] THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [GSYM MATRIX_MUL_ASSOC] THEN
    ASM_SIMP_TAC[ORTHOGONAL_MATRIX_TRANSP_RMUL; MATRIX_MUL_RID];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  REWRITE_TAC[MATRIX_TRANSP_MUL; TRANSP_TRANSP; GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[RFA_BASIS_MUL_EXPAND] THEN
  SUBGOAL_THEN
   `!c:num->real. transp (S0:real^N^N) ** vsum(1..dimindex(:N)) (\a. c a % basis a) =
                  vsum(1..dimindex(:N)) (\a. c a % (transp (S0:real^N^N) ** basis a))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`\x:real^N. transp (S0:real^N^N) ** x`;
                   `\a. (c:num->real) a % (basis a:real^N)`;
                   `1..dimindex(:N)`] LINEAR_VSUM) THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR; FINITE_NUMSEG; o_DEF] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_LRICCI_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^N. lricci (G:real^N->real^N^N) y x
                   (vsum(1..dimindex(:N)) (\a. (P:real^N^N)$a$j % (transp (S0:real^N^N) ** basis a)))`;
                 `1..dimindex(:N)`; `\a. (P:real^N^N)$a$i`;
                 `\a. transp (S0:real^N^N) ** basis a`] RFA_LINEAR_SUM_EXPAND) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `!a. lricci (G:real^N->real^N^N) y (transp (S0:real^N^N) ** basis a)
          (vsum(1..dimindex(:N)) (\b. (P:real^N^N)$b$j % (transp (S0:real^N^N) ** basis b))) =
        sum(1..dimindex(:N)) (\b. P$b$j * lricci G y (transp (S0:real^N^N) ** basis a)
                                                  (transp (S0:real^N^N) ** basis b))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`\z:real^N. lricci (G:real^N->real^N^N) y (transp (S0:real^N^N) ** basis a) z`;
                   `1..dimindex(:N)`; `\b. (P:real^N^N)$b$j`;
                   `\b. transp (S0:real^N^N) ** basis b`] RFA_LINEAR_SUM_EXPAND) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `(transp (P:real^N^N) ** (M:real^N^N) ** P)$i$j` THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`P:real^N^N`; `M:real^N^N`; `i:num`; `j:num`] RFA_TPMP_COMPONENT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
    EXPAND_TAC "M" THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[LAMBDA_BETA]]);;

let RFA_LIFT_DOT_GMUL_LINEAR = prove
 (`!(A:real^N^N) c. linear (\z. lift(c dot (A ** z)))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`\w:real^N. lift((c:real^N) dot w)`; `\z:real^N. (A:real^N^N) ** z`]
         LRG_LINEAR_COMPOSE_LAMBDA) THEN
  REWRITE_TAC[LINEAR_LIFT_DOT; MATRIX_VECTOR_MUL_LINEAR]);;

let RFA_LRM4_LINEAR = prove
 (`!U (G:real^N->real^N^N) y a b c d.
     metric_field U G /\ y IN U
     ==> linear (\x. lift(lrm4 G y (\m. if m = 1 then x else if m = 2 then b
                                         else if m = 3 then c else d))) /\
         linear (\x. lift(lrm4 G y (\m. if m = 1 then a else if m = 2 then x
                                         else if m = 3 then c else d))) /\
         linear (\x. lift(lrm4 G y (\m. if m = 1 then a else if m = 2 then b
                                         else if m = 3 then x else d))) /\
         linear (\x. lift(lrm4 G y (\m. if m = 1 then a else if m = 2 then b
                                         else if m = 3 then c else x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[lrm4] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRIEMANN_TRILINEAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`\z:real^N. lift((c:real^N) dot ((G:real^N->real^N^N) y ** z))`;
                   `\x:real^N. lriemann (G:real^N->real^N^N) y x b d`]
           LRG_LINEAR_COMPOSE_LAMBDA) THEN
    ASM_REWRITE_TAC[RFA_LIFT_DOT_GMUL_LINEAR];
    MP_TAC(ISPECL [`\z:real^N. lift((c:real^N) dot ((G:real^N->real^N^N) y ** z))`;
                   `\x:real^N. lriemann (G:real^N->real^N^N) y a x d`]
           LRG_LINEAR_COMPOSE_LAMBDA) THEN
    ASM_REWRITE_TAC[RFA_LIFT_DOT_GMUL_LINEAR];
    ONCE_REWRITE_TAC[DOT_SYM] THEN REWRITE_TAC[LINEAR_LIFT_DOT];
    MP_TAC(ISPECL [`\z:real^N. lift((c:real^N) dot ((G:real^N->real^N^N) y ** z))`;
                   `\x:real^N. lriemann (G:real^N->real^N^N) y a b x`]
           LRG_LINEAR_COMPOSE_LAMBDA) THEN
    ASM_REWRITE_TAC[RFA_LIFT_DOT_GMUL_LINEAR]]);;

let RFA_LIN_MUL_CONST = prove
 (`!(f:real^N->real) c. linear (\x. lift(f x)) ==> linear (\x. lift(f x * c))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[LIFT_CMUL] THEN
  MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN ASM_REWRITE_TAC[]);;

let RFA_LIN_CONST_MUL = prove
 (`!(f:real^N->real) c. linear (\x. lift(f x)) ==> linear (\x. lift(c * f x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_CMUL] THEN
  MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN ASM_REWRITE_TAC[]);;

let RFA_LINEAR_LIFT_SUM = prove
 (`!(f:A->real^N->real) s.
     FINITE s /\ (!i. i IN s ==> linear (\x. lift(f i x)))
     ==> linear (\x. lift(sum s (\i. f i x)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_SUM; o_DEF] THEN
  MP_TAC(ISPECL [`\i:A x:real^N. lift((f:A->real^N->real) i x)`; `s:A->bool`]
         LINEAR_COMPOSE_VSUM) THEN
  ASM_SIMP_TAC[]);;

let RFA_LINEAR_LIFT_ADD = prove
 (`!(f:real^N->real) g. linear (\x. lift(f x)) /\ linear (\x. lift(g x))
     ==> linear (\x. lift(f x + g x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_ADD] THEN
  MP_TAC(ISPECL [`\x:real^N. lift((f:real^N->real) x)`; `\x:real^N. lift((g:real^N->real) x)`]
         LINEAR_COMPOSE_ADD) THEN
  ASM_REWRITE_TAC[]);;

let RFA_LINEAR_LIFT_SUB = prove
 (`!(f:real^N->real) g. linear (\x. lift(f x)) /\ linear (\x. lift(g x))
     ==> linear (\x. lift(f x - g x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_SUB] THEN
  MP_TAC(ISPECL [`\x:real^N. lift((f:real^N->real) x)`; `\x:real^N. lift((g:real^N->real) x)`]
         LINEAR_COMPOSE_SUB) THEN
  ASM_REWRITE_TAC[]);;

let RFA_SCAL_FRAME = prove
 (`!U (G:real^N->real^N^N) y (S:real^N^N).
     metric_field U G /\ y IN U /\ matrix_inv(G y) = transp S ** S
     ==> lscalar G y =
         sum(1..dimindex(:N)) (\s. lricci G y (transp S ** basis s) (transp S ** basis s))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lscalar] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_LRICCI_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `S:real^N^N`;
                 `\x z. lricci (G:real^N->real^N^N) y x z`] RFA_TRACE_FRAME) THEN
  ASM_REWRITE_TAC[]);;

let RFA_RIC2_FRAME = prove
 (`!U (G:real^N->real^N^N) y (S:real^N^N) v w.
     metric_field U G /\ y IN U /\ matrix_inv(G y) = transp S ** S
     ==> sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
           matrix_inv(G y)$p$q * lricci G y v (basis p) * lricci G y (basis q) w)) =
         sum(1..dimindex(:N)) (\s. lricci G y v (transp S ** basis s) *
                                   lricci G y (transp S ** basis s) w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_LRICCI_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `S:real^N^N`;
                 `\x z. lricci (G:real^N->real^N^N) y v x * lricci G y z w`]
         RFA_TRACE_FRAME) THEN
  ASM_SIMP_TAC[RFA_LIN_MUL_CONST; RFA_LIN_CONST_MUL]);;

let RFA_RIC_FRAME_RM = prove
 (`!U (G:real^N->real^N^N) y (S:real^N^N) p q.
     metric_field U G /\ y IN U /\ matrix_inv(G y) = transp S ** S
     ==> lricci G y p q =
         sum(1..dimindex(:N)) (\s. lrm4 G y
           (\m. if m = 1 then transp S ** basis s else if m = 2 then p
                else if m = 3 then transp S ** basis s else q))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `p:real^N`;
                 `q:real^N`] LRG_LRM4_CONTRACT13) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] RFA_LRM4_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `S:real^N^N`;
                 `\x z. lrm4 (G:real^N->real^N^N) y
                          (\m. if m = 1 then x else if m = 2 then p
                               else if m = 3 then z else q)`] RFA_TRACE_FRAME) THEN
  ASM_REWRITE_TAC[]);;

let RFA_RICNORM_FRAME = prove
 (`!U (G:real^N->real^N^N) y (S:real^N^N).
     metric_field U G /\ y IN U /\ matrix_inv(G y) = transp S ** S
     ==> ltnorm2 2 G (lric2 G) y =
         sum(1..dimindex(:N)) (\r. sum(1..dimindex(:N)) (\s.
           lricci G y (transp S ** basis r) (transp S ** basis s) pow 2))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`; `lric2 (G:real^N->real^N^N)`;
                 `y:real^N`; `S:real^N^N`] LRG_LTNORM2_SQUARES) THEN
  ASM_SIMP_TAC[LRG_LRIC2_FIELD] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[LRG_SUM_INDEX_TUPLES_2; lric2] THEN CONV_TAC NUM_REDUCE_CONV);;

let RFA_T_FRAME = prove
 (`!U (G:real^N->real^N^N) y (S:real^N^N) v w.
     metric_field U G /\ y IN U /\ matrix_inv(G y) = transp S ** S
     ==> sum(1..dimindex(:N)) (\k. sum(1..dimindex(:N)) (\l.
           sum(1..dimindex(:N)) (\p. sum(1..dimindex(:N)) (\q.
             matrix_inv(G y)$k$l * matrix_inv(G y)$p$q *
             lrm4 G y (\m. if m = 1 then basis k else if m = 2 then v
                           else if m = 3 then basis p else w) *
             lricci G y (basis l) (basis q))))) =
         sum(1..dimindex(:N)) (\s. sum(1..dimindex(:N)) (\r.
           lrm4 G y (\m. if m = 1 then transp S ** basis r else if m = 2 then v
                         else if m = 3 then transp S ** basis s else w) *
           lricci G y (transp S ** basis r) (transp S ** basis s)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] RFA_LRM4_LINEAR) THEN
  REWRITE_TAC[ASSUME `metric_field U (G:real^N->real^N^N)`; ASSUME `(y:real^N) IN U`] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_LRICCI_LINEAR) THEN
  REWRITE_TAC[ASSUME `metric_field U (G:real^N->real^N^N)`; ASSUME `(y:real^N) IN U`] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum(1..dimindex(:N)) (\k. sum(1..dimindex(:N)) (\l.
      matrix_inv((G:real^N->real^N^N) y)$k$l *
      sum(1..dimindex(:N)) (\s.
        lrm4 G y (\m. if m = 1 then basis k else if m = 2 then v
                      else if m = 3 then transp (S:real^N^N) ** basis s else w) *
        lricci G y (basis l) (transp (S:real^N^N) ** basis s))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[SUM_LMUL] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `S:real^N^N`;
                   `\x z. lrm4 (G:real^N->real^N^N) y
                            (\m. if m = 1 then basis k else if m = 2 then v
                                 else if m = 3 then x else w) *
                          lricci G y (basis l) z`] RFA_TRACE_FRAME) THEN
    ASM_SIMP_TAC[RFA_LIN_MUL_CONST; RFA_LIN_CONST_MUL] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN BETA_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `s:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `S:real^N^N`;
                 `\x z. lrm4 (G:real^N->real^N^N) y
                          (\m. if m = 1 then x else if m = 2 then v
                               else if m = 3 then transp (S:real^N^N) ** basis s else w) *
                        lricci G y z (transp (S:real^N^N) ** basis s)`] RFA_TRACE_FRAME) THEN
  ASM_SIMP_TAC[RFA_LIN_MUL_CONST; RFA_LIN_CONST_MUL] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[REAL_MUL_ASSOC]);;

let RFA_BILIN_FRAME_EQ = prove
 (`!(G0:real^N^N) (S:real^N^N) (B1:real^N->real^N->real) B2 v w.
     invertible G0 /\ invertible S /\ matrix_inv G0 = transp S ** S /\
     (!z. linear (\x. lift(B1 x z))) /\ (!x. linear (\z. lift(B1 x z))) /\
     (!z. linear (\x. lift(B2 x z))) /\ (!x. linear (\z. lift(B2 x z))) /\
     (!a b. 1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)
            ==> B1 (transp S ** basis a) (transp S ** basis b) =
                B2 (transp S ** basis a) (transp S ** basis b))
     ==> B1 v w = B2 v w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G0:real^N^N`; `S:real^N^N`; `B1:real^N->real^N->real`; `v:real^N`;
                 `w:real^N`] RFA_BILIN_FRAME) THEN
  MP_TAC(ISPECL [`G0:real^N^N`; `S:real^N^N`; `B2:real^N->real^N->real`; `v:real^N`;
                 `w:real^N`] RFA_BILIN_FRAME) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;


(* ========================================================================= *)
(* Dimension 3: the evolution of Ric (RFA_LRICCI_EVOLUTION_3D) and the       *)
(* sectional curvatures as values of lpcurv (RFA_LSECTIONAL_PCURV_3D).       *)
(* ========================================================================= *)

let RFA_LRM4_ZERO12 = prove
 (`!U (G:real^N->real^N^N) y x c d.
     metric_field U G /\ y IN U
     ==> lrm4 G y (\m. if m = 1 then x else if m = 2 then x
                       else if m = 3 then c else d) = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lrm4] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `x:real^N`;
                 `x:real^N`; `d:real^N`] LRIEMANN_ANTISYM) THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `x:real^N = --x <=> x = vec 0`] THEN
  SIMP_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO]);;

let RFA_LRM4_ZERO34 = prove
 (`!U (G:real^N->real^N^N) y a b x.
     metric_field U G /\ y IN U
     ==> lrm4 G y (\m. if m = 1 then a else if m = 2 then b
                       else if m = 3 then x else x) = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lrm4] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `a:real^N`;
                 `b:real^N`; `x:real^N`; `x:real^N`] LRIEMANN_METRIC_ANTISYM) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let RFA_LRM4_SWAP_PAIRS = prove
 (`!U (G:real^N->real^N^N) y p q.
     metric_field U G /\ y IN U
     ==> lrm4 G y (\m. if m = 1 then p else if m = 2 then q
                       else if m = 3 then p else q) =
         lrm4 G y (\m. if m = 1 then q else if m = 2 then p
                       else if m = 3 then q else p)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lrm4] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `lriemann (G:real^N->real^N^N) y q p p = --lriemann G y p q p`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRIEMANN_ANTISYM THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RNEG; DOT_RNEG] THEN
  MATCH_MP_TAC LRIEMANN_METRIC_ANTISYM THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

let RFA_T3D_DIAG_ALG = prove
 (`!(k:num->num->real) a.
     (!i. k i i = &0) /\ (!i j. k i j = k j i) /\ (a = 1 \/ a = 2 \/ a = 3)
     ==> sum(1..3) (\s. sum(1..3) (\i. k i s) * k s a) =
         &3 / &2 * sum(1..3) (\s. sum(1..3) (\i. k i s)) * sum(1..3) (\i. k i a) -
         &2 * sum(1..3) (\i. k i a) pow 2 +
         (sum(1..3) (\s. sum(1..3) (\i. k i s) pow 2) -
          sum(1..3) (\s. sum(1..3) (\i. k i s)) pow 2 / &2)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "z")
    (CONJUNCTS_THEN2 (LABEL_TAC "sy") MP_TAC)) THEN
  SUBGOAL_THEN `(k:num->num->real) 2 1 = k 1 2 /\ k 3 1 = k 1 3 /\ k 3 2 = k 2 3`
  (fun th -> REWRITE_TAC[th]) THENL
   [USE_THEN "sy" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  USE_THEN "z" (fun th -> REWRITE_TAC[th]) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[SUM_3] THEN
  USE_THEN "z" (fun th -> REWRITE_TAC[th]) THEN CONV_TAC REAL_RING);;

let RFA_T3D_FRAME_DIAG = prove
 (`!U (G:real^3->real^3^3) y (S:real^3^3) a.
     metric_field U G /\ y IN U /\ matrix_inv(G y) = transp S ** S /\
     (a = 1 \/ a = 2 \/ a = 3)
     ==> sum(1..3) (\s. lricci G y (transp S ** basis s) (transp S ** basis s) *
                        lrm4 G y (\m. if m = 1 then transp S ** basis s
                                      else if m = 2 then transp S ** basis a
                                      else if m = 3 then transp S ** basis s
                                      else transp S ** basis a)) =
         &3 / &2 * sum(1..3) (\s. lricci G y (transp S ** basis s) (transp S ** basis s)) *
                   lricci G y (transp S ** basis a) (transp S ** basis a) -
         &2 * lricci G y (transp S ** basis a) (transp S ** basis a) pow 2 +
         (sum(1..3) (\s. lricci G y (transp S ** basis s) (transp S ** basis s) pow 2) -
          sum(1..3) (\s. lricci G y (transp S ** basis s) (transp S ** basis s)) pow 2 / &2)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  ABBREV_TAC `kk = \i s. lrm4 (G:real^3->real^3^3) y
                     (\m. if m = 1 then transp (S:real^3^3) ** basis i
                          else if m = 2 then transp S ** basis s
                          else if m = 3 then transp S ** basis i
                          else transp S ** basis s)` THEN
  SUBGOAL_THEN `!s. lricci (G:real^3->real^3^3) y (transp (S:real^3^3) ** basis s) (transp S ** basis s) =
                    sum(1..3) (\i. (kk:num->num->real) i s)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN EXPAND_TAC "kk" THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`;
                   `transp (S:real^3^3) ** basis s`; `transp (S:real^3^3) ** basis s`]
           RFA_RIC_FRAME_RM) THEN
    ASM_REWRITE_TAC[DIMINDEX_3];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. lrm4 (G:real^3->real^3^3) y
          (\m. if m = 1 then transp (S:real^3^3) ** basis s
               else if m = 2 then transp S ** basis a
               else if m = 3 then transp S ** basis s
               else transp S ** basis a) = (kk:num->num->real) s a`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN EXPAND_TAC "kk" THEN REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC RFA_T3D_DIAG_ALG THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "kk" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC RFA_LRM4_ZERO12 THEN EXISTS_TAC `U:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN EXPAND_TAC "kk" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC RFA_LRM4_SWAP_PAIRS THEN EXISTS_TAC `U:real^3->bool` THEN
    ASM_REWRITE_TAC[]]);;

let RFA_T3D_FRAME_OFF = prove
 (`!U (G:real^3->real^3^3) y (S:real^3^3) a b s.
     metric_field U G /\ y IN U /\ matrix_inv(G y) = transp S ** S /\
     lricci G y (transp S ** basis a) (transp S ** basis b) = &0 /\
     ~(a = b) /\ (a = 1 \/ a = 2 \/ a = 3) /\ (b = 1 \/ b = 2 \/ b = 3) /\
     (s = 1 \/ s = 2 \/ s = 3)
     ==> lrm4 G y (\m. if m = 1 then transp S ** basis s
                       else if m = 2 then transp S ** basis a
                       else if m = 3 then transp S ** basis s
                       else transp S ** basis b) = &0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "eig")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "da")
    (CONJUNCTS_THEN2 (LABEL_TAC "db") (LABEL_TAC "ds")))))))) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`;
                 `transp (S:real^3^3) ** basis a`; `transp (S:real^3^3) ** basis b`]
         RFA_RIC_FRAME_RM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_3; SUM_3] THEN
  DISCH_THEN(fun th -> USE_THEN "eig" (MP_TAC o REWRITE_RULE[th])) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] RFA_LRM4_ZERO12) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] RFA_LRM4_ZERO34) THEN
  REWRITE_TAC[ASSUME `metric_field U (G:real^3->real^3^3)`; ASSUME `(y:real^3) IN U`] THEN
  DISCH_THEN(LABEL_TAC "z34") THEN DISCH_THEN(LABEL_TAC "z12") THEN
  REMOVE_THEN "eig" (K ALL_TAC) THEN
  REMOVE_THEN "da" (REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  REMOVE_THEN "db" (REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  REMOVE_THEN "ds" (REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  REWRITE_TAC[] THEN TRY(FIRST_ASSUM(CONTR_TAC o check (fun th -> concl th = `F`))) THEN
  USE_THEN "z12" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "z34" (fun th -> REWRITE_TAC[th]) THEN
  REAL_ARITH_TAC);;

let RFA_EIGEN_SUM_COLLAPSE = prove
 (`!(G:real^3->real^3^3) y (S:real^3^3) (Fr:num->real) s.
     (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3 /\ ~(i = j)
            ==> lricci G y (transp S ** basis i) (transp S ** basis j) = &0) /\
     1 <= s /\ s <= 3
     ==> sum(1..3) (\r. Fr r * lricci G y (transp S ** basis r) (transp S ** basis s)) =
         Fr s * lricci G y (transp S ** basis s) (transp S ** basis s) /\
         sum(1..3) (\r. lricci G y (transp S ** basis s) (transp S ** basis r) * Fr r) =
         lricci G y (transp S ** basis s) (transp S ** basis s) * Fr s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN
  MATCH_MP_TAC EQ_TRANS THENL
   [EXISTS_TAC `sum(1..3) (\r. if r = s then (Fr:num->real) s *
                     lricci (G:real^3->real^3^3) y (transp (S:real^3^3) ** basis s) (transp S ** basis s)
                     else &0)`;
    EXISTS_TAC `sum(1..3) (\r. if r = s then
                     lricci (G:real^3->real^3^3) y (transp (S:real^3^3) ** basis s) (transp S ** basis s) *
                     (Fr:num->real) s else &0)`] THEN
  (CONJ_TAC THENL
    [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
     BETA_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
     FIRST_ASSUM(MP_TAC o SPECL [`r:num`; `s:num`]) THEN
     FIRST_ASSUM(MP_TAC o SPECL [`s:num`; `r:num`]) THEN
     ASM_REWRITE_TAC[] THEN
     ASM_SIMP_TAC[REAL_MUL_RZERO; REAL_MUL_LZERO] THEN
     REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_LZERO];
     REWRITE_TAC[SUM_DELTA; IN_NUMSEG] THEN ASM_REWRITE_TAC[]]));;

let RFA_T3D_FRAME_VALUE = prove
 (`!U (G:real^3->real^3^3) y (S:real^3^3) a b.
     metric_field U G /\ y IN U /\ invertible S /\ matrix_inv(G y) = transp S ** S /\
     (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3 /\ ~(i = j)
            ==> lricci G y (transp S ** basis i) (transp S ** basis j) = &0) /\
     (a = 1 \/ a = 2 \/ a = 3) /\ (b = 1 \/ b = 2 \/ b = 3)
     ==> sum(1..3) (\s. sum(1..3) (\r.
           lrm4 G y (\m. if m = 1 then transp S ** basis r
                         else if m = 2 then transp S ** basis a
                         else if m = 3 then transp S ** basis s
                         else transp S ** basis b) *
           lricci G y (transp S ** basis r) (transp S ** basis s))) =
         &3 / &2 * sum(1..3) (\s. lricci G y (transp S ** basis s) (transp S ** basis s)) *
                   lricci G y (transp S ** basis a) (transp S ** basis b) -
         &2 * sum(1..3) (\s. lricci G y (transp S ** basis a) (transp S ** basis s) *
                             lricci G y (transp S ** basis s) (transp S ** basis b)) +
         (sum(1..3) (\r. sum(1..3) (\s.
             lricci G y (transp S ** basis r) (transp S ** basis s) pow 2)) -
          sum(1..3) (\s. lricci G y (transp S ** basis s) (transp S ** basis s)) pow 2 / &2) *
         ((transp S ** basis a) dot (G y ** (transp S ** basis b)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "eig") (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))))) THEN
  SUBGOAL_THEN `1 <= a /\ a <= 3 /\ 1 <= b /\ b <= 3` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. 1 <= s /\ s <= 3
        ==> sum(1..3) (\r. lrm4 (G:real^3->real^3^3) y
                (\m. if m = 1 then transp (S:real^3^3) ** basis r
                     else if m = 2 then transp S ** basis a
                     else if m = 3 then transp S ** basis s
                     else transp S ** basis b) *
                lricci G y (transp S ** basis r) (transp S ** basis s)) =
            lrm4 G y (\m. if m = 1 then transp S ** basis s
                          else if m = 2 then transp S ** basis a
                          else if m = 3 then transp S ** basis s
                          else transp S ** basis b) *
            lricci G y (transp S ** basis s) (transp S ** basis s)`
  (LABEL_TAC "c1") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`;
                   `\r. lrm4 (G:real^3->real^3^3) y
                          (\m. if m = 1 then transp (S:real^3^3) ** basis r
                               else if m = 2 then transp S ** basis a
                               else if m = 3 then transp S ** basis s
                               else transp S ** basis b)`; `s:num`]
           RFA_EIGEN_SUM_COLLAPSE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..3) (\s. sum(1..3) (\r.
       lrm4 (G:real^3->real^3^3) y
         (\m. if m = 1 then transp (S:real^3^3) ** basis r
              else if m = 2 then transp S ** basis a
              else if m = 3 then transp S ** basis s
              else transp S ** basis b) *
       lricci G y (transp S ** basis r) (transp S ** basis s))) =
    sum(1..3) (\s. lricci G y (transp S ** basis s) (transp S ** basis s) *
                   lrm4 G y (\m. if m = 1 then transp S ** basis s
                                 else if m = 2 then transp S ** basis a
                                 else if m = 3 then transp S ** basis s
                                 else transp S ** basis b))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `s:num` THEN STRIP_TAC THEN BETA_TAC THEN
    USE_THEN "c1" (fun th -> REWRITE_TAC[MATCH_MP th
      (CONJ (ASSUME `1 <= s`) (ASSUME `s <= 3`))]) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..3) (\r. sum(1..3) (\s.
       lricci (G:real^3->real^3^3) y (transp (S:real^3^3) ** basis r) (transp S ** basis s) pow 2)) =
    sum(1..3) (\s. lricci G y (transp S ** basis s) (transp S ** basis s) pow 2)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[REAL_POW_2] THEN
    MP_TAC(ISPECL [`G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`;
                   `\s. lricci (G:real^3->real^3^3) y (transp (S:real^3^3) ** basis r)
                                                         (transp S ** basis s)`; `r:num`]
           RFA_EIGEN_SUM_COLLAPSE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..3) (\s. lricci (G:real^3->real^3^3) y (transp (S:real^3^3) ** basis a) (transp S ** basis s) *
                   lricci G y (transp S ** basis s) (transp S ** basis b)) =
    lricci G y (transp S ** basis a) (transp S ** basis a) *
    lricci G y (transp S ** basis a) (transp S ** basis b)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`;
                   `\s. lricci (G:real^3->real^3^3) y (transp (S:real^3^3) ** basis s)
                                                         (transp S ** basis b)`; `a:num`]
           RFA_EIGEN_SUM_COLLAPSE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(G:real^3->real^3^3) y`; `S:real^3^3`; `a:num`; `b:num`]
         RFA_GFRAME_ORTHO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[DIMINDEX_3] THEN ASM_MESON_TAC[LRG_METRIC_INVERTIBLE];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_CASES_TAC `a:num = b` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN REWRITE_TAC[REAL_MUL_RID] THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`;
                   `a:num`] RFA_T3D_FRAME_DIAG) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
  USE_THEN "eig" (fun th -> REWRITE_TAC[MATCH_MP th
    (end_itlist CONJ (map ASSUME [`1 <= a`; `a <= 3`; `1 <= b`; `b <= 3`; `~(a:num = b)`]))]) THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_RZERO; REAL_ADD_RID] THEN
  MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN X_GEN_TAC `s:num` THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_ENTIRE] THEN DISJ2_TAC THEN
  MATCH_MP_TAC RFA_T3D_FRAME_OFF THEN EXISTS_TAC `U:real^3->bool` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [USE_THEN "eig" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_ARITH_TAC]);;

let RFA_RMRIC_3D = prove
 (`!U (G:real^3->real^3^3) y v w.
     metric_field U G /\ y IN U
     ==> sum(1..dimindex(:3)) (\k. sum(1..dimindex(:3)) (\l.
           sum(1..dimindex(:3)) (\p. sum(1..dimindex(:3)) (\q.
             matrix_inv(G y)$k$l * matrix_inv(G y)$p$q *
             lrm4 G y (\m. if m = 1 then basis k else if m = 2 then v
                           else if m = 3 then basis p else w) *
             lricci G y (basis l) (basis q))))) =
         &3 / &2 * lscalar G y * lricci G y v w -
         &2 * sum(1..dimindex(:3)) (\p. sum(1..dimindex(:3)) (\q.
                matrix_inv(G y)$p$q * lricci G y v (basis p) * lricci G y (basis q) w)) +
         (ltnorm2 2 G (lric2 G) y - lscalar G y pow 2 / &2) * (v dot (G y ** w))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] RFA_RIC_EIGENFRAME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` (STRIP_ASSUME_TAC o REWRITE_RULE[DIMINDEX_3])) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`;
                 `v:real^3`; `w:real^3`] RFA_T_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`;
                 `v:real^3`; `w:real^3`] RFA_RIC2_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`]
         RFA_SCAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`]
         RFA_RICNORM_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[DIMINDEX_3] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] RFA_LRM4_LINEAR) THEN
  REWRITE_TAC[ASSUME `metric_field U (G:real^3->real^3^3)`; ASSUME `(y:real^3) IN U`] THEN
  DISCH_THEN(LABEL_TAC "lrm") THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] LRG_LRICCI_LINEAR) THEN
  REWRITE_TAC[ASSUME `metric_field U (G:real^3->real^3^3)`; ASSUME `(y:real^3) IN U`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ric1") (LABEL_TAC "ric2")) THEN
  MP_TAC(ISPECL
   [`(G:real^3->real^3^3) y`; `S:real^3^3`;
    `\x z. sum(1..3) (\s. sum(1..3) (\r.
       lrm4 (G:real^3->real^3^3) y
         (\m. if m = 1 then transp (S:real^3^3) ** basis r else if m = 2 then x
              else if m = 3 then transp S ** basis s else z) *
       lricci G y (transp S ** basis r) (transp S ** basis s)))`;
    `\x z. &3 / &2 * sum(1..3) (\s. lricci (G:real^3->real^3^3) y
                                     (transp (S:real^3^3) ** basis s) (transp S ** basis s)) *
                     lricci G y x z -
           &2 * sum(1..3) (\s. lricci G y x (transp S ** basis s) *
                               lricci G y (transp S ** basis s) z) +
           (sum(1..3) (\r. sum(1..3) (\s.
               lricci G y (transp S ** basis r) (transp S ** basis s) pow 2)) -
            sum(1..3) (\s. lricci G y (transp S ** basis s) (transp S ** basis s)) pow 2 /
            &2) * (x dot (G y ** z))`;
    `v:real^3`; `w:real^3`] RFA_BILIN_FRAME_EQ) THEN
  BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[DIMINDEX_3] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REPEAT(MATCH_MP_TAC RFA_LINEAR_LIFT_SUM THEN
      REWRITE_TAC[FINITE_NUMSEG] THEN GEN_TAC THEN DISCH_TAC) THEN
    MATCH_MP_TAC RFA_LIN_MUL_CONST THEN USE_THEN "lrm" (fun th -> REWRITE_TAC[th]);
    GEN_TAC THEN REPEAT(MATCH_MP_TAC RFA_LINEAR_LIFT_SUM THEN
      REWRITE_TAC[FINITE_NUMSEG] THEN GEN_TAC THEN DISCH_TAC) THEN
    MATCH_MP_TAC RFA_LIN_MUL_CONST THEN USE_THEN "lrm" (fun th -> REWRITE_TAC[th]);
    GEN_TAC THEN MATCH_MP_TAC RFA_LINEAR_LIFT_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFA_LINEAR_LIFT_SUB THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC RFA_LIN_CONST_MUL THEN
        USE_THEN "ric1" (fun th -> REWRITE_TAC[th]);
        MATCH_MP_TAC RFA_LIN_CONST_MUL THEN MATCH_MP_TAC RFA_LINEAR_LIFT_SUM THEN
        REWRITE_TAC[FINITE_NUMSEG] THEN GEN_TAC THEN DISCH_TAC THEN
        MATCH_MP_TAC RFA_LIN_MUL_CONST THEN USE_THEN "ric1" (fun th -> REWRITE_TAC[th])];
      MATCH_MP_TAC RFA_LIN_CONST_MUL THEN ONCE_REWRITE_TAC[DOT_SYM] THEN
      REWRITE_TAC[LINEAR_LIFT_DOT]];
    GEN_TAC THEN MATCH_MP_TAC RFA_LINEAR_LIFT_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFA_LINEAR_LIFT_SUB THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC RFA_LIN_CONST_MUL THEN
        USE_THEN "ric2" (fun th -> REWRITE_TAC[th]);
        MATCH_MP_TAC RFA_LIN_CONST_MUL THEN MATCH_MP_TAC RFA_LINEAR_LIFT_SUM THEN
        REWRITE_TAC[FINITE_NUMSEG] THEN GEN_TAC THEN DISCH_TAC THEN
        MATCH_MP_TAC RFA_LIN_CONST_MUL THEN USE_THEN "ric2" (fun th -> REWRITE_TAC[th])];
      MATCH_MP_TAC RFA_LIN_CONST_MUL THEN REWRITE_TAC[RFA_LIFT_DOT_GMUL_LINEAR]];
    MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN STRIP_TAC THEN
    MATCH_MP_TAC RFA_T3D_FRAME_VALUE THEN EXISTS_TAC `U:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let RFA_LRICCI_EVOLUTION_3D = prove
 (`!U a b (G:real->real^3->real^3^3) t y v w.
        lricci_flow U a b G /\ a < t /\ t < b /\ y IN U
        ==> ((\s. lricci (G s) y v w) has_real_derivative
             ltlap 2 (G t) (lric2 (G t)) y (\m. if m = 1 then v else w) +
             &3 * lscalar (G t) y * lricci (G t) y v w -
             &6 * sum(1..3)
                   (\p. sum(1..3)
                     (\q. matrix_inv(G t y)$p$q * lricci (G t) y v (basis p) *
                          lricci (G t) y (basis q) w)) +
             (&2 * ltnorm2 2 (G t) (lric2 (G t)) y - lscalar (G t) y pow 2) *
             (v dot (G t y ** w))) (atreal t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^3->real^3^3) t)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_FLOW_BASIC]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `a:real`; `b:real`; `G:real->real^3->real^3^3`;
                 `t:real`; `y:real^3`; `v:real^3`; `w:real^3`]
         (INST_TYPE [`:3`,`:N`] RFA_LRICCI_EVOLUTION)) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `(G:real->real^3->real^3^3) t`; `y:real^3`;
                 `v:real^3`; `w:real^3`] RFA_RMRIC_3D) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIMINDEX_3] THEN
  MATCH_MP_TAC(MESON[]
   `(x:real) = y ==> (f has_real_derivative x) net ==> (f has_real_derivative y) net`) THEN
  REAL_ARITH_TAC);;

let RFA_ORTHO3_MATRIX = prove
 (`!(G0:real^3^3) u v w.
     (!a b. a dot (G0 ** b) = b dot (G0 ** a)) /\
     u dot (G0 ** u) = &1 /\ v dot (G0 ** v) = &1 /\ w dot (G0 ** w) = &1 /\
     u dot (G0 ** v) = &0 /\ u dot (G0 ** w) = &0 /\ v dot (G0 ** w) = &0
     ==> ?S:real^3^3. invertible S /\ matrix_inv G0 = transp S ** S /\
                      transp S ** basis 1 = u /\ transp S ** basis 2 = v /\
                      transp S ** basis 3 = w`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `(lambda i j. if i = 1 then (u:real^3)$j else if i = 2 then (v:real^3)$j
                           else (w:real^3)$j):real^3^3` THEN
  ABBREV_TAC `S = (lambda i j. if i = 1 then (u:real^3)$j else if i = 2 then (v:real^3)$j
                               else (w:real^3)$j):real^3^3` THEN
  SUBGOAL_THEN `transp (S:real^3^3) ** basis 1 = u /\ transp S ** basis 2 = v /\
                transp S ** basis 3 = w`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REPEAT CONJ_TAC THEN
    SIMP_TAC[CART_EQ; MATRIX_VECTOR_MUL_BASIS; column; transp; LAMBDA_BETA;
             DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
                      ==> ((S:real^3^3) ** (G0:real^3^3) ** transp S)$i$j =
                          (transp S ** basis i) dot (G0 ** (transp S ** basis j))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL; MATRIX_VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[DOT_BASIS; DIMINDEX_3] THEN
    REWRITE_TAC[MATRIX_MUL_ASSOC] THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_BASIS; DIMINDEX_3; column; LAMBDA_BETA];
    ALL_TAC] THEN
  SUBGOAL_THEN `(S:real^3^3) ** (G0:real^3^3) ** transp S = mat 1` ASSUME_TAC THENL
   [REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3] THEN
    SUBGOAL_THEN `(v:real^3) dot ((G0:real^3^3) ** u) = &0 /\ (w:real^3) dot (G0 ** u) = &0 /\
                  w dot (G0 ** v) = &0` STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH; MAT_COMPONENT; DIMINDEX_3];
    ALL_TAC] THEN
  SUBGOAL_THEN `matrix_inv (G0:real^3^3) = transp (S:real^3^3) ** S` ASSUME_TAC THENL
   [MATCH_MP_TAC MATRIX_INV_UNIQUE THEN
    SUBGOAL_THEN `(G0:real^3^3) ** (transp (S:real^3^3) ** S) = mat 1` ASSUME_TAC THENL
     [REWRITE_TAC[MATRIX_MUL_ASSOC] THEN ONCE_REWRITE_TAC[MATRIX_LEFT_RIGHT_INVERSE] THEN
      ASM_REWRITE_TAC[GSYM MATRIX_MUL_ASSOC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[MATRIX_LEFT_RIGHT_INVERSE] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[INVERTIBLE_RIGHT_INVERSE] THEN
  EXISTS_TAC `(G0:real^3^3) ** transp (S:real^3^3)` THEN ASM_REWRITE_TAC[]);;

let lpcurv = new_definition
 `lpcurv (G:real^N->real^N^N) (y:real^N) (u:num->real^N) =
    lscalar G y / &2 * lmetric2 G y u - lric2 G y u`;;

let RFA_LSECTIONAL_PCURV_3D = prove
 (`!U (G:real^3->real^3^3) y u v w.
        metric_field U G /\ y IN U /\
        u dot (G y ** u) = &1 /\ v dot (G y ** v) = &1 /\ w dot (G y ** w) = &1 /\
        u dot (G y ** v) = &0 /\ u dot (G y ** w) = &0 /\ v dot (G y ** w) = &0
        ==> lsectional G y u v = lpcurv G y (\m. w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(G:real^3->real^3^3) y`; `u:real^3`; `v:real^3`; `w:real^3`]
         RFA_ORTHO3_MATRIX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN MATCH_MP_TAC LRG_METRIC_SYM THEN
    EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[lsectional; lpcurv; lmetric2; lric2] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_DIV_1; REAL_MUL_RID] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`]
         RFA_SCAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_3; SUM_3] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MAP_EVERY (fun t -> MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`;
                                     `S:real^3^3`; t; t] RFA_RIC_FRAME_RM))
    [`u:real^3`; `v:real^3`; `w:real^3`] THEN
  ASM_REWRITE_TAC[DIMINDEX_3; SUM_3] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] RFA_LRM4_ZERO12) THEN
  REWRITE_TAC[ASSUME `metric_field U (G:real^3->real^3^3)`; ASSUME `(y:real^3) IN U`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MAP_EVERY (fun (p,q) -> MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`;
                                         p; q] RFA_LRM4_SWAP_PAIRS))
    [`v:real^3`,`u:real^3`; `w:real^3`,`u:real^3`; `w:real^3`,`v:real^3`] THEN
  REWRITE_TAC[ASSUME `metric_field U (G:real^3->real^3^3)`; ASSUME `(y:real^3) IN U`] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[lrm4] THEN CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC);;

