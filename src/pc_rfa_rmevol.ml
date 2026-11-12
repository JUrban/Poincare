(* ========================================================================= *)
(* Unit pc_rfa_rmevol: evolution of the curvature tensor under the Ricci     *)
(* flow: the time derivative of Rm, the rough Laplacian of Rm through the    *)
(* second Bianchi identity and the contracted Bianchi identity, the exact    *)
(* evolution equation, and the evolution d/dt Rm = Lap Rm + B(Rm,Rm) with B  *)
(* in the class lbilin (RFA_LRM4_EVOLUTION).                                 *)
(* ========================================================================= *)

needs "src/pc_rfa_ricid.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The time derivative of lrm4 along a local Ricci flow, in                  *)
(* terms of the covariant derivative of the time derivative of the          *)
(* Christoffel symbols (LRG_FLOW_DRIEMANN, LRG_FLOW_PALATINI).              *)
(* ========================================================================= *)

let RFA_LRM4_DT = prove
 (`!U a b (G:real->real^N->real^N^N) t y u.
        lricci_flow U a b G /\ a < t /\ t < b /\ y IN U
        ==> ((\s. lrm4 (G s) y u) has_real_derivative
             --(&2) * lricci (G t) y (u 3) (lriemann (G t) y (u 1) (u 2) (u 4)) +
             (lnabla 3 (G t) (\x p. p 3 dot (G t x ** ldgamma G t x (p 1) (p 2))) y
                (\m. if m = 1 then u 2 else if m = 2 then u 4 else if m = 3 then u 3
                     else u 1) -
              lnabla 3 (G t) (\x p. p 3 dot (G t x ** ldgamma G t x (p 1) (p 2))) y
                (\m. if m = 1 then u 1 else if m = 2 then u 4 else if m = 3 then u 3
                     else u 2))) (atreal t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t)` ASSUME_TAC THENL
   [ASM_MESON_TAC[lricci_flow]; ALL_TAC] THEN
  REWRITE_TAC[lrm4; HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `t:real`; `y:real^N`] LRG_FLOW_VDERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(REWRITE_RULE[GSYM ldgamma]
    (ISPECL [`U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
             `t:real`; `y:real^N`; `(u:num->real^N) 1`; `(u:num->real^N) 2`;
             `(u:num->real^N) 4`] LRG_FLOW_DRIEMANN)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th1 -> FIRST_X_ASSUM(fun th2 ->
    MP_TAC(SPEC `(u:num->real^N) 3`
      (MATCH_MP LRG_VDERIV_DOT_PRODUCT (CONJ th2 th1))))) THEN
  REWRITE_TAC[LIFT_DROP] THEN
  MATCH_MP_TAC(MESON[]
   `(x:real^1) = y ==> (f has_vector_derivative x) net
                     ==> (f has_vector_derivative y) net`) THEN
  AP_TERM_TAC THEN BINOP_TAC THENL
   [MATCH_MP_TAC LRG_HDOT THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC LRG_FLOW_PALATINI THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The time derivative of lrm4 in terms of the second                        *)
(* covariant derivative of the Ricci tensor (LRG_FLOW_NQ).                  *)
(* ========================================================================= *)

let rfa_n3 = new_definition
 `rfa_n3 (G:real^N->real^N^N) y (a:real^N) b c d =
    lnabla 3 G (lnabla 2 G (lric2 G)) y
      (\m. if m = 1 then a else if m = 2 then b else if m = 3 then c else d)`;;

let RFA_LRM4_DT_N3 = prove
 (`!U a b (G:real->real^N->real^N^N) t y u.
        lricci_flow U a b G /\ a < t /\ t < b /\ y IN U
        ==> ((\s. lrm4 (G s) y u) has_real_derivative
             --(&2) * lricci (G t) y (u 3) (lriemann (G t) y (u 1) (u 2) (u 4)) +
             (rfa_n3 (G t) y (u 4) (u 3) (u 1) (u 2) -
              rfa_n3 (G t) y (u 4) (u 3) (u 2) (u 1)) +
             rfa_n3 (G t) y (u 2) (u 4) (u 3) (u 1) +
             rfa_n3 (G t) y (u 1) (u 3) (u 4) (u 2) -
             rfa_n3 (G t) y (u 2) (u 3) (u 4) (u 1) -
             rfa_n3 (G t) y (u 1) (u 4) (u 3) (u 2)) (atreal t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `t:real`; `y:real^N`; `u:num->real^N`] RFA_LRM4_DT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `t:real`; `y:real^N`; `(u:num->real^N) 2`; `(u:num->real^N) 4`;
                 `(u:num->real^N) 3`; `(u:num->real^N) 1`] LRG_FLOW_NQ) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `t:real`; `y:real^N`; `(u:num->real^N) 1`; `(u:num->real^N) 4`;
                 `(u:num->real^N) 3`; `(u:num->real^N) 2`] LRG_FLOW_NQ) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[GSYM rfa_n3] THEN
  MATCH_MP_TAC(MESON[]
   `(x:real) = y ==> (f has_real_derivative x) net
                   ==> (f has_real_derivative y) net`) THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Covariant derivatives and contractions of arbitrary slot                  *)
(* pairs commute; the second Bianchi identity one derivative higher; the    *)
(* symmetries of nabla Rm on explicit tuples; the contracted Bianchi        *)
(* identity for the divergence of Rm in its fourth slot.                    *)
(* ========================================================================= *)

let RFA_LNABLA_CTR_AT = prove
 (`!k U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) i j y u.
        metric_field U G /\ ltensor_field (k + 2) U tf /\
        (!u. smooth_map_on U (\x. lift(tf x u))) /\ y IN U /\
        1 <= i /\ i < j /\ j <= k + 2
        ==> lnabla k G (\z w. sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
                                 matrix_inv(G z)$a$b *
                                 tf z (rfa_ins i j (basis a) (basis b) w)))) y u =
            sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
              matrix_inv(G y)$a$b *
              lnabla (k + 2) G tf y (rfa_ins i j (basis a) (basis b) u)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z w. sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
             matrix_inv((G:real^N->real^N^N) z)$a$b *
             (tf:real^N->(num->real^N)->real) z
               (rfa_ins i j (basis a) (basis b) w)))) =
    ltcontr G (ltperm (rfa_sig i j) tf)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REPEAT GEN_TAC THEN BETA_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC RFA_LTCONTR_SIG THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfa_sig i j permutes 1..k + 2` ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_SIG_PERMUTES THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `ltperm (rfa_sig i j) (tf:real^N->(num->real^N)->real)`;
                 `y:real^N`; `u:num->real^N`] RFA_LNABLA_LTCONTR) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RFA_LTPERM_FIELD] THEN MATCH_MP_TAC RFA_LTPERM_SMOOTH THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `lnabla (k + 2) (G:real^N->real^N^N) (ltperm (rfa_sig i j) tf) =
    ltperm (rfa_sig i j) (lnabla (k + 2) G (tf:real^N->(num->real^N)->real))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
    MATCH_MP_TAC RFA_LNABLA_LTPERM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC RFA_LTCONTR_SIG THEN ASM_REWRITE_TAC[]);;

(* The second Bianchi identity for nabla Rm, differentiated once more. *)

let RFA_PERM345_1 = prove
 (`(\m. if m = 3 then 4 else if m = 4 then 5 else if m = 5 then 3 else m)
   permutes 1..5`,
  MATCH_MP_TAC PERMUTES_BIJECTIONS THEN
  EXISTS_TAC `\m. if m = 3 then 5 else if m = 4 then 3 else if m = 5 then 4 else m` THEN
  REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC);;

let RFA_PERM345_2 = prove
 (`(\m. if m = 3 then 5 else if m = 4 then 3 else if m = 5 then 4 else m)
   permutes 1..5`,
  MATCH_MP_TAC PERMUTES_BIJECTIONS THEN
  EXISTS_TAC `\m. if m = 3 then 4 else if m = 4 then 5 else if m = 5 then 3 else m` THEN
  REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC);;

let RFA_N5_FIELD = prove
 (`!U (G:real^N->real^N^N).
        metric_field U G
        ==> ltensor_field 5 U (lnabla 4 G (lrm4 G)) /\
            (!u. smooth_map_on U (\y. lift(lnabla 4 G (lrm4 G) y u)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`4`; `U:real^N->bool`; `G:real^N->real^N^N`; `lrm4(G:real^N->real^N^N)`]
         LNABLA_TENSOR_FIELD) THEN
  ASM_SIMP_TAC[LRM4_TENSOR_FIELD; ARITH]);;

let RFA_N5_BIANCHI = prove
 (`!U (G:real^N->real^N^N) z w.
        metric_field U G /\ z IN U
        ==> lnabla 4 G (lrm4 G) z w +
            lnabla 4 G (lrm4 G) z
              (\m. w(if m = 3 then 4 else if m = 4 then 5 else if m = 5 then 3 else m)) +
            lnabla 4 G (lrm4 G) z
              (\m. w(if m = 3 then 5 else if m = 4 then 3 else if m = 5 then 4 else m)) =
            &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`;
                 `(w:num->real^N) 1`; `(w:num->real^N) 2`; `(w:num->real^N) 3`;
                 `(w:num->real^N) 4`; `(w:num->real^N) 5`] LRM4_BIANCHI2) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `a = a' /\ b = b' /\ c = c' ==> a + b + c = &0 ==> a' + b' + c' = &0`) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] RFA_N5_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `z:real^N` o
    GEN_REWRITE_RULE I [ltensor_field] o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN X_GEN_TAC `m:num` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `m = 1 \/ m = 2 \/ m = 3 \/ m = 4 \/ m = 5`
    (REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  TRY ASM_ARITH_TAC THEN REWRITE_TAC[ARITH]);;

(* Same statement as LRG_LNABLA_ZERO of pc_lrg_stab.ml, which this unit does *)
(* not load.                                                                  *)

let RFA_LNABLA_ZERO = prove
 (`!k (G:real^N->real^N^N) y u. lnabla k G (\x u. &0) y u = &0`,
  REWRITE_TAC[lnabla; LIFT_NUM; FRECHET_DERIVATIVE_CONST_AT; DROP_VEC; SUM_0;
              REAL_SUB_REFL]);;

let RFA_N6_BIANCHI = prove
 (`!U (G:real^N->real^N^N) y w.
        metric_field U G /\ y IN U
        ==> lnabla_iter 4 2 G (lrm4 G) y w +
            lnabla_iter 4 2 G (lrm4 G) y
              (\m. w(if m = 3 then 4 else if m = 4 then 5 else if m = 5 then 3 else m)) +
            lnabla_iter 4 2 G (lrm4 G) y
              (\m. w(if m = 3 then 5 else if m = 4 then 3 else if m = 5 then 4 else m)) =
            &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] RFA_N5_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[RFA_LNABLA_ITER_2; ARITH_RULE `4 + 1 = 5`] THEN
  MP_TAC(ISPECL [`5`; `G:real^N->real^N^N`; `G:real^N->real^N^N`;
    `\x (u:num->real^N). lnabla 4 (G:real^N->real^N^N) (lrm4 G) x u +
       lnabla 4 G (lrm4 G) x
         (\m. u(if m = 3 then 4 else if m = 4 then 5 else if m = 5 then 3 else m)) +
       lnabla 4 G (lrm4 G) x
         (\m. u(if m = 3 then 5 else if m = 4 then 3 else if m = 5 then 4 else m))`;
    `\x:real^N u:num->real^N. &0`; `U:real^N->bool`; `y:real^N`; `w:num->real^N`]
    LRG_LNABLA_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC RFA_N5_BIANCHI THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[RFA_LNABLA_ZERO]] THEN
  SUBGOAL_THEN
   `!u. (\x. lift(lnabla 4 (G:real^N->real^N^N) (lrm4 G) x u)) differentiable at y`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LRG_LNABLA_ADD; LIFT_ADD; DIFFERENTIABLE_ADD] THEN
  ASM_SIMP_TAC[LRG_LNABLA_PERMUTE; RFA_PERM345_1; RFA_PERM345_2] THEN
  REWRITE_TAC[ETA_AX]);;

(* Double sums against a symmetric array. *)

let RFA_SUM_ANTISYM = prove
 (`!(g:num->num->real) (X:num->num->real) n.
        (!a b. 1 <= a /\ a <= n /\ 1 <= b /\ b <= n
               ==> g a b = g b a /\ X a b = --(X b a))
        ==> sum(1..n) (\a. sum(1..n) (\b. g a b * X a b)) = &0`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "sym") THEN
  MATCH_MP_TAC(REAL_ARITH `s = --s ==> s = &0`) THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
  REWRITE_TAC[GSYM SUM_NEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN
  STRIP_TAC THEN BETA_TAC THEN
  USE_THEN "sym" (MP_TAC o SPECL [`j:num`; `i:num`]) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC) THEN REAL_ARITH_TAC);;

let RFA_SUM_SWAP_SYM = prove
 (`!(g:num->num->real) (Fn:num->num->real) n.
        (!a b. 1 <= a /\ a <= n /\ 1 <= b /\ b <= n ==> g a b = g b a)
        ==> sum(1..n) (\a. sum(1..n) (\b. g a b * Fn b a)) =
            sum(1..n) (\a. sum(1..n) (\b. g a b * Fn a b))`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "sym") THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN
  STRIP_TAC THEN BETA_TAC THEN
  USE_THEN "sym" (MP_TAC o SPECL [`j:num`; `i:num`]) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN REFL_TAC);;

(* Symmetries of nabla Rm on explicit tuples. *)

let RFA_N5_ANTI34_T = prove
 (`!U (G:real^N->real^N^N) z a b c d e.
        metric_field U G /\ z IN U
        ==> lnabla 4 (G:real^N->real^N^N) (lrm4 G) z (\m. if m = 1 then a else if m = 2 then b else if m = 3 then c else if m = 4 then d else e) = --(lnabla 4 G (lrm4 G) z (\m. if m = 1 then a else if m = 2 then b else if m = 3 then d else if m = 4 then c else e))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`;
                 `(\m. if m = 1 then a:real^N else if m = 2 then b:real^N else if m = 3 then c:real^N else if m = 4 then d:real^N else e:real^N)`] LRG_NRM_ANTI34) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `x' = x ==> x = --y ==> y = --x'`) THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; swap] THEN X_GEN_TAC `m:num` THEN
  ASM_CASES_TAC `m = 3` THEN ASM_REWRITE_TAC[ARITH] THEN
  ASM_CASES_TAC `m = 4` THEN ASM_REWRITE_TAC[ARITH]);;

(* The contracted second Bianchi identity: the divergence of Rm in its     *)
(* fourth slot is a difference of covariant derivatives of Ric.             *)

let RFA_LRM4_DIV = prove
 (`!U (G:real^N->real^N^N) z p q r.
        metric_field U G /\ z IN U
        ==> sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b. matrix_inv((G:real^N->real^N^N) z)$a$b * lnabla 4 G (lrm4 G) z (\m. if m = 1 then p else if m = 2 then q else if m = 3 then r else if m = 4 then basis a else basis b))) =
            lnabla 2 G (lric2 G) z (\m. if m = 1 then p else if m = 2 then r else q) - lnabla 2 G (lric2 G) z (\m. if m = 1 then q else if m = 2 then r else p)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!a b. matrix_inv((G:real^N->real^N^N) z)$a$b = matrix_inv(G z)$b$a`
  (LABEL_TAC "gsym") THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC LRG_MATRIX_INV_SYM THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* Bianchi with (p,q,r,e_a,e_b) *)
  SUBGOAL_THEN
   `sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b. matrix_inv((G:real^N->real^N^N) z)$a$b * lnabla 4 G (lrm4 G) z (\m. if m = 1 then p else if m = 2 then q else if m = 3 then r else if m = 4 then basis a else basis b))) =
    --(sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b. matrix_inv((G:real^N->real^N^N) z)$a$b * lnabla 4 G (lrm4 G) z (\m. if m = 1 then p else if m = 2 then q else if m = 3 then basis a else if m = 4 then basis b else r)))) - sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b. matrix_inv((G:real^N->real^N^N) z)$a$b * lnabla 4 G (lrm4 G) z (\m. if m = 1 then p else if m = 2 then q else if m = 3 then basis b else if m = 4 then r else basis a)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_NEG; GSYM SUM_SUB_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    BETA_TAC THEN REWRITE_TAC[GSYM SUM_NEG; GSYM SUM_SUB_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`;
                   `p:real^N`; `q:real^N`; `r:real^N`; `basis a:real^N`;
                   `basis b:real^N`] LRM4_BIANCHI2) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  (* the first contraction vanishes *)
  SUBGOAL_THEN `sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b. matrix_inv((G:real^N->real^N^N) z)$a$b * lnabla 4 G (lrm4 G) z (\m. if m = 1 then p else if m = 2 then q else if m = 3 then basis a else if m = 4 then basis b else r))) = &0` SUBST1_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[] (ISPECL
     [`\a b. matrix_inv((G:real^N->real^N^N) z)$a$b`;
      `\a b. lnabla 4 (G:real^N->real^N^N) (lrm4 G) z (\m. if m = 1 then p else if m = 2 then q else if m = 3 then basis a else if m = 4 then basis b else r)`; `dimindex(:N)`] RFA_SUM_ANTISYM)) THEN
    REPEAT STRIP_TAC THEN USE_THEN "gsym" (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC RFA_N5_ANTI34_T THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* pair symmetry and Bianchi again for the second one *)
  SUBGOAL_THEN
   `sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b. matrix_inv((G:real^N->real^N^N) z)$a$b * lnabla 4 G (lrm4 G) z (\m. if m = 1 then p else if m = 2 then q else if m = 3 then basis b else if m = 4 then r else basis a))) =
    --(sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b. matrix_inv((G:real^N->real^N^N) z)$a$b * lnabla 4 G (lrm4 G) z (\m. if m = 1 then basis b else if m = 2 then r else if m = 3 then q else if m = 4 then basis a else p)))) - sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b. matrix_inv((G:real^N->real^N^N) z)$a$b * lnabla 4 G (lrm4 G) z (\m. if m = 1 then basis b else if m = 2 then r else if m = 3 then basis a else if m = 4 then p else q)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_NEG; GSYM SUM_SUB_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    BETA_TAC THEN REWRITE_TAC[GSYM SUM_NEG; GSYM SUM_SUB_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`;
                   `p:real^N`; `q:real^N`; `basis b:real^N`; `r:real^N`;
                   `basis a:real^N`] LRG_LNABLA_LRM4_PAIR) THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`;
                   `basis b:real^N`; `r:real^N`; `p:real^N`; `q:real^N`;
                   `basis a:real^N`] LRM4_BIANCHI2) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  (* the remaining contractions are covariant derivatives of Ric *)
  SUBGOAL_THEN `sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b. matrix_inv((G:real^N->real^N^N) z)$a$b * lnabla 4 G (lrm4 G) z (\m. if m = 1 then basis b else if m = 2 then r else if m = 3 then basis a else if m = 4 then p else q))) = lnabla 2 G (lric2 G) z (\m. if m = 1 then r else if m = 2 then p else q)` SUBST1_TAC THENL
   [MP_TAC(REWRITE_RULE[] (ISPECL
     [`\a b. matrix_inv((G:real^N->real^N^N) z)$a$b`;
      `\i j. lnabla 4 (G:real^N->real^N^N) (lrm4 G) z (\m. if m = 1 then basis i else if m = 2 then r else if m = 3 then basis j else if m = 4 then p else q)`; `dimindex(:N)`] RFA_SUM_SWAP_SYM)) THEN
    ANTS_TAC THENL [REPEAT STRIP_TAC THEN USE_THEN "gsym" MATCH_ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC LRG_NRM_CONTRACT13 THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b. matrix_inv((G:real^N->real^N^N) z)$a$b * lnabla 4 G (lrm4 G) z (\m. if m = 1 then basis b else if m = 2 then r else if m = 3 then q else if m = 4 then basis a else p))) = --(lnabla 2 G (lric2 G) z (\m. if m = 1 then r else if m = 2 then q else p))` SUBST1_TAC THENL
   [SUBGOAL_THEN
     `sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b. matrix_inv((G:real^N->real^N^N) z)$a$b * lnabla 4 G (lrm4 G) z (\m. if m = 1 then basis b else if m = 2 then r else if m = 3 then q else if m = 4 then basis a else p))) = --(sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b. matrix_inv((G:real^N->real^N^N) z)$a$b * lnabla 4 G (lrm4 G) z (\m. if m = 1 then basis b else if m = 2 then r else if m = 3 then basis a else if m = 4 then q else p))))`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM SUM_NEG] THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
      BETA_TAC THEN REWRITE_TAC[GSYM SUM_NEG] THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN
      BETA_TAC THEN REWRITE_TAC[GSYM REAL_MUL_RNEG] THEN AP_TERM_TAC THEN
      MATCH_MP_TAC RFA_N5_ANTI34_T THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    AP_TERM_TAC THEN
    MP_TAC(REWRITE_RULE[] (ISPECL
     [`\a b. matrix_inv((G:real^N->real^N^N) z)$a$b`;
      `\i j. lnabla 4 (G:real^N->real^N^N) (lrm4 G) z (\m. if m = 1 then basis i else if m = 2 then r else if m = 3 then basis j else if m = 4 then q else p)`; `dimindex(:N)`] RFA_SUM_SWAP_SYM)) THEN
    ANTS_TAC THENL [REPEAT STRIP_TAC THEN USE_THEN "gsym" MATCH_ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC LRG_NRM_CONTRACT13 THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* symmetry of nabla Ric in its first two slots *)
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`;
                 `(\m. if m = 1 then r:real^N else if m = 2 then p:real^N else q:real^N)`] LRG_N2_SYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`;
                 `(\m. if m = 1 then r:real^N else if m = 2 then q:real^N else p:real^N)`] LRG_N2_SYM) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\m. if swap(1,2) m = 1 then r:real^N else if swap(1,2) m = 2 then p else q) = (\m. if m = 1 then p else if m = 2 then r else q) /\
    (\m. if swap(1,2) m = 1 then r:real^N else if swap(1,2) m = 2 then q else p) = (\m. if m = 1 then q else if m = 2 then r else p)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM; swap] THEN CONJ_TAC THEN X_GEN_TAC `m:num` THEN
    ASM_CASES_TAC `m = 1` THEN ASM_REWRITE_TAC[ARITH] THEN
    ASM_CASES_TAC `m = 2` THEN ASM_REWRITE_TAC[ARITH];
    REPEAT(DISCH_THEN SUBST1_TAC) THEN REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The rough Laplacian of Rm through the second Bianchi                      *)
(* identity, the contracted Bianchi identity and the Ricci identity.        *)
(* ========================================================================= *)

(* Concrete tuples: agreement on the slots 1..n by evaluation. *)

let RFA_TUPLE_TAC n =
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN (list_mk_disj (map (fun i -> mk_eq(`m:num`, mk_small_numeral i)) (1--n)))
    (REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  TRY ASM_ARITH_TAC THEN REWRITE_TAC[ARITH; rfa_ins; swap];;

let RFA_N2_AGREE = prove
 (`!U (G:real^N->real^N^N) z w w'.
        metric_field U G /\ z IN U /\ (!m. 1 <= m /\ m <= 3 ==> w m = w' m)
        ==> lnabla 2 (G:real^N->real^N^N) (lric2 G) z w = lnabla 2 G (lric2 G) z w'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRG_N2_FIELD) THEN
  ASM_REWRITE_TAC[ltensor_field] THEN ASM_MESON_TAC[]);;

let RFA_N3_FIELD = prove
 (`!U (G:real^N->real^N^N).
        metric_field U G
        ==> ltensor_field 4 U (lnabla 3 (G:real^N->real^N^N) (lnabla 2 G (lric2 G))) /\
            (!u. smooth_map_on U (\y. lift(lnabla 3 G (lnabla 2 G (lric2 G)) y u)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`3`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lnabla 2 (G:real^N->real^N^N) (lric2 G)`] LNABLA_TENSOR_FIELD) THEN
  ASM_SIMP_TAC[LRG_N2_FIELD; ARITH]);;

let RFA_N3_AGREE = prove
 (`!U (G:real^N->real^N^N) z w w'.
        metric_field U G /\ z IN U /\ (!m. 1 <= m /\ m <= 4 ==> w m = w' m)
        ==> lnabla 3 (G:real^N->real^N^N) (lnabla 2 G (lric2 G)) z w = lnabla 3 G (lnabla 2 G (lric2 G)) z w'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] RFA_N3_FIELD) THEN
  ASM_REWRITE_TAC[ltensor_field] THEN ASM_MESON_TAC[]);;

let RFA_N5_AGREE = prove
 (`!U (G:real^N->real^N^N) z w w'.
        metric_field U G /\ z IN U /\ (!m. 1 <= m /\ m <= 5 ==> w m = w' m)
        ==> lnabla 4 (G:real^N->real^N^N) (lrm4 G) z w = lnabla 4 G (lrm4 G) z w'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] RFA_N5_FIELD) THEN
  ASM_REWRITE_TAC[ltensor_field] THEN ASM_MESON_TAC[]);;

let RFA_N6_FIELD = prove
 (`!U (G:real^N->real^N^N).
        metric_field U G
        ==> ltensor_field 6 U (lnabla_iter 4 2 (G:real^N->real^N^N) (lrm4 G)) /\
            (!u. smooth_map_on U (\y. lift(lnabla_iter 4 2 G (lrm4 G) y u)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`4`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lrm4 (G:real^N->real^N^N)`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_SIMP_TAC[LRM4_TENSOR_FIELD] THEN
  DISCH_THEN(MP_TAC o SPEC `2`) THEN REWRITE_TAC[ARITH] THEN SIMP_TAC[]);;

let RFA_N6_AGREE = prove
 (`!U (G:real^N->real^N^N) z w w'.
        metric_field U G /\ z IN U /\ (!m. 1 <= m /\ m <= 6 ==> w m = w' m)
        ==> lnabla_iter 4 2 (G:real^N->real^N^N) (lrm4 G) z w = lnabla_iter 4 2 G (lrm4 G) z w'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] RFA_N6_FIELD) THEN
  ASM_REWRITE_TAC[ltensor_field] THEN ASM_MESON_TAC[]);;

let RFA_CYC3_PERMUTES = prove
 (`(\m. if m = 1 then 2 else if m = 2 then 3 else if m = 3 then 1 else m)
   permutes 1..3`,
  MATCH_MP_TAC PERMUTES_BIJECTIONS THEN
  EXISTS_TAC `\m. if m = 1 then 3 else if m = 2 then 1 else if m = 3 then 2 else m` THEN
  REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC);;

(* The covariant derivative of the divergence of Rm in its fourth slot. *)

let RFA_LNABLA_D4 = prove
 (`!U (G:real^N->real^N^N) y u.
        metric_field U G /\ y IN U
        ==> lnabla 3 G
              (\z w. sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
                       matrix_inv(G z)$a$b *
                       lnabla 4 G (lrm4 G) z (rfa_ins 4 5 (basis a) (basis b) w))))
              y u =
            rfa_n3 G y (u 1) (u 3) (u 2) (u 4) - rfa_n3 G y (u 2) (u 3) (u 1) (u 4)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`3`; `G:real^N->real^N^N`; `G:real^N->real^N^N`;
    `\z w. sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
             matrix_inv((G:real^N->real^N^N) z)$a$b *
             lnabla 4 G (lrm4 G) z (rfa_ins 4 5 (basis a) (basis b) w)))`;
    `\z (w:num->real^N).
       lnabla 2 (G:real^N->real^N^N) (lric2 G) z (\m. w(swap(2,3) m)) -
       lnabla 2 G (lric2 G) z
         (\m. w(if m = 1 then 2 else if m = 2 then 3 else if m = 3 then 1 else m))`;
    `U:real^N->bool`; `y:real^N`; `u:num->real^N`] LRG_LNABLA_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`z:real^N`; `w:num->real^N`] THEN
    DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
        matrix_inv((G:real^N->real^N^N) z)$a$b *
        lnabla 4 G (lrm4 G) z (\m. if m = 1 then w 1 else if m = 2 then w 2 else if m = 3 then w 3 else if m = 4 then basis a else basis b)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
      BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN
      STRIP_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC RFA_N5_AGREE THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN RFA_TUPLE_TAC 5;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`;
                   `(w:num->real^N) 1`; `(w:num->real^N) 2`; `(w:num->real^N) 3`]
           RFA_LRM4_DIV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN BINOP_TAC THEN
    MATCH_MP_TAC RFA_N2_AGREE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN RFA_TUPLE_TAC 3;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRG_N2_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!v. (\x. lift(lnabla 2 (G:real^N->real^N^N) (lric2 G) x v)) differentiable at y`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LRG_LNABLA_SUB] THEN
  SUBGOAL_THEN `swap(2,3) permutes 1..3` ASSUME_TAC THENL
   [MATCH_MP_TAC PERMUTES_SWAP THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`3`; `G:real^N->real^N^N`; `lnabla 2 (G:real^N->real^N^N) (lric2 G)`;
                 `swap(2,3)`; `y:real^N`; `u:num->real^N`] LRG_LNABLA_PERMUTE) THEN
  MP_TAC(ISPECL [`3`; `G:real^N->real^N^N`; `lnabla 2 (G:real^N->real^N^N) (lric2 G)`;
                 `\m. if m = 1 then 2 else if m = 2 then 3 else if m = 3 then 1 else m`;
                 `y:real^N`; `u:num->real^N`] LRG_LNABLA_PERMUTE) THEN
  ASM_REWRITE_TAC[RFA_CYC3_PERMUTES] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[rfa_n3] THEN BINOP_TAC THEN
  MATCH_MP_TAC RFA_N3_AGREE THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN RFA_TUPLE_TAC 4);;

let RFA_LNABLA_D3 = prove
 (`!U (G:real^N->real^N^N) y u.
        metric_field U G /\ y IN U
        ==> lnabla 3 G
              (\z w. sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
                       matrix_inv(G z)$a$b *
                       lnabla 4 G (lrm4 G) z (rfa_ins 3 5 (basis a) (basis b) w))))
              y u =
            --(rfa_n3 G y (u 1) (u 3) (u 2) (u 4) - rfa_n3 G y (u 2) (u 3) (u 1) (u 4))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`3`; `G:real^N->real^N^N`; `G:real^N->real^N^N`;
    `\z w. sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
             matrix_inv((G:real^N->real^N^N) z)$a$b *
             lnabla 4 G (lrm4 G) z (rfa_ins 3 5 (basis a) (basis b) w)))`;
    `\z (w:num->real^N).
       lnabla 2 (G:real^N->real^N^N) (lric2 G) z
         (\m. w(if m = 1 then 2 else if m = 2 then 3 else if m = 3 then 1 else m)) -
       lnabla 2 G (lric2 G) z (\m. w(swap(2,3) m))`;
    `U:real^N->bool`; `y:real^N`; `u:num->real^N`] LRG_LNABLA_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`z:real^N`; `w:num->real^N`] THEN
    DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `--(sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
          matrix_inv((G:real^N->real^N^N) z)$a$b *
          lnabla 4 G (lrm4 G) z (\m. if m = 1 then w 1 else if m = 2 then w 2 else if m = 3 then w 3 else if m = 4 then basis a else basis b))))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM SUM_NEG] THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
      BETA_TAC THEN REWRITE_TAC[GSYM SUM_NEG] THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN
      STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC[GSYM REAL_MUL_RNEG] THEN
      AP_TERM_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `lnabla 4 (G:real^N->real^N^N) (lrm4 G) z (\m. if m = 1 then w 1 else if m = 2 then w 2 else if m = 3 then basis a else if m = 4 then w 3 else basis b)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC RFA_N5_AGREE THEN EXISTS_TAC `U:real^N->bool` THEN
        ASM_REWRITE_TAC[] THEN RFA_TUPLE_TAC 5;
        MATCH_MP_TAC RFA_N5_ANTI34_T THEN EXISTS_TAC `U:real^N->bool` THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`;
                   `(w:num->real^N) 1`; `(w:num->real^N) 2`; `(w:num->real^N) 3`]
           RFA_LRM4_DIV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `a = a' /\ b = b' ==> --(b - a) = a' - b'`) THEN
    CONJ_TAC THEN MATCH_MP_TAC RFA_N2_AGREE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN RFA_TUPLE_TAC 3;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRG_N2_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!v. (\x. lift(lnabla 2 (G:real^N->real^N^N) (lric2 G) x v)) differentiable at y`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LRG_LNABLA_SUB] THEN
  SUBGOAL_THEN `swap(2,3) permutes 1..3` ASSUME_TAC THENL
   [MATCH_MP_TAC PERMUTES_SWAP THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`3`; `G:real^N->real^N^N`; `lnabla 2 (G:real^N->real^N^N) (lric2 G)`;
                 `swap(2,3)`; `y:real^N`; `u:num->real^N`] LRG_LNABLA_PERMUTE) THEN
  MP_TAC(ISPECL [`3`; `G:real^N->real^N^N`; `lnabla 2 (G:real^N->real^N^N) (lric2 G)`;
                 `\m. if m = 1 then 2 else if m = 2 then 3 else if m = 3 then 1 else m`;
                 `y:real^N`; `u:num->real^N`] LRG_LNABLA_PERMUTE) THEN
  ASM_REWRITE_TAC[RFA_CYC3_PERMUTES] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[rfa_n3] THEN
  MATCH_MP_TAC(REAL_ARITH `a = a' /\ b = b' ==> a - b = --(b' - a')`) THEN
  CONJ_TAC THEN MATCH_MP_TAC RFA_N3_AGREE THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN RFA_TUPLE_TAC 4);;

let RFA_N6_BIANCHI_T = prove
 (`!U (G:real^N->real^N^N) y x1 x2 x3 x4 e f.
        metric_field U G /\ y IN U
        ==> lnabla_iter 4 2 (G:real^N->real^N^N) (lrm4 G) y (\m. if m = 1 then x1 else if m = 2 then x2 else if m = 3 then x3 else if m = 4 then x4 else if m = 5 then e else f) =
            --(lnabla_iter 4 2 G (lrm4 G) y (\m. if m = 1 then x1 else if m = 2 then x2 else if m = 3 then x4 else if m = 4 then e else if m = 5 then x3 else f)) - lnabla_iter 4 2 G (lrm4 G) y (\m. if m = 1 then x1 else if m = 2 then x2 else if m = 3 then e else if m = 4 then x3 else if m = 5 then x4 else f)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `(\m. if m = 1 then x1:real^N else if m = 2 then x2 else if m = 3 then x3 else if m = 4 then x4 else if m = 5 then e else f)`] RFA_N6_BIANCHI) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `b = b' /\ c = c' ==> a + b + c = &0 ==> a = --b' - c'`) THEN
  CONJ_TAC THEN MATCH_MP_TAC RFA_N6_AGREE THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN RFA_TUPLE_TAC 6);;

(* The rough Laplacian of Rm: second derivatives of Ric, and the Ricci     *)
(* identity defects of the second derivative of Rm (contracted).           *)

let RFA_LTLAP_LRM4 = prove
 (`!U (G:real^N->real^N^N) y x1 x2 x3 x4.
        metric_field U G /\ y IN U
        ==> ltlap 4 G (lrm4 G) y (\m. if m = 1 then x1 else if m = 2 then x2 else if m = 3 then x3 else x4) =
            --(rfa_n3 G y x1 x4 x2 x3 - rfa_n3 G y x2 x4 x1 x3) +
            (rfa_n3 G y x1 x3 x2 x4 - rfa_n3 G y x2 x3 x1 x4) -
            sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b. matrix_inv((G:real^N->real^N^N) y)$a$b * (lnabla_iter 4 2 G (lrm4 G) y (\m. if m = 1 then x1 else if m = 2 then x2 else if m = 3 then x4 else if m = 4 then basis a else if m = 5 then x3 else basis b) - lnabla_iter 4 2 G (lrm4 G) y (\m. if m = 1 then x1 else if m = 2 then x2 else if m = 3 then x4 else if m = 4 then basis a else if m = 5 then basis b else x3)))) - sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b. matrix_inv((G:real^N->real^N^N) y)$a$b * (lnabla_iter 4 2 G (lrm4 G) y (\m. if m = 1 then x1 else if m = 2 then x2 else if m = 3 then basis a else if m = 4 then x3 else if m = 5 then x4 else basis b) - lnabla_iter 4 2 G (lrm4 G) y (\m. if m = 1 then x1 else if m = 2 then x2 else if m = 3 then basis a else if m = 4 then x3 else if m = 5 then basis b else x4))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] RFA_N5_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ltlap 4 G (lrm4 G) y (\m. if m = 1 then x1 else if m = 2 then x2 else if m = 3 then x3 else x4) = sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b. matrix_inv((G:real^N->real^N^N) y)$a$b * lnabla_iter 4 2 G (lrm4 G) y (\m. if m = 1 then x1 else if m = 2 then x2 else if m = 3 then x3 else if m = 4 then x4 else if m = 5 then basis a else basis b)))` SUBST1_TAC THENL
   [REWRITE_TAC[ltlap] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN
    STRIP_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC RFA_N6_AGREE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN RFA_TUPLE_TAC 6;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. lnabla_iter 4 2 (G:real^N->real^N^N) (lrm4 G) y (\m. if m = 1 then x1 else if m = 2 then x2 else if m = 3 then x3 else if m = 4 then x4 else if m = 5 then basis a else basis b) =
          --(lnabla_iter 4 2 G (lrm4 G) y (\m. if m = 1 then x1 else if m = 2 then x2 else if m = 3 then x4 else if m = 4 then basis a else if m = 5 then x3 else basis b)) - lnabla_iter 4 2 G (lrm4 G) y (\m. if m = 1 then x1 else if m = 2 then x2 else if m = 3 then basis a else if m = 4 then x3 else if m = 5 then x4 else basis b)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC RFA_N6_BIANCHI_T THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_LDISTRIB; REAL_MUL_RNEG; SUM_SUB_NUMSEG; SUM_NEG] THEN
  SUBGOAL_THEN `sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b. matrix_inv((G:real^N->real^N^N) y)$a$b * lnabla_iter 4 2 G (lrm4 G) y (\m. if m = 1 then x1 else if m = 2 then x2 else if m = 3 then x4 else if m = 4 then basis a else if m = 5 then basis b else x3))) = rfa_n3 G y x1 x4 x2 x3 - rfa_n3 G y x2 x4 x1 x3`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`3`; `U:real^N->bool`; `G:real^N->real^N^N`;
                   `lnabla 4 (G:real^N->real^N^N) (lrm4 G)`; `4`; `5`; `y:real^N`;
                   `(\m. if m = 1 then x1:real^N else if m = 2 then x2 else if m = 3 then x4 else x3)`] RFA_LNABLA_CTR_AT) THEN
    ASM_REWRITE_TAC[ARITH] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                   `(\m. if m = 1 then x1:real^N else if m = 2 then x2 else if m = 3 then x4 else x3)`] RFA_LNABLA_D4) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ARITH] THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN
    STRIP_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `lnabla_iter 4 2 (G:real^N->real^N^N) (lrm4 G) y
                  (rfa_ins 4 5 (basis a) (basis b) (\m. if m = 1 then x1:real^N else if m = 2 then x2 else if m = 3 then x4 else x3))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RFA_N6_AGREE THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN RFA_TUPLE_TAC 6;
      REWRITE_TAC[RFA_LNABLA_ITER_2; ARITH]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b. matrix_inv((G:real^N->real^N^N) y)$a$b * lnabla_iter 4 2 G (lrm4 G) y (\m. if m = 1 then x1 else if m = 2 then x2 else if m = 3 then basis a else if m = 4 then x3 else if m = 5 then basis b else x4))) = --(rfa_n3 G y x1 x3 x2 x4 - rfa_n3 G y x2 x3 x1 x4)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`3`; `U:real^N->bool`; `G:real^N->real^N^N`;
                   `lnabla 4 (G:real^N->real^N^N) (lrm4 G)`; `3`; `5`; `y:real^N`;
                   `(\m. if m = 1 then x1:real^N else if m = 2 then x2 else if m = 3 then x3 else x4)`] RFA_LNABLA_CTR_AT) THEN
    ASM_REWRITE_TAC[ARITH] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                   `(\m. if m = 1 then x1:real^N else if m = 2 then x2 else if m = 3 then x3 else x4)`] RFA_LNABLA_D3) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ARITH] THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN
    STRIP_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `lnabla_iter 4 2 (G:real^N->real^N^N) (lrm4 G) y
                  (rfa_ins 3 5 (basis a) (basis b) (\m. if m = 1 then x1:real^N else if m = 2 then x2 else if m = 3 then x3 else x4))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RFA_N6_AGREE THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN RFA_TUPLE_TAC 6;
      REWRITE_TAC[RFA_LNABLA_ITER_2; ARITH]];
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The evolution of Rm, exact form: d/dt Rm = Lap Rm + reaction              *)
(* terms (Ric * Rm, the Ricci identity defects of nabla^2 Ric and of        *)
(* nabla^2 Rm).                                                               *)
(* ========================================================================= *)

let RFA_LRM4_EVOL_EXACT = prove
 (`!U a b (G:real->real^N->real^N^N) t y x1 x2 x3 x4.
        lricci_flow U a b G /\ a < t /\ t < b /\ y IN U
        ==> ((\s. lrm4 (G s) y (\m. if m = 1 then x1:real^N else if m = 2 then x2 else if m = 3 then x3 else x4)) has_real_derivative
             ltlap 4 (G t) (lrm4 (G t)) y (\m. if m = 1 then x1:real^N else if m = 2 then x2 else if m = 3 then x3 else x4) + (--(&2) * lricci (G t) y x3 (lriemann (G t) y x1 x2 x4) + (rfa_n3 (G t) y x4 x3 x1 x2 - rfa_n3 (G t) y x4 x3 x2 x1) + (rfa_n3 (G t) y x1 x4 x2 x3 - rfa_n3 (G t) y x1 x4 x3 x2) + (rfa_n3 (G t) y x2 x4 x3 x1 - rfa_n3 (G t) y x2 x4 x1 x3) + (rfa_n3 (G t) y x1 x3 x4 x2 - rfa_n3 (G t) y x1 x3 x2 x4) + (rfa_n3 (G t) y x2 x3 x1 x4 - rfa_n3 (G t) y x2 x3 x4 x1) + sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b. matrix_inv(G t y)$a$b * (lnabla_iter 4 2 (G t) (lrm4 (G t)) y (\m. if m = 1 then x1 else if m = 2 then x2 else if m = 3 then x4 else if m = 4 then basis a else if m = 5 then x3 else basis b) - lnabla_iter 4 2 (G t) (lrm4 (G t)) y (\m. if m = 1 then x1 else if m = 2 then x2 else if m = 3 then x4 else if m = 4 then basis a else if m = 5 then basis b else x3)))) + sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b. matrix_inv(G t y)$a$b * (lnabla_iter 4 2 (G t) (lrm4 (G t)) y (\m. if m = 1 then x1 else if m = 2 then x2 else if m = 3 then basis a else if m = 4 then x3 else if m = 5 then x4 else basis b) - lnabla_iter 4 2 (G t) (lrm4 (G t)) y (\m. if m = 1 then x1 else if m = 2 then x2 else if m = 3 then basis a else if m = 4 then x3 else if m = 5 then basis b else x4)))))) (atreal t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t)` ASSUME_TAC THENL
   [ASM_MESON_TAC[lricci_flow]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `t:real`; `y:real^N`; `(\m. if m = 1 then x1:real^N else if m = 2 then x2 else if m = 3 then x3 else x4)`] RFA_LRM4_DT_N3) THEN
  ASM_REWRITE_TAC[ARITH] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `y:real^N`;
                 `x1:real^N`; `x2:real^N`; `x3:real^N`; `x4:real^N`] RFA_LTLAP_LRM4) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC(MESON[]
   `(x:real) = y ==> (f has_real_derivative x) net
                   ==> (f has_real_derivative y) net`) THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The reaction terms of the evolution of Rm are a member of                 *)
(* the class lbilin 4 4 4.                                                   *)
(* ========================================================================= *)

(* Ric as a contraction of a permutation of Rm. *)

let RFA_LRIC2_CONTR = prove
 (`!U (G:real^N->real^N^N) y u.
        metric_field U G /\ y IN U
        ==> lric2 G y u = ltcontr G (ltperm (swap(2,3)) (lrm4 G)) y u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lric2; ltcontr; ltperm] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `(u:num->real^N) 1`; `(u:num->real^N) 2`] LRG_LRM4_CONTRACT13) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN
  STRIP_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[lrm4; swap; ARITH]);;

(* Ric(x3, R(x1,x2) x4) expanded against the metric. *)

let RFA_RIC_RM_EXPAND = prove
 (`!U (G:real^N->real^N^N) y x1 x2 x3 x4.
        metric_field U G /\ y IN U
        ==> lricci G y x3 (lriemann G y x1 x2 x4) =
            sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
              matrix_inv(G y)$a$b * lrm4 G y (\m. if m = 1 then x1 else if m = 2 then x2 else if m = 3 then basis a else x4) *
              lric2 G y (\m. if m = 1 then x3 else basis b)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`; `lric2(G:real^N->real^N^N)`;
                 `y:real^N`; `2`; `\m:num. x3:real^N`;
                 `lriemann (G:real^N->real^N^N) y x1 x2 x4`] RFA_METRIC_EXPAND) THEN
  ASM_SIMP_TAC[LRG_LRIC2_FIELD; ARITH] THEN
  REWRITE_TAC[lric2; lrm4; ARITH] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN
  STRIP_TAC THEN BETA_TAC THEN REWRITE_TAC[ARITH]);;

(* The Ric * Rm operator in the class. *)

let RFA_E1_LBILIN = prove
 (`lbilin_on 4 4 2
     (\(G:real^N->real^N^N) (sf:real^N->(num->real^N)->real)
       (tf:real^N->(num->real^N)->real) y u.
        sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
          matrix_inv(G y)$a$b *
          sf y (\m. if m = 1 then u 1 else if m = 2 then u 2 else if m = 3 then basis a
                    else u 4) *
          tf y (\m. if m = 1 then u 3 else basis b))))`,
  MP_TAC(ISPECL [`4`; `4`; `2`; `3`; `6`;
    `\(G:real^N->real^N^N) (sf:real^N->(num->real^N)->real)
      (tf:real^N->(num->real^N)->real). ltprod 4 sf tf`] RFA_LBILIN_ON_CTR_AT) THEN
  REWRITE_TAC[ARITH; ARITH_RULE `4 + 2 = 6`] THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`4`; `2`] RFA_LBILIN_ON_PROD) THEN REWRITE_TAC[ARITH];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `swap(3,4)` o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    (ISPECL [`4`; `4`; `2`] RFA_LBILIN_ON_PERM))) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC PERMUTES_SWAP THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    DISCH_TAC] THEN
  MATCH_MP_TAC RFA_LBILIN_ON_EQ THEN
  FIRST_ASSUM(fun th -> EXISTS_TAC (rand(concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `G:real^N->real^N^N`;
                       `sf:real^N->(num->real^N)->real`;
                       `tf:real^N->(num->real^N)->real`; `y:real^N`;
                       `u:num->real^N`] THEN
  STRIP_TAC THEN REWRITE_TAC[ltperm; ltprod] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN
  STRIP_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN BINOP_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `y:real^N` o GEN_REWRITE_RULE I [ltensor_field] o
      check (fun th -> concl th = `ltensor_field 4 U (sf:real^N->(num->real^N)->real)`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    RFA_TUPLE_TAC 4;
    FIRST_ASSUM(MP_TAC o SPEC `y:real^N` o GEN_REWRITE_RULE I [ltensor_field] o
      check (fun th -> concl th = `ltensor_field 2 U (tf:real^N->(num->real^N)->real)`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    RFA_TUPLE_TAC 2]);;

let RFA_PI1_PERMUTES = prove
 (`(\m. if m = 1 then 4 else if m = 2 then 3 else if m = 3 then 1 else if m = 4 then 2 else m) permutes 1..4`,
  MATCH_MP_TAC PERMUTES_BIJECTIONS THEN
  EXISTS_TAC `\m. if m = 1 then 3 else if m = 2 then 4 else if m = 3 then 2 else if m = 4 then 1 else m` THEN
  REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC);;

let RFA_PI2_PERMUTES = prove
 (`(\m. if m = 1 then 1 else if m = 2 then 4 else if m = 3 then 2 else if m = 4 then 3 else m) permutes 1..4`,
  MATCH_MP_TAC PERMUTES_BIJECTIONS THEN
  EXISTS_TAC `\m. if m = 1 then 1 else if m = 2 then 3 else if m = 3 then 4 else if m = 4 then 2 else m` THEN
  REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC);;

let RFA_PI3_PERMUTES = prove
 (`(\m. if m = 1 then 2 else if m = 2 then 4 else if m = 3 then 3 else if m = 4 then 1 else m) permutes 1..4`,
  MATCH_MP_TAC PERMUTES_BIJECTIONS THEN
  EXISTS_TAC `\m. if m = 1 then 4 else if m = 2 then 1 else if m = 3 then 3 else if m = 4 then 2 else m` THEN
  REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC);;

let RFA_PI4_PERMUTES = prove
 (`(\m. if m = 1 then 1 else if m = 2 then 3 else if m = 3 then 4 else if m = 4 then 2 else m) permutes 1..4`,
  MATCH_MP_TAC PERMUTES_BIJECTIONS THEN
  EXISTS_TAC `\m. if m = 1 then 1 else if m = 2 then 4 else if m = 3 then 2 else if m = 4 then 3 else m` THEN
  REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC);;

let RFA_PI5_PERMUTES = prove
 (`(\m. if m = 1 then 2 else if m = 2 then 3 else if m = 3 then 1 else if m = 4 then 4 else m) permutes 1..4`,
  MATCH_MP_TAC PERMUTES_BIJECTIONS THEN
  EXISTS_TAC `\m. if m = 1 then 3 else if m = 2 then 1 else if m = 3 then 2 else if m = 4 then 4 else m` THEN
  REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC);;

(* The two Ricci identity defects in terms of the class members. *)

let RFA_RIC_DEFECT = prove
 (`!(B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) U (G:real^N->real^N^N) y a b c d.
        (!U (G:real^N->real^N^N) tf y u.
            metric_field U G /\ ltensor_field 2 U tf /\
            (!u. smooth_map_on U (\x. lift(tf x u))) /\ y IN U
            ==> lnabla_iter 2 2 G tf y u -
                lnabla_iter 2 2 G tf y
                  (\m. if m = 2 + 1 then u(2 + 2) else if m = 2 + 2 then u(2 + 1)
                       else u m) =
                B2 G (lrm4 G) tf y u) /\
        metric_field U G /\ y IN U
        ==> B2 G (lrm4 G) (lric2 G) y (\m. if m = 1 then a:real^N else if m = 2 then b else if m = 3 then c else d) =
            rfa_n3 G y a b c d - rfa_n3 G y a b d c`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ri") STRIP_ASSUME_TAC) THEN
  USE_THEN "ri" (MP_TAC o SPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                                 `lric2(G:real^N->real^N^N)`; `y:real^N`;
                                 `(\m. if m = 1 then a:real^N else if m = 2 then b else if m = 3 then c else d)`]) THEN
  ASM_SIMP_TAC[LRG_LRIC2_FIELD] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[RFA_LNABLA_ITER_2; ARITH; rfa_n3] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC RFA_N3_AGREE THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN RFA_TUPLE_TAC 4);;

let RFA_RM_DEFECT = prove
 (`!(B4:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) U (G:real^N->real^N^N) y w1 w2 w3 w4 w5 w6.
        (!U (G:real^N->real^N^N) tf y u.
            metric_field U G /\ ltensor_field 4 U tf /\
            (!u. smooth_map_on U (\x. lift(tf x u))) /\ y IN U
            ==> lnabla_iter 4 2 G tf y u -
                lnabla_iter 4 2 G tf y
                  (\m. if m = 4 + 1 then u(4 + 2) else if m = 4 + 2 then u(4 + 1)
                       else u m) =
                B4 G (lrm4 G) tf y u) /\
        metric_field U G /\ y IN U
        ==> B4 G (lrm4 G) (lrm4 G) y (\m. if m = 1 then w1 else if m = 2 then w2 else if m = 3 then w3 else if m = 4 then w4 else if m = 5 then w5 else w6) =
            lnabla_iter 4 2 G (lrm4 G) y (\m. if m = 1 then w1 else if m = 2 then w2 else if m = 3 then w3 else if m = 4 then w4 else if m = 5 then w5 else w6) -
            lnabla_iter 4 2 G (lrm4 G) y (\m. if m = 1 then w1 else if m = 2 then w2 else if m = 3 then w3 else if m = 4 then w4 else if m = 5 then w6 else w5)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ri") STRIP_ASSUME_TAC) THEN
  USE_THEN "ri" (MP_TAC o SPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                                 `lrm4(G:real^N->real^N^N)`; `y:real^N`;
                                 `(\m. if m = 1 then w1:real^N else if m = 2 then w2 else if m = 3 then w3 else if m = 4 then w4 else if m = 5 then w5 else w6)`]) THEN
  ASM_SIMP_TAC[LRM4_TENSOR_FIELD] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[ARITH] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC RFA_N6_AGREE THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN RFA_TUPLE_TAC 6);;

(* The reaction operator is in the class. *)

let RFA_A8_E_LBILIN = prove
 (`!(B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) (B4:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real).
        lbilin 4 4 2 B2 /\ lbilin 6 4 4 B4
        ==> lbilin_on 4 4 4
              (\(G:real^N->real^N^N) (sf:real^N->(num->real^N)->real) (tf:real^N->(num->real^N)->real) y u.
    --(&2) * (\(G:real^N->real^N^N) (sf:real^N->(num->real^N)->real)
       (tf:real^N->(num->real^N)->real) y u.
        sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
          matrix_inv(G y)$a$b *
          sf y (\m. if m = 1 then u 1 else if m = 2 then u 2 else if m = 3 then basis a
                    else u 4) *
          tf y (\m. if m = 1 then u 3 else basis b)))) G sf (ltcontr G (ltperm (swap(2,3)) tf)) y u +
    ltperm (\m. if m = 1 then 4 else if m = 2 then 3 else if m = 3 then 1 else if m = 4 then 2 else m) ((B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G sf (ltcontr G (ltperm (swap(2,3)) tf))) y u +
    ltperm (\m. if m = 1 then 1 else if m = 2 then 4 else if m = 3 then 2 else if m = 4 then 3 else m) ((B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G sf (ltcontr G (ltperm (swap(2,3)) tf))) y u +
    ltperm (\m. if m = 1 then 2 else if m = 2 then 4 else if m = 3 then 3 else if m = 4 then 1 else m) ((B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G sf (ltcontr G (ltperm (swap(2,3)) tf))) y u +
    ltperm (\m. if m = 1 then 1 else if m = 2 then 3 else if m = 3 then 4 else if m = 4 then 2 else m) ((B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G sf (ltcontr G (ltperm (swap(2,3)) tf))) y u +
    ltperm (\m. if m = 1 then 2 else if m = 2 then 3 else if m = 3 then 1 else if m = 4 then 4 else m) ((B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G sf (ltcontr G (ltperm (swap(2,3)) tf))) y u +
    ltperm (swap(3,4)) (\y u. sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b. matrix_inv(G y)$a$b * (B4:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G sf tf y (rfa_ins 4 6 (basis a) (basis b) u)))) y u +
    sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b. matrix_inv(G y)$a$b * (B4:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G sf tf y (rfa_ins 3 6 (basis a) (basis b) u))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lbilin_on 4 4 4 (\(G:real^N->real^N^N) (sf:real^N->(num->real^N)->real) (tf:real^N->(num->real^N)->real). (B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G sf (ltcontr G (ltperm (swap(2,3)) tf)))` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP RFA_LBILIN_ON_SUBST2_CONTR
      (MATCH_MP RFA_LBILIN_ON_LBILIN (ASSUME `lbilin 4 4 2 (B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real)`))) THEN
    REWRITE_TAC[ARITH] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`4`; `4`; `4`; `swap(2,3)`;
      `\(G:real^N->real^N^N) (sf:real^N->(num->real^N)->real)
        (tf:real^N->(num->real^N)->real). (B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G sf (ltcontr G tf)`]
      RFA_LBILIN_ON_SUBST2_PERM) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [MATCH_MP_TAC PERMUTES_SWAP THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
      REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `lbilin_on (4 + 2) 4 4 (B4:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real)` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH] THEN MATCH_MP_TAC RFA_LBILIN_ON_LBILIN THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC RFA_LBILIN_ON_ADD THEN CONJ_TAC) THENL
   [MATCH_MP_TAC RFA_LBILIN_ON_CMUL THEN
    MP_TAC(MATCH_MP RFA_LBILIN_ON_SUBST2_CONTR RFA_E1_LBILIN) THEN
    REWRITE_TAC[ARITH] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`4`; `4`; `4`; `swap(2,3)`] RFA_LBILIN_ON_SUBST2_PERM) THEN
    DISCH_THEN(MP_TAC o C MATCH_MP (CONJ (ASSUME (concl(REWRITE_RULE[ARITH]
      (MATCH_MP RFA_LBILIN_ON_SUBST2_CONTR RFA_E1_LBILIN))))
      (prove(`swap(2,3) permutes 1..4`,
             MATCH_MP_TAC PERMUTES_SWAP THEN REWRITE_TAC[IN_NUMSEG] THEN
             ARITH_TAC)))) THEN
    REWRITE_TAC[];
    REWRITE_TAC[ETA_AX] THEN
    MP_TAC(ISPECL [`4`; `4`; `4`; `(\m. if m = 1 then 4 else if m = 2 then 3 else if m = 3 then 1 else if m = 4 then 2 else m)`; `\(G:real^N->real^N^N) (sf:real^N->(num->real^N)->real) (tf:real^N->(num->real^N)->real). (B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G sf (ltcontr G (ltperm (swap(2,3)) tf))`] RFA_LBILIN_ON_PERM) THEN
    REWRITE_TAC[RFA_PI1_PERMUTES] THEN ANTS_TAC THENL
     [MATCH_ACCEPT_TAC (ASSUME `lbilin_on 4 4 4 (\(G:real^N->real^N^N) (sf:real^N->(num->real^N)->real) (tf:real^N->(num->real^N)->real). (B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G sf (ltcontr G (ltperm (swap(2,3)) tf)))`); REWRITE_TAC[]];
    REWRITE_TAC[ETA_AX] THEN
    MP_TAC(ISPECL [`4`; `4`; `4`; `(\m. if m = 1 then 1 else if m = 2 then 4 else if m = 3 then 2 else if m = 4 then 3 else m)`; `\(G:real^N->real^N^N) (sf:real^N->(num->real^N)->real) (tf:real^N->(num->real^N)->real). (B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G sf (ltcontr G (ltperm (swap(2,3)) tf))`] RFA_LBILIN_ON_PERM) THEN
    REWRITE_TAC[RFA_PI2_PERMUTES] THEN ANTS_TAC THENL
     [MATCH_ACCEPT_TAC (ASSUME `lbilin_on 4 4 4 (\(G:real^N->real^N^N) (sf:real^N->(num->real^N)->real) (tf:real^N->(num->real^N)->real). (B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G sf (ltcontr G (ltperm (swap(2,3)) tf)))`); REWRITE_TAC[]];
    REWRITE_TAC[ETA_AX] THEN
    MP_TAC(ISPECL [`4`; `4`; `4`; `(\m. if m = 1 then 2 else if m = 2 then 4 else if m = 3 then 3 else if m = 4 then 1 else m)`; `\(G:real^N->real^N^N) (sf:real^N->(num->real^N)->real) (tf:real^N->(num->real^N)->real). (B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G sf (ltcontr G (ltperm (swap(2,3)) tf))`] RFA_LBILIN_ON_PERM) THEN
    REWRITE_TAC[RFA_PI3_PERMUTES] THEN ANTS_TAC THENL
     [MATCH_ACCEPT_TAC (ASSUME `lbilin_on 4 4 4 (\(G:real^N->real^N^N) (sf:real^N->(num->real^N)->real) (tf:real^N->(num->real^N)->real). (B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G sf (ltcontr G (ltperm (swap(2,3)) tf)))`); REWRITE_TAC[]];
    REWRITE_TAC[ETA_AX] THEN
    MP_TAC(ISPECL [`4`; `4`; `4`; `(\m. if m = 1 then 1 else if m = 2 then 3 else if m = 3 then 4 else if m = 4 then 2 else m)`; `\(G:real^N->real^N^N) (sf:real^N->(num->real^N)->real) (tf:real^N->(num->real^N)->real). (B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G sf (ltcontr G (ltperm (swap(2,3)) tf))`] RFA_LBILIN_ON_PERM) THEN
    REWRITE_TAC[RFA_PI4_PERMUTES] THEN ANTS_TAC THENL
     [MATCH_ACCEPT_TAC (ASSUME `lbilin_on 4 4 4 (\(G:real^N->real^N^N) (sf:real^N->(num->real^N)->real) (tf:real^N->(num->real^N)->real). (B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G sf (ltcontr G (ltperm (swap(2,3)) tf)))`); REWRITE_TAC[]];
    REWRITE_TAC[ETA_AX] THEN
    MP_TAC(ISPECL [`4`; `4`; `4`; `(\m. if m = 1 then 2 else if m = 2 then 3 else if m = 3 then 1 else if m = 4 then 4 else m)`; `\(G:real^N->real^N^N) (sf:real^N->(num->real^N)->real) (tf:real^N->(num->real^N)->real). (B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G sf (ltcontr G (ltperm (swap(2,3)) tf))`] RFA_LBILIN_ON_PERM) THEN
    REWRITE_TAC[RFA_PI5_PERMUTES] THEN ANTS_TAC THENL
     [MATCH_ACCEPT_TAC (ASSUME `lbilin_on 4 4 4 (\(G:real^N->real^N^N) (sf:real^N->(num->real^N)->real) (tf:real^N->(num->real^N)->real). (B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G sf (ltcontr G (ltperm (swap(2,3)) tf)))`); REWRITE_TAC[]];
    REWRITE_TAC[ETA_AX] THEN
    MP_TAC(ISPECL [`4`; `4`; `4`; `4`; `6`; `B4:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real`] RFA_LBILIN_ON_CTR_AT) THEN
    ASM_REWRITE_TAC[ARITH] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`4`; `4`; `4`; `swap(3,4)`;
      `\(G:real^N->real^N^N) (tf:real^N->(num->real^N)->real)
        (tg:real^N->(num->real^N)->real) y u.
         sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
           matrix_inv(G y)$a$b *
           (B4:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) G tf tg y (rfa_ins 4 6 (basis a) (basis b) u)))`]
      RFA_LBILIN_ON_PERM) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [MATCH_MP_TAC PERMUTES_SWAP THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
      REWRITE_TAC[]];
    MP_TAC(ISPECL [`4`; `4`; `4`; `3`; `6`; `B4:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real`] RFA_LBILIN_ON_CTR_AT) THEN
    ASM_REWRITE_TAC[ARITH]]);;

(* The evolution of Rm (RFA_LRM4_EVOLUTION). *)

let RFA_LRM4_EVOLUTION = prove
 (`?B. lbilin 4 4 4 B /\
       !U a b (G:real->real^N->real^N^N) t y u.
          lricci_flow U a b G /\ a < t /\ t < b /\ y IN U
          ==> ((\s. lrm4 (G s) y u) has_real_derivative
               ltlap 4 (G t) (lrm4 (G t)) y u +
               B (G t) (lrm4 (G t)) (lrm4 (G t)) y u) (atreal t)`,
  MP_TAC(SPEC `2` RFA_RICCI_IDENTITY_LB) THEN
  DISCH_THEN(X_CHOOSE_THEN `B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real` (CONJUNCTS_THEN2
    (ASSUME_TAC o REWRITE_RULE[ARITH]) (LABEL_TAC "ri2"))) THEN
  MP_TAC(SPEC `4` RFA_RICCI_IDENTITY_LB) THEN
  DISCH_THEN(X_CHOOSE_THEN `B4:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real` (CONJUNCTS_THEN2
    (ASSUME_TAC o REWRITE_RULE[ARITH]) (LABEL_TAC "ri4"))) THEN
  MP_TAC(ISPECL [`B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real`; `B4:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real`] RFA_A8_E_LBILIN) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[lbilin_on] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "agree"))) THEN
  EXISTS_TAC `B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t)` ASSUME_TAC THENL
   [ASM_MESON_TAC[lricci_flow]; ALL_TAC] THEN
  SUBGOAL_THEN `(\s. lrm4 ((G:real->real^N->real^N^N) s) y u) =
                (\s. lrm4 (G s) y (\m. if m = 1 then (u:num->real^N) 1 else if m = 2 then u 2 else if m = 3 then u 3 else u 4))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; lrm4; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `ltlap 4 ((G:real->real^N->real^N^N) t) (lrm4 ((G:real->real^N->real^N^N) t)) y u = ltlap 4 (G t) (lrm4 (G t)) y (\m. if m = 1 then (u:num->real^N) 1 else if m = 2 then u 2 else if m = 3 then u 3 else u 4)`
  SUBST1_TAC THENL
   [REWRITE_TAC[ltlap] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN
    STRIP_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC RFA_N6_AGREE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN RFA_TUPLE_TAC 6;
    ALL_TAC] THEN
  SUBGOAL_THEN `(B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) ((G:real->real^N->real^N^N) t) (lrm4 ((G:real->real^N->real^N^N) t)) (lrm4 ((G:real->real^N->real^N^N) t)) y u =
                B (G t) (lrm4 (G t)) (lrm4 (G t)) y (\m. if m = 1 then (u:num->real^N) 1 else if m = 2 then u 2 else if m = 3 then u 3 else u 4)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`4`; `4`; `4`; `B:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real`; `U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                   `lrm4 ((G:real->real^N->real^N^N) t)`; `lrm4 ((G:real->real^N->real^N^N) t)`] RFA_LBILIN_TENSOR_ALT) THEN
    ASM_SIMP_TAC[LRM4_TENSOR_FIELD] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N` o GEN_REWRITE_RULE I [ltensor_field]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    RFA_TUPLE_TAC 4;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `t:real`; `y:real^N`; `(u:num->real^N) 1`; `(u:num->real^N) 2`;
                 `(u:num->real^N) 3`; `(u:num->real^N) 4`] RFA_LRM4_EVOL_EXACT) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[]
   `(x:real) = y ==> (f has_real_derivative x) net
                   ==> (f has_real_derivative y) net`) THEN
  AP_TERM_TAC THEN
  USE_THEN "agree" (MP_TAC o SPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `lrm4 ((G:real->real^N->real^N^N) t)`; `lrm4 ((G:real->real^N->real^N^N) t)`;
                                    `y:real^N`; `(\m. if m = 1 then (u:num->real^N) 1 else if m = 2 then u 2 else if m = 3 then u 3 else u 4)`]) THEN
  ASM_SIMP_TAC[LRM4_TENSOR_FIELD] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH
   `x1 = y1 /\ x2 = y2 /\ x3 = y3 /\ x4 = y4 /\ x5 = y5 /\ x6 = y6 /\ x7 = y7 /\
    x8 = y8 ==> y1 + y2 + y3 + y4 + y5 + y6 + y7 + y8 =
                x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8`) THEN
  REPEAT CONJ_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[ARITH] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `y:real^N`; `(u:num->real^N) 1`;
                   `(u:num->real^N) 2`; `(u:num->real^N) 3`; `(u:num->real^N) 4`]
           RFA_RIC_RM_EXPAND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN
    STRIP_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC RFA_LRIC2_CONTR THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[ltperm] THEN
    MP_TAC(ISPECL [`4`; `4`; `2`; `B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real`] RFA_LBILIN_LOCAL) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`(G:real->real^N->real^N^N) t`; `(G:real->real^N->real^N^N) t`; `lrm4 ((G:real->real^N->real^N^N) t)`; `lrm4 ((G:real->real^N->real^N^N) t)`;
      `ltcontr ((G:real->real^N->real^N^N) t) (\y u. lrm4 ((G:real->real^N->real^N^N) t) y (\m. u(swap(2,3) m)))`; `lric2 ((G:real->real^N->real^N^N) t)`; `y:real^N`]) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `w:num->real^N` THEN
      CONV_TAC SYM_CONV THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `y:real^N`;
                     `w:num->real^N`] RFA_LRIC2_CONTR) THEN
      ASM_REWRITE_TAC[ltperm];
      DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) ((G:real->real^N->real^N^N) t) (lrm4 ((G:real->real^N->real^N^N) t)) (lric2 ((G:real->real^N->real^N^N) t)) y
                  (\m. if m = 1 then u 4 else if m = 2 then u 3 else if m = 3 then u 1 else u 2)` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`4`; `4`; `2`; `B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real`; `U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                     `lrm4 ((G:real->real^N->real^N^N) t)`; `lric2 ((G:real->real^N->real^N^N) t)`] RFA_LBILIN_TENSOR_ALT) THEN
      ASM_SIMP_TAC[LRM4_TENSOR_FIELD; LRG_LRIC2_FIELD] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^N` o GEN_REWRITE_RULE I [ltensor_field]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
      RFA_TUPLE_TAC 4;
      MATCH_MP_TAC RFA_RIC_DEFECT THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[ltperm] THEN
    MP_TAC(ISPECL [`4`; `4`; `2`; `B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real`] RFA_LBILIN_LOCAL) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`(G:real->real^N->real^N^N) t`; `(G:real->real^N->real^N^N) t`; `lrm4 ((G:real->real^N->real^N^N) t)`; `lrm4 ((G:real->real^N->real^N^N) t)`;
      `ltcontr ((G:real->real^N->real^N^N) t) (\y u. lrm4 ((G:real->real^N->real^N^N) t) y (\m. u(swap(2,3) m)))`; `lric2 ((G:real->real^N->real^N^N) t)`; `y:real^N`]) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `w:num->real^N` THEN
      CONV_TAC SYM_CONV THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `y:real^N`;
                     `w:num->real^N`] RFA_LRIC2_CONTR) THEN
      ASM_REWRITE_TAC[ltperm];
      DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) ((G:real->real^N->real^N^N) t) (lrm4 ((G:real->real^N->real^N^N) t)) (lric2 ((G:real->real^N->real^N^N) t)) y
                  (\m. if m = 1 then u 1 else if m = 2 then u 4 else if m = 3 then u 2 else u 3)` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`4`; `4`; `2`; `B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real`; `U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                     `lrm4 ((G:real->real^N->real^N^N) t)`; `lric2 ((G:real->real^N->real^N^N) t)`] RFA_LBILIN_TENSOR_ALT) THEN
      ASM_SIMP_TAC[LRM4_TENSOR_FIELD; LRG_LRIC2_FIELD] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^N` o GEN_REWRITE_RULE I [ltensor_field]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
      RFA_TUPLE_TAC 4;
      MATCH_MP_TAC RFA_RIC_DEFECT THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[ltperm] THEN
    MP_TAC(ISPECL [`4`; `4`; `2`; `B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real`] RFA_LBILIN_LOCAL) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`(G:real->real^N->real^N^N) t`; `(G:real->real^N->real^N^N) t`; `lrm4 ((G:real->real^N->real^N^N) t)`; `lrm4 ((G:real->real^N->real^N^N) t)`;
      `ltcontr ((G:real->real^N->real^N^N) t) (\y u. lrm4 ((G:real->real^N->real^N^N) t) y (\m. u(swap(2,3) m)))`; `lric2 ((G:real->real^N->real^N^N) t)`; `y:real^N`]) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `w:num->real^N` THEN
      CONV_TAC SYM_CONV THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `y:real^N`;
                     `w:num->real^N`] RFA_LRIC2_CONTR) THEN
      ASM_REWRITE_TAC[ltperm];
      DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) ((G:real->real^N->real^N^N) t) (lrm4 ((G:real->real^N->real^N^N) t)) (lric2 ((G:real->real^N->real^N^N) t)) y
                  (\m. if m = 1 then u 2 else if m = 2 then u 4 else if m = 3 then u 3 else u 1)` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`4`; `4`; `2`; `B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real`; `U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                     `lrm4 ((G:real->real^N->real^N^N) t)`; `lric2 ((G:real->real^N->real^N^N) t)`] RFA_LBILIN_TENSOR_ALT) THEN
      ASM_SIMP_TAC[LRM4_TENSOR_FIELD; LRG_LRIC2_FIELD] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^N` o GEN_REWRITE_RULE I [ltensor_field]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
      RFA_TUPLE_TAC 4;
      MATCH_MP_TAC RFA_RIC_DEFECT THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[ltperm] THEN
    MP_TAC(ISPECL [`4`; `4`; `2`; `B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real`] RFA_LBILIN_LOCAL) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`(G:real->real^N->real^N^N) t`; `(G:real->real^N->real^N^N) t`; `lrm4 ((G:real->real^N->real^N^N) t)`; `lrm4 ((G:real->real^N->real^N^N) t)`;
      `ltcontr ((G:real->real^N->real^N^N) t) (\y u. lrm4 ((G:real->real^N->real^N^N) t) y (\m. u(swap(2,3) m)))`; `lric2 ((G:real->real^N->real^N^N) t)`; `y:real^N`]) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `w:num->real^N` THEN
      CONV_TAC SYM_CONV THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `y:real^N`;
                     `w:num->real^N`] RFA_LRIC2_CONTR) THEN
      ASM_REWRITE_TAC[ltperm];
      DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) ((G:real->real^N->real^N^N) t) (lrm4 ((G:real->real^N->real^N^N) t)) (lric2 ((G:real->real^N->real^N^N) t)) y
                  (\m. if m = 1 then u 1 else if m = 2 then u 3 else if m = 3 then u 4 else u 2)` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`4`; `4`; `2`; `B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real`; `U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                     `lrm4 ((G:real->real^N->real^N^N) t)`; `lric2 ((G:real->real^N->real^N^N) t)`] RFA_LBILIN_TENSOR_ALT) THEN
      ASM_SIMP_TAC[LRM4_TENSOR_FIELD; LRG_LRIC2_FIELD] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^N` o GEN_REWRITE_RULE I [ltensor_field]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
      RFA_TUPLE_TAC 4;
      MATCH_MP_TAC RFA_RIC_DEFECT THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[ltperm] THEN
    MP_TAC(ISPECL [`4`; `4`; `2`; `B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real`] RFA_LBILIN_LOCAL) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`(G:real->real^N->real^N^N) t`; `(G:real->real^N->real^N^N) t`; `lrm4 ((G:real->real^N->real^N^N) t)`; `lrm4 ((G:real->real^N->real^N^N) t)`;
      `ltcontr ((G:real->real^N->real^N^N) t) (\y u. lrm4 ((G:real->real^N->real^N^N) t) y (\m. u(swap(2,3) m)))`; `lric2 ((G:real->real^N->real^N^N) t)`; `y:real^N`]) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `w:num->real^N` THEN
      CONV_TAC SYM_CONV THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `y:real^N`;
                     `w:num->real^N`] RFA_LRIC2_CONTR) THEN
      ASM_REWRITE_TAC[ltperm];
      DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) ((G:real->real^N->real^N^N) t) (lrm4 ((G:real->real^N->real^N^N) t)) (lric2 ((G:real->real^N->real^N^N) t)) y
                  (\m. if m = 1 then u 2 else if m = 2 then u 3 else if m = 3 then u 1 else u 4)` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`4`; `4`; `2`; `B2:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real`; `U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                     `lrm4 ((G:real->real^N->real^N^N) t)`; `lric2 ((G:real->real^N->real^N^N) t)`] RFA_LBILIN_TENSOR_ALT) THEN
      ASM_SIMP_TAC[LRM4_TENSOR_FIELD; LRG_LRIC2_FIELD] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^N` o GEN_REWRITE_RULE I [ltensor_field]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
      RFA_TUPLE_TAC 4;
      MATCH_MP_TAC RFA_RIC_DEFECT THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[ltperm] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN
    STRIP_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(B4:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) ((G:real->real^N->real^N^N) t) (lrm4 ((G:real->real^N->real^N^N) t)) (lrm4 ((G:real->real^N->real^N^N) t)) y (\m. if m = 1 then u 1 else if m = 2 then u 2 else if m = 3 then u 4 else if m = 4 then basis a else if m = 5 then u 3 else basis b)` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`6`; `4`; `4`; `B4:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real`; `U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                     `lrm4 ((G:real->real^N->real^N^N) t)`; `lrm4 ((G:real->real^N->real^N^N) t)`] RFA_LBILIN_TENSOR_ALT) THEN
      ASM_SIMP_TAC[LRM4_TENSOR_FIELD] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^N` o GEN_REWRITE_RULE I [ltensor_field]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
      RFA_TUPLE_TAC 6;
      MATCH_MP_TAC RFA_RM_DEFECT THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN BINOP_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REWRITE_TAC[ARITH]];
    
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN
    STRIP_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(B4:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real) ((G:real->real^N->real^N^N) t) (lrm4 ((G:real->real^N->real^N^N) t)) (lrm4 ((G:real->real^N->real^N^N) t)) y (\m. if m = 1 then u 1 else if m = 2 then u 2 else if m = 3 then basis a else if m = 4 then u 3 else if m = 5 then u 4 else basis b)` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`6`; `4`; `4`; `B4:(real^N->real^N^N)->(real^N->(num->real^N)->real)->(real^N->(num->real^N)->real)->real^N->(num->real^N)->real`; `U:real^N->bool`; `(G:real->real^N->real^N^N) t`;
                     `lrm4 ((G:real->real^N->real^N^N) t)`; `lrm4 ((G:real->real^N->real^N^N) t)`] RFA_LBILIN_TENSOR_ALT) THEN
      ASM_SIMP_TAC[LRM4_TENSOR_FIELD] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^N` o GEN_REWRITE_RULE I [ltensor_field]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
      RFA_TUPLE_TAC 6;
      MATCH_MP_TAC RFA_RM_DEFECT THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN BINOP_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REWRITE_TAC[ARITH]]]);;

