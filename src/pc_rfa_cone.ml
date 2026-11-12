(* ========================================================================= *)
(* Unit pc_rfa_cone: MT Prop 4.22, the statement P2B_REQ_RFA_CONE_STATEMENT  *)
(* of pc_p2b_conereq, proved as RFA_P2B_REQ_CONE: a flow with sec >= 0 on    *)
(* (a,0] whose final slice carries a positive rho with Hess(rho^2/2) = g(0)  *)
(* is flat.  In charts Hess f = g gives df(R(X,Y)Z) = 0 (Ricci identity), so *)
(* planes containing grad f have zero curvature; a zero of R at time 0 gives *)
(* flatness by RFA_SPLIT_PT_END (ii); otherwise lambda = 0 on (a,0] and the  *)
(* parallel unit field of the split (RFA_PARALLEL_CHART_END) is parallel to  *)
(* grad f, against nabla grad f = id.                                        *)
(* ========================================================================= *)

needs "src/pc_rfa_splitend.ml";;
needs "src/pc_p2b_conereq.ml";;

prioritize_real();;
type_invention_error := true;;



(* ========================================================================= *)
(* Chart-level lemmas: Hess f = g kills df(R(X,Y)Z), excludes                *)
(* parallel unit fields orthogonal to the kernel of df; pointwise algebra    *)
(* of P = (R/2) g - Ric.                                                     *)
(* ========================================================================= *)

(* A function with Hess f = g on an open set: df(R(a,b)c) = 0 there (the   *)
(* Ricci identity for df, with nabla Hess f = nabla g = 0).                 *)

let RFA_HESS_METRIC_RM = prove
 (`!U (G:real^N->real^N^N) (f:real^N->real).
     metric_field U G /\ smooth_map_on U (\z. lift(f z)) /\
     (!y u. y IN U
            ==> lnabla 1 G (\z w. drop(frechet_derivative (\x. lift(f x)) (at z) (w 1))) y u =
                lmetric2 G y u)
     ==> !y a b c. y IN U
                   ==> drop(frechet_derivative (\x. lift(f x)) (at y)
                              (lriemann G y a b c)) = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `f:real^N->real`] LRG_DF_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `Tf = \z (w:num->real^N). drop(frechet_derivative (\x. lift((f:real^N->real) x)) (at z) (w 1))` THEN
  SUBGOAL_THEN `!v. lnabla_iter 1 2 (G:real^N->real^N^N) Tf y v = &0` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[RFA_LNABLA_ITER_2; ARITH_RULE `1 + 1 = 2`] THEN
    TRANS_TAC EQ_TRANS `lnabla 2 (G:real^N->real^N^N) (lmetric2 G) y v` THEN CONJ_TAC THENL
     [MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC LNABLA_METRIC THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`1`; `U:real^N->bool`; `G:real^N->real^N^N`; `Tf:real^N->(num->real^N)->real`;
                 `y:real^N`; `\m:num. if m = 1 then (c:real^N) else if m = 2 then a else b`]
         RFA_RICCI_IDENTITY) THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL; SUM_SING_NUMSEG; ARITH] THEN
  EXPAND_TAC "Tf" THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* No parallel unit field V with df orthogonal to V^perp can coexist with  *)
(* Hess f = g: on V^perp the Hessian would vanish (dimension >= 2).        *)

let RFA_HESS_METRIC_PARALLEL_FALSE = prove
 (`!U (G:real^N->real^N^N) (f:real^N->real) (V:real^N->real^N) y.
     metric_field U G /\ smooth_map_on U (\z. lift(f z)) /\ smooth_map_on U V /\ y IN U /\
     2 <= dimindex(:N) /\
     (!z u. z IN U
            ==> lnabla 1 G (\z w. drop(frechet_derivative (\x. lift(f x)) (at z) (w 1))) z u =
                lmetric2 G z u) /\
     (!z w. z IN U ==> frechet_derivative V (at z) w + christoffel G z w (V z) = vec 0) /\
     (!z w. z IN U /\ V z dot (G z ** w) = &0
            ==> drop(frechet_derivative (\x. lift(f x)) (at z) w) = &0) /\
     (!z. z IN U ==> V z dot (G z ** V z) = &1)
     ==> F`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "mf fsm vsm yU dim hess par perp unit" THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  ABBREV_TAC `D = \z w. drop(frechet_derivative (\x. lift((f:real^N->real) x)) (at z) w)` THEN
  SUBGOAL_THEN `!z. z IN U ==> linear (\w. lift((D:real^N->real^N->real) z w))` (LABEL_TAC "lin") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "D" THEN REWRITE_TAC[LIFT_DROP; ETA_AX] THEN
    MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `\x. lift((f:real^N->real) x)`; `z:real^N`;
                   `vec 0:real^N`] LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* df = s V-flat *)
  SUBGOAL_THEN
   `!z w. z IN U
          ==> (D:real^N->real^N->real) z w =
              D z (V z) * ((V:real^N->real^N) z dot ((G:real^N->real^N^N) z ** w))`
  (LABEL_TAC "flat") THENL
   [REPEAT STRIP_TAC THEN
    ABBREV_TAC `c = (V:real^N->real^N) z dot ((G:real^N->real^N^N) z ** w)` THEN
    SUBGOAL_THEN `w = c % (V:real^N->real^N) z + (w - c % V z)` SUBST1_TAC THENL
     [VECTOR_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "lin" (fun th -> ASSUME_TAC(MATCH_MP th (ASSUME `(z:real^N) IN U`))) THEN
    SUBGOAL_THEN `(D:real^N->real^N->real) z (c % (V:real^N->real^N) z + (w - c % V z)) =
                  c * D z (V z) + D z (w - c % V z)` SUBST1_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP LINEAR_ADD) THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP LINEAR_CMUL) THEN
      REWRITE_TAC[LIFT_EQ; GSYM LIFT_ADD; GSYM LIFT_CMUL] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(D:real^N->real^N->real) z (w - c % (V:real^N->real^N) z) = &0`
    SUBST1_TAC THENL
     [EXPAND_TAC "D" THEN USE_THEN "perp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; MATRIX_VECTOR_MUL_RMUL; DOT_RSUB; DOT_RMUL] THEN
      ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(V:real^N->real^N) z dot ((G:real^N->real^N^N) z **
                    (c % V z + (w - c % V z))) = c`
    SUBST1_TAC THENL [REWRITE_TAC[VECTOR_ARITH `c % v + (w - c % v) = w:real^N`] THEN
                      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* s = df(V) is differentiable at y *)
  SUBGOAL_THEN `(\z. lift((D:real^N->real^N->real) z ((V:real^N->real^N) z))) differentiable at y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `\z. lift(sum(1..dimindex(:N))
                       (\k. (V:real^N->real^N) z$k * (D:real^N->real^N->real) z (basis k)))` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
      USE_THEN "lin" (MP_TAC o MATCH_MP LRG_LINEAR_DROP_EXPAND o
        C MATCH_MP (ASSUME `(z:real^N) IN U`)) THEN
      REWRITE_TAC[LIFT_DROP] THEN SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "D" THEN REWRITE_TAC[LIFT_DROP] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* a nonzero w orthogonal to V(y) *)
  SUBGOAL_THEN `?w:real^N. ~(w = vec 0) /\ (V:real^N->real^N) y dot ((G:real^N->real^N^N) y ** w) = &0`
  STRIP_ASSUME_TAC THENL
   [ABBREV_TAC `c1 = (V:real^N->real^N) y dot ((G:real^N->real^N^N) y ** basis 1)` THEN
    ABBREV_TAC `c2 = (V:real^N->real^N) y dot ((G:real^N->real^N^N) y ** basis 2)` THEN
    ASM_CASES_TAC `c1 = &0` THENL
     [EXISTS_TAC `basis 1:real^N` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC BASIS_NONZERO THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    EXISTS_TAC `c2 % basis 1 - c1 % basis 2:real^N` THEN CONJ_TAC THENL
     [DISCH_THEN(MP_TAC o AP_TERM `\v:real^N. v$2`) THEN
      SUBGOAL_THEN `1 <= 2 /\ 2 <= dimindex(:N)` STRIP_ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; VEC_COMPONENT] THEN
      REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; MATRIX_VECTOR_MUL_RMUL; DOT_RSUB; DOT_RMUL] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the derivative of z |-> df(z)(w) at y in the direction w *)
  SUBGOAL_THEN
   `drop(frechet_derivative (\z. lift((D:real^N->real^N->real) z w)) (at y) w) =
    D y ((V:real^N->real^N) y) *
    (V y dot ((G:real^N->real^N^N) y ** christoffel G y w w))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `frechet_derivative (\z. lift((D:real^N->real^N->real) z w)) (at y) =
      frechet_derivative (\z. D z ((V:real^N->real^N) z) %
                              lift(V z dot ((G:real^N->real^N^N) z ** w))) (at y)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[GSYM LIFT_CMUL] THEN AP_TERM_TAC THEN
      USE_THEN "flat" (fun th -> ACCEPT_TAC(MP (SPECL [`z:real^N`; `w:real^N`] th)
                                               (ASSUME `(z:real^N) IN U`)));
      ALL_TAC] THEN
    SUBGOAL_THEN `(\z. lift((V:real^N->real^N) z dot ((G:real^N->real^N^N) z ** w)))
                  differentiable at y`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `\z:real^N. (w:real^N)`]
             LRG_SMOOTH_MATVEC) THEN
      REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[metric_field];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`\z. (D:real^N->real^N->real) z ((V:real^N->real^N) z)`;
      `\h. drop(frechet_derivative (\z. lift((D:real^N->real^N->real) z ((V:real^N->real^N) z)))
                                   (at y) h)`;
      `\z. lift((V:real^N->real^N) z dot ((G:real^N->real^N^N) z ** w))`;
      `frechet_derivative (\z. lift((V:real^N->real^N) z dot ((G:real^N->real^N^N) z ** w)))
                          (at y)`;
      `y:real^N`] HAS_DERIVATIVE_MUL_AT) THEN
    REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    REWRITE_TAC[ASSUME `(V:real^N->real^N) y dot ((G:real^N->real^N^N) y ** w) = &0`;
                LIFT_NUM; VECTOR_MUL_RZERO; VECTOR_ADD_RID; DROP_CMUL] THEN
    AP_TERM_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `\z:real^N. (w:real^N)`;
                   `V:real^N->real^N`; `\z:real^N. (w:real^N)`; `y:real^N`] LCOVD_METRIC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST]; ALL_TAC] THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[lcovd; LIFT_DROP; FRECHET_DERIVATIVE_CONST_AT; VECTOR_ADD_LID] THEN
    USE_THEN "par" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(y:real^N) IN U`)]) THEN
    REWRITE_TAC[DOT_LZERO; REAL_ADD_LID];
    ALL_TAC] THEN
  (* Hess(w,w) = 0 against Hess(w,w) = g(w,w) > 0 *)
  SUBGOAL_THEN `&0 < w dot ((G:real^N->real^N^N) y ** w)` ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_METRIC_POS THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(D:real^N->real^N->real) y (christoffel (G:real^N->real^N^N) y w w) =
    D y ((V:real^N->real^N) y) * (V y dot (G y ** christoffel G y w w))`
  ASSUME_TAC THENL
   [USE_THEN "flat" (fun th -> ACCEPT_TAC(MP (SPECL [`y:real^N`;
      `christoffel (G:real^N->real^N^N) y w w`] th) (ASSUME `(y:real^N) IN U`)));
    ALL_TAC] THEN
  USE_THEN "hess" (MP_TAC o SPECL [`y:real^N`; `\m:num. (w:real^N)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[lnabla; lmetric2; SUM_SING_NUMSEG; ARITH] THEN
  SUBGOAL_THEN
   `!z v. drop(frechet_derivative (\x. lift((f:real^N->real) x)) (at z) v) =
          (D:real^N->real^N->real) z v`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "D" THEN REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ASSUME
   `drop(frechet_derivative (\z. lift((D:real^N->real^N->real) z w)) (at y) w) =
    D y ((V:real^N->real^N) y) *
    (V y dot ((G:real^N->real^N^N) y ** christoffel G y w w))`] THEN
  REWRITE_TAC[ASSUME
   `(D:real^N->real^N->real) y (christoffel (G:real^N->real^N^N) y w w) =
    D y ((V:real^N->real^N) y) * (V y dot (G y ** christoffel G y w w))`] THEN
  UNDISCH_TAC `&0 < w dot ((G:real^N->real^N^N) y ** w)` THEN REAL_ARITH_TAC);;

(* lambda |w|^2 <= P(w,w) in any chart (Ricci eigenframe of the chart).     *)

let RFA_SECMIN_LE_PCURV_CHART = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) c x w.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ c IN atlas /\ x IN FST c
     ==> mfd_sec_min atlas g x * (w dot (metric_local atlas c g (SND c x) ** w)) <=
         lpcurv (metric_local atlas c g) (SND c x) (\m. w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `c:(A->bool)#(A->real^3)`; `x:A`] RFA_SECMIN_CHART_3D) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c))
                 (metric_local atlas c (g:A->real^3^3)) /\
    SND c x IN IMAGE (SND c) (FST c)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas (g:A->real^3^3)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `G = metric_local atlas (c:(A->bool)#(A->real^3)) (g:A->real^3^3)` THEN
  ABBREV_TAC `y = SND (c:(A->bool)#(A->real^3)) x` THEN
  MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)`; `G:real^3->real^3^3`;
                 `y:real^3`; `S:real^3^3`; `w:real^3`; `w:real^3`] RFA_FRAME3_P) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[COND_ID]] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`(G:real^3->real^3^3) y`; `S:real^3^3`; `w:real^3`; `w:real^3`]
         RFA_FRAME3_DOT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)`; `G:real^3->real^3^3`;
                   `y:real^3`] LRG_METRIC_INVERTIBLE) THEN
    ASM_SIMP_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `p1 = lpcurv (G:real^3->real^3^3) y (\m. transp(S:real^3^3) ** basis 1)` THEN
  ABBREV_TAC `p2 = lpcurv (G:real^3->real^3^3) y (\m. transp(S:real^3^3) ** basis 2)` THEN
  ABBREV_TAC `p3 = lpcurv (G:real^3->real^3^3) y (\m. transp(S:real^3^3) ** basis 3)` THEN
  ABBREV_TAC `a1 = (transp(S:real^3^3) ** basis 1) dot ((G:real^3->real^3^3) y ** w)` THEN
  ABBREV_TAC `a2 = (transp(S:real^3^3) ** basis 2) dot ((G:real^3->real^3^3) y ** w)` THEN
  ABBREV_TAC `a3 = (transp(S:real^3^3) ** basis 3) dot ((G:real^3->real^3^3) y ** w)` THEN
  SUBGOAL_THEN `&0 <= a2 * a2 * (p2 - p1) /\ &0 <= a3 * a3 * (p3 - p1)` MP_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_LE_SQUARE] THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* The G-gradient of a linear functional L at y.                           *)

let RFA_GRAD_DOT = prove
 (`!U (G:real^N->real^N^N) y (L:real^N->real^1) x.
     metric_field U G /\ y IN U /\ linear L
     ==> (matrix_inv(G y) ** ((lambda k. drop(L(basis k))):real^N)) dot (G y ** x) =
         drop(L x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(MATCH_MP LRG_METRIC_INVERTIBLE
    (CONJ (ASSUME `metric_field U (G:real^N->real^N^N)`) (ASSUME `(y:real^N) IN U`))) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `transp((G:real^N->real^N^N) y) = G y` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o LAND_CONV) [SYM(ASSUME
    `transp((G:real^N->real^N^N) y) = G y`)] THEN
  REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL; MATRIX_VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[MATRIX_INV; MATRIX_VECTOR_MUL_LID] THEN
  MP_TAC(ISPECL [`L:real^N->real^1`; `x:real^N`] LRG_LINEAR_DROP_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[dot] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN
  STRIP_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC);;

(* A nonnegative quadratic form P(x,x) = 0 kills x: P(u,x) = 0.            *)

let RFA_PCURV_NULL_KILL = prove
 (`!U (G:real^N->real^N^N) y x u.
     metric_field U G /\ y IN U /\
     (!w. &0 <= lpcurv G y (\m. w)) /\ lpcurv G y (\m. x) = &0
     ==> lpcurv G y (\m. if m = 1 then u else x) = &0`,
  REPEAT GEN_TAC THEN INTRO_TAC "mf yU psd px" THEN
  ABBREV_TAC `q = lpcurv (G:real^N->real^N^N) y (\m. if m = 1 then u else x)` THEN
  ABBREV_TAC `pu = lpcurv (G:real^N->real^N^N) y (\m. u)` THEN
  SUBGOAL_THEN `!t. lpcurv (G:real^N->real^N^N) y (\m. &1 % u + t % x) = pu + &2 * t * q`
  (LABEL_TAC "tid") THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `&1`; `t:real`;
                   `u:real^N`; `x:real^N`] RFA_LPCURV_QUAD) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  USE_THEN "psd" (MP_TAC o SPEC `&1 % u + (--(pu + &1) / (&2 * q)) % x:real^N`) THEN
  USE_THEN "tid" (fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `pu + &2 * --(pu + &1) / (&2 * q) * q = --(&1)` SUBST1_TAC THENL
   [UNDISCH_TAC `~(q = &0)` THEN CONV_TAC REAL_FIELD; REAL_ARITH_TAC]);;

(* In dimension 3, if every plane containing n has zero curvature (in the  *)
(* form L(R(a,b)c) = 0 for the functional L = <n,.>), then P(u,u) = 0 for   *)
(* every u orthogonal to n.                                                 *)

let RFA_PCURV_ZERO_PERP = prove
 (`!U (G:real^3->real^3^3) y (n:real^3) (L:real^3->real^1).
     metric_field U G /\ y IN U /\ ~(n = vec 0) /\
     (!x. n dot (G y ** x) = drop(L x)) /\
     (!a b c. drop(L(lriemann G y a b c)) = &0)
     ==> !u. u dot (G y ** n) = &0 ==> lpcurv G y (\m. u) = &0`,
  REPEAT GEN_TAC THEN INTRO_TAC "mf yU nz nL rz" THEN X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN
  ASM_CASES_TAC `u:real^3 = vec 0` THENL
   [ASM_REWRITE_TAC[RFA_LPCURV_DIAG; MATRIX_VECTOR_MUL_RZERO; DOT_LZERO; REAL_MUL_RZERO] THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`] RFA_LRICCI_LCOMB) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`&0`; `vec 0:real^3`; `&0`; `vec 0:real^3`; `vec 0:real^3`]) THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID; REAL_MUL_LZERO; REAL_ADD_LID] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < u dot ((G:real^3->real^3^3) y ** u) /\ &0 < n dot (G y ** n)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LRG_METRIC_POS THEN EXISTS_TAC `U:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `cu = inv(sqrt(u dot ((G:real^3->real^3^3) y ** u)))` THEN
  ABBREV_TAC `cn = inv(sqrt(n dot ((G:real^3->real^3^3) y ** n)))` THEN
  SUBGOAL_THEN `&0 < cu /\ &0 < cn` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["cu"; "cn"] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN
    MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(cn % n) dot ((G:real^3->real^3^3) y ** (cn % n)) = &1 /\
    (cu % u) dot (G y ** (cu % u)) = &1 /\ (cn % n) dot (G y ** (cu % u)) = &0`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["cu"; "cn"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC RFA_GNORM_UNIT THEN EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFA_GNORM_UNIT THEN EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN
      MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `n:real^3`;
                     `u:real^3`] LRG_METRIC_SYM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RZERO]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `cn % n:real^3`;
                 `cu % u:real^3`] RFA_NORMAL3) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `cn % n:real^3`;
                 `w:real^3`; `cu % u:real^3`] RFA_LSECTIONAL_PCURV_3D) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `w:real^3`;
                   `cu % u:real^3`] LRG_METRIC_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lsectional (G:real^3->real^3^3) y (cn % n) w = &0` SUBST1_TAC THENL
   [REWRITE_TAC[lsectional] THEN
    SUBGOAL_THEN `(cn % n) dot ((G:real^3->real^3^3) y ** lriemann G y (cn % n) w w) = &0`
    SUBST1_TAC THENL
     [REWRITE_TAC[DOT_LMUL] THEN ASM_REWRITE_TAC[REAL_MUL_RZERO]; ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `inv cu`; `&0`;
                 `cu % u:real^3`; `w:real^3`] RFA_LPCURV_QUAD) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_ASSOC; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
  DISCH_THEN SUBST1_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REAL_ARITH_TAC);;

(* If P >= 0 vanishes on n-perp and P(b0,b0) > 0, then P(b0,w) = 0 forces  *)
(* w orthogonal to n.                                                       *)

let RFA_PCURV_PERP_ORTHO = prove
 (`!U (G:real^N->real^N^N) y (n:real^N) b0 w.
     metric_field U G /\ y IN U /\
     (!u. &0 <= lpcurv G y (\m. u)) /\
     (!u. u dot (G y ** n) = &0 ==> lpcurv G y (\m. u) = &0) /\
     &0 < lpcurv G y (\m. b0) /\ lpcurv G y (\m. if m = 1 then b0 else w) = &0
     ==> w dot (G y ** n) = &0`,
  REPEAT GEN_TAC THEN INTRO_TAC "mf yU psd perp pb pbw" THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  ABBREV_TAC `c = (b0 dot ((G:real^N->real^N^N) y ** n)) / (w dot (G y ** n))` THEN
  SUBGOAL_THEN `(b0 - c % w:real^N) dot ((G:real^N->real^N^N) y ** n) = &0` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[DOT_LSUB; DOT_LMUL] THEN
    UNDISCH_TAC `~((w:real^N) dot ((G:real^N->real^N^N) y ** n) = &0)` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `lpcurv (G:real^N->real^N^N) y (\m. if m = 1 then b0 else b0 - c % w) = &0`
  (LABEL_TAC "pbx") THENL
   [MATCH_MP_TAC RFA_PCURV_NULL_KILL THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "perp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lpcurv (G:real^N->real^N^N) y (\m. b0) = &0` MP_TAC THENL
   [ALL_TAC; USE_THEN "pb" MP_TAC THEN REAL_ARITH_TAC] THEN
  USE_THEN "pbx" MP_TAC THEN USE_THEN "pbw" MP_TAC THEN
  REWRITE_TAC[RFA_LPCURV_BIL; RFA_LPCURV_DIAG] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `&1`; `b0:real^N`;
                 `--c`; `w:real^N`; `b0:real^N`] RFA_LRICCI_LCOMB) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LID; VECTOR_ARITH `b + --c % w:real^N = b - c % w`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2 th]) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; MATRIX_VECTOR_MUL_RMUL; DOT_RSUB; DOT_RMUL] THEN
  CONV_TAC REAL_RING);;




(* ========================================================================= *)
(* The Hessian in two charts and Hess f = g in every chart.                  *)
(* ========================================================================= *)

(* The Hessian of f in two charts: the covariant derivative of df transforms *)
(* as a (0,2)-tensor (LRG_LNABLA_ITER_PULLBACK for the chart transition).   *)

let RFA_HESS_CHART_TRANS = prove
 (`!top atlas (g:A->real^N^N) (f:A->real) c c' x u v.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_smooth_on atlas (topspace top) (\x. lift(f x)) /\
     c IN atlas /\ c' IN atlas /\ x IN FST c /\ x IN FST c'
     ==> lnabla 1 (metric_local atlas c g)
           (\z w. drop(frechet_derivative (\y. lift(f(chart_inv c y))) (at z) (w 1)))
           (SND c x) (\m. if m = 1 then u else v) =
         lnabla 1 (metric_local atlas c' g)
           (\z w. drop(frechet_derivative (\y. lift(f(chart_inv c' y))) (at z) (w 1)))
           (SND c' x) (\m. if m = 1 then chart_jac c c' x u else chart_jac c c' x v)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `g:A->real^N^N`; `f:A->real`; `U1:A->bool`; `phi:A->real^N`;
                       `V1:A->bool`; `psi:A->real^N`; `x:A`; `u:real^N`; `v:real^N`] THEN
  REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U1:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `V1:A->bool`; `psi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U1:A->bool`; `phi:A->real^N`] CHART_INV) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `V1:A->bool`; `psi:A->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pi1") (LABEL_TAC "pi2")) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fi1") (LABEL_TAC "fi2")) THEN
  ABBREV_TAC `h = chart_trans (U1:A->bool,phi:A->real^N) (V1,psi)` THEN
  ABBREV_TAC `h' = chart_trans (V1:A->bool,psi:A->real^N) (U1,phi)` THEN
  ABBREV_TAC `W' = IMAGE (phi:A->real^N) (U1 INTER V1)` THEN
  ABBREV_TAC `W = IMAGE (psi:A->real^N) (U1 INTER V1)` THEN
  SUBGOAL_THEN `open(W':real^N->bool) /\ open(W:real^N->bool)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["W'"; "W"] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `(U1:A->bool,phi:A->real^N)`; `U1 INTER V1:A->bool`]
             MFDM_CHART_IMAGE_OPEN);
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `(V1:A->bool,psi:A->real^N)`; `U1 INTER V1:A->bool`]
             MFDM_CHART_IMAGE_OPEN)] THEN
    REWRITE_TAC[SND] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[OPEN_IN_INTER; FST; INTER_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `diffeomorphism_on W' W (h:real^N->real^N) h'` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["W'"; "W"; "h"; "h'"] THEN MATCH_MP_TAC CHART_TRANS_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(W:real^N->bool) SUBSET IMAGE (psi:A->real^N) V1 /\ (W':real^N->bool) SUBSET IMAGE (phi:A->real^N) U1`
  STRIP_ASSUME_TAC THENL [MAP_EVERY EXPAND_TAC ["W"; "W'"] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(U1:A->bool) SUBSET topspace top /\ (V1:A->bool) SUBSET topspace top`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (IMAGE (psi:A->real^N) V1) (metric_local atlas (V1,psi) (g:A->real^N^N))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
    REWRITE_TAC[riemannian_metric] THEN
    DISCH_THEN(MP_TAC o SPEC `(V1:A->bool,psi:A->real^N)`) THEN ASM_REWRITE_TAC[FST; SND];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (IMAGE (psi:A->real^N) V1)
                  (\y. lift((f:A->real)(chart_inv (V1,psi) y)))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_smooth_on (atlas:((A->bool)#(A->real^N))->bool) (topspace top) (\x. lift((f:A->real) x))` THEN
    REWRITE_TAC[mfd_smooth_on] THEN DISCH_THEN(MP_TAC o SPEC `(V1:A->bool,psi:A->real^N)`) THEN
    ASM_REWRITE_TAC[FST; SND; o_DEF] THEN
    SUBGOAL_THEN `V1 INTER topspace top = (V1:A->bool)` SUBST1_TAC THENL
     [ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (W:real^N->bool) (\y. lift((f:A->real)(chart_inv (V1,psi) y)))`
  ASSUME_TAC THENL [ASM_MESON_TAC[SMOOTH_MAP_ON_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`W:real^N->bool`; `\y. (f:A->real)(chart_inv (V1:A->bool,psi:A->real^N) y)`]
         LRG_DF_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  ABBREV_TAC `Tv = \z (w:num->real^N).
                     drop(frechet_derivative (\y. lift((f:A->real)(chart_inv (V1,psi) y))) (at z) (w 1))` THEN
  ABBREV_TAC `Tu = \z (w:num->real^N).
                     drop(frechet_derivative (\y. lift((f:A->real)(chart_inv (U1,phi) y))) (at z) (w 1))` THEN
  (* df in the two charts *)
  SUBGOAL_THEN `!z w. z IN W' ==> (Tu:real^N->(num->real^N)->real) z w = ltpullback h Tv z w`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`z:real^N`; `w:num->real^N`] THEN DISCH_TAC THEN
    MAP_EVERY EXPAND_TAC ["Tu"; "Tv"] THEN REWRITE_TAC[ltpullback] THEN
    SUBGOAL_THEN
     `frechet_derivative (\y. lift((f:A->real)(chart_inv (U1,phi) y))) (at z) =
      frechet_derivative (\y. (\y'. lift(f(chart_inv (V1:A->bool,psi:A->real^N) y')))
                                ((h:real^N->real^N) y)) (at z)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `W':real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN
      SUBST1_TAC(SYM(ASSUME `IMAGE (phi:A->real^N) (U1 INTER V1) = W'`)) THEN
      REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN
      X_GEN_TAC `x':A` THEN STRIP_TAC THEN EXPAND_TAC "h" THEN
      REWRITE_TAC[chart_trans; SND] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^N) IN W' /\ (h:real^N->real^N) z IN W` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`h:real^N->real^N`;
                   `\y'. lift((f:A->real)(chart_inv (V1:A->bool,psi:A->real^N) y'))`;
                   `z:real^N`; `(w:num->real^N) 1`] LRG_FRECHET_DERIVATIVE_CHAIN) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
       [EXISTS_TAC `W':real^N->bool`; EXISTS_TAC `W:real^N->bool`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:A->real^N) x IN W'` ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `IMAGE (phi:A->real^N) (U1 INTER V1) = W'`)) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`1`; `W:real^N->bool`; `W':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`;
                 `metric_local atlas (V1:A->bool,psi:A->real^N) (g:A->real^N^N)`;
                 `Tv:real^N->(num->real^N)->real`; `Tu:real^N->(num->real^N)->real`]
         LRG_LNABLA_ITER_PULLBACK) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
      EXISTS_TAC `IMAGE (psi:A->real^N) V1` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      EXPAND_TAC "Tv" THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "Tv" THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`1`; `(phi:A->real^N) x`;
                             `\m:num. if m = 1 then (u:real^N) else v`]) THEN
  ASM_REWRITE_TAC[RFA_LNABLA_ITER_1] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `lnabla 1 (metric_local atlas (U1:A->bool,phi:A->real^N) (g:A->real^N^N)) Tu (phi x)
           (\m:num. if m = 1 then (u:real^N) else v) =
    lnabla 1 (mpullback (h:real^N->real^N) (metric_local atlas (V1,psi) g)) Tu (phi x)
           (\m:num. if m = 1 then u else v)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `W':real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(SYM(ASSUME `IMAGE (phi:A->real^N) (U1 INTER V1) = W'`)) THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `x':A` THEN STRIP_TAC THEN
    EXPAND_TAC "h" THEN MATCH_MP_TAC METRIC_LOCAL_TRANS THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ltpullback] THEN
  SUBGOAL_THEN `(h:real^N->real^N) (phi x) = (psi:A->real^N) x` SUBST1_TAC THENL
   [EXPAND_TAC "h" THEN MATCH_MP_TAC CHART_TRANS_AT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `m:num` THEN
  REWRITE_TAC[chart_jac; SND] THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[]);;

(* Hess f = g at every point (preferred charts) gives Hess f = g on the     *)
(* whole image of every chart.                                              *)

let RFA_HESS_METRIC_CHART = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (f:A->real) c.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_smooth_on atlas (topspace top) (\x. lift(f x)) /\
     (!x u v. x IN topspace top ==> p2b_mfd_hess atlas g f x u v = u dot (g x ** v)) /\
     c IN atlas
     ==> !y u. y IN IMAGE (SND c) (FST c)
               ==> lnabla 1 (metric_local atlas c g)
                     (\z w. drop(frechet_derivative (\y. lift(f(chart_inv c y))) (at z) (w 1)))
                     y u =
                   lmetric2 (metric_local atlas c g) y u`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
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
  (* reduce to a pair of vectors *)
  SUBGOAL_THEN `smooth_map_on (IMAGE (phi:A->real^N) U1)
                  (\y. lift((f:A->real)(chart_inv (U1,phi) y)))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_smooth_on (atlas:((A->bool)#(A->real^N))->bool) (topspace top)
                   (\x. lift((f:A->real) x))` THEN
    REWRITE_TAC[mfd_smooth_on] THEN DISCH_THEN(MP_TAC o SPEC `(U1:A->bool,phi:A->real^N)`) THEN
    ASM_REWRITE_TAC[FST; SND; o_DEF] THEN
    SUBGOAL_THEN `U1 INTER topspace top = (U1:A->bool)` SUBST1_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET; SET_RULE `!s t:A->bool. s SUBSET t ==> s INTER t = s`]; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^N) U1`; `\y. (f:A->real)(chart_inv (U1:A->bool,phi:A->real^N) y)`]
         LRG_DF_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`1`; `IMAGE (phi:A->real^N) U1`;
                 `metric_local atlas (U1:A->bool,phi:A->real^N) (g:A->real^N^N)`;
                 `\z w. drop(frechet_derivative (\y. lift((f:A->real)(chart_inv (U1:A->bool,phi:A->real^N) y)))
                                                (at z) (w 1))`;
                 `(phi:A->real^N) x`; `uu:num->real^N`;
                 `\m:num. if m = 1 then (uu:num->real^N) 1 else uu 2`] LRG_LNABLA_AGREE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `m = 1 \/ m = 2` MP_TAC THENL
     [ASM_ARITH_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[ARITH]];
    DISCH_THEN SUBST1_TAC] THEN
  (* transfer to the preferred chart of x *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `(U1:A->bool,phi:A->real^N)`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`; `x:A`;
                 `(uu:num->real^N) 1`; `(uu:num->real^N) 2`] RFA_HESS_CHART_TRANS) THEN
  ASM_REWRITE_TAC[FST; SND] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM p2b_mfd_hess] THEN ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPEC `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`V2:A->bool`; `psi:A->real^N`] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN
  REWRITE_TAC[FST; SND] THEN REWRITE_TAC[lmetric2] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U1:A->bool`; `phi:A->real^N`; `V2:A->bool`; `psi:A->real^N`;
                 `g:A->real^N^N`; `x:A`] METRIC_LOCAL_JAC) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `linear(chart_jac (U1:A->bool,phi:A->real^N) (V2,psi) x)` ASSUME_TAC THENL
   [REWRITE_TAC[chart_jac] THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    REWRITE_TAC[differentiable; SND] THEN
    EXISTS_TAC `chart_jac (U1:A->bool,phi:A->real^N) (V2,psi) x` THEN
    MATCH_MP_TAC CHART_TRANS_HAS_DERIVATIVE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
  ASM_SIMP_TAC[MATRIX_WORKS]);;




(* ========================================================================= *)
(* Pointwise consequences at time 0 and the existence of a                   *)
(* point with grad f nonzero.                                               *)
(* ========================================================================= *)

(* Hess f = g forces df to be nonzero somewhere.                            *)

let RFA_HESS_METRIC_DF_NONZERO = prove
 (`!U (G:real^N->real^N^N) (f:real^N->real) y0.
     metric_field U G /\ y0 IN U /\
     (!y u. y IN U
            ==> lnabla 1 G (\z w. drop(frechet_derivative (\x. lift(f x)) (at z) (w 1))) y u =
                lmetric2 G y u)
     ==> ?y w. y IN U /\ ~(drop(frechet_derivative (\x. lift(f x)) (at y) w) = &0)`,
  REPEAT GEN_TAC THEN INTRO_TAC "mf yU hess" THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM]) THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `!y w. y IN U ==> drop(frechet_derivative (\x. lift((f:real^N->real) x)) (at y) w) = &0`
  (LABEL_TAC "zero") THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  USE_THEN "hess" (MP_TAC o SPECL [`y0:real^N`; `\m:num. basis 1:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[lnabla; lmetric2; SUM_SING_NUMSEG; ARITH] THEN
  SUBGOAL_THEN
   `frechet_derivative (\z. lift(drop(frechet_derivative (\x. lift((f:real^N->real) x)) (at z)
                                      (basis 1)))) (at y0) =
    frechet_derivative (\z:real^N. vec 0:real^1) (at y0)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_SIMP_TAC[LIFT_NUM];
    ALL_TAC] THEN
  USE_THEN "zero" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(y0:real^N) IN U`)]) THEN
  REWRITE_TAC[FRECHET_DERIVATIVE_CONST_AT; DROP_VEC; REAL_SUB_REFL] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(&0 = x)`) THEN MATCH_MP_TAC LRG_METRIC_POS THEN
  EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC BASIS_NONZERO THEN REWRITE_TAC[LE_REFL; DIMINDEX_GE_1]);;

(* At a chart point where grad f is nonzero (Hess f = g, lambda >= 0):     *)
(* lambda = 0, P >= 0, and P(b0,w) = 0 with P(b0,b0) > 0 forces df(w) = 0.  *)

let RFA_CONE_POINT = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g0:A->real^3^3) (f:A->real) c y.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g0 /\
     mfd_smooth_on atlas (topspace top) (\x. lift(f x)) /\
     (!x u v. x IN topspace top ==> p2b_mfd_hess atlas g0 f x u v = u dot (g0 x ** v)) /\
     (!x. x IN topspace top ==> &0 <= mfd_sec_min atlas g0 x) /\
     c IN atlas /\ y IN IMAGE (SND c) (FST c) /\
     ~(matrix_inv(metric_local atlas c g0 y) **
       ((lambda k. drop(frechet_derivative (\z. lift(f(chart_inv c z))) (at y) (basis k))):real^3) =
       vec 0)
     ==> mfd_sec_min atlas g0 (chart_inv c y) = &0 /\
         (!w. &0 <= lpcurv (metric_local atlas c g0) y (\m. w)) /\
         (!b0 w. &0 < lpcurv (metric_local atlas c g0) y (\m. b0) /\
                 lpcurv (metric_local atlas c g0) y (\m. if m = 1 then b0 else w) = &0
                 ==> drop(frechet_derivative (\z. lift(f(chart_inv c z))) (at y) w) = &0)`,
  REPEAT GEN_TAC THEN INTRO_TAC "sma rm fsm hess lam cA yI nz" THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ci1") (LABEL_TAC "ci2")))) THEN
  USE_THEN "ci2" (MP_TAC o SPEC `y:real^3`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `x = chart_inv (c:(A->bool)#(A->real^3)) y` THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g0:A->real^3^3`;
                 `f:A->real`; `c:(A->bool)#(A->real^3)`] RFA_HESS_METRIC_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `U = IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)` THEN
  ABBREV_TAC `G = metric_local atlas (c:(A->bool)#(A->real^3)) (g0:A->real^3^3)` THEN
  SUBGOAL_THEN `metric_field U (G:real^3->real^3^3)` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["U"; "G"] THEN
    UNDISCH_TAC `riemannian_metric atlas (g0:A->real^3^3)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U (\z. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^3)) z)))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_smooth_on (atlas:((A->bool)#(A->real^3))->bool) (topspace top)
                   (\x. lift((f:A->real) x))` THEN
    REWRITE_TAC[mfd_smooth_on] THEN
    DISCH_THEN(MP_TAC o C MATCH_MP (ASSUME `(c:(A->bool)#(A->real^3)) IN atlas`)) THEN
    REWRITE_TAC[o_DEF] THEN
    SUBGOAL_THEN `FST c INTER topspace top = FST(c:(A->bool)#(A->real^3))` SUBST1_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET; SET_RULE `!s t:A->bool. s SUBSET t ==> s INTER t = s`];
      ALL_TAC] THEN
    EXPAND_TAC "U" THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`;
                 `\z. (f:A->real)(chart_inv (c:(A->bool)#(A->real^3)) z)`] RFA_HESS_METRIC_RM)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN DISCH_THEN(LABEL_TAC "rz") THEN
  ABBREV_TAC `L = frechet_derivative (\z. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^3)) z)))
                                      (at y)` THEN
  SUBGOAL_THEN `linear(L:real^3->real^1)` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^3->bool` THEN
    ASM_MESON_TAC[metric_field];
    ALL_TAC] THEN
  ABBREV_TAC `n = matrix_inv((G:real^3->real^3^3) y) **
                  ((lambda k. drop((L:real^3->real^1)(basis k))):real^3)` THEN
  SUBGOAL_THEN `!w. (n:real^3) dot ((G:real^3->real^3^3) y ** w) = drop((L:real^3->real^1) w)`
  (LABEL_TAC "nL") THENL
   [GEN_TAC THEN EXPAND_TAC "n" THEN MATCH_MP_TAC RFA_GRAD_DOT THEN
    EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* P vanishes on n-perp *)
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `n:real^3`;
                 `L:real^3->real^1`] RFA_PCURV_ZERO_PERP) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(LABEL_TAC "zp")] THEN
  (* P >= 0 *)
  SUBGOAL_THEN `!w. &0 <= lpcurv (G:real^3->real^3^3) y (\m. w)` (LABEL_TAC "psd") THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_sec_min atlas (g0:A->real^3^3) x * (w dot ((G:real^3->real^3^3) y ** w))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[] THEN
      ASM_CASES_TAC `w:real^3 = vec 0` THENL
       [ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_LE_REFL];
        MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC LRG_METRIC_POS THEN
        EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[]];
      MAP_EVERY EXPAND_TAC ["G"; "x"] THEN
      SUBGOAL_THEN `y = SND(c:(A->bool)#(A->real^3)) (chart_inv c y)` (fun th ->
        GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RAND_CONV) [th] THEN
        GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV o LAND_CONV o RAND_CONV) [th])
      THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC RFA_SECMIN_LE_PCURV_CHART THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (n:real^3) dot ((G:real^3->real^3^3) y ** n)` ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_METRIC_POS THEN EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(inv(sqrt((n:real^3) dot ((G:real^3->real^3^3) y ** n))) = &0)` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x = &0)`) THEN MATCH_MP_TAC REAL_LT_INV THEN
    MATCH_MP_TAC SQRT_POS_LT THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* lambda = 0 *)
    MATCH_MP_TAC(REAL_ARITH `&0 <= l /\ l <= &0 ==> l = &0`) THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`;
                   `inv(sqrt((n:real^3) dot ((G:real^3->real^3^3) y ** n))) % n`]
           RFA_UNIT_PERP3) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC RFA_GNORM_UNIT THEN EXISTS_TAC `U:real^3->bool` THEN
        REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
      DISCH_THEN(X_CHOOSE_THEN `uh:real^3` STRIP_ASSUME_TAC)] THEN
    SUBGOAL_THEN `(uh:real^3) dot ((G:real^3->real^3^3) y ** n) = &0` ASSUME_TAC THENL
     [UNDISCH_TAC `(inv(sqrt((n:real^3) dot ((G:real^3->real^3^3) y ** n))) % n) dot
                   (G y ** uh) = &0` THEN
      REWRITE_TAC[DOT_LMUL; REAL_ENTIRE] THEN
      REWRITE_TAC[ASSUME `~(inv(sqrt((n:real^3) dot ((G:real^3->real^3^3) y ** n))) = &0)`] THEN
      MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `n:real^3`;
                     `uh:real^3`] LRG_METRIC_SYM) THEN
      ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lpcurv (G:real^3->real^3^3) y (\m. uh)` THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g0:A->real^3^3`;
                     `c:(A->bool)#(A->real^3)`; `x:A`; `uh:real^3`] RFA_SECMIN_LE_PCURV_CHART) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN EXPAND_TAC "x" THEN
        FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      EXPAND_TAC "x" THEN
      REWRITE_TAC[ASSUME `SND (c:(A->bool)#(A->real^3)) (chart_inv c y) = y`] THEN
      REWRITE_TAC[ASSUME `metric_local atlas (c:(A->bool)#(A->real^3)) (g0:A->real^3^3) = G`] THEN
      REWRITE_TAC[ASSUME `(uh:real^3) dot ((G:real^3->real^3^3) y ** uh) = &1`; REAL_MUL_RID];
      USE_THEN "zp" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
        `(uh:real^3) dot ((G:real^3->real^3^3) y ** n) = &0`)]) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL [USE_THEN "psd" ACCEPT_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`b0:real^3`; `w:real^3`] THEN STRIP_TAC THEN
  USE_THEN "nL" (fun th -> REWRITE_TAC[GSYM th]) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `n:real^3`;
                 `w:real^3`] LRG_METRIC_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC RFA_PCURV_PERP_ORTHO THEN
  MAP_EVERY EXISTS_TAC [`U:real^3->bool`; `b0:real^3`] THEN ASM_REWRITE_TAC[]);;




(* ========================================================================= *)
(* Smoothness of rho^2/2 and of the gradient field; the                      *)
(* contradiction when R > 0 everywhere at time 0.                           *)
(* ========================================================================= *)

(* rho^2/2 is smooth when rho is.                                           *)

let RFA_MFD_SMOOTH_SQ_HALF = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (rho:A->real).
     smooth_manifold_atlas top atlas /\
     mfd_smooth_on atlas (topspace top) (\x. lift(rho x))
     ==> mfd_smooth_on atlas (topspace top) (\x. lift(rho x pow 2 / &2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_smooth_on; o_DEF] THEN STRIP_TAC THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `open(IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER topspace top))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
    REWRITE_TAC[OPEN_IN_TOPSPACE] THEN ASM_MESON_TAC[MFDM_CHART];
    ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER topspace top)`; `inv(&2)`;
                 `\y. lift(drop(lift((rho:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y))) pow 2)`]
         SMOOTH_MAP_ON_LIFT_CMUL) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER topspace top)`;
                 `\y. lift((rho:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y))`; `2`]
         SMOOTH_MAP_ON_LIFT_POW) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

(* The gradient field of f in a chart is smooth.                            *)

let RFA_GRAD_FIELD_SMOOTH = prove
 (`!U (G:real^N->real^N^N) (f:real^N->real).
     metric_field U G /\ smooth_map_on U (\z. lift(f z))
     ==> smooth_map_on U
           (\y. matrix_inv(G y) **
                ((lambda k. drop(frechet_derivative (\z. lift(f z)) (at y) (basis k))):real^N))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MATCH_MP_TAC LRG_SMOOTH_MATVEC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LRG_SMOOTH_MATRIX_INV THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`]
           LRG_METRIC_INVERTIBLE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`;
                 `\k y. lift(drop(frechet_derivative (\z. lift((f:real^N->real) z)) (at y) (basis k)))`]
         (INST_TYPE [`:N`,`:M`] SMOOTH_MAP_ON_LAMBDA)) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]);;

(* With R(0,.) > 0 everywhere the cone hypotheses are contradictory: the   *)
(* split field of RFA_PARALLEL_CHART_END would be parallel to grad f.       *)

let RFA_CONE_POS_FALSE = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:real->A->real^3^3) a (f:A->real) x.
     connected_space top /\ a < &0 /\ rfs_flow_upto (top,atlas) a (&0) g /\
     (!t x. a < t /\ t <= &0 /\ x IN topspace top ==> &0 <= mfd_sec_min atlas (g t) x) /\
     mfd_smooth_on atlas (topspace top) (\x. lift(f x)) /\
     (!x u v. x IN topspace top
              ==> p2b_mfd_hess atlas (g(&0)) f x u v = u dot (g (&0) x ** v)) /\
     (!p. p IN topspace top ==> &0 < mfd_scalar atlas (g(&0)) p) /\
     x IN topspace top
     ==> F`,
  REPEAT GEN_TAC THEN INTRO_TAC "conn a0 flow lam fsm hess rpos xM" THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) /\
                riemannian_metric atlas ((g:real->A->real^3^3) (&0))`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[rfs_flow_upto; ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ci1") (LABEL_TAC "ci2")))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(g:real->A->real^3^3) (&0)`; `f:A->real`; `c:(A->bool)#(A->real^3)`]
         RFA_HESS_METRIC_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ABBREV_TAC `U = IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)` THEN
  ABBREV_TAC `G = metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) (&0))` THEN
  SUBGOAL_THEN `metric_field U (G:real^3->real^3^3)` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["U"; "G"] THEN
    UNDISCH_TAC `riemannian_metric atlas ((g:real->A->real^3^3) (&0))` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U (\z. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^3)) z)))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_smooth_on (atlas:((A->bool)#(A->real^3))->bool) (topspace top)
                   (\x. lift((f:A->real) x))` THEN
    REWRITE_TAC[mfd_smooth_on] THEN
    DISCH_THEN(MP_TAC o C MATCH_MP (ASSUME `(c:(A->bool)#(A->real^3)) IN atlas`)) THEN
    REWRITE_TAC[o_DEF] THEN
    SUBGOAL_THEN `FST c INTER topspace top = FST(c:(A->bool)#(A->real^3))` SUBST1_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET; SET_RULE `!s t:A->bool. s SUBSET t ==> s INTER t = s`];
      ALL_TAC] THEN
    EXPAND_TAC "U" THEN REWRITE_TAC[];
    ALL_TAC] THEN
  (* a point where grad f is nonzero *)
  MP_TAC(BETA_RULE(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`;
                 `\z. (f:A->real)(chart_inv (c:(A->bool)#(A->real^3)) z)`;
                 `SND(c:(A->bool)#(A->real^3)) x`] RFA_HESS_METRIC_DF_NONZERO)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "U" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `y0:real^3` (X_CHOOSE_THEN `w0:real^3` STRIP_ASSUME_TAC))] THEN
  ABBREV_TAC `nf = \y. matrix_inv((G:real^3->real^3^3) y) **
                       ((lambda k. drop(frechet_derivative
                           (\z. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^3)) z)))
                           (at y) (basis k))):real^3)` THEN
  SUBGOAL_THEN `~((nf:real^3->real^3) y0 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y0:real^3`;
                   `frechet_derivative (\z. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^3)) z)))
                                       (at y0)`; `w0:real^3`] RFA_GRAD_DOT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^3->bool` THEN
      ASM_MESON_TAC[metric_field];
      ALL_TAC] THEN
    UNDISCH_TAC `(nf:real^3->real^3) y0 = vec 0` THEN EXPAND_TAC "nf" THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DOT_LZERO] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  (* the point y0 *)
  SUBGOAL_THEN `!z. z IN U /\ ~((nf:real^3->real^3) z = vec 0)
                    ==> mfd_sec_min atlas ((g:real->A->real^3^3) (&0))
                                    (chart_inv (c:(A->bool)#(A->real^3)) z) = &0 /\
                        (!w. &0 <= lpcurv (G:real^3->real^3^3) z (\m. w)) /\
                        (!b0 w. &0 < lpcurv G z (\m. b0) /\
                                lpcurv G z (\m. if m = 1 then b0 else w) = &0
                                ==> drop(frechet_derivative
                                      (\x. lift((f:A->real)(chart_inv c x))) (at z) w) = &0)`
  (LABEL_TAC "pt") THENL
   [X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) (&0)`; `f:A->real`; `c:(A->bool)#(A->real^3)`;
                   `z:real^3`] RFA_CONE_POINT) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN USE_THEN "lam" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `~((nf:real^3->real^3) z = vec 0)` THEN EXPAND_TAC "nf" THEN
        REWRITE_TAC[]];
      SIMP_TAC[]];
    ALL_TAC] THEN
  USE_THEN "ci2" (MP_TAC o SPEC `y0:real^3`) THEN
  ANTS_TAC THENL [EXPAND_TAC "U" THEN ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `x0 = chart_inv (c:(A->bool)#(A->real^3)) y0` THEN
  SUBGOAL_THEN `(x0:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  (* lambda = 0 on (a,0] x M *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `&0`;
                 `g:real->A->real^3^3`; `x0:A`] RFA_SECMIN_ZERO_UPTO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "x0" THEN
    USE_THEN "pt" (fun th -> MP_TAC(MATCH_MP th (CONJ (ASSUME `(y0:real^3) IN U`)
                                          (ASSUME `~((nf:real^3->real^3) y0 = vec 0)`)))) THEN
    SIMP_TAC[];
    DISCH_THEN(LABEL_TAC "lz")] THEN
  (* a direction b0 with P(b0,b0) > 0 at y0 *)
  SUBGOAL_THEN `?b0:real^3. &0 < lpcurv (G:real^3->real^3^3) y0 (\m. b0)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) (&0)`; `c:(A->bool)#(A->real^3)`; `x0:A`]
           RFA_SECMIN_CHART_3D) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y0:real^3`; `S:real^3^3`]
           RFA_P3_FRAME_SCALARS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXPAND_TAC "U" THEN ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
    SUBGOAL_THEN `&0 < lscalar (G:real^3->real^3^3) y0` MP_TAC THENL
     [USE_THEN "rpos" (fun th -> MP_TAC(MP (SPEC `x0:A` th) (ASSUME `(x0:A) IN topspace top`))) THEN
      REWRITE_TAC[mfd_scalar] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `(g:real->A->real^3^3) (&0)`; `c:(A->bool)#(A->real^3)`; `x0:A`]
             RFA_MFD_SCALAR_CHART) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN DISCH_TAC THEN
    ASM_CASES_TAC `&0 < lpcurv (G:real^3->real^3^3) y0 (\m. transp(S:real^3^3) ** basis 1)` THENL
     [EXISTS_TAC `transp(S:real^3^3) ** basis 1` THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `&0 < lpcurv (G:real^3->real^3^3) y0 (\m. transp(S:real^3^3) ** basis 2)` THENL
     [EXISTS_TAC `transp(S:real^3^3) ** basis 2` THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    EXISTS_TAC `transp(S:real^3^3) ** basis 3` THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the open set where P(b0,b0) > 0 and grad f is nonzero *)
  ABBREV_TAC `N0 = {y:real^3 | y IN U /\ &0 < lpcurv (G:real^3->real^3^3) y (\m. b0) /\
                               ~((nf:real^3->real^3) y = vec 0)}` THEN
  SUBGOAL_THEN `open(N0:real^3->bool) /\ N0 SUBSET U /\ (y0:real^3) IN N0` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `open(U:real^3->bool)` ASSUME_TAC THENL [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN
       `N0 = {y:real^3 | y IN U /\ (\y. lift(lpcurv (G:real^3->real^3^3) y (\m. b0))) y IN
                                    {x:real^1 | x$1 > &0}} INTER
             {y:real^3 | y IN U /\ (nf:real^3->real^3) y IN ((:real^3) DELETE vec 0)}`
      SUBST1_TAC THENL
       [EXPAND_TAC "N0" THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_DELETE; IN_UNIV;
                                         GSYM drop; LIFT_DROP; real_gt] THEN
        MESON_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC THEN
      MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
        MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`] RFA_LPCURV_FIELD) THEN
        ASM_SIMP_TAC[];
        REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT];
        MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN EXPAND_TAC "nf" THEN
        MATCH_MP_TAC RFA_GRAD_FIELD_SMOOTH THEN ASM_REWRITE_TAC[];
        SIMP_TAC[OPEN_DELETE; OPEN_UNIV]];
      EXPAND_TAC "N0" THEN SET_TAC[];
      EXPAND_TAC "N0" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "U" THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field N0 (G:real^3->real^3^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. w IN N0
        ==> ~(matrix_inv((G:real^3->real^3^3) w) **
              ((lambda k. lpcurv G w (\m. if m = 1 then b0 else basis k)):real^3) = vec 0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`N0:real^3->bool`; `G:real^3->real^3^3`; `w:real^3`; `b0:real^3`;
                   `b0:real^3`] RFA_PFIELD_DOT) THEN
    ASM_REWRITE_TAC[DOT_LZERO; COND_ID] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(&0 = x)`) THEN
    UNDISCH_TAC `(w:real^3) IN N0` THEN EXPAND_TAC "N0" THEN SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] RFA_HESS_METRIC_PARALLEL_FALSE) THEN
  MAP_EVERY EXISTS_TAC [`N0:real^3->bool`; `G:real^3->real^3^3`;
                        `\z. (f:A->real)(chart_inv (c:(A->bool)#(A->real^3)) z)`;
                        `\w. inv(sqrt((matrix_inv((G:real^3->real^3^3) w) ** ((lambda k. lpcurv G w (\m. if m = 1 then b0 else basis k)):real^3)) dot ((G:real^3->real^3^3) w ** (matrix_inv((G:real^3->real^3^3) w) ** ((lambda k. lpcurv G w (\m. if m = 1 then b0 else basis k)):real^3))))) % (matrix_inv((G:real^3->real^3^3) w) ** ((lambda k. lpcurv G w (\m. if m = 1 then b0 else basis k)):real^3))`;
                        `y0:real^3`] THEN
  BETA_TAC THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC RFA_GNORMALIZE_SMOOTH THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RFA_PFIELD_SMOOTH THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC;
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    MAP_EVERY X_GEN_TAC [`z:real^3`; `w:real^3`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `&0`;
                   `g:real->A->real^3^3`; `c:(A->bool)#(A->real^3)`; `N0:real^3->bool`;
                   `b0:real^3`; `z:real^3`; `w:real^3`] RFA_PARALLEL_CHART_END) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN EXPAND_TAC "N0" THEN
      SIMP_TAC[IN_ELIM_THM];
      ASM_REWRITE_TAC[lcovd]];
    MAP_EVERY X_GEN_TAC [`z:real^3`; `w:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN U /\ &0 < lpcurv (G:real^3->real^3^3) z (\m. b0) /\
                  ~((nf:real^3->real^3) z = vec 0)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN N0` THEN EXPAND_TAC "N0" THEN SIMP_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    USE_THEN "pt" (MP_TAC o SPEC `z:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
    EXISTS_TAC `b0:real^3` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`N0:real^3->bool`; `G:real^3->real^3^3`; `z:real^3`; `b0:real^3`;
                   `w:real^3`] RFA_PFIELD_DOT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    SUBGOAL_THEN `&0 < (matrix_inv((G:real^3->real^3^3) z) ** ((lambda k. lpcurv G z (\m. if m = 1 then b0 else basis k)):real^3)) dot ((G:real^3->real^3^3) z ** (matrix_inv((G:real^3->real^3^3) z) ** ((lambda k. lpcurv G z (\m. if m = 1 then b0 else basis k)):real^3)))` ASSUME_TAC THENL
     [MATCH_MP_TAC LRG_METRIC_POS THEN EXISTS_TAC `N0:real^3->bool` THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(inv(sqrt((matrix_inv((G:real^3->real^3^3) z) ** ((lambda k. lpcurv G z (\m. if m = 1 then b0 else basis k)):real^3)) dot ((G:real^3->real^3^3) z ** (matrix_inv((G:real^3->real^3^3) z) ** ((lambda k. lpcurv G z (\m. if m = 1 then b0 else basis k)):real^3))))) % (matrix_inv((G:real^3->real^3^3) z) ** ((lambda k. lpcurv G z (\m. if m = 1 then b0 else basis k)):real^3))) dot (G z ** w) = &0` THEN
    REWRITE_TAC[DOT_LMUL; REAL_ENTIRE] THEN
    ASM_SIMP_TAC[REAL_INV_EQ_0; SQRT_POS_LT; REAL_LT_IMP_NZ];
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC RFA_GNORM_UNIT THEN
    EXISTS_TAC `N0:real^3->bool` THEN ASM_SIMP_TAC[]]);;




(* ========================================================================= *)
(* The main theorem RFA_P2B_REQ_CONE (MT Prop 4.22).                         *)
(* ========================================================================= *)

let RFA_P2B_REQ_CONE = prove
 (`!w:A->bool. P2B_REQ_RFA_CONE_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_REQ_RFA_CONE_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:real->A->real^3^3`; `a:real`; `rho:A->real`] THEN
  STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `u:real^3`; `v:real^3`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool)`
  ASSUME_TAC THENL [ASM_MESON_TAC[rfs_flow_upto; ricci_flow_on]; ALL_TAC] THEN
  SUBGOAL_THEN `!t x. a < t /\ t <= &0 /\ x IN topspace top
                      ==> &0 <= mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
                                            ((g:real->A->real^3^3) t) x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_SECMIN_NONNEG THEN
    REWRITE_TAC[DIMINDEX_3; ARITH] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `?p:A. p IN topspace top /\
                       mfd_scalar (atlas:((A->bool)#(A->real^3))->bool)
                                  ((g:real->A->real^3^3) (&0)) p = &0` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `p:A` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `&0`;
                   `g:real->A->real^3^3`; `p:A`] RFA_SPLIT_PT_END) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN MATCH_MP_TAC RFA_CONE_POS_FALSE THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                        `g:real->A->real^3^3`; `a:real`; `\y:A. (rho:A->real) y pow 2 / &2`;
                        `x:A`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC RFA_MFD_SMOOTH_SQ_HALF THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `p:A` THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= r /\ ~(r = &0) ==> &0 < r`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&6 * mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
                                ((g:real->A->real^3^3) (&0)) p` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[REAL_LE_REFL];
      MATCH_MP_TAC RFA_SCALAR_GE_6SECMIN THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[rfs_flow_upto]];
    ASM_MESON_TAC[]]);;

