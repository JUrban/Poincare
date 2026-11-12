(* ========================================================================= *)
(* Unit pc_p2b_gpb (Part 2B): general pointwise facts on pulled-back         *)
(* metrics in charts, used by G1 of MT Prop 9.20 and usable for other        *)
(* rescaled limits.  All statements are pointwise: no metric_field           *)
(* hypotheses on the pulled-back objects.                                    *)
(*                                                                           *)
(* Overlap: P2CV_P_CHART and P2CV_P_FIELD of pc_p2c_flloc give the chart     *)
(* formula and the metric_field property for the manifold metric p2cv_pb     *)
(* under p2cv_one; P2BX_MPULLBACK_COMPOSE has the statement of               *)
(* P2A_MPULLBACK_COMPOSE (pc_p2a_lgeo2), APX_MPULLBACK_CHAIN (pc_apx_chain)  *)
(* and P2CE_MPULLBACK_CHAIN (pc_p2c_cgemb), none of which is in this         *)
(* closure; P2BX_RFS_PULLBACK_LOCAL has the statement of                     *)
(* P2CV_RFS_PULLBACK_LOCAL (pc_p2c_flloc, not in this closure either).       *)
(*                                                                           *)
(* First constant metric fields; the order-0 distance is pointwise; its      *)
(* quadratic-form bound; the chain rule for mpullback and rfs_pullback.      *)
(* ========================================================================= *)

needs "src/pc_lrg_stab.ml";;
needs "src/pc_rfs_geom.ml";;

prioritize_real();;
type_invention_error := true;;

let P2BX_METRIC_FIELD_CONST = prove
 (`!(A:real^N^N). transp A = A /\ (!v. ~(v = vec 0) ==> &0 < v dot (A ** v))
                  ==> metric_field (:real^N) (\z. A)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[metric_field; OPEN_UNIV; o_DEF] THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST]);;

(* lck_dist2 0 only sees the two matrices at the point. *)

let P2BX_LCK0_PT = prove
 (`!(G0:real^N->real^N^N) G y.
     lck_dist2 0 G0 G y = lck_dist2 0 (\z. G0 y) (\z. G y) y`,
  REWRITE_TAC[lck_dist2; SUM_SING_NUMSEG; lnabla_iter; ADD_CLAUSES; ltnorm2; lmetric2]);;

(* The chain rule for mpullback. *)

let P2BX_MPULLBACK_COMPOSE = prove
 (`!(h:real^N->real^N) (k:real^N->real^N) G z.
     h differentiable at z /\ k differentiable at (h z)
     ==> mpullback h (mpullback k G) z = mpullback (k o h) G z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mpullback; o_THM] THEN
  SUBGOAL_THEN `frechet_derivative ((k:real^N->real^N) o (h:real^N->real^N)) (at (z:real^N)) =
                frechet_derivative k (at (h z)) o frechet_derivative h (at z)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN MATCH_MP_TAC DIFF_CHAIN_AT THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(frechet_derivative (k:real^N->real^N) (at (h z))) /\
                linear(frechet_derivative (h:real^N->real^N) (at z))` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[LINEAR_FRECHET_DERIVATIVE]; ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_COMPOSE; MATRIX_TRANSP_MUL; MATRIX_MUL_ASSOC]);;

(* rfs_pullback of a composition (with a chart-coordinate change Tr). *)

let P2BX_RFS_PULLBACK_COMPOSE = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) (e:real^N->A) (Tr:real^N->real^N) (g:A->real^N^N) x.
     Tr differentiable at x /\
     (SND(chart_at atlas (e(Tr x))) o e) differentiable at (Tr x)
     ==> rfs_pullback atlas (e o Tr) g x = mpullback Tr (rfs_pullback atlas e g) x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_pullback] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [mpullback] THEN
  REWRITE_TAC[o_THM] THEN
  MP_TAC(ISPECL [`Tr:real^N->real^N`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((e:real^N->A)((Tr:real^N->real^N) (x:real^N)))) o e`;
                 `metric_local (atlas:((A->bool)#(A->real^N))->bool) (chart_at atlas ((e:real^N->A)((Tr:real^N->real^N) (x:real^N))))
                               (g:A->real^N^N)`;
                 `x:real^N`] P2BX_MPULLBACK_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[mpullback; o_ASSOC] THEN MESON_TAC[]);;

(* rfs_pullback depends on the map only near the point. *)

let P2BX_RFS_PULLBACK_LOCAL = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) (e1:real^N->A) e2 (g:A->real^N^N) O x.
     open O /\ x IN O /\ (!w. w IN O ==> e1 w = e2 w)
     ==> rfs_pullback atlas e1 g x = rfs_pullback atlas e2 g x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_pullback; mpullback] THEN
  SUBGOAL_THEN `(e1:real^N->A) x = e2 x` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `frechet_derivative (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((e2:real^N->A) x)) o
                        (e1:real^N->A)) (at x) =
    frechet_derivative (SND(chart_at atlas (e2 x)) o e2) (at x)`
  (fun th -> REWRITE_TAC[th; o_THM]) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[frechet_derivative] THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `f':real^N->real^N` THEN
  UNDISCH_TAC `open(O:real^N->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EQ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THENL
   [EXISTS_TAC `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((e2:real^N->A) x)) o
                (e1:real^N->A)`;
    EXISTS_TAC `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((e2:real^N->A) x)) o
                (e2:real^N->A)`] THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[o_THM] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN O` (fun th -> ASM_SIMP_TAC[th]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[DIST_SYM]);;

(* The difference of two bilinear forms is a (0,2)-tensor field. *)

let P2BX_LMETRIC2_DIFF_TENSOR = prove
 (`!U (G0:real^N->real^N^N) G.
     ltensor_field 2 U (\z u. lmetric2 G z u - lmetric2 G0 z u)`,
  REWRITE_TAC[ltensor_field; lmetric2] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(u:num->real^N) 1 = u' 1 /\ u 2 = u' 2` (fun th -> REWRITE_TAC[th]) THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `i = 1 \/ i = 2` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[ARITH_EQ; LIFT_SUB] THEN MATCH_MP_TAC LINEAR_COMPOSE_SUB THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[DOT_SYM] THEN REWRITE_TAC[LINEAR_LIFT_DOT];
    ONCE_REWRITE_TAC[DOT_SYM] THEN REWRITE_TAC[LINEAR_LIFT_DOT];
    REWRITE_TAC[GSYM DOT_MATRIX_TRANSP_LMUL; LINEAR_LIFT_DOT];
    REWRITE_TAC[GSYM DOT_MATRIX_TRANSP_LMUL; LINEAR_LIFT_DOT]]);;

(* The order-0 quadratic-form bound, pointwise, with conditions on G0 y    *)
(* only (compare LCK_DIST_C0, which needs two metric fields).             *)

let P2BX_LCK0_QF = prove
 (`!(G0:real^N->real^N^N) G y w.
     transp(G0 y) = G0 y /\ (!v. ~(v = vec 0) ==> &0 < v dot (G0 y ** v))
     ==> abs(w dot (G y ** w) - w dot (G0 y ** w)) <=
         sqrt(lck_dist2 0 G0 G y) * (w dot (G0 y ** w))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[P2BX_LCK0_PT] THEN
  SUBGOAL_THEN `metric_field (:real^N) (\z. (G0:real^N->real^N^N) y)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX_METRIC_FIELD_CONST THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `lck_dist2 0 (\z. (G0:real^N->real^N^N) y) (\z. G y) y =
    ltnorm2 2 (\z. G0 y) (\z u. lmetric2 (\z. G y) z u - lmetric2 (\z. G0 y) z u) y`
  SUBST1_TAC THENL
   [REWRITE_TAC[lck_dist2; SUM_SING_NUMSEG; lnabla_iter; ADD_CLAUSES]; ALL_TAC] THEN
  MATCH_MP_TAC LRG_ABS_LE_SQRT_MUL THEN
  EXISTS_TAC `ltnorm2 2 (\z. (G0:real^N->real^N^N) y)
                (\z u. lmetric2 (\z. (G:real^N->real^N^N) y) z u - lmetric2 (\z. G0 y) z u) y` THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`2`; `(:real^N)`; `\z:real^N. (G0:real^N->real^N^N) y`;
                   `\z:real^N u. lmetric2 (\z. (G:real^N->real^N^N) y) z u -
                                 lmetric2 (\z. (G0:real^N->real^N^N) y) z u`;
                   `y:real^N`; `\m:num. (w:real^N)`] LRG_LTNORM2_BOUND) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[IN_UNIV; P2BX_LMETRIC2_DIFF_TENSOR]; ALL_TAC] THEN
    REWRITE_TAC[PRODUCT_CONST_NUMSEG; lmetric2] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[];
    REAL_ARITH_TAC;
    MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `(:real^N)` THEN
    ASM_REWRITE_TAC[IN_UNIV; P2BX_LMETRIC2_DIFF_TENSOR];
    ASM_CASES_TAC `w:real^N = vec 0` THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_SIMP_TAC[]]);;

(* ========================================================================= *)
(* The chart change of rfs_pullback on the source side, quadratic-form       *)
(* bounds under congruence, entries from quadratic forms.                    *)
(* ========================================================================= *)

(* The chart change on the source side: f o chart_inv c versus f o          *)
(* chart_inv c' at a common point y of the two chart domains.              *)

let P2BX_RFS_PULLBACK_TRANS = prove
 (`!(top':B topology) atlas' (atlas:((A->bool)#(A->real^N))->bool) (f:B->A)
    (G:A->real^N^N) (c:(B->bool)#(B->real^N)) c' y.
     smooth_manifold_atlas top' atlas' /\ c IN atlas' /\ c' IN atlas' /\
     y IN FST c /\ y IN FST c' /\
     (SND(chart_at atlas (f y)) o f o chart_inv c') differentiable at (SND c' y)
     ==> rfs_pullback atlas (f o chart_inv c) G (SND c y) =
         transp(matrix(chart_jac c c' y)) **
         rfs_pullback atlas (f o chart_inv c') G (SND c' y) **
         matrix(chart_jac c c' y)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:B->bool`; `phi:B->real^N`; `V:B->bool`; `psi:B->real^N`; `y:B`] THEN
  REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `U:B->bool`; `phi:B->real^N`] CHART_INV) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `V:B->bool`; `psi:B->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `!x:B. x IN U ==> chart_trans (U,phi:B->real^N) (V,psi) (phi x) = psi x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CHART_TRANS_AT THEN
    MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `rfs_pullback (atlas:((A->bool)#(A->real^N))->bool)
      (((f:B->A) o chart_inv (V:B->bool,psi:B->real^N)) o
       chart_trans (U:B->bool,phi:B->real^N) (V,psi))
      (G:A->real^N^N) (phi(y:B))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2BX_RFS_PULLBACK_LOCAL THEN
    EXISTS_TAC `IMAGE (phi:B->real^N) (U INTER V)` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[CHART_OVERLAP_IMAGE_OPEN]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER; o_THM] THEN
    X_GEN_TAC `x:B` THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`;
                 `(f:B->A) o chart_inv (V:B->bool,psi:B->real^N)`;
                 `chart_trans (U:B->bool,phi:B->real^N) (V,psi)`;
                 `G:A->real^N^N`; `(phi:B->real^N) y`] P2BX_RFS_PULLBACK_COMPOSE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[differentiable] THEN
      EXISTS_TAC `chart_jac (U:B->bool,phi:B->real^N) (V,psi) y` THEN
      MATCH_MP_TAC CHART_TRANS_HAS_DERIVATIVE THEN
      MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`] THEN
      ASM_REWRITE_TAC[IN_INTER];
      ASM_SIMP_TAC[o_THM]];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[mpullback; chart_jac; SND] THEN
  ASM_SIMP_TAC[]);;

(* Quadratic-form bounds are preserved under congruence by any matrix J.    *)

let P2BX_QF_CONGRUENCE = prove
 (`!(A:real^N^N) B (J:real^N^N) s.
     (!w. abs(w dot (A ** w) - w dot (B ** w)) <= s * (w dot (B ** w)))
     ==> !v. abs(v dot ((transp J ** A ** J) ** v) - v dot ((transp J ** B ** J) ** v)) <=
             s * (v dot ((transp J ** B ** J) ** v))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  REWRITE_TAC[DOT_MATRIX_TRANSP_RMUL] THEN ASM_REWRITE_TAC[]);;

(* Entries of a symmetric matrix D from a bound on its quadratic form       *)
(* relative to B0 (polarization).                                           *)

let P2BX_ENTRY_FROM_QF = prove
 (`!(D:real^N^N) (B0:real^N^N) s i j.
     transp D = D /\ 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
     (!w. abs(w dot (D ** w)) <= s * (w dot (B0 ** w)))
     ==> abs(D$i$j) <= s * (B0$i$i + B0$j$j) / &2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!u v:real^N. u dot ((D:real^N^N) ** v) = v dot (D ** u)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    SUBGOAL_THEN `u dot ((D:real^N^N) ** v) = u dot (transp D ** v)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[DOT_MATRIX_TRANSP_RMUL] THEN MATCH_ACCEPT_TAC DOT_SYM;
    ALL_TAC] THEN
  SUBGOAL_THEN `basis i dot ((D:real^N^N) ** basis j) = D$i$j` ASSUME_TAC THENL
   [ASM_SIMP_TAC[DOT_BASIS; MATRIX_VECTOR_MUL_BASIS; column; LAMBDA_BETA]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(D:real^N^N)$i$j =
    ((basis i + basis j) dot (D ** (basis i + basis j)) -
     (basis i - basis j) dot (D ** (basis i - basis j))) / &4`
  SUBST1_TAC THENL
   [REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_SUB_LDISTRIB;
                DOT_LADD; DOT_RADD; DOT_LSUB; DOT_RSUB] THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
      [SPECL [`basis j:real^N`; `basis i:real^N`] th]) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(basis i + basis j) dot ((B0:real^N^N) ** (basis i + basis j)) +
    (basis i - basis j) dot (B0 ** (basis i - basis j)) =
    &2 * (B0$i$i + B0$j$j)`
  ASSUME_TAC THENL
   [REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_SUB_LDISTRIB;
                DOT_LADD; DOT_RADD; DOT_LSUB; DOT_RSUB] THEN
    ASM_SIMP_TAC[DOT_BASIS; MATRIX_VECTOR_MUL_BASIS; column; LAMBDA_BETA] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs((basis i + basis j) dot ((D:real^N^N) ** (basis i + basis j))) <=
    s * ((basis i + basis j) dot ((B0:real^N^N) ** (basis i + basis j))) /\
    abs((basis i - basis j) dot (D ** (basis i - basis j))) <=
    s * ((basis i - basis j) dot (B0 ** (basis i - basis j)))`
  MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `(*) (s:real)` o check (fun th ->
    can (find_term (fun t -> t = `&2`)) (concl th) && is_eq (concl th))) THEN
  REAL_ARITH_TAC);;

