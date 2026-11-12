(* ========================================================================= *)
(* pc_p2b_p946s: soliton calculus and properness of the potential f for MT   *)
(* Prop 9.46.                                                                *)
(* Local (any N, in a chart, on the shrinker equation of RFA_SH_CHART_DATA): *)
(* (9.21) in coordinates dR(w) = 2 Ric(grad F, w) (P2BX46_DR_GRAD, from the  *)
(* frame form RFA_S2_SOLITON_DR), d|dF|^2(w) = dF(w) - 2 Ric(grad F, w)      *)
(* (P2BX46_DLGRAD2_SHRINK, from RFA_DNORM2_FORM) and Hamilton's identity     *)
(* d(R + |dF|^2 - F) = 0 (P2BX46_LOCAL_HAMILTON).                            *)
(* Manifold: R + |grad f|^2 - f = C on a connected shrinker                  *)
(* (P2BX46_MFD_HAMILTON_GEN); (f o gamma)'' = |gamma'|^2/2 - Ric along       *)
(* geodesics (P2BX46_GEO_F2); MT (9.24) along minimizing geodesics with      *)
(* Claim 9.47 = CMP_RICCI_INTEGRAL (P2BX46_F_GEO_LOWER); with R >= 0, f >=   *)
(* -C and |grad f|^2 <= f + C (P2BX46_HAMILTON_BOUNDS), f >= d^2/4 - C1 d -  *)
(* C0 (P2BX46_F_LOWER_GLOBAL), sublevel sets compact (P2BX46_F_PROPER).      *)
(* ========================================================================= *)

needs "src/pc_rfa_s2loc.ml";;
needs "src/pc_mfd_cflow.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Local soliton calculus in a chart: (9.21) in coordinates, dR = 2 Ric(grad *)
(* pf, .), and Hamilton's identity d(R + |dpf|^2 - pf) = 0.                  *)
(* ========================================================================= *)

(* Sums over index tuples of length 1 (the 3-line proof of                  *)
(* S2E_SUM_INDEX_TUPLES_1 of pc_s2ent_calc, which is not in this closure).  *)

let P2BX46_SUM_TUPLES_1 = prove
 (`!f. sum (index_tuples 1 (:N)) f =
       sum(1..dimindex(:N)) (\q. f (\m. if m = 1 then q else 0))`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`f:(num->num)->real`; `0`] LRG_SUM_INDEX_TUPLES_SUC) THEN
  REWRITE_TAC[ADD_CLAUSES; LRG_SUM_INDEX_TUPLES_0]);;

let P2BX46_LGRAD2_LTNORM2 = prove
 (`!(G:real^N->real^N^N) (pf:real^N->real) y.
     lgrad2 G pf y = ltnorm2 1 G (rfa_sh_df pf) y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[lgrad2; ltnorm2; P2BX46_SUM_TUPLES_1; PRODUCT_SING_NUMSEG; rfa_sh_df] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[] THEN MATCH_ACCEPT_TAC(REAL_ARITH `!x y z:real. x * y * z = y * z * x`));;

(* The Hessian lnabla 1 G (rfa_sh_df pf) depends on the first two slots only. *)

let P2BX46_HESS_SLOTS = prove
 (`!(G:real^N->real^N^N) (pf:real^N->real) y u u'.
     u 1 = u' 1 /\ u 2 = u' 2
     ==> lnabla 1 G (rfa_sh_df pf) y u = lnabla 1 G (rfa_sh_df pf) y u'`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[lnabla; rfa_sh_df; SUM_SING_NUMSEG] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[]);;

(* The derivative of |dF|^2 is twice the Hessian against grad pf. *)

let P2BX46_DLGRAD2 = prove
 (`!U (G:real^N->real^N^N) (pf:real^N->real) y w.
     metric_field U G /\ smooth_map_on U (\z. lift(pf z)) /\ y IN U
     ==> drop(frechet_derivative (\x. lift(lgrad2 G pf x)) (at y) w) =
         &2 * sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
                matrix_inv(G y)$a$b * rfa_d1 pf y (basis a) *
                lnabla 1 G (rfa_sh_df pf) y (\m. if m = 1 then basis b else w)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `pf:real^N->real`] RFA_SH_DF_SF) THEN
  ASM_REWRITE_TAC[rfa_sf] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x. lift(lgrad2 (G:real^N->real^N^N) pf x)) =
                (\x. lift(ltnorm2 1 G (rfa_sh_df pf) x))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; P2BX46_LGRAD2_LTNORM2]; ALL_TAC] THEN
  MP_TAC(ISPECL [`1`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `rfa_sh_df (pf:real^N->real)`; `y:real^N`; `w:real^N`] RFA_DNORM2_FORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[ltinner; P2BX46_SUM_TUPLES_1; PRODUCT_SING_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `lnabla 1 G (rfa_sh_df pf) y
      (\m. if m = 1 + 1 then w else basis (if m = 1 then b else 0)) =
    lnabla 1 (G:real^N->real^N^N) (rfa_sh_df (pf:real^N->real)) y
      (\m. if m = 1 then basis b else w)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC P2BX46_HESS_SLOTS THEN BETA_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[rfa_sh_df; rfa_d1] THEN
  MATCH_ACCEPT_TAC(REAL_ARITH `!x y z:real. x * y * z = z * x * y`));;

let P2BX46_GINV_SYM = prove
 (`!U (G:real^N->real^N^N) y.
     metric_field U G /\ y IN U ==> transp(matrix_inv(G y)) = matrix_inv(G y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM MATRIX_INV_TRANSP] THEN
  ASM_MESON_TAC[metric_field]);;

(* Linearity of lricci in each slot, in sum form. *)

let P2BX46_LRICCI_VSUM1 = prove
 (`!U (G:real^N->real^N^N) y (s:num->bool) (c:num->real) (v:num->real^N) w.
     metric_field U G /\ y IN U /\ FINITE s
     ==> lricci G y (vsum s (\r. c r % v r)) w = sum s (\r. c r * lricci G y (v r) w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_LRICCI_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `w:real^N` o CONJUNCT1) THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM LIFT_EQ] THEN
  REWRITE_TAC[LIFT_SUM; o_DEF; LIFT_CMUL] THEN
  MP_TAC(ISPECL [`\a:real^N. lift(lricci (G:real^N->real^N^N) y a w)`;
                 `\r:num. (c:num->real) r % (v:num->real^N) r`; `s:num->bool`] LINEAR_VSUM) THEN
  ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[BETA_RULE(MATCH_MP LINEAR_CMUL th)]));;

let P2BX46_LRICCI_VSUM2 = prove
 (`!U (G:real^N->real^N^N) y (s:num->bool) (c:num->real) (v:num->real^N) a.
     metric_field U G /\ y IN U /\ FINITE s
     ==> lricci G y a (vsum s (\r. c r % v r)) = sum s (\r. c r * lricci G y a (v r))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_LRICCI_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `a:real^N` o CONJUNCT2) THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM LIFT_EQ] THEN
  REWRITE_TAC[LIFT_SUM; o_DEF; LIFT_CMUL] THEN
  MP_TAC(ISPECL [`\b:real^N. lift(lricci (G:real^N->real^N^N) y a b)`;
                 `\r:num. (c:num->real) r % (v:num->real^N) r`; `s:num->bool`] LINEAR_VSUM) THEN
  ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[BETA_RULE(MATCH_MP LINEAR_CMUL th)]));;

(* Two linear functionals agreeing on a G0-orthonormal frame agree. *)

let P2BX46_FRAME_LINEAR_EQ = prove
 (`!(G0:real^N^N) (S:real^N^N) (f:real^N->real^1) g.
     invertible G0 /\ invertible S /\ matrix_inv G0 = transp S ** S /\
     linear f /\ linear g /\
     (!b. 1 <= b /\ b <= dimindex(:N) ==> f(transp S ** basis b) = g(transp S ** basis b))
     ==> !v. f v = g v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G0:real^N^N`; `S:real^N^N`; `v:real^N`] RFA_FRAME_VEXPAND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN ASM_SIMP_TAC[]);;

(* The coordinate gradient covector D = (dF(e_a)) represents dF. *)

let P2BX46_D1_DOT = prove
 (`!U (pf:real^N->real) y.
     open U /\ smooth_map_on U (\z. lift(pf z)) /\ y IN U
     ==> !u. u dot ((lambda a. rfa_d1 pf y (basis a)):real^N) = rfa_d1 pf y u /\
             ((lambda a. rfa_d1 pf y (basis a)):real^N) dot u = rfa_d1 pf y u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC(MESON[DOT_SYM] `!x y:real^N. x dot y = z ==> x dot y = z /\ y dot x = z`) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `pf:real^N->real`; `y:real^N`] RFA_D1_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [CONJUNCT2(CONJUNCT2 th)]) THEN
  REWRITE_TAC[dot] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  SIMP_TAC[LAMBDA_BETA]);;

(* (9.21) in coordinates: dR(w) = 2 Ric(grad pf, w), grad pf = G^-1 D. *)

let P2BX46_DR_GRAD = prove
 (`!U (G:real^N->real^N^N) (pf:real^N->real) y w.
     metric_field U G /\ y IN U /\ smooth_map_on U (\z. lift(pf z)) /\
     rfa_eqon U (lnabla 1 G (rfa_sh_df pf)) (\y u. inv(&2) * lmetric2 G y u - lric2 G y u)
     ==> drop(frechet_derivative (\x. lift(lscalar G x)) (at y) w) =
         &2 * lricci G y (matrix_inv(G y) ** (lambda a. rfa_d1 pf y (basis a))) w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_METRIC_INV_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S:real^N^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_METRIC_INVERTIBLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `pf:real^N->real`; `y:real^N`] P2BX46_D1_DOT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "dot")] THEN
  ABBREV_TAC `D = (lambda a. rfa_d1 (pf:real^N->real) y (basis a)):real^N` THEN
  SUBGOAL_THEN
   `matrix_inv((G:real^N->real^N^N) y) ** D =
    vsum(1..dimindex(:N))
      (\r. rfa_d1 (pf:real^N->real) y (transp (S:real^N^N) ** basis r) %
            (transp S ** basis r))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `S:real^N^N`;
                   `matrix_inv((G:real^N->real^N^N) y) ** D`] RFA_FRAME_VEXPAND) THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN BETA_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN USE_THEN "dot" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v. frechet_derivative (\x. lift(lscalar (G:real^N->real^N^N) x)) (at y) v =
        (\w. lift(&2 * lricci G y (matrix_inv(G y) ** D) w)) v`
  (fun th -> REWRITE_TAC[th; LIFT_DROP]) THEN
  MATCH_MP_TAC P2BX46_FRAME_LINEAR_EQ THEN
  MAP_EVERY EXISTS_TAC [`(G:real^N->real^N^N) y`; `S:real^N^N`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[LRG_LSCALAR_SMOOTH];
    REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_LRICCI_LINEAR) THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `b:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `pf:real^N->real`; `y:real^N`;
                   `S:real^N^N`; `b:num`] RFA_S2_SOLITON_DR) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM LIFT_DROP] THEN
                         REWRITE_TAC[th]) THEN
    REWRITE_TAC[LIFT_EQ] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRICCI_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `1..dimindex(:N)`;
                   `\r. rfa_d1 (pf:real^N->real) y (transp (S:real^N^N) ** basis r)`;
                   `\r. transp (S:real^N^N) ** basis r`; `transp(S:real^N^N) ** basis b`]
      P2BX46_LRICCI_VSUM2) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[rfa_sh_df; rfa_ft; rfa_d1] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[EL; HD] THEN MATCH_ACCEPT_TAC REAL_MUL_SYM]);;

(* Hamilton's identity in a chart: d(R + |dF|^2 - F) = 0 on a shrinker. *)

let P2BX46_DLGRAD2_SHRINK = prove
 (`!U (G:real^N->real^N^N) (pf:real^N->real) y w.
     metric_field U G /\ y IN U /\ smooth_map_on U (\z. lift(pf z)) /\
     rfa_eqon U (lnabla 1 G (rfa_sh_df pf)) (\y u. inv(&2) * lmetric2 G y u - lric2 G y u)
     ==> drop(frechet_derivative (\x. lift(lgrad2 G pf x)) (at y) w) =
         rfa_d1 pf y w -
         &2 * lricci G y (matrix_inv(G y) ** (lambda a. rfa_d1 pf y (basis a))) w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `pf:real^N->real`; `y:real^N`;
                 `w:real^N`] P2BX46_DLGRAD2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `!b. lnabla 1 G (rfa_sh_df pf) y (\m. if m = 1 then basis b else w) =
        inv(&2) * (basis b dot ((G:real^N->real^N^N) y ** w)) - lricci G y (basis b) w`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    UNDISCH_TAC `rfa_eqon U (lnabla 1 (G:real^N->real^N^N) (rfa_sh_df pf))
                   (\y u. inv(&2) * lmetric2 G y u - lric2 G y u)` THEN
    REWRITE_TAC[rfa_eqon] THEN
    DISCH_THEN(MP_TAC o SPECL [`y:real^N`; `\m. if m = 1 then basis b else w:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[lmetric2; lric2] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `pf:real^N->real`; `y:real^N`] P2BX46_D1_DOT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "dot")] THEN
  ABBREV_TAC `D = (lambda a. rfa_d1 (pf:real^N->real) y (basis a)):real^N` THEN
  SUBGOAL_THEN `!a. 1 <= a /\ a <= dimindex(:N) ==> rfa_d1 (pf:real^N->real) y (basis a) = (D:real^N)$a`
  ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN SIMP_TAC[LAMBDA_BETA]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_METRIC_INVERTIBLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
       matrix_inv((G:real^N->real^N^N) y)$a$b * rfa_d1 pf y (basis a) *
       (inv(&2) * (basis b dot (G y ** w)) - lricci G y (basis b) w))) =
    inv(&2) * sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
       matrix_inv(G y)$a$b * rfa_d1 pf y (basis a) * (G y ** w)$b)) -
    sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
       matrix_inv(G y)$a$b * rfa_d1 pf y (basis a) * lricci G y (basis b) w))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_SUB_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_SUB_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
    ASM_SIMP_TAC[DOT_BASIS] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
       matrix_inv((G:real^N->real^N^N) y)$a$b * rfa_d1 pf y (basis a) * (G y ** w)$b)) =
    rfa_d1 pf y w`
  SUBST1_TAC THENL
   [SUBGOAL_THEN
     `!a. sum(1..dimindex(:N)) (\b. matrix_inv((G:real^N->real^N^N) y)$a$b * (G y ** w)$b) =
          if 1 <= a /\ a <= dimindex(:N) then (w:real^N)$a else
          sum(1..dimindex(:N)) (\b. matrix_inv((G:real^N->real^N^N) y)$a$b * (G y ** w)$b)`
    ASSUME_TAC THENL
     [GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN REWRITE_TAC[GSYM dot] THEN
      ASM_SIMP_TAC[GSYM MATRIX_VECTOR_MUL_COMPONENT; MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV;
                   MATRIX_VECTOR_MUL_LID];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `pf:real^N->real`; `y:real^N`] RFA_D1_LINEAR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [CONJUNCT2(CONJUNCT2 th)]) THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
    TRANS_TAC EQ_TRANS
     `rfa_d1 (pf:real^N->real) y (basis a) *
      sum(1..dimindex(:N)) (\b. matrix_inv((G:real^N->real^N^N) y)$a$b * (G y ** w)$b)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `a:num`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N)) (\a. sum(1..dimindex(:N)) (\b.
       matrix_inv((G:real^N->real^N^N) y)$a$b * rfa_d1 pf y (basis a) *
       lricci G y (basis b) w)) =
    lricci G y (matrix_inv(G y) ** (D:real^N)) w`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `1..dimindex(:N)`;
                   `\b. (matrix_inv((G:real^N->real^N^N) y) ** (D:real^N))$b`;
                   `\b:num. basis b:real^N`; `w:real^N`] P2BX46_LRICCI_VSUM1) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[FINITE_NUMSEG]; REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[REAL_MUL_ASSOC; SUM_RMUL] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT; ASSUME `1 <= b`; ASSUME `b <= dimindex(:N)`] THEN
    REWRITE_TAC[dot] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `rfa_d1 (pf:real^N->real) y (basis a) = (D:real^N)$a` SUBST1_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] P2BX46_GINV_SYM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o LAND_CONV o LAND_CONV)
                 [GSYM th]) THEN
    ASM_SIMP_TAC[TRANSP_COMPONENT];
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

let P2BX46_LOCAL_HAMILTON = prove
 (`!U (G:real^N->real^N^N) (pf:real^N->real) y w.
     metric_field U G /\ y IN U /\ smooth_map_on U (\z. lift(pf z)) /\
     rfa_eqon U (lnabla 1 G (rfa_sh_df pf)) (\y u. inv(&2) * lmetric2 G y u - lric2 G y u)
     ==> drop(frechet_derivative (\x. lift(lscalar G x)) (at y) w) +
         drop(frechet_derivative (\x. lift(lgrad2 G pf x)) (at y) w) -
         rfa_d1 pf y w = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `pf:real^N->real`; `y:real^N`;
                 `w:real^N`] P2BX46_DR_GRAD) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `pf:real^N->real`; `y:real^N`;
                 `w:real^N`] P2BX46_DLGRAD2_SHRINK) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let P2BX46_LOCAL_HAMILTON_DERIV = prove
 (`!U (G:real^N->real^N^N) (pf:real^N->real) z.
     metric_field U G /\ z IN U /\ smooth_map_on U (\z. lift(pf z)) /\
     rfa_eqon U (lnabla 1 G (rfa_sh_df pf)) (\y u. inv(&2) * lmetric2 G y u - lric2 G y u)
     ==> ((\w. lift(lscalar G w + lgrad2 G pf w - pf w)) has_derivative (\v. vec 0)) (at z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\w. lift(lscalar (G:real^N->real^N^N) w)) differentiable at z /\
    (\w. lift(lgrad2 G pf w)) differentiable at z /\
    (\w. lift((pf:real^N->real) w)) differentiable at z`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[LRG_LSCALAR_SMOOTH] THEN
    REWRITE_TAC[P2BX46_LGRAD2_LTNORM2] THEN MATCH_MP_TAC LRG_LTNORM2_SMOOTH THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `pf:real^N->real`] RFA_SH_DF_SF) THEN
    ASM_SIMP_TAC[rfa_sf];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\v:real^N. vec 0:real^1) =
    (\v. frechet_derivative (\w. lift(lscalar (G:real^N->real^N^N) w)) (at z) v +
         frechet_derivative (\w. lift(lgrad2 G pf w)) (at z) v -
         frechet_derivative (\w. lift((pf:real^N->real) w)) (at z) v)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `v:real^N` THEN
    ONCE_REWRITE_TAC[GSYM DROP_EQ] THEN REWRITE_TAC[DROP_ADD; DROP_SUB; DROP_VEC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `pf:real^N->real`; `z:real^N`;
                   `v:real^N`] P2BX46_LOCAL_HAMILTON) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[rfa_d1]] THEN
    DISCH_THEN(fun th ->
      MATCH_MP_TAC(REAL_ARITH `!a b c:real. a + b - c = &0 ==> &0 = a + b - c`) THEN
      ACCEPT_TAC th);
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_ADD; LIFT_SUB] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[ETA_AX; GSYM FRECHET_DERIVATIVE_WORKS];
    MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
    ASM_REWRITE_TAC[ETA_AX; GSYM FRECHET_DERIVATIVE_WORKS]]);;


(* ========================================================================= *)
(* Manifold forms.  |grad f|^2 in any chart; Hamilton's identity R + |grad   *)
(* f|^2 - f = C on a connected shrinker.                                     *)
(* ========================================================================= *)

(* |grad f|^2 does not depend on the chart (template LSCALAR_CHART_TRANS). *)

let P2BX46_LGRAD2_CHART_TRANS = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) V psi (g:A->real^N^N) (f:A->real) x.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        (U,phi) IN atlas /\ (V,psi) IN atlas /\ x IN U INTER V /\
        smooth_map_on (IMAGE psi V) (\y. lift(f(chart_inv (V,psi) y)))
        ==> lgrad2 (metric_local atlas (U,phi) g) (\y. f(chart_inv (U,phi) y)) (phi x) =
            lgrad2 (metric_local atlas (V,psi) g) (\y. f(chart_inv (V,psi) y)) (psi x)`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
   `lgrad2 (mpullback (chart_trans (U:A->bool,phi:A->real^N) (V,psi))
                      (metric_local atlas (V,psi) (g:A->real^N^N)))
           ((\y. (f:A->real)(chart_inv (V,psi) y)) o chart_trans (U,phi) (V,psi))
           (phi x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LGRAD2_LOCAL THEN
    EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER V)` THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CHART_OVERLAP_IMAGE_OPEN]; ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `p:A` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_LOCAL_TRANS THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[o_THM] THEN
      MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                    `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`;
                    `p:A`] CHART_TRANS_AT) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                    `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
      MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                    `V:A->bool`; `psi:A->real^N`] CHART_INV) THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`;
                `x:A`] CHART_TRANS_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
  MATCH_MP_TAC LGRAD2_PULLBACK THEN
  MAP_EVERY EXISTS_TAC
   [`IMAGE (psi:A->real^N) (U INTER V)`; `IMAGE (phi:A->real^N) (U INTER V)`;
    `chart_trans (V:A->bool,psi:A->real^N) (U,phi)`] THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN REPEAT CONJ_TAC THENL
   [ONCE_REWRITE_TAC[INTER_COMM] THEN
    MATCH_MP_TAC RIEMANNIAN_METRIC_OVERLAP THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `phi:A->real^N`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC CHART_TRANS_DIFFEO THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (psi:A->real^N) V` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

let P2BX46_LGRAD2_CHART = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) c' (g:A->real^N^N) (f:A->real) x.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        c IN atlas /\ c' IN atlas /\ x IN FST c INTER FST c' /\
        smooth_map_on (IMAGE (SND c') (FST c')) (\y. lift(f(chart_inv c' y)))
        ==> lgrad2 (metric_local atlas c g) (\y. f(chart_inv c y)) (SND c x) =
            lgrad2 (metric_local atlas c' g) (\y. f(chart_inv c' y)) (SND c' x)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC P2BX46_LGRAD2_CHART_TRANS THEN EXISTS_TAC `top:A topology` THEN
  ASM_REWRITE_TAC[]);;

(* Hamilton's identity on a connected shrinker, any dimension. *)

let P2BX46_MFD_HAMILTON_GEN = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f.
     connected_space top /\ p2b_shrinker (top,atlas) g f
     ==> ?C. !x. x IN topspace top
                 ==> mfd_scalar atlas g x +
                     lgrad2 (metric_local atlas (chart_at atlas x) g)
                            (\y. f(chart_inv (chart_at atlas x) y))
                            (SND(chart_at atlas x) x) - f x = C`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[p2b_shrinker]) THEN
  ABBREV_TAC
   `h = \x:A. mfd_scalar atlas g x +
              lgrad2 (metric_local atlas (chart_at atlas x) (g:A->real^N^N))
                     (\y. f(chart_inv (chart_at atlas x) y))
                     (SND(chart_at atlas x) x) - f x` THEN
  SUBGOAL_THEN
   `!(c:(A->bool)#(A->real^N)) (z:real^N).
          c IN atlas /\ z IN IMAGE (SND c) (FST c)
          ==> ((\w. lift((h:A->real)(chart_inv c w))) has_derivative (\v. vec 0)) (at z)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^N)`; `z:real^N`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `f:A->real`; `c:(A->bool)#(A->real^N)`]
      RFA_SH_CHART_DATA) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ABBREV_TAC `Gc = metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)` THEN
    ABBREV_TAC `fc = \y. (f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y)` THEN
    SUBGOAL_THEN
     `!w. w IN IMAGE (SND c) (FST c)
          ==> (h:A->real)(chart_inv (c:(A->bool)#(A->real^N)) w) =
              lscalar (Gc:real^N->real^N^N) w + lgrad2 Gc fc w - fc w`
    ASSUME_TAC THENL
     [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN EXPAND_TAC "h" THEN BETA_TAC THEN
      SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) w IN FST c /\
                    chart_inv c w IN topspace top /\ SND c (chart_inv c w) = w`
      STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[MCF_CHART_FACTS]; ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `c:(A->bool)#(A->real^N)`;
                     `chart_inv (c:(A->bool)#(A->real^N)) w`] RFA_SH_QR_CHART) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o CONJUNCT2)] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `chart_at (atlas:((A->bool)#(A->real^N))->bool)
                               (chart_inv (c:(A->bool)#(A->real^N)) w)`;
                     `c:(A->bool)#(A->real^N)`; `g:A->real^N^N`; `f:A->real`;
                     `chart_inv (c:(A->bool)#(A->real^N)) w`] P2BX46_LGRAD2_CHART) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[IN_INTER] THEN ASM_MESON_TAC[CHART_AT];
        DISCH_THEN SUBST1_TAC] THEN
      MAP_EVERY EXPAND_TAC ["Gc"; "fc"] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `\w. lift(lscalar (Gc:real^N->real^N^N) w + lgrad2 Gc fc w - fc w)` THEN
    MP_TAC(ISPEC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` OPEN_CONTAINS_BALL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `z:real^N`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      REWRITE_TAC[LIFT_EQ] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `ball(z:real^N,d) SUBSET IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
      REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_MESON_TAC[DIST_SYM];
      ALL_TAC] THEN
    MATCH_MP_TAC P2BX46_LOCAL_HAMILTON_DERIV THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
    MAP_EVERY EXPAND_TAC ["Gc"; "fc"] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `h:A->real`]
    RFA_S2_LOCCONST_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `h:A->real`] RFA_SH_LOCCONST_CONNECTED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ASM_CASES_TAC `topspace top:A->bool = {}` THENL
   [ASM_REWRITE_TAC[NOT_IN_EMPTY]; ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `x0:A` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  EXISTS_TAC `(h:A->real) x0` THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(h:A->real) x = h x0` MP_TAC THENL
   [ASM_MESON_TAC[]; EXPAND_TAC "h" THEN REWRITE_TAC[]]);;


(* ========================================================================= *)
(* Geodesics of a shrinker: (f o gamma)'' = |gamma'|^2/2 - Ric.              *)
(* ========================================================================= *)

(* (f o gamma)'' = |gamma'|^2 / 2 - Ric(gamma',gamma') along geodesics of  *)
(* a shrinker, any dimension (adapted from RFA_S2_GEO_F2, pc_rfa_s2geo).    *)

let P2BX46_GEO_F2 = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (f:A->real)
    (gamma:real->A) J t.
     p2b_shrinker (top,atlas) g f /\
     mfd_geodesic (top,atlas) g gamma J /\ t IN J
     ==> (\s. f(gamma s)) real_differentiable atreal t /\
         (real_derivative (\s. f(gamma s)) has_real_derivative
            (inv(&2) * (mfd_vel atlas gamma t dot (g(gamma t) ** mfd_vel atlas gamma t)) -
             mfd_ricci atlas g (gamma t) (mfd_vel atlas gamma t) (mfd_vel atlas gamma t)))
         (atreal t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  SUBGOAL_THEN `(gamma:real->A) t IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[GEOL_GEODESIC_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `(gamma:real->A) t`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?U phi. chart_at atlas ((gamma:real->A) t) = (U:A->bool,phi:A->real^N)`
  STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[FST] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `(U:A->bool,phi:A->real^N)`] RFA_SH_CHART_DATA) THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `gamma:real->A`; `J:real->bool`; `(U:A->bool,phi:A->real^N)`]
                GEOL_GEODESIC_CHART_VEL_EXISTS) THEN
  ASM_REWRITE_TAC[FST; SND] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real->real^N` (LABEL_TAC "vv")) THEN
  MP_TAC(ISPECL [`top:A topology`; `gamma:real->A`; `J:real->bool`; `U:A->bool`; `t:real`]
                GEOL_CURVE_NEAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[GEOL_GEODESIC_BASIC]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "near"))) THEN
  SUBGOAL_THEN
   `!s. abs(s - t) < d
        ==> (f:A->real)((gamma:real->A) s) =
            f(chart_inv (U,phi) ((phi:A->real^N)(gamma s)))`
  (LABEL_TAC "loc") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "near" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `abs(s - t) < d`))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. abs(s - t) < d
        ==> ((\s. (f:A->real)((gamma:real->A) s)) has_real_derivative
             drop(frechet_derivative (\y. lift(f(chart_inv (U,phi) y)))
                    (at ((phi:A->real^N)(gamma s))) ((v:real->real^N) s))) (atreal s)`
  (LABEL_TAC "d1") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "near" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `abs(s - t) < d`))) THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    EXISTS_TAC `\r. (f:A->real)(chart_inv (U,phi) ((phi:A->real^N)((gamma:real->A) r)))` THEN
    EXISTS_TAC `d - abs(s - t)` THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `r:real` THEN DISCH_TAC THEN BETA_TAC THEN CONV_TAC SYM_CONV THEN
      USE_THEN "loc" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF; LIFT_DROP] THEN
    MP_TAC(ISPECL [`IMAGE (phi:A->real^N) U`;
                   `\y. (f:A->real)(chart_inv (U:A->bool,phi:A->real^N) y)`;
                   `\r. (phi:A->real^N)((gamma:real->A)(drop r))`; `(v:real->real^N) s`;
                   `lift s`] RFA_S2_CURVE_D1) THEN
    REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      USE_THEN "vv" (fun th -> MP_TAC(MATCH_MP th (CONJ (ASSUME `(s:real) IN J`)
                                                        (ASSUME `(gamma:real->A) s IN U`)))) THEN
      SIMP_TAC[];
      REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\s. drop(frechet_derivative (\y. lift((f:A->real)(chart_inv (U,phi) y)))
              (at ((phi:A->real^N)((gamma:real->A) s))) ((v:real->real^N) s)))
     has_real_derivative
     lnabla 1 (metric_local atlas (U,phi) (g:A->real^N^N))
       (rfa_sh_df (\y. f(chart_inv (U,phi) y))) (phi(gamma t)) (\m. v t)) (atreal t)`
  ASSUME_TAC THENL
   [REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF; LIFT_DROP] THEN
    MP_TAC(ISPECL [`IMAGE (phi:A->real^N) U`; `metric_local atlas (U,phi) (g:A->real^N^N)`;
                   `\y. (f:A->real)(chart_inv (U:A->bool,phi:A->real^N) y)`;
                   `\r. (phi:A->real^N)((gamma:real->A)(drop r))`;
                   `\r. (v:real->real^N)(drop r)`; `lift t`] RFA_S2_CURVE_HESS) THEN
    REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      USE_THEN "vv" (fun th -> MP_TAC(MATCH_MP th (CONJ (ASSUME `(t:real) IN J`)
                                                        (ASSUME `(gamma:real->A) t IN U`)))) THEN
      SIMP_TAC[];
      REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lnabla 1 (metric_local atlas (U,phi) (g:A->real^N^N))
      (rfa_sh_df (\y. (f:A->real)(chart_inv (U,phi) y))) ((phi:A->real^N)((gamma:real->A) t))
      (\m. (v:real->real^N) t) =
    inv(&2) * (mfd_vel atlas gamma t dot (g(gamma t) ** mfd_vel atlas gamma t)) -
    mfd_ricci atlas g (gamma t) (mfd_vel atlas gamma t) (mfd_vel atlas gamma t)`
  SUBST_ALL_TAC THENL
   [UNDISCH_TAC
     `rfa_eqon (IMAGE (phi:A->real^N) U)
        (lnabla 1 (metric_local atlas (U,phi) (g:A->real^N^N))
           (rfa_sh_df (\y. (f:A->real)(chart_inv (U,phi) y))))
        (\y u. inv(&2) * lmetric2 (metric_local atlas (U,phi) g) y u -
               lric2 (metric_local atlas (U,phi) g) y u)` THEN
    REWRITE_TAC[rfa_eqon] THEN
    DISCH_THEN(MP_TAC o SPECL [`(phi:A->real^N)((gamma:real->A) t)`;
                               `\m:num. (v:real->real^N) t`]) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[lmetric2; lric2] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `gamma:real->A`; `J:real->bool`; `(U:A->bool,phi:A->real^N)`;
                   `(v:real->real^N) t`; `t:real`] GEOL_ENERGY_CHART) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[FST; SND] THEN
      USE_THEN "vv" (fun th -> MP_TAC(MATCH_MP th (CONJ (ASSUME `(t:real) IN J`)
                                                        (ASSUME `(gamma:real->A) t IN U`)))) THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SND] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) t =
                  (v:real->real^N) t`
    SUBST1_TAC THENL
     [REWRITE_TAC[mfd_vel] THEN ASM_REWRITE_TAC[SND] THEN
      MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
      USE_THEN "vv" (fun th -> MP_TAC(MATCH_MP th (CONJ (ASSUME `(t:real) IN J`)
                                                        (ASSUME `(gamma:real->A) t IN U`)))) THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[mfd_ricci; SND];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[real_differentiable] THEN
    EXISTS_TAC `drop(frechet_derivative (\y. lift((f:A->real)(chart_inv (U,phi) y)))
                   (at ((phi:A->real^N)((gamma:real->A) t))) ((v:real->real^N) t))` THEN
    USE_THEN "d1" MATCH_MP_TAC THEN REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC `\s. drop(frechet_derivative (\y. lift((f:A->real)(chart_inv (U,phi) y)))
                    (at ((phi:A->real^N)((gamma:real->A) s))) ((v:real->real^N) s))` THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_DERIVATIVE THEN
  USE_THEN "d1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;


(* The first derivative of f along a geodesic, in the preferred chart. *)

let P2BX46_GEO_F1 = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (f:A->real)
    (gamma:real->A) J t.
     p2b_shrinker (top,atlas) g f /\
     mfd_geodesic (top,atlas) g gamma J /\ t IN J
     ==> ((\s. f(gamma s)) has_real_derivative
          rfa_d1 (\y. f(chart_inv (chart_at atlas (gamma t)) y))
                 (SND(chart_at atlas (gamma t)) (gamma t)) (mfd_vel atlas gamma t))
         (atreal t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  SUBGOAL_THEN `(gamma:real->A) t IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[GEOL_GEODESIC_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `(gamma:real->A) t`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?U phi. chart_at atlas ((gamma:real->A) t) = (U:A->bool,phi:A->real^N)`
  STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[FST] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `(U:A->bool,phi:A->real^N)`] RFA_SH_CHART_DATA) THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `gamma:real->A`; `J:real->bool`; `(U:A->bool,phi:A->real^N)`]
                GEOL_GEODESIC_CHART_VEL_EXISTS) THEN
  ASM_REWRITE_TAC[FST; SND] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real->real^N` (LABEL_TAC "vv")) THEN
  MP_TAC(ISPECL [`top:A topology`; `gamma:real->A`; `J:real->bool`; `U:A->bool`; `t:real`]
                GEOL_CURVE_NEAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[GEOL_GEODESIC_BASIC]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "near"))) THEN
  SUBGOAL_THEN
   `!s. abs(s - t) < d
        ==> (f:A->real)((gamma:real->A) s) =
            f(chart_inv (U,phi) ((phi:A->real^N)(gamma s)))`
  (LABEL_TAC "loc") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "near" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `abs(s - t) < d`))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. abs(s - t) < d
        ==> ((\s. (f:A->real)((gamma:real->A) s)) has_real_derivative
             drop(frechet_derivative (\y. lift(f(chart_inv (U,phi) y)))
                    (at ((phi:A->real^N)(gamma s))) ((v:real->real^N) s))) (atreal s)`
  (LABEL_TAC "d1") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "near" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `abs(s - t) < d`))) THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    EXISTS_TAC `\r. (f:A->real)(chart_inv (U,phi) ((phi:A->real^N)((gamma:real->A) r)))` THEN
    EXISTS_TAC `d - abs(s - t)` THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `r:real` THEN DISCH_TAC THEN BETA_TAC THEN CONV_TAC SYM_CONV THEN
      USE_THEN "loc" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF; LIFT_DROP] THEN
    MP_TAC(ISPECL [`IMAGE (phi:A->real^N) U`;
                   `\y. (f:A->real)(chart_inv (U:A->bool,phi:A->real^N) y)`;
                   `\r. (phi:A->real^N)((gamma:real->A)(drop r))`; `(v:real->real^N) s`;
                   `lift s`] RFA_S2_CURVE_D1) THEN
    REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      USE_THEN "vv" (fun th -> MP_TAC(MATCH_MP th (CONJ (ASSUME `(s:real) IN J`)
                                                        (ASSUME `(gamma:real->A) s IN U`)))) THEN
      SIMP_TAC[];
      REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) t =
                (v:real->real^N) t`
  SUBST1_TAC THENL
   [REWRITE_TAC[mfd_vel] THEN ASM_REWRITE_TAC[SND] THEN
    MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
    USE_THEN "vv" (fun th -> MP_TAC(MATCH_MP th (CONJ (ASSUME `(t:real) IN J`)
                                                      (ASSUME `(gamma:real->A) t IN U`)))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[rfa_d1; SND] THEN
  USE_THEN "d1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0]);;


(* ========================================================================= *)
(* A second-order lower bound on [0,1] and Cauchy-Schwarz for the            *)
(* differential.                                                             *)
(* ========================================================================= *)

(* A second-order lower bound on [0,1]: phi'' = A - rho with rho >= 0 and   *)
(* int rho <= B gives phi(1) >= phi(0) + phi'(0) + A/2 - B.                 *)

let P2BX46_TAYLOR_LOWER = prove
 (`!(phi:real->real) phi' rho A B.
     (!t. t IN real_interval[&0,&1]
          ==> (phi has_real_derivative phi' t) (atreal t within real_interval[&0,&1])) /\
     (!t. t IN real_interval[&0,&1]
          ==> (phi' has_real_derivative (A - rho t))
              (atreal t within real_interval[&0,&1])) /\
     (!t. t IN real_interval[&0,&1] ==> &0 <= rho t) /\
     rho real_integrable_on real_interval[&0,&1] /\
     real_integral (real_interval[&0,&1]) rho <= B
     ==> phi(&0) + phi'(&0) + A / &2 - B <= phi(&1)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "d1") (CONJUNCTS_THEN2 (LABEL_TAC "d2")
    (CONJUNCTS_THEN2 (LABEL_TAC "pos") (CONJUNCTS_THEN2 (LABEL_TAC "int") (LABEL_TAC "bd"))))) THEN
  SUBGOAL_THEN `!t. t IN real_interval[&0,&1] ==> phi'(&0) + A * t - B <= phi' t`
  (LABEL_TAC "lo") THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= t /\ t <= &1` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_REAL_INTERVAL]; ALL_TAC] THEN
    SUBGOAL_THEN `real_interval[&0,t] SUBSET real_interval[&0,&1]` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`phi':real->real`; `\s. A - (rho:real->real) s`; `&0`; `t:real`]
      REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_SUBSET THEN
      EXISTS_TAC `real_interval[&0,&1]` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "d2" MATCH_MP_TAC THEN ASM SET_TAC[];
      DISCH_TAC] THEN
    SUBGOAL_THEN `(rho:real->real) real_integrable_on real_interval[&0,t]` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `real_integral (real_interval[&0,t]) rho = A * t - (phi' t - phi'(&0))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
      MP_TAC(ISPECL [`&0`; `t:real`; `A:real`] HAS_REAL_INTEGRAL_CONST) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MP_TAC(MATCH_MP HAS_REAL_INTEGRAL_SUB
        (CONJ (ASSUME `((\x. A) has_real_integral A * (t - &0)) (real_interval[&0,t])`)
              (ASSUME `((\s. A - (rho:real->real) s) has_real_integral phi' t - phi'(&0))
                       (real_interval[&0,t])`))) THEN
      REWRITE_TAC[REAL_ARITH `A - (A - r:real) = r`; REAL_SUB_RZERO; ETA_AX];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`rho:real->real`; `real_interval[&0,t]`; `real_interval[&0,&1]`]
      REAL_INTEGRAL_SUBSET_LE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `real_integral (real_interval[&0,&1]) rho <= B` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. (phi:real->real) t - ((phi'(&0) - B) * t + A * t pow 2 / &2)`;
                 `\t. (phi':real->real) t - ((phi'(&0) - B) + A * t)`; `&0`; `&1`]
    REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_POS] THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN CONJ_TAC THENL
     [USE_THEN "d1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REAL_DIFF_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_1] THEN
      REAL_ARITH_TAC];
    DISCH_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] HAS_REAL_INTEGRAL_POS)) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN BETA_TAC THEN
    USE_THEN "lo" (MP_TAC o C MATCH_MP (ASSUME `t IN real_interval[&0,&1]`)) THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* Cauchy-Schwarz for finite sums over 1..dimindex(:N) (via vectors). *)

let P2BX46_SUM_CS = prove
 (`!(a:num->real) b.
     sum(1..dimindex(:N)) (\c. a c * b c) pow 2 <=
     sum(1..dimindex(:N)) (\c. a c pow 2) * sum(1..dimindex(:N)) (\c. b c pow 2)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`(lambda c. (a:num->real) c):real^N`; `(lambda c. (b:num->real) c):real^N`]
    NORM_CAUCHY_SCHWARZ_ABS) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `sum(1..dimindex(:N)) (\c. (a:num->real) c * b c) =
                ((lambda c. a c):real^N) dot ((lambda c. b c):real^N)` SUBST1_TAC THENL
   [REWRITE_TAC[dot] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[LAMBDA_BETA];
    ALL_TAC] THEN
  SUBGOAL_THEN `!h:num->real. sum(1..dimindex(:N)) (\c. h c pow 2) =
                              norm((lambda c. h c):real^N) pow 2`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[NORM_POW_2; dot] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    SIMP_TAC[LAMBDA_BETA; REAL_POW_2];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_POW_MUL] THEN ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
  ASM_REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NORM]);;

(* A linear functional in an orthonormal frame. *)

let P2BX46_FRAME_FUNCTIONAL = prove
 (`!(G0:real^N^N) (S:real^N^N) (L:real^N->real^1) v.
     invertible G0 /\ invertible S /\ matrix_inv G0 = transp S ** S /\ linear L
     ==> L v = vsum(1..dimindex(:N))
                 (\c. ((transp S ** basis c) dot (G0 ** v)) % L(transp S ** basis c))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G0:real^N^N`; `S:real^N^N`; `v:real^N`] RFA_FRAME_VEXPAND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
  ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL]);;

let P2BX46_D1_CS = prove
 (`!U (G:real^N->real^N^N) (pf:real^N->real) y v.
     metric_field U G /\ smooth_map_on U (\z. lift(pf z)) /\ y IN U
     ==> rfa_d1 pf y v pow 2 <= lgrad2 G pf y * (v dot (G y ** v))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_METRIC_INV_FACTOR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^N^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_METRIC_INVERTIBLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `rfa_d1 (pf:real^N->real) y v =
    sum(1..dimindex(:N)) (\c. ((transp (S:real^N^N) ** basis c) dot ((G:real^N->real^N^N) y ** v)) *
                              rfa_d1 pf y (transp S ** basis c))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `pf:real^N->real`; `y:real^N`] RFA_SH_D1_LINEAR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `S:real^N^N`;
                   `\u. lift(rfa_d1 (pf:real^N->real) y u)`; `v:real^N`]
      P2BX46_FRAME_FUNCTIONAL) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o AP_TERM `drop`) THEN
    REWRITE_TAC[LIFT_DROP; DROP_VSUM; FINITE_NUMSEG; o_DEF; DROP_CMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `v dot ((G:real^N->real^N^N) y ** v) =
    sum(1..dimindex(:N)) (\c. ((transp (S:real^N^N) ** basis c) dot (G y ** v)) pow 2)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `S:real^N^N`;
                   `\u. lift(u dot ((G:real^N->real^N^N) y ** v))`; `v:real^N`]
      P2BX46_FRAME_FUNCTIONAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[linear; LIFT_ADD; LIFT_CMUL; DOT_LADD; DOT_LMUL];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `drop`) THEN
    REWRITE_TAC[LIFT_DROP; DROP_VSUM; FINITE_NUMSEG; o_DEF; DROP_CMUL; REAL_POW_2];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `pf:real^N->real`; `y:real^N`;
                 `S:real^N^N`] RFA_LGRAD2_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN REWRITE_TAC[P2BX46_SUM_CS]);;


(* ========================================================================= *)
(* MT (9.24) along a minimizing geodesic from p: f(x) >= f(p) - |grad f(p)|  *)
(* d + d^2/4 - C d, with Claim 9.47 = CMP_RICCI_INTEGRAL at r0 = 1.          *)
(* ========================================================================= *)

let P2BX46_REAL_DIFF_DERIV = prove
 (`!f t. f real_differentiable atreal t
         ==> (f has_real_derivative real_derivative f t) (atreal t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_differentiable] THEN
  DISCH_THEN(X_CHOOSE_TAC `f':real`) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP HAS_REAL_DERIVATIVE_DERIVATIVE) THEN
  ASM_REWRITE_TAC[]);;

(* From a^2 <= Q d^2 with Q, d >= 0: -sqrt Q d <= a. *)

let P2BX46_SQ_LOWER = prove
 (`!a Q d. &0 <= Q /\ &0 <= d /\ a pow 2 <= Q * d pow 2 ==> --(sqrt Q * d) <= a`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `--a <= sqrt Q * d` MP_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `sqrt Q * d = sqrt(Q * d pow 2)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[SQRT_MUL; REAL_LE_POW_2; POW_2_SQRT]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[REAL_POW_NEG; ARITH]);;

let P2BX46_F_GEO_LOWER = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f K p x.
     hausdorff_space top /\ connected_space top /\ p2b_shrinker (top,atlas) g f /\
     mfd_complete (top,atlas) g /\ p IN topspace top /\ x IN topspace top /\
     (!y w. y IN topspace top ==> &0 <= mfd_ricci atlas g y w w) /\
     (!y w. y IN topspace top
            ==> mfd_ricci atlas g y w w <= &(dimindex(:N) - 1) * K * (w dot (g y ** w))) /\
     &2 <= mfd_dist (top,atlas) g p x
     ==> f p -
         sqrt(lgrad2 (metric_local atlas (chart_at atlas p) g)
                     (\y. f(chart_inv (chart_at atlas p) y)) (SND(chart_at atlas p) p)) *
         mfd_dist (top,atlas) g p x +
         mfd_dist (top,atlas) g p x pow 2 / &4 -
         mfd_dist (top,atlas) g p x *
         (&2 * &(dimindex(:N) - 1) * (&2 / &3 * K + &1)) <= f x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `p:A`; `x:A`] MFD_COMPLETE_MINIMIZING_GEODESIC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `d = mfd_dist (top,atlas) (g:A->real^N^N) p x` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `p:A`; `v:real^N`] CMPS_RAY_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_UNIV]; ALL_TAC] THEN
  ABBREV_TAC `gam = mfd_geo (top,atlas) (g:A->real^N^N) p v` THEN
  ABBREV_TAC `J = mfd_geo_maxint (top,atlas) (g:A->real^N^N) p v` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "exp") (LABEL_TAC "speed")))))) THEN
  SUBGOAL_THEN `(gam:real->A) (&1) = x` ASSUME_TAC THENL
   [USE_THEN "exp" (MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_POS; REAL_LE_REFL] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LID] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN J ==> (gam:real->A) s IN topspace top` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                          `J:real->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= d` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s IN J
        ==> &0 <= mfd_vel atlas (gam:real->A) s dot ((g:A->real^N^N)(gam s) ** mfd_vel atlas gam s)`
  (LABEL_TAC "nn") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    ASM_CASES_TAC `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gam:real->A) s = vec 0` THEN
    ASM_REWRITE_TAC[DOT_LZERO; REAL_LE_REFL] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `(gam:real->A) s`] RIEMANNIAN_METRIC_POS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) p v = d` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s IN J
        ==> mfd_vel atlas (gam:real->A) s dot ((g:A->real^N^N)(gam s) ** mfd_vel atlas gam s) =
            d pow 2`
  (LABEL_TAC "sp2") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "speed" (MP_TAC o C MATCH_MP (ASSUME `(s:real) IN J`)) THEN
    ASM_REWRITE_TAC[mfd_tnorm] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SQRT_POW_2 THEN
    USE_THEN "nn" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN real_interval[&0,&1] ==> s IN J` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `p:A`; `v:real^N`; `K:real`; `&1`]
    (REWRITE_RULE[CMP_RICCI_INTEGRAL_STATEMENT]
      (ISPECL [`(:A)`; `(:N)`] CMP_RICCI_INTEGRAL))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_UNIV; REAL_LT_01] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IN_UNION; mfd_ball; IN_ELIM_THM] THEN
      ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]];
    ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`\t. (f:A->real)((gam:real->A) t)`;
                 `real_derivative (\s. (f:A->real)((gam:real->A) s))`;
                 `\t. mfd_ricci atlas (g:A->real^N^N) ((gam:real->A) t)
                        (mfd_vel atlas gam t) (mfd_vel atlas gam t)`;
                 `d pow 2 / &2`;
                 `d * (&2 * &(dimindex(:N) - 1) * (&2 / &3 * K + &1))`] P2BX46_TAYLOR_LOWER) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MATCH_MP_TAC P2BX46_REAL_DIFF_DERIV THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                     `f:A->real`; `gam:real->A`; `J:real->bool`; `t:real`] P2BX46_GEO_F2) THEN
      ASM_SIMP_TAC[];
      X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                     `f:A->real`; `gam:real->A`; `J:real->bool`; `t:real`] P2BX46_GEO_F2) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT2)] THEN
      USE_THEN "sp2" (fun th -> ASM_SIMP_TAC[th]) THEN
      REWRITE_TAC[REAL_ARITH `inv(&2) * x = x / &2`];
      X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> try fst(dest_var(fst(dest_forall(concl th)))) = "y" with Failure _ -> false)) THEN
      ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `mfd_tnorm (g:A->real^N^N) p v * &2 * &(dimindex(:N) - 1) *
                  (&2 / &3 * K * &1 + inv(&1))` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_MUL_RID; REAL_INV_1] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 IN (J:real->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `gam:real->A`; `J:real->bool`; `&0`] P2BX46_GEO_F1) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP HAS_REAL_DERIVATIVE_DERIVATIVE) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `p:A`] CMPF_LOCAL_METRIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A)`]
    RFA_SH_CHART_DATA) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[CHART_AT]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A)))
                         (FST(chart_at atlas p))`;
                 `metric_local atlas (chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A))
                    (g:A->real^N^N)`;
                 `\y. (f:A->real)(chart_inv (chart_at (atlas:((A->bool)#(A->real^N))->bool) p) y)`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A)) p`; `v:real^N`]
    P2BX46_D1_CS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `v dot ((g:A->real^N^N) p ** v) = d pow 2` SUBST1_TAC THENL
   [UNDISCH_TAC `mfd_tnorm (g:A->real^N^N) p v = d` THEN REWRITE_TAC[mfd_tnorm] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SQRT_POW_2 THEN
    ASM_CASES_TAC `v:real^N = vec 0` THEN ASM_REWRITE_TAC[DOT_LZERO; REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `p:A`] RIEMANNIAN_METRIC_POS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`rfa_d1 (\y. (f:A->real)(chart_inv (chart_at (atlas:((A->bool)#(A->real^N))->bool) p) y))
                   (SND(chart_at atlas (p:A)) p) v`;
                 `lgrad2 (metric_local atlas (chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A))
                            (g:A->real^N^N))
                         (\y. (f:A->real)(chart_inv (chart_at atlas p) y))
                         (SND(chart_at atlas p) p)`; `d:real`] P2BX46_SQ_LOWER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LGRAD2_POS THEN
    EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A)))
                      (FST(chart_at atlas p))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REAL_ARITH_TAC);;


(* ========================================================================= *)
(* The potential f is bounded below, grows quadratically and is proper.      *)
(* ========================================================================= *)

(* The preferred-chart |grad f|^2 and its nonnegativity. *)

let P2BX46_GRAD2_POS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top
     ==> &0 <= lgrad2 (metric_local atlas (chart_at atlas x) g)
                      (\y. f(chart_inv (chart_at atlas x) y)) (SND(chart_at atlas x) x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`] CMPF_LOCAL_METRIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MATCH_MP_TAC LGRAD2_POS THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                    (FST(chart_at atlas x))` THEN
  ASM_REWRITE_TAC[]);;

(* Hamilton's identity with R >= 0: f is bounded below and |grad f|^2 <= f + C. *)

let P2BX46_HAMILTON_BOUNDS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f.
     connected_space top /\ p2b_shrinker (top,atlas) g f /\
     (!x. x IN topspace top ==> &0 <= mfd_scalar atlas g x)
     ==> ?C. !x. x IN topspace top
                 ==> --C <= f x /\
                     lgrad2 (metric_local atlas (chart_at atlas x) g)
                            (\y. f(chart_inv (chart_at atlas x) y))
                            (SND(chart_at atlas x) x) <= f x + C`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`] P2BX46_MFD_HAMILTON_GEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `C:real` ASSUME_TAC) THEN
  EXISTS_TAC `C:real` THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `x:A`] P2BX46_GRAD2_POS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[p2b_shrinker]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* MT (9.24) globally: f >= d(p,x)^2/4 - C1 d(p,x) - C0. *)

let P2BX46_F_LOWER_GLOBAL = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f K p.
     hausdorff_space top /\ connected_space top /\ p2b_shrinker (top,atlas) g f /\
     mfd_complete (top,atlas) g /\ p IN topspace top /\ &0 <= K /\
     (!x. x IN topspace top ==> &0 <= mfd_scalar atlas g x) /\
     (!y w. y IN topspace top ==> &0 <= mfd_ricci atlas g y w w) /\
     (!y w. y IN topspace top
            ==> mfd_ricci atlas g y w w <= &(dimindex(:N) - 1) * K * (w dot (g y ** w)))
     ==> ?C1 C0. &0 <= C1 /\
                 !x. x IN topspace top
                     ==> mfd_dist (top,atlas) g p x pow 2 / &4 -
                         C1 * mfd_dist (top,atlas) g p x - C0 <= f x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`] P2BX46_HAMILTON_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `C:real` (LABEL_TAC "hb")) THEN
  ABBREV_TAC
   `Q = lgrad2 (metric_local atlas (chart_at atlas p) (g:A->real^N^N))
               (\y. (f:A->real)(chart_inv (chart_at atlas p) y)) (SND(chart_at atlas p) p)` THEN
  SUBGOAL_THEN `&0 <= Q` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN MATCH_MP_TAC P2BX46_GRAD2_POS THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &2 * &(dimindex(:N) - 1) * (&2 / &3 * K + &1)` ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`sqrt Q + &2 * &(dimindex(:N) - 1) * (&2 / &3 * K + &1)`;
    `max (&1 + C) (--((f:A->real) p))`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN ASM_SIMP_TAC[SQRT_POS_LE]; ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= mfd_dist (top,atlas) (g:A->real^N^N) p x` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `d = mfd_dist (top,atlas) (g:A->real^N^N) p x` THEN
  ABBREV_TAC `B0 = &2 * &(dimindex(:N) - 1) * (&2 / &3 * K + &1)` THEN
  ASM_CASES_TAC `&2 <= d` THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `f:A->real`; `K:real`; `p:A`; `x:A`] P2BX46_F_GEO_LOWER) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "hb" (MP_TAC o C MATCH_MP (ASSUME `(x:A) IN topspace top`)) THEN
  SUBGOAL_THEN `d pow 2 <= &4` MP_TAC THENL
   [SUBST1_TAC(REAL_ARITH `&4 = &2 pow 2`) THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (sqrt Q + B0) * d` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_SIMP_TAC[SQRT_POS_LE];
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* Sublevel sets of f are compact. *)

let P2BX46_F_PROPER = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) f K.
     hausdorff_space top /\ connected_space top /\ p2b_shrinker (top,atlas) g f /\
     mfd_complete (top,atlas) g /\ &0 <= K /\
     (!x. x IN topspace top ==> &0 <= mfd_scalar atlas g x) /\
     (!y w. y IN topspace top ==> &0 <= mfd_ricci atlas g y w w) /\
     (!y w. y IN topspace top
            ==> mfd_ricci atlas g y w w <= &(dimindex(:N) - 1) * K * (w dot (g y ** w)))
     ==> !c. compact_in top {x | x IN topspace top /\ f x <= c}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  ASM_CASES_TAC `topspace top:A->bool = {}` THENL
   [ASM_REWRITE_TAC[NOT_IN_EMPTY; EMPTY_GSPEC; COMPACT_IN_EMPTY]; ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `p:A` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `K:real`; `p:A`] P2BX46_F_LOWER_GLOBAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real` (X_CHOOSE_THEN `C0:real` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `R = &8 * C1 + sqrt(&8 * abs(C0 + c)) + &1` THEN
  MATCH_MP_TAC CLOSED_COMPACT_IN THEN
  EXISTS_TAC `mfd_cball (top,atlas) (g:A->real^N^N) p R` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC GEOH_CBALL_COMPACT THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `p:A`] MFD_HOPF_RINOW_POINT) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    REWRITE_TAC[SUBSET; IN_ELIM_THM; mfd_cball] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= mfd_dist (top,atlas) (g:A->real^N^N) p x` ASSUME_TAC THENL
     [MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ABBREV_TAC `d = mfd_dist (top,atlas) (g:A->real^N^N) p x` THEN
    MATCH_MP_TAC(REAL_ARITH `~(R < d) ==> d <= R`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `C1 * d <= d pow 2 / &8` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_POW_2; REAL_ARITH `(d * d) / &8 = (d / &8) * d`] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `&8 * abs(C0 + c)` SQRT_POS_LE) THEN
      REWRITE_TAC[REAL_LE_MUL_EQ; REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&8 * abs(C0 + c) < d pow 2` ASSUME_TAC THENL
     [SUBGOAL_THEN `&8 * abs(C0 + c) = sqrt(&8 * abs(C0 + c)) pow 2` SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SQRT_POW_2 THEN
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_MUL THEN
        REWRITE_TAC[REAL_ABS_POS] THEN REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:A. (f:A->real) x`; `top:A topology`; `euclideanreal`;
                 `{r:real | r <= c}`] CLOSED_IN_CONTINUOUS_MAP_PREIMAGE) THEN
  REWRITE_TAC[GSYM REAL_CLOSED_IN; REAL_CLOSED_HALFSPACE_LE; IN_ELIM_THM; ETA_AX] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `\x:A. lift((f:A->real) x)`] GRGE_MFD_SMOOTH_CONTINUOUS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `\x:A. lift((f:A->real) x)`] MFD_SMOOTH_ON_TOPSPACE) THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[CONTINUOUS_MAP_EQ_DROP; o_DEF; LIFT_DROP; ETA_AX]]);;

