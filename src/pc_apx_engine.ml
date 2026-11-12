(* ========================================================================= *)
(* pc_apx_engine: the engine of the Appendix (MT Lemma A.13 with A.16), T1  *)
(* of pc_apx_defs: the union of a finite chain of eps-necks is              *)
(* an eps-tube with a product chart that is exactly the first neck near its *)
(* start and (radially) the last neck near its end.  Proved as an           *)
(* implication from M6b (SMT_PRODUCT2_STATEMENT), using the neck layer      *)
(* (pc_apx_neck, N0-N8).  The statement is the corrected A13 (hypothesis    *)
(* apx_sphere_sep, exact-end regions of length 1/(8 eps)).                  *)
(* ========================================================================= *)

needs "src/pc_apx_neck.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The transition between two overlapping necks in model                    *)
(* coordinates.  For tau = ei o e' (ei the inverse of e), the s-coordinate   *)
(* of e along tau has, at every point of the overlap, differential within   *)
(* 7 sqrt(alpha1) |.|_G0 of +/- sqrt(R/R') ds (from the pair estimate of N3).*)
(* ------------------------------------------------------------------------- *)

let APX_DUAL_CS = prove
 (`!(G:real^N^N) (M:real^N^N) c W.
        G = transp M ** M /\ invertible M
        ==> (c dot W) pow 2 <= (c dot (matrix_inv G ** c)) * (W dot (G ** W))`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ABBREV_TAC `Mi = matrix_inv(M:real^N^N)` THEN
  SUBGOAL_THEN `(M:real^N^N) ** Mi = mat 1 /\ Mi ** M = mat 1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Mi" THEN ASM_SIMP_TAC[MATRIX_INV]; ALL_TAC] THEN
  SUBGOAL_THEN `matrix_inv(transp M ** M:real^N^N) = (Mi:real^N^N) ** transp Mi`
  SUBST1_TAC THENL
   [EXPAND_TAC "Mi" THEN
    ASM_SIMP_TAC[MATRIX_INV_MUL; INVERTIBLE_TRANSP; MATRIX_INV_TRANSP];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^N) dot W = (transp(Mi:real^N^N) ** c) dot ((M:real^N^N) ** W)`
  SUBST1_TAC THENL
   [REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL; MATRIX_VECTOR_MUL_ASSOC] THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^N) dot (((Mi:real^N^N) ** transp Mi) ** c) =
                (transp Mi ** c) dot (transp Mi ** c) /\
                (W:real^N) dot ((transp M ** M) ** W) = ((M:real^N^N) ** W) dot (M ** W)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL; MATRIX_VECTOR_MUL_ASSOC];
      REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM NORM_POW_2; GSYM REAL_POW_MUL] THEN
  REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS; REAL_ABS_MUL; REAL_ABS_NORM] THEN
  REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS]);;

let APX_TRANSITION_DERIV_ARITH = prove
 (`!A B Q G R R' sg alpha1 eps.
        &0 < R /\ &0 < R' /\ &0 <= Q /\ &0 <= G /\ &0 <= alpha1 /\ &0 <= eps /\
        eps <= &1 / &32 /\ R / R' <= &9 / &8 /\
        (A / sqrt R - sg * B / sqrt R') pow 2 <= (&32 * alpha1) * Q /\
        R' * Q <= (&1 + eps) * G
        ==> abs(A - sg * sqrt(R / R') * B) <= &7 * sqrt alpha1 * sqrt G`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt R /\ &0 < sqrt R'` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(R / R') = sqrt R / sqrt R'` SUBST1_TAC THENL
   [ASM_SIMP_TAC[SQRT_DIV; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `A - sg * sqrt R / sqrt R' * B = sqrt R * (A / sqrt R - sg * B / sqrt R')`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < sqrt R` THEN UNDISCH_TAC `&0 < sqrt R'` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&7 * sqrt alpha1 * sqrt G = sqrt(&49 * alpha1 * G)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[SQRT_MUL; REAL_LE_MUL; REAL_POS] THEN
    SUBGOAL_THEN `sqrt(&49) = &7` SUBST1_TAC THENL
     [MATCH_MP_TAC SQRT_UNIQUE THEN CONV_TAC REAL_RAT_REDUCE_CONV; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RSQRT THEN REWRITE_TAC[REAL_POW2_ABS; REAL_POW_MUL] THEN
  ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `R * ((&32 * alpha1) * Q)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `R * Q <= R / R' * ((&1 + eps) * G)` ASSUME_TAC THENL
   [SUBGOAL_THEN `R * Q = R / R' * (R' * Q)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < R'` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `R / R' * ((&1 + eps) * G) <= &9 / &8 * ((&33 / &32) * G)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&32 * alpha1) * (R * Q) <= (&32 * alpha1) * (&9 / &8 * ((&33 / &32) * G))`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= alpha1 * G` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* E2.1, the derivative of the transition map between two                    *)
(* overlapping eps-necks.  In the coordinates v of N' (centre x'), the       *)
(* model differential of s at tau v = ei(e' v) composed with d tau agrees     *)
(* with sg sqrt(R/R') ds_v up to 7 sqrt(alpha1) |k|_G0 (R = R(x), R' = R(x')):  *)
(* the pair estimate APX_NECK_PAIR_ESTIMATE of pc_apx_neck, the rank-one     *)
(* comparison in a frame, the dual Cauchy-Schwarz bound (above) and the C^0  *)
(* bound for N'.                                                             *)
(* ------------------------------------------------------------------------- *)

let APX_TRANSITION_DERIV = prove
 (`!alpha1 eps1.
     &0 < alpha1 /\ alpha1 <= &1 / &32 /\ &0 < eps1 /\ eps1 <= alpha1 /\
     (!top atlas (g:A->real^3^3) eps x (e:real^3->A) y.
        &0 < eps /\ eps <= eps1 /\ riemannian_metric atlas g /\
        rfs_neck (top,atlas) g eps x e /\ y IN rfs_neck_dom eps
        ==> abs(lscalar (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y - &1)
            <= alpha1 /\
            (!w. abs(lricci (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y w w -
                     lricci (cylinder_flow (&0)) y w w)
                 <= alpha1 * (w dot (cylinder_flow (&0) y ** w))))
     ==> !top atlas (g:A->real^3^3) eps x (e:real^3->A) x' e' (ei:A->real^3) v.
           &0 < eps /\ eps <= eps1 /\ riemannian_metric atlas g /\
           rfs_neck (top,atlas) g eps x e /\ rfs_neck (top,atlas) g eps x' e' /\
           (!z. z IN rfs_neck_dom eps ==> ei(e z) = z) /\
           v IN rfs_neck_dom eps /\ e' v IN IMAGE e (rfs_neck_dom eps)
           ==> abs(mfd_scalar atlas g x / mfd_scalar atlas g x' - &1) <= &4 * alpha1 /\
               ?sg. (sg = &1 \/ sg = -- &1) /\
                    !k. abs(sqrt(&2) * (ei(e' v) dot frechet_derivative (ei o e') (at v) k) /
                            (ei(e' v) dot ei(e' v)) -
                            sg * sqrt(mfd_scalar atlas g x / mfd_scalar atlas g x') *
                            sqrt(&2) * (v dot k) / (v dot v))
                        <= &7 * sqrt alpha1 * sqrt(k dot (cylinder_flow (&0) v ** k))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`alpha1:real`; `eps1:real`] APX_NECK_PAIR_ESTIMATE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "pair") THEN
  MP_TAC(SPECL [`alpha1:real`; `eps1:real`] APX_NECK_OVERLAP_GEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "ovl") THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
                mfd_param top atlas (rfs_neck_dom eps) (e:real^3->A) /\
                mfd_param top atlas (rfs_neck_dom eps) (e':real^3->A) /\
                &0 < mfd_scalar atlas (g:A->real^3^3) x /\
                &0 < mfd_scalar atlas (g:A->real^3^3) x'`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `rfs_neck_dom eps`; `e:real^3->A`; `e':real^3->A`;
                 `ei:A->real^3`] APX_PARAM_TRANSITION) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `v:real^3` o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `y = (ei:A->real^3)((e':real^3->A) v)` THEN
  USE_THEN "ovl" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `eps:real`; `x':A`; `e':real^3->A`; `x:A`; `e:real^3->A`;
    `(e':real^3->A) v`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_INTER] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  USE_THEN "pair" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `x':A`; `e':real^3->A`;
    `y:real^3`; `v:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `(e:real^3->A) y = e' (v:real^3)`] THEN
  DISCH_THEN(X_CHOOSE_THEN `L1:real^3->real^1` (X_CHOOSE_THEN `L2:real^3->real^1`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) ((e':real^3->A) v)` THEN
  ABBREV_TAC `D1 = frechet_derivative (SND (c:(A->bool)#(A->real^3)) o (e:real^3->A)) (at y)` THEN
  ABBREV_TAC `D2 = frechet_derivative (SND (c:(A->bool)#(A->real^3)) o (e':real^3->A)) (at v)` THEN
  ABBREV_TAC `Dt = frechet_derivative ((ei:A->real^3) o (e':real^3->A)) (at v)` THEN
  ABBREV_TAC `Gc = metric_local atlas (c:(A->bool)#(A->real^3)) (g:A->real^3^3)
                     (SND c ((e':real^3->A) v))` THEN
  ABBREV_TAC `R = mfd_scalar atlas (g:A->real^3^3) x` THEN
  ABBREV_TAC `R' = mfd_scalar atlas (g:A->real^3^3) x'` THEN
  SUBGOAL_THEN `(e':real^3->A) v IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `rfs_neck_dom eps`; `e':real^3->A`] GRGD_PARAM_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `IMAGE (e':real^3->A) (rfs_neck_dom eps) SUBSET topspace top` THEN
    UNDISCH_TAC `(v:real^3) IN rfs_neck_dom eps` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(e':real^3->A) v`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?M:real^3^3. invertible M /\ Gc = transp M ** M` MP_TAC THENL
   [EXPAND_TAC "Gc" THEN MATCH_MP_TAC LRG_FRAME THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` THEN CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas (g:A->real^3^3)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `M:real^3^3` (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)))] THEN
  ABBREV_TAC `a = inv(sqrt R) % ((lambda i. drop((L1:real^3->real^1)(basis i))):real^3)` THEN
  ABBREV_TAC `b = inv(sqrt R') % ((lambda i. drop((L2:real^3->real^1)(basis i))):real^3)` THEN
  SUBGOAL_THEN `!W:real^3. (a:real^3) dot W = drop((L1:real^3->real^1) W) / sqrt R /\
                           (b:real^3) dot W = drop((L2:real^3->real^1) W) / sqrt R'`
  ASSUME_TAC THENL
   [GEN_TAC THEN MAP_EVERY EXPAND_TAC ["a"; "b"] THEN REWRITE_TAC[DOT_LMUL] THEN
    ASM_SIMP_TAC[GSYM APX_LINEAR_FUNCTIONAL_DOT] THEN
    CONJ_TAC THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!W:real^3. abs((a dot W) pow 2 - (b dot W) pow 2) <=
                           (&16 * alpha1) * (W dot ((Gc:real^3^3) ** W))`
  ASSUME_TAC THENL
   [X_GEN_TAC `W:real^3` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `W:real^3` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> t = `L2:real^3->real^1`)) (concl th) &&
      can (find_term (fun t -> t = `alpha1:real`)) (concl th))) THEN
    MATCH_MP_TAC(REAL_ARITH `a = b ==> a <= c ==> b <= c`) THEN AP_TERM_TAC THEN
    ASM_REWRITE_TAC[REAL_POW_DIV] THEN ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Gc:real^3^3`; `M:real^3^3`; `a:real^3`; `b:real^3`; `&16 * alpha1`]
                APX_RANK_ONE_METRIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `sg:real` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  EXISTS_TAC `sg:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:real^3` THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                `g:A->real^3^3`; `eps:real`; `x':A`; `e':real^3->A`; `v:real^3`]
               APX_NECK_CHART_DATA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `O2:real^3->bool` (X_CHOOSE_THEN `k2:real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                `g:A->real^3^3`; `eps:real`; `x':A`; `e':real^3->A`; `v:real^3`; `k:real^3`]
               APX_NECK_C0_BOUNDS) THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN STRIP_TAC THEN
  ABBREV_TAC `Q = (D2:real^3->real^3) k dot ((Gc:real^3^3) ** D2 k)` THEN
  ABBREV_TAC `G = (k:real^3) dot (cylinder_flow (&0) v ** k)` THEN
  SUBGOAL_THEN `&0 <= G` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN REWRITE_TAC[APX_CYL0_QUAD] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[DOT_POS_LE] THEN MATCH_MP_TAC REAL_LE_DIV THEN
    REWRITE_TAC[REAL_POS; REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Q` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= R' * Q` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 - eps) * G` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_MUL_EQ]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(a - sg % b:real^3) dot (D2:real^3->real^3) k =
    (sqrt(&2) * (y dot (Dt:real^3->real^3) k) / (y dot y)) / sqrt R -
    sg * (sqrt(&2) * (v dot k) / (v dot v)) / sqrt R'`
  ASSUME_TAC THENL
   [REWRITE_TAC[DOT_LSUB; DOT_LMUL] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM(ASSUME `!k. (D1:real^3->real^3) ((Dt:real^3->real^3) k) = D2 k`)] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Gc:real^3^3`; `M:real^3^3`; `a - sg % b:real^3`; `(D2:real^3->real^3) k`]
                APX_DUAL_CS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`sqrt(&2) * (y dot (Dt:real^3->real^3) k) / (y dot y)`;
                 `sqrt(&2) * ((v:real^3) dot k) / (v dot v)`;
                 `Q:real`; `G:real`; `R:real`; `R':real`; `sg:real`; `alpha1:real`;
                 `eps:real`] APX_TRANSITION_DERIV_ARITH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `((a - sg % b:real^3) dot (matrix_inv Gc ** (a - sg % b))) * Q` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* One-dimensional analysis along the radial lines of a neck.                *)
(* A real function whose derivative is within kappa of +rho or -rho          *)
(* (kappa < rho) is strictly monotone on intervals; increasing functions     *)
(* have derivative near +rho; with an end value c the distance to the end    *)
(* controls c - f.                                                           *)
(* ------------------------------------------------------------------------- *)

let APX_1D_CONT = prove
 (`!f f' s.
        (!t. t IN s ==> (f has_real_derivative f' t) (atreal t))
        ==> f real_continuous_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
  EXISTS_TAC `(f':real->real) x` THEN ASM_SIMP_TAC[]);;

let APX_1D_MONO = prove
 (`!f f' a b rho kappa.
        a < b /\ kappa < rho /\
        (!t. a < t /\ t < b
             ==> (f has_real_derivative f' t) (atreal t) /\
                 (abs(f' t - rho) <= kappa \/ abs(f' t + rho) <= kappa))
        ==> (!x y. a < x /\ x < y /\ y < b ==> f x < f y) \/
            (!x y. a < x /\ x < y /\ y < b ==> f y < f x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `real_interval(a,b)`]
                REAL_CONTINUOUS_INJECTIVE_IFF_MONOTONIC) THEN
  REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN ANTS_TAC THENL
   [MATCH_MP_TAC APX_1D_CONT THEN EXISTS_TAC `f':real->real` THEN
    ASM_SIMP_TAC[IN_REAL_INTERVAL];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
  SUBGOAL_THEN `!x y. a < x /\ x < y /\ y < b ==> ~((f:real->real) x = f y)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real->real`; `f':real->real`; `x:real`; `y:real`] REAL_ROLLE) THEN
    ASM_REWRITE_TAC[NOT_IMP; IN_REAL_INTERVAL] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC APX_1D_CONT THEN EXISTS_TAC `f':real->real` THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `z:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `z:real` o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun t -> t = `kappa:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`x:real`; `y:real`] REAL_LT_TOTAL) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`x:real`; `y:real`]) THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPECL [`y:real`; `x:real`]) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_OR THEN CONJ_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let APX_1D_INCR_DERIV = prove
 (`!f f' a b rho kappa.
        a < b /\ kappa < rho /\
        (!t. a < t /\ t < b
             ==> (f has_real_derivative f' t) (atreal t) /\
                 (abs(f' t - rho) <= kappa \/ abs(f' t + rho) <= kappa)) /\
        (!x y. a < x /\ x < y /\ y < b ==> f x < f y)
        ==> !t. a < t /\ t < b ==> abs(f' t - rho) <= kappa`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `f':real->real`; `real_interval(a,b)`]
                HAS_REAL_DERIVATIVE_INCREASING) THEN
  REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_REAL_INTERVAL; IN_SING; NOT_EXISTS_THM] THEN
      X_GEN_TAC `z:real` THEN DISCH_THEN(fun th ->
        MP_TAC(SPEC `(a + b) / &2` th) THEN MP_TAC(SPEC `(&3 * a + b) / &4` th)) THEN
      ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o snd o EQ_IMP_RULE) THEN ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `x:real = y` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
    is_forall(concl th) && can (find_term (fun u -> u = `kappa:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC);;

let APX_1D_MVT_BOUNDS = prove
 (`!f f' a b rho kappa t t'.
        (!s. a < s /\ s < b
             ==> (f has_real_derivative f' s) (atreal s) /\ abs(f' s - rho) <= kappa) /\
        a < t /\ t < t' /\ t' < b
        ==> (rho - kappa) * (t' - t) <= f t' - f t /\
            f t' - f t <= (rho + kappa) * (t' - t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `f':real->real`; `t:real`; `t':real`] REAL_MVT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC APX_1D_CONT THEN EXISTS_TAC `f':real->real` THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC SUBST1_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real`) THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN `&0 < t' - t` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`t' - t:real`,`h:real`) THEN SPEC_TAC(`(f':real->real) z`,`q:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN CONJ_TAC THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC);;

let APX_1D_ENDBOUND = prove
 (`!f f' a tau c rho kappa.
        a < tau /\ &0 <= kappa /\ kappa < rho /\
        (!t. a < t /\ t < tau
             ==> (f has_real_derivative f' t) (atreal t) /\ abs(f' t - rho) <= kappa) /\
        (!t. a < t /\ t < tau ==> f t < c) /\
        (!m. m < c ==> ?d. &0 < d /\ !t. a < t /\ t < tau /\ tau - d < t ==> m < f t)
        ==> !t. a < t /\ t < tau
                ==> (rho - kappa) * (tau - t) <= c - f t /\
                    c - f t <= (rho + kappa) * (tau - t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t'. t < t' /\ t' < tau
         ==> (rho - kappa) * (t' - t) <= f t' - f t /\
             f t' - f t <= (rho + kappa) * (t' - t)`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC APX_1D_MVT_BOUNDS THEN
    MAP_EVERY EXISTS_TAC [`f':real->real`; `a:real`; `tau:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real->real) t < c` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `~(c - f < r) ==> r <= c - f`) THEN DISCH_TAC THEN
    ABBREV_TAC `t' = (tau + t + (c - (f:real->real) t) / (rho - kappa)) / &2` THEN
    SUBGOAL_THEN `&0 < rho - kappa` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (c - (f:real->real) t) / (rho - kappa) /\
                  (c - (f:real->real) t) / (rho - kappa) < tau - t`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_DIV; REAL_SUB_LT; REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t':real` o check (fun th ->
      is_forall(concl th) && can (find_term (fun u -> u = `rho + kappa`)) (concl th))) THEN
    ANTS_TAC THENL [EXPAND_TAC "t'" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    SUBGOAL_THEN `(f:real->real) t' < c` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN EXPAND_TAC "t'" THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `c - (f:real->real) t <= (rho - kappa) * (t' - t)` MP_TAC THENL
     [EXPAND_TAC "t'" THEN
      SUBGOAL_THEN `(rho - kappa) * ((tau + t + (c - (f:real->real) t) / (rho - kappa)) / &2
                                     - t) =
                    ((rho - kappa) * (tau - t) + (c - f t)) / &2`
      SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < rho - kappa` THEN CONV_TAC REAL_FIELD; ASM_REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    MATCH_MP_TAC(REAL_ARITH `~((rho + kappa) * (tau - t) < c - f) ==> c - f <= (rho + kappa) * (tau - t)`) THEN
    DISCH_TAC THEN
    ABBREV_TAC `e0 = c - (f:real->real) t - (rho + kappa) * (tau - t)` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c - e0 / &2` o check (fun th ->
      is_forall(concl th) && can (find_term (fun u -> u = `d:real`)) (concl th))) THEN
    ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `t' = (max t (tau - d) + tau) / &2` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t':real`) THEN
    ANTS_TAC THENL [EXPAND_TAC "t'" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t':real` o check (fun th ->
      is_forall(concl th) && can (find_term (fun u -> u = `rho + kappa`)) (concl th))) THEN
    ANTS_TAC THENL [EXPAND_TAC "t'" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    SUBGOAL_THEN `(rho + kappa) * (t' - t) <= (rho + kappa) * (tau - t)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN EXPAND_TAC "t'" THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC]]);;

(* An increasing function cannot exit (|f| -> c) at the left end of an       *)
(* interval, a decreasing one not at the right end, when f >= -c/2 and       *)
(* f < c.                                                                    *)

let APX_1D_BAD_LEFT = prove
 (`!f S p q c t0.
        p < t0 /\ t0 < q /\ &0 < c /\
        (!t. p < t /\ t < q ==> t IN S) /\
        (!t. t IN S ==> --(c / &2) <= f t /\ f t < c) /\
        (!x y. p < x /\ x < y /\ y < q ==> f x < f y) /\
        (!m. m < c ==> ?d. &0 < d /\ !t'. t' IN S /\ abs(t' - p) < d ==> m < abs(f t'))
        ==> F`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(f:real->real) t0 < c /\ --(c / &2) <= f t0` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `max (c / &2) ((f:real->real) t0)`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p + min d (t0 - p) / &2`) THEN
  SUBGOAL_THEN `p < p + min d (t0 - p) / &2 /\ p + min d (t0 - p) / &2 < t0`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(p + min d (t0 - p) / &2) IN S` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real->real)(p + min d (t0 - p) / &2) < f t0` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--(c / &2) <= (f:real->real)(p + min d (t0 - p) / &2)` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let APX_1D_BAD_RIGHT = prove
 (`!f S p q c t0.
        p < t0 /\ t0 < q /\ &0 < c /\
        (!t. p < t /\ t < q ==> t IN S) /\
        (!t. t IN S ==> --(c / &2) <= f t /\ f t < c) /\
        (!x y. p < x /\ x < y /\ y < q ==> f y < f x) /\
        (!m. m < c ==> ?d. &0 < d /\ !t'. t' IN S /\ abs(t' - q) < d ==> m < abs(f t'))
        ==> F`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(f:real->real) t0 < c /\ --(c / &2) <= f t0` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `max (c / &2) ((f:real->real) t0)`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `q - min d (q - t0) / &2`) THEN
  SUBGOAL_THEN `t0 < q - min d (q - t0) / &2 /\ q - min d (q - t0) / &2 < q`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(q - min d (q - t0) / &2) IN S` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real->real)(q - min d (q - t0) / &2) < f t0` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--(c / &2) <= (f:real->real)(q - min d (q - t0) / &2)` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* The component structure: every point of S is joined to the left end a.   *)

let APX_RAY_1D_DOWN = prove
 (`!f f' S a b b' c rho kappa.
        a < b' /\ b' < b /\ kappa < rho /\ &0 < c /\
        (!t. t IN S ==> a < t /\ t <= b') /\
        (!t. t IN S ==> ?d. &0 < d /\ !t'. abs(t' - t) < d ==> t' IN S) /\
        (!t. t IN S ==> (f has_real_derivative f' t) (atreal t) /\
                        (abs(f' t - rho) <= kappa \/ abs(f' t + rho) <= kappa)) /\
        (!t. t IN S ==> --(c / &2) <= f t /\ f t < c) /\
        (!t m. a < t /\ t < b /\ ~(t IN S) /\ m < c
               ==> ?d. &0 < d /\ !t'. t' IN S /\ abs(t' - t) < d ==> m < abs(f t'))
        ==> !t0 t1. t0 IN S /\ a < t1 /\ t1 <= t0 ==> t1 IN S`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "inS") (CONJUNCTS_THEN2 (LABEL_TAC "open")
    (CONJUNCTS_THEN2 (LABEL_TAC "der") (CONJUNCTS_THEN2 (LABEL_TAC "rng")
    (LABEL_TAC "exit"))))))))) THEN
  MAP_EVERY X_GEN_TAC [`t0:real`; `t1:real`] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `a < t0 /\ t0 <= b'` STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPEC `{t:real | t1 <= t /\ t <= t0 /\ ~(t IN S)}` SUP) THEN ANTS_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN CONJ_TAC THENL
     [EXISTS_TAC `t1:real` THEN ASM_REWRITE_TAC[REAL_LE_REFL];
      EXISTS_TAC `t0:real` THEN SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `p = sup {t:real | t1 <= t /\ t <= t0 /\ ~(t IN S)}` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pub" o REWRITE_RULE[IN_ELIM_THM])
                             (LABEL_TAC "plub" o REWRITE_RULE[IN_ELIM_THM])) THEN
  SUBGOAL_THEN `t1 <= p /\ p <= t0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "pub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL];
      USE_THEN "plub" MATCH_MP_TAC THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((p:real) IN S)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    USE_THEN "open" (fun th -> MP_TAC(MP (SPEC `p:real` th) (ASSUME `(p:real) IN S`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    USE_THEN "plub" (MP_TAC o SPEC `p - d / &2`) THEN ANTS_TAC THENL
     [X_GEN_TAC `z:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `z <= p:real` ASSUME_TAC THENL
       [USE_THEN "pub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `~(p - d / &2 < z) ==> z <= p - d / &2`) THEN DISCH_TAC THEN
      UNDISCH_TAC `~((z:real) IN S)` THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. p < t /\ t <= t0 ==> t IN S` (LABEL_TAC "left") THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_TAC THEN SUBGOAL_THEN `t <= p:real` MP_TAC THENL
     [USE_THEN "pub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `p < t0` ASSUME_TAC THENL
   [ASM_CASES_TAC `p:real = t0` THENL [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  MP_TAC(SPEC `{t:real | t0 <= t /\ t < b /\ ~(t IN S)}` INF) THEN ANTS_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN CONJ_TAC THENL
     [EXISTS_TAC `(b' + b) / &2` THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_TAC THEN
      USE_THEN "inS" (fun th -> MP_TAC(MP (SPEC `(b' + b) / &2` th)
                                          (ASSUME `((b' + b) / &2) IN S`))) THEN
      ASM_REAL_ARITH_TAC;
      EXISTS_TAC `t0:real` THEN SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `q = inf {t:real | t0 <= t /\ t < b /\ ~(t IN S)}` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "qlb" o REWRITE_RULE[IN_ELIM_THM])
                             (LABEL_TAC "qglb" o REWRITE_RULE[IN_ELIM_THM])) THEN
  SUBGOAL_THEN `t0 <= q /\ q < b` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "qglb" MATCH_MP_TAC THEN SIMP_TAC[];
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(b' + b) / &2` THEN
      CONJ_TAC THENL
       [USE_THEN "qlb" MATCH_MP_TAC THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        DISCH_TAC THEN
        USE_THEN "inS" (fun th -> MP_TAC(MP (SPEC `(b' + b) / &2` th)
                                            (ASSUME `((b' + b) / &2) IN S`))) THEN
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((q:real) IN S)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    USE_THEN "open" (fun th -> MP_TAC(MP (SPEC `q:real` th) (ASSUME `(q:real) IN S`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    USE_THEN "qglb" (MP_TAC o SPEC `q + d / &2`) THEN ANTS_TAC THENL
     [X_GEN_TAC `z:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `q <= z:real` ASSUME_TAC THENL
       [USE_THEN "qlb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `~(z < q + d / &2) ==> q + d / &2 <= z`) THEN DISCH_TAC THEN
      UNDISCH_TAC `~((z:real) IN S)` THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t0 <= t /\ t < q ==> t IN S` (LABEL_TAC "right") THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_TAC THEN SUBGOAL_THEN `q <= t:real` MP_TAC THENL
     [USE_THEN "qlb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `t0 < q` ASSUME_TAC THENL
   [ASM_CASES_TAC `q:real = t0` THENL [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. p < t /\ t < q ==> t IN S` ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN ASM_CASES_TAC `t <= t0` THENL
     [USE_THEN "left" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "right" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real->real`; `f':real->real`; `p:real`; `q:real`; `rho:real`;
                 `kappa:real`] APX_1D_MONO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN USE_THEN "der" MATCH_MP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [MATCH_MP_TAC APX_1D_BAD_LEFT THEN
    MAP_EVERY EXISTS_TAC [`f:real->real`; `S:real->bool`; `p:real`; `q:real`; `c:real`;
                          `t0:real`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:real` THEN DISCH_TAC THEN
    USE_THEN "exit" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC APX_1D_BAD_RIGHT THEN
    MAP_EVERY EXISTS_TAC [`f:real->real`; `S:real->bool`; `p:real`; `q:real`; `c:real`;
                          `t0:real`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:real` THEN DISCH_TAC THEN
    USE_THEN "exit" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* The structure of S: an initial interval (a,tau), with f increasing at     *)
(* rate rho +/- kappa and c - f controlled by the distance to tau.           *)

let APX_RAY_1D = prove
 (`!f f' S a b b' c rho kappa.
        a < b' /\ b' < b /\ &0 <= kappa /\ kappa < rho /\ &0 < c /\
        (!t. t IN S ==> a < t /\ t <= b') /\
        (!t. t IN S ==> ?d. &0 < d /\ !t'. abs(t' - t) < d ==> t' IN S) /\
        (!t. t IN S ==> (f has_real_derivative f' t) (atreal t) /\
                        (abs(f' t - rho) <= kappa \/ abs(f' t + rho) <= kappa)) /\
        (!t. t IN S ==> --(c / &2) <= f t /\ f t < c) /\
        (!t m. a < t /\ t < b /\ ~(t IN S) /\ m < c
               ==> ?d. &0 < d /\ !t'. t' IN S /\ abs(t' - t) < d ==> m < abs(f t')) /\
        ~(S = {})
        ==> ?tau. a < tau /\ tau <= b' /\ (!t. t IN S <=> a < t /\ t < tau) /\
                  (!t. a < t /\ t < tau
                       ==> abs(f' t - rho) <= kappa /\
                           (rho - kappa) * (tau - t) <= c - f t /\
                           c - f t <= (rho + kappa) * (tau - t))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`f:real->real`; `f':real->real`; `S:real->bool`; `a:real`; `b:real`;
                `b':real`; `c:real`; `rho:real`; `kappa:real`] APX_RAY_1D_DOWN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "down")] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "inS") (CONJUNCTS_THEN2 (LABEL_TAC "open")
    (CONJUNCTS_THEN2 (LABEL_TAC "der") (CONJUNCTS_THEN2 (LABEL_TAC "rng")
    (CONJUNCTS_THEN2 (LABEL_TAC "exit") ASSUME_TAC)))))))))) THEN
  MP_TAC(SPEC `S:real->bool` SUP) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `b':real` THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `tau = sup S` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ub") (LABEL_TAC "lub")) THEN
  EXISTS_TAC `tau:real` THEN
  SUBGOAL_THEN `?t0:real. t0 IN S` (X_CHOOSE_TAC `t0:real`) THENL
   [ASM_MESON_TAC[MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `a < tau /\ tau <= b'` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `t0:real` THEN CONJ_TAC THENL
       [ASM_MESON_TAC[]; USE_THEN "ub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      USE_THEN "lub" MATCH_MP_TAC THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((tau:real) IN S)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    USE_THEN "open" (fun th -> MP_TAC(MP (SPEC `tau:real` th) (ASSUME `(tau:real) IN S`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(tau + d / &2) IN S` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> USE_THEN "ub" (MP_TAC o C MATCH_MP th)) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN S <=> a < t /\ t < tau` (LABEL_TAC "Seq") THENL
   [X_GEN_TAC `t:real` THEN EQ_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `a < t /\ t <= tau` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [ASM_MESON_TAC[]; USE_THEN "ub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      ASM_CASES_TAC `t:real = tau` THENL [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC];
      STRIP_TAC THEN
      SUBGOAL_THEN `?s:real. s IN S /\ t < s` STRIP_ASSUME_TAC THENL
       [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
        DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; REAL_NOT_LT]) THEN
        SUBGOAL_THEN `tau <= t:real` MP_TAC THENL
         [USE_THEN "lub" MATCH_MP_TAC THEN ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      USE_THEN "down" MATCH_MP_TAC THEN EXISTS_TAC `s:real` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!t. a < t /\ t < tau
                    ==> (f has_real_derivative f' t) (atreal t) /\
                        (abs(f' t - rho) <= kappa \/ abs(f' t + rho) <= kappa)`
  (LABEL_TAC "der1") THENL
   [GEN_TAC THEN DISCH_TAC THEN USE_THEN "der" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real->real`; `f':real->real`; `a:real`; `tau:real`; `rho:real`;
                 `kappa:real`] APX_1D_MONO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THENL
   [ALL_TAC;
    DISCH_TAC THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN MATCH_MP_TAC APX_1D_BAD_RIGHT THEN
    MAP_EVERY EXISTS_TAC [`f:real->real`; `S:real->bool`; `a:real`; `tau:real`; `c:real`;
                          `(a + tau) / &2`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[];
      USE_THEN "Seq" (fun th -> REWRITE_TAC[th]);
      USE_THEN "rng" ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      X_GEN_TAC `m:real` THEN DISCH_TAC THEN USE_THEN "exit" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]] THEN
  SUBGOAL_THEN `!t. a < t /\ t < tau ==> abs(f' t - rho) <= kappa` (LABEL_TAC "dr") THENL
   [MATCH_MP_TAC APX_1D_INCR_DERIV THEN EXISTS_TAC `f:real->real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  CONJ_TAC THENL [USE_THEN "dr" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real->real`; `f':real->real`; `a:real`; `tau:real`; `c:real`;
                 `rho:real`; `kappa:real`] APX_1D_ENDBOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
       [USE_THEN "der1" (fun th -> MP_TAC(MP (SPEC `t':real` th) (ASSUME `a < t' /\ t' < tau`))) THEN
        SIMP_TAC[];
        USE_THEN "dr" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      GEN_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `(t':real) IN S` ASSUME_TAC THENL
       [USE_THEN "Seq" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "rng" (fun th -> MP_TAC(MP (SPEC `t':real` th) (ASSUME `(t':real) IN S`))) THEN
      SIMP_TAC[];
      X_GEN_TAC `m:real` THEN DISCH_TAC THEN
      USE_THEN "exit" (MP_TAC o SPECL [`tau:real`; `max m (c / &2)`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(s:real) IN S` ASSUME_TAC THENL
       [USE_THEN "Seq" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "rng" (fun th -> MP_TAC(MP (SPEC `s:real` th) (ASSUME `(s:real) IN S`))) THEN
      REAL_ARITH_TAC];
    DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The radial lines t -> exp(t / sqrt 2) om of a neck (om a                  *)
(* unit vector, t the s-value): membership in slabs, openness of preimages,  *)
(* and the chain rule for apx_sval o h along them.                           *)
(* ------------------------------------------------------------------------- *)

let APX_RAY_SVAL = prove
 (`!(om:real^3) t. norm om = &1 ==> apx_sval(exp(t / sqrt(&2)) % om) = t`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[apx_sval; NORM_MUL; REAL_ABS_EXP; REAL_MUL_RID] THEN
  REWRITE_TAC[LOG_EXP] THEN
  SUBGOAL_THEN `~(sqrt(&2) = &0)` MP_TAC THENL
   [SIMP_TAC[SQRT_EQ_0; REAL_POS] THEN REAL_ARITH_TAC; CONV_TAC REAL_FIELD]);;

let APX_RAY_NONZERO = prove
 (`!(om:real^3) t. norm om = &1 ==> ~(exp(t / sqrt(&2)) % om = vec 0)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `norm:real^3->real`) THEN
  ASM_REWRITE_TAC[NORM_MUL; REAL_ABS_EXP; NORM_0; REAL_MUL_RID] THEN
  MP_TAC(SPEC `t / sqrt(&2)` REAL_EXP_POS_LT) THEN REAL_ARITH_TAC);;

let APX_RAY_IN_SLAB = prove
 (`!(om:real^3) t a b.
        norm om = &1 ==> (exp(t / sqrt(&2)) % om IN apx_slab a b <=> a < t /\ t < b)`,
  SIMP_TAC[APX_SLAB_SVAL; APX_RAY_SVAL; APX_RAY_NONZERO]);;

let APX_RAY_IN_DOM = prove
 (`!(om:real^3) t eps.
        norm om = &1
        ==> (exp(t / sqrt(&2)) % om IN rfs_neck_dom eps <=> --inv eps < t /\ t < inv eps)`,
  SIMP_TAC[APX_SLAB_NECK_DOM; APX_RAY_IN_SLAB]);;

let APX_EXP_HALF_DERIV = prove
 (`!t. ((\s. exp(s / sqrt(&2))) has_real_derivative
        (exp(t / sqrt(&2)) * inv(sqrt(&2)))) (atreal t)`,
  GEN_TAC THEN REAL_DIFF_TAC THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let APX_RAY_CONT = prove
 (`!(om:real^3) t. (\r. exp(drop r / sqrt(&2)) % om) continuous (at (lift t))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`at(lift t)`; `\r:real^1. exp(drop r / sqrt(&2))`; `om:real^3`]
                CONTINUOUS_VMUL) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`\s. exp(s / sqrt(&2))`; `t:real`] (GEN `f:real->real` (GEN `x:real`
    REAL_CONTINUOUS_CONTINUOUS_ATREAL))) THEN
  REWRITE_TAC[o_DEF] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
  EXISTS_TAC `exp(t / sqrt(&2)) * inv(sqrt(&2))` THEN
  REWRITE_TAC[APX_EXP_HALF_DERIV]);;

let APX_RAY_OPEN_PRE = prove
 (`!(V:real^3->bool) (om:real^3) t.
        open V /\ exp(t / sqrt(&2)) % om IN V
        ==> ?d. &0 < d /\ !t'. abs(t' - t) < d ==> exp(t' / sqrt(&2)) % om IN V`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`om:real^3`; `t:real`] APX_RAY_CONT) THEN
  REWRITE_TAC[continuous_at] THEN
  UNDISCH_TAC `open(V:real^3->bool)` THEN REWRITE_TAC[open_def] THEN
  DISCH_THEN(MP_TAC o SPEC `exp(t / sqrt(&2)) % (om:real^3)`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `lift s`) THEN
  REWRITE_TAC[LIFT_DROP; DIST_LIFT] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[DIST_SYM] THEN SIMP_TAC[]);;

let APX_RAY_SVAL_DERIV = prove
 (`!(h:real^3->real^3) (om:real^3) t.
        h differentiable (at (exp(t / sqrt(&2)) % om)) /\
        ~(h(exp(t / sqrt(&2)) % om) = vec 0)
        ==> ((\s. apx_sval(h(exp(s / sqrt(&2)) % om))) has_real_derivative
             (sqrt(&2) * (h(exp(t / sqrt(&2)) % om) dot
                          frechet_derivative h (at (exp(t / sqrt(&2)) % om))
                            (inv(sqrt(&2)) % exp(t / sqrt(&2)) % om)) /
              (h(exp(t / sqrt(&2)) % om) dot h(exp(t / sqrt(&2)) % om)))) (atreal t)`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `v = exp(t / sqrt(&2)) % (om:real^3)` THEN
  ABBREV_TAC `y = (h:real^3->real^3) v` THEN STRIP_TAC THEN
  ABBREV_TAC `Dh = frechet_derivative (h:real^3->real^3) (at v)` THEN
  SUBGOAL_THEN `((h:real^3->real^3) has_derivative Dh) (at v) /\ linear(Dh:real^3->real^3)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Dh" THEN ASM_SIMP_TAC[GSYM FRECHET_DERIVATIVE_WORKS; LINEAR_FRECHET_DERIVATIVE];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\r. exp(drop r / sqrt(&2)) % (om:real^3)) has_derivative
                 (\r. drop r % (inv(sqrt(&2)) % v))) (at (lift t))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\s. exp(s / sqrt(&2))`; `exp(t / sqrt(&2)) * inv(sqrt(&2))`; `t:real`;
                   `om:real^3`] APX_REAL_VMUL_VD) THEN
    REWRITE_TAC[APX_EXP_HALF_DERIV; has_vector_derivative] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN EXPAND_TAC "v" THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\r. exp(drop r / sqrt(&2)) % (om:real^3)`; `h:real^3->real^3`;
                 `\r. drop r % (inv(sqrt(&2)) % (v:real^3))`; `Dh:real^3->real^3`;
                 `lift t`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `y:real^3` APX_SVAL_DERIV) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(h:real^3->real^3) o (\r. exp(drop r / sqrt(&2)) % (om:real^3))`;
                 `\z:real^3. lift(apx_sval z)`;
                 `(Dh:real^3->real^3) o (\r. drop r % (inv(sqrt(&2)) % (v:real^3)))`;
                 `\w. lift(sqrt(&2) * ((y:real^3) dot w) / (y dot y))`;
                 `lift t`] DIFF_CHAIN_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[o_THM; LIFT_DROP]; ALL_TAC] THEN
  REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `r:real^1` THEN
  ASM_SIMP_TAC[LINEAR_CMUL; DOT_RMUL] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM LIFT_DROP] THEN
  REWRITE_TAC[GSYM LIFT_CMUL; LIFT_EQ] THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let APX_RAY_UNIT_FACTS = prove
 (`!v:real^3.
        ~(v = vec 0)
        ==> sqrt(&2) * (v dot (inv(sqrt(&2)) % v)) / (v dot v) = &1 /\
            (inv(sqrt(&2)) % v) dot (cylinder_flow (&0) v ** (inv(sqrt(&2)) % v)) = &1`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~((v:real^3) dot v = &0) /\ ~(norm(v:real^3) = &0) /\ ~(sqrt(&2) = &0) /\
                sqrt(&2) pow 2 = &2`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_EQ_0; NORM_EQ_0] THEN SIMP_TAC[SQRT_POW_2; REAL_POS] THEN
    SIMP_TAC[SQRT_EQ_0; REAL_POS] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[APX_CYL0_QUAD] THEN REWRITE_TAC[DOT_LMUL; DOT_RMUL; GSYM NORM_POW_2] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `~(norm(v:real^3) = &0)` THEN UNDISCH_TAC `~(sqrt(&2) = &0)` THEN
    CONV_TAC REAL_FIELD;
    UNDISCH_TAC `~(norm(v:real^3) = &0)` THEN UNDISCH_TAC `~(sqrt(&2) = &0)` THEN
    UNDISCH_TAC `sqrt(&2) pow 2 = &2` THEN CONV_TAC REAL_FIELD]);;

(* Exit: approaching (along a radial line of N') a point outside N, the      *)
(* s-value of N leaves every compact range [-m,m], m < 1/eps.                *)

let APX_RAY_EXIT = prove
 (`!top atlas (e:real^3->A) e' (ei:A->real^3) eps (om:real^3).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ &0 < eps /\
        mfd_param top atlas (rfs_neck_dom eps) e /\
        mfd_param top atlas (rfs_neck_dom eps) e' /\
        (!z. z IN rfs_neck_dom eps ==> ei(e z) = z) /\ norm om = &1
        ==> !t m. --inv eps < t /\ t < inv eps /\
                  ~(e'(exp(t / sqrt(&2)) % om) IN IMAGE e (rfs_neck_dom eps)) /\
                  m < inv eps
                  ==> ?d. &0 < d /\
                          !t'. (--inv eps < t' /\ t' < inv eps /\
                                e'(exp(t' / sqrt(&2)) % om) IN IMAGE e (rfs_neck_dom eps)) /\
                               abs(t' - t) < d
                               ==> m < abs(apx_sval(ei(e'(exp(t' / sqrt(&2)) % om))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`t:real`; `m:real`] THEN
  STRIP_TAC THEN ASM_CASES_TAC `m < &0` THENL
   [EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPEC `apx_sval((ei:A->real^3)((e':real^3->A)(exp(t' / sqrt(&2)) % om)))`
                REAL_ABS_POS) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`eps:real`; `m:real`] APX_SUBSLAB) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `K = cball(vec 0:real^3,exp(m / sqrt(&2))) DIFF ball(vec 0,exp(--m / sqrt(&2)))` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `e:real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e0:A->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `e':real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e1:A->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `closed_in top (IMAGE (e:real^3->A) K)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean (rfs_neck_dom eps)` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open {v:real^3 | v IN rfs_neck_dom eps /\
                     (e':real^3->A) v IN topspace top DIFF IMAGE (e:real^3->A) K}`
  ASSUME_TAC THENL
   [UNDISCH_TAC `continuous_map (subtopology euclidean (rfs_neck_dom eps),top)
                                (e':real^3->A)` THEN
    REWRITE_TAC[continuous_map; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    DISCH_THEN(MP_TAC o SPEC `topspace top DIFF IMAGE (e:real^3->A) K` o CONJUNCT2) THEN
    ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_TOPSPACE; APX_NECK_DOM_OPEN; OPEN_IN_OPEN_EQ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{v:real^3 | v IN rfs_neck_dom eps /\
                     (e':real^3->A) v IN topspace top DIFF IMAGE (e:real^3->A) K}`;
                 `om:real^3`; `t:real`] APX_RAY_OPEN_PRE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM; IN_DIFF] THEN ASM_SIMP_TAC[APX_RAY_IN_DOM] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (e':real^3->A) (rfs_neck_dom eps) SUBSET topspace top` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[APX_RAY_IN_DOM];
      UNDISCH_TAC `~((e':real^3->A)(exp(t / sqrt(&2)) % om) IN
                     IMAGE (e:real^3->A) (rfs_neck_dom eps))` THEN
      UNDISCH_TAC `(K:real^3->bool) SUBSET rfs_neck_dom eps` THEN SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[IN_ELIM_THM; IN_DIFF] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `(e':real^3->A)(exp(s / sqrt(&2)) % om) IN IMAGE (e:real^3->A) (rfs_neck_dom eps)` THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `~(abs x <= m) ==> m < abs x`) THEN DISCH_TAC THEN
  UNDISCH_TAC `~((e':real^3->A)(exp(s / sqrt(&2)) % om) IN IMAGE (e:real^3->A) K)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[APX_SVAL_NECK_DOM]);;

(* The overlap of two necks along a radial line of N' (one-sided chain       *)
(* clauses: N' misses the negative quarter of N, N misses the positive       *)
(* quarter of N'), given the alignment of E2.1: an initial interval          *)
(* (-1/eps,tau) on which s_N increases at rate rho +/- kappa up to 1/eps.     *)

let APX_RAY_OVERLAP = prove
 (`!top atlas (e:real^3->A) e' (ei:A->real^3) eps rho kappa (om:real^3).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ &0 < eps /\
        mfd_param top atlas (rfs_neck_dom eps) e /\
        mfd_param top atlas (rfs_neck_dom eps) e' /\
        (!z. z IN rfs_neck_dom eps ==> ei(e z) = z) /\ norm om = &1 /\
        &0 <= kappa /\ kappa < rho /\
        (!v. v IN rfs_neck_dom eps /\ e' v IN IMAGE e (rfs_neck_dom eps)
             ==> ?sg. (sg = &1 \/ sg = -- &1) /\
                      !k. abs(sqrt(&2) * (ei(e' v) dot frechet_derivative (ei o e') (at v) k) /
                              (ei(e' v) dot ei(e' v)) -
                              sg * rho * sqrt(&2) * (v dot k) / (v dot v))
                          <= kappa * sqrt(k dot (cylinder_flow (&0) v ** k))) /\
        DISJOINT (IMAGE e' (rfs_neck_dom eps))
                 (IMAGE e (apx_slab (--inv eps) (--inv(&2 * eps)))) /\
        DISJOINT (IMAGE e (rfs_neck_dom eps))
                 (IMAGE e' (apx_slab (inv(&2 * eps)) (inv eps))) /\
        (?t. --inv eps < t /\ t < inv eps /\
             e'(exp(t / sqrt(&2)) % om) IN IMAGE e (rfs_neck_dom eps))
        ==> ?tau. --inv eps < tau /\ tau <= inv(&2 * eps) /\
                  (!t. (--inv eps < t /\ t < inv eps /\
                        e'(exp(t / sqrt(&2)) % om) IN IMAGE e (rfs_neck_dom eps)) <=>
                       --inv eps < t /\ t < tau) /\
                  (!t. --inv eps < t /\ t < tau
                       ==> abs(sqrt(&2) * (ei(e'(exp(t / sqrt(&2)) % om)) dot
                                 frechet_derivative (ei o e') (at (exp(t / sqrt(&2)) % om))
                                   (inv(sqrt(&2)) % exp(t / sqrt(&2)) % om)) /
                               (ei(e'(exp(t / sqrt(&2)) % om)) dot
                                ei(e'(exp(t / sqrt(&2)) % om))) - rho) <= kappa /\
                           (rho - kappa) * (tau - t) <=
                           inv eps - apx_sval(ei(e'(exp(t / sqrt(&2)) % om))) /\
                           inv eps - apx_sval(ei(e'(exp(t / sqrt(&2)) % om))) <=
                           (rho + kappa) * (tau - t))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "align")
    (CONJUNCTS_THEN2 (LABEL_TAC "h2") (CONJUNCTS_THEN2 (LABEL_TAC "h3")
     ASSUME_TAC)))))))))))) THEN
  SUBGOAL_THEN `&0 < inv eps /\ inv(&2 * eps) = inv eps / &2` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV; REAL_INV_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `rfs_neck_dom eps`; `e:real^3->A`; `e':real^3->A`;
                 `ei:A->real^3`] APX_PARAM_TRANSITION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tr"))) THEN
  MP_TAC(ISPECL [`\t. apx_sval((ei:A->real^3)((e':real^3->A)(exp(t / sqrt(&2)) % om)))`;
                 `\t. sqrt(&2) * ((ei:A->real^3)((e':real^3->A)(exp(t / sqrt(&2)) % om)) dot
                         frechet_derivative (ei o e') (at (exp(t / sqrt(&2)) % om))
                           (inv(sqrt(&2)) % exp(t / sqrt(&2)) % om)) /
                      (ei(e'(exp(t / sqrt(&2)) % om)) dot ei(e'(exp(t / sqrt(&2)) % om)))`;
                 `{t | --inv eps < t /\ t < inv eps /\
                       (e':real^3->A)(exp(t / sqrt(&2)) % om) IN
                       IMAGE (e:real^3->A) (rfs_neck_dom eps)}`;
                 `--inv eps`; `inv eps`; `inv(&2 * eps)`; `inv eps`; `rho:real`;
                 `kappa:real`] APX_RAY_1D) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `~(i / &2 < t) ==> t <= i / &2`) THEN DISCH_TAC THEN
      USE_THEN "h3" (MP_TAC o REWRITE_RULE[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY]) THEN
      DISCH_THEN(MP_TAC o SPEC `(e':real^3->A)(exp(t / sqrt(&2)) % om)`) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_SIMP_TAC[APX_RAY_IN_SLAB] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`{v:real^3 | v IN rfs_neck_dom eps /\
                        (e':real^3->A) v IN IMAGE (e:real^3->A) (rfs_neck_dom eps)}`;
                     `om:real^3`; `t:real`] APX_RAY_OPEN_PRE) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[APX_RAY_IN_DOM] THEN
      REWRITE_TAC[CONJ_ASSOC];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `exp(t / sqrt(&2)) % (om:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
       [ASM_SIMP_TAC[APX_RAY_IN_DOM]; ALL_TAC] THEN
      SUBGOAL_THEN
       `(ei:A->real^3)((e':real^3->A)(exp(t / sqrt(&2)) % om)) IN rfs_neck_dom eps /\
        (e:real^3->A)(ei(e'(exp(t / sqrt(&2)) % om))) = e'(exp(t / sqrt(&2)) % om)`
      STRIP_ASSUME_TAC THENL
       [USE_THEN "tr" (MP_TAC o SPEC `exp(t / sqrt(&2)) % (om:real^3)`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [MP_TAC(ISPECL [`(ei:A->real^3) o (e':real^3->A)`; `om:real^3`; `t:real`]
                      APX_RAY_SVAL_DERIV) THEN
        REWRITE_TAC[o_THM] THEN ANTS_TAC THENL
         [CONJ_TAC THENL
           [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
            EXISTS_TAC `{v:real^3 | v IN rfs_neck_dom eps /\
                          (e':real^3->A) v IN IMAGE (e:real^3->A) (rfs_neck_dom eps)}` THEN
            ASM_REWRITE_TAC[IN_ELIM_THM];
            ASM_MESON_TAC[APX_SVAL_NECK_DOM]];
          REWRITE_TAC[]];
        USE_THEN "align" (MP_TAC o SPEC `exp(t / sqrt(&2)) % (om:real^3)`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `sg:real` (CONJUNCTS_THEN2 ASSUME_TAC
          (MP_TAC o SPEC `inv(sqrt(&2)) % exp(t / sqrt(&2)) % (om:real^3)`))) THEN
        MP_TAC(SPEC `exp(t / sqrt(&2)) % (om:real^3)` APX_RAY_UNIT_FACTS) THEN
        ASM_SIMP_TAC[APX_RAY_NONZERO; SQRT_1; REAL_MUL_RID] THEN
        FIRST_X_ASSUM DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `exp(t / sqrt(&2)) % (om:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
       [ASM_SIMP_TAC[APX_RAY_IN_DOM]; ALL_TAC] THEN
      SUBGOAL_THEN
       `(ei:A->real^3)((e':real^3->A)(exp(t / sqrt(&2)) % om)) IN rfs_neck_dom eps /\
        (e:real^3->A)(ei(e'(exp(t / sqrt(&2)) % om))) = e'(exp(t / sqrt(&2)) % om)`
      STRIP_ASSUME_TAC THENL
       [USE_THEN "tr" (MP_TAC o SPEC `exp(t / sqrt(&2)) % (om:real^3)`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
        ALL_TAC] THEN
      ABBREV_TAC `y = (ei:A->real^3)((e':real^3->A)(exp(t / sqrt(&2)) % om))` THEN
      MP_TAC(SPECL [`eps:real`; `y:real^3`] APX_SVAL_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `~(s < --(i / &2)) ==> --(i / &2) <= s`) THEN DISCH_TAC THEN
      USE_THEN "h2" (MP_TAC o REWRITE_RULE[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY]) THEN
      DISCH_THEN(MP_TAC o SPEC `(e:real^3->A) y`) THEN REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`t:real`; `m:real`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `e:real^3->A`; `e':real^3->A`; `ei:A->real^3`; `eps:real`;
                     `om:real^3`] APX_RAY_EXIT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `tau:real` THEN REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The variation of s_N along a level sphere of N' that lies in               *)
(* N: tangent vectors k have ds(k) = 0, so the alignment bound gives          *)
(* |d(s_N o tau)(k)| <= kappa |k|_G0, and a great circle arc of angle <= pi   *)
(* has G0-length sqrt 2 times its angle.                                     *)
(* ------------------------------------------------------------------------- *)

let APX_CURVE_SVAL_DERIV = prove
 (`!(h:real^3->real^3) (c:real->real^3) c' s.
        ((\r. c(drop r)) has_vector_derivative c') (at (lift s)) /\
        h differentiable (at (c s)) /\ ~(h(c s) = vec 0)
        ==> ((\t. apx_sval(h(c t))) has_real_derivative
             (sqrt(&2) * (h(c s) dot frechet_derivative h (at (c s)) c') /
              (h(c s) dot h(c s)))) (atreal s)`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `v = (c:real->real^3) s` THEN
  ABBREV_TAC `y = (h:real^3->real^3) v` THEN STRIP_TAC THEN
  ABBREV_TAC `Dh = frechet_derivative (h:real^3->real^3) (at v)` THEN
  SUBGOAL_THEN `((h:real^3->real^3) has_derivative Dh) (at v) /\ linear(Dh:real^3->real^3)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Dh" THEN ASM_SIMP_TAC[GSYM FRECHET_DERIVATIVE_WORKS; LINEAR_FRECHET_DERIVATIVE];
    ALL_TAC] THEN
  UNDISCH_TAC `((\r. (c:real->real^3)(drop r)) has_vector_derivative c') (at (lift s))` THEN
  REWRITE_TAC[has_vector_derivative] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\r. (c:real->real^3)(drop r)`; `h:real^3->real^3`;
                 `\x. drop x % (c':real^3)`; `Dh:real^3->real^3`;
                 `lift s`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `y:real^3` APX_SVAL_DERIV) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(h:real^3->real^3) o (\r. (c:real->real^3)(drop r))`;
                 `\z:real^3. lift(apx_sval z)`;
                 `(Dh:real^3->real^3) o (\x. drop x % (c':real^3))`;
                 `\w. lift(sqrt(&2) * ((y:real^3) dot w) / (y dot y))`;
                 `lift s`] DIFF_CHAIN_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[o_THM; LIFT_DROP]; ALL_TAC] THEN
  REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `r:real^1` THEN
  ASM_SIMP_TAC[LINEAR_CMUL; DOT_RMUL] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM LIFT_DROP] THEN
  REWRITE_TAC[GSYM LIFT_CMUL; LIFT_EQ] THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let APX_CIRCLE_VD = prove
 (`!(a:real^3) b s.
        ((\r. cos(drop r) % a + sin(drop r) % b) has_vector_derivative
         (--sin s % a + cos s % b)) (at (lift s))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC APX_REAL_VMUL_VD THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_SIN; HAS_REAL_DERIVATIVE_COS]);;

let APX_CIRCLE_FACTS = prove
 (`!(u:real^3) q r0 s.
        norm u = &1 /\ norm q = &1 /\ u dot q = &0 /\ &0 < r0
        ==> norm(cos s % (r0 % u) + sin s % (r0 % q)) = r0 /\
            (cos s % (r0 % u) + sin s % (r0 % q)) dot
            (--sin s % (r0 % u) + cos s % (r0 % q)) = &0 /\
            (--sin s % (r0 % u) + cos s % (r0 % q)) dot
            (--sin s % (r0 % u) + cos s % (r0 % q)) = r0 pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(u:real^3) dot u = &1 /\ (q:real^3) dot q = &1 /\ (q:real^3) dot u = &0`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM NORM_EQ_1] THEN ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `s:real` SIN_CIRCLE) THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[vector_norm; DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SQRT_UNIQUE THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `sin s pow 2 + cos s pow 2 = &1` THEN CONV_TAC REAL_RING;
    CONV_TAC REAL_RING;
    UNDISCH_TAC `sin s pow 2 + cos s pow 2 = &1` THEN CONV_TAC REAL_RING]);;

let APX_SPHERE_VARIATION = prove
 (`!(h:real^3->real^3) U r0 kappa rho.
        &0 < r0 /\ &0 <= kappa /\
        (!v. norm v = r0 ==> v IN U) /\
        (!v. v IN U ==> h differentiable (at v) /\ ~(h v = vec 0)) /\
        (!v. v IN U
             ==> ?sg. (sg = &1 \/ sg = -- &1) /\
                      !k. abs(sqrt(&2) * (h v dot frechet_derivative h (at v) k) /
                              (h v dot h v) -
                              sg * rho * sqrt(&2) * (v dot k) / (v dot v))
                          <= kappa * sqrt(k dot (cylinder_flow (&0) v ** k)))
        ==> !u w. norm u = &1 /\ norm w = &1
                  ==> abs(apx_sval(h(r0 % w)) - apx_sval(h(r0 % u)))
                      <= sqrt(&2) * pi * kappa`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "sph") (CONJUNCTS_THEN2 (LABEL_TAC "dif")
     (LABEL_TAC "align"))))) THEN
  MAP_EVERY X_GEN_TAC [`u:real^3`; `w:real^3`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^3`; `w:real^3`] APX_GREAT_CIRCLE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^3` (X_CHOOSE_THEN `th:real` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `c = \s. cos s % (r0 % u) + sin s % (r0 % (q:real^3))` THEN
  SUBGOAL_THEN `!s. (c:real->real^3) s IN U` (LABEL_TAC "cU") THENL
   [GEN_TAC THEN USE_THEN "sph" MATCH_MP_TAC THEN EXPAND_TAC "c" THEN
    ASM_MESON_TAC[APX_CIRCLE_FACTS];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:real->real^3) (&0) = r0 % u /\ c th = r0 % w` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN ASM_REWRITE_TAC[COS_0; SIN_0; VECTOR_MUL_LID; VECTOR_MUL_LZERO;
                                         VECTOR_ADD_RID] THEN
    REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
    REWRITE_TAC[REAL_MUL_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. ((\t. apx_sval((h:real^3->real^3)((c:real->real^3) t))) has_real_derivative
         (sqrt(&2) * (h(c s) dot frechet_derivative h (at (c s))
                                   (--sin s % (r0 % u) + cos s % (r0 % q))) /
          (h(c s) dot h(c s)))) (atreal s)`
  (LABEL_TAC "gder") THENL
   [GEN_TAC THEN MATCH_MP_TAC APX_CURVE_SVAL_DERIV THEN CONJ_TAC THENL
     [EXPAND_TAC "c" THEN REWRITE_TAC[APX_CIRCLE_VD];
      USE_THEN "dif" MATCH_MP_TAC THEN USE_THEN "cU" MATCH_ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. abs(sqrt(&2) * ((h:real^3->real^3)((c:real->real^3) s) dot
                         frechet_derivative h (at (c s))
                           (--sin s % (r0 % u) + cos s % (r0 % q))) /
            (h(c s) dot h(c s))) <= sqrt(&2) * kappa`
  (LABEL_TAC "gbd") THENL
   [GEN_TAC THEN
    USE_THEN "align" (MP_TAC o SPEC `(c:real->real^3) s`) THEN
    ANTS_TAC THENL [USE_THEN "cU" MATCH_ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `sg:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (MP_TAC o SPEC `--sin s % (r0 % u) + cos s % (r0 % (q:real^3))`))) THEN
    MP_TAC(SPECL [`u:real^3`; `q:real^3`; `r0:real`; `s:real`] APX_CIRCLE_FACTS) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "c" THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[APX_CYL0_QUAD; real_div; REAL_MUL_LZERO; REAL_MUL_RZERO;
                    REAL_SUB_RZERO] THEN
    SUBGOAL_THEN `sqrt((&2 * inv(r0 pow 2)) * r0 pow 2) = sqrt(&2)` SUBST1_TAC THENL
     [AP_TERM_TAC THEN UNDISCH_TAC `&0 < r0` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `th = &0` THENL
   [UNDISCH_TAC `w = cos th % u + sin th % (q:real^3)` THEN
    ASM_REWRITE_TAC[COS_0; SIN_0; VECTOR_MUL_LID; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[PI_POS_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. apx_sval((h:real^3->real^3)((c:real->real^3) t))`;
                 `\s. sqrt(&2) * ((h:real^3->real^3)((c:real->real^3) s) dot
                         frechet_derivative h (at (c s))
                           (--sin s % (r0 % u) + cos s % (r0 % q))) /
                      (h(c s) dot h(c s))`;
                 `&0`; `th:real`] REAL_MVT) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC APX_1D_CONT THEN
      EXISTS_TAC `\s. sqrt(&2) * ((h:real^3->real^3)((c:real->real^3) s) dot
                         frechet_derivative h (at (c s))
                           (--sin s % (r0 % u) + cos s % (r0 % q))) /
                      (h(c s) dot h(c s))` THEN
      REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN USE_THEN "gder" MATCH_ACCEPT_TAC;
      GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[] THEN USE_THEN "gder" MATCH_ACCEPT_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_SUB_RZERO; REAL_ABS_MUL] THEN
  SUBGOAL_THEN `abs th = th /\ th <= pi` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `abs th = th`] THEN
  USE_THEN "gbd" (ASSUME_TAC o SPEC `z:real`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(sqrt(&2) * kappa) * th` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(a * k) * t = a * t * k`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[SQRT_POS_LE; REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* E2, the structure of the overlap of two necks N = e(D),                   *)
(* N' = e'(D) under the one-sided chain clauses (the negative quarter of N'  *)
(* lies in N; N' misses the negative quarter of N; N misses the positive     *)
(* quarter of N') and the alignment of E2.1.  In the coordinates of N':      *)
(* s_N = s' + Delta up to d0, with 1/(2eps) <= Delta <= 3/(2eps); the part   *)
(* of N' below 1/eps - Delta - d0 lies in N; the sign of the alignment is +1.*)
(* ------------------------------------------------------------------------- *)

let APX_POLAR = prove
 (`!v:real^3.
        ~(v = vec 0)
        ==> norm(inv(norm v) % v) = &1 /\
            exp(apx_sval v / sqrt(&2)) % (inv(norm v) % v) = v`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < norm(v:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM; VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
  SUBGOAL_THEN `apx_sval v / sqrt(&2) = log(norm(v:real^3))` SUBST1_TAC THENL
   [REWRITE_TAC[apx_sval] THEN
    SUBGOAL_THEN `~(sqrt(&2) = &0)` MP_TAC THENL
     [SIMP_TAC[SQRT_EQ_0; REAL_POS] THEN REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  ASM_SIMP_TAC[EXP_LOG; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID]);;

let APX_PAIR_ARITH1 = prove
 (`!X Fv r k.
        &0 < X /\ &0 <= k /\ (r - k) * X <= Fv /\ Fv <= (r + k) * X
        ==> abs(X - Fv) <= (abs(r - &1) + k) * X`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= k * X` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&1 <= r` THENL
   [SUBGOAL_THEN `abs(r - &1) = r - &1 /\ &0 <= (r - &1) * X` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC];
    SUBGOAL_THEN `abs(r - &1) = &1 - r /\ &0 <= (&1 - r) * X` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC]] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let APX_INV2 = prove
 (`!eps. inv(&2 * eps) = inv eps / &2`,
  REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC);;

let APX_PAIR_STRUCT = prove
 (`!top atlas (e:real^3->A) e' (ei:A->real^3) eps rho kappa.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ &0 < eps /\
        mfd_param top atlas (rfs_neck_dom eps) e /\
        mfd_param top atlas (rfs_neck_dom eps) e' /\
        (!z. z IN rfs_neck_dom eps ==> ei(e z) = z) /\
        &0 <= kappa /\ kappa < rho /\
        (!v. v IN rfs_neck_dom eps /\ e' v IN IMAGE e (rfs_neck_dom eps)
             ==> ?sg. (sg = &1 \/ sg = -- &1) /\
                      !k. abs(sqrt(&2) * (ei(e' v) dot frechet_derivative (ei o e') (at v) k) /
                              (ei(e' v) dot ei(e' v)) -
                              sg * rho * sqrt(&2) * (v dot k) / (v dot v))
                          <= kappa * sqrt(k dot (cylinder_flow (&0) v ** k))) /\
        IMAGE e' (apx_slab (--inv eps) (--inv(&2 * eps))) SUBSET
        IMAGE e (rfs_neck_dom eps) /\
        DISJOINT (IMAGE e' (rfs_neck_dom eps))
                 (IMAGE e (apx_slab (--inv eps) (--inv(&2 * eps)))) /\
        DISJOINT (IMAGE e (rfs_neck_dom eps))
                 (IMAGE e' (apx_slab (inv(&2 * eps)) (inv eps)))
        ==> ?Delta.
              inv(&2 * eps) <= Delta /\ Delta <= &3 * inv(&2 * eps) /\
              (!v. v IN rfs_neck_dom eps /\ e' v IN IMAGE e (rfs_neck_dom eps)
                   ==> abs(apx_sval(ei(e' v)) - apx_sval v - Delta) <=
                       (abs(rho - &1) + kappa) * (&4 * inv eps) + sqrt(&2) * pi * kappa) /\
              (!v. v IN rfs_neck_dom eps /\
                   apx_sval v < inv eps - Delta -
                                ((abs(rho - &1) + kappa) * (&4 * inv eps) +
                                 sqrt(&2) * pi * kappa)
                   ==> e' v IN IMAGE e (rfs_neck_dom eps)) /\
              (!v. v IN rfs_neck_dom eps /\ e' v IN IMAGE e (rfs_neck_dom eps)
                   ==> !k. abs(sqrt(&2) * (ei(e' v) dot frechet_derivative (ei o e') (at v) k) /
                               (ei(e' v) dot ei(e' v)) -
                               rho * sqrt(&2) * (v dot k) / (v dot v))
                           <= kappa * sqrt(k dot (cylinder_flow (&0) v ** k)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "align") (CONJUNCTS_THEN2 (LABEL_TAC "h1")
    (CONJUNCTS_THEN2 (LABEL_TAC "h2") (LABEL_TAC "h3")))))))))))) THEN
  ABBREV_TAC `A = abs(rho - &1) + kappa` THEN
  SUBGOAL_THEN `&0 <= A` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN MP_TAC(SPEC `rho - &1` REAL_ABS_POS) THEN
    UNDISCH_TAC `&0 <= kappa` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv eps` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `rfs_neck_dom eps`; `e:real^3->A`; `e':real^3->A`;
                 `ei:A->real^3`] APX_PARAM_TRANSITION) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tr"))) THEN
  (* the negative quarter of N' lies in the overlap *)
  SUBGOAL_THEN `!v. v IN rfs_neck_dom eps /\ apx_sval v < --inv(&2 * eps)
                    ==> (e':real^3->A) v IN IMAGE (e:real^3->A) (rfs_neck_dom eps)`
  (LABEL_TAC "q'") THENL
   [GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "h1" (MATCH_MP_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]) THEN
    MP_TAC(SPECL [`eps:real`; `v:real^3`] APX_SVAL_NECK_DOM) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN
    UNDISCH_TAC `abs(apx_sval v) < inv eps` THEN
    UNDISCH_TAC `apx_sval v < --inv(&2 * eps)` THEN
    MP_TAC(SPEC `eps:real` APX_INV2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* one radial line at a time *)
  SUBGOAL_THEN
   `!om:real^3. ?tau. norm om = &1
      ==> --inv eps < tau /\ tau <= inv(&2 * eps) /\
          (!t. (--inv eps < t /\ t < inv eps /\
                (e':real^3->A)(exp(t / sqrt(&2)) % om) IN IMAGE (e:real^3->A) (rfs_neck_dom eps)) <=>
               --inv eps < t /\ t < tau) /\
          (!t. --inv eps < t /\ t < tau
               ==> abs(sqrt(&2) * ((ei:A->real^3)(e'(exp(t / sqrt(&2)) % om)) dot
                         frechet_derivative (ei o e') (at (exp(t / sqrt(&2)) % om))
                           (inv(sqrt(&2)) % exp(t / sqrt(&2)) % om)) /
                       (ei(e'(exp(t / sqrt(&2)) % om)) dot
                        ei(e'(exp(t / sqrt(&2)) % om))) - rho) <= kappa /\
                   (rho - kappa) * (tau - t) <=
                   inv eps - apx_sval(ei(e'(exp(t / sqrt(&2)) % om))) /\
                   inv eps - apx_sval(ei(e'(exp(t / sqrt(&2)) % om))) <=
                   (rho + kappa) * (tau - t))`
  MP_TAC THENL
   [X_GEN_TAC `om:real^3` THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC APX_RAY_OVERLAP THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `--(&3 * inv eps / &4)` THEN
    CONJ_TAC THENL [UNDISCH_TAC `&0 < inv eps` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [UNDISCH_TAC `&0 < inv eps` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "q'" MATCH_MP_TAC THEN ASM_SIMP_TAC[APX_RAY_IN_DOM; APX_RAY_SVAL] THEN
    MP_TAC(SPEC `eps:real` APX_INV2) THEN UNDISCH_TAC `&0 < inv eps` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `tau:real^3->real` (LABEL_TAC "ray")) THEN
  SUBGOAL_THEN
   `!om t. norm om = &1 /\ --inv eps < t /\ t < tau om
           ==> abs(apx_sval((ei:A->real^3)((e':real^3->A)(exp(t / sqrt(&2)) % om))) - t -
                   (inv eps - tau om)) <= A * (tau om - t)`
  (LABEL_TAC "est") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "ray" (fun th -> MP_TAC(MP (SPEC `om:real^3` th) (ASSUME `norm(om:real^3) = &1`))) THEN
    DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT2) THEN
    MP_TAC(ISPECL [`tau(om:real^3) - t`;
                   `inv eps - apx_sval((ei:A->real^3)((e':real^3->A)(exp(t / sqrt(&2)) % om)))`;
                   `rho:real`; `kappa:real`] APX_PAIR_ARITH1) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "A" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!om:real^3. norm om = &1
                            ==> --inv(&2 * eps) <= tau om /\ tau om <= inv(&2 * eps)`
  (LABEL_TAC "taurange") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "ray" (fun th -> MP_TAC(MP (SPEC `om:real^3` th) (ASSUME `norm(om:real^3) = &1`))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `~(x < a) ==> a <= x`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(tau(om:real^3) + --inv(&2 * eps)) / &2` o check (fun th ->
      is_forall(concl th) && is_iff(snd(dest_forall(concl th))))) THEN
    MATCH_MP_TAC(TAUT `p /\ ~q ==> (p <=> q) ==> F`) THEN CONJ_TAC THENL
     [MP_TAC(SPEC `eps:real` APX_INV2) THEN DISCH_TAC THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "q'" MATCH_MP_TAC THEN ASM_SIMP_TAC[APX_RAY_IN_DOM; APX_RAY_SVAL] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(ei:A->real^3) o (e':real^3->A)`;
                 `{v:real^3 | v IN rfs_neck_dom eps /\
                              (e':real^3->A) v IN IMAGE (e:real^3->A) (rfs_neck_dom eps)}`;
                 `exp(--(&3 * inv eps / &4) / sqrt(&2))`; `kappa:real`; `rho:real`] APX_SPHERE_VARIATION) THEN
  REWRITE_TAC[o_THM; IN_ELIM_THM] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_EXP_POS_LT];
      ASM_REWRITE_TAC[];
      X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(v:real^3 = vec 0) /\ apx_sval v = --(&3 * inv eps / &4)` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [DISCH_TAC THEN UNDISCH_TAC `norm(v:real^3) = exp(--(&3 * inv eps / &4) / sqrt(&2))` THEN
          ASM_REWRITE_TAC[NORM_0] THEN MP_TAC(SPEC `--(&3 * inv eps / &4) / sqrt(&2)` REAL_EXP_POS_LT) THEN
          REAL_ARITH_TAC;
          ASM_REWRITE_TAC[apx_sval; LOG_EXP] THEN
          SUBGOAL_THEN `~(sqrt(&2) = &0)` MP_TAC THENL
           [SIMP_TAC[SQRT_EQ_0; REAL_POS] THEN REAL_ARITH_TAC; CONV_TAC REAL_FIELD]];
        ALL_TAC] THEN
      SUBGOAL_THEN `(v:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN
        UNDISCH_TAC `&0 < inv eps` THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "q'" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `eps:real` APX_INV2) THEN
      UNDISCH_TAC `&0 < inv eps` THEN REAL_ARITH_TAC;
      X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
        EXISTS_TAC `{v:real^3 | v IN rfs_neck_dom eps /\
                      (e':real^3->A) v IN IMAGE (e:real^3->A) (rfs_neck_dom eps)}` THEN
        ASM_REWRITE_TAC[IN_ELIM_THM];
        USE_THEN "tr" (MP_TAC o SPEC `v:real^3`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        MESON_TAC[APX_SVAL_NECK_DOM]];
      USE_THEN "align" ACCEPT_TAC];
    DISCH_THEN(LABEL_TAC "var")] THEN
  SUBGOAL_THEN `norm(basis 1:real^3) = &1` ASSUME_TAC THENL
   [SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!om:real^3. norm om = &1
                ==> abs(tau om - tau(basis 1:real^3)) <=
                    A * (&5 * inv eps / &2) + sqrt(&2) * pi * kappa`
  (LABEL_TAC "tdiff") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "taurange" (fun th -> MP_TAC(MP (SPEC `om:real^3` th)
      (ASSUME `norm(om:real^3) = &1`))) THEN
    USE_THEN "taurange" (fun th -> MP_TAC(MP (SPEC `basis 1:real^3` th)
      (ASSUME `norm(basis 1:real^3) = &1`))) THEN
    MP_TAC(SPEC `eps:real` APX_INV2) THEN REPEAT DISCH_TAC THEN
    USE_THEN "est" (MP_TAC o SPECL [`om:real^3`; `--(&3 * inv eps / &4)`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    USE_THEN "est" (MP_TAC o SPECL [`basis 1:real^3`; `--(&3 * inv eps / &4)`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    USE_THEN "var" (MP_TAC o SPECL [`basis 1:real^3`; `om:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN `A * (tau(om:real^3) - --(&3 * inv eps / &4)) <= A * (&5 * inv eps / &4) /\
                  A * (tau(basis 1:real^3) - --(&3 * inv eps / &4)) <= A * (&5 * inv eps / &4)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `inv eps - tau(basis 1:real^3)` THEN
  USE_THEN "taurange" (fun th -> MP_TAC(MP (SPEC `basis 1:real^3` th)
    (ASSUME `norm(basis 1:real^3) = &1`))) THEN
  MP_TAC(SPEC `eps:real` APX_INV2) THEN REPEAT DISCH_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`eps:real`; `v:real^3`] APX_SVAL_NECK_DOM) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPEC `v:real^3` APX_POLAR) THEN ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `om = inv(norm v) % (v:real^3)` THEN
    ABBREV_TAC `t = apx_sval(v:real^3)` THEN STRIP_TAC THEN
    SUBGOAL_THEN `--inv eps < t /\ t < tau(om:real^3)` STRIP_ASSUME_TAC THENL
     [USE_THEN "ray" (fun th -> MP_TAC(MP (SPEC `om:real^3` th)
        (ASSUME `norm(om:real^3) = &1`))) THEN
      DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "est" (MP_TAC o SPECL [`om:real^3`; `t:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]] THEN DISCH_TAC THEN
    USE_THEN "tdiff" (fun th -> MP_TAC(MP (SPEC `om:real^3` th)
      (ASSUME `norm(om:real^3) = &1`))) THEN DISCH_TAC THEN
    USE_THEN "taurange" (fun th -> MP_TAC(MP (SPEC `om:real^3` th)
      (ASSUME `norm(om:real^3) = &1`))) THEN DISCH_TAC THEN
    SUBGOAL_THEN `A * (tau(om:real^3) - t) <= A * (&3 * inv eps / &2) /\
                  A * (&5 * inv eps / &2) + A * (&3 * inv eps / &2) = A * &4 * inv eps`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`eps:real`; `v:real^3`] APX_SVAL_NECK_DOM) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPEC `v:real^3` APX_POLAR) THEN ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `om = inv(norm v) % (v:real^3)` THEN
    ABBREV_TAC `t = apx_sval(v:real^3)` THEN STRIP_TAC THEN
    USE_THEN "tdiff" (fun th -> MP_TAC(MP (SPEC `om:real^3` th)
      (ASSUME `norm(om:real^3) = &1`))) THEN DISCH_TAC THEN
    SUBGOAL_THEN `A * (&5 * inv eps / &2) <= A * &4 * inv eps` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "ray" (fun th -> MP_TAC(MP (SPEC `om:real^3` th)
      (ASSUME `norm(om:real^3) = &1`))) THEN
    DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o snd o EQ_IMP_RULE) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`eps:real`; `v:real^3`] APX_SVAL_NECK_DOM) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    USE_THEN "align" (MP_TAC o SPEC `v:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `sg:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "al"))) THEN
    SUBGOAL_THEN `sg = &1` SUBST_ALL_TAC THENL
     [MP_TAC(SPEC `v:real^3` APX_POLAR) THEN ASM_REWRITE_TAC[] THEN
      ABBREV_TAC `om = inv(norm v) % (v:real^3)` THEN
      ABBREV_TAC `t = apx_sval(v:real^3)` THEN STRIP_TAC THEN
      SUBGOAL_THEN `--inv eps < t /\ t < tau(om:real^3)` STRIP_ASSUME_TAC THENL
       [USE_THEN "ray" (fun th -> MP_TAC(MP (SPEC `om:real^3` th)
          (ASSUME `norm(om:real^3) = &1`))) THEN
        DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      USE_THEN "ray" (fun th -> MP_TAC(MP (SPEC `om:real^3` th)
        (ASSUME `norm(om:real^3) = &1`))) THEN
      DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
      USE_THEN "al" (MP_TAC o SPEC `inv(sqrt(&2)) % (v:real^3)`) THEN
      REWRITE_TAC[MP (SPEC `v:real^3` APX_RAY_UNIT_FACTS) (ASSUME `~(v:real^3 = vec 0)`);
                  SQRT_1; REAL_MUL_RID] THEN
      DISJ_CASES_THEN SUBST1_TAC (ASSUME `sg = &1 \/ sg = -- &1`) THEN
      UNDISCH_TAC `kappa < rho` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "al" MP_TAC THEN REWRITE_TAC[REAL_MUL_LID]]);;

(* ------------------------------------------------------------------------- *)
(* E2 for two consecutive necks of a chain (clause (1) of                    *)
(* apx_chain for the pair), with the constants of N1: rho = sqrt(R/R'),       *)
(* kappa = 7 sqrt(alpha1), and d0 <= 80 sqrt(alpha1) / eps.                  *)
(* ------------------------------------------------------------------------- *)

let APX_SQRT2_PI = prove
 (`sqrt(&2) * pi <= &24 / &5`,
  SUBGOAL_THEN `sqrt(&2) <= &3 / &2 /\ pi <= &16 / &5` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      MP_TAC PI_APPROX_32 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 / &2 * &16 / &5` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_POS; PI_POS_LE];
    REAL_ARITH_TAC]);;

let APX_SQRT_DEV = prove
 (`!r. &0 <= r ==> abs(sqrt r - &1) <= abs(r - &1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `r - &1 = (sqrt r - &1) * (sqrt r + &1)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[REAL_ARITH `(s - &1) * (s + &1) = s pow 2 - &1`; SQRT_POW_2]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[REAL_ABS_POS] THEN MP_TAC(SPEC `r:real` SQRT_POS_LE) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let APX_SLAB_SUB_DOM = prove
 (`!a b eps. --inv eps <= a /\ b <= inv eps ==> apx_slab a b SUBSET rfs_neck_dom eps`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[SUBSET; APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[]]);;

let APX_QUARTERS_SUB_DOM = prove
 (`!eps. &0 < eps
         ==> apx_slab (--inv eps) (--inv(&2 * eps)) SUBSET rfs_neck_dom eps /\
             apx_slab (inv(&2 * eps)) (inv eps) SUBSET rfs_neck_dom eps /\
             apx_slab (--inv(&2 * eps)) (inv eps) SUBSET rfs_neck_dom eps /\
             apx_slab (--inv eps) (inv(&2 * eps)) SUBSET rfs_neck_dom eps`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < inv eps` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC APX_SLAB_SUB_DOM THEN
  MP_TAC(SPEC `eps:real` APX_INV2) THEN UNDISCH_TAC `&0 < inv eps` THEN REAL_ARITH_TAC);;

(* The one-sided clauses of E2 from clause (1) of a chain for the pair. *)

let APX_CHAIN_CLAUSE1_SIDES = prove
 (`!(e:real^3->A) e' eps.
        &0 < eps /\
        (!u v. u IN rfs_neck_dom eps /\ v IN rfs_neck_dom eps /\ e u = e v ==> u = v) /\
        (!u v. u IN rfs_neck_dom eps /\ v IN rfs_neck_dom eps /\ e' u = e' v ==> u = v) /\
        IMAGE e (apx_slab (inv(&2 * eps)) (inv eps)) UNION
        IMAGE e' (apx_slab (--inv eps) (--inv(&2 * eps)))
        SUBSET IMAGE e (rfs_neck_dom eps) INTER IMAGE e' (rfs_neck_dom eps) /\
        IMAGE e (rfs_neck_dom eps) INTER IMAGE e' (rfs_neck_dom eps)
        SUBSET IMAGE e (apx_slab (--inv(&2 * eps)) (inv eps)) INTER
               IMAGE e' (apx_slab (--inv eps) (inv(&2 * eps)))
        ==> IMAGE e' (apx_slab (--inv eps) (--inv(&2 * eps))) SUBSET
            IMAGE e (rfs_neck_dom eps) /\
            DISJOINT (IMAGE e' (rfs_neck_dom eps))
                     (IMAGE e (apx_slab (--inv eps) (--inv(&2 * eps)))) /\
            DISJOINT (IMAGE e (rfs_neck_dom eps))
                     (IMAGE e' (apx_slab (inv(&2 * eps)) (inv eps)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < inv eps` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    X_GEN_TAC `p:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(y:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
     [MP_TAC(SPEC `eps:real` APX_QUARTERS_SUB_DOM) THEN ASM_REWRITE_TAC[SUBSET] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(p:A) IN IMAGE (e:real^3->A) (apx_slab (--inv(&2 * eps)) (inv eps))`
    MP_TAC THENL
     [UNDISCH_TAC `IMAGE (e:real^3->A) (rfs_neck_dom eps) INTER
                   IMAGE (e':real^3->A) (rfs_neck_dom eps)
                   SUBSET IMAGE e (apx_slab (--inv(&2 * eps)) (inv eps)) INTER
                          IMAGE e' (apx_slab (--inv eps) (inv(&2 * eps)))` THEN
      REWRITE_TAC[SUBSET; IN_INTER] THEN DISCH_THEN(MP_TAC o SPEC `p:A`) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[FUN_IN_IMAGE]; SIMP_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(z:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
     [MP_TAC(SPEC `eps:real` APX_QUARTERS_SUB_DOM) THEN ASM_REWRITE_TAC[SUBSET] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `y:real^3 = z` SUBST_ALL_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(z:real^3) IN apx_slab (--inv eps) (--inv(&2 * eps))` THEN
    UNDISCH_TAC `(z:real^3) IN apx_slab (--inv(&2 * eps)) (inv eps)` THEN
    REWRITE_TAC[APX_SLAB_SVAL] THEN REAL_ARITH_TAC;
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    X_GEN_TAC `p:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(y:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
     [MP_TAC(SPEC `eps:real` APX_QUARTERS_SUB_DOM) THEN ASM_REWRITE_TAC[SUBSET] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(p:A) IN IMAGE (e':real^3->A) (apx_slab (--inv eps) (inv(&2 * eps)))`
    MP_TAC THENL
     [UNDISCH_TAC `IMAGE (e:real^3->A) (rfs_neck_dom eps) INTER
                   IMAGE (e':real^3->A) (rfs_neck_dom eps)
                   SUBSET IMAGE e (apx_slab (--inv(&2 * eps)) (inv eps)) INTER
                          IMAGE e' (apx_slab (--inv eps) (inv(&2 * eps)))` THEN
      REWRITE_TAC[SUBSET; IN_INTER] THEN DISCH_THEN(MP_TAC o SPEC `p:A`) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[FUN_IN_IMAGE]; SIMP_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(z:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
     [MP_TAC(SPEC `eps:real` APX_QUARTERS_SUB_DOM) THEN ASM_REWRITE_TAC[SUBSET] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `y:real^3 = z` SUBST_ALL_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(z:real^3) IN apx_slab (inv(&2 * eps)) (inv eps)` THEN
    UNDISCH_TAC `(z:real^3) IN apx_slab (--inv eps) (inv(&2 * eps))` THEN
    REWRITE_TAC[APX_SLAB_SVAL] THEN REAL_ARITH_TAC]);;

let APX_D0_BOUND = prove
 (`!alpha1 eps rho kappa.
        &0 < alpha1 /\ alpha1 <= &1 / &4096 /\ &0 < eps /\ &1 <= inv eps /\
        abs(rho - &1) <= &4 * alpha1 /\ kappa = &7 * sqrt alpha1
        ==> (abs(rho - &1) + kappa) * (&4 * inv eps) + sqrt(&2) * pi * kappa <=
            &80 * sqrt alpha1 * inv eps`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= sqrt alpha1 /\ sqrt alpha1 <= &1 / &64` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `alpha1 <= sqrt alpha1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT THEN REWRITE_TAC[REAL_POW_2] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(abs(rho - &1) + kappa) * (&4 * inv eps) <=
                (&11 * sqrt alpha1) * (&4 * inv eps)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&2) * pi * kappa <= &24 / &5 * kappa` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[APX_SQRT2_PI] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt alpha1 <= sqrt alpha1 * inv eps` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let APX_CHAIN_PAIR_STRUCT = prove
 (`!alpha1 eps1.
     &0 < alpha1 /\ alpha1 <= &1 / &4096 /\ &0 < eps1 /\ eps1 <= alpha1 /\
     (!top atlas (g:A->real^3^3) eps x (e:real^3->A) y.
        &0 < eps /\ eps <= eps1 /\ riemannian_metric atlas g /\
        rfs_neck (top,atlas) g eps x e /\ y IN rfs_neck_dom eps
        ==> abs(lscalar (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y - &1)
            <= alpha1 /\
            (!w. abs(lricci (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y w w -
                     lricci (cylinder_flow (&0)) y w w)
                 <= alpha1 * (w dot (cylinder_flow (&0) y ** w))))
     ==> !top atlas (g:A->real^3^3) eps x (e:real^3->A) x' e' (ei:A->real^3).
           &0 < eps /\ eps <= eps1 /\ hausdorff_space top /\ riemannian_metric atlas g /\
           rfs_neck (top,atlas) g eps x e /\ rfs_neck (top,atlas) g eps x' e' /\
           (!z. z IN rfs_neck_dom eps ==> ei(e z) = z) /\
           IMAGE e (apx_slab (inv(&2 * eps)) (inv eps)) UNION
           IMAGE e' (apx_slab (--inv eps) (--inv(&2 * eps)))
           SUBSET IMAGE e (rfs_neck_dom eps) INTER IMAGE e' (rfs_neck_dom eps) /\
           IMAGE e (rfs_neck_dom eps) INTER IMAGE e' (rfs_neck_dom eps)
           SUBSET IMAGE e (apx_slab (--inv(&2 * eps)) (inv eps)) INTER
                  IMAGE e' (apx_slab (--inv eps) (inv(&2 * eps)))
           ==> abs(mfd_scalar atlas g x / mfd_scalar atlas g x' - &1) <= &4 * alpha1 /\
               ?Delta.
                 inv(&2 * eps) <= Delta /\ Delta <= &3 * inv(&2 * eps) /\
                 (!v. v IN rfs_neck_dom eps /\ e' v IN IMAGE e (rfs_neck_dom eps)
                      ==> abs(apx_sval(ei(e' v)) - apx_sval v - Delta) <=
                          &80 * sqrt alpha1 * inv eps) /\
                 (!v. v IN rfs_neck_dom eps /\
                      apx_sval v < inv eps - Delta - &80 * sqrt alpha1 * inv eps
                      ==> e' v IN IMAGE e (rfs_neck_dom eps)) /\
                 (!v. v IN rfs_neck_dom eps /\ e' v IN IMAGE e (rfs_neck_dom eps)
                      ==> !k. abs(sqrt(&2) *
                                  (ei(e' v) dot frechet_derivative (ei o e') (at v) k) /
                                  (ei(e' v) dot ei(e' v)) -
                                  sqrt(mfd_scalar atlas g x / mfd_scalar atlas g x') *
                                  sqrt(&2) * (v dot k) / (v dot v))
                              <= (&7 * sqrt alpha1) *
                                 sqrt(k dot (cylinder_flow (&0) v ** k)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`alpha1:real`; `eps1:real`] APX_TRANSITION_DERIV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "td") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
                mfd_param top atlas (rfs_neck_dom eps) (e:real^3->A) /\
                mfd_param top atlas (rfs_neck_dom eps) (e':real^3->A)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!u v. u IN rfs_neck_dom eps /\ v IN rfs_neck_dom eps /\ (e:real^3->A) u = e v
           ==> u = v) /\
    (!u v. u IN rfs_neck_dom eps /\ v IN rfs_neck_dom eps /\ (e':real^3->A) u = e' v
           ==> u = v)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT STRIP_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `rfs_neck_dom eps`; `e:real^3->A`] GRGD_PARAM_FACTS);
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `rfs_neck_dom eps`; `e':real^3->A`] GRGD_PARAM_FACTS)] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`e:real^3->A`; `e':real^3->A`; `eps:real`] APX_CHAIN_CLAUSE1_SIDES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 < inv eps /\ &1 <= inv eps` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV] THEN
    SUBGOAL_THEN `inv eps = &1 / eps` SUBST1_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_LID]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `v0 = exp(--(&3 * inv eps / &4) / sqrt(&2)) % (basis 1:real^3)` THEN
  SUBGOAL_THEN `(v0:real^3) IN rfs_neck_dom eps /\
                (e':real^3->A) v0 IN IMAGE (e:real^3->A) (rfs_neck_dom eps)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(v0:real^3) IN apx_slab (--inv eps) (--inv(&2 * eps))` ASSUME_TAC THENL
     [EXPAND_TAC "v0" THEN SIMP_TAC[APX_RAY_IN_SLAB; NORM_BASIS; DIMINDEX_3; ARITH] THEN
      MP_TAC(SPEC `eps:real` APX_INV2) THEN UNDISCH_TAC `&0 < inv eps` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(SPEC `eps:real` APX_QUARTERS_SUB_DOM) THEN ASM_REWRITE_TAC[SUBSET] THEN
      ASM_MESON_TAC[];
      UNDISCH_TAC `IMAGE (e':real^3->A) (apx_slab (--inv eps) (--inv (&2 * eps))) SUBSET
                   IMAGE (e:real^3->A) (rfs_neck_dom eps)` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(mfd_scalar atlas (g:A->real^3^3) x / mfd_scalar atlas g x' - &1)
                <= &4 * alpha1` ASSUME_TAC THENL
   [USE_THEN "td" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `x':A`; `e':real^3->A`;
      `ei:A->real^3`; `v0:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `rho = sqrt(mfd_scalar atlas (g:A->real^3^3) x / mfd_scalar atlas g x')` THEN
  SUBGOAL_THEN `abs(rho - &1) <= &4 * alpha1 /\ &1 / &2 <= rho` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `abs(mfd_scalar atlas (g:A->real^3^3) x / mfd_scalar atlas g x' - &1)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC APX_SQRT_DEV THEN ASM_REAL_ARITH_TAC;
        FIRST_ASSUM ACCEPT_TAC];
      MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &7 * sqrt alpha1 /\ &7 * sqrt alpha1 < rho` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE; REAL_POS];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&1 / &2` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `sqrt alpha1 <= &1 / &64` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `e:real^3->A`;
                 `e':real^3->A`; `ei:A->real^3`; `eps:real`; `rho:real`;
                 `&7 * sqrt alpha1`] APX_PAIR_STRUCT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN
    USE_THEN "td" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `x':A`; `e':real^3->A`;
      `ei:A->real^3`; `v:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[REAL_MUL_ASSOC];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `Delta:real` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`alpha1:real`; `eps:real`; `rho:real`; `&7 * sqrt alpha1`] APX_D0_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(abs(rho - &1) + &7 * sqrt alpha1) * (&4 * inv eps) +
                sqrt(&2) * pi * &7 * sqrt alpha1` THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* E2 (ii), the forward inclusion in the coordinates of N:                   *)
(* points of N above Delta - 1/eps + d0 lie in N'.  The set of such points   *)
(* of a slightly smaller slab that lie in N' is open and (by the estimate of *)
(* E2 and compactness of a sub-annulus of N') closed; the slab is connected  *)
(* and meets N' in its positive quarter.                                     *)
(* ------------------------------------------------------------------------- *)

let APX_PAIR_FORWARD = prove
 (`!top atlas (e:real^3->A) e' (ei:A->real^3) eps Delta d0.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ &0 < eps /\
        mfd_param top atlas (rfs_neck_dom eps) e /\
        mfd_param top atlas (rfs_neck_dom eps) e' /\
        (!z. z IN rfs_neck_dom eps ==> ei(e z) = z) /\
        &0 <= d0 /\ d0 < inv(&2 * eps) /\ inv(&2 * eps) <= Delta /\
        Delta <= &3 * inv(&2 * eps) /\
        IMAGE e (apx_slab (inv(&2 * eps)) (inv eps)) SUBSET IMAGE e' (rfs_neck_dom eps) /\
        (!v. v IN rfs_neck_dom eps /\ e' v IN IMAGE e (rfs_neck_dom eps)
             ==> abs(apx_sval(ei(e' v)) - apx_sval v - Delta) <= d0)
        ==> !y. y IN rfs_neck_dom eps /\ Delta - inv eps + d0 < apx_sval y
                ==> e y IN IMAGE e' (rfs_neck_dom eps)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "q") (LABEL_TAC "c1")))))))))))) THEN
  X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  MP_TAC(SPEC `eps:real` APX_INV2) THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < inv eps` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
  ABBREV_TAC `mu = min ((apx_sval y - (Delta - inv eps + d0)) / &2)
                       ((inv(&2 * eps) - d0) / &2)` THEN
  SUBGOAL_THEN `&0 < mu /\ mu <= (apx_sval y - (Delta - inv eps + d0)) / &2 /\
                mu <= (inv(&2 * eps) - d0) / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "mu" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `m = inv eps - min mu (Delta - d0)` THEN
  SUBGOAL_THEN `m < inv eps /\ --m <= --inv eps + mu /\ inv eps - Delta + d0 <= m`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "m" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`eps:real`; `m:real`] APX_SUBSLAB) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `K = cball(vec 0:real^3,exp(m / sqrt(&2))) DIFF ball(vec 0,exp(--m / sqrt(&2)))` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `e:real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e0:A->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `e':real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e1:A->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `closed_in top (IMAGE (e':real^3->A) K)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean (rfs_neck_dom eps)` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN];
    ALL_TAC] THEN
  ABBREV_TAC `V = apx_slab (Delta - inv eps + d0 + mu) (inv eps)` THEN
  SUBGOAL_THEN `(V:real^3->bool) SUBSET rfs_neck_dom eps` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN MATCH_MP_TAC APX_SLAB_SUB_DOM THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (subtopology euclidean V,top) (e:real^3->A)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
    EXISTS_TAC `rfs_neck_dom eps` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{z | z IN V /\ (e:real^3->A) z IN IMAGE (e':real^3->A) (rfs_neck_dom eps)} =
    {z | z IN V /\ e z IN IMAGE e' K}`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN
    ASM_CASES_TAC `(z:real^3) IN V` THEN ASM_REWRITE_TAC[] THEN EQ_TAC THENL
     [REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `v:real^3` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(z:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      USE_THEN "c1" (MP_TAC o SPEC `v:real^3`) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(e:real^3->A) z = (e':real^3->A) v` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `(e:real^3->A) z = (e':real^3->A) v` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC[] THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      CONJ_TAC THENL [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
      UNDISCH_TAC `(z:real^3) IN V` THEN EXPAND_TAC "V" THEN
      REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `(K:real^3->bool) SUBSET rfs_neck_dom eps` THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `V:real^3->bool` CONNECTED_CLOPEN) THEN
  SUBGOAL_THEN `connected(V:real^3->bool)` (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "V" THEN REWRITE_TAC[apx_slab; APX_CONNECTED_ANNULUS3]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC
    `{z | z IN V /\ (e:real^3->A) z IN IMAGE (e':real^3->A) (rfs_neck_dom eps)}`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`e:real^3->A`; `subtopology euclidean (V:real^3->bool)`; `top:A topology`;
                     `IMAGE (e':real^3->A) (rfs_neck_dom eps)`]
                    OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
      ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`e:real^3->A`; `subtopology euclidean (V:real^3->bool)`; `top:A topology`;
                     `IMAGE (e':real^3->A) K`] CLOSED_IN_CONTINUOUS_MAP_PREIMAGE) THEN
      ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]];
    ALL_TAC] THEN
  ABBREV_TAC `s0 = (max (Delta - inv eps + d0 + mu) (inv(&2 * eps)) + inv eps) / &2` THEN
  SUBGOAL_THEN `Delta - inv eps + d0 + mu < s0 /\ inv(&2 * eps) < s0 /\ s0 < inv eps`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "s0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `norm(basis 1:real^3) = &1` ASSUME_TAC THENL
   [SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
   [REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `exp(s0 / sqrt(&2)) % basis 1:real^3`) THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN CONJ_TAC THENL
     [EXPAND_TAC "V" THEN ASM_SIMP_TAC[APX_RAY_IN_SLAB] THEN ASM_REAL_ARITH_TAC;
      USE_THEN "q" (MATCH_MP_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]) THEN
      ASM_SIMP_TAC[APX_RAY_IN_SLAB] THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN
    MATCH_MP_TAC(TAUT `q ==> (p /\ r <=> q) ==> r`) THEN
    EXPAND_TAC "V" THEN REWRITE_TAC[APX_SLAB_SVAL] THEN
    MP_TAC(SPECL [`eps:real`; `y:real^3`] APX_SVAL_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Tubes under construction.  apx_eng_tube: a parametrization E              *)
(* of the slab (-1/eps, L + 1/eps), equal to e0 near the bottom and to the   *)
(* neck en (up to a sphere diffeomorphism and the shift of s by L) near the  *)
(* top (the conclusion of A13 without the image and tube clauses).          *)
(* ------------------------------------------------------------------------- *)

let apx_eng_tube = new_definition
 `apx_eng_tube (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) (eps:real)
               (e0:real^3->A) (en:real^3->A) (E:real^3->A) (L:real) <=>
    &0 <= L /\
    mfd_param top atlas (apx_slab (--inv eps) (L + inv eps)) E /\
    (!y. y IN apx_slab (--inv eps) (inv(&8 * eps)) ==> E y = e0 y) /\
    ?f f'. sphere_diffeo f f' /\
           !y. y IN apx_slab (L - inv(&8 * eps)) (L + inv eps)
               ==> E y = en(radial_ext f (exp(--L / sqrt(&2)) % y))`;;

let APX_SVAL_EXP_SCALE = prove
 (`!L v:real^3. ~(v = vec 0) ==> apx_sval(exp(L / sqrt(&2)) % v) = L + apx_sval v`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[APX_SVAL_SCALE; REAL_EXP_POS_LT; LOG_EXP] THEN
  SUBGOAL_THEN `~(sqrt(&2) = &0)` MP_TAC THENL
   [SIMP_TAC[SQRT_EQ_0; REAL_POS] THEN REAL_ARITH_TAC; CONV_TAC REAL_FIELD]);;

(* Points of the top part of en are E-images of the shifted level. *)

let APX_TUBE_TOP = prove
 (`!top atlas eps (e0:real^3->A) en E L.
        &0 < eps /\ apx_eng_tube top atlas eps e0 en E L
        ==> !z. z IN rfs_neck_dom eps /\ --inv(&8 * eps) < apx_sval z
                ==> ?y. y IN apx_slab (L - inv(&8 * eps)) (L + inv eps) /\
                        apx_sval y = L + apx_sval z /\ E y = en z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[apx_eng_tube] THEN STRIP_TAC THEN
  X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`eps:real`; `z:real^3`] APX_SVAL_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `sphere_diffeo (f:real^3->real^3) f'` THEN REWRITE_TAC[sphere_diffeo] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `norm(radial_ext (f':real^3->real^3) z) = norm z /\
                radial_ext f (radial_ext f' z) = z` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SMT_RADIAL_EXT_NORM THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC SMT_RADIAL_EXT_INVERSE THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(radial_ext (f':real^3->real^3) z = vec 0) /\
                apx_sval(radial_ext (f':real^3->real^3) z) = apx_sval z`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM NORM_EQ_0; apx_sval] THEN ASM_REWRITE_TAC[NORM_EQ_0];
    ALL_TAC] THEN
  EXISTS_TAC `exp(L / sqrt(&2)) % radial_ext (f':real^3->real^3) z` THEN
  SUBGOAL_THEN `apx_sval(exp(L / sqrt(&2)) % radial_ext (f':real^3->real^3) z) =
                L + apx_sval z` ASSUME_TAC THENL
   [ASM_SIMP_TAC[APX_SVAL_EXP_SCALE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REWRITE_TAC[VECTOR_MUL_EQ_0] THEN
    REWRITE_TAC[REAL_EXP_NZ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(L / sqrt(&2)) % radial_ext (f':real^3->real^3) z IN
                apx_slab (L - inv(&8 * eps)) (L + inv eps)` ASSUME_TAC THENL
   [REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REWRITE_TAC[VECTOR_MUL_EQ_0] THEN
    REWRITE_TAC[REAL_EXP_NZ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; GSYM REAL_EXP_ADD] THEN
  REWRITE_TAC[real_div; REAL_MUL_LNEG; REAL_ADD_LINV; REAL_EXP_0; VECTOR_MUL_LID] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* No triple overlaps.  If T is a tube under construction                    *)
(* whose top part is the neck en, and N' = e'(D) is consecutive to en, then  *)
(* every neck N_j inside T meets N' only inside en(D): along a radial line   *)
(* of N' the N_j-overlap starts at -1/eps; if it reached the exit tau of the *)
(* en-overlap, the exit point would lie in T where the tube coordinate      *)
(* sval o E^-1 would have to reach L + 1/eps.                                *)
(* ------------------------------------------------------------------------- *)

let apx_eng_align = new_definition
 `apx_eng_align (eps:real) (e:real^3->A) (ei:A->real^3) (e':real^3->A)
                (rho:real) (kappa:real) <=>
    &0 <= kappa /\ kappa < rho /\
    !v. v IN rfs_neck_dom eps /\ e' v IN IMAGE e (rfs_neck_dom eps)
        ==> ?sg. (sg = &1 \/ sg = -- &1) /\
                 !k. abs(sqrt(&2) * (ei(e' v) dot frechet_derivative (ei o e') (at v) k) /
                         (ei(e' v) dot ei(e' v)) -
                         sg * rho * sqrt(&2) * (v dot k) / (v dot v))
                     <= kappa * sqrt(k dot (cylinder_flow (&0) v ** k))`;;

let apx_eng_sides = new_definition
 `apx_eng_sides (eps:real) (e:real^3->A) (e':real^3->A) <=>
    DISJOINT (IMAGE e' (rfs_neck_dom eps))
             (IMAGE e (apx_slab (--inv eps) (--inv(&2 * eps)))) /\
    DISJOINT (IMAGE e (rfs_neck_dom eps))
             (IMAGE e' (apx_slab (inv(&2 * eps)) (inv eps)))`;;

let APX_NO_TRIPLE = prove
 (`!top atlas eps (e0:real^3->A) en E L e' (ein:A->real^3) ej (eij:A->real^3)
    rhon kappan rho kappa.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ &0 < eps /\
        apx_eng_tube top atlas eps e0 en E L /\
        mfd_param top atlas (rfs_neck_dom eps) en /\
        (!z. z IN rfs_neck_dom eps ==> ein(en z) = z) /\
        mfd_param top atlas (rfs_neck_dom eps) e' /\
        mfd_param top atlas (rfs_neck_dom eps) ej /\
        (!z. z IN rfs_neck_dom eps ==> eij(ej z) = z) /\
        IMAGE ej (rfs_neck_dom eps) SUBSET IMAGE E (apx_slab (--inv eps) (L + inv eps)) /\
        apx_eng_align eps en ein e' rhon kappan /\ apx_eng_align eps ej eij e' rho kappa /\
        IMAGE e' (apx_slab (--inv eps) (--inv(&2 * eps))) SUBSET
        IMAGE en (rfs_neck_dom eps) /\
        apx_eng_sides eps en e' /\ apx_eng_sides eps ej e'
        ==> IMAGE e' (rfs_neck_dom eps) INTER IMAGE ej (rfs_neck_dom eps) SUBSET
            IMAGE en (rfs_neck_dom eps)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[apx_eng_align; apx_eng_sides] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "tube")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "jT")
    (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
                      (LABEL_TAC "aln")))
    (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
                      (LABEL_TAC "alj")))
    (CONJUNCTS_THEN2 (LABEL_TAC "h1")
    (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (LABEL_TAC "h2n") (LABEL_TAC "h3n"))
                     (CONJUNCTS_THEN2 (LABEL_TAC "h2j") (LABEL_TAC "h3j")))))))))))))))) THEN
  SUBGOAL_THEN `&0 < inv eps` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
  MP_TAC(SPEC `eps:real` APX_INV2) THEN DISCH_TAC THEN
  REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `p:A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`eps:real`; `v:real^3`] APX_SVAL_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(SPEC `v:real^3` APX_POLAR) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `om = inv(norm v) % (v:real^3)` THEN
  ABBREV_TAC `tp = apx_sval(v:real^3)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `--inv eps < tp /\ tp < inv eps /\
                (e':real^3->A) v IN IMAGE (ej:real^3->A) (rfs_neck_dom eps)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  (* the N_j-overlap along the line *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `ej:real^3->A`;
                 `e':real^3->A`; `eij:A->real^3`; `eps:real`; `rho:real`; `kappa:real`;
                 `om:real^3`] APX_RAY_OVERLAP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `tp:real` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tauj:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "Sj") (K ALL_TAC))))) THEN
  SUBGOAL_THEN `tp < tauj` ASSUME_TAC THENL
   [USE_THEN "Sj" (MP_TAC o SPEC `tp:real`) THEN
    REWRITE_TAC[ASSUME `exp(tp / sqrt(&2)) % (om:real^3) = v`] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the en-overlap along the line *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `en:real^3->A`;
                 `e':real^3->A`; `ein:A->real^3`; `eps:real`; `rhon:real`; `kappan:real`;
                 `om:real^3`] APX_RAY_OVERLAP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `--(&3 * inv eps / &4)` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "h1" (MATCH_MP_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE]) THEN
    ASM_SIMP_TAC[APX_RAY_IN_SLAB] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `taun:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "Sn") (LABEL_TAC "bn"))))) THEN
  ASM_CASES_TAC `tp < taun` THENL
   [USE_THEN "Sn" (MP_TAC o SPEC `tp:real`) THEN
    DISCH_THEN(MP_TAC o snd o EQ_IMP_RULE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `exp(tp / sqrt(&2)) % (om:real^3) = v`; IN_IMAGE] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `--inv eps < taun /\ taun < tauj /\ taun < inv eps` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `q = (e':real^3->A)(exp(taun / sqrt(&2)) % om)` THEN
  SUBGOAL_THEN `(q:A) IN IMAGE (ej:real^3->A) (rfs_neck_dom eps)` ASSUME_TAC THENL
   [USE_THEN "Sj" (MP_TAC o SPEC `taun:real`) THEN
    DISCH_THEN(MP_TAC o snd o EQ_IMP_RULE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `(e':real^3->A)(exp(taun / sqrt(&2)) % om) = q`] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?yq. yq IN apx_slab (--inv eps) (L + inv eps) /\ (E:real^3->A) yq = q`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "jT" MP_TAC THEN UNDISCH_TAC `(q:A) IN IMAGE (ej:real^3->A) (rfs_neck_dom eps)` THEN
    REWRITE_TAC[SUBSET; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param top atlas (apx_slab (--inv eps) (L + inv eps)) (E:real^3->A)`
  ASSUME_TAC THENL [ASM_MESON_TAC[apx_eng_tube]; ALL_TAC] THEN
  SUBGOAL_THEN `apx_sval yq < L + inv eps` ASSUME_TAC THENL
   [UNDISCH_TAC `(yq:real^3) IN apx_slab (--inv eps) (L + inv eps)` THEN
    SIMP_TAC[APX_SLAB_SVAL];
    ALL_TAC] THEN
  ABBREV_TAC `mu = min ((L + inv eps - apx_sval yq) / &2) (inv eps / &2)` THEN
  SUBGOAL_THEN `&0 < mu /\ mu <= (L + inv eps - apx_sval yq) / &2 /\ mu <= inv eps / &2`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "mu" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `apx_slab (--inv eps) (L + inv eps - mu) SUBSET
                apx_slab (--inv eps) (L + inv eps)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; APX_SLAB_SVAL] THEN GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (IMAGE (E:real^3->A) (apx_slab (--inv eps) (L + inv eps - mu)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                          `apx_slab (--inv eps) (L + inv eps)`] THEN
    ASM_REWRITE_TAC[apx_slab; OPEN_ANNULUS] THEN ASM_REWRITE_TAC[GSYM apx_slab];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `e':real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e1:A->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `open {w:real^3 | w IN rfs_neck_dom eps /\
                     (e':real^3->A) w IN IMAGE (E:real^3->A) (apx_slab (--inv eps) (L + inv eps - mu))}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`e':real^3->A`; `subtopology euclidean (rfs_neck_dom eps)`; `top:A topology`;
                   `IMAGE (E:real^3->A) (apx_slab (--inv eps) (L + inv eps - mu))`]
                  OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_EQ; APX_NECK_DOM_OPEN];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{w:real^3 | w IN rfs_neck_dom eps /\
                     (e':real^3->A) w IN IMAGE (E:real^3->A) (apx_slab (--inv eps) (L + inv eps - mu))}`;
                 `om:real^3`; `taun:real`] APX_RAY_OPEN_PRE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[APX_RAY_IN_DOM] THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `yq:real^3` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(yq:real^3) IN apx_slab (--inv eps) (L + inv eps)` THEN
    REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < rhon + kappan` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `t = taun - min d (min (mu / (rhon + kappan)) (taun + inv eps)) / &2` THEN
  SUBGOAL_THEN `&0 < mu / (rhon + kappan)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
  SUBGOAL_THEN `--inv eps < t /\ t < taun /\ abs(t - taun) < d /\
                taun - t < mu / (rhon + kappan)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(rhon + kappan) * (taun - t) < mu` ASSUME_TAC THENL
   [UNDISCH_TAC `taun - t < mu / (rhon + kappan)` THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun u -> u = `d:real`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `y1:real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(e':real^3->A)(exp(t / sqrt(&2)) % om) IN IMAGE (en:real^3->A) (rfs_neck_dom eps)`
  MP_TAC THENL
   [USE_THEN "Sn" (MP_TAC o SPEC `t:real`) THEN
    DISCH_THEN(MP_TAC o snd o EQ_IMP_RULE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(ein:A->real^3)((e':real^3->A)(exp(t / sqrt(&2)) % om)) = z` ASSUME_TAC
  THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  USE_THEN "bn" (MP_TAC o SPEC `t:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
  REWRITE_TAC[ASSUME `(ein:A->real^3)((e':real^3->A)(exp(t / sqrt(&2)) % om)) = z`] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                 `e0:real^3->A`; `en:real^3->A`; `E:real^3->A`; `L:real`] APX_TUBE_TOP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN
  SUBGOAL_THEN `&0 < inv(&8 * eps)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y2:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 <= L /\ inv(&8 * eps) <= inv eps` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[apx_eng_tube]; ALL_TAC] THEN
    REWRITE_TAC[REAL_INV_MUL] THEN UNDISCH_TAC `&0 < inv eps` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `y1:real^3 = y2` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_INJ THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `apx_slab (--inv eps) (L + inv eps)`; `E:real^3->A`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `apx_slab (--inv eps) (L + inv eps - mu) SUBSET
                   apx_slab (--inv eps) (L + inv eps)` THEN
      UNDISCH_TAC `(y1:real^3) IN apx_slab (--inv eps) (L + inv eps - mu)` THEN SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(SPECL [`L - inv(&8 * eps)`; `L + inv eps`; `--inv eps`; `L + inv eps`]
                   APX_SLAB_SUBSET) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `(y1:real^3) IN apx_slab (--inv eps) (L + inv eps - mu)` THEN
  ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Smoothness and regularity of real functions on a manifold                 *)
(* in terms of parametrizations: locality of mfd_smooth_on, smoothness on    *)
(* e(O) from smoothness of f o e on O, and regularity at e(y) from a nonzero *)
(* derivative of f o e at y (chain rule through the chart).                  *)
(* ------------------------------------------------------------------------- *)

let APX_MFD_SMOOTH_ON_LOCAL = prove
 (`!top atlas W (f:A->real^K).
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        open_in top W /\
        (!x. x IN W ==> ?w. open_in top w /\ x IN w /\ w SUBSET W /\
                            mfd_smooth_on atlas w f)
        ==> mfd_smooth_on atlas W f`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "loc"))) THEN
  REWRITE_TAC[mfd_smooth_on] THEN X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
    ASM_MESON_TAC[MFDM_CHART];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  USE_THEN "loc" (MP_TAC o SPEC `x:A`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER w)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
    ASM_MESON_TAC[MFDM_CHART];
    ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
  UNDISCH_TAC `mfd_smooth_on (atlas:((A->bool)#(A->real^N))->bool) w (f:A->real^K)` THEN
  REWRITE_TAC[mfd_smooth_on] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let APX_MFD_SMOOTH_ON_PARAM = prove
 (`!top atlas s (e:real^N->A) O (f:A->real^K).
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        mfd_param top atlas s e /\ open O /\ O SUBSET s /\ smooth_map_on O (f o e)
        ==> mfd_smooth_on atlas (IMAGE e O) f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s:real^N->bool`; `e:real^N->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ei:A->real^N` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[mfd_smooth_on] THEN X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `open_in top (IMAGE (e:real^N->A) O)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `s:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER IMAGE (e:real^N->A) O))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
    ASM_MESON_TAC[MFDM_CHART];
    ALL_TAC] THEN
  UNDISCH_TAC `mfd_smooth_map (atlas:((A->bool)#(A->real^N))->bool) (open_set_atlas s)
                 (IMAGE (e:real^N->A) s) (ei:A->real^N)` THEN
  REWRITE_TAC[mfd_smooth_map; open_set_atlas; IN_SING] THEN
  DISCH_THEN(MP_TAC o SPECL [`c:(A->bool)#(A->real^N)`; `(s:real^N->bool,(\x:real^N. x))`]) THEN
  ASM_REWRITE_TAC[FST; SND] THEN DISCH_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `((f:A->real^K) o (e:real^N->A)) o
              ((ei:A->real^N) o chart_inv (c:(A->bool)#(A->real^N)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER; o_THM] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) (SND c x) = x` SUBST1_TAC THENL
     [ASM_MESON_TAC[MFDM_CHART]; ALL_TAC] THEN
    AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `O:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; o_THM] THEN X_GEN_TAC `x:A` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) (SND c x) = x` SUBST1_TAC THENL
     [ASM_MESON_TAC[MFDM_CHART]; ALL_TAC] THEN
    UNDISCH_TAC `(x:A) IN IMAGE (e:real^N->A) O` THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(ei:A->real^N)((e:real^N->A) y) = y` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
  EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N)))
                {x | x IN FST c INTER IMAGE (e:real^N->A) s /\ (ei:A->real^N) x IN s}` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
    STRIP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:A) IN IMAGE (e:real^N->A) O` THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(y:real^N) IN s` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `(\x:real^N. x) o (ei:A->real^N) o chart_inv (c:(A->bool)#(A->real^N))` THEN
    ASM_REWRITE_TAC[o_THM]]);;

let APX_MFD_REGULAR_AT_PARAM = prove
 (`!top atlas s (e:real^N->A) W (f:A->real) c y.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        mfd_param top atlas s e /\
        open_in top W /\ mfd_smooth_on atlas W (\x. lift(f x)) /\
        c IN atlas /\ y IN s /\ e y IN FST c INTER W /\
        ~(frechet_derivative (\z. lift(f(e z))) (at y) = (\h. vec 0))
        ==> ~(frechet_derivative (\z. lift(f(chart_inv c z))) (at (SND c (e y))) =
              (\h. vec 0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s:real^N->bool`; `e:real^N->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ei:A->real^N` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `G = \z. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) z))` THEN
  ABBREV_TAC `phi = SND(c:(A->bool)#(A->real^N)) o (e:real^N->A)` THEN
  SUBGOAL_THEN `open {z:real^N | z IN s /\ (e:real^N->A) z IN FST(c:(A->bool)#(A->real^N)) INTER W}` ASSUME_TAC THENL
   [UNDISCH_TAC `continuous_map (subtopology euclidean s,top) (e:real^N->A)` THEN
    REWRITE_TAC[continuous_map; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    DISCH_THEN(MP_TAC o SPEC `FST(c:(A->bool)#(A->real^N)) INTER W` o CONJUNCT2) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_MESON_TAC[MFDM_CHART]; ALL_TAC] THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `(G:real^N->real^1) differentiable (at (SND(c:(A->bool)#(A->real^N)) (e(y:real^N))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER W)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
      ASM_MESON_TAC[MFDM_CHART];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `mfd_smooth_on (atlas:((A->bool)#(A->real^N))->bool) W
                     (\x. lift((f:A->real) x))` THEN
      REWRITE_TAC[mfd_smooth_on] THEN DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "G" THEN REWRITE_TAC[o_DEF];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:real^N->real^N) differentiable (at y)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `{z:real^N | z IN s /\ (e:real^N->A) z IN FST(c:(A->bool)#(A->real^N)) INTER W}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    UNDISCH_TAC `mfd_smooth_map (open_set_atlas s) (atlas:((A->bool)#(A->real^N))->bool)
                   s (e:real^N->A)` THEN
    REWRITE_TAC[mfd_smooth_map; open_set_atlas; IN_SING] THEN
    DISCH_THEN(MP_TAC o SPECL [`(s:real^N->bool,(\x:real^N. x))`;
                               `c:(A->bool)#(A->real^N)`]) THEN
    ASM_REWRITE_TAC[FST; SND; IMAGE_ID; INTER_IDEMPOT] THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `{z:real^N | z IN s /\ (e:real^N->A) z IN FST(c:(A->bool)#(A->real^N))}` THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `SND(c:(A->bool)#(A->real^N)) o (e:real^N->A) o chart_inv (s,(\x:real^N. x))` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "phi" THEN
    SIMP_TAC[IN_ELIM_THM; o_THM; MFDM_CHART_INV_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\z. lift((f:A->real)(e z))) has_derivative
     (frechet_derivative (G:real^N->real^1) (at (phi y)) o
      frechet_derivative (phi:real^N->real^N) (at y))) (at y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `(G:real^N->real^1) o (phi:real^N->real^N)` THEN
    UNDISCH_TAC `open {z:real^N | z IN s /\ (e:real^N->A) z IN FST(c:(A->bool)#(A->real^N)) INTER W}` THEN
    REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(z:real^N) IN s /\ (e:real^N->A) z IN FST(c:(A->bool)#(A->real^N)) INTER W`
      STRIP_ASSUME_TAC
      THENL
       [UNDISCH_TAC `ball(y:real^N,d) SUBSET
                     {z | z IN s /\ (e:real^N->A) z IN FST(c:(A->bool)#(A->real^N)) INTER W}` THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
        ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MAP_EVERY EXPAND_TAC ["G"; "phi"] THEN REWRITE_TAC[o_THM] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
      ASM_MESON_TAC[MFDM_CHART; IN_INTER];
      MATCH_MP_TAC DIFF_CHAIN_AT THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        EXPAND_TAC "phi" THEN REWRITE_TAC[o_THM] THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  UNDISCH_TAC `~(frechet_derivative (\z. lift((f:A->real)(e z))) (at (y:real^N)) =
                (\h. vec 0))` THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  SUBGOAL_THEN `(phi:real^N->real^N) y = SND(c:(A->bool)#(A->real^N)) (e y)` SUBST1_TAC THENL
   [EXPAND_TAC "phi" THEN REWRITE_TAC[o_THM]; ALL_TAC] THEN
  EXPAND_TAC "G" THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[FUN_EQ_THM; o_THM]);;

(* ------------------------------------------------------------------------- *)
(* The derivative of smooth_step exists everywhere and is                    *)
(* bounded (continuous on [0,1] by smoothness, zero outside where the step   *)
(* is constant).                                                             *)
(* ------------------------------------------------------------------------- *)

let APX_SMOOTH_STEP_DERIV = prove
 (`?D C. &0 < C /\
         !t. (smooth_step has_real_derivative D t) (atreal t) /\ abs(D t) <= C`,
  MP_TAC SMOOTH_STEP_SMOOTH THEN REWRITE_TAC[smooth_map_on] THEN
  DISCH_THEN(MP_TAC o SPEC `SUC 0`) THEN
  REWRITE_TAC[continuously_differentiable; IN_UNIV; WITHIN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^1->real^1->real^1` (CONJUNCTS_THEN2
    (LABEL_TAC "der") (LABEL_TAC "cont"))) THEN
  EXISTS_TAC `\t. drop((f':real^1->real^1->real^1) (lift t) (lift(&1)))` THEN
  SUBGOAL_THEN
   `!t. (smooth_step has_real_derivative
          drop((f':real^1->real^1->real^1) (lift t) (lift(&1)))) (atreal t)`
  (LABEL_TAC "rd") THENL
   [GEN_TAC THEN REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT] THEN
    USE_THEN "der" (MP_TAC o SPEC `lift t`) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `linear((f':real^1->real^1->real^1)(lift t))` ASSUME_TAC THENL
     [USE_THEN "der" (MP_TAC o SPEC `lift t`) THEN SIMP_TAC[has_derivative]; ALL_TAC] THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^1` THEN
    SUBGOAL_THEN `x = drop x % lift(&1)` (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th])
    THENL [REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; LIFT_DROP; REAL_MUL_RID]; ALL_TAC] THEN
    ASM_SIMP_TAC[LINEAR_CMUL] THEN
    REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^1. (f':real^1->real^1->real^1) x (lift(&1))`;
                 `interval[lift(&0),lift(&1)]`] COMPACT_CONTINUOUS_IMAGE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_INTERVAL] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(:real^1)` THEN REWRITE_TAC[SUBSET_UNIV] THEN
    USE_THEN "cont" (ACCEPT_TAC o SPEC `lift(&1)`);
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[bounded; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` (LABEL_TAC "B")) THEN
  EXISTS_TAC `abs B + &1` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN USE_THEN "rd" (fun th -> REWRITE_TAC[th]) THEN
  ASM_CASES_TAC `t < &0` THENL
   [SUBGOAL_THEN `drop((f':real^1->real^1->real^1) (lift t) (lift(&1))) = &0` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
      MAP_EVERY EXISTS_TAC [`smooth_step`; `t:real`] THEN
      USE_THEN "rd" (fun th -> REWRITE_TAC[th]) THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
      MAP_EVERY EXISTS_TAC [`\x:real. &0`; `--t`] THEN
      REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `x:real` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC SMOOTH_STEP_0 THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `&1 < t` THENL
   [SUBGOAL_THEN `drop((f':real^1->real^1->real^1) (lift t) (lift(&1))) = &0` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
      MAP_EVERY EXISTS_TAC [`smooth_step`; `t:real`] THEN
      USE_THEN "rd" (fun th -> REWRITE_TAC[th]) THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
      MAP_EVERY EXISTS_TAC [`\x:real. &1`; `t - &1`] THEN
      REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `x:real` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC SMOOTH_STEP_1 THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "B" (MP_TAC o SPEC `lift t`) THEN
  REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[NORM_REAL; GSYM drop] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* E3, the splice.  On T UNION N', F is the tube coordinate                  *)
(* sigma = sval o Ei below the window (w1,w2) of N' (in the coordinate sp =  *)
(* sval o ei' of N'), s' + c above it, and the smooth_step interpolation in  *)
(* between.  Basic values; smoothness of sval.                               *)
(* ------------------------------------------------------------------------- *)

let apx_splice = new_definition
 `apx_splice (eps:real) (e':real^3->A) (ei':A->real^3) (Ei:A->real^3)
             (w1:real) (w2:real) (c:real) (p:A) =
    if p IN IMAGE e' (rfs_neck_dom eps)
    then (&1 - smooth_step((apx_sval(ei' p) - w1) / (w2 - w1))) * apx_sval(Ei p) +
         smooth_step((apx_sval(ei' p) - w1) / (w2 - w1)) * (apx_sval(ei' p) + c)
    else apx_sval(Ei p)`;;

let APX_SPLICE_VALUES = prove
 (`!eps (e':real^3->A) ei' Ei w1 w2 c p.
        w1 < w2
        ==> (~(p IN IMAGE e' (rfs_neck_dom eps))
             ==> apx_splice eps e' ei' Ei w1 w2 c p = apx_sval(Ei p)) /\
            (p IN IMAGE e' (rfs_neck_dom eps) /\ apx_sval(ei' p) <= w1
             ==> apx_splice eps e' ei' Ei w1 w2 c p = apx_sval(Ei p)) /\
            (p IN IMAGE e' (rfs_neck_dom eps) /\ w2 <= apx_sval(ei' p)
             ==> apx_splice eps e' ei' Ei w1 w2 c p = apx_sval(ei' p) + c)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[apx_splice] THEN
  SUBGOAL_THEN `&0 < w2 - w1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `smooth_step((apx_sval((ei':A->real^3) p) - w1) / (w2 - w1)) = &0`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SMOOTH_STEP_0 THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    SUBGOAL_THEN `smooth_step((apx_sval((ei':A->real^3) p) - w1) / (w2 - w1)) = &1`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SMOOTH_STEP_1 THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC]]);;

let APX_SVAL_SMOOTH = prove
 (`smooth_map_on {y:real^3 | ~(y = vec 0)} (\y. lift(apx_sval y))`,
  REWRITE_TAC[apx_sval] THEN
  MP_TAC(ISPECL [`{y:real^3 | ~(y = vec 0)}`; `sqrt(&2)`;
                 `\y:real^3. lift(log(norm y))`] SMOOTH_MAP_ON_LIFT_CMUL) THEN
  REWRITE_TAC[LIFT_DROP; OPEN_NONZERO] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`{y:real^3 | ~(y = vec 0)}`; `\y:real^3. lift(norm y)`]
    SMOOTH_MAP_ON_LIFT_LOG) THEN
  REWRITE_TAC[LIFT_DROP; OPEN_NONZERO; SMOOTH_MAP_ON_LIFT_NORM_NONZERO] THEN
  DISCH_THEN MATCH_MP_TAC THEN SIMP_TAC[IN_ELIM_THM; NORM_POS_LT]);;

(* The splice formula in the coordinates of N' is smooth. *)

let APX_SPLICE_FORMULA_SMOOTH = prove
 (`!O (h:real^3->real^3) w1 w2 c.
        open O /\ smooth_map_on O h /\
        (!v. v IN O ==> ~(h v = vec 0) /\ ~(v = vec 0))
        ==> smooth_map_on O
              (\v. lift((&1 - smooth_step((apx_sval v - w1) / (w2 - w1))) * apx_sval(h v) +
                        smooth_step((apx_sval v - w1) / (w2 - w1)) * (apx_sval v + c)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on O (\v:real^3. lift(apx_sval v))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `{y:real^3 | ~(y = vec 0)}` THEN
    REWRITE_TAC[APX_SVAL_SMOOTH] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on O (\v:real^3. lift(apx_sval((h:real^3->real^3) v)))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\v:real^3. lift(apx_sval((h:real^3->real^3) v))) =
                  (\y. lift(apx_sval y)) o h` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `{y:real^3 | ~(y = vec 0)}` THEN
    ASM_REWRITE_TAC[OPEN_NONZERO; APX_SVAL_SMOOTH] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on O (\v:real^3. lift(smooth_step((apx_sval v - w1) / (w2 - w1))))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`O:real^3->bool`;
                   `\v:real^3. lift((apx_sval v - w1) / (w2 - w1))`]
                  SMOOTH_MAP_ON_SMOOTH_STEP_COMPOSE) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    MP_TAC(ISPECL [`O:real^3->bool`; `inv(w2 - w1)`;
                   `\v:real^3. lift(apx_sval v - w1)`] SMOOTH_MAP_ON_LIFT_CMUL) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`O:real^3->bool`; `\v:real^3. lift(apx_sval v)`; `\v:real^3. lift w1`]
                  SMOOTH_MAP_ON_LIFT_SUB) THEN
    ASM_REWRITE_TAC[LIFT_DROP; SMOOTH_MAP_ON_CONST];
    ALL_TAC] THEN
  ABBREV_TAC `X = \v:real^3. lift(smooth_step((apx_sval v - w1) / (w2 - w1)))` THEN
  ABBREV_TAC `Y = \v:real^3. lift(apx_sval((h:real^3->real^3) v))` THEN
  ABBREV_TAC `Z = \v:real^3. lift(apx_sval v + c)` THEN
  SUBGOAL_THEN `smooth_map_on O (Z:real^3->real^1)` ASSUME_TAC THENL
   [EXPAND_TAC "Z" THEN
    MP_TAC(ISPECL [`O:real^3->bool`; `\v:real^3. lift(apx_sval v)`; `\v:real^3. lift c`]
                  SMOOTH_MAP_ON_LIFT_ADD) THEN
    ASM_REWRITE_TAC[LIFT_DROP; SMOOTH_MAP_ON_CONST];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\v. lift((&1 - smooth_step((apx_sval v - w1) / (w2 - w1))) * apx_sval((h:real^3->real^3) v) +
              smooth_step((apx_sval v - w1) / (w2 - w1)) * (apx_sval v + c))) =
    (\v. lift(drop((\v. lift(drop((\v. lift(&1)) v) - drop((X:real^3->real^1) v))) v) *
              drop((Y:real^3->real^1) v) +
              drop(X v) * drop((Z:real^3->real^1) v)))`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["X"; "Y"; "Z"] THEN REWRITE_TAC[FUN_EQ_THM; LIFT_DROP];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`O:real^3->bool`;
                 `\v:real^3. lift(drop((\v:real^3. lift(drop((\v:real^3. lift(&1)) v) -
                                                   drop((X:real^3->real^1) v))) v) *
                                  drop((Y:real^3->real^1) v))`;
                 `\v:real^3. lift(drop((X:real^3->real^1) v) * drop((Z:real^3->real^1) v))`]
                SMOOTH_MAP_ON_LIFT_ADD) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`O:real^3->bool`; `\v:real^3. lift(&1 - drop((X:real^3->real^1) v))`;
                   `Y:real^3->real^1`] SMOOTH_MAP_ON_LIFT_MUL) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`O:real^3->bool`; `\v:real^3. lift(&1)`; `X:real^3->real^1`]
                  SMOOTH_MAP_ON_LIFT_SUB) THEN
    ASM_REWRITE_TAC[LIFT_DROP; SMOOTH_MAP_ON_CONST; ETA_AX];
    MP_TAC(ISPECL [`O:real^3->bool`; `X:real^3->real^1`; `Z:real^3->real^1`]
                  SMOOTH_MAP_ON_LIFT_MUL) THEN
    ASM_REWRITE_TAC[]]);;

let APX_CSLAB = prove
 (`!a b. compact(cball(vec 0:real^3,exp(b / sqrt(&2))) DIFF ball(vec 0,exp(a / sqrt(&2)))) /\
         (!v:real^3. v IN cball(vec 0,exp(b / sqrt(&2))) DIFF ball(vec 0,exp(a / sqrt(&2))) <=>
                     ~(v = vec 0) /\ a <= apx_sval v /\ apx_sval v <= b)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[COMPACT_CBALL; OPEN_BALL]; ALL_TAC] THEN
  X_GEN_TAC `v:real^3` THEN REWRITE_TAC[IN_DIFF; IN_CBALL_0; IN_BALL_0; REAL_NOT_LT] THEN
  ASM_CASES_TAC `v:real^3 = vec 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[NORM_0] THEN MP_TAC(SPEC `a / sqrt(&2)` REAL_EXP_POS_LT) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[APX_EXP_LT_NORM] THEN REWRITE_TAC[apx_sval] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC);;

(* Smoothness of the splice on T UNION N'. *)

let APX_SPLICE_SMOOTH = prove
 (`!top atlas eps (E:real^3->A) (Ei:A->real^3) S e' (ei':A->real^3) w1 w2 c.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ &0 < eps /\
        mfd_param top atlas S E /\ S SUBSET {y | ~(y = vec 0)} /\
        (!y. y IN S ==> Ei(E y) = y) /\
        mfd_param top atlas (rfs_neck_dom eps) e' /\
        (!z. z IN rfs_neck_dom eps ==> ei'(e' z) = z) /\
        --inv eps < w1 /\ w1 < w2 /\ w2 < inv(&2 * eps) /\
        (!p. p IN IMAGE E S INTER IMAGE e' (rfs_neck_dom eps)
             ==> apx_sval(ei' p) <= inv(&2 * eps)) /\
        (!p. p IN IMAGE e' (rfs_neck_dom eps) /\ ~(p IN IMAGE E S)
             ==> w2 < apx_sval(ei' p))
        ==> mfd_smooth_on atlas (IMAGE E S UNION IMAGE e' (rfs_neck_dom eps))
                          (\p. lift(apx_splice eps e' ei' Ei w1 w2 c p))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "pq") (LABEL_TAC "out"))))))))))))) THEN
  SUBGOAL_THEN `&0 < inv eps /\ inv(&2 * eps) < inv eps` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV] THEN MP_TAC(SPEC `eps:real` APX_INV2) THEN
    SUBGOAL_THEN `&0 < inv eps` MP_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `S:real^3->bool`; `E:real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `E0:A->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `e':real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e1:A->real^3` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC APX_MFD_SMOOTH_ON_LOCAL THEN EXISTS_TAC `top:A topology` THEN
  ASM_SIMP_TAC[OPEN_IN_UNION] THEN X_GEN_TAC `q:A` THEN REWRITE_TAC[IN_UNION] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `!v:real^3. v IN rfs_neck_dom eps ==> ~(v = vec 0)` ASSUME_TAC THENL
   [MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
  ASM_CASES_TAC `(q:A) IN IMAGE (e':real^3->A) (rfs_neck_dom eps)` THENL
   [ASM_CASES_TAC `(q:A) IN IMAGE (E:real^3->A) S` THENL
     [(* q in T and N': the splice formula in the coordinates of N' *)
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `S:real^3->bool`; `rfs_neck_dom eps`; `E:real^3->A`; `e':real^3->A`;
                     `Ei:A->real^3`] APX_PARAM_TRANSITION) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "trE"))) THEN
      EXISTS_TAC `IMAGE (e':real^3->A)
                    {v | v IN rfs_neck_dom eps /\ e' v IN IMAGE (E:real^3->A) S}` THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
        MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        UNDISCH_TAC `(q:A) IN IMAGE (e':real^3->A) (rfs_neck_dom eps)` THEN
        UNDISCH_TAC `(q:A) IN IMAGE (E:real^3->A) S` THEN SET_TAC[];
        SET_TAC[];
        MATCH_MP_TAC APX_MFD_SMOOTH_ON_PARAM THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `rfs_neck_dom eps`] THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
        EXISTS_TAC `\v. lift((&1 - smooth_step((apx_sval v - w1) / (w2 - w1))) *
                             apx_sval(((Ei:A->real^3) o (e':real^3->A)) v) +
                             smooth_step((apx_sval v - w1) / (w2 - w1)) * (apx_sval v + c))` THEN
        CONJ_TAC THENL
         [REWRITE_TAC[IN_ELIM_THM; o_THM; apx_splice] THEN X_GEN_TAC `v:real^3` THEN
          STRIP_TAC THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
          MATCH_MP_TAC APX_SPLICE_FORMULA_SMOOTH THEN ASM_REWRITE_TAC[ETA_AX] THEN
          REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN
          REWRITE_TAC[o_THM] THEN
          USE_THEN "trE" (MP_TAC o SPEC `v:real^3`) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
          DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_TAC THEN CONJ_TAC THENL
           [UNDISCH_TAC `S SUBSET {y:real^3 | ~(y = vec 0)}` THEN
            UNDISCH_TAC `(Ei:A->real^3)((e':real^3->A) v) IN S` THEN SET_TAC[];
            MP_TAC(SPECL [`eps:real`; `v:real^3`] APX_SVAL_NECK_DOM) THEN
            ASM_SIMP_TAC[]]]];
      (* q in N' outside T: s' + c beyond the window *)
      EXISTS_TAC `IMAGE (e':real^3->A) (apx_slab w2 (inv eps))` THEN
      SUBGOAL_THEN `apx_slab w2 (inv eps) SUBSET rfs_neck_dom eps` ASSUME_TAC THENL
       [MATCH_MP_TAC APX_SLAB_SUB_DOM THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `open(apx_slab w2 (inv eps))` ASSUME_TAC THENL
       [REWRITE_TAC[apx_slab; OPEN_ANNULUS]; ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
        MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `(q:A) IN IMAGE (e':real^3->A) (rfs_neck_dom eps)` THEN
        REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `v0:real^3` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `v0:real^3` THEN ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN
        USE_THEN "out" (MP_TAC o SPEC `q:A`) THEN ANTS_TAC THENL
         [CONJ_TAC THENL
           [REWRITE_TAC[ASSUME `(q:A) = (e':real^3->A) v0`] THEN
            MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
            FIRST_ASSUM ACCEPT_TAC];
          ALL_TAC] THEN
        REWRITE_TAC[ASSUME `(q:A) = (e':real^3->A) v0`] THEN
        REWRITE_TAC[MP (SPEC `v0:real^3` (ASSUME `!z:real^3. z IN rfs_neck_dom eps ==>
                                                   (ei':A->real^3)((e':real^3->A) z) = z`))
                       (ASSUME `(v0:real^3) IN rfs_neck_dom eps`)] THEN
        MP_TAC(SPECL [`eps:real`; `v0:real^3`] APX_SVAL_NECK_DOM) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `apx_slab w2 (inv eps) SUBSET rfs_neck_dom eps` THEN SET_TAC[];
        MATCH_MP_TAC APX_MFD_SMOOTH_ON_PARAM THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `rfs_neck_dom eps`] THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
        EXISTS_TAC `\v:real^3. lift(apx_sval v + c)` THEN CONJ_TAC THENL
         [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN
          SUBGOAL_THEN `(v:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
           [UNDISCH_TAC `apx_slab w2 (inv eps) SUBSET rfs_neck_dom eps` THEN
            UNDISCH_TAC `(v:real^3) IN apx_slab w2 (inv eps)` THEN SET_TAC[];
            ALL_TAC] THEN
          MP_TAC(ISPECL [`eps:real`; `e':real^3->A`; `ei':A->real^3`; `Ei:A->real^3`;
                         `w1:real`; `w2:real`; `c:real`; `(e':real^3->A) v`]
                        APX_SPLICE_VALUES) THEN
          ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
          DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
          REWRITE_TAC[MP (SPEC `v:real^3` (ASSUME `!z:real^3. z IN rfs_neck_dom eps ==>
                                                   (ei':A->real^3)((e':real^3->A) z) = z`))
                         (ASSUME `(v:real^3) IN rfs_neck_dom eps`)] THEN
          ANTS_TAC THENL
           [CONJ_TAC THENL
             [MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
              UNDISCH_TAC `(v:real^3) IN apx_slab w2 (inv eps)` THEN
              SIMP_TAC[APX_SLAB_SVAL; REAL_LT_IMP_LE]];
            SIMP_TAC[]];
          MP_TAC(ISPECL [`apx_slab w2 (inv eps)`; `\v:real^3. lift(apx_sval v)`;
                         `\v:real^3. lift c`] SMOOTH_MAP_ON_LIFT_ADD) THEN
          REWRITE_TAC[LIFT_DROP; SMOOTH_MAP_ON_CONST] THEN DISCH_THEN MATCH_MP_TAC THEN
          ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `{y:real^3 | ~(y = vec 0)}` THEN
          REWRITE_TAC[APX_SVAL_SMOOTH] THEN REWRITE_TAC[SUBSET; APX_SLAB_SVAL; IN_ELIM_THM] THEN
          MESON_TAC[]]]];
    ALL_TAC] THEN
  (* q in T outside N': near q, N' only meets the part below the window *)
  SUBGOAL_THEN `(q:A) IN IMAGE (E:real^3->A) S` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`w1:real`; `inv(&2 * eps)`] APX_CSLAB) THEN
  ABBREV_TAC `Kc = cball(vec 0:real^3,exp(inv(&2 * eps) / sqrt(&2))) DIFF
                   ball(vec 0,exp(w1 / sqrt(&2)))` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Kc")) THEN
  SUBGOAL_THEN `(Kc:real^3->bool) SUBSET rfs_neck_dom eps` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `v:real^3` THEN
    USE_THEN "Kc" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `closed_in top (IMAGE (e':real^3->A) Kc)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean (rfs_neck_dom eps)` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open {y:real^3 | y IN S /\ (E:real^3->A) y IN topspace top DIFF IMAGE (e':real^3->A) Kc}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`E:real^3->A`; `subtopology euclidean (S:real^3->bool)`; `top:A topology`;
                   `topspace top DIFF IMAGE (e':real^3->A) Kc`]
                  OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    ASM_SIMP_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; OPEN_IN_DIFF; OPEN_IN_TOPSPACE] THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_EQ];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (E:real^3->A)
                {y | y IN S /\ E y IN topspace top DIFF IMAGE (e':real^3->A) Kc}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `S:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    UNDISCH_TAC `(q:A) IN IMAGE (E:real^3->A) S` THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `y0:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `y0:real^3` THEN ASM_REWRITE_TAC[IN_ELIM_THM; IN_DIFF] THEN CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (E:real^3->A) S SUBSET topspace top` THEN
      UNDISCH_TAC `(y0:real^3) IN S` THEN SET_TAC[];
      DISCH_TAC THEN
      UNDISCH_TAC `~((q:A) IN IMAGE (e':real^3->A) (rfs_neck_dom eps))` THEN
      REWRITE_TAC[ASSUME `(q:A) = (E:real^3->A) y0`] THEN
      UNDISCH_TAC `(Kc:real^3->bool) SUBSET rfs_neck_dom eps` THEN
      UNDISCH_TAC `(E:real^3->A) y0 IN IMAGE (e':real^3->A) Kc` THEN SET_TAC[]];
    SET_TAC[];
    MATCH_MP_TAC APX_MFD_SMOOTH_ON_PARAM THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `S:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `\y:real^3. lift(apx_sval y)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM; IN_DIFF; o_THM] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
      AP_TERM_TAC THEN
      SUBGOAL_THEN `(Ei:A->real^3)((E:real^3->A) y) = y` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term (fun u -> u = `Ei:A->real^3`)) (concl th))) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`eps:real`; `e':real^3->A`; `ei':A->real^3`; `Ei:A->real^3`;
                     `w1:real`; `w2:real`; `c:real`; `(E:real^3->A) y`]
                    APX_SPLICE_VALUES) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      ASM_CASES_TAC `(E:real^3->A) y IN IMAGE (e':real^3->A) (rfs_neck_dom eps)` THENL
       [DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
        ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
        UNDISCH_TAC `(E:real^3->A) y IN IMAGE (e':real^3->A) (rfs_neck_dom eps)` THEN
        REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
        REWRITE_TAC[ASSUME `(E:real^3->A) y = (e':real^3->A) z`] THEN
        REWRITE_TAC[MP (SPEC `z:real^3` (ASSUME `!z:real^3. z IN rfs_neck_dom eps ==>
                                                   (ei':A->real^3)((e':real^3->A) z) = z`))
                       (ASSUME `(z:real^3) IN rfs_neck_dom eps`)] THEN
        MATCH_MP_TAC(REAL_ARITH `~(w1 < s) ==> s <= w1`) THEN DISCH_TAC THEN
        UNDISCH_TAC `~((E:real^3->A) y IN IMAGE (e':real^3->A) Kc)` THEN
        REWRITE_TAC[ASSUME `(E:real^3->A) y = (e':real^3->A) z`] THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN USE_THEN "Kc" (fun th -> REWRITE_TAC[th]) THEN
        CONJ_TAC THENL [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        USE_THEN "pq" (MP_TAC o SPEC `(e':real^3->A) z`) THEN ANTS_TAC THENL
         [REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
           [REWRITE_TAC[GSYM(ASSUME `(E:real^3->A) y = (e':real^3->A) z`)] THEN
            MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
            MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC];
          REWRITE_TAC[MP (SPEC `z:real^3` (ASSUME `!z:real^3. z IN rfs_neck_dom eps ==>
                                                   (ei':A->real^3)((e':real^3->A) z) = z`))
                         (ASSUME `(z:real^3) IN rfs_neck_dom eps`)]];
        DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `{y:real^3 | ~(y = vec 0)}` THEN
      REWRITE_TAC[APX_SVAL_SMOOTH] THEN
      UNDISCH_TAC `S SUBSET {y:real^3 | ~(y = vec 0)}` THEN SET_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* E3, regularity of the splice.  Along the radial line of N'                *)
(* through a window point, the splice has derivative                         *)
(* (1-chi) g' + chi + chi' (t + c - g - L) >= min(rho - kappa,1) - C d0/(w2-w1)*)
(* > 0, where g = s_N along the line (g' near rho by the alignment).         *)
(* ------------------------------------------------------------------------- *)

let APX_RAY_COMPOSE_DERIV = prove
 (`!(H:real^3->real^1) H' (om:real^3) t.
        (H has_derivative H') (at (exp(t / sqrt(&2)) % om))
        ==> ((\s. drop(H(exp(s / sqrt(&2)) % om))) has_real_derivative
             drop(H'(inv(sqrt(&2)) % exp(t / sqrt(&2)) % om))) (atreal t)`,
  REPEAT GEN_TAC THEN ABBREV_TAC `v = exp(t / sqrt(&2)) % (om:real^3)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `linear(H':real^3->real^1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
  SUBGOAL_THEN `((\r. exp(drop r / sqrt(&2)) % (om:real^3)) has_derivative
                 (\r. drop r % (inv(sqrt(&2)) % v))) (at (lift t))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\s. exp(s / sqrt(&2))`; `exp(t / sqrt(&2)) * inv(sqrt(&2))`; `t:real`;
                   `om:real^3`] APX_REAL_VMUL_VD) THEN
    REWRITE_TAC[APX_EXP_HALF_DERIV; has_vector_derivative] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN EXPAND_TAC "v" THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\r. exp(drop r / sqrt(&2)) % (om:real^3)`; `H:real^3->real^1`;
                 `\r. drop r % (inv(sqrt(&2)) % (v:real^3))`; `H':real^3->real^1`;
                 `lift t`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN
  REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `r:real^1` THEN
  ASM_SIMP_TAC[LINEAR_CMUL] THEN REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL] THEN
  REAL_ARITH_TAC);;

let APX_SPLICE_RAY_POS = prove
 (`!g g' t0 w1 w2 c L Delta D C rho kappa d0.
        (g has_real_derivative g') (atreal t0) /\ abs(g' - rho) <= kappa /\
        (smooth_step has_real_derivative D) (atreal ((t0 - w1) / (w2 - w1))) /\
        abs D <= C /\ w1 < w2 /\ c = L + Delta /\ abs(g t0 - t0 - Delta) <= d0 /\
        &0 <= d0 /\ C * d0 < (w2 - w1) * min (rho - kappa) (&1)
        ==> ?f'. ((\t. (&1 - smooth_step((t - w1) / (w2 - w1))) * (g t + L) +
                       smooth_step((t - w1) / (w2 - w1)) * (t + c))
                  has_real_derivative f') (atreal t0) /\ &0 < f'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < w2 - w1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `chi = smooth_step((t0 - w1) / (w2 - w1))` THEN
  ABBREV_TAC `dchi = D * inv(w2 - w1)` THEN
  SUBGOAL_THEN `((\t. smooth_step((t - w1) / (w2 - w1))) has_real_derivative dchi) (atreal t0)`
  ASSUME_TAC THENL
   [EXPAND_TAC "dchi" THEN
    MP_TAC(ISPECL [`\t. (t - w1) / (w2 - w1)`; `smooth_step`; `inv(w2 - w1)`; `D:real`;
                   `t0:real`] REAL_DIFF_CHAIN_ATREAL) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_div] THEN
    MP_TAC(ISPECL [`\t:real. t - w1`; `&1`; `\t:real. inv(w2 - w1)`; `&0`; `t0:real`]
                  HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN ANTS_TAC THENL
     [MP_TAC(ISPECL [`\t:real. t`; `&1`; `\t:real. (w1:real)`; `&0`; `atreal t0`]
                    HAS_REAL_DERIVATIVE_SUB) THEN
      REWRITE_TAC[HAS_REAL_DERIVATIVE_ID; HAS_REAL_DERIVATIVE_CONST; REAL_SUB_RZERO; ETA_AX];
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `(&1 - chi) * g' + chi * &1 + dchi * ((t0 + c) - (g t0 + L))` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `((\t. &1 - smooth_step((t - w1) / (w2 - w1))) has_real_derivative
                   (&0 - dchi)) (atreal t0)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`\t:real. &1`; `&0`; `\t. smooth_step((t - w1) / (w2 - w1))`;
                     `dchi:real`; `atreal t0`] HAS_REAL_DERIVATIVE_SUB) THEN
      ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST];
      ALL_TAC] THEN
    SUBGOAL_THEN `((\t. (g:real->real) t + L) has_real_derivative (g' + &0)) (atreal t0)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`g:real->real`; `g':real`; `\t:real. (L:real)`; `&0`; `atreal t0`]
                    HAS_REAL_DERIVATIVE_ADD) THEN
      ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST];
      ALL_TAC] THEN
    SUBGOAL_THEN `((\t:real. t + c) has_real_derivative (&1 + &0)) (atreal t0)` ASSUME_TAC
    THENL
     [MP_TAC(ISPECL [`\t:real. t`; `&1`; `\t:real. (c:real)`; `&0`; `atreal t0`]
                    HAS_REAL_DERIVATIVE_ADD) THEN
      REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST; HAS_REAL_DERIVATIVE_ID];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\t. &1 - smooth_step((t - w1) / (w2 - w1))`; `&0 - dchi`;
                   `\t. (g:real->real) t + L`; `g' + &0`; `t0:real`]
                  HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\t. smooth_step((t - w1) / (w2 - w1))`; `dchi:real`;
                   `\t:real. t + c`; `&1 + &0`; `t0:real`]
                  HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\t. (&1 - smooth_step((t - w1) / (w2 - w1))) * ((g:real->real) t + L)`;
                   `(&1 - smooth_step((t0 - w1) / (w2 - w1))) * (g' + &0) +
                    (&0 - dchi) * ((g:real->real) t0 + L)`;
                   `\t. smooth_step((t - w1) / (w2 - w1)) * (t + c)`;
                   `smooth_step((t0 - w1) / (w2 - w1)) * (&1 + &0) + dchi * (t0 + c)`;
                   `atreal t0`] HAS_REAL_DERIVATIVE_ADD) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `m = min (rho - kappa) (&1)` THEN
  SUBGOAL_THEN `&0 <= chi /\ chi <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "chi" THEN REWRITE_TAC[SMOOTH_STEP_BOUNDS]; ALL_TAC] THEN
  SUBGOAL_THEN `m <= (&1 - chi) * g' + chi * &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `(&1 - chi) * m <= (&1 - chi) * g' /\ chi * m <= chi * &1` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN EXPAND_TAC "m" THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(dchi * ((t0 + c) - ((g:real->real) t0 + L))) <= (C * inv(w2 - w1)) * d0`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[REAL_ABS_POS] THEN CONJ_TAC THENL
     [EXPAND_TAC "dchi" THEN REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_INV] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
      UNDISCH_TAC `c = L + Delta` THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(C * inv(w2 - w1)) * d0 < m` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `(C * i) * d = (C * d) * i`; GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Near a point of T outside the window part of N', the splice is sigma. *)

let APX_SPLICE_NEAR_T = prove
 (`!top atlas eps (E:real^3->A) (Ei:A->real^3) S e' (ei':A->real^3) w1 w2 c x.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ &0 < eps /\
        mfd_param top atlas S E /\ (!y. y IN S ==> Ei(E y) = y) /\
        mfd_param top atlas (rfs_neck_dom eps) e' /\
        (!z. z IN rfs_neck_dom eps ==> ei'(e' z) = z) /\
        --inv eps < w1 /\ w1 < w2 /\ inv(&2 * eps) < inv eps /\
        (!p. p IN IMAGE E S INTER IMAGE e' (rfs_neck_dom eps)
             ==> apx_sval(ei' p) <= inv(&2 * eps)) /\
        x IN IMAGE E S /\
        (~(x IN IMAGE e' (rfs_neck_dom eps)) \/ apx_sval(ei' x) < w1)
        ==> ?O. open O /\ O SUBSET S /\ Ei x IN O /\
                !y. y IN O ==> apx_splice eps e' ei' Ei w1 w2 c (E y) = apx_sval y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "pq") (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "case"))))))))))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `S:real^3->bool`; `E:real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `E0:A->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`w1:real`; `inv(&2 * eps)`] APX_CSLAB) THEN
  ABBREV_TAC `Kc = cball(vec 0:real^3,exp(inv(&2 * eps) / sqrt(&2))) DIFF
                   ball(vec 0,exp(w1 / sqrt(&2)))` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Kc")) THEN
  SUBGOAL_THEN `(Kc:real^3->bool) SUBSET rfs_neck_dom eps` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `v:real^3` THEN
    USE_THEN "Kc" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `closed_in top (IMAGE (e':real^3->A) Kc)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean (rfs_neck_dom eps)` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `rfs_neck_dom eps`; `e':real^3->A`] GRGD_PARAM_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN];
    ALL_TAC] THEN
  EXISTS_TAC `{y:real^3 | y IN S /\ (E:real^3->A) y IN topspace top DIFF IMAGE (e':real^3->A) Kc}` THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`E:real^3->A`; `subtopology euclidean (S:real^3->bool)`; `top:A topology`;
                   `topspace top DIFF IMAGE (e':real^3->A) Kc`]
                  OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    ASM_SIMP_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; OPEN_IN_DIFF; OPEN_IN_TOPSPACE] THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_EQ];
    SET_TAC[];
    UNDISCH_TAC `(x:A) IN IMAGE (E:real^3->A) S` THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `y0:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(Ei:A->real^3) x = y0` SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; IN_DIFF] THEN CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (E:real^3->A) S SUBSET topspace top` THEN
      UNDISCH_TAC `(y0:real^3) IN S` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    USE_THEN "case" MP_TAC THEN
    REWRITE_TAC[ASSUME `(x:A) = (E:real^3->A) y0`; ASSUME `(E:real^3->A) y0 = (e':real^3->A) z`] THEN
    REWRITE_TAC[DE_MORGAN_THM; REAL_NOT_LT] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[];
      SUBGOAL_THEN `(z:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[MP (SPEC `z:real^3` (ASSUME `!z:real^3. z IN rfs_neck_dom eps ==>
                                                   (ei':A->real^3)((e':real^3->A) z) = z`))
                     (ASSUME `(z:real^3) IN rfs_neck_dom eps`)] THEN
      UNDISCH_TAC `(z:real^3) IN Kc` THEN USE_THEN "Kc" (fun th -> REWRITE_TAC[th]) THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_DIFF] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(Ei:A->real^3)((E:real^3->A) y) = y` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun u -> u = `Ei:A->real^3`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`eps:real`; `e':real^3->A`; `ei':A->real^3`; `Ei:A->real^3`;
                 `w1:real`; `w2:real`; `c:real`; `(E:real^3->A) y`]
                APX_SPLICE_VALUES) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `(E:real^3->A) y IN IMAGE (e':real^3->A) (rfs_neck_dom eps)` THENL
   [DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `(E:real^3->A) y IN IMAGE (e':real^3->A) (rfs_neck_dom eps)` THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[ASSUME `(E:real^3->A) y = (e':real^3->A) z`] THEN
    REWRITE_TAC[MP (SPEC `z:real^3` (ASSUME `!z:real^3. z IN rfs_neck_dom eps ==>
                                               (ei':A->real^3)((e':real^3->A) z) = z`))
                   (ASSUME `(z:real^3) IN rfs_neck_dom eps`)] THEN
    MATCH_MP_TAC(REAL_ARITH `~(w1 < s) ==> s <= w1`) THEN DISCH_TAC THEN
    UNDISCH_TAC `~((E:real^3->A) y IN IMAGE (e':real^3->A) Kc)` THEN
    REWRITE_TAC[ASSUME `(E:real^3->A) y = (e':real^3->A) z`] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN USE_THEN "Kc" (fun th -> REWRITE_TAC[th]) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "pq" (MP_TAC o SPEC `(e':real^3->A) z`) THEN ANTS_TAC THENL
     [REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM(ASSUME `(E:real^3->A) y = (e':real^3->A) z`)] THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC];
      REWRITE_TAC[MP (SPEC `z:real^3` (ASSUME `!z:real^3. z IN rfs_neck_dom eps ==>
                                               (ei':A->real^3)((e':real^3->A) z) = z`))
                     (ASSUME `(z:real^3) IN rfs_neck_dom eps`)]];
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[]]);;

let APX_FRECHET_LOCAL_NZ = prove
 (`!(f:real^3->real^1) g g' x O.
        open O /\ x IN O /\ (!y. y IN O ==> f y = g y) /\
        (g has_derivative g') (at x) /\ ~(g' = (\h. vec 0))
        ==> ~(frechet_derivative f (at x) = (\h. vec 0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `((f:real^3->real^1) has_derivative g') (at x)` ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN EXISTS_TAC `g:real^3->real^1` THEN
    UNDISCH_TAC `open(O:real^3->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN EXISTS_TAC `d:real` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `ball(x:real^3,d) SUBSET O` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN ASM_REWRITE_TAC[]);;

let APX_SVAL_DERIV_NZ = prove
 (`!y:real^3 c.
        ~(y = vec 0)
        ==> ((\z. lift(apx_sval z + c)) has_derivative
             (\w. lift(sqrt(&2) * (y dot w) / (y dot y)))) (at y) /\
            ~((\w. lift(sqrt(&2) * (y dot w) / (y dot y))) = (\h. vec 0))`,
  REPEAT STRIP_TAC THENL
   [SUBGOAL_THEN `(\z:real^3. lift(apx_sval z + c)) = (\z. lift(apx_sval z) + lift c)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; LIFT_ADD]; ALL_TAC] THEN
    SUBGOAL_THEN `(\w:real^3. lift(sqrt(&2) * (y dot w) / (y dot y))) =
                  (\w. lift(sqrt(&2) * (y dot w) / (y dot y)) + vec 0)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; VECTOR_ADD_RID]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
    ASM_SIMP_TAC[APX_SVAL_DERIV];
    FIRST_X_ASSUM(MP_TAC o C AP_THM `y:real^3`) THEN
    REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN
    SUBGOAL_THEN `~((y:real^3) dot y = &0) /\ ~(sqrt(&2) = &0)` MP_TAC THENL
     [ASM_REWRITE_TAC[DOT_EQ_0] THEN SIMP_TAC[SQRT_EQ_0; REAL_POS] THEN REAL_ARITH_TAC;
      CONV_TAC REAL_FIELD]]);;

(* In the window, the splice has a nonzero differential (radial direction). *)

let APX_SPLICE_WINDOW_NZ = prove
 (`!top atlas eps (E:real^3->A) (Ei:A->real^3) S e' (ei':A->real^3) en (ein:A->real^3)
    w1 w2 c L Delta d0 rho kappa D C v0.
        smooth_manifold_atlas top atlas /\ &0 < eps /\
        mfd_param top atlas S E /\ (!y. y IN S ==> Ei(E y) = y) /\
        mfd_param top atlas (rfs_neck_dom eps) e' /\
        (!z. z IN rfs_neck_dom eps ==> ei'(e' z) = z) /\
        mfd_param top atlas (rfs_neck_dom eps) en /\
        (!z. z IN rfs_neck_dom eps ==> ein(en z) = z) /\
        w1 < w2 /\
        (!z. z IN rfs_neck_dom eps /\ --inv(&8 * eps) < apx_sval z
             ==> en z IN IMAGE E S /\ apx_sval(Ei(en z)) = apx_sval z + L) /\
        v0 IN rfs_neck_dom eps /\ w1 <= apx_sval v0 /\ apx_sval v0 <= w2 /\
        e' v0 IN IMAGE en (rfs_neck_dom eps) /\ --inv(&8 * eps) < apx_sval(ein(e' v0)) /\
        abs(apx_sval(ein(e' v0)) - apx_sval v0 - Delta) <= d0 /\
        (!k. abs(sqrt(&2) * (ein(e' v0) dot frechet_derivative (ein o e') (at v0) k) /
                 (ein(e' v0) dot ein(e' v0)) -
                 rho * sqrt(&2) * (v0 dot k) / (v0 dot v0))
             <= kappa * sqrt(k dot (cylinder_flow (&0) v0 ** k))) /\
        c = L + Delta /\ &0 <= d0 /\
        (!t. (smooth_step has_real_derivative D t) (atreal t) /\ abs(D t) <= C) /\
        C * d0 < (w2 - w1) * min (rho - kappa) (&1)
        ==> ~(frechet_derivative (\z. lift(apx_splice eps e' ei' Ei w1 w2 c (e' z))) (at v0) =
              (\h. vec 0))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "top")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "al") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "DC") ASSUME_TAC)))))))))))))))))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `rfs_neck_dom eps`; `en:real^3->A`; `e':real^3->A`;
                 `ein:A->real^3`] APX_PARAM_TRANSITION) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tr"))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `e':real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e1:A->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `en:real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `en1:A->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `apx_slab (--inv(&8 * eps)) (inv eps) SUBSET rfs_neck_dom eps /\
                open(apx_slab (--inv(&8 * eps)) (inv eps))` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[apx_slab; OPEN_ANNULUS] THEN REWRITE_TAC[GSYM apx_slab] THEN
    MATCH_MP_TAC APX_SLAB_SUB_DOM THEN
    SUBGOAL_THEN `&0 < inv eps /\ inv(&8 * eps) <= inv eps` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_INV] THEN REWRITE_TAC[REAL_INV_MUL] THEN
      SUBGOAL_THEN `&0 < inv eps` MP_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV]; REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `O = {z:real^3 | z IN rfs_neck_dom eps /\
                    (e':real^3->A) z IN IMAGE (en:real^3->A) (apx_slab (--inv(&8 * eps)) (inv eps))}` THEN
  SUBGOAL_THEN `open(O:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN
    MP_TAC(ISPECL [`e':real^3->A`; `subtopology euclidean (rfs_neck_dom eps)`; `top:A topology`;
                   `IMAGE (en:real^3->A) (apx_slab (--inv(&8 * eps)) (inv eps))`]
                  OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN ANTS_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[OPEN_IN_OPEN_EQ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v0:real^3) IN O` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(ein:A->real^3)((e':real^3->A) v0)` THEN
    USE_THEN "tr" (MP_TAC o SPEC `v0:real^3`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
    MP_TAC(SPECL [`eps:real`; `(ein:A->real^3)((e':real^3->A) v0)`] APX_SVAL_NECK_DOM) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `O' = {v:real^3 | v IN rfs_neck_dom eps /\
                     (e':real^3->A) v IN IMAGE (en:real^3->A) (rfs_neck_dom eps)}` THEN
  SUBGOAL_THEN `open(O':real^3->bool) /\ smooth_map_on O' ((ein:A->real^3) o (e':real^3->A))`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(O:real^3->bool) SUBSET O'` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["O"; "O'"] THEN
    UNDISCH_TAC `apx_slab (--inv(&8 * eps)) (inv eps) SUBSET rfs_neck_dom eps` THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `H = \z. lift(((&1 - smooth_step((apx_sval z - w1) / (w2 - w1))) *
                  apx_sval(((ein:A->real^3) o (e':real^3->A)) z) +
                  smooth_step((apx_sval z - w1) / (w2 - w1)) * (apx_sval z + Delta)) + L)` THEN
  SUBGOAL_THEN `smooth_map_on O' (H:real^3->real^1)` ASSUME_TAC THENL
   [EXPAND_TAC "H" THEN
    MP_TAC(ISPECL [`O':real^3->bool`;
                   `\z. lift((&1 - smooth_step((apx_sval z - w1) / (w2 - w1))) *
                             apx_sval(((ein:A->real^3) o (e':real^3->A)) z) +
                             smooth_step((apx_sval z - w1) / (w2 - w1)) * (apx_sval z + Delta))`;
                   `\z:real^3. lift L`] SMOOTH_MAP_ON_LIFT_ADD) THEN
    REWRITE_TAC[LIFT_DROP; SMOOTH_MAP_ON_CONST] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APX_SPLICE_FORMULA_SMOOTH THEN
    ASM_REWRITE_TAC[ETA_AX] THEN EXPAND_TAC "O'" THEN REWRITE_TAC[IN_ELIM_THM; o_THM] THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    USE_THEN "tr" (MP_TAC o SPEC `z:real^3`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`eps:real`; `(ein:A->real^3)((e':real^3->A) z)`] APX_SVAL_NECK_DOM) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      MP_TAC(SPECL [`eps:real`; `z:real^3`] APX_SVAL_NECK_DOM) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC APX_FRECHET_LOCAL_NZ THEN
  MAP_EVERY EXISTS_TAC [`H:real^3->real^1`; `frechet_derivative (H:real^3->real^1) (at v0)`;
                        `O:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `y:real^3` THEN EXPAND_TAC "O" THEN REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(z:real^3) IN rfs_neck_dom eps /\ --inv(&8 * eps) < apx_sval z`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `apx_slab (--inv(&8 * eps)) (inv eps) SUBSET rfs_neck_dom eps` THEN
        UNDISCH_TAC `(z:real^3) IN apx_slab (--inv(&8 * eps)) (inv eps)` THEN SET_TAC[];
        UNDISCH_TAC `(z:real^3) IN apx_slab (--inv(&8 * eps)) (inv eps)` THEN
        SIMP_TAC[APX_SLAB_SVAL]];
      ALL_TAC] THEN
    USE_THEN "top" (MP_TAC o SPEC `z:real^3`) THEN ANTS_TAC THENL
     [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(e':real^3->A) y IN IMAGE e' (rfs_neck_dom eps)` ASSUME_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(ein:A->real^3)((e':real^3->A) y) = z /\ (ei':A->real^3)(e' y) = y`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[ASSUME `(e':real^3->A) y = (en:real^3->A) z`] THEN CONJ_TAC THENL
       [MATCH_MP_TAC(ASSUME `!z:real^3. z IN rfs_neck_dom eps ==>
                                        (ein:A->real^3)((en:real^3->A) z) = z`) THEN
        FIRST_ASSUM ACCEPT_TAC;
        REWRITE_TAC[GSYM(ASSUME `(e':real^3->A) y = (en:real^3->A) z`)] THEN
        MATCH_MP_TAC(ASSUME `!z:real^3. z IN rfs_neck_dom eps ==>
                                        (ei':A->real^3)((e':real^3->A) z) = z`) THEN
        FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    EXPAND_TAC "H" THEN REWRITE_TAC[apx_splice; o_THM] THEN
    ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `O':real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(O:real^3->bool) SUBSET O'` THEN UNDISCH_TAC `(v0:real^3) IN O` THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(v0:real^3) IN O'` ASSUME_TAC THENL
   [UNDISCH_TAC `(O:real^3->bool) SUBSET O'` THEN UNDISCH_TAC `(v0:real^3) IN O` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(v0:real^3 = vec 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
  MP_TAC(SPEC `v0:real^3` APX_POLAR) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `om = inv(norm v0) % (v0:real^3)` THEN
  ABBREV_TAC `t0 = apx_sval(v0:real^3)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `((H:real^3->real^1) has_derivative frechet_derivative H (at v0)) (at v0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `O':real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(MP (REWRITE_RULE[ASSUME `exp(t0 / sqrt(&2)) % (om:real^3) = v0`]
               (ISPECL [`H:real^3->real^1`; `frechet_derivative (H:real^3->real^1) (at v0)`;
                        `om:real^3`; `t0:real`] APX_RAY_COMPOSE_DERIV))
            (ASSUME `((H:real^3->real^1) has_derivative frechet_derivative H (at v0)) (at v0)`)) THEN
  REWRITE_TAC[ASSUME `frechet_derivative (H:real^3->real^1) (at v0) = (\h. vec 0)`;
              DROP_VEC] THEN DISCH_TAC THEN
  ABBREV_TAC `g = \s. apx_sval((ein:A->real^3)((e':real^3->A)(exp(s / sqrt(&2)) % om)))` THEN
  SUBGOAL_THEN
   `(\s. drop((H:real^3->real^1)(exp(s / sqrt(&2)) % om))) =
    (\t. (&1 - smooth_step((t - w1) / (w2 - w1))) * ((g:real->real) t + L) +
         smooth_step((t - w1) / (w2 - w1)) * (t + (L + Delta)))`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["H"; "g"] THEN REWRITE_TAC[FUN_EQ_THM; LIFT_DROP; o_THM] THEN
    X_GEN_TAC `s:real` THEN ASM_SIMP_TAC[APX_RAY_SVAL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(ein:A->real^3)((e':real^3->A) v0) IN rfs_neck_dom eps` ASSUME_TAC THENL
   [USE_THEN "tr" (MP_TAC o SPEC `v0:real^3`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `g' = sqrt(&2) * ((ein:A->real^3)((e':real^3->A) v0) dot
                     frechet_derivative (ein o e') (at v0) (inv(sqrt(&2)) % v0)) /
                   (ein(e' v0) dot ein(e' v0))` THEN
  SUBGOAL_THEN `((g:real->real) has_real_derivative g') (atreal t0)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(ein:A->real^3) o (e':real^3->A)`; `om:real^3`; `t0:real`]
                  APX_RAY_SVAL_DERIV) THEN
    REWRITE_TAC[o_THM] THEN ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `O':real^3->bool` THEN
        ASM_REWRITE_TAC[];
        MP_TAC(SPECL [`eps:real`; `(ein:A->real^3)((e':real^3->A) v0)`] APX_SVAL_NECK_DOM) THEN
        ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
      MAP_EVERY EXPAND_TAC ["g"; "g'"] THEN REWRITE_TAC[ETA_AX]];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(g' - rho) <= kappa` ASSUME_TAC THENL
   [USE_THEN "al" (MP_TAC o SPEC `inv(sqrt(&2)) % (v0:real^3)`) THEN
    REWRITE_TAC[MP (SPEC `v0:real^3` APX_RAY_UNIT_FACTS) (ASSUME `~(v0:real^3 = vec 0)`);
                SQRT_1; REAL_MUL_RID] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real->real`; `g':real`; `t0:real`; `w1:real`; `w2:real`;
                 `L + Delta`; `L:real`; `Delta:real`; `(D:real->real)((t0 - w1) / (w2 - w1))`;
                 `C:real`; `rho:real`; `kappa:real`; `d0:real`] APX_SPLICE_RAY_POS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(g:real->real) t0 = apx_sval((ein:A->real^3)((e':real^3->A) v0))`
    SUBST1_TAC THENL [EXPAND_TAC "g" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "DC" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `f' = &0` MP_TAC THENL
   [MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
    MAP_EVERY EXISTS_TAC
     [`\t. (&1 - smooth_step((t - w1) / (w2 - w1))) * ((g:real->real) t + L) +
           smooth_step((t - w1) / (w2 - w1)) * (t + (L + Delta))`; `t0:real`] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM((fun th -> REWRITE_TAC[GSYM th]) o check (fun th ->
      is_eq(concl th) && is_abs(lhs(concl th)))) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ASM_REAL_ARITH_TAC]);;

let APX_SPLICE_REGULAR = prove
 (`!top atlas eps (E:real^3->A) (Ei:A->real^3) S e' (ei':A->real^3) en (ein:A->real^3)
    w1 w2 c L Delta d0 rho kappa D C.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\ &0 < eps /\
        mfd_param top atlas S E /\ S SUBSET {y | ~(y = vec 0)} /\
        (!y. y IN S ==> Ei(E y) = y) /\
        mfd_param top atlas (rfs_neck_dom eps) e' /\
        (!z. z IN rfs_neck_dom eps ==> ei'(e' z) = z) /\
        mfd_param top atlas (rfs_neck_dom eps) en /\
        (!z. z IN rfs_neck_dom eps ==> ein(en z) = z) /\
        --inv eps < w1 /\ w1 < w2 /\ w2 < inv(&2 * eps) /\
        (!p. p IN IMAGE E S INTER IMAGE e' (rfs_neck_dom eps)
             ==> apx_sval(ei' p) <= inv(&2 * eps)) /\
        (!p. p IN IMAGE e' (rfs_neck_dom eps) /\ ~(p IN IMAGE E S)
             ==> w2 < apx_sval(ei' p)) /\
        (!z. z IN rfs_neck_dom eps /\ --inv(&8 * eps) < apx_sval z
             ==> en z IN IMAGE E S /\ apx_sval(Ei(en z)) = apx_sval z + L) /\
        (!v. v IN rfs_neck_dom eps /\ w1 <= apx_sval v /\ apx_sval v <= w2
             ==> e' v IN IMAGE en (rfs_neck_dom eps) /\
                 --inv(&8 * eps) < apx_sval(ein(e' v))) /\
        (!v. v IN rfs_neck_dom eps /\ e' v IN IMAGE en (rfs_neck_dom eps)
             ==> abs(apx_sval(ein(e' v)) - apx_sval v - Delta) <= d0) /\
        (!v. v IN rfs_neck_dom eps /\ e' v IN IMAGE en (rfs_neck_dom eps)
             ==> !k. abs(sqrt(&2) * (ein(e' v) dot frechet_derivative (ein o e') (at v) k) /
                         (ein(e' v) dot ein(e' v)) -
                         rho * sqrt(&2) * (v dot k) / (v dot v))
                     <= kappa * sqrt(k dot (cylinder_flow (&0) v ** k))) /\
        c = L + Delta /\ &0 <= d0 /\
        (!t. (smooth_step has_real_derivative D t) (atreal t) /\ abs(D t) <= C) /\
        C * d0 < (w2 - w1) * min (rho - kappa) (&1)
        ==> mfd_regular_on atlas (IMAGE E S UNION IMAGE e' (rfs_neck_dom eps))
                           (apx_splice eps e' ei' Ei w1 w2 c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `inv(&2 * eps) < inv eps` ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_INV2) THEN
    SUBGOAL_THEN `&0 < inv eps` MP_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                 `E:real^3->A`; `Ei:A->real^3`; `S:real^3->bool`; `e':real^3->A`;
                 `ei':A->real^3`; `w1:real`; `w2:real`; `c:real`] APX_SPLICE_SMOOTH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `open_in top (IMAGE (E:real^3->A) S UNION IMAGE (e':real^3->A) (rfs_neck_dom eps))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_UNION THEN CONJ_TAC THEN MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^3))->bool` THEN ASM_MESON_TAC[SUBSET_REFL; GRGD_PARAM_FACTS];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_regular_on] THEN
  MAP_EVERY X_GEN_TAC [`cc:(A->bool)#(A->real^3)`; `x:A`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `(x:A) IN IMAGE (e':real^3->A) (rfs_neck_dom eps) /\ w1 <= apx_sval(ei' x)` THENL
   [FIRST_X_ASSUM(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `v0:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(ei':A->real^3) x = v0` ASSUME_TAC THENL
     [REWRITE_TAC[ASSUME `(x:A) = (e':real^3->A) v0`] THEN
      MATCH_MP_TAC(ASSUME `!z:real^3. z IN rfs_neck_dom eps ==>
                                      (ei':A->real^3)((e':real^3->A) z) = z`) THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `(x:A) IN FST(cc:(A->bool)#(A->real^3)) INTER
                 (IMAGE (E:real^3->A) S UNION IMAGE (e':real^3->A) (rfs_neck_dom eps))` THEN
    UNDISCH_TAC `w1 <= apx_sval((ei':A->real^3) x)` THEN
    REWRITE_TAC[ASSUME `(ei':A->real^3) x = v0`] THEN
    REWRITE_TAC[ASSUME `(x:A) = (e':real^3->A) v0`] THEN DISCH_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC APX_MFD_REGULAR_AT_PARAM THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `rfs_neck_dom eps`;
                          `IMAGE (E:real^3->A) S UNION IMAGE (e':real^3->A) (rfs_neck_dom eps)`] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `w2 < apx_sval(v0:real^3)` THENL
     [MATCH_MP_TAC APX_FRECHET_LOCAL_NZ THEN
      MAP_EVERY EXISTS_TAC [`\z:real^3. lift(apx_sval z + c)`;
                            `\w:real^3. lift(sqrt(&2) * (v0 dot w) / (v0 dot v0))`;
                            `apx_slab w2 (inv eps)`] THEN
      SUBGOAL_THEN `~(v0:real^3 = vec 0)` ASSUME_TAC THENL
       [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
      ASM_SIMP_TAC[APX_SVAL_DERIV_NZ] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[apx_slab; OPEN_ANNULUS];
        REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(SPECL [`eps:real`; `v0:real^3`] APX_SVAL_NECK_DOM) THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN AP_TERM_TAC THEN
        SUBGOAL_THEN `(y:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
         [MP_TAC(SPECL [`w2:real`; `inv eps`; `eps:real`] APX_SLAB_SUB_DOM) THEN
          ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
          ALL_TAC] THEN
        MP_TAC(ISPECL [`eps:real`; `e':real^3->A`; `ei':A->real^3`; `Ei:A->real^3`;
                       `w1:real`; `w2:real`; `c:real`; `(e':real^3->A) y`]
                      APX_SPLICE_VALUES) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
        REWRITE_TAC[MP (SPEC `y:real^3` (ASSUME `!z:real^3. z IN rfs_neck_dom eps ==>
                                                   (ei':A->real^3)((e':real^3->A) z) = z`))
                       (ASSUME `(y:real^3) IN rfs_neck_dom eps`)] THEN
        ANTS_TAC THENL
         [CONJ_TAC THENL
           [MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
            UNDISCH_TAC `(y:real^3) IN apx_slab w2 (inv eps)` THEN
            SIMP_TAC[APX_SLAB_SVAL; REAL_LT_IMP_LE]];
          ASM_REWRITE_TAC[]]];
      MATCH_MP_TAC APX_SPLICE_WINDOW_NZ THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `E:real^3->A`; `S:real^3->bool`; `en:real^3->A`; `ein:A->real^3`;
                            `L:real`; `Delta:real`; `d0:real`; `rho:real`; `kappa:real`;
                            `D:real->real`; `C:real`] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `apx_sval(v0:real^3) <= w2` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `v0:real^3` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun u -> u = `--inv(&8 * eps)`)) (concl th) &&
        can (find_term (fun u -> u = `w2:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((x:A) IN IMAGE (e':real^3->A) (rfs_neck_dom eps)) \/
                apx_sval((ei':A->real^3) x) < w1` ASSUME_TAC THENL
   [UNDISCH_TAC `~((x:A) IN IMAGE (e':real^3->A) (rfs_neck_dom eps) /\
                   w1 <= apx_sval((ei':A->real^3) x))` THEN
    REWRITE_TAC[DE_MORGAN_THM; REAL_NOT_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN IMAGE (E:real^3->A) S` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:A) IN IMAGE (e':real^3->A) (rfs_neck_dom eps)` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:A) IN FST(cc:(A->bool)#(A->real^3)) INTER
                   (IMAGE (E:real^3->A) S UNION IMAGE (e':real^3->A) (rfs_neck_dom eps))` THEN
      UNDISCH_TAC `~((x:A) IN IMAGE (E:real^3->A) S)` THEN SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun u -> u = `w2:real`)) (concl th) &&
      not (can (find_term (fun u -> u = `w1:real`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((x:A) IN IMAGE (e':real^3->A) (rfs_neck_dom eps)) \/
                 apx_sval((ei':A->real^3) x) < w1` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                 `E:real^3->A`; `Ei:A->real^3`; `S:real^3->bool`; `e':real^3->A`;
                 `ei':A->real^3`; `w1:real`; `w2:real`; `c:real`; `x:A`] APX_SPLICE_NEAR_T) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `O:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(E:real^3->A)((Ei:A->real^3) x) = x` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:A) IN IMAGE (E:real^3->A) S` THEN REWRITE_TAC[IN_IMAGE] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun u -> u = `Ei:A->real^3`)) (concl th) &&
      not (can (find_term (fun u -> u = `apx_splice`)) (concl th)) &&
      length(fst(strip_forall(concl th))) = 1)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `SND(cc:(A->bool)#(A->real^3)) x = SND cc ((E:real^3->A)((Ei:A->real^3) x))`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC APX_MFD_REGULAR_AT_PARAM THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                        `S:real^3->bool`;
                        `IMAGE (E:real^3->A) S UNION IMAGE (e':real^3->A) (rfs_neck_dom eps)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~((Ei:A->real^3) x = vec 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `S SUBSET {y:real^3 | ~(y = vec 0)}` THEN
    UNDISCH_TAC `(O:real^3->bool) SUBSET S` THEN
    UNDISCH_TAC `(Ei:A->real^3) x IN O` THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC APX_FRECHET_LOCAL_NZ THEN
  MAP_EVERY EXISTS_TAC [`\z:real^3. lift(apx_sval z + &0)`;
                        `\w:real^3. lift(sqrt(&2) * ((Ei:A->real^3) x dot w) / (Ei x dot Ei x))`;
                        `O:real^3->bool`] THEN
  ASM_SIMP_TAC[APX_SVAL_DERIV_NZ] THEN REWRITE_TAC[REAL_ADD_RID] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM(ASSUME `c:real = L + Delta`)] THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* E4 tools.  Gluing two parametrizations of overlapping slabs                *)
(* along a common coordinate function F (F o P = sval on each piece), and    *)
(* the transport of smoothness/regularity of F to F / sqrt 2.                *)
(* ------------------------------------------------------------------------- *)

let APX_SLAB_UNION = prove
 (`!a1 b1 a2 b2. a1 <= a2 /\ a2 < b1 /\ b1 <= b2
                 ==> apx_slab a1 b1 UNION apx_slab a2 b2 = apx_slab a1 b2 /\
                     apx_slab a1 b1 INTER apx_slab a2 b2 = apx_slab a2 b1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_UNION; IN_INTER; APX_SLAB_SVAL] THEN
  CONJ_TAC THEN X_GEN_TAC `y:real^3` THEN
  ASM_CASES_TAC `y:real^3 = vec 0` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let APX_GLUE_SLABS = prove
 (`!top atlas (Fc:A->real) a1 b1 a2 b2 (P1:real^3->A) P2 P.
        smooth_manifold_atlas top atlas /\ a1 <= a2 /\ a2 < b1 /\ b1 <= b2 /\
        mfd_param top atlas (apx_slab a1 b1) P1 /\ mfd_param top atlas (apx_slab a2 b2) P2 /\
        (!y. y IN apx_slab a1 b1 ==> Fc(P1 y) = apx_sval y) /\
        (!y. y IN apx_slab a2 b2 ==> Fc(P2 y) = apx_sval y) /\
        (!y. y IN apx_slab a2 b1 ==> P1 y = P2 y) /\
        (!y. y IN apx_slab a1 b1 ==> P y = P1 y) /\
        (!y. y IN apx_slab a2 b2 ==> P y = P2 y)
        ==> mfd_param top atlas (apx_slab a1 b2) P`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a1:real`; `b1:real`; `a2:real`; `b2:real`] APX_SLAB_UNION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
  MATCH_MP_TAC MFD_PARAM_UNION THEN
  MAP_EVERY EXISTS_TAC [`P1:real^3->A`; `P2:real^3->A`] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `y:real^3` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN apx_slab a1 b1 /\ (y:real^3) IN apx_slab a2 b2`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `apx_slab a1 b1 INTER apx_slab a2 b2 = apx_slab a2 b1` THEN
      UNDISCH_TAC `(y:real^3) IN apx_slab a2 b1` THEN SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:real^3` THEN
    ASM_SIMP_TAC[]] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_IMAGE] THEN X_GEN_TAC `p:A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y1:real^3` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `y2:real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `apx_sval(y1:real^3) = apx_sval(y2:real^3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(y1:real^3) IN apx_slab a2 b1 /\ (y2:real^3) IN apx_slab a2 b1`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y1:real^3) IN apx_slab a1 b1` THEN
    UNDISCH_TAC `(y2:real^3) IN apx_slab a2 b2` THEN
    REWRITE_TAC[APX_SLAB_SVAL] THEN
    DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `y1:real^3 = y2` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_INJ THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `apx_slab a2 b2`; `P2:real^3->A`] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `y2:real^3` THEN ASM_SIMP_TAC[] THEN ASM SET_TAC[]);;

let APX_MFD_SMOOTH_ON_CMUL = prove
 (`!top atlas W (f:A->real) k.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\ open_in top W /\
        mfd_smooth_on atlas W (\p. lift(f p))
        ==> mfd_smooth_on atlas W (\p. lift(k * f p))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_smooth_on] THEN STRIP_TAC THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER W)`; `k:real`;
                 `(\p. lift((f:A->real) p)) o chart_inv (c:(A->bool)#(A->real^N))`]
                SMOOTH_MAP_ON_LIFT_CMUL) THEN
  ASM_REWRITE_TAC[o_DEF; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
  ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
  ASM_MESON_TAC[MFDM_CHART]);;

let APX_MFD_REGULAR_CMUL = prove
 (`!top atlas W (f:A->real) k.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\ open_in top W /\
        mfd_smooth_on atlas W (\p. lift(f p)) /\ mfd_regular_on atlas W f /\ ~(k = &0)
        ==> mfd_regular_on atlas W (\p. k * f p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_regular_on] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^N)`; `x:A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`c:(A->bool)#(A->real^N)`; `x:A`]) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `G = \y. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y))` THEN
  SUBGOAL_THEN `(G:real^N->real^1) differentiable (at (SND(c:(A->bool)#(A->real^N)) x))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER W)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
      ASM_MESON_TAC[MFDM_CHART];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `mfd_smooth_on (atlas:((A->bool)#(A->real^N))->bool) W
                     (\p. lift((f:A->real) p))` THEN
      REWRITE_TAC[mfd_smooth_on] THEN DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "G" THEN REWRITE_TAC[o_DEF];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\y. lift(k * (f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y))) =
                (\y. k % (G:real^N->real^1) y)` SUBST1_TAC THENL
   [EXPAND_TAC "G" THEN REWRITE_TAC[FUN_EQ_THM; LIFT_CMUL]; ALL_TAC] THEN
  SUBGOAL_THEN `((\y. k % (G:real^N->real^1) y) has_derivative
                 (\h. k % frechet_derivative G (at (SND(c:(A->bool)#(A->real^N)) x)) h))
                (at (SND c x))` ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN REWRITE_TAC[ETA_AX] THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[FUN_EQ_THM; VECTOR_MUL_EQ_0] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM FUN_EQ_THM; ETA_AX]);;

let APX_MFD_SMOOTH_ON_COMPOSE_PARAM = prove
 (`!top atlas W (g:A->real^K) s (e:real^N->A).
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\ open_in top W /\
        mfd_smooth_on atlas W g /\ mfd_param top atlas s e /\ IMAGE e s SUBSET W
        ==> smooth_map_on s (g o e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `s:real^N->bool`; `e:real^N->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ei:A->real^N` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(e:real^N->A) y IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (e:real^N->A) s SUBSET topspace top` THEN
    UNDISCH_TAC `(y:real^N) IN s` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(e:real^N->A) y`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((e:real^N->A) y)` THEN
  STRIP_TAC THEN
  EXISTS_TAC `{z:real^N | z IN s /\ (e:real^N->A) z IN FST(c:(A->bool)#(A->real^N)) INTER W}` THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `continuous_map (subtopology euclidean s,top) (e:real^N->A)` THEN
    REWRITE_TAC[continuous_map; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    DISCH_THEN(MP_TAC o SPEC `FST(c:(A->bool)#(A->real^N)) INTER W` o CONJUNCT2) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_MESON_TAC[MFDM_CHART]; ALL_TAC] THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_EQ];
    REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (e:real^N->A) s SUBSET W` THEN UNDISCH_TAC `(y:real^N) IN s` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `((g:A->real^K) o chart_inv (c:(A->bool)#(A->real^N))) o
              (SND c o (e:real^N->A))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; IN_INTER; o_THM] THEN X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
    AP_TERM_TAC THEN ASM_MESON_TAC[MFDM_CHART];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER W)` THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `continuous_map (subtopology euclidean s,top) (e:real^N->A)` THEN
    REWRITE_TAC[continuous_map; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    DISCH_THEN(MP_TAC o SPEC `FST(c:(A->bool)#(A->real^N)) INTER W` o CONJUNCT2) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_MESON_TAC[MFDM_CHART]; ALL_TAC] THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_EQ];
    MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
    ASM_MESON_TAC[MFDM_CHART];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; o_THM] THEN
    X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `mfd_smooth_map (open_set_atlas s) (atlas:((A->bool)#(A->real^N))->bool)
                   s (e:real^N->A)` THEN
    REWRITE_TAC[mfd_smooth_map; open_set_atlas; IN_SING] THEN
    DISCH_THEN(MP_TAC o SPECL [`(s:real^N->bool,(\x:real^N. x))`;
                               `c:(A->bool)#(A->real^N)`]) THEN
    ASM_REWRITE_TAC[FST; SND; IMAGE_ID; INTER_IDEMPOT] THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `{z:real^N | z IN s /\ (e:real^N->A) z IN FST(c:(A->bool)#(A->real^N))}` THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `SND(c:(A->bool)#(A->real^N)) o (e:real^N->A) o chart_inv (s,(\x:real^N. x))` THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[IN_ELIM_THM; o_THM; MFDM_CHART_INV_ID];
    UNDISCH_TAC `mfd_smooth_on (atlas:((A->bool)#(A->real^N))->bool) W (g:A->real^K)` THEN
    REWRITE_TAC[mfd_smooth_on] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The data of one inductive step (apx_eng_step) and the                     *)
(* analysis of the splice F on W = T UNION N': the comparison of the tube   *)
(* coordinate sigma with the next neck coordinate on T INTER N', the three  *)
(* cases (sigma below the window, the window, N' \ T), and the regions     *)
(* where F is sigma (F < w1 + c - d0) and where F is s' + c                   *)
(* (F > w2 + c + d0).                                                        *)
(* ------------------------------------------------------------------------- *)

let apx_eng_step = new_definition
 `apx_eng_step (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) (eps:real)
               (E:real^3->A) (Ei:A->real^3) (L:real) (en:real^3->A) (ein:A->real^3)
               (e':real^3->A) (ei':A->real^3) (Delta:real) (d0:real) (w1:real)
               (w2:real) <=>
    hausdorff_space top /\ smooth_manifold_atlas top atlas /\ &0 < eps /\ &0 <= L /\
    mfd_param top atlas (apx_slab (--inv eps) (L + inv eps)) E /\
    (!y. y IN apx_slab (--inv eps) (L + inv eps) ==> Ei(E y) = y) /\
    mfd_param top atlas (rfs_neck_dom eps) en /\
    (!z. z IN rfs_neck_dom eps ==> ein(en z) = z) /\
    mfd_param top atlas (rfs_neck_dom eps) e' /\
    (!z. z IN rfs_neck_dom eps ==> ei'(e' z) = z) /\
    (!z. z IN rfs_neck_dom eps /\ --inv(&8 * eps) < apx_sval z
         ==> en z IN IMAGE E (apx_slab (--inv eps) (L + inv eps)) /\
             apx_sval(Ei(en z)) = apx_sval z + L) /\
    (!y. y IN apx_slab (--inv eps) (L + inv eps) /\ L - inv(&8 * eps) < apx_sval y
         ==> ?z. z IN rfs_neck_dom eps /\ E y = en z /\ apx_sval z = apx_sval y - L) /\
    IMAGE en (rfs_neck_dom eps) SUBSET IMAGE E (apx_slab (--inv eps) (L + inv eps)) /\
    IMAGE E (apx_slab (--inv eps) (L + inv eps)) INTER IMAGE e' (rfs_neck_dom eps)
    SUBSET IMAGE en (rfs_neck_dom eps) /\
    IMAGE en (rfs_neck_dom eps) INTER IMAGE e' (rfs_neck_dom eps)
    SUBSET IMAGE e' (apx_slab (--inv eps) (inv(&2 * eps))) /\
    inv(&2 * eps) <= Delta /\ Delta <= &3 * inv(&2 * eps) /\
    &0 <= d0 /\ d0 < inv(&2 * eps) /\
    (!v. v IN rfs_neck_dom eps /\ e' v IN IMAGE en (rfs_neck_dom eps)
         ==> abs(apx_sval(ein(e' v)) - apx_sval v - Delta) <= d0) /\
    (!v. v IN rfs_neck_dom eps /\ apx_sval v < inv eps - Delta - d0
         ==> e' v IN IMAGE en (rfs_neck_dom eps)) /\
    (!z. z IN rfs_neck_dom eps /\ Delta - inv eps + d0 < apx_sval z
         ==> en z IN IMAGE e' (rfs_neck_dom eps)) /\
    inv(&8 * eps) - Delta + d0 + &3 <= w1 /\ --inv eps + d0 + &3 <= w1 /\ w1 < w2 /\
    w2 + d0 + &3 <= inv eps - Delta /\ w2 + d0 + &3 <= --inv(&8 * eps)`;;

(* On N' the splice is a convex combination of sigma and s' + c. *)

let APX_SPLICE_IN_N = prove
 (`!eps (e':real^3->A) ei' Ei w1 w2 c p.
        p IN IMAGE e' (rfs_neck_dom eps)
        ==> abs(apx_splice eps e' ei' Ei w1 w2 c p - (apx_sval(ei' p) + c)) <=
            abs(apx_sval(Ei p) - (apx_sval(ei' p) + c)) /\
            abs(apx_splice eps e' ei' Ei w1 w2 c p - apx_sval(Ei p)) <=
            abs(apx_sval(Ei p) - (apx_sval(ei' p) + c))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[apx_splice] THEN
  MP_TAC(SPEC `(apx_sval((ei':A->real^3) p) - w1) / (w2 - w1)` SMOOTH_STEP_BOUNDS) THEN
  SPEC_TAC(`smooth_step((apx_sval((ei':A->real^3) p) - w1) / (w2 - w1))`,`t:real`) THEN
  SPEC_TAC(`apx_sval((Ei:A->real^3) p)`,`s:real`) THEN
  SPEC_TAC(`apx_sval((ei':A->real^3) p) + c`,`u:real`) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `((&1 - t) * s + t * u) - u = (&1 - t) * (s - u) /\
                ((&1 - t) * s + t * u) - s = t * --(s - u)`
  (fun th -> REWRITE_TAC[th]) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NEG] THEN
  CONJ_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC);;

(* On T INTER N' above the threshold the tube coordinate is the next neck   *)
(* coordinate shifted by c = L + Delta, up to d0.                            *)

let APX_STEP_K = prove
 (`!top atlas eps (E:real^3->A) Ei L en ein e' ei' Delta d0 w1 w2 p.
        apx_eng_step top atlas eps E Ei L en ein e' ei' Delta d0 w1 w2 /\
        p IN IMAGE E (apx_slab (--inv eps) (L + inv eps)) /\
        p IN IMAGE e' (rfs_neck_dom eps) /\
        --inv(&8 * eps) - Delta + d0 < apx_sval(ei' p)
        ==> p IN IMAGE en (rfs_neck_dom eps) /\
            abs(apx_sval(Ei p) - (apx_sval(ei' p) + L + Delta)) <= d0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[apx_eng_step] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(p:A) IN IMAGE en (rfs_neck_dom eps)` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (E:real^3->A) (apx_slab (--inv eps) (L + inv eps)) INTER
                 IMAGE e' (rfs_neck_dom eps) SUBSET IMAGE en (rfs_neck_dom eps)` THEN
    UNDISCH_TAC `(p:A) IN IMAGE E (apx_slab (--inv eps) (L + inv eps))` THEN
    UNDISCH_TAC `(p:A) IN IMAGE e' (rfs_neck_dom eps)` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(p:A) IN IMAGE e' (rfs_neck_dom eps)` THEN REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `(ei':A->real^3)(e' v) = v` (fun th -> REWRITE_TAC[th] THEN
                                                 RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `v:real^3` o check (fun th ->
    is_forall (concl th) &&
    can (find_term (fun t -> t = `ein:A->real^3`)) (concl th) &&
    can (find_term (fun t -> t = `Delta:real`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  UNDISCH_TAC `((e':real^3->A) v) IN IMAGE en (rfs_neck_dom eps)` THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(ein:A->real^3)((e':real^3->A) v) = z` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `--inv(&8 * eps) < apx_sval z` ASSUME_TAC THENL
   [UNDISCH_TAC `abs(apx_sval((ein:A->real^3)((e':real^3->A) v)) - apx_sval v - Delta)
                 <= d0` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `z:real^3` o check (fun th ->
    is_forall (concl th) &&
    can (find_term (fun t -> t = `Ei:A->real^3`)) (concl th) &&
    can (find_term (fun t -> t = `en:real^3->A`)) (concl th) &&
    can (find_term (fun t -> t = `--inv(&8 * eps)`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `abs(apx_sval((ein:A->real^3)((e':real^3->A) v)) - apx_sval v - Delta)
               <= d0` THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* The three cases for a point of W = T UNION N'. *)

let APX_STEP_CASES = prove
 (`!top atlas eps (E:real^3->A) Ei L en ein e' ei' Delta d0 w1 w2 p.
        apx_eng_step top atlas eps E Ei L en ein e' ei' Delta d0 w1 w2 /\
        p IN IMAGE E (apx_slab (--inv eps) (L + inv eps)) UNION
             IMAGE e' (rfs_neck_dom eps)
        ==> (p IN IMAGE E (apx_slab (--inv eps) (L + inv eps)) /\
             apx_splice eps e' ei' Ei w1 w2 (L + Delta) p = apx_sval(Ei p) /\
             (p IN IMAGE e' (rfs_neck_dom eps) ==> apx_sval(ei' p) <= w1)) \/
            (p IN IMAGE E (apx_slab (--inv eps) (L + inv eps)) /\
             p IN IMAGE e' (rfs_neck_dom eps) /\ w1 < apx_sval(ei' p) /\
             abs(apx_sval(Ei p) - (apx_sval(ei' p) + L + Delta)) <= d0 /\
             abs(apx_splice eps e' ei' Ei w1 w2 (L + Delta) p -
                 (apx_sval(ei' p) + L + Delta)) <= d0 /\
             abs(apx_splice eps e' ei' Ei w1 w2 (L + Delta) p - apx_sval(Ei p)) <= d0) \/
            (p IN IMAGE e' (rfs_neck_dom eps) /\
             ~(p IN IMAGE E (apx_slab (--inv eps) (L + inv eps))) /\
             inv eps - Delta - d0 <= apx_sval(ei' p) /\
             apx_splice eps e' ei' Ei w1 w2 (L + Delta) p = apx_sval(ei' p) + L + Delta)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[apx_eng_step] th))
   ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < inv(&8 * eps)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `(p:A) IN IMAGE E (apx_slab (--inv eps) (L + inv eps))` THENL
   [ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(p:A) IN IMAGE e' (rfs_neck_dom eps)` THENL
     [ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `apx_sval((ei':A->real^3) p) <= w1` THENL
       [DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`eps:real`; `e':real^3->A`; `ei':A->real^3`; `Ei:A->real^3`;
                       `w1:real`; `w2:real`; `L + Delta:real`; `p:A`] APX_SPLICE_VALUES) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC;
        ALL_TAC] THEN
      DISJ2_TAC THEN
      SUBGOAL_THEN `w1 < apx_sval((ei':A->real^3) p)` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                     `E:real^3->A`; `Ei:A->real^3`; `L:real`; `en:real^3->A`;
                     `ein:A->real^3`; `e':real^3->A`; `ei':A->real^3`; `Delta:real`;
                     `d0:real`; `w1:real`; `w2:real`; `p:A`] APX_STEP_K) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      MP_TAC(ISPECL [`eps:real`; `e':real^3->A`; `ei':A->real^3`; `Ei:A->real^3`;
                     `w1:real`; `w2:real`; `L + Delta:real`; `p:A`] APX_SPLICE_IN_N) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`eps:real`; `e':real^3->A`; `ei':A->real^3`; `Ei:A->real^3`;
                     `w1:real`; `w2:real`; `L + Delta:real`; `p:A`] APX_SPLICE_VALUES) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:A) IN IMAGE e' (rfs_neck_dom eps)` ASSUME_TAC THENL
   [UNDISCH_TAC `(p:A) IN IMAGE E (apx_slab (--inv eps) (L + inv eps)) UNION
                 IMAGE e' (rfs_neck_dom eps)` THEN
    ASM_REWRITE_TAC[IN_UNION];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(ei':A->real^3) p IN rfs_neck_dom eps /\ (e':real^3->A)(ei' p) = p`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(p:A) IN IMAGE e' (rfs_neck_dom eps)` THEN REWRITE_TAC[IN_IMAGE] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv eps - Delta - d0 <= apx_sval((ei':A->real^3) p)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~((p:A) IN IMAGE E (apx_slab (--inv eps) (L + inv eps)))` THEN
    REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (en:real^3->A) (rfs_neck_dom eps) SUBSET
                 IMAGE E (apx_slab (--inv eps) (L + inv eps))` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `(e':real^3->A)((ei':A->real^3) p) = p`)) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> t = `inv eps - Delta - d0`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`eps:real`; `e':real^3->A`; `ei':A->real^3`; `Ei:A->real^3`;
                 `w1:real`; `w2:real`; `L + Delta:real`; `p:A`] APX_SPLICE_VALUES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
  ASM_REAL_ARITH_TAC);;

(* Below w1 + c - d0 the splice is the tube coordinate, on T. *)

let APX_STEP_LOW = prove
 (`!top atlas eps (E:real^3->A) Ei L en ein e' ei' Delta d0 w1 w2 p.
        apx_eng_step top atlas eps E Ei L en ein e' ei' Delta d0 w1 w2 /\
        p IN IMAGE E (apx_slab (--inv eps) (L + inv eps)) UNION
             IMAGE e' (rfs_neck_dom eps) /\
        apx_splice eps e' ei' Ei w1 w2 (L + Delta) p < w1 + L + Delta - d0
        ==> p IN IMAGE E (apx_slab (--inv eps) (L + inv eps)) /\
            apx_splice eps e' ei' Ei w1 w2 (L + Delta) p = apx_sval(Ei p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o check (fun th -> is_const(fst(strip_comb(concl th))) &&
    fst(dest_const(fst(strip_comb(concl th)))) = "apx_eng_step")) THEN
  REWRITE_TAC[apx_eng_step] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                 `E:real^3->A`; `Ei:A->real^3`; `L:real`; `en:real^3->A`;
                 `ein:A->real^3`; `e':real^3->A`; `ei':A->real^3`; `Delta:real`;
                 `d0:real`; `w1:real`; `w2:real`; `p:A`] APX_STEP_CASES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let APX_STEP_LOW_SIGMA = prove
 (`!top atlas eps (E:real^3->A) Ei L en ein e' ei' Delta d0 w1 w2 p.
        apx_eng_step top atlas eps E Ei L en ein e' ei' Delta d0 w1 w2 /\
        p IN IMAGE E (apx_slab (--inv eps) (L + inv eps)) /\
        apx_sval(Ei p) < w1 + L + Delta - d0
        ==> apx_splice eps e' ei' Ei w1 w2 (L + Delta) p = apx_sval(Ei p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                 `E:real^3->A`; `Ei:A->real^3`; `L:real`; `en:real^3->A`;
                 `ein:A->real^3`; `e':real^3->A`; `ei':A->real^3`; `Delta:real`;
                 `d0:real`; `w1:real`; `w2:real`; `p:A`] APX_STEP_CASES) THEN
  ASM_REWRITE_TAC[IN_UNION] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

(* Above w2 + c + d0 the splice is the next neck coordinate plus c, on N'. *)

let APX_STEP_HIGH = prove
 (`!top atlas eps (E:real^3->A) Ei L en ein e' ei' Delta d0 w1 w2 p.
        apx_eng_step top atlas eps E Ei L en ein e' ei' Delta d0 w1 w2 /\
        p IN IMAGE E (apx_slab (--inv eps) (L + inv eps)) UNION
             IMAGE e' (rfs_neck_dom eps) /\
        w2 + L + Delta + d0 < apx_splice eps e' ei' Ei w1 w2 (L + Delta) p
        ==> p IN IMAGE e' (rfs_neck_dom eps) /\ w2 <= apx_sval(ei' p) /\
            apx_splice eps e' ei' Ei w1 w2 (L + Delta) p = apx_sval(ei' p) + L + Delta`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o check (fun th -> is_const(fst(strip_comb(concl th))) &&
    fst(dest_const(fst(strip_comb(concl th)))) = "apx_eng_step")) THEN
  REWRITE_TAC[apx_eng_step] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                 `E:real^3->A`; `Ei:A->real^3`; `L:real`; `en:real^3->A`;
                 `ein:A->real^3`; `e':real^3->A`; `ei':A->real^3`; `Delta:real`;
                 `d0:real`; `w1:real`; `w2:real`; `p:A`] APX_STEP_CASES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `w2 <= apx_sval((ei':A->real^3) p)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`eps:real`; `e':real^3->A`; `ei':A->real^3`; `Ei:A->real^3`;
                   `w1:real`; `w2:real`; `L + Delta:real`; `p:A`] APX_SPLICE_VALUES) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC] THEN
  (* case (i): F = sigma > w2 + c + d0, so p is high in the tube, hence in N' *)
  SUBGOAL_THEN `&0 < inv(&8 * eps)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?y. y IN apx_slab (--inv eps) (L + inv eps) /\ (p:A) = E y`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(p:A) IN IMAGE E (apx_slab (--inv eps) (L + inv eps))` THEN
    REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `apx_sval((Ei:A->real^3) p) = apx_sval(y:real^3)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
    is_forall (concl th) &&
    can (find_term (fun t -> t = `L - inv(&8 * eps)`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(p:A) IN IMAGE e' (rfs_neck_dom eps)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> t = `Delta - inv eps + d0`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `apx_sval((ei':A->real^3) p) <= w1` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?v. v IN rfs_neck_dom eps /\ (p:A) = e' v` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(p:A) IN IMAGE e' (rfs_neck_dom eps)` THEN
    REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(ei':A->real^3) p = v /\ (ein:A->real^3) p = z` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `(p:A) = e' (v:real^3)` THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[];
      UNDISCH_TAC `(p:A) = E (y:real^3)` THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `v:real^3` o check (fun th ->
    is_forall (concl th) &&
    can (find_term (fun t -> t = `ein:A->real^3`)) (concl th) &&
    can (find_term (fun t -> t = `Delta:real`)) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `z:real^3` THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(ein:A->real^3)((e':real^3->A) v) = z` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `w2 + L + Delta + d0 <
               apx_splice eps (e':real^3->A) ei' Ei w1 w2 (L + Delta) (p:A)` THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* The parametrized part of a closed slab where a smooth function lies in   *)
(* [a,b] is compact.                                                         *)

let APX_PARAM_LEVEL_COMPACT = prove
 (`!top atlas (e:real^3->A) s W (Fc:A->real) a b lo hi.
        smooth_manifold_atlas top atlas /\ mfd_param top atlas s e /\
        open_in top W /\ IMAGE e s SUBSET W /\
        mfd_smooth_on atlas W (\p. lift(Fc p)) /\
        (!y. ~(y = vec 0) /\ lo <= apx_sval y /\ apx_sval y <= hi ==> y IN s)
        ==> compact_in top
              (IMAGE e {y | ~(y = vec 0) /\ lo <= apx_sval y /\ apx_sval y <= hi /\
                            a <= Fc(e y) /\ Fc(e y) <= b})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `s:real^3->bool`; `e:real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ei:A->real^3` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC IMAGE_COMPACT_IN THEN
  EXISTS_TAC `subtopology euclidean (s:real^3->bool)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN] THEN
  FIRST_ASSUM(ASSUME_TAC o check (fun th ->
    is_forall (concl th) && can (find_term (fun t -> t = `lo:real`)) (concl th))) THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `lo:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `((\p. lift((Fc:A->real) p)) o (e:real^3->A)) continuous_on s`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MATCH_MP_TAC APX_MFD_SMOOTH_ON_COMPOSE_PARAM THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `W:A->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`lo:real`; `hi:real`] APX_CSLAB) THEN STRIP_TAC THEN
  ABBREV_TAC `K = cball(vec 0:real^3,exp(hi / sqrt(&2))) DIFF
                  ball(vec 0,exp(lo / sqrt(&2)))` THEN
  SUBGOAL_THEN
   `{y:real^3 | ~(y = vec 0) /\ lo <= apx_sval y /\ apx_sval y <= hi /\
                a <= (Fc:A->real)(e y) /\ Fc((e:real^3->A) y) <= b} =
    {y | y IN K /\ ((\p. lift((Fc:A->real) p)) o e) y IN interval[lift a,lift b]}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; o_THM; IN_INTERVAL_1; LIFT_DROP] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[CONJ_ACI];
    ALL_TAC] THEN
  SUBGOAL_THEN `(K:real^3->bool) SUBSET s` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^3` THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `K:real^3->bool`)) (concl th))) THEN
    STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `lo:real`)) (concl th) &&
      not (can (find_term (fun t -> t = `K:real^3->bool`)) (concl th)))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
   [MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `K:real^3->bool` THEN
    CONJ_TAC THENL [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN ASM_REWRITE_TAC[]; SET_TAC[]];
    MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; CLOSED_INTERVAL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^3->bool` THEN
    REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]]);;

let APX_STEP_F_BOTTOM = prove
 (`!top atlas eps (E:real^3->A) Ei L en ein e' ei' Delta d0 w1 w2 y.
        apx_eng_step top atlas eps E Ei L en ein e' ei' Delta d0 w1 w2 /\
        y IN apx_slab (--inv eps) (L + inv eps) /\ apx_sval y < w1 + L + Delta - d0
        ==> apx_splice eps e' ei' Ei w1 w2 (L + Delta) (E y) = apx_sval y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[apx_eng_step] th))
   STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(Ei:A->real^3)((E:real^3->A) y) = y` ASSUME_TAC THENL
   [MATCH_MP_TAC(ASSUME `!y. y IN apx_slab (--inv eps) (L + inv eps)
                             ==> (Ei:A->real^3)((E:real^3->A) y) = y`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                 `E:real^3->A`; `Ei:A->real^3`; `L:real`; `en:real^3->A`;
                 `ein:A->real^3`; `e':real^3->A`; `ei':A->real^3`; `Delta:real`;
                 `d0:real`; `w1:real`; `w2:real`; `(E:real^3->A) y`] APX_STEP_LOW_SIGMA) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE]);;

let APX_STEP_F_TOP = prove
 (`!top atlas eps (E:real^3->A) Ei L en ein e' ei' Delta d0 w1 w2 v.
        apx_eng_step top atlas eps E Ei L en ein e' ei' Delta d0 w1 w2 /\
        v IN rfs_neck_dom eps /\ w2 <= apx_sval v
        ==> apx_splice eps e' ei' Ei w1 w2 (L + Delta) (e' v) = apx_sval v + L + Delta`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[apx_eng_step] th))
   STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(ei':A->real^3)((e':real^3->A) v) = v` ASSUME_TAC THENL
   [MATCH_MP_TAC(ASSUME `!z. z IN rfs_neck_dom eps
                             ==> (ei':A->real^3)((e':real^3->A) z) = z`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`eps:real`; `e':real^3->A`; `ei':A->real^3`; `Ei:A->real^3`;
                 `w1:real`; `w2:real`; `L + Delta:real`; `(e':real^3->A) v`]
                APX_SPLICE_VALUES) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE]);;

(* The part of W where the splice lies in [a,b], as two parametrized pieces. *)

let APX_STEP_DECOMP = prove
 (`!top atlas eps (E:real^3->A) Ei L en ein e' ei' Delta d0 w1 w2 a b.
        apx_eng_step top atlas eps E Ei L en ein e' ei' Delta d0 w1 w2 /\
        --inv eps < a /\ b < L + inv eps /\ b - (L + Delta) + d0 < inv eps
        ==> {p | p IN IMAGE E (apx_slab (--inv eps) (L + inv eps)) UNION
                      IMAGE e' (rfs_neck_dom eps) /\
                 a <= apx_splice eps e' ei' Ei w1 w2 (L + Delta) p /\
                 apx_splice eps e' ei' Ei w1 w2 (L + Delta) p <= b} =
            IMAGE E {y | ~(y = vec 0) /\ a <= apx_sval y /\ apx_sval y <= b /\
                         a <= apx_splice eps e' ei' Ei w1 w2 (L + Delta) (E y) /\
                         apx_splice eps e' ei' Ei w1 w2 (L + Delta) (E y) <= b} UNION
            IMAGE e' {v | ~(v = vec 0) /\ w1 <= apx_sval v /\
                          apx_sval v <= b - (L + Delta) + d0 /\
                          a <= apx_splice eps e' ei' Ei w1 w2 (L + Delta) (e' v) /\
                          apx_splice eps e' ei' Ei w1 w2 (L + Delta) (e' v) <= b}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[apx_eng_step] th))
   STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNION] THEN X_GEN_TAC `p:A` THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                   `E:real^3->A`; `Ei:A->real^3`; `L:real`; `en:real^3->A`;
                   `ein:A->real^3`; `e':real^3->A`; `ei':A->real^3`; `Delta:real`;
                   `d0:real`; `w1:real`; `w2:real`; `p:A`] APX_STEP_CASES) THEN
    ASM_REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
     [DISJ1_TAC THEN
      UNDISCH_TAC `(p:A) IN IMAGE E (apx_slab (--inv eps) (L + inv eps))` THEN
      REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `y:real^3` THEN
      SUBGOAL_THEN `(Ei:A->real^3) p = y` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(y:real^3) IN apx_slab (--inv eps) (L + inv eps)` THEN
      REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN
      UNDISCH_TAC `a <= apx_splice eps (e':real^3->A) ei' Ei w1 w2 (L + Delta) (p:A)` THEN
      UNDISCH_TAC `apx_splice eps (e':real^3->A) ei' Ei w1 w2 (L + Delta) (p:A) <= b` THEN
      UNDISCH_TAC `apx_splice eps (e':real^3->A) ei' Ei w1 w2 (L + Delta) (p:A) =
                   apx_sval((Ei:A->real^3) p)` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(p:A) = E(y:real^3)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      SIMP_TAC[];
      DISJ2_TAC;
      DISJ2_TAC] THEN
    (SUBGOAL_THEN `(ei':A->real^3) p IN rfs_neck_dom eps /\ (e':real^3->A)(ei' p) = p`
     STRIP_ASSUME_TAC THENL
      [UNDISCH_TAC `(p:A) IN IMAGE e' (rfs_neck_dom eps)` THEN REWRITE_TAC[IN_IMAGE] THEN
       STRIP_TAC THEN ASM_SIMP_TAC[];
       ALL_TAC]) THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN EXISTS_TAC `(ei':A->real^3) p` THEN
    ASM_REWRITE_TAC[] THEN
    (SUBGOAL_THEN `~((ei':A->real^3) p = vec 0)` ASSUME_TAC THENL
      [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC]) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC o
                               REWRITE_RULE[IN_IMAGE; IN_ELIM_THM])) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THENL
   [DISJ1_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC;
    DISJ2_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC]);;

let APX_SVAL_LEVEL_SPHERE = prove
 (`!t. {y:real^3 | ~(y = vec 0) /\ apx_sval y = t} =
       IMAGE (\x. exp(t / sqrt(&2)) % x) (sphere(vec 0,&1))`,
  GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_SPHERE_0] THEN
  X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
   [STRIP_TAC THEN EXISTS_TAC `inv(norm y) % (y:real^3)` THEN
    MP_TAC(ISPEC `y:real^3` APX_POLAR) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `norm(x:real^3) = &1` THEN
      ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; REAL_EXP_NZ] THEN
    ASM_SIMP_TAC[APX_SVAL_EXP_SCALE; APX_SVAL_UNIT] THEN REAL_ARITH_TAC]);;

(* Low level sets of the splice are spheres of the tube chart. *)

let APX_STEP_LEVEL_LOW = prove
 (`!top atlas eps (E:real^3->A) Ei L en ein e' ei' Delta d0 w1 w2 t.
        apx_eng_step top atlas eps E Ei L en ein e' ei' Delta d0 w1 w2 /\
        --inv eps < t /\ t < w1 + L + Delta - d0
        ==> {p | p IN IMAGE E (apx_slab (--inv eps) (L + inv eps)) UNION
                      IMAGE e' (rfs_neck_dom eps) /\
                 apx_splice eps e' ei' Ei w1 w2 (L + Delta) p = t} =
            IMAGE E {y | ~(y = vec 0) /\ apx_sval y = t}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[apx_eng_step] th))
   STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `p:A` THEN EQ_TAC THENL
   [STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                   `E:real^3->A`; `Ei:A->real^3`; `L:real`; `en:real^3->A`;
                   `ein:A->real^3`; `e':real^3->A`; `ei':A->real^3`; `Delta:real`;
                   `d0:real`; `w1:real`; `w2:real`; `p:A`] APX_STEP_LOW) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
    EXISTS_TAC `y:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    SUBGOAL_THEN `(Ei:A->real^3)((E:real^3->A) y) = y` ASSUME_TAC THENL
     [MATCH_MP_TAC(ASSUME `!y. y IN apx_slab (--inv eps) (L + inv eps)
                               ==> (Ei:A->real^3)((E:real^3->A) y) = y`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(y:real^3) IN apx_slab (--inv eps) (L + inv eps)` THEN
    REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `apx_splice eps (e':real^3->A) ei' Ei w1 w2 (L + Delta)
                   ((E:real^3->A) y) = t` THEN
    UNDISCH_TAC `apx_splice eps (e':real^3->A) ei' Ei w1 w2 (L + Delta)
                   ((E:real^3->A) y) = apx_sval((Ei:A->real^3)(E y))` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
  SUBGOAL_THEN `(y:real^3) IN apx_slab (--inv eps) (L + inv eps)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[IN_UNION; FUN_IN_IMAGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                 `E:real^3->A`; `Ei:A->real^3`; `L:real`; `en:real^3->A`;
                 `ein:A->real^3`; `e':real^3->A`; `ei':A->real^3`; `Delta:real`;
                 `d0:real`; `w1:real`; `w2:real`; `y:real^3`] APX_STEP_F_BOTTOM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]);;

(* High level sets of the splice are spheres of the next neck. *)

let APX_STEP_LEVEL_HIGH = prove
 (`!top atlas eps (E:real^3->A) Ei L en ein e' ei' Delta d0 w1 w2 t.
        apx_eng_step top atlas eps E Ei L en ein e' ei' Delta d0 w1 w2 /\
        w2 + L + Delta + d0 < t /\ t < L + Delta + inv eps
        ==> {p | p IN IMAGE E (apx_slab (--inv eps) (L + inv eps)) UNION
                      IMAGE e' (rfs_neck_dom eps) /\
                 apx_splice eps e' ei' Ei w1 w2 (L + Delta) p = t} =
            IMAGE e' {v | ~(v = vec 0) /\ apx_sval v = t - (L + Delta)}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[apx_eng_step] th))
   STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `p:A` THEN EQ_TAC THENL
   [STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                   `E:real^3->A`; `Ei:A->real^3`; `L:real`; `en:real^3->A`;
                   `ein:A->real^3`; `e':real^3->A`; `ei':A->real^3`; `Delta:real`;
                   `d0:real`; `w1:real`; `w2:real`; `p:A`] APX_STEP_HIGH) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `v:real^3` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    SUBGOAL_THEN `(ei':A->real^3) p = v` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
    UNDISCH_TAC `apx_splice eps (e':real^3->A) ei' Ei w1 w2 (L + Delta) (p:A) = t` THEN
    UNDISCH_TAC `apx_splice eps (e':real^3->A) ei' Ei w1 w2 (L + Delta) (p:A) =
                 apx_sval((ei':A->real^3) p) + L + Delta` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
  SUBGOAL_THEN `(v:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[IN_UNION; FUN_IN_IMAGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                 `E:real^3->A`; `Ei:A->real^3`; `L:real`; `en:real^3->A`;
                 `ein:A->real^3`; `e':real^3->A`; `ei':A->real^3`; `Delta:real`;
                 `d0:real`; `w1:real`; `w2:real`; `v:real^3`] APX_STEP_F_TOP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The splice F of a step is smooth and regular on the open                 *)
(* set W = T UNION N' (from APX_SPLICE_SMOOTH and APX_SPLICE_REGULAR).      *)
(* ------------------------------------------------------------------------- *)

let APX_STEP_SMOOTH = prove
 (`!top atlas eps (E:real^3->A) Ei L en ein e' ei' Delta d0 w1 w2.
        apx_eng_step top atlas eps E Ei L en ein e' ei' Delta d0 w1 w2
        ==> open_in top (IMAGE E (apx_slab (--inv eps) (L + inv eps)) UNION
                         IMAGE e' (rfs_neck_dom eps)) /\
            mfd_smooth_on atlas (IMAGE E (apx_slab (--inv eps) (L + inv eps)) UNION
                                 IMAGE e' (rfs_neck_dom eps))
                          (\p. lift(apx_splice eps e' ei' Ei w1 w2 (L + Delta) p)) /\
            (!p. p IN IMAGE E (apx_slab (--inv eps) (L + inv eps)) INTER
                      IMAGE e' (rfs_neck_dom eps)
                 ==> apx_sval(ei' p) <= inv(&2 * eps)) /\
            (!p. p IN IMAGE e' (rfs_neck_dom eps) /\
                 ~(p IN IMAGE E (apx_slab (--inv eps) (L + inv eps)))
                 ==> w2 < apx_sval(ei' p))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[apx_eng_step] th)) THEN
  SUBGOAL_THEN `&0 < inv(&8 * eps) /\ &0 < inv(&2 * eps)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (IMAGE (E:real^3->A) (apx_slab (--inv eps) (L + inv eps))) /\
                open_in top (IMAGE (e':real^3->A) (rfs_neck_dom eps))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `apx_slab (--inv eps) (L + inv eps)`; `E:real^3->A`] GRGD_PARAM_FACTS);
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `rfs_neck_dom eps`; `e':real^3->A`] GRGD_PARAM_FACTS)] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `apx_slab (--inv eps) (L + inv eps) SUBSET {y:real^3 | ~(y = vec 0)}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; APX_SLAB_SVAL] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `--inv eps < w1 /\ w2 < inv(&2 * eps)` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!p. p IN IMAGE (E:real^3->A) (apx_slab (--inv eps) (L + inv eps)) INTER
             IMAGE e' (rfs_neck_dom eps)
        ==> apx_sval((ei':A->real^3) p) <= inv(&2 * eps)`
  ASSUME_TAC THENL
   [X_GEN_TAC `p:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(p:A) IN IMAGE e' (apx_slab (--inv eps) (inv(&2 * eps)))` MP_TAC THENL
     [UNDISCH_TAC `IMAGE (en:real^3->A) (rfs_neck_dom eps) INTER IMAGE e' (rfs_neck_dom eps)
                   SUBSET IMAGE e' (apx_slab (--inv eps) (inv(&2 * eps)))` THEN
      UNDISCH_TAC `IMAGE (E:real^3->A) (apx_slab (--inv eps) (L + inv eps)) INTER
                   IMAGE e' (rfs_neck_dom eps) SUBSET IMAGE en (rfs_neck_dom eps)` THEN
      UNDISCH_TAC `(p:A) IN IMAGE (E:real^3->A) (apx_slab (--inv eps) (L + inv eps)) INTER
                   IMAGE e' (rfs_neck_dom eps)` THEN
      SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(v:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
     [MP_TAC(SPEC `eps:real` APX_QUARTERS_SUB_DOM) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(v:real^3) IN apx_slab (--inv eps) (inv(&2 * eps))` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(ei':A->real^3) p = v` SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(v:real^3) IN apx_slab (--inv eps) (inv(&2 * eps))` THEN
    REWRITE_TAC[APX_SLAB_SVAL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p. p IN IMAGE e' (rfs_neck_dom eps) /\
        ~(p IN IMAGE (E:real^3->A) (apx_slab (--inv eps) (L + inv eps)))
        ==> w2 < apx_sval((ei':A->real^3) p)`
  ASSUME_TAC THENL
   [X_GEN_TAC `p:A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                   `E:real^3->A`; `Ei:A->real^3`; `L:real`; `en:real^3->A`;
                   `ein:A->real^3`; `e':real^3->A`; `ei':A->real^3`; `Delta:real`;
                   `d0:real`; `w1:real`; `w2:real`; `p:A`] APX_STEP_CASES) THEN
    ASM_REWRITE_TAC[IN_UNION] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_UNION THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC APX_SPLICE_SMOOTH THEN EXISTS_TAC `top:A topology` THEN
  ASM_REWRITE_TAC[]);;

let APX_STEP_REGULAR = prove
 (`!top atlas eps (E:real^3->A) Ei L en ein e' ei' Delta d0 w1 w2 rho kappa Ds C.
        apx_eng_step top atlas eps E Ei L en ein e' ei' Delta d0 w1 w2 /\
        (!v. v IN rfs_neck_dom eps /\ e' v IN IMAGE en (rfs_neck_dom eps)
             ==> !k. abs(sqrt(&2) * (ein(e' v) dot frechet_derivative (ein o e') (at v) k) /
                         (ein(e' v) dot ein(e' v)) -
                         rho * sqrt(&2) * (v dot k) / (v dot v))
                     <= kappa * sqrt(k dot (cylinder_flow (&0) v ** k))) /\
        (!t. (smooth_step has_real_derivative Ds t) (atreal t) /\ abs(Ds t) <= C) /\
        C * d0 < (w2 - w1) * min (rho - kappa) (&1)
        ==> mfd_regular_on atlas (IMAGE E (apx_slab (--inv eps) (L + inv eps)) UNION
                                  IMAGE e' (rfs_neck_dom eps))
                           (apx_splice eps e' ei' Ei w1 w2 (L + Delta))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[apx_eng_step] th))
   STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                 `E:real^3->A`; `Ei:A->real^3`; `L:real`; `en:real^3->A`;
                 `ein:A->real^3`; `e':real^3->A`; `ei':A->real^3`; `Delta:real`;
                 `d0:real`; `w1:real`; `w2:real`] APX_STEP_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < inv(&8 * eps)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `apx_slab (--inv eps) (L + inv eps) SUBSET {y:real^3 | ~(y = vec 0)}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; APX_SLAB_SVAL] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `--inv eps < w1 /\ w2 < inv(&2 * eps)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < inv(&2 * eps)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v. v IN rfs_neck_dom eps /\ w1 <= apx_sval v /\ apx_sval v <= w2
        ==> (e':real^3->A) v IN IMAGE en (rfs_neck_dom eps) /\
            --inv(&8 * eps) < apx_sval((ein:A->real^3)(e' v))`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(e':real^3->A) v IN IMAGE en (rfs_neck_dom eps)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall (concl th) &&
        can (find_term (fun t -> t = `inv eps - Delta - d0`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `v:real^3` o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> t = `ein:A->real^3`)) (concl th) &&
      can (find_term (fun t -> t = `Delta:real`)) (concl th) &&
      not (can (find_term (fun t -> t = `frechet_derivative`)) (concl th)))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                 `E:real^3->A`; `Ei:A->real^3`; `apx_slab (--inv eps) (L + inv eps)`;
                 `e':real^3->A`; `ei':A->real^3`; `en:real^3->A`; `ein:A->real^3`;
                 `w1:real`; `w2:real`; `L + Delta:real`; `L:real`; `Delta:real`;
                 `d0:real`; `rho:real`; `kappa:real`; `Ds:real->real`; `C:real`]
                APX_SPLICE_REGULAR) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Annuli as slabs, scaling diffeomorphisms of slabs, the                   *)
(* numerical constants sqrt 2 log 2 and d1 = sqrt 2 log(3/2), and the two   *)
(* neck charts e0' x = E(exp(a/sqrt 2) x), e1' x = e'(exp((b-c)/sqrt 2) x)  *)
(* at the levels a = w1 + c - d0 - 2 and b = w2 + c + d0 + 2 of the splice. *)
(* ------------------------------------------------------------------------- *)

let APX_ANNULUS_AS_SLAB = prove
 (`!r1 r2. &0 < r1 /\ &0 < r2
           ==> annulus r1 r2 = apx_slab (sqrt(&2) * log r1) (sqrt(&2) * log r2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[apx_slab] THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!r. &0 < r ==> exp((sqrt(&2) * log r) / sqrt(&2)) = r`
  (fun th -> ASM_SIMP_TAC[th]) THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(sqrt(&2) * log r) / sqrt(&2) = log r` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < sqrt(&2)` THEN CONV_TAC REAL_FIELD; ASM_SIMP_TAC[EXP_LOG]]);;

let APX_SLAB_SCALE_DIFFEO = prove
 (`!t a b. diffeomorphism_on (apx_slab a b) (apx_slab (a + t) (b + t))
                             (\x:real^3. exp(t / sqrt(&2)) % x)
                             (\x. exp(--t / sqrt(&2)) % x)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`exp(t / sqrt(&2))`; `exp(a / sqrt(&2))`; `exp(b / sqrt(&2))`]
                (INST_TYPE [`:3`,`:N`] SMT_DIFFEO_SCALING_ANNULUS)) THEN
  REWRITE_TAC[REAL_EXP_POS_LT; GSYM REAL_EXP_ADD; GSYM REAL_EXP_NEG] THEN
  REWRITE_TAC[apx_slab] THEN
  SUBGOAL_THEN `t / sqrt(&2) + a / sqrt(&2) = (a + t) / sqrt(&2) /\
                t / sqrt(&2) + b / sqrt(&2) = (b + t) / sqrt(&2) /\
                --(t / sqrt(&2)) = --t / sqrt(&2)`
  (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let APX_LOG_CONSTS = prove
 (`&0 < sqrt(&2) * log(&3 / &2) /\
   sqrt(&2) * log(&3 / &2) < sqrt(&2) * log(&2) /\
   sqrt(&2) * log(&2) <= &3 / &2 /\
   sqrt(&2) * log(&1 / &2) = --(sqrt(&2) * log(&2)) /\
   sqrt(&2) * log(&2 / &3) = --(sqrt(&2) * log(&3 / &2))`,
  SUBGOAL_THEN `&0 < sqrt(&2) /\ sqrt(&2) <= &3 / &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log(&3 / &2) /\ log(&3 / &2) < log(&2) /\ log(&2) <= &1`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      MATCH_MP_TAC LOG_MONO_LT_IMP THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      GEN_REWRITE_TAC RAND_CONV [GSYM LOG_EXP] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      MP_TAC(SPEC `&1` REAL_EXP_LE_X) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 / &2 * &1` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    REWRITE_TAC[REAL_ARITH `&1 / &2 = inv(&2)`] THEN
    SIMP_TAC[LOG_INV; REAL_ARITH `&0 < &2`] THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `&2 / &3 = inv(&3 / &2)` SUBST1_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    SIMP_TAC[LOG_INV; REAL_ARITH `&0 < &3 / &2`] THEN REAL_ARITH_TAC]);;

let APX_ANNULUS_HALF_TWO = prove
 (`annulus (&1 / &2) (&2) =
   apx_slab (--(sqrt(&2) * log(&2))) (sqrt(&2) * log(&2)) :real^3->bool`,
  SIMP_TAC[APX_ANNULUS_AS_SLAB; REAL_ARITH `&0 < &1 / &2 /\ &0 < &2`] THEN
  REWRITE_TAC[APX_LOG_CONSTS]);;

(* The window forces Delta to be large. *)

let APX_STEP_DELTA_BIG = prove
 (`!top atlas eps (E:real^3->A) Ei L en ein e' ei' Delta d0 w1 w2.
        apx_eng_step top atlas eps E Ei L en ein e' ei' Delta d0 w1 w2
        ==> &6 < Delta /\ &0 < inv(&8 * eps) /\ &0 < inv eps`,
  REPEAT GEN_TAC THEN REWRITE_TAC[apx_eng_step] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < inv(&8 * eps) /\ &0 < inv eps` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* The neck chart e0' at the level a of the splice. *)

let APX_STEP_CHART0 = prove
 (`!top atlas eps (E:real^3->A) Ei L en ein e' ei' Delta d0 w1 w2 a.
        apx_eng_step top atlas eps E Ei L en ein e' ei' Delta d0 w1 w2 /\
        a = w1 + L + Delta - d0 - &2
        ==> mfd_neck_chart top atlas (\x. E(exp(a / sqrt(&2)) % x)) /\
            IMAGE (\x. E(exp(a / sqrt(&2)) % x)) (annulus (&1 / &2) (&2)) SUBSET
            IMAGE E (apx_slab (--inv eps) (L + inv eps)) /\
            (!x. x IN annulus (&1 / &2) (&2)
                 ==> apx_splice eps e' ei' Ei w1 w2 (L + Delta)
                       (E(exp(a / sqrt(&2)) % x)) = a + apx_sval x) /\
            {p | p IN IMAGE E (apx_slab (--inv eps) (L + inv eps)) UNION
                      IMAGE e' (rfs_neck_dom eps) /\
                 apx_splice eps e' ei' Ei w1 w2 (L + Delta) p = a} =
            IMAGE (\x. E(exp(a / sqrt(&2)) % x)) (sphere(vec 0,&1))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[apx_eng_step] th) THEN
              STRIP_ASSUME_TAC(MATCH_MP APX_STEP_DELTA_BIG th))
   ASSUME_TAC) THEN
  STRIP_ASSUME_TAC APX_LOG_CONSTS THEN
  REWRITE_TAC[APX_ANNULUS_HALF_TWO; mfd_neck_chart] THEN
  SUBGOAL_THEN
   `!x:real^3. x IN apx_slab (--(sqrt(&2) * log(&2))) (sqrt(&2) * log(&2))
               ==> exp(a / sqrt(&2)) % x IN apx_slab (--inv eps) (L + inv eps) /\
                   apx_sval(exp(a / sqrt(&2)) % x) = a + apx_sval x /\
                   apx_sval(exp(a / sqrt(&2)) % x) < w1 + L + Delta - d0`
  (LABEL_TAC "mem") THENL
   [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[APX_SVAL_EXP_SCALE; VECTOR_MUL_EQ_0; REAL_EXP_NZ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `(\x. (E:real^3->A)(exp(a / sqrt(&2)) % x)) =
                  E o (\x. exp(a / sqrt(&2)) % x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
    MAP_EVERY EXISTS_TAC
     [`apx_slab (--inv eps) (L + inv eps)`;
      `apx_slab (--(sqrt(&2) * log(&2)) + a) (sqrt(&2) * log(&2) + a)`;
      `\x:real^3. exp(--a / sqrt(&2)) % x`] THEN
    ASM_REWRITE_TAC[APX_SLAB_SCALE_DIFFEO] THEN
    MATCH_MP_TAC APX_SLAB_SUBSET THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN
    USE_THEN "mem" (MP_TAC o SPEC `x:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    USE_THEN "mem" (MP_TAC o SPEC `x:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                   `E:real^3->A`; `Ei:A->real^3`; `L:real`; `en:real^3->A`;
                   `ein:A->real^3`; `e':real^3->A`; `ei':A->real^3`; `Delta:real`;
                   `d0:real`; `w1:real`; `w2:real`; `exp(a / sqrt(&2)) % (x:real^3)`]
                  APX_STEP_F_BOTTOM) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                   `E:real^3->A`; `Ei:A->real^3`; `L:real`; `en:real^3->A`;
                   `ein:A->real^3`; `e':real^3->A`; `ei':A->real^3`; `Delta:real`;
                   `d0:real`; `w1:real`; `w2:real`; `a:real`] APX_STEP_LEVEL_LOW) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[APX_SVAL_LEVEL_SPHERE; GSYM IMAGE_o; o_DEF]]);;

(* The neck chart e1' at the level b of the splice. *)

let APX_STEP_CHART1 = prove
 (`!top atlas eps (E:real^3->A) Ei L en ein e' ei' Delta d0 w1 w2 b.
        apx_eng_step top atlas eps E Ei L en ein e' ei' Delta d0 w1 w2 /\
        b = w2 + L + Delta + d0 + &2
        ==> mfd_neck_chart top atlas (\x. e'(exp((b - (L + Delta)) / sqrt(&2)) % x)) /\
            IMAGE (\x. e'(exp((b - (L + Delta)) / sqrt(&2)) % x)) (annulus (&1 / &2) (&2))
            SUBSET IMAGE e' (rfs_neck_dom eps) /\
            (!x. x IN annulus (&1 / &2) (&2)
                 ==> apx_splice eps e' ei' Ei w1 w2 (L + Delta)
                       (e'(exp((b - (L + Delta)) / sqrt(&2)) % x)) = b + apx_sval x) /\
            {p | p IN IMAGE E (apx_slab (--inv eps) (L + inv eps)) UNION
                      IMAGE e' (rfs_neck_dom eps) /\
                 apx_splice eps e' ei' Ei w1 w2 (L + Delta) p = b} =
            IMAGE (\x. e'(exp((b - (L + Delta)) / sqrt(&2)) % x)) (sphere(vec 0,&1))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[apx_eng_step] th) THEN
              STRIP_ASSUME_TAC(MATCH_MP APX_STEP_DELTA_BIG th))
   ASSUME_TAC) THEN
  STRIP_ASSUME_TAC APX_LOG_CONSTS THEN
  REWRITE_TAC[APX_ANNULUS_HALF_TWO; mfd_neck_chart] THEN
  SUBGOAL_THEN
   `!x:real^3. x IN apx_slab (--(sqrt(&2) * log(&2))) (sqrt(&2) * log(&2))
               ==> exp((b - (L + Delta)) / sqrt(&2)) % x IN rfs_neck_dom eps /\
                   apx_sval(exp((b - (L + Delta)) / sqrt(&2)) % x) =
                   (b - (L + Delta)) + apx_sval x /\
                   w2 <= apx_sval(exp((b - (L + Delta)) / sqrt(&2)) % x)`
  (LABEL_TAC "mem") THENL
   [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[APX_SLAB_SVAL; APX_SLAB_NECK_DOM] THEN
    STRIP_TAC THEN
    ASM_SIMP_TAC[APX_SVAL_EXP_SCALE; VECTOR_MUL_EQ_0; REAL_EXP_NZ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `(\x. (e':real^3->A)(exp((b - (L + Delta)) / sqrt(&2)) % x)) =
                  e' o (\x. exp((b - (L + Delta)) / sqrt(&2)) % x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
    MAP_EVERY EXISTS_TAC
     [`rfs_neck_dom eps`;
      `apx_slab (--(sqrt(&2) * log(&2)) + (b - (L + Delta)))
                (sqrt(&2) * log(&2) + (b - (L + Delta)))`;
      `\x:real^3. exp(--(b - (L + Delta)) / sqrt(&2)) % x`] THEN
    ASM_REWRITE_TAC[APX_SLAB_SCALE_DIFFEO] THEN
    REWRITE_TAC[APX_SLAB_NECK_DOM] THEN
    MATCH_MP_TAC APX_SLAB_SUBSET THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN
    USE_THEN "mem" (MP_TAC o SPEC `x:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    USE_THEN "mem" (MP_TAC o SPEC `x:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                   `E:real^3->A`; `Ei:A->real^3`; `L:real`; `en:real^3->A`;
                   `ein:A->real^3`; `e':real^3->A`; `ei':A->real^3`; `Delta:real`;
                   `d0:real`; `w1:real`; `w2:real`;
                   `exp((b - (L + Delta)) / sqrt(&2)) % (x:real^3)`]
                  APX_STEP_F_TOP) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                   `E:real^3->A`; `Ei:A->real^3`; `L:real`; `en:real^3->A`;
                   `ein:A->real^3`; `e':real^3->A`; `ei':A->real^3`; `Delta:real`;
                   `d0:real`; `w1:real`; `w2:real`; `b:real`] APX_STEP_LEVEL_HIGH) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[APX_SVAL_LEVEL_SPHERE; GSYM IMAGE_o; o_DEF]]);;

let APX_STEP_CHARTS_DISJOINT = prove
 (`!top atlas eps (E:real^3->A) Ei L en ein e' ei' Delta d0 w1 w2 a b.
        apx_eng_step top atlas eps E Ei L en ein e' ei' Delta d0 w1 w2 /\
        a = w1 + L + Delta - d0 - &2 /\ b = w2 + L + Delta + d0 + &2
        ==> DISJOINT (IMAGE (\x. E(exp(a / sqrt(&2)) % x)) (annulus (&1 / &2) (&2)))
                     (IMAGE (\x. e'(exp((b - (L + Delta)) / sqrt(&2)) % x))
                            (annulus (&1 / &2) (&2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                 `E:real^3->A`; `Ei:A->real^3`; `L:real`; `en:real^3->A`;
                 `ein:A->real^3`; `e':real^3->A`; `ei':A->real^3`; `Delta:real`;
                 `d0:real`; `w1:real`; `w2:real`; `a:real`] APX_STEP_CHART0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                 `E:real^3->A`; `Ei:A->real^3`; `L:real`; `en:real^3->A`;
                 `ein:A->real^3`; `e':real^3->A`; `ei':A->real^3`; `Delta:real`;
                 `d0:real`; `w1:real`; `w2:real`; `b:real`] APX_STEP_CHART1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_eng_step] o check (fun th ->
    is_const(fst(strip_comb(concl th))) &&
    fst(dest_const(fst(strip_comb(concl th)))) = "apx_eng_step")) THEN
  STRIP_ASSUME_TAC APX_LOG_CONSTS THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
  X_GEN_TAC `p:A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `x':real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `a + apx_sval(x:real^3) = b + apx_sval(x':real^3)` MP_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `apx_splice eps (e':real^3->A) ei' Ei w1 w2 (L + Delta) (p:A)` THEN
    CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN
      FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> concl th =
        `(p:A) = (E:real^3->A)(exp(a / sqrt(&2)) % x)`)) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> concl th =
        `(p:A) = (e':real^3->A)(exp((b - (L + Delta)) / sqrt(&2)) % x')`)) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `(x:real^3) IN annulus (&1 / &2) (&2)` THEN
  UNDISCH_TAC `(x':real^3) IN annulus (&1 / &2) (&2)` THEN
  REWRITE_TAC[APX_ANNULUS_HALF_TWO; APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Conversions between the annulus coordinates of the product               *)
(* chart of SMT_PRODUCT2_STATEMENT and the s-slabs of the tube, and the     *)
(* application of M6b to the splice of one step (APX_STEP_PRODUCT).         *)
(* ------------------------------------------------------------------------- *)

let APX_SQRT2_SCALE_EQS = prove
 (`!s t. (s / sqrt(&2) <= inv(sqrt(&2)) * t <=> s <= t) /\
         (inv(sqrt(&2)) * t <= s / sqrt(&2) <=> t <= s) /\
         (inv(sqrt(&2)) * t = s / sqrt(&2) <=> t = s) /\
         (s / sqrt(&2) < t / sqrt(&2) <=> s < t) /\
         inv(sqrt(&2)) * (s + sqrt(&2) * t) = s / sqrt(&2) + t /\
         s / sqrt(&2) - t / sqrt(&2) = (s - t) / sqrt(&2) /\
         sqrt(&2) * (s / sqrt(&2)) = s`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(sqrt(&2))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!r. r / sqrt(&2) = inv(sqrt(&2)) * r` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_LT_LMUL_EQ; REAL_EQ_MUL_LCANCEL; REAL_LT_IMP_NZ] THEN
  UNDISCH_TAC `&0 < sqrt(&2)` THEN CONV_TAC REAL_FIELD);;

let APX_M6B_ANNULI = prove
 (`(!t. annulus (&2 / &3 * exp(t / sqrt(&2))) (&3 / &2 * exp(t / sqrt(&2))) =
        apx_slab (t - sqrt(&2) * log(&3 / &2)) (t + sqrt(&2) * log(&3 / &2))) /\
   (!t. annulus (&2 / &3) (&3 / &2 * exp(t / sqrt(&2))) =
        apx_slab (--(sqrt(&2) * log(&3 / &2))) (t + sqrt(&2) * log(&3 / &2))) /\
   annulus (&2 / &3) (&3 / &2) =
   apx_slab (--(sqrt(&2) * log(&3 / &2))) (sqrt(&2) * log(&3 / &2)) :real^3->bool`,
  SUBGOAL_THEN `!t. &0 < &2 / &3 * exp(t / sqrt(&2)) /\ &0 < &3 / &2 * exp(t / sqrt(&2))`
  ASSUME_TAC THENL
   [GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN
    REWRITE_TAC[REAL_EXP_POS_LT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[APX_ANNULUS_AS_SLAB; REAL_ARITH `&0 < &2 / &3 /\ &0 < &3 / &2`] THEN
  SIMP_TAC[LOG_MUL; REAL_EXP_POS_LT; REAL_ARITH `&0 < &2 / &3 /\ &0 < &3 / &2`;
           LOG_EXP; REAL_ADD_LDISTRIB; APX_SQRT2_SCALE_EQS; APX_LOG_CONSTS] THEN
  REWRITE_TAC[REAL_ADD_SYM] THEN REWRITE_TAC[real_sub] THEN REWRITE_TAC[REAL_ADD_SYM]);;

let APX_NORM_RANGE_SVAL = prove
 (`!(x:real^3) s. &1 <= norm x /\ norm x <= exp(s / sqrt(&2)) <=>
                  ~(x = vec 0) /\ &0 <= apx_sval x /\ apx_sval x <= s`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `x:real^3 = vec 0` THEN ASM_REWRITE_TAC[NORM_0] THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(x:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= norm(x:real^3) <=> &0 <= apx_sval x` SUBST1_TAC THENL
   [REWRITE_TAC[apx_sval] THEN
    ASM_SIMP_TAC[REAL_LE_MUL_EQ; GSYM LOG_1] THEN
    ASM_SIMP_TAC[LOG_MONO_LE; REAL_ARITH `&0 < &1`];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(x:real^3) <= exp(s / sqrt(&2)) <=> apx_sval x <= s` SUBST1_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM(MATCH_MP EXP_LOG
      (ASSUME `&0 < norm(x:real^3)`))] THEN
    REWRITE_TAC[REAL_EXP_MONO_LE; apx_sval] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2
      (CONJUNCT2(CONJUNCT2(SPECL [`s:real`; `&0`] APX_SQRT2_SCALE_EQS)))))))] THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN REWRITE_TAC[real_div; REAL_MUL_SYM];
    ALL_TAC] THEN
  REWRITE_TAC[]);;

let APX_EXP_SCALE_COMPOSE = prove
 (`!s t (x:real^3). exp(s / sqrt(&2)) % exp(t / sqrt(&2)) % x =
                    exp((s + t) / sqrt(&2)) % x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VECTOR_MUL_ASSOC; GSYM REAL_EXP_ADD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

(* The product chart of M6b in s-slab coordinates of the tube. *)

let APX_M6B_RESCALE = prove
 (`!top atlas (EM0:real^3->A) (g:real^3->real^3) (Fc:A->real) (E:real^3->A)
    (e':real^3->A) W a b c d1.
        smooth_manifold_atlas top atlas /\
        d1 = sqrt(&2) * log(&3 / &2) /\ a < b /\
        mfd_param top atlas (annulus (&2 / &3) (&3 / &2 * exp((b - a) / sqrt(&2)))) EM0 /\
        (!x. x IN annulus (&2 / &3) (&3 / &2) ==> EM0 x = E(exp(a / sqrt(&2)) % x)) /\
        (!x. x IN annulus (&2 / &3 * exp((b - a) / sqrt(&2)))
                          (&3 / &2 * exp((b - a) / sqrt(&2)))
             ==> EM0 x = e'(exp((b - c) / sqrt(&2)) %
                            radial_ext g (exp((a - b) / sqrt(&2)) % x))) /\
        (!x. x IN annulus (&2 / &3) (&3 / &2 * exp((b - a) / sqrt(&2)))
             ==> inv(sqrt(&2)) * Fc(EM0 x) = a / sqrt(&2) + log(norm x)) /\
        {p | p IN W /\ a <= Fc p /\ Fc p <= b} =
        IMAGE EM0 {x | &1 <= norm x /\ norm x <= exp((b - a) / sqrt(&2))}
        ==> mfd_param top atlas (apx_slab (a - d1) (b + d1))
                      (\y. EM0(exp(--a / sqrt(&2)) % y)) /\
            (!y. y IN apx_slab (a - d1) (a + d1) ==> EM0(exp(--a / sqrt(&2)) % y) = E y) /\
            (!y. y IN apx_slab (b - d1) (b + d1)
                 ==> EM0(exp(--a / sqrt(&2)) % y) =
                     e'(radial_ext g (exp(--c / sqrt(&2)) % y))) /\
            (!y. y IN apx_slab (a - d1) (b + d1)
                 ==> Fc(EM0(exp(--a / sqrt(&2)) % y)) = apx_sval y) /\
            {p | p IN W /\ a <= Fc p /\ Fc p <= b} =
            IMAGE (\y. EM0(exp(--a / sqrt(&2)) % y))
                  {y | ~(y = vec 0) /\ a <= apx_sval y /\ apx_sval y <= b}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th =
    `d1 = sqrt(&2) * log(&3 / &2)`)) THEN
  STRIP_ASSUME_TAC APX_LOG_CONSTS THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^3. ~(y = vec 0)
               ==> ~(exp(--a / sqrt(&2)) % y = vec 0) /\
                   apx_sval(exp(--a / sqrt(&2)) % y) = --a + apx_sval y`
  (LABEL_TAC "sc") THENL
   [SIMP_TAC[APX_SVAL_EXP_SCALE; VECTOR_MUL_EQ_0; REAL_EXP_NZ]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `(\y. (EM0:real^3->A)(exp(--a / sqrt(&2)) % y)) =
                  EM0 o (\y. exp(--a / sqrt(&2)) % y)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
    MAP_EVERY EXISTS_TAC
     [`annulus (&2 / &3) (&3 / &2 * exp((b - a) / sqrt(&2))):real^3->bool`;
      `apx_slab ((a - sqrt(&2) * log(&3 / &2)) + --a)
                ((b + sqrt(&2) * log(&3 / &2)) + --a)`;
      `\x:real^3. exp(--(--a) / sqrt(&2)) % x`] THEN
    ASM_REWRITE_TAC[APX_SLAB_SCALE_DIFFEO; APX_M6B_ANNULI] THEN
    MATCH_MP_TAC APX_SLAB_SUBSET THEN REAL_ARITH_TAC;
    X_GEN_TAC `y:real^3` THEN REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN
    USE_THEN "sc" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(E:real^3->A)(exp(a / sqrt(&2)) % exp(--a / sqrt(&2)) % y)` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[APX_M6B_ANNULI; APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[APX_EXP_SCALE_COMPOSE; REAL_ADD_RINV; real_div; REAL_MUL_LZERO;
                  REAL_EXP_0; VECTOR_MUL_LID]];
    X_GEN_TAC `y:real^3` THEN REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN
    USE_THEN "sc" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(e':real^3->A)(exp((b - c) / sqrt(&2)) %
                  radial_ext g (exp((a - b) / sqrt(&2)) % exp(--a / sqrt(&2)) % y))` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[APX_M6B_ANNULI; APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC;
      AP_TERM_TAC THEN REWRITE_TAC[APX_EXP_SCALE_COMPOSE] THEN
      SIMP_TAC[GSYM SMT_RADIAL_EXT_HOMOG; REAL_EXP_POS_LT] THEN
      REWRITE_TAC[APX_EXP_SCALE_COMPOSE] THEN
      AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC];
    X_GEN_TAC `y:real^3` THEN REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN
    USE_THEN "sc" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `exp(--a / sqrt(&2)) % (y:real^3)` o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> t = `Fc:A->real`)) (concl th))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[APX_M6B_ANNULI; APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `apx_sval(exp(--a / sqrt(&2)) % (y:real^3)) =
                  sqrt(&2) * log(norm(exp(--a / sqrt(&2)) % y))` MP_TAC THENL
     [REWRITE_TAC[apx_sval]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < sqrt(&2)` THEN CONV_TAC REAL_FIELD;
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[APX_NORM_RANGE_SVAL; EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `p:A` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `exp(a / sqrt(&2)) % (x:real^3)` THEN
      ASM_SIMP_TAC[APX_SVAL_EXP_SCALE; VECTOR_MUL_EQ_0; REAL_EXP_NZ] THEN
      REWRITE_TAC[APX_EXP_SCALE_COMPOSE; REAL_ADD_LINV; real_div; REAL_MUL_LZERO;
                  REAL_EXP_0; VECTOR_MUL_LID] THEN
      ASM_REAL_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `exp(--a / sqrt(&2)) % (y:real^3)` THEN
      USE_THEN "sc" (MP_TAC o SPEC `y:real^3`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]]);;

(* M6b applied to the splice of one step, in s-slab coordinates. *)

let APX_STEP_PRODUCT = prove
 (`!u top atlas eps (E:real^3->A) Ei L en ein e' ei' Delta d0 w1 w2 rho kappa Ds C
    a b d1.
        SMT_PRODUCT2_STATEMENT (u:A->bool) /\
        apx_eng_step top atlas eps E Ei L en ein e' ei' Delta d0 w1 w2 /\
        (!v. v IN rfs_neck_dom eps /\ e' v IN IMAGE en (rfs_neck_dom eps)
             ==> !k. abs(sqrt(&2) * (ein(e' v) dot frechet_derivative (ein o e') (at v) k) /
                         (ein(e' v) dot ein(e' v)) -
                         rho * sqrt(&2) * (v dot k) / (v dot v))
                     <= kappa * sqrt(k dot (cylinder_flow (&0) v ** k))) /\
        (!t. (smooth_step has_real_derivative Ds t) (atreal t) /\ abs(Ds t) <= C) /\
        C * d0 < (w2 - w1) * min (rho - kappa) (&1) /\
        a = w1 + L + Delta - d0 - &2 /\ b = w2 + L + Delta + d0 + &2 /\
        d1 = sqrt(&2) * log(&3 / &2)
        ==> ?EM g g'.
              mfd_param top atlas (apx_slab (a - d1) (b + d1)) EM /\ sphere_diffeo g g' /\
              (!y. y IN apx_slab (a - d1) (a + d1) ==> EM y = E y) /\
              (!y. y IN apx_slab (b - d1) (b + d1)
                   ==> EM y = e'(radial_ext g (exp(--(L + Delta) / sqrt(&2)) % y))) /\
              (!y. y IN apx_slab (a - d1) (b + d1)
                   ==> apx_splice eps e' ei' Ei w1 w2 (L + Delta) (EM y) = apx_sval y) /\
              {p | p IN IMAGE E (apx_slab (--inv eps) (L + inv eps)) UNION
                        IMAGE e' (rfs_neck_dom eps) /\
                   a <= apx_splice eps e' ei' Ei w1 w2 (L + Delta) p /\
                   apx_splice eps e' ei' Ei w1 w2 (L + Delta) p <= b} =
              IMAGE EM {y | ~(y = vec 0) /\ a <= apx_sval y /\ apx_sval y <= b}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "m6b") (CONJUNCTS_THEN2
    (fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[apx_eng_step] th) THEN
               STRIP_ASSUME_TAC(MATCH_MP APX_STEP_DELTA_BIG th))
    STRIP_ASSUME_TAC)) THEN
  STRIP_ASSUME_TAC APX_LOG_CONSTS THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                 `E:real^3->A`; `Ei:A->real^3`; `L:real`; `en:real^3->A`;
                 `ein:A->real^3`; `e':real^3->A`; `ei':A->real^3`; `Delta:real`;
                 `d0:real`; `w1:real`; `w2:real`] APX_STEP_SMOOTH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                 `E:real^3->A`; `Ei:A->real^3`; `L:real`; `en:real^3->A`;
                 `ein:A->real^3`; `e':real^3->A`; `ei':A->real^3`; `Delta:real`;
                 `d0:real`; `w1:real`; `w2:real`; `rho:real`; `kappa:real`;
                 `Ds:real->real`; `C:real`] APX_STEP_REGULAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                 `E:real^3->A`; `Ei:A->real^3`; `L:real`; `en:real^3->A`;
                 `ein:A->real^3`; `e':real^3->A`; `ei':A->real^3`; `Delta:real`;
                 `d0:real`; `w1:real`; `w2:real`; `a:real`] APX_STEP_CHART0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                 `E:real^3->A`; `Ei:A->real^3`; `L:real`; `en:real^3->A`;
                 `ein:A->real^3`; `e':real^3->A`; `ei':A->real^3`; `Delta:real`;
                 `d0:real`; `w1:real`; `w2:real`; `b:real`] APX_STEP_CHART1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                 `E:real^3->A`; `Ei:A->real^3`; `L:real`; `en:real^3->A`;
                 `ein:A->real^3`; `e':real^3->A`; `ei':A->real^3`; `Delta:real`;
                 `d0:real`; `w1:real`; `w2:real`; `a:real`; `b:real`]
                APX_STEP_CHARTS_DISJOINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ABBREV_TAC `W = IMAGE (E:real^3->A) (apx_slab (--inv eps) (L + inv eps)) UNION
                  IMAGE e' (rfs_neck_dom eps)` THEN
  SUBGOAL_THEN `IMAGE (E:real^3->A) (apx_slab (--inv eps) (L + inv eps)) SUBSET W /\
                IMAGE (e':real^3->A) (rfs_neck_dom eps) SUBSET W`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[SUBSET_UNION]; ALL_TAC] THEN
  SUBGOAL_THEN
   `compact_in top {p | p IN W /\
                        a <= apx_splice eps (e':real^3->A) ei' Ei w1 w2 (L + Delta) p /\
                        apx_splice eps e' ei' Ei w1 w2 (L + Delta) (p:A) <= b}`
  ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                   `E:real^3->A`; `Ei:A->real^3`; `L:real`; `en:real^3->A`;
                   `ein:A->real^3`; `e':real^3->A`; `ei':A->real^3`; `Delta:real`;
                   `d0:real`; `w1:real`; `w2:real`; `a:real`; `b:real`] APX_STEP_DECOMP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC COMPACT_IN_UNION THEN CONJ_TAC THEN
    MATCH_MP_TAC APX_PARAM_LEVEL_COMPACT THENL
     [MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                            `apx_slab (--inv eps) (L + inv eps)`; `W:A->bool`] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[APX_SLAB_SVAL] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                            `rfs_neck_dom eps`; `W:A->bool`] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN X_GEN_TAC `y:real^3` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_smooth_on (atlas:((A->bool)#(A->real^3))->bool) W
      (\x. lift(inv(sqrt(&2)) * apx_splice eps (e':real^3->A) ei' Ei w1 w2 (L + Delta) x)) /\
    mfd_regular_on (atlas:((A->bool)#(A->real^3))->bool) W
      (\p. inv(sqrt(&2)) * apx_splice eps (e':real^3->A) ei' Ei w1 w2 (L + Delta) (p:A))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC APX_MFD_SMOOTH_ON_CMUL THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC APX_MFD_REGULAR_CMUL THEN EXISTS_TAC `top:A topology` THEN
      REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_INV_EQ_0] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (\x. (E:real^3->A)(exp(a / sqrt(&2)) % x)) (annulus (&1 / &2) (&2)) SUBSET W /\
    IMAGE (\x. (e':real^3->A)(exp((b - (L + Delta)) / sqrt(&2)) % x))
          (annulus (&1 / &2) (&2)) SUBSET W`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_TRANS THENL
     [EXISTS_TAC `IMAGE (E:real^3->A) (apx_slab (--inv eps) (L + inv eps))`;
      EXISTS_TAC `IMAGE (e':real^3->A) (rfs_neck_dom eps)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x. x IN annulus (&1 / &2) (&2)
         ==> inv(sqrt(&2)) * apx_splice eps (e':real^3->A) ei' Ei w1 w2 (L + Delta)
                               ((E:real^3->A)(exp(a / sqrt(&2)) % x)) =
             a / sqrt(&2) + log(norm x)) /\
    (!x. x IN annulus (&1 / &2) (&2)
         ==> inv(sqrt(&2)) * apx_splice eps (e':real^3->A) ei' Ei w1 w2 (L + Delta)
                               (e'(exp((b - (L + Delta)) / sqrt(&2)) % x)) =
             b / sqrt(&2) + log(norm x))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o check (fun th ->
        is_forall (concl th) &&
        can (find_term (fun t -> t = `a + apx_sval x`)) (snd(strip_forall(concl th)))));
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o check (fun th ->
        is_forall (concl th) &&
        can (find_term (fun t -> t = `b + apx_sval x`)) (snd(strip_forall(concl th)))))] THEN
    ASM_REWRITE_TAC[apx_sval] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[APX_SQRT2_SCALE_EQS];
    ALL_TAC] THEN
  SUBGOAL_THEN `a < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "m6b" (MP_TAC o REWRITE_RULE[SMT_PRODUCT2_STATEMENT]) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `W:A->bool`;
    `\p:A. inv(sqrt(&2)) * apx_splice eps (e':real^3->A) ei' Ei w1 w2 (L + Delta) p`;
    `\x:real^3. (E:real^3->A)(exp(a / sqrt(&2)) % x)`;
    `\x:real^3. (e':real^3->A)(exp((b - (L + Delta)) / sqrt(&2)) % x)`;
    `a / sqrt(&2)`; `b / sqrt(&2)`]) THEN
  REWRITE_TAC[APX_SQRT2_SCALE_EQS] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `IMAGE (E:real^3->A) (apx_slab (--inv eps) (L + inv eps)) UNION
                 IMAGE e' (rfs_neck_dom eps) = W` THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `EM0:real^3->A` (X_CHOOSE_THEN `g:real^3->real^3`
    (X_CHOOSE_THEN `g':real^3->real^3` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `EM0:real^3->A`; `g:real^3->real^3`;
                 `apx_splice eps (e':real^3->A) ei' Ei w1 w2 (L + Delta)`;
                 `E:real^3->A`; `e':real^3->A`; `W:A->bool`; `a:real`; `b:real`;
                 `L + Delta:real`; `d1:real`] APX_M6B_RESCALE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MAP_EVERY EXISTS_TAC [`\y. (EM0:real^3->A)(exp(--a / sqrt(&2)) % y)`;
                        `g:real^3->real^3`; `g':real^3->real^3`] THEN
  BETA_TAC THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Gluing three slab parametrizations along a coordinate                    *)
(* function (APX_GLUE3), the radial end chart e' o radial_ext g o scale,     *)
(* and the inductive step of the tube construction (APX_STEP_GLUE,          *)
(* APX_TUBE_STEP).                                                           *)
(* ------------------------------------------------------------------------- *)

let APX_RADIAL_FACTS = prove
 (`!(g:real^3->real^3) g' x.
        sphere_diffeo g g'
        ==> norm(radial_ext g x) = norm x /\ norm(radial_ext g' x) = norm x /\
            radial_ext g (radial_ext g' x) = x /\ radial_ext g' (radial_ext g x) = x /\
            apx_sval(radial_ext g x) = apx_sval x /\
            apx_sval(radial_ext g' x) = apx_sval x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sphere_diffeo] THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm(radial_ext (g:real^3->real^3) x) = norm x /\
                norm(radial_ext (g':real^3->real^3) x) = norm x`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMT_RADIAL_EXT_NORM THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[apx_sval] THEN CONJ_TAC THEN MATCH_MP_TAC SMT_RADIAL_EXT_INVERSE THEN
  ASM_SIMP_TAC[]);;

(* The end chart y -> e'(radial_ext g (exp(-c/sqrt 2) y)) on a slab. *)

let APX_RADIAL_PARAM = prove
 (`!top atlas (e:real^3->A) (g:real^3->real^3) g' eps c lo hi.
        smooth_manifold_atlas top atlas /\ mfd_param top atlas (rfs_neck_dom eps) e /\
        sphere_diffeo g g' /\ --inv eps <= lo - c /\ hi - c <= inv eps
        ==> mfd_param top atlas (apx_slab lo hi)
                      (\y. e(radial_ext g (exp(--c / sqrt(&2)) % y)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\y. (e:real^3->A)(radial_ext (g:real^3->real^3) (exp(--c / sqrt(&2)) % y))) =
                (e o radial_ext g) o (\y. exp(--c / sqrt(&2)) % y)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
  MAP_EVERY EXISTS_TAC [`apx_slab (lo + --c) (hi + --c)`; `apx_slab (lo + --c) (hi + --c)`;
                        `\x:real^3. exp(--(--c) / sqrt(&2)) % x`] THEN
  ASM_REWRITE_TAC[APX_SLAB_SCALE_DIFFEO; SUBSET_REFL] THEN
  MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
  MAP_EVERY EXISTS_TAC [`rfs_neck_dom eps`; `apx_slab (lo + --c) (hi + --c)`;
                        `radial_ext (g':real^3->real^3)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[apx_slab] THEN MATCH_MP_TAC SMT_DIFFEO_RADIAL_EXT_ANNULUS THEN
    ASM_REWRITE_TAC[REAL_EXP_POS_LE];
    REWRITE_TAC[APX_SLAB_NECK_DOM] THEN MATCH_MP_TAC APX_SLAB_SUBSET THEN
    ASM_REAL_ARITH_TAC]);;

(* Three slab parametrizations, consecutive ones overlapping and compatible, *)
(* with a common coordinate function, glue to one parametrization.           *)

let APX_GLUE3 = prove
 (`!top atlas (Fc:A->real) (P1:real^3->A) P2 P3 a1 b1 a2 b2 a3 b3 m1 m2.
        smooth_manifold_atlas top atlas /\
        a1 <= a2 /\ a2 < m1 /\ m1 < b1 /\ b1 <= a3 /\ a3 < m2 /\ m2 < b2 /\ b2 <= b3 /\
        mfd_param top atlas (apx_slab a1 b1) P1 /\
        mfd_param top atlas (apx_slab a2 b2) P2 /\
        mfd_param top atlas (apx_slab a3 b3) P3 /\
        (!y. y IN apx_slab a1 b1 ==> Fc(P1 y) = apx_sval y) /\
        (!y. y IN apx_slab a2 b2 ==> Fc(P2 y) = apx_sval y) /\
        (!y. y IN apx_slab a3 b3 ==> Fc(P3 y) = apx_sval y) /\
        (!y. y IN apx_slab a2 b1 ==> P1 y = P2 y) /\
        (!y. y IN apx_slab a3 b2 ==> P2 y = P3 y)
        ==> mfd_param top atlas (apx_slab a1 b3)
              (\y. if apx_sval y < m1 then P1 y
                   else if apx_sval y <= m2 then P2 y else P3 y) /\
            (!y. y IN apx_slab a1 b1
                 ==> (if apx_sval y < m1 then P1 y
                      else if apx_sval y <= m2 then P2 y else P3 y) = P1 y) /\
            (!y. y IN apx_slab a2 b2
                 ==> (if apx_sval y < m1 then P1 y
                      else if apx_sval y <= m2 then P2 y else P3 y) = P2 y) /\
            (!y. y IN apx_slab a3 b3
                 ==> (if apx_sval y < m1 then P1 y
                      else if apx_sval y <= m2 then P2 y else P3 y) = P3 y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `P = \y. if apx_sval y < m1 then (P1:real^3->A) y
                      else if apx_sval y <= m2 then P2 y else P3 y` THEN
  SUBGOAL_THEN `!y:real^3. P y = if apx_sval y < m1 then (P1:real^3->A) y
                                 else if apx_sval y <= m2 then P2 y else P3 y`
  (fun th -> REWRITE_TAC[GSYM th] THEN ASSUME_TAC th) THENL
   [EXPAND_TAC "P" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN apx_slab a1 b1 ==> (P:real^3->A) y = P1 y` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `apx_sval(y:real^3) <= m2` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> t = `apx_slab a2 b1`)) (concl th))) THEN
    ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN apx_slab a2 b2 ==> (P:real^3->A) y = P2 y` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall (concl th) &&
        can (find_term (fun t -> t = `apx_slab a2 b1`)) (concl th))) THEN
      ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> t = `apx_slab a3 b2`)) (concl th))) THEN
    ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN apx_slab a3 b3 ==> (P:real^3->A) y = P3 y` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(apx_sval(y:real^3) < m1)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> t = `apx_slab a3 b2`)) (concl th))) THEN
    ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    is_forall (concl th) && is_eq (snd(strip_forall(concl th))) &&
    can (find_term (fun t -> t = `m2:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `mfd_param top atlas (apx_slab a1 b2) (P:real^3->A)` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_GLUE_SLABS THEN
    MAP_EVERY EXISTS_TAC [`Fc:A->real`; `b1:real`; `a2:real`;
                          `P1:real^3->A`; `P2:real^3->A`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC APX_GLUE_SLABS THEN
  MAP_EVERY EXISTS_TAC [`Fc:A->real`; `b2:real`; `a3:real`;
                        `P:real^3->A`; `P3:real^3->A`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `a1 <= a3 /\ a3 < b2 /\ b2 <= b3` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    ASM_CASES_TAC `apx_sval(y:real^3) < b1` THENL
     [SUBGOAL_THEN `(y:real^3) IN apx_slab a1 b1` ASSUME_TAC THENL
       [UNDISCH_TAC `(y:real^3) IN apx_slab a1 b2` THEN
        REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[]];
      SUBGOAL_THEN `(y:real^3) IN apx_slab a2 b2` ASSUME_TAC THENL
       [UNDISCH_TAC `(y:real^3) IN apx_slab a1 b2` THEN
        REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[]]];
    X_GEN_TAC `y:real^3` THEN REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> t = `apx_slab a3 b3`)) (concl th) &&
      can (find_term (fun t -> t = `P:real^3->A`)) (concl th))) THEN
    ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC]);;

(* The end chart lands in the next neck, and the splice is s there. *)

let APX_STEP_END_CHART = prove
 (`!top atlas eps (E:real^3->A) Ei L en ein e' ei' Delta d0 w1 w2 (g:real^3->real^3) g' y.
        apx_eng_step top atlas eps E Ei L en ein e' ei' Delta d0 w1 w2 /\
        sphere_diffeo g g' /\ ~(y = vec 0) /\
        w2 + L + Delta <= apx_sval y /\ apx_sval y < (L + Delta) + inv eps
        ==> radial_ext g (exp(--(L + Delta) / sqrt(&2)) % y) IN rfs_neck_dom eps /\
            apx_sval(radial_ext g (exp(--(L + Delta) / sqrt(&2)) % y)) =
            apx_sval y - (L + Delta) /\
            apx_splice eps e' ei' Ei w1 w2 (L + Delta)
              (e'(radial_ext g (exp(--(L + Delta) / sqrt(&2)) % y))) = apx_sval y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[apx_eng_step] th) THEN
              STRIP_ASSUME_TAC(MATCH_MP APX_STEP_DELTA_BIG th))
   STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`;
                 `exp(--(L + Delta) / sqrt(&2)) % (y:real^3)`] APX_RADIAL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `v = radial_ext (g:real^3->real^3) (exp(--(L + Delta) / sqrt(&2)) % y)` THEN
  SUBGOAL_THEN `~(v:real^3 = vec 0) /\ apx_sval v = apx_sval y - (L + Delta)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[GSYM NORM_EQ_0] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[NORM_EQ_0; VECTOR_MUL_EQ_0; REAL_EXP_NZ] THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[APX_SVAL_EXP_SCALE] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                 `E:real^3->A`; `Ei:A->real^3`; `L:real`; `en:real^3->A`;
                 `ein:A->real^3`; `e':real^3->A`; `ei':A->real^3`; `Delta:real`;
                 `d0:real`; `w1:real`; `w2:real`; `v:real^3`] APX_STEP_F_TOP) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
                           ASM_REAL_ARITH_TAC];
    DISCH_THEN SUBST1_TAC] THEN
  UNDISCH_TAC `apx_sval(v:real^3) = apx_sval(y:real^3) - (L + Delta)` THEN
  REAL_ARITH_TAC);;

(* Gluing E (below), the M6b chart (middle) and the end chart (above). *)

let APX_STEP_GLUE = prove
 (`!top atlas eps (E:real^3->A) Ei L en ein e' ei' Delta d0 w1 w2 e0 EM
    (g:real^3->real^3) g' a b d1.
        apx_eng_step top atlas eps E Ei L en ein e' ei' Delta d0 w1 w2 /\
        (!y. y IN apx_slab (--inv eps) (inv(&8 * eps)) ==> E y = e0 y) /\
        a = w1 + L + Delta - d0 - &2 /\ b = w2 + L + Delta + d0 + &2 /\
        d1 = sqrt(&2) * log(&3 / &2) /\
        mfd_param top atlas (apx_slab (a - d1) (b + d1)) EM /\ sphere_diffeo g g' /\
        (!y. y IN apx_slab (a - d1) (a + d1) ==> EM y = E y) /\
        (!y. y IN apx_slab (b - d1) (b + d1)
             ==> EM y = e'(radial_ext g (exp(--(L + Delta) / sqrt(&2)) % y))) /\
        (!y. y IN apx_slab (a - d1) (b + d1)
             ==> apx_splice eps e' ei' Ei w1 w2 (L + Delta) (EM y) = apx_sval y) /\
        {p | p IN IMAGE E (apx_slab (--inv eps) (L + inv eps)) UNION
                  IMAGE e' (rfs_neck_dom eps) /\
             a <= apx_splice eps e' ei' Ei w1 w2 (L + Delta) p /\
             apx_splice eps e' ei' Ei w1 w2 (L + Delta) p <= b} =
        IMAGE EM {y | ~(y = vec 0) /\ a <= apx_sval y /\ apx_sval y <= b}
        ==> ?E'. apx_eng_tube top atlas eps e0 e' E' (L + Delta) /\
                 (!y. y IN apx_slab (--inv eps) ((L + Delta) + inv eps)
                      ==> apx_splice eps e' ei' Ei w1 w2 (L + Delta) (E' y) =
                          apx_sval y) /\
                 IMAGE E' (apx_slab (--inv eps) ((L + Delta) + inv eps)) =
                 IMAGE E (apx_slab (--inv eps) (L + inv eps)) UNION
                 IMAGE e' (rfs_neck_dom eps)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[apx_eng_step] th) THEN
              STRIP_ASSUME_TAC(MATCH_MP APX_STEP_DELTA_BIG th))
   STRIP_ASSUME_TAC) THEN
  STRIP_ASSUME_TAC APX_LOG_CONSTS THEN
  SUBGOAL_THEN `&0 < d1 /\ d1 < &3 / &2` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    concl th = `a = w1 + L + Delta - d0 - &2`)) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    concl th = `b = w2 + L + Delta + d0 + &2`)) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    concl th = `d1 = sqrt(&2) * log(&3 / &2)`)) THEN
  SUBGOAL_THEN `mfd_param top atlas (apx_slab (--inv eps) (a + d1)) (E:real^3->A)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN
    EXISTS_TAC `apx_slab (--inv eps) (L + inv eps)` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[apx_slab; OPEN_ANNULUS];
      MATCH_MP_TAC APX_SLAB_SUBSET THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_param top atlas (apx_slab (b - d1) ((L + Delta) + inv eps))
      (\y. (e':real^3->A)(radial_ext g (exp(--(L + Delta) / sqrt(&2)) % y)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APX_RADIAL_PARAM THEN
    MAP_EVERY EXISTS_TAC [`g':real^3->real^3`; `eps:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN apx_slab (b - d1) ((L + Delta) + inv eps)
        ==> apx_splice eps e' ei' Ei w1 w2 (L + Delta)
              ((e':real^3->A)(radial_ext g (exp(--(L + Delta) / sqrt(&2)) % y))) =
            apx_sval y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                   `E:real^3->A`; `Ei:A->real^3`; `L:real`; `en:real^3->A`;
                   `ein:A->real^3`; `e':real^3->A`; `ei':A->real^3`; `Delta:real`;
                   `d0:real`; `w1:real`; `w2:real`; `g:real^3->real^3`;
                   `g':real^3->real^3`; `y:real^3`] APX_STEP_END_CHART) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN apx_slab (--inv eps) (a + d1)
        ==> apx_splice eps e' ei' Ei w1 w2 (L + Delta) ((E:real^3->A) y) = apx_sval y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC APX_STEP_F_BOTTOM THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `en:real^3->A`; `ein:A->real^3`; `d0:real`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:real^3) IN apx_slab (--inv eps) (a + d1)` THEN
    REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `apx_splice eps (e':real^3->A) ei' Ei w1 w2 (L + Delta)`;
                 `E:real^3->A`; `EM:real^3->A`;
                 `\y. (e':real^3->A)(radial_ext g (exp(--(L + Delta) / sqrt(&2)) % y))`;
                 `--inv eps`; `a + d1`; `a - d1`; `b + d1`; `b - d1`;
                 `(L + Delta) + inv eps`; `a:real`; `b:real`] APX_GLUE3) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN apx_slab (--inv eps) ((L + Delta) + inv eps)
        ==> apx_splice eps e' ei' Ei w1 w2 (L + Delta)
              (if apx_sval y < a then (E:real^3->A) y
               else if apx_sval y <= b then EM y
               else (e':real^3->A)(radial_ext g (exp(--(L + Delta) / sqrt(&2)) % y))) =
            apx_sval y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(y:real^3 = vec 0) /\ --inv eps < apx_sval y /\
                  apx_sval y < (L + Delta) + inv eps` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN apx_slab (--inv eps) ((L + Delta) + inv eps)` THEN
      SIMP_TAC[APX_SLAB_SVAL];
      ALL_TAC] THEN
    ASM_CASES_TAC `apx_sval(y:real^3) < a + d1` THENL
     [SUBGOAL_THEN `(y:real^3) IN apx_slab (--inv eps) (a + d1)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[APX_SLAB_SVAL]; ALL_TAC] THEN
      FIRST_ASSUM((fun th -> REWRITE_TAC[MP (SPEC `y:real^3` th)
        (ASSUME `(y:real^3) IN apx_slab (--inv eps) (a + d1)`)]) o check (fun th ->
        is_forall (concl th) &&
        can (find_term (fun t -> t = `apx_slab (--inv eps) (a + d1)`)) (concl th) &&
        can (find_term (fun t -> t = `EM:real^3->A`)) (concl th))) THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall (concl th) &&
        can (find_term (fun t -> t = `apx_slab (--inv eps) (a + d1)`)) (concl th) &&
        not (can (find_term (fun t -> t = `EM:real^3->A`)) (concl th)))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `apx_sval(y:real^3) < b + d1` THENL
     [SUBGOAL_THEN `(y:real^3) IN apx_slab (a - d1) (b + d1)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_ASSUM((fun th -> REWRITE_TAC[MP (SPEC `y:real^3` th)
        (ASSUME `(y:real^3) IN apx_slab (a - d1) (b + d1)`)]) o check (fun th ->
        is_forall (concl th) &&
        can (find_term (fun t -> t = `apx_slab (a - d1) (b + d1)`)) (concl th) &&
        is_cond (lhs(snd(dest_imp(snd(dest_forall(concl th)))))))) THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall (concl th) &&
        can (find_term (fun t -> t = `apx_slab (a - d1) (b + d1)`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_splice")) (concl th) &&
        not (can (find_term (fun t -> t = `EM:real^3->A`)) (rhs(snd(dest_imp(snd(dest_forall(concl th))))))))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^3) IN apx_slab (b - d1) ((L + Delta) + inv eps)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[MP (SPEC `y:real^3` th)
      (ASSUME `(y:real^3) IN apx_slab (b - d1) ((L + Delta) + inv eps)`)]) o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> t = `apx_slab (b - d1) ((L + Delta) + inv eps)`)) (concl th) &&
      is_cond (lhs(snd(dest_imp(snd(dest_forall(concl th)))))))) THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> t = `apx_slab (b - d1) ((L + Delta) + inv eps)`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_splice")) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `\y. if apx_sval y < a then (E:real^3->A) y
                  else if apx_sval y <= b then EM y
                  else (e':real^3->A)(radial_ext g (exp(--(L + Delta) / sqrt(&2)) % y))` THEN
  REWRITE_TAC[apx_eng_tube] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(E:real^3->A) y` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall (concl th) &&
        can (find_term (fun t -> t = `apx_slab (--inv eps) (a + d1)`)) (concl th) &&
        can (find_term (fun t -> t = `EM:real^3->A`)) (concl th))) THEN
      UNDISCH_TAC `(y:real^3) IN apx_slab (--inv eps) (inv(&8 * eps))` THEN
      REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `g':real^3->real^3`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> t = `apx_slab (b - d1) ((L + Delta) + inv eps)`)) (concl th) &&
      can (find_term (fun t -> t = `EM:real^3->A`)) (concl th))) THEN
    UNDISCH_TAC `(y:real^3) IN apx_slab ((L + Delta) - inv(&8 * eps)) ((L + Delta) + inv eps)` THEN
    REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the image *)
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN
    REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN
    ASM_CASES_TAC `apx_sval(y:real^3) < a` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    COND_CASES_TAC THENL
     [SUBGOAL_THEN `(EM:real^3->A) y IN
                    IMAGE EM {y | ~(y = vec 0) /\ a <= apx_sval y /\ apx_sval y <= b}`
      MP_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_ELIM_THM] THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      FIRST_ASSUM((fun th -> REWRITE_TAC[GSYM th]) o check (fun th ->
        is_eq (concl th) && is_comb(rhs(concl th)) &&
        can (find_term (fun t -> t = `EM:real^3->A`)) (rhs(concl th)) &&
        not (is_forall (concl th)))) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[];
      REWRITE_TAC[IN_UNION] THEN DISJ2_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                     `E:real^3->A`; `Ei:A->real^3`; `L:real`; `en:real^3->A`;
                     `ein:A->real^3`; `e':real^3->A`; `ei':A->real^3`; `Delta:real`;
                     `d0:real`; `w1:real`; `w2:real`; `g:real^3->real^3`;
                     `g':real^3->real^3`; `y:real^3`] APX_STEP_END_CHART) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `p:A` THEN DISCH_TAC THEN
  REWRITE_TAC[IN_IMAGE] THEN
  ASM_CASES_TAC `apx_splice eps (e':real^3->A) ei' Ei w1 w2 (L + Delta) (p:A) < a` THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                   `E:real^3->A`; `Ei:A->real^3`; `L:real`; `en:real^3->A`;
                   `ein:A->real^3`; `e':real^3->A`; `ei':A->real^3`; `Delta:real`;
                   `d0:real`; `w1:real`; `w2:real`; `p:A`] APX_STEP_LOW) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `y:real^3` THEN
    SUBGOAL_THEN `(Ei:A->real^3) p = y` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(y:real^3) IN apx_slab (--inv eps) (L + inv eps)` THEN
    REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN
    SUBGOAL_THEN `apx_sval(y:real^3) < a` ASSUME_TAC THENL
     [UNDISCH_TAC `apx_splice eps (e':real^3->A) ei' Ei w1 w2 (L + Delta) (p:A) < a` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `apx_splice eps (e':real^3->A) ei' Ei w1 w2 (L + Delta) (p:A) <= b` THENL
   [SUBGOAL_THEN `(p:A) IN
                  IMAGE EM {y | ~(y = vec 0) /\ a <= apx_sval y /\ apx_sval y <= b}`
    MP_TAC THENL
     [FIRST_ASSUM((fun th -> REWRITE_TAC[GSYM th]) o check (fun th ->
        is_eq (concl th) && is_comb(rhs(concl th)) &&
        can (find_term (fun t -> t = `EM:real^3->A`)) (rhs(concl th)) &&
        not (is_forall (concl th)))) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN
    SUBGOAL_THEN `~(apx_sval(y:real^3) < a)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                 `E:real^3->A`; `Ei:A->real^3`; `L:real`; `en:real^3->A`;
                 `ein:A->real^3`; `e':real^3->A`; `ei':A->real^3`; `Delta:real`;
                 `d0:real`; `w1:real`; `w2:real`; `p:A`] APX_STEP_HIGH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(ei':A->real^3) p = v` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `v:real^3`] APX_RADIAL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(v:real^3 = vec 0) /\ abs(apx_sval v) < inv eps` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
  SUBGOAL_THEN `~(radial_ext (g':real^3->real^3) v = vec 0)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NORM_EQ_0] THEN ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[NORM_EQ_0];
    ALL_TAC] THEN
  EXISTS_TAC `exp((L + Delta) / sqrt(&2)) % radial_ext (g':real^3->real^3) v` THEN
  ASM_SIMP_TAC[APX_SVAL_EXP_SCALE; APX_SLAB_SVAL; VECTOR_MUL_EQ_0; REAL_EXP_NZ] THEN
  SUBGOAL_THEN `~((L + Delta) + apx_sval(v:real^3) < a) /\
                ~((L + Delta) + apx_sval(v:real^3) <= b) /\
                --inv eps < (L + Delta) + apx_sval v /\
                (L + Delta) + apx_sval v < (L + Delta) + inv eps`
  (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `apx_splice eps (e':real^3->A) ei' Ei w1 w2 (L + Delta) (p:A) =
                 apx_sval((ei':A->real^3) p) + L + Delta` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(apx_splice eps (e':real^3->A) ei' Ei w1 w2 (L + Delta) (p:A) <= b)` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[APX_EXP_SCALE_COMPOSE] THEN
  REWRITE_TAC[REAL_ARITH `--(L + Delta) + L + Delta = &0`; real_div; REAL_MUL_LZERO;
              REAL_EXP_0; VECTOR_MUL_LID] THEN
  ASM_REWRITE_TAC[]);;

(* The inductive step: a step datum extends the tube by the next neck. *)

let APX_TUBE_STEP = prove
 (`!u top atlas eps (E:real^3->A) Ei L en ein e' ei' Delta d0 w1 w2 e0 rho kappa Ds C.
        SMT_PRODUCT2_STATEMENT (u:A->bool) /\
        apx_eng_step top atlas eps E Ei L en ein e' ei' Delta d0 w1 w2 /\
        (!y. y IN apx_slab (--inv eps) (inv(&8 * eps)) ==> E y = e0 y) /\
        (!v. v IN rfs_neck_dom eps /\ e' v IN IMAGE en (rfs_neck_dom eps)
             ==> !k. abs(sqrt(&2) * (ein(e' v) dot frechet_derivative (ein o e') (at v) k) /
                         (ein(e' v) dot ein(e' v)) -
                         rho * sqrt(&2) * (v dot k) / (v dot v))
                     <= kappa * sqrt(k dot (cylinder_flow (&0) v ** k))) /\
        (!t. (smooth_step has_real_derivative Ds t) (atreal t) /\ abs(Ds t) <= C) /\
        C * d0 < (w2 - w1) * min (rho - kappa) (&1)
        ==> ?E'. apx_eng_tube top atlas eps e0 e' E' (L + Delta) /\
                 (!y. y IN apx_slab (--inv eps) ((L + Delta) + inv eps)
                      ==> apx_splice eps e' ei' Ei w1 w2 (L + Delta) (E' y) =
                          apx_sval y) /\
                 IMAGE E' (apx_slab (--inv eps) ((L + Delta) + inv eps)) =
                 IMAGE E (apx_slab (--inv eps) (L + inv eps)) UNION
                 IMAGE e' (rfs_neck_dom eps)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u:A->bool`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `eps:real`; `E:real^3->A`; `Ei:A->real^3`; `L:real`; `en:real^3->A`;
                 `ein:A->real^3`; `e':real^3->A`; `ei':A->real^3`; `Delta:real`;
                 `d0:real`; `w1:real`; `w2:real`; `rho:real`; `kappa:real`;
                 `Ds:real->real`; `C:real`; `w1 + L + Delta - d0 - &2`;
                 `w2 + L + Delta + d0 + &2`; `sqrt(&2) * log(&3 / &2)`]
                APX_STEP_PRODUCT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `EM:real^3->A` (X_CHOOSE_THEN `g:real^3->real^3`
    (X_CHOOSE_THEN `g':real^3->real^3` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `eps:real`; `E:real^3->A`; `Ei:A->real^3`; `L:real`; `en:real^3->A`;
                 `ein:A->real^3`; `e':real^3->A`; `ei':A->real^3`; `Delta:real`;
                 `d0:real`; `w1:real`; `w2:real`; `e0:real^3->A`; `EM:real^3->A`;
                 `g:real^3->real^3`; `g':real^3->real^3`; `w1 + L + Delta - d0 - &2`;
                 `w2 + L + Delta + d0 + &2`; `sqrt(&2) * log(&3 / &2)`]
                APX_STEP_GLUE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Ingredients of the chain induction: alignment of any two                  *)
(* necks (APX_PAIR_ALIGN), the exactness facts of a tube in the form of the  *)
(* step datum, the window arithmetic, and the scale bound for rho - kappa.   *)
(* ------------------------------------------------------------------------- *)

let APX_PAIR_ALIGN = prove
 (`!alpha1 eps1.
     &0 < alpha1 /\ alpha1 <= &1 / &4096 /\ &0 < eps1 /\ eps1 <= alpha1 /\
     (!top atlas (g:A->real^3^3) eps x (e:real^3->A) y.
        &0 < eps /\ eps <= eps1 /\ riemannian_metric atlas g /\
        rfs_neck (top,atlas) g eps x e /\ y IN rfs_neck_dom eps
        ==> abs(lscalar (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y - &1)
            <= alpha1 /\
            (!w. abs(lricci (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y w w -
                     lricci (cylinder_flow (&0)) y w w)
                 <= alpha1 * (w dot (cylinder_flow (&0) y ** w))))
     ==> !top atlas (g:A->real^3^3) eps x (e:real^3->A) x' e' (ei:A->real^3).
           &0 < eps /\ eps <= eps1 /\ riemannian_metric atlas g /\
           rfs_neck (top,atlas) g eps x e /\ rfs_neck (top,atlas) g eps x' e' /\
           (!z. z IN rfs_neck_dom eps ==> ei(e z) = z)
           ==> ?rho. apx_eng_align eps e ei e' rho (&7 * sqrt alpha1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`alpha1:real`; `eps1:real`] APX_TRANSITION_DERIV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "td") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `sqrt alpha1 <= &1 / &64 /\ &0 <= sqrt alpha1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `?v. v IN rfs_neck_dom eps /\
                     (e':real^3->A) v IN IMAGE e (rfs_neck_dom eps)` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `v0:real^3` STRIP_ASSUME_TAC) THEN
    USE_THEN "td" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `x':A`; `e':real^3->A`;
      `ei:A->real^3`; `v0:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
    EXISTS_TAC `sqrt(mfd_scalar atlas (g:A->real^3^3) x / mfd_scalar atlas g x')` THEN
    REWRITE_TAC[apx_eng_align] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&1 / &2` THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_RSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN
      USE_THEN "td" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
        `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `x':A`; `e':real^3->A`;
        `ei:A->real^3`; `v:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `sg:real` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) o
                 CONJUNCT2) THEN
      EXISTS_TAC `sg:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:real^3` THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `k:real^3`) THEN REWRITE_TAC[REAL_MUL_ASSOC]];
    EXISTS_TAC `&1` THEN REWRITE_TAC[apx_eng_align] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]]]);;

(* The exactness facts of a tube, in the form used by the step datum. *)

let APX_TUBE_EXACT_FACTS = prove
 (`!top atlas eps (e0:real^3->A) en E L (Ei:A->real^3).
        &0 < eps /\ apx_eng_tube top atlas eps e0 en E L /\
        (!y. y IN apx_slab (--inv eps) (L + inv eps) ==> Ei(E y) = y)
        ==> (!z. z IN rfs_neck_dom eps /\ --inv(&8 * eps) < apx_sval z
                 ==> en z IN IMAGE E (apx_slab (--inv eps) (L + inv eps)) /\
                     apx_sval(Ei(en z)) = apx_sval z + L) /\
            (!y. y IN apx_slab (--inv eps) (L + inv eps) /\ L - inv(&8 * eps) < apx_sval y
                 ==> ?z. z IN rfs_neck_dom eps /\ E y = en z /\
                         apx_sval z = apx_sval y - L)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < inv(&8 * eps) /\ inv(&8 * eps) <= inv eps` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_INV_MUL] THEN
    SUBGOAL_THEN `&0 < inv eps` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= L` ASSUME_TAC THENL
   [UNDISCH_TAC `apx_eng_tube top atlas eps (e0:real^3->A) en E L` THEN
    REWRITE_TAC[apx_eng_tube] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                   `e0:real^3->A`; `en:real^3->A`; `E:real^3->A`; `L:real`] APX_TUBE_TOP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(y:real^3) IN apx_slab (--inv eps) (L + inv eps)` ASSUME_TAC THENL
     [MP_TAC(SPECL [`L - inv(&8 * eps)`; `L + inv eps`; `--inv eps`; `L + inv eps`]
                   APX_SLAB_SUBSET) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `(E:real^3->A) y = (en:real^3->A) z` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  UNDISCH_TAC `apx_eng_tube top atlas eps (e0:real^3->A) en E L` THEN
  REWRITE_TAC[apx_eng_tube] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `f':real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0) /\ apx_sval y < L + inv eps` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN apx_slab (--inv eps) (L + inv eps)` THEN
    SIMP_TAC[APX_SLAB_SVAL];
    ALL_TAC] THEN
  EXISTS_TAC `radial_ext (f:real^3->real^3) (exp(--L / sqrt(&2)) % y)` THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `f':real^3->real^3`;
                 `exp(--L / sqrt(&2)) % (y:real^3)`] APX_RADIAL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `apx_sval(radial_ext (f:real^3->real^3) (exp(--L / sqrt(&2)) % y)) =
                apx_sval y - L /\
                ~(radial_ext (f:real^3->real^3) (exp(--L / sqrt(&2)) % y) = vec 0)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_SIMP_TAC[APX_SVAL_EXP_SCALE] THEN REAL_ARITH_TAC;
      REWRITE_TAC[GSYM NORM_EQ_0] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[NORM_EQ_0; VECTOR_MUL_EQ_0; REAL_EXP_NZ] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[APX_SLAB_SVAL];
    ASM_SIMP_TAC[APX_SVAL_EXP_SCALE] THEN REAL_ARITH_TAC]);;

(* The window of a step and its arithmetic. *)

let APX_WINDOW_ARITH = prove
 (`!eps Delta d0 w1 w2.
        &0 < eps /\ inv(&2 * eps) <= Delta /\ Delta <= &3 * inv(&2 * eps) /\
        &0 <= d0 /\ &32 * d0 <= inv eps /\ &96 <= inv eps /\
        w1 = max (inv(&8 * eps) - Delta) (--(&7 * inv(&8 * eps))) + d0 + &3 /\
        w2 = min (inv eps - Delta) (--inv(&8 * eps)) - d0 - &3
        ==> inv(&8 * eps) - Delta + d0 + &3 <= w1 /\ --inv eps + d0 + &3 <= w1 /\
            w1 < w2 /\ w2 + d0 + &3 <= inv eps - Delta /\
            w2 + d0 + &3 <= --inv(&8 * eps) /\ inv eps / &8 <= w2 - w1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_INV_MUL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < inv eps` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN
  UNDISCH_TAC `inv(&2) * inv eps <= Delta` THEN
  UNDISCH_TAC `Delta <= &3 * inv(&2) * inv eps` THEN
  UNDISCH_TAC `&32 * d0 <= inv eps` THEN UNDISCH_TAC `&96 <= inv eps` THEN
  UNDISCH_TAC `&0 <= d0` THEN
  SPEC_TAC(`inv eps`,`x:real`) THEN GEN_TAC THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

let APX_RHO_KAPPA = prove
 (`!r alpha1. &0 <= alpha1 /\ sqrt alpha1 <= &1 / &64 /\ abs(r - &1) <= &4 * alpha1
              ==> &1 / &2 <= min (sqrt r - &7 * sqrt alpha1) (&1) /\
                  &7 * sqrt alpha1 < sqrt r /\ &0 <= &7 * sqrt alpha1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `alpha1 <= &1 / &4096` ASSUME_TAC THENL
   [SUBGOAL_THEN `alpha1 = sqrt alpha1 pow 2` SUBST1_TAC THENL
     [ASM_SIMP_TAC[SQRT_POW_2]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 / &64) pow 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[SQRT_POS_LE];
      CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN `&61 / &100 <= sqrt r` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt alpha1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let APX_REG_CONST = prove
 (`!eps C s d0 w1 w2 rho kappa.
        &0 < eps /\ &0 < C /\ &0 <= s /\ C * s <= &1 / &2560 /\
        d0 = &80 * s * inv eps /\ inv eps / &8 <= w2 - w1 /\
        &1 / &2 <= min (rho - kappa) (&1)
        ==> C * d0 < (w2 - w1) * min (rho - kappa) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < inv eps` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `inv eps / &8 * &1 / &2 <= (w2 - w1) * min (rho - kappa) (&1)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `C * d0 = &80 * (C * s) * inv eps` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&80 * (C * s) * inv eps <= &80 * (&1 / &2560) * inv eps` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  UNDISCH_TAC `&0 < inv eps` THEN REAL_ARITH_TAC);;

let APX_UNIONS_UPTO_SUC = prove
 (`!(f:num->A->bool) m. UNIONS {f i | i <= m + 1} = UNIONS {f i | i <= m} UNION f(m + 1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_UNIONS; IN_UNION; IN_ELIM_THM] THEN
  X_GEN_TAC `p:A` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `t:A->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    ASM_CASES_TAC `i = m + 1` THENL
     [DISJ2_TAC THEN ASM_MESON_TAC[];
      DISJ1_TAC THEN EXISTS_TAC `t:A->bool` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    STRIP_TAC THENL
     [EXISTS_TAC `t:A->bool` THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `i:num` THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      EXISTS_TAC `(f:num->A->bool)(m + 1)` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `m + 1` THEN REWRITE_TAC[LE_REFL]]]);;

(* ------------------------------------------------------------------------- *)
(* The C^0 comparison carried through the chain induction.                 *)
(* apx_eng_cmp: the tube coordinate sval o E^-1 is within 2 d0 of s_i + c_i *)
(* on every chain neck N_i (i <= k), within d0 on the upper part of the     *)
(* last neck N_k, the constants c_i increase by at least 1/(2 eps), and     *)
(* consecutive necks satisfy C1, C2 and the forward inclusion with the     *)
(* shifts c_(i+1) - c_i.                                                     *)
(* ------------------------------------------------------------------------- *)

let apx_eng_cmp = new_definition
 `apx_eng_cmp (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) (eps:real)
              (E:real^3->A) (L:real) (e:int->real^3->A) (c:num->real) (k:num)
              (d0:real) <=>
    c 0 = &0 /\ c k = L /\
    (!i. i < k ==> inv(&2 * eps) <= c(i + 1) - c i) /\
    (!i. i < k
         ==> !v. v IN rfs_neck_dom eps /\ e(&(i + 1)) v IN IMAGE (e(&i)) (rfs_neck_dom eps)
                 ==> ?z. z IN rfs_neck_dom eps /\ e(&i) z = e(&(i + 1)) v /\
                         abs(apx_sval z - apx_sval v - (c(i + 1) - c i)) <= d0) /\
    (!i. i < k
         ==> !v. v IN rfs_neck_dom eps /\
                 apx_sval v < inv eps - (c(i + 1) - c i) - d0
                 ==> e(&(i + 1)) v IN IMAGE (e(&i)) (rfs_neck_dom eps)) /\
    (!i. i < k
         ==> !z. z IN rfs_neck_dom eps /\ (c(i + 1) - c i) - inv eps + d0 < apx_sval z
                 ==> e(&i) z IN IMAGE (e(&(i + 1))) (rfs_neck_dom eps)) /\
    (!i. i <= k
         ==> !z. z IN rfs_neck_dom eps
                 ==> ?y. y IN apx_slab (--inv eps) (L + inv eps) /\ E y = e(&i) z /\
                         abs(apx_sval y - (apx_sval z + c i)) <= &2 * d0) /\
    (!z. z IN rfs_neck_dom eps /\ --inv(&2 * eps) - &2 * d0 < apx_sval z
         ==> ?y. y IN apx_slab (--inv eps) (L + inv eps) /\ E y = e(&k) z /\
                 abs(apx_sval y - (apx_sval z + c k)) <= d0)`;;

(* The constants grow at least linearly. *)

let APX_CMP_GROWTH = prove
 (`!(c:num->real) k eps.
        (!i. i < k ==> inv(&2 * eps) <= c(i + 1) - c i)
        ==> !i j. i <= j /\ j <= k ==> &(j - i) * inv(&2 * eps) <= c j - c i`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN REWRITE_TAC[LE] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[SUB_REFL; REAL_MUL_LZERO; REAL_SUB_REFL;
                                           REAL_LE_REFL];
    STRIP_TAC THEN ASM_CASES_TAC `i = SUC j` THENL
     [ASM_REWRITE_TAC[SUB_REFL; REAL_MUL_LZERO; REAL_SUB_REFL; REAL_LE_REFL]; ALL_TAC] THEN
    SUBGOAL_THEN `(i:num) <= j /\ j <= k /\ j < k` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `i <= SUC j` THEN UNDISCH_TAC `SUC j <= k` THEN
      UNDISCH_TAC `~(i = SUC j)` THEN ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
      can (find_term (fun t -> t = `j:num`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[ADD1] THEN
    SUBGOAL_THEN `&((j + 1) - i) = &(j - i) + &1` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
      UNDISCH_TAC `(i:num) <= j` THEN ARITH_TAC;
      ALL_TAC] THEN
    REAL_ARITH_TAC]);;

(* The splice on an old neck N_i (i <= k) stays within 2 d0 of s_i + c_i. *)

let APX_CMP_OLD_NECKS = prove
 (`!top atlas eps (E:real^3->A) Ei L ein ei' Delta d0 w1 w2 (e:int->real^3->A) c k i z.
        apx_eng_step top atlas eps E Ei L (e(&k)) ein (e(&(k + 1))) ei' Delta d0 w1 w2 /\
        apx_eng_cmp top atlas eps E L e c k d0 /\
        (!i. i <= k ==> mfd_param top atlas (rfs_neck_dom eps) (e(&i))) /\
        &4 * d0 <= inv(&8 * eps) /\ i <= k /\ z IN rfs_neck_dom eps
        ==> e(&i) z IN IMAGE E (apx_slab (--inv eps) (L + inv eps)) /\
            abs(apx_splice eps (e(&(k + 1))) ei' Ei w1 w2 (L + Delta) (e(&i) z) -
                (apx_sval z + c i)) <= &2 * d0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[apx_eng_step] th))
   (CONJUNCTS_THEN2
     (fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[apx_eng_cmp] th))
     STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `&0 < inv eps /\ &0 < inv(&8 * eps) /\ inv(&2 * eps) = inv eps / &2`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[APX_INV2] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the old tube point and its coordinate *)
  FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
    is_forall (concl th) && length(fst(strip_forall(concl th))) = 1 &&
    can (find_term (fun t -> t = `&2 * d0`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o SPEC `z:real^3`)] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(Ei:A->real^3)((e:int->real^3->A)(&i) z) = y` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `(E:real^3->A) y = (e:int->real^3->A)(&i) z`)) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:int->real^3->A)(&i) z IN IMAGE E (apx_slab (--inv eps) (L + inv eps))`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                 `E:real^3->A`; `Ei:A->real^3`; `L:real`; `(e:int->real^3->A)(&k)`;
                 `ein:A->real^3`; `(e:int->real^3->A)(&(k + 1))`; `ei':A->real^3`;
                 `Delta:real`; `d0:real`; `w1:real`; `w2:real`;
                 `(e:int->real^3->A)(&i) z`] APX_STEP_CASES) THEN
  ASM_REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* case (ii): the point is in N_k and N_(k+1), high in N_k *)
  ABBREV_TAC `p = (e:int->real^3->A)(&i) z` THEN
  SUBGOAL_THEN `(p:A) IN IMAGE ((e:int->real^3->A)(&k)) (rfs_neck_dom eps)` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (E:real^3->A) (apx_slab (--inv eps) (L + inv eps)) INTER
                 IMAGE ((e:int->real^3->A)(&(k + 1))) (rfs_neck_dom eps) SUBSET
                 IMAGE (e(&k)) (rfs_neck_dom eps)` THEN
    UNDISCH_TAC `(p:A) IN IMAGE (E:real^3->A) (apx_slab (--inv eps) (L + inv eps))` THEN
    UNDISCH_TAC `(p:A) IN IMAGE ((e:int->real^3->A)(&(k + 1))) (rfs_neck_dom eps)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?v. v IN rfs_neck_dom eps /\ (p:A) = (e:int->real^3->A)(&(k + 1)) v`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(p:A) IN IMAGE ((e:int->real^3->A)(&(k + 1))) (rfs_neck_dom eps)` THEN
    REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?zk. zk IN rfs_neck_dom eps /\ (p:A) = (e:int->real^3->A)(&k) zk`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(p:A) IN IMAGE ((e:int->real^3->A)(&k)) (rfs_neck_dom eps)` THEN
    REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(ei':A->real^3) p = v /\ (ein:A->real^3) p = zk` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `(p:A) = (e:int->real^3->A)(&(k + 1)) v` THEN
      DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[];
      UNDISCH_TAC `(p:A) = (e:int->real^3->A)(&k) zk` THEN
      DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  (* C1 for the step pair: zk is high in N_k *)
  SUBGOAL_THEN `abs(apx_sval(zk:real^3) - apx_sval(v:real^3) - Delta) <= d0`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `v:real^3` o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> t = `ein:A->real^3`)) (concl th) &&
      can (find_term (fun t -> t = `Delta:real`)) (concl th))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(p:A) = (e:int->real^3->A)(&(k + 1)) v` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `(p:A) = (e:int->real^3->A)(&(k + 1)) v` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(&8 * eps) + &3 < apx_sval(zk:real^3)` ASSUME_TAC THENL
   [UNDISCH_TAC `w1 < apx_sval((ei':A->real^3) p)` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `apx_sval(y:real^3) = apx_sval(zk:real^3) + (c:num->real) k` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `zk:real^3` o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> t = `--inv(&8 * eps)`)) (concl th) &&
      can (find_term (fun t -> t = `Ei:A->real^3`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    SUBGOAL_THEN `(Ei:A->real^3)((e:int->real^3->A)(&k) zk) = y` SUBST1_TAC THENL
     [UNDISCH_TAC `(p:A) = (e:int->real^3->A)(&k) zk` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `i:num = k` THENL
   [(* the last neck itself *)
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `z:real^3 = zk` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_INJ THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `rfs_neck_dom eps`; `(e:int->real^3->A)(&k)`] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `(i:num) + 1 = k` THENL
   [(* the neck before the last: C1 of the pair (k-1, k) *)
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      is_forall (concl th) && length(fst(strip_forall(concl th))) = 1 &&
      can (find_term (fun t -> t = `d0:real`)) (concl th) &&
      not (can (find_term (fun t -> t = `&2 * d0`)) (concl th)) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "?")) (concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(MP_TAC o SPEC `zk:real^3`)] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(p:A) = (e:int->real^3->A)(&k) zk` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      EXPAND_TAC "p" THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `z':real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `z':real^3 = z` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_INJ THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `rfs_neck_dom eps`; `(e:int->real^3->A)(&i)`] THEN
      ASM_SIMP_TAC[LE_REFL; LT_IMP_LE; ARITH_RULE `i + 1 = k ==> i <= k`] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(c:num->real)(i + 1) = c k` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* older necks cannot reach the window *)
  SUBGOAL_THEN `inv eps <= (c:num->real) k - c i` ASSUME_TAC THENL
   [MP_TAC(SPECL [`c:num->real`; `k:num`; `eps:real`] APX_CMP_GROWTH) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`i:num`; `k:num`]) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&2 <= &(k - i)` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `eps:real` APX_INV2) THEN
    SUBGOAL_THEN `&0 <= inv(&2 * eps)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SPEC_TAC(`&(k - i)`,`r:real`) THEN GEN_TAC THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `&2 * inv(&2 * eps) <= r * inv(&2 * eps)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(apx_sval(z:real^3)) < inv eps` ASSUME_TAC THENL
   [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
  UNDISCH_TAC `abs(apx_sval(y:real^3) - (apx_sval(z:real^3) + (c:num->real) i)) <= &2 * d0` THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* On the new neck the splice is within 2 d0 of s' + c, within d0 above   *)
(* level -1/(2 eps) - 2 d0.                                                  *)

let APX_CMP_NEW_NECK = prove
 (`!top atlas eps (E:real^3->A) Ei L ein ei' Delta d0 w1 w2 (e:int->real^3->A) c k z.
        apx_eng_step top atlas eps E Ei L (e(&k)) ein (e(&(k + 1))) ei' Delta d0 w1 w2 /\
        apx_eng_cmp top atlas eps E L e c k d0 /\
        &4 * d0 <= inv(&8 * eps) /\ z IN rfs_neck_dom eps
        ==> abs(apx_splice eps (e(&(k + 1))) ei' Ei w1 w2 (L + Delta) (e(&(k + 1)) z) -
                (apx_sval z + L + Delta)) <= &2 * d0 /\
            (--inv(&2 * eps) - &2 * d0 < apx_sval z
             ==> abs(apx_splice eps (e(&(k + 1))) ei' Ei w1 w2 (L + Delta)
                       (e(&(k + 1)) z) - (apx_sval z + L + Delta)) <= d0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[apx_eng_step] th))
   (CONJUNCTS_THEN2
     (fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[apx_eng_cmp] th))
     STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `&0 < inv eps /\ &0 < inv(&8 * eps) /\ inv(&2 * eps) = inv eps / &2`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[APX_INV2] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(apx_sval(z:real^3)) < inv eps` ASSUME_TAC THENL
   [ASM_MESON_TAC[APX_SVAL_NECK_DOM]; ALL_TAC] THEN
  SUBGOAL_THEN `(ei':A->real^3)((e:int->real^3->A)(&(k + 1)) z) = z` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `p = (e:int->real^3->A)(&(k + 1)) z` THEN
  SUBGOAL_THEN `(p:A) IN IMAGE ((e:int->real^3->A)(&(k + 1))) (rfs_neck_dom eps)`
  ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                 `E:real^3->A`; `Ei:A->real^3`; `L:real`; `(e:int->real^3->A)(&k)`;
                 `ein:A->real^3`; `(e:int->real^3->A)(&(k + 1))`; `ei':A->real^3`;
                 `Delta:real`; `d0:real`; `w1:real`; `w2:real`; `p:A`] APX_STEP_CASES) THEN
  ASM_REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
   [ALL_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC] THEN
  (* case (i): p in the old tube, below the window *)
  SUBGOAL_THEN `(p:A) IN IMAGE ((e:int->real^3->A)(&k)) (rfs_neck_dom eps)` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (E:real^3->A) (apx_slab (--inv eps) (L + inv eps)) INTER
                 IMAGE ((e:int->real^3->A)(&(k + 1))) (rfs_neck_dom eps) SUBSET
                 IMAGE (e(&k)) (rfs_neck_dom eps)` THEN
    UNDISCH_TAC `(p:A) IN IMAGE (E:real^3->A) (apx_slab (--inv eps) (L + inv eps))` THEN
    UNDISCH_TAC `(p:A) IN IMAGE ((e:int->real^3->A)(&(k + 1))) (rfs_neck_dom eps)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?zk. zk IN rfs_neck_dom eps /\ (p:A) = (e:int->real^3->A)(&k) zk`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(p:A) IN IMAGE ((e:int->real^3->A)(&k)) (rfs_neck_dom eps)` THEN
    REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(ein:A->real^3) p = zk` ASSUME_TAC THENL
   [UNDISCH_TAC `(p:A) = (e:int->real^3->A)(&k) zk` THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(apx_sval(zk:real^3) - apx_sval(z:real^3) - Delta) <= d0` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `z:real^3` o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> t = `ein:A->real^3`)) (concl th) &&
      can (find_term (fun t -> t = `Delta:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `zk:real^3` o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> t = `--inv(&2 * eps) - &2 * d0`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `apx_sval((Ei:A->real^3) p) = apx_sval(y:real^3)` ASSUME_TAC THENL
     [AP_TERM_TAC THEN
      UNDISCH_TAC `(p:A) = (e:int->real^3->A)(&k) zk` THEN DISCH_THEN SUBST1_TAC THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `(E:real^3->A) y = (e:int->real^3->A)(&k) zk`)) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `zk:real^3` o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> t = `--inv(&8 * eps)`)) (concl th) &&
      can (find_term (fun t -> t = `Ei:A->real^3`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    UNDISCH_TAC `(p:A) = (e:int->real^3->A)(&k) zk` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REAL_ARITH_TAC]);;

(* The comparison passes to the extended tube. *)

let APX_CMP_STEP = prove
 (`!top atlas eps (E:real^3->A) Ei L ein ei' Delta d0 w1 w2 (e:int->real^3->A) c k E'.
        apx_eng_step top atlas eps E Ei L (e(&k)) ein (e(&(k + 1))) ei' Delta d0 w1 w2 /\
        apx_eng_cmp top atlas eps E L e c k d0 /\
        (!i. i <= k ==> mfd_param top atlas (rfs_neck_dom eps) (e(&i))) /\
        &4 * d0 <= inv(&8 * eps) /\
        (!y. y IN apx_slab (--inv eps) ((L + Delta) + inv eps)
             ==> apx_splice eps (e(&(k + 1))) ei' Ei w1 w2 (L + Delta) (E' y) =
                 apx_sval y) /\
        IMAGE E' (apx_slab (--inv eps) ((L + Delta) + inv eps)) =
        IMAGE E (apx_slab (--inv eps) (L + inv eps)) UNION
        IMAGE (e(&(k + 1))) (rfs_neck_dom eps)
        ==> apx_eng_cmp top atlas eps E' (L + Delta) e
                        (\i. if i = k + 1 then L + Delta else c i) (k + 1) d0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "st") (CONJUNCTS_THEN2 (LABEL_TAC "cmp")
    STRIP_ASSUME_TAC)) THEN
  USE_THEN "st" (STRIP_ASSUME_TAC o REWRITE_RULE[apx_eng_step]) THEN
  USE_THEN "cmp" (STRIP_ASSUME_TAC o REWRITE_RULE[apx_eng_cmp]) THEN
  SUBGOAL_THEN
   `!p X B. p IN IMAGE (E:real^3->A) (apx_slab (--inv eps) (L + inv eps)) UNION
                 IMAGE ((e:int->real^3->A)(&(k + 1))) (rfs_neck_dom eps) /\
            abs(apx_splice eps (e(&(k + 1))) ei' Ei w1 w2 (L + Delta) p - X) <= B
            ==> ?y. y IN apx_slab (--inv eps) ((L + Delta) + inv eps) /\
                    (E':real^3->A) y = p /\ abs(apx_sval y - X) <= B`
  (LABEL_TAC "tr") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `(p:A) IN IMAGE (E':real^3->A) (apx_slab (--inv eps) ((L + Delta) + inv eps))`
    MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `(p:A) = E' (y:real^3)`)) THEN
    SUBGOAL_THEN `apx_splice eps ((e:int->real^3->A)(&(k + 1))) ei' Ei w1 w2 (L + Delta)
                    ((E':real^3->A) y) = apx_sval y` (fun th -> ASM_MESON_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[apx_eng_cmp] THEN
  REWRITE_TAC[ARITH_RULE `~(0 = k + 1)`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!i. i < k + 1 ==> ~(i = k + 1)` (fun th -> SIMP_TAC[th]) THENL
   [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!i. i < k + 1 ==> (i + 1 = k + 1 <=> i = k)` (fun th -> SIMP_TAC[th]) THENL
   [ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* growth *)
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_CASES_TAC `i:num = k` THEN
    ASM_REWRITE_TAC[] THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~((i:num) + 1 = k + 1) /\ (i:num) < k` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(i:num) < k + 1` THEN UNDISCH_TAC `~((i:num) = k)` THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[];
    (* C1 *)
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_CASES_TAC `i:num = k` THEN
    ASM_REWRITE_TAC[] THENL
     [X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN
      EXISTS_TAC `(ein:A->real^3)((e:int->real^3->A)(&(k + 1)) v)` THEN
      SUBGOAL_THEN `?z0. z0 IN rfs_neck_dom eps /\
                         (e:int->real^3->A)(&(k + 1)) v = e(&k) z0` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(e:int->real^3->A)(&(k + 1)) v IN IMAGE (e(&k)) (rfs_neck_dom eps)` THEN
        REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `v:real^3` o check (fun th ->
        is_forall (concl th) &&
        can (find_term (fun t -> t = `ein:A->real^3`)) (concl th) &&
        can (find_term (fun t -> t = `Delta:real`)) (concl th))) THEN
      ASM_SIMP_TAC[FUN_IN_IMAGE] THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `~((i:num) + 1 = k + 1) /\ (i:num) < k` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(i:num) < k + 1` THEN UNDISCH_TAC `~((i:num) = k)` THEN ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[]];
    (* C2 *)
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_CASES_TAC `i:num = k` THEN
    ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[REAL_ARITH `inv eps - ((L + Delta) - L) - d0 = inv eps - Delta - d0`] THEN
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN `~((i:num) + 1 = k + 1) /\ (i:num) < k` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(i:num) < k + 1` THEN UNDISCH_TAC `~((i:num) = k)` THEN ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[]];
    (* forward inclusion *)
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_CASES_TAC `i:num = k` THEN
    ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[REAL_ARITH `((L + Delta) - L) - inv eps + d0 = Delta - inv eps + d0`] THEN
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN `~((i:num) + 1 = k + 1) /\ (i:num) < k` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(i:num) < k + 1` THEN UNDISCH_TAC `~((i:num) = k)` THEN ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[]];
    (* the 2 d0 comparison on all necks *)
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(i:num) = k + 1` THEN ASM_REWRITE_TAC[] THENL
     [USE_THEN "tr" MATCH_MP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                     `E:real^3->A`; `Ei:A->real^3`; `L:real`; `ein:A->real^3`;
                     `ei':A->real^3`; `Delta:real`; `d0:real`; `w1:real`; `w2:real`;
                     `e:int->real^3->A`; `c:num->real`; `k:num`; `z:real^3`]
                    APX_CMP_NEW_NECK) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      ASM_SIMP_TAC[IN_UNION; FUN_IN_IMAGE];
      ALL_TAC] THEN
    SUBGOAL_THEN `(i:num) <= k` ASSUME_TAC THENL
     [UNDISCH_TAC `(i:num) <= k + 1` THEN UNDISCH_TAC `~((i:num) = k + 1)` THEN ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "tr" MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                   `E:real^3->A`; `Ei:A->real^3`; `L:real`; `ein:A->real^3`;
                   `ei':A->real^3`; `Delta:real`; `d0:real`; `w1:real`; `w2:real`;
                   `e:int->real^3->A`; `c:num->real`; `k:num`; `i:num`; `z:real^3`]
                  APX_CMP_OLD_NECKS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[IN_UNION];
    (* the d0 comparison on the upper part of the new neck *)
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN USE_THEN "tr" MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                   `E:real^3->A`; `Ei:A->real^3`; `L:real`; `ein:A->real^3`;
                   `ei':A->real^3`; `Delta:real`; `d0:real`; `w1:real`; `w2:real`;
                   `e:int->real^3->A`; `c:num->real`; `k:num`; `z:real^3`]
                  APX_CMP_NEW_NECK) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_SIMP_TAC[IN_UNION; FUN_IN_IMAGE]]);;

(* ------------------------------------------------------------------------- *)
(* The chain induction.  A finite chain e_0..e_n gives, for                  *)
(* every m <= n, a tube with first neck e_0, last neck e_m and image the     *)
(* union of N_0..N_m (each step: the step datum from the chain conditions,  *)
(* then APX_TUBE_STEP).                                                      *)
(* ------------------------------------------------------------------------- *)

let APX_CHAIN_FACTS = prove
 (`!top atlas (g:A->real^3^3) eps n x (e:int->real^3->A).
        apx_chain (top,atlas) g eps {i:int | &0 <= i /\ i <= &n} x e
        ==> (!j. j <= n ==> rfs_neck (top,atlas) g eps (x(&j)) (e(&j))) /\
            (!m. m < n
                 ==> IMAGE (e(&m)) (apx_slab (inv(&2 * eps)) (inv eps)) UNION
                     IMAGE (e(&(m + 1))) (apx_slab (--inv eps) (--inv(&2 * eps)))
                     SUBSET IMAGE (e(&m)) (rfs_neck_dom eps) INTER
                            IMAGE (e(&(m + 1))) (rfs_neck_dom eps) /\
                     IMAGE (e(&m)) (rfs_neck_dom eps) INTER
                     IMAGE (e(&(m + 1))) (rfs_neck_dom eps)
                     SUBSET IMAGE (e(&m)) (apx_slab (--inv(&2 * eps)) (inv eps)) INTER
                            IMAGE (e(&(m + 1))) (apx_slab (--inv eps) (inv(&2 * eps)))) /\
            (!a i. a < i /\ i <= n
                   ==> DISJOINT (IMAGE (e(&i)) (rfs_neck_dom eps))
                                (IMAGE (e(&a)) (apx_slab (--inv eps) (--inv(&2 * eps)))) /\
                       DISJOINT (IMAGE (e(&a)) (rfs_neck_dom eps))
                                (IMAGE (e(&i)) (apx_slab (inv(&2 * eps)) (inv eps))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[apx_chain; IN_ELIM_THM] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[INT_POS; INT_OF_NUM_LE];
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> t = `inv(&2 * eps)`)) (concl th) &&
      length(fst(strip_forall(concl th))) = 1)) THEN
    REWRITE_TAC[INT_POS; INT_OF_NUM_ADD; INT_OF_NUM_LE] THEN ASM_ARITH_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && length(fst(strip_forall(concl th))) = 2)) THEN
    REWRITE_TAC[INT_POS; INT_OF_NUM_LE; INT_OF_NUM_LT] THEN ASM_ARITH_TAC]);;

(* No triple overlaps along a chain, for the tube built from N_0..N_m. *)

let APX_CHAIN_NO_TRIPLE = prove
 (`!alpha1 eps1.
     &0 < alpha1 /\ alpha1 <= &1 / &4096 /\ &0 < eps1 /\ eps1 <= alpha1 /\
     (!top atlas (g:A->real^3^3) eps x (e:real^3->A) y.
        &0 < eps /\ eps <= eps1 /\ riemannian_metric atlas g /\
        rfs_neck (top,atlas) g eps x e /\ y IN rfs_neck_dom eps
        ==> abs(lscalar (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y - &1)
            <= alpha1 /\
            (!w. abs(lricci (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y w w -
                     lricci (cylinder_flow (&0)) y w w)
                 <= alpha1 * (w dot (cylinder_flow (&0) y ** w))))
     ==> !top atlas (g:A->real^3^3) eps n x (e:int->real^3->A) m E L.
           &0 < eps /\ eps <= eps1 /\ hausdorff_space top /\ riemannian_metric atlas g /\
           apx_chain (top,atlas) g eps {i:int | &0 <= i /\ i <= &n} x e /\ m < n /\
           apx_eng_tube top atlas eps (e(&0)) (e(&m)) E L /\
           IMAGE E (apx_slab (--inv eps) (L + inv eps)) =
           UNIONS {IMAGE (e(&i)) (rfs_neck_dom eps) | i <= m}
           ==> IMAGE E (apx_slab (--inv eps) (L + inv eps)) INTER
               IMAGE (e(&(m + 1))) (rfs_neck_dom eps)
               SUBSET IMAGE (e(&m)) (rfs_neck_dom eps)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`alpha1:real`; `eps1:real`] APX_PAIR_ALIGN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "al")] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `n:num`; `x:int->A`; `e:int->real^3->A`] APX_CHAIN_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "nk") (CONJUNCTS_THEN2 (LABEL_TAC "c1")
    (LABEL_TAC "c2"))) THEN
  SUBGOAL_THEN `!j. j <= n ==> smooth_manifold_atlas top atlas /\
                               mfd_param top atlas (rfs_neck_dom eps)
                                 ((e:int->real^3->A)(&j)) /\
                               ?ej. !z. z IN rfs_neck_dom eps ==> ej(e(&j) z) = z`
  (LABEL_TAC "par") THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    USE_THEN "nk" (MP_TAC o SPEC `j:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[rfs_neck] THEN STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `rfs_neck_dom eps`; `(e:int->real^3->A)(&j)`] GRGD_PARAM_FACTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ej:A->real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `ej:A->real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "par" (MP_TAC o SPEC `m:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_TAC `ein:A->real^3`))) THEN
  USE_THEN "par" (MP_TAC o SPEC `m + 1`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_TAC `ei':A->real^3`))) THEN
  USE_THEN "al" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `eps:real`; `(x:int->A)(&m)`; `(e:int->real^3->A)(&m)`;
    `(x:int->A)(&(m + 1))`; `(e:int->real^3->A)(&(m + 1))`; `ein:A->real^3`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN USE_THEN "nk" MATCH_MP_TAC THEN ASM_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_TAC `rhon:real`)] THEN
  USE_THEN "c1" (MP_TAC o SPEC `m:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `p:A` THEN STRIP_TAC THEN
  SUBGOAL_THEN `?j. j <= m /\ (p:A) IN IMAGE ((e:int->real^3->A)(&j)) (rfs_neck_dom eps)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(p:A) IN IMAGE E (apx_slab (--inv eps) (L + inv eps))` THEN
    ASM_REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "par" (MP_TAC o SPEC `j:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_TAC `eij:A->real^3`))) THEN
  USE_THEN "al" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `eps:real`; `(x:int->A)(&j)`; `(e:int->real^3->A)(&j)`;
    `(x:int->A)(&(m + 1))`; `(e:int->real^3->A)(&(m + 1))`; `eij:A->real^3`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN USE_THEN "nk" MATCH_MP_TAC THEN ASM_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_TAC `rho:real`)] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                 `(e:int->real^3->A)(&0)`; `(e:int->real^3->A)(&m)`; `E:real^3->A`;
                 `L:real`; `(e:int->real^3->A)(&(m + 1))`; `ein:A->real^3`;
                 `(e:int->real^3->A)(&j)`; `eij:A->real^3`; `rhon:real`;
                 `&7 * sqrt alpha1`; `rho:real`; `&7 * sqrt alpha1`] APX_NO_TRIPLE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `q:A` THEN
      DISCH_TAC THEN EXISTS_TAC `IMAGE ((e:int->real^3->A)(&j)) (rfs_neck_dom eps)` THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC
       `IMAGE ((e:int->real^3->A)(&m)) (apx_slab (inv(&2 * eps)) (inv eps)) UNION
        IMAGE (e(&(m + 1))) (apx_slab (--inv eps) (--inv(&2 * eps)))
        SUBSET IMAGE (e(&m)) (rfs_neck_dom eps) INTER IMAGE (e(&(m + 1))) (rfs_neck_dom eps)` THEN
      SET_TAC[];
      REWRITE_TAC[apx_eng_sides] THEN USE_THEN "c2" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC[apx_eng_sides] THEN USE_THEN "c2" MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ASM SET_TAC[]);;

(* One step of the chain induction. *)

let APX_CHAIN_STEP = prove
 (`!alpha1 eps1.
     &0 < alpha1 /\ alpha1 <= &1 / &4096 /\ &0 < eps1 /\ eps1 <= alpha1 /\
     (!top atlas (g:A->real^3^3) eps x (e:real^3->A) y.
        &0 < eps /\ eps <= eps1 /\ riemannian_metric atlas g /\
        rfs_neck (top,atlas) g eps x e /\ y IN rfs_neck_dom eps
        ==> abs(lscalar (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y - &1)
            <= alpha1 /\
            (!w. abs(lricci (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y w w -
                     lricci (cylinder_flow (&0)) y w w)
                 <= alpha1 * (w dot (cylinder_flow (&0) y ** w))))
     ==> !u top atlas (g:A->real^3^3) eps n x (e:int->real^3->A) Ds C m E L c.
           SMT_PRODUCT2_STATEMENT (u:A->bool) /\
           &0 < eps /\ eps <= eps1 /\ &96 * eps <= &1 /\ hausdorff_space top /\
           riemannian_metric atlas g /\
           apx_chain (top,atlas) g eps {i:int | &0 <= i /\ i <= &n} x e /\
           (!t. (smooth_step has_real_derivative Ds t) (atreal t) /\ abs(Ds t) <= C) /\
           &0 < C /\ sqrt alpha1 <= &1 / &2560 /\ C * sqrt alpha1 <= &1 / &2560 /\
           m < n /\
           apx_eng_tube top atlas eps (e(&0)) (e(&m)) E L /\
           IMAGE E (apx_slab (--inv eps) (L + inv eps)) =
           UNIONS {IMAGE (e(&i)) (rfs_neck_dom eps) | i <= m} /\
           apx_eng_cmp top atlas eps E L e c m (&80 * sqrt alpha1 * inv eps)
           ==> ?E' L' c'. apx_eng_tube top atlas eps (e(&0)) (e(&(m + 1))) E' L' /\
                          IMAGE E' (apx_slab (--inv eps) (L' + inv eps)) =
                          UNIONS {IMAGE (e(&i)) (rfs_neck_dom eps) | i <= m + 1} /\
                          apx_eng_cmp top atlas eps E' L' e c' (m + 1)
                                      (&80 * sqrt alpha1 * inv eps)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`alpha1:real`; `eps1:real`] APX_CHAIN_PAIR_STRUCT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "ps")] THEN
  MP_TAC(SPECL [`alpha1:real`; `eps1:real`] APX_CHAIN_NO_TRIPLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "nt")] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `n:num`; `x:int->A`; `e:int->real^3->A`] APX_CHAIN_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "nk") (CONJUNCTS_THEN2 (LABEL_TAC "c1")
    (LABEL_TAC "c2"))) THEN
  SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) eps ((x:int->A)(&m))
                         ((e:int->real^3->A)(&m)) /\
                rfs_neck (top,atlas) g eps (x(&(m + 1))) (e(&(m + 1)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "nk" MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
                mfd_param top atlas (rfs_neck_dom eps) ((e:int->real^3->A)(&m)) /\
                mfd_param top atlas (rfs_neck_dom eps) (e(&(m + 1)))`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `(e:int->real^3->A)(&m)`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ein:A->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `(e:int->real^3->A)(&(m + 1))`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ei':A->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `mfd_param top atlas (apx_slab (--inv eps) (L + inv eps)) (E:real^3->A)`
  ASSUME_TAC THENL [ASM_MESON_TAC[apx_eng_tube]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `apx_slab (--inv eps) (L + inv eps)`; `E:real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Ei:A->real^3` STRIP_ASSUME_TAC) THEN
  USE_THEN "c1" (MP_TAC o SPEC `m:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "ps" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `eps:real`; `(x:int->A)(&m)`; `(e:int->real^3->A)(&m)`;
    `(x:int->A)(&(m + 1))`; `(e:int->real^3->A)(&(m + 1))`; `ein:A->real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `Delta:real` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `d0 = &80 * sqrt alpha1 * inv eps` THEN
  SUBGOAL_THEN `&0 < inv eps /\ &96 <= inv eps /\ &0 <= sqrt alpha1` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `inv eps = &1 / eps` SUBST1_TAC THENL
       [REWRITE_TAC[real_div; REAL_MUL_LID]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= d0 /\ &32 * d0 <= inv eps /\ d0 < inv(&2 * eps)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d0" THEN REWRITE_TAC[REAL_INV_MUL] THEN
    SUBGOAL_THEN `&0 <= sqrt alpha1 * inv eps /\
                  sqrt alpha1 * inv eps <= &1 / &2560 * inv eps`
    MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      UNDISCH_TAC `&0 < inv eps` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(e:int->real^3->A)(&m)`; `(e:int->real^3->A)(&(m + 1))`; `ein:A->real^3`;
                 `eps:real`; `Delta:real`; `d0:real`] APX_PAIR_FORWARD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
     `IMAGE ((e:int->real^3->A)(&m)) (apx_slab (inv(&2 * eps)) (inv eps)) UNION
      IMAGE (e(&(m + 1))) (apx_slab (--inv eps) (--inv(&2 * eps)))
      SUBSET IMAGE (e(&m)) (rfs_neck_dom eps) INTER IMAGE (e(&(m + 1))) (rfs_neck_dom eps)` THEN
    SET_TAC[];
    DISCH_TAC] THEN
  USE_THEN "nt" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `eps:real`; `n:num`; `x:int->A`; `e:int->real^3->A`; `m:num`;
    `E:real^3->A`; `L:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                 `(e:int->real^3->A)(&0)`; `(e:int->real^3->A)(&m)`; `E:real^3->A`;
                 `L:real`; `Ei:A->real^3`] APX_TUBE_EXACT_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `w1 = max (inv(&8 * eps) - Delta) (--(&7 * inv(&8 * eps))) + d0 + &3` THEN
  ABBREV_TAC `w2 = min (inv eps - Delta) (--inv(&8 * eps)) - d0 - &3` THEN
  MP_TAC(SPECL [`eps:real`; `Delta:real`; `d0:real`; `w1:real`; `w2:real`]
               APX_WINDOW_ARITH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`mfd_scalar atlas (g:A->real^3^3) ((x:int->A)(&m)) /
                 mfd_scalar atlas g (x(&(m + 1)))`; `alpha1:real`] APX_RHO_KAPPA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 <= L` ASSUME_TAC THENL
   [UNDISCH_TAC `apx_eng_tube top atlas eps ((e:int->real^3->A)(&0)) (e(&m)) E L` THEN
    REWRITE_TAC[apx_eng_tube] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN apx_slab (--inv eps) (inv(&8 * eps))
                    ==> (E:real^3->A) y = (e:int->real^3->A)(&0) y` ASSUME_TAC THENL
   [UNDISCH_TAC `apx_eng_tube top atlas eps ((e:int->real^3->A)(&0)) (e(&m)) E L` THEN
    REWRITE_TAC[apx_eng_tube] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE ((e:int->real^3->A)(&m)) (rfs_neck_dom eps) SUBSET
                IMAGE E (apx_slab (--inv eps) (L + inv eps))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `q:A` THEN
    DISCH_TAC THEN EXISTS_TAC `IMAGE ((e:int->real^3->A)(&m)) (rfs_neck_dom eps)` THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `m:num` THEN REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE ((e:int->real^3->A)(&m)) (rfs_neck_dom eps) INTER
                IMAGE (e(&(m + 1))) (rfs_neck_dom eps) SUBSET
                IMAGE (e(&(m + 1))) (apx_slab (--inv eps) (inv(&2 * eps)))` ASSUME_TAC THENL
   [UNDISCH_TAC
     `IMAGE ((e:int->real^3->A)(&m)) (rfs_neck_dom eps) INTER
      IMAGE (e(&(m + 1))) (rfs_neck_dom eps)
      SUBSET IMAGE (e(&m)) (apx_slab (--inv(&2 * eps)) (inv eps)) INTER
             IMAGE (e(&(m + 1))) (apx_slab (--inv eps) (inv(&2 * eps)))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `C * d0 < (w2 - w1) *
             min (sqrt(mfd_scalar atlas (g:A->real^3^3) ((x:int->A)(&m)) /
                       mfd_scalar atlas g (x(&(m + 1)))) - &7 * sqrt alpha1) (&1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APX_REG_CONST THEN
    MAP_EVERY EXISTS_TAC [`eps:real`; `sqrt alpha1`] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `apx_eng_step top atlas eps (E:real^3->A) Ei L ((e:int->real^3->A)(&m)) ein
                  (e(&(m + 1))) ei' Delta d0 w1 w2` ASSUME_TAC THENL
   [REWRITE_TAC[apx_eng_step] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`u:A->bool`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `eps:real`; `E:real^3->A`; `Ei:A->real^3`; `L:real`;
                 `(e:int->real^3->A)(&m)`; `ein:A->real^3`;
                 `(e:int->real^3->A)(&(m + 1))`; `ei':A->real^3`; `Delta:real`;
                 `d0:real`; `w1:real`; `w2:real`; `(e:int->real^3->A)(&0)`;
                 `sqrt(mfd_scalar atlas (g:A->real^3^3) ((x:int->A)(&m)) /
                       mfd_scalar atlas g (x(&(m + 1))))`;
                 `&7 * sqrt alpha1`; `Ds:real->real`; `C:real`] APX_TUBE_STEP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `E':real^3->A` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`E':real^3->A`; `L + Delta:real`;
                        `\i. if i = m + 1 then L + Delta else (c:num->real) i`] THEN
  ASM_REWRITE_TAC[APX_UNIONS_UPTO_SUC] THEN
  MATCH_MP_TAC APX_CMP_STEP THEN
  MAP_EVERY EXISTS_TAC [`E:real^3->A`; `Ei:A->real^3`; `ein:A->real^3`; `ei':A->real^3`;
                        `w1:real`; `w2:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    USE_THEN "nk" (MP_TAC o SPEC `j:num`) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `(j:num) <= m` THEN UNDISCH_TAC `(m:num) < n` THEN ARITH_TAC;
      SIMP_TAC[rfs_neck]];
    UNDISCH_TAC `&32 * d0 <= inv eps` THEN REWRITE_TAC[REAL_INV_MUL] THEN
    REAL_ARITH_TAC]);;

(* The base of the induction: a single neck is a tube of length 0. *)

let APX_TUBE_BASE = prove
 (`!top atlas (g:A->real^3^3) eps x (e0:real^3->A).
        rfs_neck (top,atlas) g eps x e0
        ==> apx_eng_tube top atlas eps e0 e0 e0 (&0) /\
            IMAGE e0 (apx_slab (--inv eps) (&0 + inv eps)) =
            IMAGE e0 (rfs_neck_dom eps)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
  REWRITE_TAC[apx_eng_tube; REAL_ADD_LID; GSYM APX_SLAB_NECK_DOM; REAL_LE_REFL] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`\x:real^3. x`; `\x:real^3. x`] THEN
  REWRITE_TAC[SMT_SPHERE_DIFFEO_ID; SMT_RADIAL_EXT_ID; REAL_NEG_0; real_div;
              REAL_MUL_LZERO; REAL_EXP_0; VECTOR_MUL_LID]);;

(* The comparison for a single neck. *)

let APX_CMP_BASE = prove
 (`!top atlas eps (e:int->real^3->A) d0.
        &0 <= d0 ==> apx_eng_cmp top atlas eps (e(&0)) (&0) e (\i. &0) 0 d0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[apx_eng_cmp; LT; LE; REAL_ADD_LID; REAL_ADD_RID; GSYM APX_SLAB_NECK_DOM] THEN
  CONJ_TAC THEN REPEAT STRIP_TAC THEN EXISTS_TAC `z:real^3` THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN ASM_REAL_ARITH_TAC);;

(* The induction along the chain. *)

let APX_CHAIN_TUBE = prove
 (`!alpha1 eps1.
     &0 < alpha1 /\ alpha1 <= &1 / &4096 /\ &0 < eps1 /\ eps1 <= alpha1 /\
     (!top atlas (g:A->real^3^3) eps x (e:real^3->A) y.
        &0 < eps /\ eps <= eps1 /\ riemannian_metric atlas g /\
        rfs_neck (top,atlas) g eps x e /\ y IN rfs_neck_dom eps
        ==> abs(lscalar (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y - &1)
            <= alpha1 /\
            (!w. abs(lricci (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y w w -
                     lricci (cylinder_flow (&0)) y w w)
                 <= alpha1 * (w dot (cylinder_flow (&0) y ** w))))
     ==> !u top atlas (g:A->real^3^3) eps n x (e:int->real^3->A) Ds C.
           SMT_PRODUCT2_STATEMENT (u:A->bool) /\
           &0 < eps /\ eps <= eps1 /\ &96 * eps <= &1 /\ hausdorff_space top /\
           riemannian_metric atlas g /\
           apx_chain (top,atlas) g eps {i:int | &0 <= i /\ i <= &n} x e /\
           (!t. (smooth_step has_real_derivative Ds t) (atreal t) /\ abs(Ds t) <= C) /\
           &0 < C /\ sqrt alpha1 <= &1 / &2560 /\ C * sqrt alpha1 <= &1 / &2560
           ==> !m. m <= n
                   ==> ?E L c. apx_eng_tube top atlas eps (e(&0)) (e(&m)) E L /\
                               IMAGE E (apx_slab (--inv eps) (L + inv eps)) =
                               UNIONS {IMAGE (e(&i)) (rfs_neck_dom eps) | i <= m} /\
                               apx_eng_cmp top atlas eps E L e c m
                                           (&80 * sqrt alpha1 * inv eps)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`alpha1:real`; `eps1:real`] APX_CHAIN_STEP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "st")] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `n:num`; `x:int->A`; `e:int->real^3->A`] APX_CHAIN_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `0` o CONJUNCT1) THEN REWRITE_TAC[LE_0] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `(x:int->A)(&0)`; `(e:int->real^3->A)(&0)`] APX_TUBE_BASE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`(e:int->real^3->A)(&0)`; `&0`; `\i:num. &0`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[LE; EXTENSION; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
      MATCH_MP_TAC APX_CMP_BASE THEN
      SUBGOAL_THEN `&0 <= sqrt alpha1 /\ &0 < inv eps` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
      can (find_term (fun t -> t = `m:num`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `E:real^3->A` (X_CHOOSE_THEN `L:real`
      (X_CHOOSE_THEN `c:num->real` STRIP_ASSUME_TAC))) THEN
    REWRITE_TAC[ADD1] THEN
    USE_THEN "st" (MP_TAC o SPECL [`u:A->bool`; `top:A topology`;
      `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `eps:real`; `n:num`;
      `x:int->A`; `e:int->real^3->A`; `Ds:real->real`; `C:real`; `m:num`;
      `E:real^3->A`; `L:real`; `c:num->real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The constants and the core of A13 (everything except the                 *)
(* sections clause of apx_tube): from SMT_PRODUCT2_STATEMENT, for every     *)
(* finite chain a product chart E with exact ends and image the chain union, *)
(* every point lying in an eps-neck of the chain inside the tube.          *)
(* ------------------------------------------------------------------------- *)

let APX_CHAIN_UNION_UPTO = prove
 (`!eps n (e:int->real^3->A).
        apx_chain_union eps {i:int | &0 <= i /\ i <= &n} e =
        UNIONS {IMAGE (e(&i)) (rfs_neck_dom eps) | i <= n}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[apx_chain_union; EXTENSION; IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `p:A` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `t:A->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `i:int` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    MP_TAC(SPEC `i:int` INT_OF_NUM_EXISTS) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC) THEN
    EXISTS_TAC `t:A->bool` THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `k:num` THEN
    ASM_MESON_TAC[INT_OF_NUM_LE];
    DISCH_THEN(X_CHOOSE_THEN `t:A->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    EXISTS_TAC `t:A->bool` THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `&k:int` THEN
    ASM_REWRITE_TAC[INT_POS; INT_OF_NUM_LE]]);;

(* The constants: alpha1 = s0^2 with s0 = 1/(2560 (1 + C)). *)

let APX_ENGINE_CONSTANTS = prove
 (`!C. &0 < C
       ==> ?alpha1. &0 < alpha1 /\ alpha1 <= &1 / &4096 /\
                    sqrt alpha1 <= &1 / &2560 /\ C * sqrt alpha1 <= &1 / &2560`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `s0 = inv(&2560 * (&1 + C))` THEN
  SUBGOAL_THEN `&0 < s0 /\ s0 <= &1 / &2560 /\ C * s0 <= &1 / &2560` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s0" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_INV_MUL; real_div; REAL_MUL_LID] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= a * (&1 - b) ==> a * b <= a`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[REAL_SUB_LE] THEN MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_INV_MUL] THEN
      SUBGOAL_THEN `C * inv(&1 + C) <= &1` MP_TAC THENL
       [SUBGOAL_THEN `&0 < &1 + C` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= C * inv(&1 + C)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `C * inv(&2560) * inv(&1 + C) = inv(&2560) * (C * inv(&1 + C))`
      SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      SPEC_TAC(`C * inv(&1 + C)`,`q:real`) THEN GEN_TAC THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `s0 pow 2` THEN
  ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE; REAL_POW_LT] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 / &2560) pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    CONV_TAC REAL_RAT_REDUCE_CONV]);;

(* The core of A13 (all of the conclusion except the sections clause). *)

let APX_A13_CORE = prove
 (`!u:A->bool.
     SMT_PRODUCT2_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !top atlas g eps n x e.
              &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\
              riemannian_metric atlas g /\
              apx_chain (top,atlas) g eps {i:int | &0 <= i /\ i <= &n} x
                        (e:int->real^3->A)
              ==> ?E L f f'.
                    &0 <= L /\ sphere_diffeo f f' /\
                    mfd_param top atlas (apx_slab (--inv eps) (L + inv eps)) E /\
                    (!y. y IN apx_slab (--inv eps) (inv(&8 * eps)) ==> E y = e (&0) y) /\
                    (!y. y IN apx_slab (L - inv(&8 * eps)) (L + inv eps)
                         ==> E y = e (&n) (radial_ext f (exp(--L / sqrt(&2)) % y))) /\
                    IMAGE E (apx_slab (--inv eps) (L + inv eps)) =
                    apx_chain_union eps {i:int | &0 <= i /\ i <= &n} e /\
                    (!p. p IN IMAGE E (apx_slab (--inv eps) (L + inv eps))
                         ==> ?x e. rfs_neck (top,atlas) g eps x e /\
                                   p IN IMAGE e (rfs_neck_dom eps) /\
                                   IMAGE e (rfs_neck_dom eps) SUBSET
                                   IMAGE E (apx_slab (--inv eps) (L + inv eps)))`,
  GEN_TAC THEN DISCH_TAC THEN
  X_CHOOSE_THEN `Ds:real->real` (X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC)
    APX_SMOOTH_STEP_DERIV THEN
  MP_TAC(SPEC `C:real` APX_ENGINE_CONSTANTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `alpha1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `u:A->bool` APX_NECK_CURV) THEN REWRITE_TAC[APX_NECK_CURV_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `alpha1:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n1"))) THEN
  ABBREV_TAC `eps1 = min eps2 alpha1` THEN
  SUBGOAL_THEN `&0 < eps1 /\ eps1 <= alpha1 /\ eps1 <= eps2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eps1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`alpha1:real`; `eps1:real`] APX_CHAIN_TUBE) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "n1" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    DISCH_THEN(LABEL_TAC "ct")] THEN
  EXISTS_TAC `min eps1 (&1 / &96)` THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  USE_THEN "ct" (MP_TAC o SPECL [`u:A->bool`; `top:A topology`;
    `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `eps:real`; `n:num`;
    `x:int->A`; `e:int->real^3->A`; `Ds:real->real`; `C:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `E:real^3->A` (X_CHOOSE_THEN `L:real`
    (X_CHOOSE_THEN `c:num->real` STRIP_ASSUME_TAC))) THEN
  UNDISCH_TAC `apx_eng_tube top atlas eps ((e:int->real^3->A)(&0)) (e(&n)) E L` THEN
  REWRITE_TAC[apx_eng_tube] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `f':real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`E:real^3->A`; `L:real`; `f:real^3->real^3`; `f':real^3->real^3`] THEN
  ASM_REWRITE_TAC[APX_CHAIN_UNION_UPTO] THEN
  X_GEN_TAC `p:A` THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:A->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`(x:int->A)(&k)`; `(e:int->real^3->A)(&k)`] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `n:num`; `x:int->A`; `e:int->real^3->A`] APX_CHAIN_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `q:A` THEN DISCH_TAC THEN
  EXISTS_TAC `IMAGE ((e:int->real^3->A)(&k)) (rfs_neck_dom eps)` THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Regions below and above a radial graph.  For continuous                  *)
(* positive radius functions a < b on the unit sphere, the region between   *)
(* the two graphs is connected (the image of annulus(1,2) under the radial  *)
(* interpolation).  In a neck chart, a radial section splits the neck into  *)
(* the connected regions below and above it.                                 *)
(* ------------------------------------------------------------------------- *)

let APX_SCALE_UNIT = prove
 (`!r (v:real^3). &0 < r /\ norm v = &1
                  ==> norm(r % v) = r /\ inv(norm(r % v)) % (r % v) = v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[NORM_MUL; REAL_ARITH `&0 < r ==> abs r = r`; REAL_MUL_RID] THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
  REWRITE_TAC[VECTOR_MUL_LID]);;

let APX_NORMALIZE_UNIT = prove
 (`!z:real^3. ~(z = vec 0)
              ==> norm(inv(norm z) % z) = &1 /\ &0 < norm z /\
                  norm z % (inv(norm z) % z) = z`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < norm(z:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ASM_REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM; VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID]);;

let APX_RADIAL_REGION = prove
 (`!(a:real^3->real) b.
        (\x. lift(a x)) continuous_on sphere(vec 0,&1) /\
        (\x. lift(b x)) continuous_on sphere(vec 0,&1) /\
        (!x. x IN sphere(vec 0,&1) ==> &0 < a x /\ a x < b x)
        ==> connected {z:real^3 | ~(z = vec 0) /\ a(inv(norm z) % z) < norm z /\
                                  norm z < b(inv(norm z) % z)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `h = \x:real^3. ((&2 - norm x) * a(inv(norm x) % x) +
                              (norm x - &1) * b(inv(norm x) % x)) % (inv(norm x) % x)` THEN
  SUBGOAL_THEN
   `{z:real^3 | ~(z = vec 0) /\ (a:real^3->real)(inv(norm z) % z) < norm z /\
                norm z < (b:real^3->real)(inv(norm z) % z)} =
    IMAGE (h:real^3->real^3) (annulus (&1) (&2))`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; annulus] THEN X_GEN_TAC `z:real^3` THEN
    EQ_TAC THENL
     [STRIP_TAC THEN
      MP_TAC(SPEC `z:real^3` APX_NORMALIZE_UNIT) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      ABBREV_TAC `th = inv(norm z) % (z:real^3)` THEN
      SUBGOAL_THEN `&0 < a(th:real^3) /\ a th < b th` STRIP_ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_SPHERE_0]; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < b(th:real^3) - a th` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `?t. &1 < t /\ t < &2 /\
                        (&2 - t) * a(th:real^3) + (t - &1) * b th = norm(z:real^3)`
      STRIP_ASSUME_TAC THENL
       [EXISTS_TAC `&1 + (norm(z:real^3) - a(th:real^3)) / (b th - a th)` THEN
        ASM_SIMP_TAC[REAL_LT_ADDR; REAL_LT_DIV; REAL_SUB_LT] THEN
        CONJ_TAC THENL
         [REWRITE_TAC[REAL_ARITH `&1 + x < &2 <=> x < &1`] THEN
          ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
          UNDISCH_TAC `&0 < b(th:real^3) - a th` THEN CONV_TAC REAL_FIELD];
        ALL_TAC] THEN
      EXISTS_TAC `t % (th:real^3)` THEN
      MP_TAC(SPECL [`t:real`; `th:real^3`] APX_SCALE_UNIT) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "h" THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `&1 < norm(x:real^3)` THEN
        ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(SPEC `x:real^3` APX_NORMALIZE_UNIT) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      ABBREV_TAC `th = inv(norm x) % (x:real^3)` THEN
      SUBGOAL_THEN `&0 < a(th:real^3) /\ a th < b th` STRIP_ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_SPHERE_0]; ALL_TAC] THEN
      ABBREV_TAC `rho = (&2 - norm(x:real^3)) * a(th:real^3) + (norm x - &1) * b th` THEN
      SUBGOAL_THEN `a(th:real^3) < rho /\ rho < b th` STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "rho" THEN CONJ_TAC THENL
         [MATCH_MP_TAC(REAL_ARITH
           `&0 < (n - &1) * (bb - aa) ==> aa < (&2 - n) * aa + (n - &1) * bb`);
          MATCH_MP_TAC(REAL_ARITH
           `&0 < (&2 - n) * (bb - aa) ==> (&2 - n) * aa + (n - &1) * bb < bb`)] THEN
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `(h:real^3->real^3) x = rho % th` SUBST1_TAC THENL
       [EXPAND_TAC "h" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(SPECL [`rho:real`; `th:real^3`] APX_SCALE_UNIT) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      ASM_REWRITE_TAC[VECTOR_MUL_EQ_0] THEN
      REWRITE_TAC[DE_MORGAN_THM] THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        DISCH_TAC THEN UNDISCH_TAC `norm(th:real^3) = &1` THEN
        ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN REWRITE_TAC[APX_CONNECTED_ANNULUS3] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    DISCH_TAC THEN UNDISCH_TAC `&1 < norm(x:real^3)` THEN
    ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `(\x:real^3. inv(norm x) % x) continuous_on {x | ~(x = vec 0)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN REWRITE_TAC[SMOOTH_MAP_ON_NORMALIZE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f:real^3->real. (\x. lift(f x)) continuous_on sphere(vec 0,&1)
        ==> (\x. lift(f(inv(norm x) % x))) continuous_on {x:real^3 | ~(x = vec 0)}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(\x. lift((f:real^3->real)(inv(norm x) % x))) =
                  (\x. lift(f x)) o (\x:real^3. inv(norm x) % x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `sphere(vec 0:real^3,&1)` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_SPHERE_0] THEN
    SIMP_TAC[APX_NORMALIZE_UNIT];
    ALL_TAC] THEN
  EXPAND_TAC "h" THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN ASM_REWRITE_TAC[o_DEF] THEN
  REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
  CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN ASM_SIMP_TAC[o_DEF] THEN
  REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
  REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
  REWRITE_TAC[REWRITE_RULE[o_DEF] CONTINUOUS_ON_LIFT_NORM]);;

(* A radial section of a chart splits its image into two connected parts. *)

let APX_SECTION_BASICS = prove
 (`!(u:real^3->real) r1 r2.
        &0 < r1 /\ (!x. x IN sphere(vec 0,&1) ==> r1 < u x /\ u x < r2)
        ==> (!x. x IN sphere(vec 0,&1)
                 ==> u x % x IN annulus r1 r2 /\ norm(u x % x) = u x /\
                     inv(norm(u x % x)) % (u x % x) = x) /\
            (!z. ~(z = vec 0)
                 ==> r1 < u(inv(norm z) % z) /\ u(inv(norm z) % z) < r2) /\
            {z | ~(z = vec 0) /\ r1 < norm z /\ norm z < u(inv(norm z) % z)} SUBSET
            annulus r1 r2 /\
            {z | ~(z = vec 0) /\ u(inv(norm z) % z) < norm z /\ norm z < r2} SUBSET
            annulus r1 r2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z:real^3. ~(z = vec 0)
                           ==> r1 < u(inv(norm z) % z) /\ u(inv(norm z) % z) < r2`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[IN_SPHERE_0; APX_NORMALIZE_UNIT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> t = `sphere(vec 0:real^3,&1)`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`(u:real^3->real) x`; `x:real^3`] APX_SCALE_UNIT) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[IN_SPHERE_0]]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[annulus; IN_ELIM_THM];
    REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (fun th ->
      is_forall (concl th) &&
      not (can (find_term (fun t -> t = `sphere(vec 0:real^3,&1)`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (fun th ->
      is_forall (concl th) &&
      not (can (find_term (fun t -> t = `sphere(vec 0:real^3,&1)`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let APX_SECTION_SPLIT = prove
 (`!top atlas (e:real^3->A) r1 r2 (u:real^3->real).
        smooth_manifold_atlas top atlas /\ &0 < r1 /\
        mfd_param top atlas (annulus r1 r2) e /\
        (\x. lift(u x)) continuous_on sphere(vec 0,&1) /\
        (!x. x IN sphere(vec 0,&1) ==> r1 < u x /\ u x < r2)
        ==> connected_in top
              (IMAGE e {z | ~(z = vec 0) /\ r1 < norm z /\ norm z < u(inv(norm z) % z)}) /\
            connected_in top
              (IMAGE e {z | ~(z = vec 0) /\ u(inv(norm z) % z) < norm z /\ norm z < r2}) /\
            IMAGE e (annulus r1 r2) =
            IMAGE (\x. e(u x % x)) (sphere(vec 0,&1)) UNION
            IMAGE e {z | ~(z = vec 0) /\ r1 < norm z /\ norm z < u(inv(norm z) % z)} UNION
            IMAGE e {z | ~(z = vec 0) /\ u(inv(norm z) % z) < norm z /\ norm z < r2} /\
            DISJOINT (IMAGE (\x. e(u x % x)) (sphere(vec 0,&1)))
                     (IMAGE e {z | ~(z = vec 0) /\ r1 < norm z /\
                                   norm z < u(inv(norm z) % z)}) /\
            DISJOINT (IMAGE (\x. e(u x % x)) (sphere(vec 0,&1)))
                     (IMAGE e {z | ~(z = vec 0) /\ u(inv(norm z) % z) < norm z /\
                                   norm z < r2})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`u:real^3->real`; `r1:real`; `r2:real`] APX_SECTION_BASICS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `annulus r1 r2:real^3->bool`; `e:real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ei:A->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!s. connected s /\ s SUBSET annulus r1 r2 ==> connected_in top (IMAGE (e:real^3->A) s)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
    EXISTS_TAC `subtopology euclidean (annulus r1 r2:real^3->bool)` THEN
    ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; CONNECTED_IN_EUCLIDEAN];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^3 x. z IN annulus r1 r2 /\ x IN sphere(vec 0,&1) /\
                 (e:real^3->A) z = e(u x % x) ==> z = u x % x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_PARAM_INJ THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `annulus r1 r2:real^3->bool`; `e:real^3->A`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "connected")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\x:real^3. (r1:real)`; `u:real^3->real`] APX_RADIAL_REGION) THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "connected")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`u:real^3->real`; `\x:real^3. (r2:real)`] APX_RADIAL_REGION) THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[REAL_LT_TRANS];
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(z:real^3 = vec 0) /\ r1 < norm z /\ norm z < r2` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(z:real^3) IN annulus r1 r2` THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(SPEC `z:real^3` APX_NORMALIZE_UNIT) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      REWRITE_TAC[IN_UNION; IN_IMAGE; IN_ELIM_THM] THEN
      ASM_CASES_TAC `norm(z:real^3) = u(inv(norm z) % z)` THENL
       [DISJ1_TAC THEN EXISTS_TAC `inv(norm z) % (z:real^3)` THEN
        ASM_REWRITE_TAC[IN_SPHERE_0] THEN AP_TERM_TAC THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          concl th = `norm(z:real^3) = u(inv(norm z) % z)`)) THEN
        ASM_REWRITE_TAC[];
        DISJ2_TAC THEN
        ASM_CASES_TAC `norm(z:real^3) < u(inv(norm z) % z)` THENL
         [DISJ1_TAC THEN EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[];
          DISJ2_TAC THEN EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[] THEN
          ASM_REAL_ARITH_TAC]];
      REWRITE_TAC[UNION_SUBSET] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_MESON_TAC[];
        MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]]];
    ALL_TAC; ALL_TAC] THEN
  (REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `p:A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o SPEC `x:real^3` o check (fun th ->
    is_forall (concl th) && length(fst(strip_forall(concl th))) = 1 &&
    can (find_term (fun t -> t = `sphere(vec 0:real^3,&1)`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "annulus")) (concl th) &&
    can (find_term (fun t -> t = `u:real^3->real`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(z:real^3) IN annulus r1 r2` ASSUME_TAC THENL
   [REWRITE_TAC[annulus; IN_ELIM_THM] THEN
    FIRST_ASSUM(MP_TAC o SPEC `z:real^3` o check (fun th ->
      is_forall (concl th) &&
      not (can (find_term (fun t -> t = `sphere(vec 0:real^3,&1)`)) (concl th)) &&
      can (find_term (fun t -> t = `r2:real`)) (concl th) &&
      can (find_term (fun t -> t = `u:real^3->real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3) = u(x:real^3) % x` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && length(fst(strip_forall(concl th))) = 2)) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(z:real^3) = u(inv(norm z) % z)` MP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> concl th = `(z:real^3) = u(x:real^3) % x`)) THEN
    ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC]));;

(* ------------------------------------------------------------------------- *)
(* A pair of points separated by a neck sphere, arbitrarily                 *)
(* close to the sphere (apx_sphere_sep for the neck chart e o pow_lambda).  *)
(* ------------------------------------------------------------------------- *)

let APX_RPOW_NEAR_1 = prove
 (`!lam. &0 < lam /\ lam <= &1 / &2
         ==> abs(&1 - (&3 / &4) rpow lam) <= lam /\
             abs(&1 - (&4 / &3) rpow lam) <= &2 * lam /\
             &1 / &2 <= (&3 / &4) rpow lam /\ (&4 / &3) rpow lam <= &2`,
  GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  SUBGOAL_THEN `&0 <= log(&4 / &3) /\ log(&4 / &3) <= &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      GEN_REWRITE_TAC RAND_CONV [GSYM LOG_EXP] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      MP_TAC(SPEC `&1` REAL_EXP_LE_X) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&3 / &4) = --log(&4 / &3)` ASSUME_TAC THENL
   [SUBGOAL_THEN `&3 / &4 = inv(&4 / &3)` SUBST1_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    MATCH_MP_TAC LOG_INV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&3 / &4) rpow lam = exp(--(lam * log(&4 / &3))) /\
                (&4 / &3) rpow lam = exp(lam * log(&4 / &3))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[rpow; REAL_ARITH `&0 < &3 / &4 /\ &0 < &4 / &3`] THEN
    ASM_REWRITE_TAC[REAL_MUL_RNEG];
    ALL_TAC] THEN
  ABBREV_TAC `t = lam * log(&4 / &3)` THEN
  SUBGOAL_THEN `&0 <= t /\ t <= lam` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPEC `--t` REAL_EXP_LE_X) THEN MP_TAC(SPEC `t:real` REAL_EXP_LE_X) THEN
  MP_TAC(SPEC `t:real` REAL_EXP_BOUND_LEMMA) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `exp(--t) <= &1` MP_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let APX_SEP_PAIR_NEAR = prove
 (`!top atlas (e:real^3->A) O eps.
        smooth_manifold_atlas top atlas /\ apx_sphere_sep top atlas /\ &0 < eps /\
        eps <= &1 / &2 /\ mfd_param top atlas (rfs_neck_dom eps) e /\ open_in top O /\
        IMAGE e (sphere(vec 0,&1)) SUBSET O
        ==> ?q1 q2. q1 IN O /\ q2 IN O /\
                    apx_separates top (IMAGE e (sphere(vec 0,&1))) q1 q2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `rfs_neck_dom eps`; `e:real^3->A`] GRGD_PARAM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ei:A->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(basis 1:real^3) IN sphere(vec 0,&1) /\ (basis 1:real^3) IN rfs_neck_dom eps`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH] THEN
    REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN
    SIMP_TAC[APX_SVAL_UNIT; NORM_BASIS; DIMINDEX_3; ARITH; BASIS_NONZERO] THEN
    SUBGOAL_THEN `&0 < inv eps` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `open {z:real^3 | z IN rfs_neck_dom eps /\ (e:real^3->A) z IN O}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `rfs_neck_dom eps` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`e:real^3->A`; `subtopology euclidean (rfs_neck_dom eps)`;
                   `top:A topology`; `O:A->bool`] OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `basis 1:real^3` o REWRITE_RULE[OPEN_CONTAINS_BALL]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (e:real^3->A) (sphere(vec 0,&1)) SUBSET O` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `lam = min (&1 / &2) (r / &4)` THEN
  SUBGOAL_THEN `&0 < lam /\ lam <= &1 / &2 /\ &2 * lam < r` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "lam" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `lam:real` APX_RPOW_NEAR_1) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the rescaled neck chart *)
  SUBGOAL_THEN
   `mfd_neck_chart top atlas ((e:real^3->A) o (\x. norm x rpow (lam - &1) % x))`
  ASSUME_TAC THENL
   [REWRITE_TAC[mfd_neck_chart] THEN MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
    MAP_EVERY EXISTS_TAC
     [`rfs_neck_dom eps`;
      `annulus ((&1 / &2) rpow lam) (&2 rpow lam):real^3->bool`;
      `\x:real^3. norm x rpow (inv lam - &1) % x`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMT_DIFFEO_POWER_ANNULUS THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN
      SUBGOAL_THEN `&1 / &2 <= (&1 / &2) rpow lam /\ &2 rpow lam <= &2` MP_TAC THENL
       [REWRITE_TAC[rpow; REAL_ARITH `&0 < &1 / &2 /\ &0 < &2`] THEN
        GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
          [GSYM(MATCH_MP EXP_LOG (REAL_ARITH `&0 < &1 / &2`))] THEN
        GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
          [GSYM(MATCH_MP EXP_LOG (REAL_ARITH `&0 < &2`))] THEN
        REWRITE_TAC[REAL_EXP_MONO_LE] THEN
        SUBGOAL_THEN `log(&1 / &2) <= &0 /\ &0 <= log(&2)` STRIP_ASSUME_TAC THENL
         [CONJ_TAC THENL
           [REWRITE_TAC[GSYM LOG_1] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
            REAL_ARITH_TAC;
            MATCH_MP_TAC LOG_POS THEN REAL_ARITH_TAC];
          ALL_TAC] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC(REAL_ARITH `&0 <= (&1 - lam) * --l ==> l <= lam * l`) THEN
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC(REAL_ARITH `&0 <= (&1 - lam) * l ==> lam * l <= l`) THEN
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
        REAL_ARITH_TAC];
      REWRITE_TAC[APX_ANNULUS_HALF_TWO; APX_SLAB_NECK_DOM] THEN
      MATCH_MP_TAC APX_SLAB_SUBSET THEN MP_TAC APX_LOG_CONSTS THEN
      SUBGOAL_THEN `&2 <= inv eps` MP_TAC THENL
       [SUBGOAL_THEN `inv eps = &1 / eps` SUBST1_TAC THENL
         [REWRITE_TAC[real_div; REAL_MUL_LID]; ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `(e:real^3->A) o (\x. norm x rpow (lam - &1) % x)` o
              REWRITE_RULE[apx_sphere_sep] o check (fun th ->
                is_comb(concl th) &&
                fst(dest_const(fst(strip_comb(concl th)))) = "apx_sphere_sep")) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `IMAGE ((e:real^3->A) o (\x. norm x rpow (lam - &1) % x)) (sphere(vec 0,&1)) =
    IMAGE e (sphere(vec 0,&1))`
  SUBST1_TAC THENL
   [REWRITE_TAC[IMAGE_o] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (\x:real^3. x) (sphere(vec 0,&1))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_EQ THEN SIMP_TAC[IN_SPHERE_0; RPOW_ONE; VECTOR_MUL_LID];
      REWRITE_TAC[IMAGE_ID]];
    ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`(e:real^3->A)(norm(&3 / &4 % basis 1:real^3) rpow (lam - &1) %
                                       (&3 / &4 % (basis 1:real^3)))`;
                        `(e:real^3->A)(norm(&4 / &3 % basis 1:real^3) rpow (lam - &1) %
                                       (&4 / &3 % (basis 1:real^3)))`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!t. &0 < t ==> norm(t % basis 1:real^3) rpow (lam - &1) % (t % (basis 1:real^3)) =
                   t rpow lam % (basis 1:real^3)`
  (fun th -> SIMP_TAC[th; REAL_ARITH `&0 < &3 / &4 /\ &0 < &4 / &3`]) THENL
   [REPEAT STRIP_TAC THEN
    SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`; VECTOR_MUL_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [REAL_ARITH `lam = (lam - &1) + &1`] THEN
    ASM_SIMP_TAC[RPOW_ADD] THEN
    ASM_SIMP_TAC[rpow; REAL_MUL_LID; EXP_LOG];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. abs(&1 - t) < r ==> (e:real^3->A)(t % (basis 1:real^3)) IN O`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `t % basis 1:real^3 IN ball((basis 1:real^3),r)` MP_TAC THENL
     [REWRITE_TAC[IN_BALL; dist; VECTOR_ARITH `b - t % b:real^N = (&1 - t) % b`] THEN
      SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
      ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

(* Separation transfers along connected sets. *)

let APX_SEP_TRANSFER = prove
 (`!top S B A P Q (p:A) q q1 q2.
        connected_in top B /\ connected_in top A /\ connected_in top P /\
        connected_in top Q /\
        B SUBSET topspace top DIFF S /\ A SUBSET topspace top DIFF S /\
        P SUBSET topspace top DIFF S /\ Q SUBSET topspace top DIFF S /\
        ~(B INTER P = {}) /\ ~(A INTER Q = {}) /\ p IN P /\ q IN Q /\
        q1 IN B UNION A /\ q2 IN B UNION A /\ apx_separates top S q1 q2
        ==> apx_separates top S p q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `apx_separates top S (q1:A) q2` THEN
  REWRITE_TAC[apx_separates; connected_component_of; CONNECTED_IN_SUBTOPOLOGY] THEN
  STRIP_TAC THEN
  REPEAT CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:A->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `~(?t. (connected_in top t /\ t SUBSET topspace top DIFF S) /\
                     (q1:A) IN t /\ q2 IN t)` THEN
  REWRITE_TAC[] THEN
  EXISTS_TAC `K UNION P UNION Q UNION B UNION A:A->bool` THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  SUBGOAL_THEN `connected_in top (K UNION P:A->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_IN_UNION THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `connected_in top ((K UNION P) UNION B:A->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_IN_UNION THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `connected_in top (((K UNION P) UNION B) UNION Q:A->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_IN_UNION THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `connected_in top ((((K UNION P) UNION B) UNION Q) UNION A:A->bool)`
  MP_TAC THENL
   [MATCH_MP_TAC CONNECTED_IN_UNION THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN SET_TAC[]);;

(* The ends of the tube are separated by a neck sphere which is a radial   *)
(* section of a chain neck reaching below and above its tube levels.       *)

let APX_ENDS_SEP_CORE = prove
 (`!top atlas (E:real^3->A) L eps (ek:real^3->A) (e:real^3->A) (u:real^3->real) m M b a.
        smooth_manifold_atlas top atlas /\
        apx_sphere_sep top atlas /\ &0 < eps /\ eps <= &1 / &2 /\
        mfd_param top atlas (apx_slab (--inv eps) (L + inv eps)) E /\
        mfd_param top atlas (rfs_neck_dom eps) ek /\
        IMAGE ek (rfs_neck_dom eps) SUBSET IMAGE E (apx_slab (--inv eps) (L + inv eps)) /\
        mfd_param top atlas (rfs_neck_dom eps) e /\
        (\x. lift(u x)) continuous_on sphere(vec 0,&1) /\
        (!x. x IN sphere(vec 0,&1)
             ==> exp(--inv eps / sqrt(&2)) < u x /\ u x < exp(inv eps / sqrt(&2))) /\
        IMAGE e (sphere(vec 0,&1)) = IMAGE (\x. ek(u x % x)) (sphere(vec 0,&1)) /\
        --inv eps < m /\ m < M /\ M < L + inv eps /\
        (!y. y IN apx_slab (--inv eps) (L + inv eps) /\ E y IN IMAGE e (sphere(vec 0,&1))
             ==> m < apx_sval y /\ apx_sval y < M) /\
        b IN rfs_neck_dom eps /\ norm b < u(inv(norm b) % b) /\
        (?yb. yb IN apx_slab (--inv eps) m /\ E yb = ek b) /\
        a IN rfs_neck_dom eps /\ u(inv(norm a) % a) < norm a /\
        (?ya. ya IN apx_slab M (L + inv eps) /\ E ya = ek a)
        ==> apx_ends_sep top E (exp(--inv eps / sqrt(&2))) (exp((L + inv eps) / sqrt(&2)))
                         (IMAGE e (sphere(vec 0,&1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `open_in top (IMAGE (ek:real^3->A) (rfs_neck_dom eps)) /\
    IMAGE (ek:real^3->A) (rfs_neck_dom eps) SUBSET topspace top /\
    IMAGE (E:real^3->A) (apx_slab (--inv eps) (L + inv eps)) SUBSET topspace top /\
    continuous_map (subtopology euclidean (apx_slab (--inv eps) (L + inv eps)),top) E`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `rfs_neck_dom eps`; `ek:real^3->A`] GRGD_PARAM_FACTS) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `apx_slab (--inv eps) (L + inv eps)`; `E:real^3->A`] GRGD_PARAM_FACTS) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `IMAGE (e:real^3->A) (sphere(vec 0,&1)) =
               IMAGE (\x. (ek:real^3->A)(u x % x)) (sphere(vec 0,&1))` THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `ek:real^3->A`;
                 `exp(--inv eps / sqrt(&2))`; `exp(inv eps / sqrt(&2))`; `u:real^3->real`]
                APX_SECTION_SPLIT) THEN
  REWRITE_TAC[GSYM(REWRITE_RULE[apx_slab] APX_SLAB_NECK_DOM)] THEN
  ASM_REWRITE_TAC[REAL_EXP_POS_LT] THEN
  ABBREV_TAC `S0 = IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
  ABBREV_TAC `Bn = IMAGE (ek:real^3->A)
                     {z | ~(z = vec 0) /\ exp(--inv eps / sqrt(&2)) < norm z /\
                          norm z < u(inv(norm z) % z)}` THEN
  ABBREV_TAC `An = IMAGE (ek:real^3->A)
                     {z | ~(z = vec 0) /\ u(inv(norm z) % z) < norm z /\
                          norm z < exp(inv eps / sqrt(&2))}` THEN
  STRIP_TAC THEN
  UNDISCH_TAC `IMAGE (ek:real^3->A) (rfs_neck_dom eps) = S0 UNION Bn UNION An` THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  (* the separated pair near S0 *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `e:real^3->A`;
                 `IMAGE (ek:real^3->A) (rfs_neck_dom eps)`; `eps:real`] APX_SEP_PAIR_NEAR) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `S0 UNION Bn UNION An = IMAGE (ek:real^3->A) (rfs_neck_dom eps)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q1:A` (X_CHOOSE_THEN `q2:A` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(q1:A) IN Bn UNION An /\ (q2:A) IN Bn UNION An` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `apx_separates top S0 (q1:A) q2` THEN REWRITE_TAC[apx_separates] THEN
    UNDISCH_TAC `(q1:A) IN IMAGE (ek:real^3->A) (rfs_neck_dom eps)` THEN
    UNDISCH_TAC `(q2:A) IN IMAGE (ek:real^3->A) (rfs_neck_dom eps)` THEN
    UNDISCH_TAC `S0 UNION Bn UNION An = IMAGE (ek:real^3->A) (rfs_neck_dom eps)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* facts on the tube slabs *)
  SUBGOAL_THEN `apx_slab (--inv eps) m SUBSET apx_slab (--inv eps) (L + inv eps) /\
                apx_slab M (L + inv eps) SUBSET apx_slab (--inv eps) (L + inv eps) /\
                apx_slab m M SUBSET apx_slab (--inv eps) (L + inv eps)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC APX_SLAB_SUBSET THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!s. s SUBSET apx_slab (--inv eps) (L + inv eps) /\ connected s
                    ==> connected_in top (IMAGE (E:real^3->A) s)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
    EXISTS_TAC `subtopology euclidean (apx_slab (--inv eps) (L + inv eps))` THEN
    ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; CONNECTED_IN_EUCLIDEAN];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected_in top (IMAGE (E:real^3->A) (apx_slab (--inv eps) m)) /\
                connected_in top (IMAGE (E:real^3->A) (apx_slab M (L + inv eps)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[apx_slab; APX_CONNECTED_ANNULUS3];
    ALL_TAC] THEN
  SUBGOAL_THEN `Bn SUBSET topspace top DIFF S0 /\ An SUBSET topspace top DIFF (S0:A->bool)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `DISJOINT S0 (Bn:A->bool)` THEN UNDISCH_TAC `DISJOINT S0 (An:A->bool)` THEN
    UNDISCH_TAC `S0 UNION Bn UNION An = IMAGE (ek:real^3->A) (rfs_neck_dom eps)` THEN
    UNDISCH_TAC `IMAGE (ek:real^3->A) (rfs_neck_dom eps) SUBSET topspace top` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (E:real^3->A) (apx_slab (--inv eps) m) SUBSET topspace top DIFF S0`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN apx_slab (--inv eps) (L + inv eps)` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; DISCH_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `S0:A->bool`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(y:real^3) IN apx_slab (--inv eps) m` THEN
    REWRITE_TAC[APX_SLAB_SVAL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (E:real^3->A) (apx_slab M (L + inv eps)) SUBSET topspace top DIFF S0`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN apx_slab (--inv eps) (L + inv eps)` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; DISCH_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `S0:A->bool`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(y:real^3) IN apx_slab M (L + inv eps)` THEN
    REWRITE_TAC[APX_SLAB_SVAL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(Bn INTER IMAGE (E:real^3->A) (apx_slab (--inv eps) m) = {}) /\
                ~(An INTER IMAGE (E:real^3->A) (apx_slab M (L + inv eps)) = {})`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN CONJ_TAC THENL
     [EXISTS_TAC `(ek:real^3->A) b` THEN CONJ_TAC THENL
       [EXPAND_TAC "Bn" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_ELIM_THM] THEN
        UNDISCH_TAC `(b:real^3) IN rfs_neck_dom eps` THEN
        REWRITE_TAC[REWRITE_RULE[apx_slab] APX_SLAB_NECK_DOM; annulus; IN_ELIM_THM] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[GSYM NORM_POS_LT] THEN
        MP_TAC(SPEC `--inv eps / sqrt(&2)` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `yb:real^3` THEN ASM_REWRITE_TAC[]];
      EXISTS_TAC `(ek:real^3->A) a` THEN CONJ_TAC THENL
       [EXPAND_TAC "An" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_ELIM_THM] THEN
        UNDISCH_TAC `(a:real^3) IN rfs_neck_dom eps` THEN
        REWRITE_TAC[REWRITE_RULE[apx_slab] APX_SLAB_NECK_DOM; annulus; IN_ELIM_THM] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[GSYM NORM_POS_LT] THEN
        MP_TAC(SPEC `--inv eps / sqrt(&2)` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `ya:real^3` THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  (* the conclusion *)
  REWRITE_TAC[apx_ends_sep] THEN
  MAP_EVERY EXISTS_TAC [`exp(m / sqrt(&2))`; `exp(M / sqrt(&2))`] THEN
  SUBGOAL_THEN `exp(--inv eps / sqrt(&2)) < exp(m / sqrt(&2)) /\
                exp(m / sqrt(&2)) < exp(M / sqrt(&2)) /\
                exp(M / sqrt(&2)) < exp((L + inv eps) / sqrt(&2))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_SIMP_TAC[REAL_LT_DIV2_EQ]; ALL_TAC] THEN
  REWRITE_TAC[GSYM apx_slab] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `p:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(p:A) IN IMAGE E (apx_slab (--inv eps) (L + inv eps))` MP_TAC THENL
     [UNDISCH_TAC `(p:A) IN S0` THEN
      UNDISCH_TAC `S0 UNION Bn UNION An = IMAGE (ek:real^3->A) (rfs_neck_dom eps)` THEN
      UNDISCH_TAC `IMAGE (ek:real^3->A) (rfs_neck_dom eps) SUBSET
                   IMAGE E (apx_slab (--inv eps) (L + inv eps))` THEN
      SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `S0:A->bool`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(y:real^3) IN apx_slab (--inv eps) (L + inv eps)` THEN
    REWRITE_TAC[APX_SLAB_SVAL] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`p:A`; `q:A`] THEN STRIP_TAC THEN
  MATCH_MP_TAC APX_SEP_TRANSFER THEN
  MAP_EVERY EXISTS_TAC [`Bn:A->bool`; `An:A->bool`;
                        `IMAGE (E:real^3->A) (apx_slab (--inv eps) m)`;
                        `IMAGE (E:real^3->A) (apx_slab M (L + inv eps))`;
                        `q1:A`; `q2:A`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The sections clause, part 1.  The N2 facts at a fixed                    *)
(* scale eps (apx_eng_n2), short curves below the distance, and a neck      *)
(* sphere through a deep point of a neck lies in that neck within s-width 8. *)
(* ------------------------------------------------------------------------- *)

let apx_eng_n2 = new_definition
 `apx_eng_n2 (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)
             (eps:real) (alpha:real) <=>
    !x1 (e1:real^3->A) y1 z1.
       rfs_neck (top,atlas) g eps x1 e1 /\ y1 IN rfs_neck_dom eps /\
       z1 IN rfs_neck_dom eps
       ==> mfd_joinable (top,atlas) (e1 y1) (e1 z1) /\
           mfd_dist (top,atlas) g (e1 y1) (e1 z1)
           <= (&1 + alpha) * inv(sqrt(mfd_scalar atlas g x1)) *
              (abs(apx_sval y1 - apx_sval z1) + sqrt(&2) * pi) /\
           (&1 - alpha) * inv(sqrt(mfd_scalar atlas g x1)) *
           min (abs(apx_sval y1 - apx_sval z1))
               (&2 * inv eps - abs(apx_sval y1) - abs(apx_sval z1))
           <= mfd_dist (top,atlas) g (e1 y1) (e1 z1) /\
           (!gamma a b.
               mfd_c1_curve (top,atlas) gamma a b /\ gamma a = e1 y1 /\
               ~(gamma b IN IMAGE e1 (rfs_neck_dom eps))
               ==> (&1 - alpha) * inv(sqrt(mfd_scalar atlas g x1)) *
                   (inv eps - abs(apx_sval y1))
                   <= mfd_length atlas g gamma a b)`;;

let APX_DIST_SHORT_CURVE = prove
 (`!top atlas (g:A->real^3^3) p q r.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_joinable (top,atlas) p q /\ mfd_dist (top,atlas) g p q < r
     ==> ?gamma. mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
                 gamma(&0) = p /\ gamma(&1) = q /\
                 mfd_length atlas g gamma (&0) (&1) < r`,
  REWRITE_TAC[mfd_dist; mfd_joinable] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{mfd_length atlas (g:A->real^3^3) gamma (&0) (&1) | gamma |
                   mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
                   gamma(&0) = (p:A) /\ gamma(&1) = q}`; `r:real`] INF_APPROACH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; GRGD_IN_LENGTHS] THEN ASM_MESON_TAC[];
      EXISTS_TAC `&0` THEN ASM_MESON_TAC[GRGD_LENGTHS_POS_LE]];
    REWRITE_TAC[GRGD_IN_LENGTHS] THEN MESON_TAC[]]);;

(* A neck sphere through a deep point e z0 of a neck e lies in e, at s-levels *)
(* within 8 of s z0 (N2: the sphere has diameter at most about sqrt 2 pi in  *)
(* the scale of e', curves leaving e from e z0 are long, and the lower bound *)
(* of N2 bounds the s-width).                                                *)

let APX_DEEP_SPHERE = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) x' (e':real^3->A) z0 x0.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ &0 < eps /\
     apx_eng_n2 top atlas g eps (&1 / &100) /\
     rfs_neck (top,atlas) g eps x e /\ rfs_neck (top,atlas) g eps x' e' /\
     inv(sqrt(mfd_scalar atlas g x')) <= &3 / &2 * inv(sqrt(mfd_scalar atlas g x)) /\
     z0 IN rfs_neck_dom eps /\ abs(apx_sval z0) <= &7 / &8 * inv eps - &10 /\
     x0 IN sphere(vec 0,&1) /\ e' x0 = e z0
     ==> !w. w IN sphere(vec 0,&1)
             ==> ?z. z IN rfs_neck_dom eps /\ e z = e' w /\
                     abs(apx_sval z - apx_sval z0) <= &8`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x0:real^3) IN rfs_neck_dom eps /\ (w:real^3) IN rfs_neck_dom eps /\
                apx_sval x0 = &0 /\ apx_sval w = &0`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[]; ASM SET_TAC[];
      MATCH_MP_TAC APX_SVAL_UNIT THEN ASM_MESON_TAC[IN_SPHERE_0];
      MATCH_MP_TAC APX_SVAL_UNIT THEN ASM_MESON_TAC[IN_SPHERE_0]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x)) /\
                &0 < inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x'))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
    ASM_MESON_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv eps` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`x':A`; `e':real^3->A`; `x0:real^3`; `w:real^3`] o
    REWRITE_RULE[apx_eng_n2] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_eng_n2")) (concl th))) THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0; REAL_ADD_LID] THEN STRIP_TAC THEN
  ABBREV_TAC `ri = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x))` THEN
  ABBREV_TAC `ri' = inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x'))` THEN
  ABBREV_TAC `D1 = mfd_dist (top,atlas) (g:A->real^3^3) (e(z0:real^3)) (e'(w:real^3))` THEN
  SUBGOAL_THEN `D1 <= &909 / &125 * ri` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + &1 / &100) * ri' * sqrt(&2) * pi` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + &1 / &100) * (&3 / &2 * ri) * &24 / &5` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; APX_SQRT2_PI] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[SQRT_POS_LE; REAL_POS; PI_POS_LE];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `rx = (&1 - &1 / &100) * ri * (inv eps - abs(apx_sval(z0:real^3)))` THEN
  SUBGOAL_THEN `D1 < rx` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&909 / &125 * ri` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "rx" THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `(&1 - &1 / &100) * ri * &10` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(e':real^3->A) w IN IMAGE e (rfs_neck_dom eps)` MP_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `(e:real^3->A) z0`; `(e':real^3->A) w`; `rx:real`] APX_DIST_SHORT_CURVE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`x:A`; `e:real^3->A`; `z0:real^3`; `z0:real^3`] o
      REWRITE_RULE[apx_eng_n2] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_eng_n2")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`gamma:real->A`; `&0`; `&1`] o
      CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`x:A`; `e:real^3->A`; `z0:real^3`; `z:real^3`] o
    REWRITE_RULE[apx_eng_n2] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_eng_n2")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`eps:real`; `z:real^3`] APX_SVAL_NECK_DOM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `min (abs(apx_sval(z0:real^3) - apx_sval(z:real^3)))
        (&2 * inv eps - abs(apx_sval z0) - abs(apx_sval z)) <= &8`
  MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "real_min")) (concl th))) THEN
    UNDISCH_TAC `D1 <= &909 / &125 * ri` THEN UNDISCH_TAC `&0 < ri` THEN
    SPEC_TAC(`min (abs(apx_sval(z0:real^3) - apx_sval(z:real^3)))
                  (&2 * inv eps - abs(apx_sval z0) - abs(apx_sval z))`, `mn:real`) THEN
    GEN_TAC THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `ri * ((&1 - &1 / &100) * mn) <= ri * (&909 / &125)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC]);;

(* The shifts of a chain with the comparison invariant are below 3/(2 eps)  *)
(* (plus slack): the negative quarter of N(i+1) lies in N(i).               *)

let APX_CMP_SHIFT_UPPER = prove
 (`!top atlas (g:A->real^3^3) eps n x (e:int->real^3->A) E L c d0 (i:num).
     &0 < eps /\ eps <= &1 / &4 /\
     apx_chain (top,atlas) g eps {i:int | &0 <= i /\ i <= &n} x e /\
     apx_eng_cmp top atlas eps E L e c n d0 /\ i < n
     ==> c(i + 1) - c i < &3 / &2 * inv eps + &1 + d0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&4 <= inv eps /\ inv(&2 * eps) = inv eps / &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPECL [`eps:real`; `&1 / &4`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `?v:real^3. v IN apx_slab (--inv eps) (--inv(&2 * eps)) /\
                           v IN rfs_neck_dom eps /\ apx_sval v = --inv(&2 * eps) - &1`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `exp((--inv(&2 * eps) - &1) / sqrt(&2)) % basis 1:real^3` THEN
    SIMP_TAC[APX_RAY_IN_SLAB; APX_RAY_IN_DOM; APX_RAY_SVAL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `n:num`; `x:int->A`; `e:int->real^3->A`] APX_CHAIN_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT1 o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[SUBSET; IN_UNION; IN_INTER] THEN
  DISCH_THEN(MP_TAC o SPEC `(e:int->real^3->A)(&(i + 1)) v`) THEN
  ANTS_TAC THENL
   [DISJ2_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `i:num` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
    REWRITE_RULE[apx_eng_cmp] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_eng_cmp")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `v:real^3`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`eps:real`; `z:real^3`] APX_SVAL_NECK_DOM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Every point of the tube is deep in some neck of the chain, or lies at a  *)
(* shallow level at the top of the last neck or the bottom of the first.    *)

let APX_TUBE_DEEP_COVER = prove
 (`!top atlas (g:A->real^3^3) eps n x (e:int->real^3->A) E L c d0 p.
     &0 < eps /\ eps <= &1 / &128 /\ &0 <= d0 /\ &32 * d0 <= inv eps /\
     apx_chain (top,atlas) g eps {i:int | &0 <= i /\ i <= &n} x e /\
     apx_eng_cmp top atlas eps E L e c n d0 /\
     p IN UNIONS {IMAGE (e(&i)) (rfs_neck_dom eps) | i <= n}
     ==> ?i z. i <= n /\ z IN rfs_neck_dom eps /\ e(&i) z = p /\
               (abs(apx_sval z) <= &7 / &8 * inv eps - &10 \/
                (i = n /\ &7 / &8 * inv eps - &10 < apx_sval z) \/
                (i = 0 /\ apx_sval z < --(&7 / &8 * inv eps - &10)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&128 <= inv eps /\ inv(&2 * eps) = inv eps / &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPECL [`eps:real`; `&1 / &128`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `p IN UNIONS {IMAGE ((e:int->real^3->A)(&i)) (rfs_neck_dom eps) | i <= n}` THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:A->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) MP_TAC)) THEN
  ASM_REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  ASM_CASES_TAC `abs(apx_sval(z:real^3)) <= &7 / &8 * inv eps - &10` THENL
   [MAP_EVERY EXISTS_TAC [`i:num`; `z:real^3`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`eps:real`; `z:real^3`] APX_SVAL_NECK_DOM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `n:num`; `x:int->A`; `e:int->real^3->A`] APX_CHAIN_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "nk") (CONJUNCTS_THEN2 (LABEL_TAC "ov") (K ALL_TAC))) THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[apx_eng_cmp] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_eng_cmp")) (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "gr") (CONJUNCTS_THEN2 (LABEL_TAC "c1") (K ALL_TAC))))) THEN
  SUBGOAL_THEN `!j. j <= n ==> mfd_param top atlas (rfs_neck_dom eps) ((e:int->real^3->A)(&j))`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN USE_THEN "nk" (MP_TAC o SPEC `j:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[rfs_neck]];
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 < apx_sval(z:real^3)` THENL
   [ASM_CASES_TAC `i:num = n` THENL
     [MAP_EVERY EXISTS_TAC [`i:num`; `z:real^3`] THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      DISJ2_TAC THEN DISJ1_TAC THEN CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(i:num) < n` ASSUME_TAC THENL
     [UNDISCH_TAC `(i:num) <= n` THEN UNDISCH_TAC `~(i:num = n)` THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^3) IN apx_slab (inv(&2 * eps)) (inv eps)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "ov" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[SUBSET; IN_UNION; IN_INTER] THEN
    DISCH_THEN(MP_TAC o SPEC `p:A`) THEN
    ANTS_TAC THENL
     [DISJ1_TAC THEN UNDISCH_TAC `(e:int->real^3->A)(&i) z = p` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^3` (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
    USE_THEN "c1" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^3`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(e:int->real^3->A)(&i) z = p` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `z':real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `z':real^3 = z` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_INJ THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `rfs_neck_dom eps`; `(e:int->real^3->A)(&i)`] THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `n:num`; `x:int->A`; `e:int->real^3->A`; `E:real^3->A`;
                   `L:real`; `c:num->real`; `d0:real`; `i:num`] APX_CMP_SHIFT_UPPER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    USE_THEN "gr" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MAP_EVERY EXISTS_TAC [`(i:num) + 1`; `v:real^3`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [UNDISCH_TAC `(i:num) < n` THEN ARITH_TAC; ALL_TAC] THEN
    DISJ1_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `i:num = 0` THENL
   [MAP_EVERY EXISTS_TAC [`i:num`; `z:real^3`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    DISJ2_TAC THEN DISJ2_TAC THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `?j. i = j + 1` (X_CHOOSE_THEN `j:num` SUBST_ALL_TAC) THENL
   [EXISTS_TAC `i - 1` THEN UNDISCH_TAC `~(i:num = 0)` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(j:num) < n` ASSUME_TAC THENL
   [UNDISCH_TAC `(j:num) + 1 <= n` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3) IN apx_slab (--inv eps) (--inv(&2 * eps))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "ov" (MP_TAC o SPEC `j:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[SUBSET; IN_UNION; IN_INTER] THEN
  DISCH_THEN(MP_TAC o SPEC `p:A`) THEN
  ANTS_TAC THENL
   [DISJ2_TAC THEN UNDISCH_TAC `(e:int->real^3->A)(&(j + 1)) z = p` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  USE_THEN "c1" (MP_TAC o SPEC `j:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z':real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `n:num`; `x:int->A`; `e:int->real^3->A`; `E:real^3->A`;
                 `L:real`; `c:num->real`; `d0:real`; `j:num`] APX_CMP_SHIFT_UPPER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  USE_THEN "gr" (MP_TAC o SPEC `j:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MAP_EVERY EXISTS_TAC [`j:num`; `z':real^3`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [UNDISCH_TAC `(j:num) < n` THEN ARITH_TAC; ALL_TAC] THEN
  DISJ1_TAC THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The sections clause, part 2.  A neck sphere which is a                   *)
(* radial section of a neck ek, at ek-levels where the tube chart E is      *)
(* exactly ek (up to the shift c0 of the levels), separates the ends of the *)
(* tube.  Used at both ends of the tube.                                     *)
(* ------------------------------------------------------------------------- *)

let APX_EXP_SVAL_LT = prove
 (`!t r. &0 < r
         ==> (exp(t / sqrt(&2)) < r <=> t < sqrt(&2) * log r) /\
             (r < exp(t / sqrt(&2)) <=> sqrt(&2) * log r < t)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `exp(t / sqrt(&2)) < exp(log r)` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[EXP_LOG];
      REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN REAL_ARITH_TAC];
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `exp(log r) < exp(t / sqrt(&2))` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[EXP_LOG];
      REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC]]);;

let APX_EXACT_SEP = prove
 (`!top atlas (E:real^3->A) L eps (ek:real^3->A) (e:real^3->A) (u:real^3->real) lo hi c0.
     smooth_manifold_atlas top atlas /\ apx_sphere_sep top atlas /\
     &0 < eps /\ eps <= &1 / &2 /\
     mfd_param top atlas (apx_slab (--inv eps) (L + inv eps)) E /\
     mfd_param top atlas (rfs_neck_dom eps) ek /\
     IMAGE ek (rfs_neck_dom eps) SUBSET IMAGE E (apx_slab (--inv eps) (L + inv eps)) /\
     mfd_param top atlas (rfs_neck_dom eps) e /\
     (\x. lift(u x)) continuous_on sphere(vec 0,&1) /\
     (!x. x IN sphere(vec 0,&1)
          ==> exp(--inv eps / sqrt(&2)) < u x /\ u x < exp(inv eps / sqrt(&2))) /\
     IMAGE e (sphere(vec 0,&1)) = IMAGE (\x. ek(u x % x)) (sphere(vec 0,&1)) /\
     --inv eps <= lo /\ hi <= inv eps /\ --inv eps <= lo + c0 /\ hi + c0 <= L + inv eps /\
     (!x. x IN sphere(vec 0,&1) ==> lo < apx_sval(u x % x) /\ apx_sval(u x % x) < hi) /\
     (!z. z IN rfs_neck_dom eps /\ lo < apx_sval z /\ apx_sval z < hi
          ==> ?y. y IN apx_slab (--inv eps) (L + inv eps) /\ E y = ek z /\
                  apx_sval y = apx_sval z + c0)
     ==> apx_ends_sep top E (exp(--inv eps / sqrt(&2))) (exp((L + inv eps) / sqrt(&2)))
                      (IMAGE e (sphere(vec 0,&1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?x1 x2. x1 IN sphere(vec 0,&1) /\ x2 IN sphere(vec 0,&1) /\
                        !x. x IN sphere(vec 0,&1)
                            ==> (u:real^3->real) x1 <= u x /\ u x <= u x2`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`u:real^3->real`; `sphere(vec 0:real^3,&1)`] CONTINUOUS_ATTAINS_SUP) THEN
    MP_TAC(ISPECL [`u:real^3->real`; `sphere(vec 0:real^3,&1)`] CONTINUOUS_ATTAINS_INF) THEN
    REWRITE_TAC[COMPACT_SPHERE; SPHERE_EQ_EMPTY; o_DEF] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `~(&1 < &0)`] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN sphere(vec 0,&1)
        ==> u x % x IN rfs_neck_dom eps /\ &0 < (u:real^3->real) x /\
            apx_sval(u x % x) = sqrt(&2) * log(u x)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`u:real^3->real`; `exp(--inv eps / sqrt(&2))`; `exp(inv eps / sqrt(&2))`]
                 APX_SECTION_BASICS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^3` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM(REWRITE_RULE[apx_slab] APX_SLAB_NECK_DOM)] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[apx_sval] THEN
    MP_TAC(SPEC `--inv eps / sqrt(&2)` REAL_EXP_POS_LT) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> t = `exp(--inv eps / sqrt(&2))`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN sphere(vec 0,&1)
        ==> apx_sval((u:real^3->real) x1 % x1) <= apx_sval(u x % x) /\
            apx_sval(u x % x) <= apx_sval(u x2 % x2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ; LOG_MONO_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `lo < apx_sval((u:real^3->real) x1 % x1) /\ apx_sval(u x2 % x2) < hi`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `x1:real^3` o check (fun th ->
        is_forall (concl th) && can (find_term (fun t -> t = `lo:real`)) (concl th) &&
        not (can (find_term (fun t -> t = `c0:real`)) (concl th))));
      FIRST_X_ASSUM(MP_TAC o SPEC `x2:real^3` o check (fun th ->
        is_forall (concl th) && can (find_term (fun t -> t = `lo:real`)) (concl th) &&
        not (can (find_term (fun t -> t = `c0:real`)) (concl th))))] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(basis 1:real^3) IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  ABBREV_TAC `smin = apx_sval((u:real^3->real) x1 % x1)` THEN
  ABBREV_TAC `smax = apx_sval((u:real^3->real) x2 % x2)` THEN
  SUBGOAL_THEN `smin <= smax` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `x1:real^3` o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `smax:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `m = (lo + smin) / &2 + c0` THEN
  ABBREV_TAC `M = (smax + hi) / &2 + c0` THEN
  ABBREV_TAC `sb = (lo + (lo + smin) / &2) / &2` THEN
  ABBREV_TAC `sa = ((smax + hi) / &2 + hi) / &2` THEN
  ABBREV_TAC `b = exp(sb / sqrt(&2)) % basis 1:real^3` THEN
  ABBREV_TAC `a = exp(sa / sqrt(&2)) % basis 1:real^3` THEN
  SUBGOAL_THEN `b IN rfs_neck_dom eps /\ apx_sval b = sb /\ norm b = exp(sb / sqrt(&2)) /\
                inv(norm b) % b = basis 1:real^3`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN
    SIMP_TAC[APX_RAY_IN_DOM; APX_RAY_SVAL; NORM_BASIS; DIMINDEX_3; ARITH; APX_SCALE_UNIT;
             REAL_EXP_POS_LT] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `a IN rfs_neck_dom eps /\ apx_sval a = sa /\ norm a = exp(sa / sqrt(&2)) /\
                inv(norm a) % a = basis 1:real^3`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN
    SIMP_TAC[APX_RAY_IN_DOM; APX_RAY_SVAL; NORM_BASIS; DIMINDEX_3; ARITH; APX_SCALE_UNIT;
             REAL_EXP_POS_LT] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (u:real^3->real)(basis 1) /\
                smin <= sqrt(&2) * log(u(basis 1)) /\ sqrt(&2) * log(u(basis 1)) <= smax`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `basis 1:real^3 IN sphere(vec 0,&1)`) o
      check (fun th -> is_forall (concl th) &&
                       can (find_term (fun t -> t = `smax:real`)) (concl th))) THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `basis 1:real^3 IN sphere(vec 0,&1)`) o
      check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "log")) (concl th))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `--inv eps < m /\ m < M /\ M < L + inv eps` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `norm b < (u:real^3->real)(inv(norm b) % b) /\ u(inv(norm a) % a) < norm a`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[APX_EXP_SVAL_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?yb. yb IN apx_slab (--inv eps) m /\ (E:real^3->A) yb = (ek:real^3->A) b` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `b:real^3` o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `c0:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `yb:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `yb:real^3` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(yb:real^3) IN apx_slab (--inv eps) (L + inv eps)` THEN
    ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?ya. ya IN apx_slab M (L + inv eps) /\ (E:real^3->A) ya = (ek:real^3->A) a` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `a:real^3` o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `c0:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ya:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `ya:real^3` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(ya:real^3) IN apx_slab (--inv eps) (L + inv eps)` THEN
    ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN apx_slab (--inv eps) (L + inv eps) /\
        (E:real^3->A) y IN IMAGE (e:real^3->A) (sphere(vec 0,&1))
        ==> m < apx_sval y /\ apx_sval y < M`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    UNDISCH_TAC `(E:real^3->A) y IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN sphere(vec 0,&1)`) o
      check (fun th -> is_forall (concl th) &&
                       can (find_term (fun t -> t = `smax:real`)) (concl th))) THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN sphere(vec 0,&1)`) o
      check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "log")) (concl th))) THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN sphere(vec 0,&1)`) o
      check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> t = `lo:real`)) (concl th) &&
        not (can (find_term (fun t -> t = `c0:real`)) (concl th)))) THEN
    REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o SPEC `(u:real^3->real) x % x` o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `c0:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y':real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `y':real^3 = y` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_INJ THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `apx_slab (--inv eps) (L + inv eps)`; `E:real^3->A`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC APX_ENDS_SEP_CORE THEN
  MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `ek:real^3->A`;
                        `u:real^3->real`; `m:real`; `M:real`; `b:real^3`; `a:real^3`] THEN
  ASM_REWRITE_TAC[]);;

(* The deep case: the neck sphere lies within s-width 8 of a deep level s0 *)
(* of a chain neck ek whose tube levels are s + ci up to 2 d0.             *)

let APX_DEEP_SEP = prove
 (`!top atlas (E:real^3->A) L eps (ek:real^3->A) (e:real^3->A) (u:real^3->real) z0 ci d0.
     smooth_manifold_atlas top atlas /\ apx_sphere_sep top atlas /\
     &0 < eps /\ eps <= &1 / &128 /\ &0 <= d0 /\ &32 * d0 <= inv eps /\
     &0 <= ci /\ ci <= L /\
     mfd_param top atlas (apx_slab (--inv eps) (L + inv eps)) E /\
     mfd_param top atlas (rfs_neck_dom eps) ek /\
     IMAGE ek (rfs_neck_dom eps) SUBSET IMAGE E (apx_slab (--inv eps) (L + inv eps)) /\
     mfd_param top atlas (rfs_neck_dom eps) e /\
     (\x. lift(u x)) continuous_on sphere(vec 0,&1) /\
     (!x. x IN sphere(vec 0,&1)
          ==> exp(--inv eps / sqrt(&2)) < u x /\ u x < exp(inv eps / sqrt(&2))) /\
     IMAGE e (sphere(vec 0,&1)) = IMAGE (\x. ek(u x % x)) (sphere(vec 0,&1)) /\
     z0 IN rfs_neck_dom eps /\ abs(apx_sval z0) <= &7 / &8 * inv eps - &10 /\
     (!w. w IN sphere(vec 0,&1)
          ==> ?z. z IN rfs_neck_dom eps /\ ek z = e w /\ abs(apx_sval z - apx_sval z0) <= &8) /\
     (!z. z IN rfs_neck_dom eps
          ==> ?y. y IN apx_slab (--inv eps) (L + inv eps) /\ E y = ek z /\
                  abs(apx_sval y - (apx_sval z + ci)) <= &2 * d0)
     ==> apx_ends_sep top E (exp(--inv eps / sqrt(&2))) (exp((L + inv eps) / sqrt(&2)))
                      (IMAGE e (sphere(vec 0,&1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&128 <= inv eps` ASSUME_TAC THENL
   [MP_TAC(SPECL [`eps:real`; `&1 / &128`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN sphere(vec 0,&1)
        ==> u x % x IN rfs_neck_dom eps /\ &0 < (u:real^3->real) x /\
            apx_sval(u x % x) = sqrt(&2) * log(u x) /\
            abs(apx_sval(u x % x) - apx_sval(z0:real^3)) <= &8`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`u:real^3->real`; `exp(--inv eps / sqrt(&2))`; `exp(inv eps / sqrt(&2))`]
                 APX_SECTION_BASICS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^3` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM(REWRITE_RULE[apx_slab] APX_SLAB_NECK_DOM)] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < (u:real^3->real) x` ASSUME_TAC THENL
     [MP_TAC(SPEC `--inv eps / sqrt(&2)` REAL_EXP_POS_LT) THEN
      FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN sphere(vec 0,&1)`) o
        check (fun th -> is_forall (concl th) &&
          can (find_term (fun t -> t = `exp(--inv eps / sqrt(&2))`)) (concl th))) THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[apx_sval] THEN
    SUBGOAL_THEN `(ek:real^3->A)((u:real^3->real) x % x) IN IMAGE (e:real^3->A) (sphere(vec 0,&1))`
    MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:real^3` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(w:real^3) IN sphere(vec 0,&1)`) o
      check (fun th -> is_forall (concl th) &&
                       can (find_term (fun t -> t = `&8`)) (concl th))) THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `z:real^3 = (u:real^3->real) x % x` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_INJ THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `rfs_neck_dom eps`; `ek:real^3->A`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `abs(apx_sval((u:real^3->real) x % x) - apx_sval(z0:real^3)) <= &8` THEN
    ASM_REWRITE_TAC[apx_sval];
    ALL_TAC] THEN
  SUBGOAL_THEN `(basis 1:real^3) IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  ABBREV_TAC `s0 = apx_sval(z0:real^3)` THEN
  ABBREV_TAC `m = s0 + ci - &8 - &2 * d0 - &1` THEN
  ABBREV_TAC `M = s0 + ci + &8 + &2 * d0 + &1` THEN
  ABBREV_TAC `sb = --inv eps + &1 / &2` THEN
  ABBREV_TAC `sa = inv eps - &1 / &2` THEN
  ABBREV_TAC `b = exp(sb / sqrt(&2)) % basis 1:real^3` THEN
  ABBREV_TAC `a = exp(sa / sqrt(&2)) % basis 1:real^3` THEN
  SUBGOAL_THEN `b IN rfs_neck_dom eps /\ apx_sval b = sb /\ norm b = exp(sb / sqrt(&2)) /\
                inv(norm b) % b = basis 1:real^3`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN
    SIMP_TAC[APX_RAY_IN_DOM; APX_RAY_SVAL; NORM_BASIS; DIMINDEX_3; ARITH; APX_SCALE_UNIT;
             REAL_EXP_POS_LT] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `a IN rfs_neck_dom eps /\ apx_sval a = sa /\ norm a = exp(sa / sqrt(&2)) /\
                inv(norm a) % a = basis 1:real^3`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN
    SIMP_TAC[APX_RAY_IN_DOM; APX_RAY_SVAL; NORM_BASIS; DIMINDEX_3; ARITH; APX_SCALE_UNIT;
             REAL_EXP_POS_LT] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (u:real^3->real)(basis 1) /\
                abs(sqrt(&2) * log(u(basis 1)) - s0) <= &8`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `basis 1:real^3 IN sphere(vec 0,&1)`) o
      check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "log")) (concl th))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `--inv eps < m /\ m < M /\ M < L + inv eps` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `norm b < (u:real^3->real)(inv(norm b) % b) /\ u(inv(norm a) % a) < norm a`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[APX_EXP_SVAL_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?yb. yb IN apx_slab (--inv eps) m /\ (E:real^3->A) yb = (ek:real^3->A) b`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `b:real^3` o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `ci:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `yb:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `yb:real^3` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(yb:real^3) IN apx_slab (--inv eps) (L + inv eps)` THEN
    ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?ya. ya IN apx_slab M (L + inv eps) /\ (E:real^3->A) ya = (ek:real^3->A) a`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `a:real^3` o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `ci:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ya:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `ya:real^3` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(ya:real^3) IN apx_slab (--inv eps) (L + inv eps)` THEN
    ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN apx_slab (--inv eps) (L + inv eps) /\
        (E:real^3->A) y IN IMAGE (e:real^3->A) (sphere(vec 0,&1))
        ==> m < apx_sval y /\ apx_sval y < M`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    UNDISCH_TAC `(E:real^3->A) y IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN sphere(vec 0,&1)`) o
      check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "log")) (concl th))) THEN
    REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o SPEC `(u:real^3->real) x % x` o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `ci:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y':real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `y':real^3 = y` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_INJ THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `apx_slab (--inv eps) (L + inv eps)`; `E:real^3->A`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC APX_ENDS_SEP_CORE THEN
  MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `ek:real^3->A`;
                        `u:real^3->real`; `m:real`; `M:real`; `b:real^3`; `a:real^3`] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The sections clause, part 3.  Sections from N4 with                      *)
(* continuous radius, their levels, and the context apx_eng_sec of the      *)
(* final tube (chain, tube, comparison invariant, N2, N4 and the scale      *)
(* comparison at the scale eps) with its basic facts.                       *)
(* ------------------------------------------------------------------------- *)

let APX_SMOOTH_NEAR_CONTINUOUS_ON = prove
 (`!k (f:real^M->real^N). smooth_near k f ==> f continuous_on k`,
  REWRITE_TAC[smooth_near] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `u:real^M->bool` THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]);;

let APX_SECTION_DATA = prove
 (`!(ek:real^3->A) eps S.
     apx_section ek (exp(--(inv(sqrt(&2) * eps)))) (exp(inv(sqrt(&2) * eps))) S
     ==> ?u. (\x. lift(u x)) continuous_on sphere(vec 0,&1) /\
             (!x. x IN sphere(vec 0,&1)
                  ==> exp(--inv eps / sqrt(&2)) < u x /\ u x < exp(inv eps / sqrt(&2))) /\
             S = IMAGE (\x. ek(u x % x)) (sphere(vec 0,&1))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `--(inv(sqrt(&2) * eps)) = --inv eps / sqrt(&2) /\
                inv(sqrt(&2) * eps) = inv eps / sqrt(&2)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[real_div; REAL_INV_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[apx_section] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^3->real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC APX_SMOOTH_NEAR_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]);;

let APX_SECTION_LEVELS = prove
 (`!top atlas (ek:real^3->A) (e:real^3->A) (u:real^3->real) eps lo hi.
     mfd_param top atlas (rfs_neck_dom eps) ek /\
     (!x. x IN sphere(vec 0,&1)
          ==> exp(--inv eps / sqrt(&2)) < u x /\ u x < exp(inv eps / sqrt(&2))) /\
     IMAGE e (sphere(vec 0,&1)) = IMAGE (\x. ek(u x % x)) (sphere(vec 0,&1)) /\
     IMAGE e (sphere(vec 0,&1)) SUBSET IMAGE ek (apx_slab lo hi) /\
     apx_slab lo hi SUBSET rfs_neck_dom eps
     ==> !x. x IN sphere(vec 0,&1) ==> lo < apx_sval(u x % x) /\ apx_sval(u x % x) < hi`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`u:real^3->real`; `exp(--inv eps / sqrt(&2))`; `exp(inv eps / sqrt(&2))`]
               APX_SECTION_BASICS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^3` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM(REWRITE_RULE[apx_slab] APX_SLAB_NECK_DOM)] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(ek:real^3->A)((u:real^3->real) x % x) IN IMAGE ek (apx_slab lo hi)` MP_TAC THENL
   [UNDISCH_TAC `IMAGE (e:real^3->A) (sphere(vec 0,&1)) SUBSET IMAGE ek (apx_slab lo hi)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(u:real^3->real) x % x = z` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_INJ THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `rfs_neck_dom eps`; `ek:real^3->A`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(z:real^3) IN apx_slab lo hi` THEN REWRITE_TAC[APX_SLAB_SVAL] THEN
  REAL_ARITH_TAC);;

let APX_CMP_MONO = prove
 (`!(c:num->real) k eps.
        &0 < eps /\ (!i. i < k ==> inv(&2 * eps) <= c(i + 1) - c i)
        ==> !i j. i <= j /\ j <= k ==> c i <= c j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:num->real`; `k:num`; `eps:real`] APX_CMP_GROWTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`i:num`; `j:num`]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= &(j - i) * inv(&2 * eps)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_INV THEN
    ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let apx_eng_sec = new_definition
 `apx_eng_sec (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)
              (eps:real) (n:num) (x:int->A) (e:int->real^3->A) (E:real^3->A) (L:real)
              (c:num->real) (d0:real) <=>
    smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
    apx_sphere_sep top atlas /\
    &0 < eps /\ eps <= &1 / &128 /\ &0 <= d0 /\ &32 * d0 <= inv eps /\
    apx_eng_n2 top atlas g eps (&1 / &100) /\
    (!x1 (e1:real^3->A) x2 e2.
        rfs_neck (top,atlas) g eps x1 e1 /\ rfs_neck (top,atlas) g eps x2 e2 /\
        IMAGE e2 (sphere(vec 0,&1)) SUBSET IMAGE e1 (rfs_neck_dom eps)
        ==> apx_section e1 (exp(--(inv(sqrt(&2) * eps)))) (exp(inv(sqrt(&2) * eps)))
                        (IMAGE e2 (sphere(vec 0,&1)))) /\
    (!x1 (e1:real^3->A) x2 e2 v.
        rfs_neck (top,atlas) g eps x1 e1 /\ rfs_neck (top,atlas) g eps x2 e2 /\
        v IN rfs_neck_dom eps /\ e2 v IN IMAGE e1 (rfs_neck_dom eps)
        ==> inv(sqrt(mfd_scalar atlas g x2)) <= &3 / &2 * inv(sqrt(mfd_scalar atlas g x1))) /\
    apx_chain (top,atlas) g eps {i:int | &0 <= i /\ i <= &n} x e /\
    apx_eng_tube top atlas eps (e(&0)) (e(&n)) E L /\
    IMAGE E (apx_slab (--inv eps) (L + inv eps)) =
    UNIONS {IMAGE (e(&i)) (rfs_neck_dom eps) | i <= n} /\
    apx_eng_cmp top atlas eps E L e c n d0`;;

let APX_SEC_FACTS = prove
 (`!top atlas (g:A->real^3^3) eps n x (e:int->real^3->A) E L c d0.
     apx_eng_sec top atlas g eps n x e E L c d0
     ==> &128 <= inv eps /\ inv(&2 * eps) = inv eps / &2 /\ inv(&8 * eps) = inv eps / &8 /\
         &0 <= L /\
         mfd_param top atlas (apx_slab (--inv eps) (L + inv eps)) E /\
         (!j. j <= n ==> rfs_neck (top,atlas) g eps (x(&j)) (e(&j)) /\
                         mfd_param top atlas (rfs_neck_dom eps) (e(&j)) /\
                         IMAGE (e(&j)) (rfs_neck_dom eps) SUBSET
                         IMAGE E (apx_slab (--inv eps) (L + inv eps)) /\
                         &0 <= c j /\ c j <= L) /\
         (!j z. j <= n /\ z IN rfs_neck_dom eps
                ==> ?y. y IN apx_slab (--inv eps) (L + inv eps) /\ E y = e(&j) z /\
                        abs(apx_sval y - (apx_sval z + c j)) <= &2 * d0) /\
         (!z. z IN rfs_neck_dom eps /\ --inv(&8 * eps) < apx_sval z
              ==> ?y. y IN apx_slab (--inv eps) (L + inv eps) /\ E y = e(&n) z /\
                      apx_sval y = apx_sval z + L) /\
         (!z. z IN rfs_neck_dom eps /\ apx_sval z < inv(&8 * eps)
              ==> ?y. y IN apx_slab (--inv eps) (L + inv eps) /\ E y = e(&0) z /\
                      apx_sval y = apx_sval z + &0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[apx_eng_sec] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&128 <= inv eps /\ inv(&2 * eps) = inv eps / &2 /\
                inv(&8 * eps) = inv eps / &8`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(SPECL [`eps:real`; `&1 / &128`] REAL_LE_INV2) THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_eng_tube] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_eng_tube")) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `n:num`; `x:int->A`; `e:int->real^3->A`] APX_CHAIN_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "nk" o CONJUNCT1) THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[apx_eng_cmp] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_eng_cmp")) (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "gr") (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "c7") (K ALL_TAC)))))))) THEN
  MP_TAC(SPECL [`c:num->real`; `n:num`; `eps:real`] APX_CMP_MONO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "mono")] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    USE_THEN "nk" (MP_TAC o SPEC `j:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[rfs_neck];
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `q:A` THEN DISCH_TAC THEN
      EXISTS_TAC `IMAGE ((e:int->real^3->A)(&j)) (rfs_neck_dom eps)` THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `(c:num->real) 0 = &0` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      USE_THEN "mono" MATCH_MP_TAC THEN ASM_REWRITE_TAC[LE_0];
      UNDISCH_TAC `(c:num->real) n = L` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      USE_THEN "mono" MATCH_MP_TAC THEN ASM_REWRITE_TAC[LE_REFL]];
    MAP_EVERY X_GEN_TAC [`j:num`; `z:real^3`] THEN STRIP_TAC THEN
    USE_THEN "c7" (MP_TAC o SPEC `j:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MESON_TAC[];
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `eps:real`;
                   `(e:int->real^3->A)(&0)`; `(e:int->real^3->A)(&n)`; `E:real^3->A`;
                   `L:real`] APX_TUBE_TOP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN EXISTS_TAC `y:real^3` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`L - inv(&8 * eps)`; `L + inv eps`; `--inv eps`; `L + inv eps`]
                   APX_SLAB_SUBSET) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
      REAL_ARITH_TAC];
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN EXISTS_TAC `z:real^3` THEN
    MP_TAC(SPECL [`eps:real`; `z:real^3`] APX_SVAL_NECK_DOM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `(z:real^3) IN apx_slab (--inv eps) (inv(&8 * eps))` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ADD_RID] THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`--inv eps`; `inv(&8 * eps)`; `--inv eps`; `L + inv eps`]
                   APX_SLAB_SUBSET) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
      ASM_SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The sections clause, part 4.  The deep case and the two                  *)
(* end cases in the context apx_eng_sec, and the clause itself: every       *)
(* eps-neck sphere in the final tube separates its ends.                     *)
(* ------------------------------------------------------------------------- *)

let APX_SEC_DEEP = prove
 (`!top atlas (g:A->real^3^3) eps n x (e:int->real^3->A) E L c d0 x' (e':real^3->A)
    i z0 x0.
     apx_eng_sec top atlas g eps n x e E L c d0 /\
     rfs_neck (top,atlas) g eps x' e' /\
     i <= n /\ z0 IN rfs_neck_dom eps /\ abs(apx_sval z0) <= &7 / &8 * inv eps - &10 /\
     x0 IN sphere(vec 0,&1) /\ e' x0 = e(&i) z0
     ==> apx_ends_sep top E (exp(--inv eps / sqrt(&2))) (exp((L + inv eps) / sqrt(&2)))
                      (IMAGE e' (sphere(vec 0,&1)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> ASSUME_TAC th THEN
      STRIP_ASSUME_TAC(MATCH_MP APX_SEC_FACTS th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[apx_eng_sec] th)) STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(i:num) <= n`) o check (fun th ->
    is_forall (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck")) (concl th) &&
    can (find_term (fun t -> t = `L:real`)) (concl th))) THEN
  SUBGOAL_THEN `mfd_param top atlas (rfs_neck_dom eps) (e':real^3->A)` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x' e'` THEN SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(sqrt(mfd_scalar atlas (g:A->real^3^3) x')) <=
                &3 / &2 * inv(sqrt(mfd_scalar atlas g ((x:int->A)(&i))))`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `&3 / &2`)) (concl th))) THEN
    MAP_EVERY EXISTS_TAC [`(e:int->real^3->A)(&i)`; `e':real^3->A`; `x0:real^3`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `eps:real`; `(x:int->A)(&i)`; `(e:int->real^3->A)(&i)`; `x':A`;
                 `e':real^3->A`; `z0:real^3`; `x0:real^3`] APX_DEEP_SPHERE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `IMAGE (e':real^3->A) (sphere(vec 0,&1)) SUBSET
                IMAGE ((e:int->real^3->A)(&i)) (rfs_neck_dom eps)`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(w:real^3) IN sphere(vec 0,&1)`) o
      check (fun th -> is_forall (concl th) && can (find_term (fun t -> t = `&8`)) (concl th))) THEN
    REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`(x:int->A)(&i)`; `(e:int->real^3->A)(&i)`; `x':A`;
                              `e':real^3->A`] o
    check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_section")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->real` STRIP_ASSUME_TAC o MATCH_MP APX_SECTION_DATA) THEN
  SUBGOAL_THEN
   `!z. z IN rfs_neck_dom eps
        ==> ?y. y IN apx_slab (--inv eps) (L + inv eps) /\
                (E:real^3->A) y = (e:int->real^3->A)(&i) z /\
                abs(apx_sval y - (apx_sval z + c i)) <= &2 * d0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `&2 * d0`)) (concl th) &&
      length(fst(strip_forall(concl th))) = 2)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC APX_DEEP_SEP THEN
  MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `(e:int->real^3->A)(&i)`;
                        `u:real^3->real`; `z0:real^3`; `(c:num->real) i`; `d0:real`] THEN
  ASM_REWRITE_TAC[]);;

let APX_SEC_TOP = prove
 (`!top atlas (g:A->real^3^3) eps n x (e:int->real^3->A) E L c d0 x' (e':real^3->A).
     apx_eng_sec top atlas g eps n x e E L c d0 /\
     rfs_neck (top,atlas) g eps x' e' /\
     IMAGE e' (sphere(vec 0,&1)) SUBSET
     IMAGE (e(&n)) (apx_slab (&7 / &8 * inv eps - &10) (inv eps))
     ==> apx_ends_sep top E (exp(--inv eps / sqrt(&2))) (exp((L + inv eps) / sqrt(&2)))
                      (IMAGE e' (sphere(vec 0,&1)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> ASSUME_TAC th THEN
      STRIP_ASSUME_TAC(MATCH_MP APX_SEC_FACTS th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[apx_eng_sec] th)) STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP (SPEC `n:num` LE_REFL) o check (fun th ->
    is_forall (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck")) (concl th) &&
    can (find_term (fun t -> t = `L:real`)) (concl th))) THEN
  SUBGOAL_THEN `mfd_param top atlas (rfs_neck_dom eps) (e':real^3->A)` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x' e'` THEN SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `apx_slab (&7 / &8 * inv eps - &10) (inv eps) SUBSET rfs_neck_dom eps`
  ASSUME_TAC THENL [MATCH_MP_TAC APX_SLAB_SUB_DOM THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`(x:int->A)(&n)`; `(e:int->real^3->A)(&n)`; `x':A`;
                              `e':real^3->A`] o
    check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_section")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->real` STRIP_ASSUME_TAC o MATCH_MP APX_SECTION_DATA) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(e:int->real^3->A)(&n)`; `e':real^3->A`; `u:real^3->real`; `eps:real`;
                 `&7 / &8 * inv eps - &10`; `inv eps`] APX_SECTION_LEVELS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `eps <= &1 / &2 /\ --inv eps <= --inv(&8 * eps) /\ inv eps <= inv eps /\
                --inv eps <= --inv(&8 * eps) + L /\ inv eps + L <= L + inv eps`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!w. w IN sphere(vec 0,&1)
                    ==> --inv(&8 * eps) < apx_sval((u:real^3->real) w % w) /\
                        apx_sval(u w % w) < inv eps`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(w:real^3) IN sphere(vec 0,&1)`) o
      check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> t = `&7 / &8 * inv eps - &10`)) (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN rfs_neck_dom eps /\ --inv(&8 * eps) < apx_sval z /\
                    apx_sval z < inv eps
                    ==> ?y. y IN apx_slab (--inv eps) (L + inv eps) /\
                            (E:real^3->A) y = (e:int->real^3->A)(&n) z /\
                            apx_sval y = apx_sval z + L`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC APX_EXACT_SEP THEN
  MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `(e:int->real^3->A)(&n)`;
                        `u:real^3->real`; `--inv(&8 * eps)`; `inv eps`; `L:real`] THEN
  ASM_REWRITE_TAC[]);;

let APX_SEC_BOT = prove
 (`!top atlas (g:A->real^3^3) eps n x (e:int->real^3->A) E L c d0 x' (e':real^3->A).
     apx_eng_sec top atlas g eps n x e E L c d0 /\
     rfs_neck (top,atlas) g eps x' e' /\
     IMAGE e' (sphere(vec 0,&1)) SUBSET
     IMAGE (e(&0)) (apx_slab (--inv eps) (--(&7 / &8 * inv eps - &10)))
     ==> apx_ends_sep top E (exp(--inv eps / sqrt(&2))) (exp((L + inv eps) / sqrt(&2)))
                      (IMAGE e' (sphere(vec 0,&1)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> ASSUME_TAC th THEN
      STRIP_ASSUME_TAC(MATCH_MP APX_SEC_FACTS th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[apx_eng_sec] th)) STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP (SPEC `n:num` LE_0) o check (fun th ->
    is_forall (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck")) (concl th) &&
    can (find_term (fun t -> t = `L:real`)) (concl th))) THEN
  SUBGOAL_THEN `mfd_param top atlas (rfs_neck_dom eps) (e':real^3->A)` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x' e'` THEN SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `apx_slab (--inv eps) (--(&7 / &8 * inv eps - &10)) SUBSET rfs_neck_dom eps`
  ASSUME_TAC THENL [MATCH_MP_TAC APX_SLAB_SUB_DOM THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`(x:int->A)(&0)`; `(e:int->real^3->A)(&0)`; `x':A`;
                              `e':real^3->A`] o
    check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_section")) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->real` STRIP_ASSUME_TAC o MATCH_MP APX_SECTION_DATA) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(e:int->real^3->A)(&0)`; `e':real^3->A`; `u:real^3->real`; `eps:real`;
                 `--inv eps`; `--(&7 / &8 * inv eps - &10)`] APX_SECTION_LEVELS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `eps <= &1 / &2 /\ --inv eps <= --inv eps /\ inv(&8 * eps) <= inv eps /\
                --inv eps <= --inv eps + &0 /\ inv(&8 * eps) + &0 <= L + inv eps`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!w. w IN sphere(vec 0,&1)
                    ==> --inv eps < apx_sval((u:real^3->real) w % w) /\
                        apx_sval(u w % w) < inv(&8 * eps)`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(w:real^3) IN sphere(vec 0,&1)`) o
      check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> t = `--(&7 / &8 * inv eps - &10)`)) (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN rfs_neck_dom eps /\ --inv eps < apx_sval z /\
                    apx_sval z < inv(&8 * eps)
                    ==> ?y. y IN apx_slab (--inv eps) (L + inv eps) /\
                            (E:real^3->A) y = (e:int->real^3->A)(&0) z /\
                            apx_sval y = apx_sval z + &0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC APX_EXACT_SEP THEN
  MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `(e:int->real^3->A)(&0)`;
                        `u:real^3->real`; `--inv eps`; `inv(&8 * eps)`; `&0`] THEN
  ASM_REWRITE_TAC[]);;

(* The sections clause of apx_tube for the final tube: a neck sphere in the *)
(* tube has a deep point in some chain neck, or lies (connected) in the top *)
(* region of the last neck or the bottom region of the first.               *)

let APX_TUBE_SECTIONS = prove
 (`!top atlas (g:A->real^3^3) eps n x (e:int->real^3->A) E L c d0.
     apx_eng_sec top atlas g eps n x e E L c d0
     ==> !x' e'. rfs_neck (top,atlas) g eps x' e' /\
                 IMAGE e' (sphere(vec 0,&1)) SUBSET
                 IMAGE E (annulus (exp(--inv eps / sqrt(&2))) (exp((L + inv eps) / sqrt(&2))))
                 ==> apx_ends_sep top E (exp(--inv eps / sqrt(&2)))
                                  (exp((L + inv eps) / sqrt(&2)))
                                  (IMAGE e' (sphere(vec 0,&1)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`x':A`; `e':real^3->A`] THEN
  REWRITE_TAC[GSYM apx_slab] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_SEC_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[apx_eng_sec] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_eng_sec")) (concl th))) THEN
  ASM_CASES_TAC
   `?i z0 x0. i <= n /\ z0 IN rfs_neck_dom eps /\
              abs(apx_sval z0) <= &7 / &8 * inv eps - &10 /\
              x0 IN sphere(vec 0,&1) /\ (e':real^3->A) x0 = (e:int->real^3->A)(&i) z0` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `z0:real^3`
      (X_CHOOSE_THEN `x0:real^3` STRIP_ASSUME_TAC))) THEN
    MATCH_MP_TAC APX_SEC_DEEP THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `n:num`;
                          `x:int->A`; `e:int->real^3->A`; `c:num->real`; `d0:real`;
                          `x':A`; `i:num`; `z0:real^3`; `x0:real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (e':real^3->A) (sphere(vec 0,&1)) SUBSET
    IMAGE ((e:int->real^3->A)(&n)) (apx_slab (&7 / &8 * inv eps - &10) (inv eps)) UNION
    IMAGE (e(&0)) (apx_slab (--inv eps) (--(&7 / &8 * inv eps - &10)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `n:num`; `x:int->A`; `e:int->real^3->A`; `E:real^3->A`;
                   `L:real`; `c:num->real`; `d0:real`; `(e':real^3->A) w`]
                  APX_TUBE_DEEP_COVER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (e':real^3->A) (sphere(vec 0,&1)) SUBSET
                   IMAGE E (apx_slab (--inv eps) (L + inv eps))` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `z:real^3`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))))) THEN
    MP_TAC(SPECL [`eps:real`; `z:real^3`] APX_SVAL_NECK_DOM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN2
      (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))) THENL
     [UNDISCH_TAC
       `~(?i z0 x0. i <= n /\ z0 IN rfs_neck_dom eps /\
                    abs(apx_sval z0) <= &7 / &8 * inv eps - &10 /\
                    x0 IN sphere(vec 0,&1) /\
                    (e':real^3->A) x0 = (e:int->real^3->A)(&i) z0)` THEN
      MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
      MAP_EVERY EXISTS_TAC [`i:num`; `z:real^3`; `w:real^3`] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IN_UNION] THEN DISJ2_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the two end regions are open, disjoint, and the sphere is connected *)
  SUBGOAL_THEN
   `open_in top (IMAGE ((e:int->real^3->A)(&n)) (apx_slab (&7 / &8 * inv eps - &10) (inv eps))) /\
    open_in top (IMAGE ((e:int->real^3->A)(&0)) (apx_slab (--inv eps) (--(&7 / &8 * inv eps - &10))))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom eps`] THEN
    ASM_SIMP_TAC[LE_REFL; LE_0] THEN REWRITE_TAC[apx_slab; OPEN_ANNULUS] THEN
    REWRITE_TAC[GSYM apx_slab] THEN MATCH_MP_TAC APX_SLAB_SUB_DOM THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `DISJOINT (IMAGE ((e:int->real^3->A)(&n)) (apx_slab (&7 / &8 * inv eps - &10) (inv eps)))
             (IMAGE ((e:int->real^3->A)(&0)) (apx_slab (--inv eps) (--(&7 / &8 * inv eps - &10))))`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `n = 0` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      SUBGOAL_THEN `apx_slab (&7 / &8 * inv eps - &10) (inv eps) SUBSET rfs_neck_dom eps /\
                    apx_slab (--inv eps) (--(&7 / &8 * inv eps - &10)) SUBSET rfs_neck_dom eps`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC APX_SLAB_SUB_DOM THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `!y z. y IN rfs_neck_dom eps /\ z IN rfs_neck_dom eps /\
                          (e:int->real^3->A)(&0) y = e(&0) z ==> y = z`
      ASSUME_TAC THENL
       [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_PARAM_INJ THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                              `rfs_neck_dom eps`; `(e:int->real^3->A)(&0)`] THEN
        ASM_SIMP_TAC[LE_REFL];
        ALL_TAC] THEN
      SUBGOAL_THEN `DISJOINT (apx_slab (&7 / &8 * inv eps - &10) (inv eps))
                             (apx_slab (--inv eps) (--(&7 / &8 * inv eps - &10)))`
      ASSUME_TAC THENL
       [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
        X_GEN_TAC `y:real^3` THEN REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      UNDISCH_TAC `!y z. y IN rfs_neck_dom eps /\ z IN rfs_neck_dom eps /\
                         (e:int->real^3->A)(&0) y = e(&0) z ==> y = z` THEN
      UNDISCH_TAC `DISJOINT (apx_slab (&7 / &8 * inv eps - &10) (inv eps))
                            (apx_slab (--inv eps) (--(&7 / &8 * inv eps - &10)))` THEN
      UNDISCH_TAC `apx_slab (&7 / &8 * inv eps - &10) (inv eps) SUBSET rfs_neck_dom eps` THEN
      UNDISCH_TAC `apx_slab (--inv eps) (--(&7 / &8 * inv eps - &10)) SUBSET rfs_neck_dom eps` THEN
      SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `n:num`; `x:int->A`; `e:int->real^3->A`] APX_CHAIN_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`0`; `n:num`] o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `~(n = 0)` THEN ARITH_TAC; DISCH_THEN(MP_TAC o CONJUNCT2)] THEN
    SUBGOAL_THEN
     `apx_slab (&7 / &8 * inv eps - &10) (inv eps) SUBSET apx_slab (inv(&2 * eps)) (inv eps) /\
      apx_slab (--inv eps) (--(&7 / &8 * inv eps - &10)) SUBSET rfs_neck_dom eps`
    MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC APX_SLAB_SUBSET THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC APX_SLAB_SUB_DOM THEN ASM_REAL_ARITH_TAC];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected_in top (IMAGE (e':real^3->A) (sphere(vec 0,&1)))` ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
    EXISTS_TAC `subtopology euclidean (rfs_neck_dom eps):(real^3)topology` THEN
    REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; CONNECTED_IN_EUCLIDEAN] THEN
    SIMP_TAC[CONNECTED_SPHERE; DIMINDEX_3; ARITH] THEN
    ASM_SIMP_TAC[APX_UNIT_SPHERE_NECK_DOM] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `rfs_neck_dom eps`; `e':real^3->A`] GRGD_PARAM_FACTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x' e'` THEN SIMP_TAC[rfs_neck];
      STRIP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`;
                 `IMAGE ((e:int->real^3->A)(&n)) (apx_slab (&7 / &8 * inv eps - &10) (inv eps))`;
                 `IMAGE ((e:int->real^3->A)(&0))
                        (apx_slab (--inv eps) (--(&7 / &8 * inv eps - &10)))`;
                 `IMAGE (e':real^3->A) (sphere(vec 0,&1))`]
                CONNECTED_IN_SUBSET_SEPARATED_UNION) THEN
  ASM_SIMP_TAC[SEPARATED_IN_OPEN_SETS] THEN STRIP_TAC THENL
   [MATCH_MP_TAC APX_SEC_TOP; MATCH_MP_TAC APX_SEC_BOT] THEN
  MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `n:num`;
                        `x:int->A`; `e:int->real^3->A`; `c:num->real`; `d0:real`;
                        `x':A`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Assembly of the corrected A13 from M6b:                                  *)
(* the engine with its comparison invariant (APX_A13_ENGINE), the context   *)
(* apx_eng_sec at small eps (N2, N4, the scale comparison from              *)
(* APX_TRANSITION_DERIV), and the apx_tube clauses.                          *)
(* ------------------------------------------------------------------------- *)

let APX_INV_SQRT_RATIO = prove
 (`!r1 r2. &0 < r1 /\ &0 < r2 /\ r1 / r2 <= &9 / &4
           ==> inv(sqrt r2) <= &3 / &2 * inv(sqrt r1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt r1 /\ &0 < sqrt r2` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt r1 <= &3 / &2 * sqrt r2` ASSUME_TAC THENL
   [SUBGOAL_THEN `sqrt(r1 / r2) <= sqrt(&9 / &4)` MP_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `sqrt(&9 / &4) = &3 / &2` SUBST1_TAC THENL
     [MATCH_MP_TAC SQRT_UNIQUE THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 / &2 * inv(sqrt r1) = inv(&2 / &3 * sqrt r1)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_INV_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC);;

(* A13_CORE with the constants and the comparison invariant exposed. *)

let APX_A13_ENGINE = prove
 (`!u:A->bool.
     SMT_PRODUCT2_STATEMENT u
     ==> ?alpha1 eps1.
           &0 < alpha1 /\ alpha1 <= &1 / &4096 /\ sqrt alpha1 <= &1 / &2560 /\
           &0 < eps1 /\ eps1 <= alpha1 /\
           (!top atlas (g:A->real^3^3) eps x (e:real^3->A) y.
              &0 < eps /\ eps <= eps1 /\ riemannian_metric atlas g /\
              rfs_neck (top,atlas) g eps x e /\ y IN rfs_neck_dom eps
              ==> abs(lscalar (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y - &1)
                  <= alpha1 /\
                  (!w. abs(lricci (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y w w -
                           lricci (cylinder_flow (&0)) y w w)
                       <= alpha1 * (w dot (cylinder_flow (&0) y ** w)))) /\
           !top atlas g eps n x e.
              &0 < eps /\ eps <= min eps1 (&1 / &96) /\ hausdorff_space top /\
              riemannian_metric atlas g /\
              apx_chain (top,atlas) g eps {i:int | &0 <= i /\ i <= &n} x (e:int->real^3->A)
              ==> ?E L c. apx_eng_tube top atlas eps (e(&0)) (e(&n)) E L /\
                          IMAGE E (apx_slab (--inv eps) (L + inv eps)) =
                          UNIONS {IMAGE (e(&i)) (rfs_neck_dom eps) | i <= n} /\
                          apx_eng_cmp top atlas eps E L e c n (&80 * sqrt alpha1 * inv eps)`,
  GEN_TAC THEN DISCH_TAC THEN
  X_CHOOSE_THEN `Ds:real->real` (X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC)
    APX_SMOOTH_STEP_DERIV THEN
  MP_TAC(SPEC `C:real` APX_ENGINE_CONSTANTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `alpha1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `u:A->bool` APX_NECK_CURV) THEN REWRITE_TAC[APX_NECK_CURV_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `alpha1:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n1"))) THEN
  MAP_EVERY EXISTS_TAC [`alpha1:real`; `min eps2 alpha1`] THEN
  SUBGOAL_THEN `&0 < min eps2 alpha1 /\ min eps2 alpha1 <= alpha1 /\ min eps2 alpha1 <= eps2`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!top atlas (g:A->real^3^3) eps x (e:real^3->A) y.
      &0 < eps /\ eps <= min eps2 alpha1 /\ riemannian_metric atlas g /\
      rfs_neck (top,atlas) g eps x e /\ y IN rfs_neck_dom eps
      ==> abs(lscalar (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y - &1)
          <= alpha1 /\
          (!w. abs(lricci (\z. mfd_scalar atlas g x %% rfs_pullback atlas e g z) y w w -
                   lricci (cylinder_flow (&0)) y w w)
               <= alpha1 * (w dot (cylinder_flow (&0) y ** w)))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "n1" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`alpha1:real`; `min eps2 alpha1`] APX_CHAIN_TUBE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "ct")] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  USE_THEN "ct" (MP_TAC o SPECL [`u:A->bool`; `top:A topology`;
    `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `eps:real`; `n:num`;
    `x:int->A`; `e:int->real^3->A`; `Ds:real->real`; `C:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[LE_REFL]);;

(* The corrected A13: APX_A13_STATEMENT with apx_sphere_sep                 *)
(* and exact-end regions 1/(8 eps), as an implication from M6b.             *)

let APX_A13 = prove
 (`!u:A->bool.
     SMT_PRODUCT2_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !top atlas g eps n x e.
              &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\
              riemannian_metric atlas g /\ apx_sphere_sep top atlas /\
              apx_chain (top,atlas) g eps {i:int | &0 <= i /\ i <= &n} x
                        (e:int->real^3->A)
              ==> ?E L f f'.
                    &0 <= L /\ sphere_diffeo f f' /\
                    mfd_param top atlas (apx_slab (--inv eps) (L + inv eps)) E /\
                    (!y. y IN apx_slab (--inv eps) (inv(&8 * eps)) ==> E y = e (&0) y) /\
                    (!y. y IN apx_slab (L - inv(&8 * eps)) (L + inv eps)
                         ==> E y = e (&n) (radial_ext f (exp(--L / sqrt(&2)) % y))) /\
                    IMAGE E (apx_slab (--inv eps) (L + inv eps)) =
                    apx_chain_union eps {i:int | &0 <= i /\ i <= &n} e /\
                    apx_tube (top,atlas) g eps E (exp(--inv eps / sqrt(&2)))
                             (exp((L + inv eps) / sqrt(&2)))`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP APX_A13_ENGINE) THEN
  DISCH_THEN(X_CHOOSE_THEN `alpha1:real` (X_CHOOSE_THEN `eps1:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "eng"))))))))) THEN
  MP_TAC(ISPEC `u:A->bool` APX_NECK_DIST) THEN REWRITE_TAC[APX_NECK_DIST_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `&1 / &100`) THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n2"))) THEN
  MP_TAC(ISPEC `u:A->bool` APX_NECK_SECTION_UNCOND) THEN
  REWRITE_TAC[APX_NECK_SECTION_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps4:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n4"))) THEN
  MP_TAC(SPECL [`alpha1:real`; `eps1:real`] APX_TRANSITION_DERIV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN(LABEL_TAC "tr")] THEN
  EXISTS_TAC `min (min eps1 (&1 / &128)) (min eps3 eps4)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `eps <= eps1 /\ eps <= &1 / &128 /\ eps <= eps3 /\ eps <= eps4 /\
                eps <= min eps1 (&1 / &96)` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "eng" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `eps:real`; `n:num`; `x:int->A`; `e:int->real^3->A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `E:real^3->A` (X_CHOOSE_THEN `L:real`
    (X_CHOOSE_THEN `c:num->real` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `eps:real`; `n:num`; `x:int->A`; `e:int->real^3->A`] APX_CHAIN_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `0` o CONJUNCT1) THEN REWRITE_TAC[LE_0] THEN SIMP_TAC[rfs_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `apx_eng_sec (top:A topology) atlas g eps n x e E L c
                 (&80 * sqrt alpha1 * inv eps)`
  ASSUME_TAC THENL
   [REWRITE_TAC[apx_eng_sec] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LE_INV; REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2560 * sqrt alpha1) * inv eps` THEN
      CONJ_TAC THENL
       [REAL_ARITH_TAC;
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_SIMP_TAC[REAL_LE_INV; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[apx_eng_n2] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
      USE_THEN "n2" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
        `g:A->real^3^3`; `eps:real`; `x1:A`; `e1:real^3->A`; `y1:real^3`; `z1:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      USE_THEN "n4" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
        `g:A->real^3^3`; `eps:real`; `x1:A`; `e1:real^3->A`; `x2:A`; `e2:real^3->A`;
        `&1`]) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[APX_UNIT_SPHERE_NECK_DOM; REAL_LT_01]; SIMP_TAC[]];
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `rfs_neck_dom eps`; `e1:real^3->A`] GRGD_PARAM_FACTS) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x1 e1` THEN SIMP_TAC[rfs_neck];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `ei:A->real^3` STRIP_ASSUME_TAC) THEN
      USE_THEN "tr" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
        `g:A->real^3^3`; `eps:real`; `x1:A`; `e1:real^3->A`; `x2:A`; `e2:real^3->A`;
        `ei:A->real^3`; `v:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_TAC THEN
      MATCH_MP_TAC APX_INV_SQRT_RATIO THEN REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x1 e1` THEN SIMP_TAC[rfs_neck];
        UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x2 e2` THEN SIMP_TAC[rfs_neck];
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_SEC_FACTS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP APX_TUBE_SECTIONS) THEN
  UNDISCH_TAC `apx_eng_tube top atlas eps ((e:int->real^3->A)(&0)) (e(&n)) E L` THEN
  REWRITE_TAC[apx_eng_tube] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `f':real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`E:real^3->A`; `L:real`; `f:real^3->real^3`; `f':real^3->real^3`] THEN
  ASM_REWRITE_TAC[APX_CHAIN_UNION_UPTO] THEN
  REWRITE_TAC[apx_tube] THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT] THEN
  REWRITE_TAC[GSYM apx_slab] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LT] THEN
    SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV2_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `p:A` THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:A->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`(x:int->A)(&k)`; `(e:int->real^3->A)(&k)`] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `k:num <= n`) o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck")) (concl th) &&
      can (find_term (fun t -> t = `L:real`)) (concl th))) THEN
    SIMP_TAC[];
    UNDISCH_TAC `(p:A) IN t` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `q:A` THEN DISCH_TAC THEN
    EXISTS_TAC `IMAGE ((e:int->real^3->A)(&k)) (rfs_neck_dom eps)` THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[]]);;

