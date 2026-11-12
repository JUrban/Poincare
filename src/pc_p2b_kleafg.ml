(* ========================================================================= *)
(* Unit pc_p2b_kleafg (Part 2B): generic leaf geometry for the compact leaf  *)
(* (pc_p2b_kleaf) and the cylinder model (pc_p2b_cylleaf) in the proof of    *)
(* P2B_SPLIT_ROUND_STATEMENT.  For a primitive h of g(X,.) on an open set V  *)
(* (X parallel and unit): chart derivative and Hessian of h, unit normal X   *)
(* and II = 0 of the level sets, Ric(a,b) = R/2 g(a,b) on X-perp, R_L = R,   *)
(* Ric_L = J^T Ric J, joint smoothness of the leaf chart representatives,    *)
(* and the leaf Ricci flow.  Main theorems: P2BKL_LEAF_RICCI_FLOW            *)
(* (one interval) and P2BKL_LEAF_FLOW_ALL (every a < b).                     *)
(* ========================================================================= *)

needs "src/pc_p2b_shsplit.ml";;
needs "src/pc_p2b_kglob.ml";;

prioritize_real();;
type_invention_error := true;;


(* P2BKL.L1 A primitive h of g(X,.) on an open set V (X parallel and unit): *)
(* its chart derivative at x is g x X x, its chart Hessians vanish, the     *)
(* level sets of h have unit normal X, second fundamental form 0, and       *)
(* tangent vectors g-orthogonal to X (versions of P2BSS_H_DERIV_AT, _H_HESS, *)
(* _H_NORMAL, _H_II, _JAC_TANGENT for p2bkg_prim on V).                     *)

let P2BKL_PRIM_DERIV_AT = prove
 (`!top atlas (g:A->real^3^3) (X:A->real^3) V h x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     open_in top V /\ p2bkg_prim atlas g X V h /\ x IN V
     ==> ((\y. lift(h(chart_inv (chart_at atlas x) y))) has_derivative
          (\w. lift(X x dot (g x ** w)))) (at (SND(chart_at atlas x) x)) /\
         frechet_derivative (\y. lift(h(chart_inv (chart_at atlas x) y)))
                            (at (SND(chart_at atlas x) x)) =
         (\w. lift(X x dot (g x ** w)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `x:A`]
         P2BSS_G_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `((\y. lift((h:A->real)(chart_inv (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) y)))
     has_derivative (\w. lift((X:A->real^3) x dot ((g:A->real^3^3) x ** w))))
    (at (SND(chart_at atlas x) x))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p2bkg_prim atlas (g:A->real^3^3) (X:A->real^3) V (h:A->real)` THEN
    REWRITE_TAC[p2bkg_prim] THEN
    DISCH_THEN(MP_TAC o SPECL [`chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)`;
                               `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) x`] o
               CONJUNCT2) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
      ALL_TAC] THEN
    REWRITE_TAC[p2bkg_cform] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `X:A->real^3`; `x:A`]
           P2BX0_VREP_AT) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `x:A`]
           METRIC_LOCAL_AT) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `w:real^3` THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [DOT_SYM] THEN MATCH_MP_TAC P2BKF_SYM_DOT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  ASM_REWRITE_TAC[]);;

let P2BKL_PRIM_HESS = prove
 (`!top atlas (g:A->real^3^3) (X:A->real^3) V h c u a b.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     p2b_parallel_on atlas g (topspace top) X /\ open_in top V /\
     p2bkg_prim atlas g X V h /\ c IN atlas /\ u IN IMAGE (SND c) (FST c INTER V)
     ==> cmp_lhess (metric_local atlas c g) (\y. h(chart_inv c y)) u a b = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `c:(A->bool)#(A->real^3)`] P2BSS_PAR_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `S = IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c INTER V)` THEN
  SUBGOAL_THEN `open (S:real^3->bool) /\ S SUBSET IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
      ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET];
      MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTER_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `transp(metric_local atlas (c:(A->bool)#(A->real^3)) (g:A->real^3^3) u) =
                metric_local atlas c g u` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN S
        ==> frechet_derivative (\x. lift((h:A->real)(chart_inv (c:(A->bool)#(A->real^3)) x))) (at z) =
            (\w. lift(mfd_vrep atlas (X:A->real^3) c z dot (metric_local atlas c (g:A->real^3^3) z ** w)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    UNDISCH_TAC `p2bkg_prim atlas (g:A->real^3^3) (X:A->real^3) V (h:A->real)` THEN
    REWRITE_TAC[p2bkg_prim] THEN
    DISCH_THEN(MP_TAC o SPECL [`c:(A->bool)#(A->real^3)`; `z:real^3`] o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[p2bkg_cform] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `w:real^3` THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [DOT_SYM] THEN MATCH_MP_TAC P2BKF_SYM_DOT THEN
    ASM_MESON_TAC[metric_field; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^3) IN S` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^3) IN IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\z. lift(drop(frechet_derivative
                     (\x. lift((h:A->real)(chart_inv (c:(A->bool)#(A->real^3)) x)))
                     (at z) a))) has_derivative
     (\w. lift(frechet_derivative (mfd_vrep atlas (X:A->real^3) c) (at u) w dot
               (metric_local atlas c (g:A->real^3^3) u ** a) +
               mfd_vrep atlas X c u dot (mderiv (metric_local atlas c g) u w ** a)))) (at u)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    EXISTS_TAC `\z. lift(mfd_vrep atlas (X:A->real^3) (c:(A->bool)#(A->real^3)) z dot
                         (metric_local atlas c (g:A->real^3^3) z ** a))` THEN
    EXISTS_TAC `S:real^3->bool` THEN
    ASM_SIMP_TAC[LIFT_DROP] THEN
    MP_TAC(ISPECL [`metric_local atlas (c:(A->bool)#(A->real^3)) (g:A->real^3^3)`;
                   `frechet_derivative ((vectorize:real^3^3->real^(3,3)finite_prod) o
                                        metric_local atlas (c:(A->bool)#(A->real^3)) (g:A->real^3^3))
                                       (at u)`;
                   `mfd_vrep atlas (X:A->real^3) (c:(A->bool)#(A->real^3))`;
                   `frechet_derivative (mfd_vrep atlas (X:A->real^3) (c:(A->bool)#(A->real^3))) (at u)`;
                   `(\z:real^3. (a:real^3))`; `(\w:real^3. vec 0:real^3)`; `u:real^3`]
           LRG_HAS_DERIVATIVE_DOT_MATVEC) THEN
    REWRITE_TAC[HAS_DERIVATIVE_CONST; MATRIX_VECTOR_MUL_RZERO; VECTOR_ADD_RID] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
        EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` THEN
        ASM_MESON_TAC[metric_field];
        MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)`;
                       `mfd_vrep atlas (X:A->real^3) (c:(A->bool)#(A->real^3))`]
               SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
        ASM_SIMP_TAC[]];
      REWRITE_TAC[mderiv]];
    ALL_TAC] THEN
  REWRITE_TAC[cmp_lhess; lnabla] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SUM_SING_NUMSEG] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  ASM_SIMP_TAC[LIFT_DROP] THEN
  SUBGOAL_THEN `frechet_derivative (mfd_vrep atlas (X:A->real^3) (c:(A->bool)#(A->real^3))) (at u) b =
                --(christoffel (metric_local atlas c (g:A->real^3^3)) u b (mfd_vrep atlas X c u))`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^3`; `b:real^3`] o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "christoffel")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "frechet_derivative")) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)`;
                 `metric_local atlas (c:(A->bool)#(A->real^3)) (g:A->real^3^3)`; `u:real^3`;
                 `mfd_vrep atlas (X:A->real^3) (c:(A->bool)#(A->real^3)) u`; `b:real^3`; `a:real^3`]
         LRG_MDERIV_CHRISTOFFEL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP P2BKF_SYM_DOT th]) THEN
  REWRITE_TAC[DOT_LNEG; DOT_RNEG; MATRIX_VECTOR_MUL_RNEG] THEN REAL_ARITH_TAC);;

let P2BKL_NORMAL = prove
 (`!top atlas (g:A->real^3^3) (X:A->real^3) V h x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     open_in top V /\ p2bkg_prim atlas g X V h /\ x IN V /\ X x dot (g x ** X x) = &1
     ==> lvs_df atlas h x = g x ** X x /\ lvs_normal atlas g h x = X x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `x:A`]
         P2BSS_G_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lvs_df atlas (h:A->real) x = (g:A->real^3^3) x ** (X:A->real^3) x`
  ASSUME_TAC THENL
   [REWRITE_TAC[lvs_df] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `X:A->real^3`; `V:A->bool`; `h:A->real`; `x:A`] P2BKL_PRIM_DERIV_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
    SUBGOAL_THEN `!w. (X:A->real^3) x dot ((g:A->real^3^3) x ** w) = (g x ** X x) dot w`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [DOT_SYM] THEN MATCH_MP_TAC P2BKF_SYM_DOT THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SIMP_TAC[CART_EQ; LAMBDA_BETA; LIFT_DROP; DOT_BASIS];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[lvs_normal] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `h:A->real`; `x:A`] LVS_GRAD2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MATRIX_INV th]) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LID] THEN ONCE_REWRITE_TAC[DOT_SYM] THEN
  ASM_SIMP_TAC[SQRT_1; REAL_INV_1; VECTOR_MUL_LID]);;

let P2BKL_II = prove
 (`!top atlas (g:A->real^3^3) (X:A->real^3) V h u x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     p2b_parallel_on atlas g (topspace top) X /\ open_in top V /\
     p2bkg_prim atlas g X V h /\ x IN V
     ==> lvs_II top atlas g V h u x = mat 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!a b. cmp_lhess (metric_local atlas (chart_at atlas x) (g:A->real^3^3))
                    (\y. (h:A->real)(chart_inv (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) y))
                    (SND(chart_at atlas x) x) a b = &0`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC P2BKL_PRIM_HESS THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `X:A->real^3`; `V:A->bool`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  REWRITE_TAC[lvs_II] THEN SIMP_TAC[CART_EQ; LAMBDA_BETA; MAT_COMPONENT; COND_ID] THEN
  ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO]);;

let P2BKL_JAC_TANGENT = prove
 (`!top atlas (g:A->real^3^3) (X:A->real^3) V h u x z.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     open_in top V /\ p2bkg_prim atlas g X V h /\
     (!y. y IN V ==> X y dot (g y ** X y) = &1) /\
     lvs_regular atlas V h u /\ x IN lvs_set V h u
     ==> lvs_jac top atlas V h u x z dot (g x ** X x) = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN V` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:A) IN lvs_set V (h:A->real) u` THEN SIMP_TAC[lvs_set; IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `V:A->bool`; `h:A->real`; `u:real`; `x:A`] LVS_POINT_FORM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3->bool` (X_CHOOSE_THEN `G:real^3->real^3^3`
    (X_CHOOSE_THEN `z0:real^2` (X_CHOOSE_THEN `D:real^3->real^3` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `V:A->bool`; `h:A->real`; `x:A`] P2BKL_NORMAL) THEN
  ASM_SIMP_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `invertible(transp(matrix(D:real^3->real^3)) ** (g:A->real^3^3) x ** matrix D)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `invertible((G:real^3->real^3^3)(lvs_iota z0))` MP_TAC THENL
     [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(X:A->real^3) x =
    inv(sqrt(basis 3 dot (matrix_inv(transp(matrix(D:real^3->real^3)) ** (g:A->real^3^3) x **
                                     matrix D) ** basis 3))) %
    D(matrix_inv(transp(matrix D) ** g x ** matrix D) ** basis 3)`
  SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_RMUL; REAL_ENTIRE] THEN DISJ2_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP MATRIX_WORKS th)]) THEN
  REWRITE_TAC[P2BSS_CONG_DOT; MATRIX_VECTOR_MUL_ASSOC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MATRIX_INV th]) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LID] THEN
  SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH; LVS_IOTA_COMPONENT]);;


(* P2BKL.L2 On a level set L of a primitive h of g(X,.) (X parallel and     *)
(* unit): Ric(a,b) = R/2 g(a,b) for a, b orthogonal to X, the scalar        *)
(* curvature of the induced metric is that of g, and the Ricci form of the *)
(* induced metric is the restriction of the Ricci form of g (in matrix      *)
(* form: transp J ** Ric ** J with J the leaf Jacobian).                    *)

let P2BKL_RIC_TANGENT = prove
 (`!top atlas (g:A->real^3^3) (X:A->real^3) V h u x a b.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     p2b_parallel_on atlas g (topspace top) X /\
     (!y. y IN topspace top ==> X y dot (g y ** X y) = &1) /\
     open_in top V /\ p2bkg_prim atlas g X V h /\ lvs_regular atlas V h u /\
     x IN lvs_set V h u /\ a dot (g x ** X x) = &0 /\ b dot (g x ** X x) = &0
     ==> mfd_ricci atlas g x a b = mfd_scalar atlas g x / &2 * (a dot (g x ** b))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN V /\ x IN topspace top` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:A) IN lvs_set V (h:A->real) u` THEN REWRITE_TAC[lvs_set; IN_ELIM_THM] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `(X:A->real^3) x dot ((g:A->real^3^3) x ** X x) = &1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `V:A->bool`; `h:A->real`; `u:real`; `x:A`] LVS_GAUSS_FRAME) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `V:A->bool`; `h:A->real`; `x:A`] P2BKL_NORMAL) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:real^2` (X_CHOOSE_THEN `v2:real^2` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)`]
         P2BSS_PAR_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[mfd_ricci; mfd_scalar] THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                        (FST(chart_at atlas x))`;
                 `metric_local atlas (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A))
                               (g:A->real^3^3)`;
                 `mfd_vrep atlas (X:A->real^3) (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) x`;
                 `lvs_jac top atlas V (h:A->real) u x v1`;
                 `lvs_jac top atlas V (h:A->real) u x v2`;
                 `a:real^3`; `b:real^3`] P2BSS_RIC_HORIZ) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `X:A->real^3`; `x:A`]
         P2BX0_VREP_AT) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `x:A`]
         METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
                  REWRITE_TAC[]]);;

let P2BKL_LEVEL_SCALAR = prove
 (`!top atlas (g:A->real^3^3) (X:A->real^3) V h u x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     p2b_parallel_on atlas g (topspace top) X /\
     (!y. y IN topspace top ==> X y dot (g y ** X y) = &1) /\
     open_in top V /\ p2bkg_prim atlas g X V h /\ lvs_regular atlas V h u /\
     x IN lvs_set V h u
     ==> mfd_scalar (lvs_atlas top atlas V h u) (lvs_metric top atlas g V h u) x =
         mfd_scalar atlas g x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN V /\ x IN topspace top` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:A) IN lvs_set V (h:A->real) u` THEN REWRITE_TAC[lvs_set; IN_ELIM_THM] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `V:A->bool`; `h:A->real`; `u:real`; `x:A`] LVS_GAUSS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `V:A->bool`; `h:A->real`; `x:A`] P2BKL_NORMAL) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `V:A->bool`; `h:A->real`; `u:real`; `x:A`] P2BKL_II) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `x:A`] P2BSS_RIC_Y) THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN DISCH_THEN SUBST1_TAC THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  ASM_REWRITE_TAC[MATRIX_MUL_RZERO; DET_0] THEN REAL_ARITH_TAC);;

let P2BKL_MFD_RICCI_DOT = prove
 (`!top atlas (g:A->real^N^N) x u v.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top
     ==> u dot (mfd_ricci_matrix atlas g x ** v) = mfd_ricci atlas g x u v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[mfd_ricci_matrix; mfd_ricci] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC LRG_LRICCI_DOT_FORM THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                    (FST(chart_at atlas x))` THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]);;

let P2BKL_MAT_ENTRY_DOT = prove
 (`!(M:real^N^N) i j.
     1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
     ==> M$i$j = basis i dot (M ** basis j)`,
  SIMP_TAC[DOT_BASIS; MATRIX_VECTOR_MUL_BASIS; column; LAMBDA_BETA]);;

let P2BKL_LEVEL_RICCI = prove
 (`!top atlas (g:A->real^3^3) (X:A->real^3) V h u x v w.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     p2b_parallel_on atlas g (topspace top) X /\
     (!y. y IN topspace top ==> X y dot (g y ** X y) = &1) /\
     open_in top V /\ p2bkg_prim atlas g X V h /\ lvs_regular atlas V h u /\
     x IN lvs_set V h u
     ==> mfd_ricci (lvs_atlas top atlas V h u) (lvs_metric top atlas g V h u) x v w =
         mfd_ricci atlas g x (lvs_jac top atlas V h u x v) (lvs_jac top atlas V h u x w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN V /\ x IN topspace top` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:A) IN lvs_set V (h:A->real) u` THEN REWRITE_TAC[lvs_set; IN_ELIM_THM] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology top (lvs_set V (h:A->real) u)`;
                 `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) V (h:A->real) u`;
                 `lvs_metric top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) V (h:A->real) u`;
                 `x:A`; `v:real^2`; `w:real^2`] P2BSS_EINSTEIN2_MFD) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LVS_MANIFOLD THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC LVS_RIEMANNIAN THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[LVS_TOPSPACE]];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `V:A->bool`; `h:A->real`; `u:real`; `x:A`] P2BKL_LEVEL_SCALAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `V:A->bool`;
                 `h:A->real`; `u:real`; `x:A`] LVS_JAC_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!z. lvs_jac top atlas V (h:A->real) u x z dot ((g:A->real^3^3) x ** (X:A->real^3) x) = &0`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC P2BKL_JAC_TANGENT THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `V:A->bool`; `h:A->real`; `u:real`; `x:A`;
                 `lvs_jac top atlas V (h:A->real) u x v`; `lvs_jac top atlas V (h:A->real) u x w`]
                P2BKL_RIC_TANGENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[lvs_metric] THEN
  REWRITE_TAC[GSYM P2BSS_CONG_DOT] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MATRIX_WORKS th]));;

let P2BKL_LEVEL_RICCI_MATRIX = prove
 (`!top atlas (g:A->real^3^3) (X:A->real^3) V h u x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     p2b_parallel_on atlas g (topspace top) X /\
     (!y. y IN topspace top ==> X y dot (g y ** X y) = &1) /\
     open_in top V /\ p2bkg_prim atlas g X V h /\ lvs_regular atlas V h u /\
     x IN lvs_set V h u
     ==> mfd_ricci_matrix (lvs_atlas top atlas V h u) (lvs_metric top atlas g V h u) x =
         transp(matrix(lvs_jac top atlas V h u x)) ** mfd_ricci_matrix atlas g x **
         matrix(lvs_jac top atlas V h u x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN V /\ x IN topspace top` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:A) IN lvs_set V (h:A->real) u` THEN REWRITE_TAC[lvs_set; IN_ELIM_THM] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `V:A->bool`;
                 `h:A->real`; `u:real`; `x:A`] LVS_JAC_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[CART_EQ] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[CART_EQ] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[RFB_MFD_RICCI_MATRIX_COMPONENT] THEN
  ASM_SIMP_TAC[P2BKL_MAT_ENTRY_DOT] THEN
  REWRITE_TAC[GSYM P2BSS_CONG_DOT] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MATRIX_WORKS th]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `x:A`; `lvs_jac top atlas V (h:A->real) u x (basis i)`;
                 `lvs_jac top atlas V (h:A->real) u x (basis j)`] P2BKL_MFD_RICCI_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC P2BKL_LEVEL_RICCI THEN EXISTS_TAC `X:A->real^3` THEN ASM_REWRITE_TAC[]);;


(* P2BKL.L3 The induced metrics of a level set form a Ricci flow: entry     *)
(* formulas for transp M ** G ** M, their time derivatives, small           *)
(* smoothness helpers, and joint smoothness of the chart representatives    *)
(* of the induced metrics on the leaf (LVS_METRIC_LOCAL, locally in an      *)
(* ambient chart).                                                          *)

let P2BKL_CONG_ENTRY = prove
 (`!(M:real^2^3) (G:real^3^3) i j.
     1 <= i /\ i <= 2 /\ 1 <= j /\ j <= 2
     ==> (transp M ** G ** M)$i$j =
         sum(1..3) (\k. sum(1..3) (\l. M$k$i * G$k$l * M$l$j))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[matrix_mul; transp; DIMINDEX_2; DIMINDEX_3; SUM_3] THEN
  ASM_SIMP_TAC[LAMBDA_BETA; DIMINDEX_2; DIMINDEX_3; ARITH] THEN
  REAL_ARITH_TAC);;

let P2BKL_CONG_DERIV = prove
 (`!(G:real->real^3^3) (G':real^3^3) (M:real^2^3) t.
     (!k l. 1 <= k /\ k <= 3 /\ 1 <= l /\ l <= 3
            ==> ((\s. G s$k$l) has_real_derivative G'$k$l) (atreal t))
     ==> !i j. 1 <= i /\ i <= 2 /\ 1 <= j /\ j <= 2
               ==> ((\s. (transp M ** G s ** M)$i$j) has_real_derivative
                    (transp M ** G' ** M)$i$j) (atreal t)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[P2BKL_CONG_ENTRY] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `l:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_RMUL_ATREAL THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let P2BKL_SMOOTH_SUM3 = prove
 (`!s (f:num->real^M->real).
     open s /\ (!k. 1 <= k /\ k <= 3 ==> smooth_map_on s (\z. lift(f k z)))
     ==> smooth_map_on s (\z. lift(sum(1..3) (\k. f k z)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\k z. lift((f:num->real^M->real) k z)`; `1..3`]
                SMOOTH_MAP_ON_LIFT_SUM) THEN
  ASM_SIMP_TAC[LIFT_DROP; FINITE_NUMSEG; IN_NUMSEG; ETA_AX]);;

let P2BKL_SMOOTH_MUL = prove
 (`!s (f:real^M->real) g.
     open s /\ smooth_map_on s (\z. lift(f z)) /\ smooth_map_on s (\z. lift(g z))
     ==> smooth_map_on s (\z. lift(f z * g z))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\z. lift((f:real^M->real) z)`; `\z. lift((g:real^M->real) z)`]
                SMOOTH_MAP_ON_LIFT_MUL) THEN
  ASM_SIMP_TAC[LIFT_DROP]);;

let P2BKL_SMOOTH_SNDCART = prove
 (`!s. open s ==> smooth_map_on s (sndcart:real^(M,N)finite_sum->real^N)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^(M,N)finite_sum->bool`; `\x:real^(M,N)finite_sum. x`]
                SMOOTH_MAP_ON_SNDCART_OPEN) THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; o_DEF; ETA_AX]);;

let P2BKL_SMOOTH_FSTCART = prove
 (`!s. open s ==> smooth_map_on s (fstcart:real^(M,N)finite_sum->real^M)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^(M,N)finite_sum->bool`; `\x:real^(M,N)finite_sum. x`]
                SMOOTH_MAP_ON_FSTCART_OPEN) THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; o_DEF; ETA_AX]);;

let P2BKL_MATRIX_ENTRY = prove
 (`!(f:real^M->real^N) k i.
     1 <= k /\ k <= dimindex(:N) /\ 1 <= i /\ i <= dimindex(:M)
     ==> (matrix f)$k$i = f(basis i)$k`,
  SIMP_TAC[matrix; LAMBDA_BETA]);;

(* Entries of the Jacobian of a smooth map of the second factor. *)

let P2BKL_JAC_ENTRY_SMOOTH = prove
 (`!O T (phi:real^2->real^3) k i.
     open O /\ smooth_map_on O phi /\ open T /\
     IMAGE (sndcart:real^(1,2)finite_sum->real^2) T SUBSET O /\
     1 <= k /\ k <= 3 /\ 1 <= i /\ i <= 2
     ==> smooth_map_on T
           (\z:real^(1,2)finite_sum. lift((matrix(frechet_derivative phi (at (sndcart z))))$k$i))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[P2BKL_MATRIX_ENTRY; DIMINDEX_2; DIMINDEX_3] THEN
  SUBGOAL_THEN
   `(\z:real^(1,2)finite_sum. lift(frechet_derivative (phi:real^2->real^3) (at (sndcart z)) (basis i)$k)) =
    (\w. lift(frechet_derivative phi (at w) (basis i)$k)) o sndcart`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `O:real^2->bool` THEN
  ASM_SIMP_TAC[P2BKL_SMOOTH_SNDCART] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]);;

let P2BKL_IN_PCROSS = prove
 (`!(z:real^(M,N)finite_sum) s t. z IN s PCROSS t <=> fstcart z IN s /\ sndcart z IN t`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM PASTECART_FST_SND] THEN
  REWRITE_TAC[PASTECART_IN_PCROSS]);;

(* Entries of a jointly smooth metric family composed with (t, phi(w)). *)

let P2BKL_METRIC_ENTRY_SMOOTH = prove
 (`!(Fm:real^(1,3)finite_sum->real^3^3) S O T (phi:real^2->real^3) a b k l.
     open S /\ open O /\ smooth_map_on O phi /\ IMAGE phi O SUBSET S /\
     smooth_map_on (interval(lift a,lift b) PCROSS S)
                   (\z. (vectorize:real^3^3->real^(3,3)finite_prod) (Fm z)) /\
     open T /\ T SUBSET interval(lift a,lift b) PCROSS O /\
     1 <= k /\ k <= 3 /\ 1 <= l /\ l <= 3
     ==> smooth_map_on T
           (\z:real^(1,2)finite_sum. lift((Fm(pastecart (fstcart z) (phi(sndcart z))))$k$l))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(interval(lift a,lift b) PCROSS (S:real^3->bool))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (interval(lift a,lift b) PCROSS (S:real^3->bool))
                  (\z. lift(((Fm:real^(1,3)finite_sum->real^3^3) z)$k$l))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`interval(lift a,lift b) PCROSS (S:real^3->bool)`;
                   `Fm:real^(1,3)finite_sum->real^3^3`] LRG_SMOOTH_VECTORIZE) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(vectorize:real^3^3->real^(3,3)finite_prod) o (Fm:real^(1,3)finite_sum->real^3^3) =
                  (\z. vectorize(Fm z))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`k:num`; `l:num`]) THEN
    ASM_REWRITE_TAC[DIMINDEX_3];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z:real^(1,2)finite_sum. lift(((Fm:real^(1,3)finite_sum->real^3^3)
                                    (pastecart (fstcart z) ((phi:real^2->real^3)(sndcart z))))$k$l)) =
    (\z. lift((Fm z)$k$l)) o (\z. pastecart (fstcart z) (phi(sndcart z)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `interval(lift a,lift b) PCROSS (S:real^3->bool)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS] THEN
    X_GEN_TAC `z:real^(1,2)finite_sum` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^(1,2)finite_sum) IN interval(lift a,lift b) PCROSS (O:real^2->bool)`
    MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[P2BKL_IN_PCROSS] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_SIMP_TAC[P2BKL_SMOOTH_FSTCART] THEN
  SUBGOAL_THEN `(\z:real^(1,2)finite_sum. (phi:real^2->real^3)(sndcart z)) = phi o sndcart`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `O:real^2->bool` THEN
  ASM_SIMP_TAC[P2BKL_SMOOTH_SNDCART] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^(1,2)finite_sum` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:real^(1,2)finite_sum) IN interval(lift a,lift b) PCROSS (O:real^2->bool)`
  MP_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[P2BKL_IN_PCROSS] THEN SIMP_TAC[]]);;


(* P2BKL.L4 Joint smoothness of the induced metrics in leaf charts, and the *)
(* leaf Ricci flow: if h is a primitive of g(t)(X,.) on V for every t, X     *)
(* parallel and unit for every g(t), and g a Ricci flow on (a,b), then the  *)
(* induced metrics on a level set of h form a Ricci flow on (a,b), with the *)
(* scalar curvature of g.                                                   *)

let P2BKL_LEAF_JOINT = prove
 (`!top atlas (g:real->A->real^3^3) V (h:A->real) u a b c.
     smooth_manifold_atlas top atlas /\ open_in top V /\ lvs_regular atlas V h u /\
     (!c'. c' IN atlas
           ==> smooth_map_on (interval(lift a,lift b) PCROSS IMAGE (SND c') (FST c'))
                 (\z. (vectorize:real^3^3->real^(3,3)finite_prod)
                      (metric_local atlas c' (g(drop(fstcart z))) (sndcart z)))) /\
     c IN lvs_atlas top atlas V h u
     ==> smooth_map_on (interval(lift a,lift b) PCROSS IMAGE (SND c) (FST c))
           (\z. (vectorize:real^2^2->real^(2,2)finite_prod)
                (metric_local (lvs_atlas top atlas V h u) c
                   (lvs_metric top atlas (g(drop(fstcart z))) V h u) (sndcart z)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (subtopology top (lvs_set V (h:A->real) u))
                                      (lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) V h u)`
  ASSUME_TAC THENL [MATCH_MP_TAC LVS_MANIFOLD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology top (lvs_set V (h:A->real) u)`;
                 `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) V (h:A->real) u`;
                 `c:(A->bool)#(A->real^2)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `FST(c:(A->bool)#(A->real^2)) SUBSET topspace top` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o check (fun th ->
      can (find_term ((=) `FST(c:(A->bool)#(A->real^2))`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "open_in")) (concl th))) THEN
    ASM_SIMP_TAC[LVS_TOPSPACE] THEN
    SUBGOAL_THEN `lvs_set V (h:A->real) u SUBSET topspace top` MP_TAC THENL
     [REWRITE_TAC[lvs_set; SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
      SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL]; ALL_TAC] THEN
  REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
  MAP_EVERY X_GEN_TAC [`t0:real^1`; `w0:real^2`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^2)) w0 IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  ABBREV_TAC `c' = chart_at (atlas:((A->bool)#(A->real^3))->bool)
                            (chart_inv (c:(A->bool)#(A->real^2)) w0)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `chart_inv (c:(A->bool)#(A->real^2)) w0`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `V:A->bool`;
                 `h:A->real`; `u:real`; `c:(A->bool)#(A->real^2)`; `c':(A->bool)#(A->real^3)`]
                LVS_CHART_AMBIENT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c':(A->bool)#(A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `O = {w | w IN IMAGE (SND (c:(A->bool)#(A->real^2))) (FST c) /\
                       chart_inv c w IN FST (c':(A->bool)#(A->real^3))}` THEN
  EXISTS_TAC `interval(lift a,lift b) PCROSS (O:real^2->bool)` THEN
  SUBGOAL_THEN `open(interval(lift a,lift b) PCROSS (O:real^2->bool))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL]; ALL_TAC] THEN
  ASM_REWRITE_TAC[PASTECART_IN_PCROSS] THEN CONJ_TAC THENL
   [EXPAND_TAC "O" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC
   `\z. (vectorize:real^2^2->real^(2,2)finite_prod)
        (transp(matrix(frechet_derivative
                  (\w. SND (c':(A->bool)#(A->real^3)) (chart_inv (c:(A->bool)#(A->real^2)) w))
                  (at (sndcart z)))) **
         metric_local atlas c' ((g:real->A->real^3^3)(drop(fstcart z)))
                      (SND c' (chart_inv c (sndcart z))) **
         matrix(frechet_derivative (\w. SND c' (chart_inv c w)) (at (sndcart z))))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[P2BKL_IN_PCROSS] THEN X_GEN_TAC `z:real^(1,2)finite_sum` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC LVS_METRIC_LOCAL THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `sndcart(z:real^(1,2)finite_sum) IN O` THEN EXPAND_TAC "O" THEN
    SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`interval(lift a,lift b) PCROSS (O:real^2->bool)`;
                 `\z. transp(matrix(frechet_derivative
                        (\w. SND (c':(A->bool)#(A->real^3)) (chart_inv (c:(A->bool)#(A->real^2)) w))
                        (at (sndcart z)))) **
                      metric_local atlas c' ((g:real->A->real^3^3)(drop(fstcart z)))
                                   (SND c' (chart_inv c (sndcart z))) **
                      matrix(frechet_derivative (\w. SND c' (chart_inv c w)) (at (sndcart z)))`]
                LRG_SMOOTH_VECTORIZE) THEN
  ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIMINDEX_2] THEN MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[P2BKL_CONG_ENTRY] THEN
  MATCH_MP_TAC P2BKL_SMOOTH_SUM3 THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC P2BKL_SMOOTH_SUM3 THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `l:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (sndcart:real^(1,2)finite_sum->real^2)
                      (interval(lift a,lift b) PCROSS (O:real^2->bool)) SUBSET O`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; P2BKL_IN_PCROSS] THEN SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC P2BKL_SMOOTH_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2BKL_JAC_ENTRY_SMOOTH THEN EXISTS_TAC `O:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC P2BKL_SMOOTH_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC P2BKL_JAC_ENTRY_SMOOTH THEN EXISTS_TAC `O:real^2->bool` THEN
    ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL
   [`\z:real^(1,3)finite_sum. metric_local atlas (c':(A->bool)#(A->real^3))
                                ((g:real->A->real^3^3)(drop(fstcart z))) (sndcart z)`;
    `IMAGE (SND (c':(A->bool)#(A->real^3))) (FST c')`; `O:real^2->bool`;
    `interval(lift a,lift b) PCROSS (O:real^2->bool)`;
    `\w. SND (c':(A->bool)#(A->real^3)) (chart_inv (c:(A->bool)#(A->real^2)) w)`;
    `a:real`; `b:real`; `k:num`; `l:num`] P2BKL_METRIC_ENTRY_SMOOTH) THEN
  ASM_SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART; SUBSET_REFL] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  EXPAND_TAC "O" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `w:real^2` THEN STRIP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]);;


(* P2BKL.L5 Main theorem A: the leaf Ricci flow.                           *)

let P2BKL_LEAF_RICCI_FLOW = prove
 (`!top atlas (g:real->A->real^3^3) (X:A->real^3) V h u a b.
     ricci_flow_on (top,atlas) a b g /\ open_in top V /\
     (!t. a < t /\ t < b
          ==> p2b_parallel_on atlas (g t) (topspace top) X /\
              (!x. x IN topspace top ==> X x dot (g t x ** X x) = &1) /\
              p2bkg_prim atlas (g t) X V h)
     ==> ricci_flow_on (subtopology top (lvs_set V h u),lvs_atlas top atlas V h u) a b
                       (\t. lvs_metric top atlas (g t) V h u) /\
         !t x. a < t /\ t < b /\ x IN lvs_set V h u
               ==> mfd_scalar (lvs_atlas top atlas V h u) (lvs_metric top atlas (g t) V h u) x =
                   mfd_scalar atlas (g t) x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tt"))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  SUBGOAL_THEN `(V:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `lvs_set V (h:A->real) u SUBSET topspace top` ASSUME_TAC THENL
   [REWRITE_TAC[lvs_set] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `lvs_regular atlas V (h:A->real) u` ASSUME_TAC THENL
   [SUBGOAL_THEN `a < (a + b) / &2 /\ (a + b) / &2 < b` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "tt" (STRIP_ASSUME_TAC o C MATCH_MP
      (CONJ (ASSUME `a < (a + b) / &2`) (ASSUME `(a + b) / &2 < b`))) THEN
    MATCH_MP_TAC P2BKG_LEVEL_REGULAR THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `(g:real->A->real^3^3)((a + b) / &2)`;
                          `X:A->real^3`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p2bkg_prim atlas ((g:real->A->real^3^3)((a + b) / &2)) (X:A->real^3) V (h:A->real)` THEN
    REWRITE_TAC[p2bkg_prim] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t x. a < t /\ t < b /\ x IN lvs_set V h u
          ==> mfd_scalar (lvs_atlas top atlas V h u) (lvs_metric top atlas (g t) V h u) x =
              mfd_scalar atlas ((g:real->A->real^3^3) t) x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "tt" (STRIP_ASSUME_TAC o C MATCH_MP (CONJ (ASSUME `a < t`) (ASSUME `t < b`))) THEN
    MATCH_MP_TAC P2BKL_LEVEL_SCALAR THEN EXISTS_TAC `X:A->real^3` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[ricci_flow_on] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC LVS_MANIFOLD THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC LVS_RIEMANNIAN THEN ASM_SIMP_TAC[];
    X_GEN_TAC `c:(A->bool)#(A->real^2)` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC P2BKL_LEAF_JOINT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `i:num`; `j:num`] THEN
  ASM_SIMP_TAC[LVS_TOPSPACE; DIMINDEX_2] THEN STRIP_TAC THEN
  USE_THEN "tt" (STRIP_ASSUME_TAC o C MATCH_MP (CONJ (ASSUME `a < t`) (ASSUME `t < b`))) THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(g:real->A->real^3^3) t`; `X:A->real^3`; `V:A->bool`; `h:A->real`; `u:real`;
                 `x:A`] P2BKL_LEVEL_RICCI_MATRIX) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[lvs_metric] THEN
  MP_TAC(ISPECL [`\s. (g:real->A->real^3^3) s x`;
                 `--(&2) %% mfd_ricci_matrix (atlas:((A->bool)#(A->real^3))->bool)
                                 ((g:real->A->real^3^3) t) x`;
                 `matrix(lvs_jac top (atlas:((A->bool)#(A->real^3))->bool) V (h:A->real) u x)`;
                 `t:real`] P2BKL_CONG_DERIV) THEN
  REWRITE_TAC[MATRIX_CMUL_COMPONENT] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "has_real_derivative")) (concl th))) THEN
    ASM_REWRITE_TAC[DIMINDEX_3];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`i:num`; `j:num`]) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MATRIX_MUL_LMUL; MATRIX_MUL_RMUL; MATRIX_CMUL_COMPONENT]);;


(* P2BKL.G6 The leaf flow on (a,b) for every a < b: a primitive h of        *)
(* g(s)(X,.) on V for every s < b with X parallel and unit for every g(s)   *)
(* gives a Ricci flow of the induced metrics on every (a,b), with R_L = R.  *)

let P2BKL_RF_RIEMANNIAN = prove
 (`!top atlas (g:real->A->real^N^N) b t.
     (!a. a < b ==> ricci_flow_on (top,atlas) a b g) /\ t < b
     ==> riemannian_metric atlas (g t)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t - &1`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REAL_ARITH_TAC);;

let P2BKL_LEAF_FLOW_ALL = prove
 (`!top atlas (g:real->A->real^3^3) b (X:A->real^3) V h u.
     (!a. a < b ==> ricci_flow_on (top,atlas) a b g) /\ open_in top V /\
     (!s. s < b ==> p2b_parallel_on atlas (g s) (topspace top) X /\
                    (!y. y IN topspace top ==> X y dot (g s y ** X y) = &1) /\
                    p2bkg_prim atlas (g s) X V h)
     ==> (!a. a < b ==> ricci_flow_on (subtopology top (lvs_set V h u),lvs_atlas top atlas V h u)
                                      a b (\t. lvs_metric top atlas (g t) V h u)) /\
         (!t y. t < b /\ y IN lvs_set V h u
                ==> mfd_scalar (lvs_atlas top atlas V h u) (lvs_metric top atlas (g t) V h u) y =
                    mfd_scalar atlas (g t) y)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "s"))) THEN
  SUBGOAL_THEN
   `!a. a < b
        ==> ricci_flow_on (subtopology top (lvs_set V h u),lvs_atlas top atlas V h u) a b
                          (\t. lvs_metric top atlas (g t) V h u) /\
            (!t y. a < t /\ t < b /\ y IN lvs_set V h u
                   ==> mfd_scalar (lvs_atlas top atlas V h u)
                                  (lvs_metric top atlas ((g:real->A->real^3^3) t) V h u) y =
                       mfd_scalar atlas (g t) y)`
  (LABEL_TAC "ab") THENL
   [X_GEN_TAC `a:real` THEN DISCH_TAC THEN MATCH_MP_TAC P2BKL_LEAF_RICCI_FLOW THEN
    EXISTS_TAC `X:A->real^3` THEN ASM_SIMP_TAC[] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN USE_THEN "s" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `a:real` THEN DISCH_TAC THEN
    USE_THEN "ab" (MP_TAC o C MATCH_MP (ASSUME `a < b:real`)) THEN SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:A`] THEN STRIP_TAC THEN
  USE_THEN "ab" (MP_TAC o SPEC `t - &1`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

