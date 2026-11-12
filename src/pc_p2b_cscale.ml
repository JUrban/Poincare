(* ========================================================================= *)
(* Unit pc_p2b_cscale: scale invariance of canonical neighbourhoods.  For    *)
(* c > 0 and a riemannian metric g, the eps-necks, (C,eps)-caps (with the    *)
(* same core), C-components (Hausdorff manifolds) and eps-round components   *)
(* of c g and of g coincide, hence so do the canonical neighbourhoods        *)
(* (P2BCS_NECK_CMUL, P2BCS_CAP_CMUL, P2BCS_CCOMP_CMUL, P2BCS_ROUND_CMUL,     *)
(* P2BCS_CANON_CMUL).  Used in Part 2B (limit transfer, unit pc_p2b_ltr),    *)
(* Part 3 and Part 2C.                                                       *)
(*                                                                           *)
(* Contents, in order:                                                       *)
(* - the manifold-level scaling of R, the squared gradient of R, the         *)
(*   Laplacian of R and the squared norm of Ric (from P2C_SCALE_QUANTITIES), *)
(*   and of the intrinsic distance; sups of scaled images; necks;            *)
(* - clause (7) of caps, and caps;                                           *)
(* - C-components (bounded distances on compact components), round           *)
(*   components, canonical neighbourhoods.                                   *)
(* ========================================================================= *)

needs "src/pc_p2b_lim.ml";;
needs "src/pc_p2c_cderiv.ml";;
needs "src/pc_grg_vol.ml";;

prioritize_real();;

type_invention_error := true;;

let P2BCS_LRIC2_ETA = prove
 (`!G:real^N->real^N^N. lric2 G = (\z u. lricci G z (u 1) (u 2))`,
  REWRITE_TAC[FUN_EQ_THM; lric2]);;

let P2BCS_LOCAL_FIELD = prove
 (`!top atlas (g:A->real^N^N) x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top
     ==> metric_field (IMAGE (SND(chart_at atlas x)) (FST(chart_at atlas x)))
                      (metric_local atlas (chart_at atlas x) g) /\
         SND(chart_at atlas x) x IN IMAGE (SND(chart_at atlas x)) (FST(chart_at atlas x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) x)`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) x)`;
                   `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) x)`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) x)`;
                   `g:A->real^N^N`] RIEMANNIAN_METRIC_OVERLAP) THEN
    ASM_REWRITE_TAC[PAIR; INTER_IDEMPOT];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]);;

let P2BCS_CMUL_QUANTITIES = prove
 (`!top atlas (g:A->real^N^N) c x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ &0 < c /\
     x IN topspace top
     ==> mfd_scalar atlas g x = c * mfd_scalar atlas (\y. c %% g y) x /\
         rfs_scalar_grad2 atlas g x = c pow 3 * rfs_scalar_grad2 atlas (\y. c %% g y) x /\
         rfs_scalar_lap atlas g x = c pow 2 * rfs_scalar_lap atlas (\y. c %% g y) x /\
         rfs_ric_norm2 atlas g x = c pow 2 * rfs_ric_norm2 atlas (\y. c %% g y) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`] P2BCS_LOCAL_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[mfd_scalar; rfs_scalar_grad2; rfs_scalar_lap; rfs_ric_norm2;
              METRIC_LOCAL_CMUL; ETA_AX] THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) x))
                        (FST(chart_at atlas x))`;
                 `metric_local atlas (chart_at (atlas:((A->bool)#(A->real^N))->bool) x)
                               (g:A->real^N^N)`;
                 `c:real`; `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) x) x`]
                P2C_SCALE_QUANTITIES) THEN
  ASM_REWRITE_TAC[P2BCS_LRIC2_ETA]);;

let P2BCS_SCALAR_CMUL = prove
 (`!top atlas (g:A->real^N^N) c x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ &0 < c /\
     x IN topspace top
     ==> mfd_scalar atlas (\y. c %% g y) x = mfd_scalar atlas g x / c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `c:real`; `x:A`] P2BCS_CMUL_QUANTITIES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD);;

let P2BCS_NECK_CMUL = prove
 (`!top atlas (g:A->real^3^3) eps x e c.
     &0 < c /\ riemannian_metric atlas g
     ==> (rfs_neck (top,atlas) (\y. c %% g y) eps x e <=> rfs_neck (top,atlas) g eps x e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[rfs_neck] THEN
  ASM_CASES_TAC `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool)` THEN
  ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `&0 < eps` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `mfd_param top (atlas:((A->bool)#(A->real^3))->bool) (rfs_neck_dom eps) e` THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(x:A) IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `rfs_neck_dom eps`; `e:real^3->A`] GRGD_PARAM_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (e:real^3->A) (rfs_neck_dom eps) SUBSET topspace top` THEN
    UNDISCH_TAC `(x:A) IN IMAGE (e:real^3->A) (sphere(vec 0,&1))` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `c:real`; `x:A`] P2BCS_SCALAR_CMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `(\y. (mfd_scalar atlas (g:A->real^3^3) x / c) %%
         rfs_pullback atlas (e:real^3->A) (\y. c %% g y) y) =
    (\y. mfd_scalar atlas g x %% rfs_pullback atlas e g y)`
  SUBST1_TAC THENL
   [REWRITE_TAC[rfs_pullback; METRIC_LOCAL_CMUL; mpullback; FUN_EQ_THM] THEN
    REWRITE_TAC[MATRIX_MUL_LMUL; MATRIX_MUL_RMUL; MATRIX_CMUL_ASSOC] THEN
    GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_MUL_LZERO]);;

let P2BCS_DIST_IN_CMUL = prove
 (`!top atlas (g:A->real^N^N) k S x y.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     &0 < k /\ mfd_joinable_in (top,atlas) S x y
     ==> mfd_dist_in (top,atlas) (\z. k %% g z) S x y =
         sqrt k * mfd_dist_in (top,atlas) g S x y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_dist_in] THEN MATCH_MP_TAC GRGD_INF_SCALE THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; GRGD_IN_LENGTHS_IN] THEN
    ASM_MESON_TAC[mfd_joinable_in];
    ASM_MESON_TAC[GRGD_LENGTHS_IN_POS_LE];
    X_GEN_TAC `L:real` THEN REWRITE_TAC[GRGD_IN_LENGTHS_IN] THEN
    SUBGOAL_THEN
     `!gamma:real->A. mfd_c1_curve (top,atlas) gamma (&0) (&1)
          ==> mfd_length atlas (\x. k %% (g:A->real^N^N) x) gamma (&0) (&1) =
              sqrt k * mfd_length atlas g gamma (&0) (&1)`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFD_LENGTH_SCALE THEN
      EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    EQ_TAC THEN STRIP_TAC THENL
     [EXISTS_TAC `mfd_length atlas (g:A->real^N^N) (gamma:real->A) (&0) (&1)` THEN
      ASM_MESON_TAC[];
      ASM_MESON_TAC[]]]);;

let P2BCS_SUP_IMAGE_CMUL = prove
 (`!(f:A->real) s c.
     &0 < c /\ ~(s = {}) /\ (?B. !x. x IN s ==> f x <= B)
     ==> sup(IMAGE (\x. c * f x) s) = c * sup(IMAGE f s)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `B:real`))) THEN
  MP_TAC(ISPEC `IMAGE (f:A->real) s` SUP) THEN
  REWRITE_TAC[IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "A0") (LABEL_TAC "B0")) THEN
  MP_TAC(ISPEC `IMAGE (\x. c * (f:A->real) x) s` SUP) THEN
  REWRITE_TAC[IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [EXISTS_TAC `c * B:real` THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "A1") (LABEL_TAC "B1")) THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
   [REMOVE_THEN "B1" MATCH_MP_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN
  REMOVE_THEN "B0" MATCH_MP_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REMOVE_THEN "A1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let P2BCS_CMUL_RATIOS = prove
 (`!top atlas (g:A->real^N^N) c x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ &0 < c /\
     x IN topspace top
     ==> mfd_scalar atlas (\y. c %% g y) x = mfd_scalar atlas g x / c /\
         sqrt(rfs_scalar_grad2 atlas (\y. c %% g y) x) /
         (mfd_scalar atlas (\y. c %% g y) x * sqrt(mfd_scalar atlas (\y. c %% g y) x)) =
         sqrt(rfs_scalar_grad2 atlas g x) /
         (mfd_scalar atlas g x * sqrt(mfd_scalar atlas g x)) /\
         abs(rfs_scalar_lap atlas (\y. c %% g y) x +
             &2 * rfs_ric_norm2 atlas (\y. c %% g y) x) /
         mfd_scalar atlas (\y. c %% g y) x pow 2 =
         abs(rfs_scalar_lap atlas g x + &2 * rfs_ric_norm2 atlas g x) /
         mfd_scalar atlas g x pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `c:real`; `x:A`] P2BCS_CMUL_QUANTITIES) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Rc = mfd_scalar atlas (\y. c %% (g:A->real^N^N) y) x` THEN
  ABBREV_TAC `Gc = rfs_scalar_grad2 atlas (\y. c %% (g:A->real^N^N) y) x` THEN
  ABBREV_TAC `Lc = rfs_scalar_lap atlas (\y. c %% (g:A->real^N^N) y) x` THEN
  ABBREV_TAC `Qc = rfs_ric_norm2 atlas (\y. c %% (g:A->real^N^N) y) x` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < sqrt c /\ sqrt(c pow 3) = c * sqrt c` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT] THEN
    REWRITE_TAC[REAL_ARITH `c pow 3 = c pow 2 * c`; SQRT_MUL] THEN
    ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REWRITE_TAC[SQRT_MUL] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD;
    UNDISCH_TAC `&0 < c` THEN UNDISCH_TAC `&0 < sqrt c` THEN CONV_TAC REAL_FIELD;
    REWRITE_TAC[REAL_ARITH `c pow 2 * l + &2 * c pow 2 * q = c pow 2 * (l + &2 * q)`;
                REAL_ABS_MUL; REAL_ABS_POW] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < c ==> abs c = c`] THEN
    UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD]);;

(* ------------------------------------------------------------------------- *)
(* Clause (7) under scaling (balls of c g are balls of g with radius divided *)
(* by sqrt c), and caps: every clause of rfs_cap is invariant.               *)
(* ------------------------------------------------------------------------- *)

let P2BCS_C7_CMUL = prove
 (`!top atlas (g:A->real^3^3) c U Y d.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ &0 < c /\
     Y SUBSET topspace top /\
     (!y r. y IN Y /\ &0 < r /\
            (?B. !z. z IN mfd_ball (top,atlas) g y r ==> mfd_scalar atlas g z <= B) /\
            sup(IMAGE (mfd_scalar atlas g) (mfd_ball (top,atlas) g y r)) = inv(r pow 2)
            ==> compact_in top (top closure_of mfd_ball (top,atlas) g y r) /\
                top closure_of mfd_ball (top,atlas) g y r SUBSET U /\
                ?v. mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g y r) v /\
                    d <= v / r pow 3)
     ==> (!y r. y IN Y /\ &0 < r /\
            (?B. !z. z IN mfd_ball (top,atlas) (\w. c %% g w) y r
                     ==> mfd_scalar atlas (\w. c %% g w) z <= B) /\
            sup(IMAGE (mfd_scalar atlas (\w. c %% g w))
                      (mfd_ball (top,atlas) (\w. c %% g w) y r)) = inv(r pow 2)
            ==> compact_in top (top closure_of mfd_ball (top,atlas) (\w. c %% g w) y r) /\
                top closure_of mfd_ball (top,atlas) (\w. c %% g w) y r SUBSET U /\
                ?v. mfd_has_volume (top,atlas) (\w. c %% g w)
                      (mfd_ball (top,atlas) (\w. c %% g w) y r) v /\
                    d <= v / r pow 3)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "H"))))) THEN
  MAP_EVERY X_GEN_TAC [`y:A`; `r:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `B:real` (LABEL_TAC "B")) (LABEL_TAC "sup")))) THEN
  SUBGOAL_THEN `&0 < sqrt c /\ sqrt c pow 2 = c` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `c:real`; `y:A`; `r:real`] MFD_BALL_SCALE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th] THEN
    REMOVE_THEN "B" (MP_TAC o REWRITE_RULE[th]) THEN
    REMOVE_THEN "sup" (MP_TAC o REWRITE_RULE[th])) THEN
  SUBGOAL_THEN `&0 < r / sqrt c` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
  ABBREV_TAC `r0 = r / sqrt c` THEN
  ABBREV_TAC `S = mfd_ball (top,atlas) (g:A->real^3^3) y r0` THEN
  DISCH_THEN(LABEL_TAC "sup") THEN DISCH_THEN(LABEL_TAC "B") THEN
  SUBGOAL_THEN `(S:A->bool) SUBSET topspace top /\ (y:A) IN S` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
      ASM_SIMP_TAC[MFD_CENTRE_IN_BALL] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN S ==> mfd_scalar atlas (\w. c %% (g:A->real^3^3) w) z =
                             inv c * mfd_scalar atlas g z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `c:real`; `z:A`] P2BCS_SCALAR_CMUL) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN S ==> mfd_scalar atlas (g:A->real^3^3) z <= c * B`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REMOVE_THEN "B" (MP_TAC o SPEC `z:A`) THEN ASM_SIMP_TAC[] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `mfd_scalar atlas (g:A->real^3^3) z =
                  c * (inv c * mfd_scalar atlas g z)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sup(IMAGE (mfd_scalar atlas (g:A->real^3^3)) S) = inv(r0 pow 2)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `IMAGE (mfd_scalar atlas (\w. c %% (g:A->real^3^3) w)) S =
      IMAGE (\z. inv c * mfd_scalar atlas g z) S`
    (fun th -> REMOVE_THEN "sup" (MP_TAC o REWRITE_RULE[th])) THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`mfd_scalar atlas (g:A->real^3^3)`; `S:A->bool`; `inv c`]
                  P2BCS_SUP_IMAGE_CMUL) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN CONJ_TAC THENL
       [ASM SET_TAC[]; EXISTS_TAC `c * B:real` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `r = sqrt c * r0` SUBST_ALL_TAC THENL
     [EXPAND_TAC "r0" THEN UNDISCH_TAC `&0 < sqrt c` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    UNDISCH_TAC `inv c * sup(IMAGE (mfd_scalar atlas (g:A->real^3^3)) S) =
                 inv((sqrt c * r0) pow 2)` THEN
    UNDISCH_TAC `sqrt c pow 2 = c` THEN UNDISCH_TAC `&0 < c` THEN
    UNDISCH_TAC `&0 < r0` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REMOVE_THEN "H" (MP_TAC o SPECL [`y:A`; `r0:real`]) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [EXISTS_TAC `c * B:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `sqrt(c pow dimindex(:3)) * v` THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `S:A->bool`; `v:real`; `c:real`] MFD_HAS_VOLUME_SCALE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_3] THEN
  SUBGOAL_THEN `sqrt(c pow 3) = c * sqrt c` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ARITH `c pow 3 = c pow 2 * c`; SQRT_MUL] THEN
    ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `r = sqrt c * r0` SUBST1_TAC THENL
   [EXPAND_TAC "r0" THEN UNDISCH_TAC `&0 < sqrt c` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `((c * sqrt c) * v) / (sqrt c * r0) pow 3 = v / r0 pow 3` SUBST1_TAC THENL
   [UNDISCH_TAC `sqrt c pow 2 = c` THEN UNDISCH_TAC `&0 < c` THEN
    UNDISCH_TAC `&0 < r0` THEN UNDISCH_TAC `&0 < sqrt c` THEN CONV_TAC REAL_FIELD;
    ASM_REWRITE_TAC[]]);;

let P2BCS_CAP_CORE_NONEMPTY = prove
 (`!top atlas (g:A->real^3^3) C eps U Y.
     rfs_cap (top,atlas) g C eps U Y ==> ?y0. y0 IN Y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_cap] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
  DISCH_THEN(DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THENL
   [EXISTS_TAC `(b:real^3->A) (vec 0)` THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[CENTRE_IN_BALL] THEN REAL_ARITH_TAC;
    EXISTS_TAC `(p:real^3->A) (basis 1)` THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC]);;

let P2BCS_CAP_CMUL_IMP = prove
 (`!top atlas (g:A->real^3^3) C eps U Y c.
     &0 < c /\ riemannian_metric atlas g /\ rfs_cap (top,atlas) g C eps U Y
     ==> rfs_cap (top,atlas) (\w. c %% g w) C eps U Y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `y0:A` o MATCH_MP P2BCS_CAP_CORE_NONEMPTY) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2B_CAP_CORE_SUBSET) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP APX_CAP_JOINABLE) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `eps:real`; `U:A->bool`; `Y:A->bool`; `y0:A`] P2B_CAP_SUP_POS) THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `B:real`) ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2B_CAP_RATIO) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `dr:real` STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `rfs_cap (top,atlas) (g:A->real^3^3) C eps U Y` THEN
  REWRITE_TAC[rfs_cap] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. w IN U
        ==> mfd_scalar atlas (\w. c %% (g:A->real^3^3) w) w = mfd_scalar atlas g w / c /\
            sqrt(rfs_scalar_grad2 atlas (\w. c %% g w) w) /
            (mfd_scalar atlas (\w. c %% g w) w * sqrt(mfd_scalar atlas (\w. c %% g w) w)) =
            sqrt(rfs_scalar_grad2 atlas g w) /
            (mfd_scalar atlas g w * sqrt(mfd_scalar atlas g w)) /\
            abs(rfs_scalar_lap atlas (\w. c %% g w) w +
                &2 * rfs_ric_norm2 atlas (\w. c %% g w) w) /
            mfd_scalar atlas (\w. c %% g w) w pow 2 =
            abs(rfs_scalar_lap atlas g w + &2 * rfs_ric_norm2 atlas g w) /
            mfd_scalar atlas g w pow 2`
  (LABEL_TAC "pt") THENL
   [X_GEN_TAC `w:A` THEN DISCH_TAC THEN MATCH_MP_TAC P2BCS_CMUL_RATIOS THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sup(IMAGE (mfd_scalar atlas (\w. c %% (g:A->real^3^3) w)) U) =
    inv c * sup(IMAGE (mfd_scalar atlas g) U)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `IMAGE (mfd_scalar atlas (\w. c %% (g:A->real^3^3) w)) U =
      IMAGE (\w. inv c * mfd_scalar atlas g w) U`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN X_GEN_TAC `q:real` THEN
      AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `w:A` THEN
      ASM_CASES_TAC `(w:A) IN U` THEN ASM_SIMP_TAC[real_div; REAL_MUL_SYM];
      ALL_TAC] THEN
    MATCH_MP_TAC P2BCS_SUP_IMAGE_CMUL THEN ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt c /\ sqrt(c pow 3) = c * sqrt c /\
                inv(sqrt(inv c * sup(IMAGE (mfd_scalar atlas (g:A->real^3^3)) U))) =
                sqrt c * inv(sqrt(sup(IMAGE (mfd_scalar atlas g) U)))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_ARITH `c pow 3 = c pow 2 * c`; SQRT_MUL] THEN
      ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE];
      REWRITE_TAC[SQRT_MUL; SQRT_INV; REAL_INV_MUL; REAL_INV_INV] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [(* chart data *)
    ASM_SIMP_TAC[P2BCS_NECK_CMUL];
    (* positive scalar *)
    X_GEN_TAC `w:A` THEN DISCH_TAC THEN
    USE_THEN "pt" (fun th -> MP_TAC(MP (SPEC `w:A` th) (ASSUME `(w:A) IN U`))) THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[];
    (* intrinsic diameter *)
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_dist_in")) (concl th))) THEN
    REWRITE_TAC[rfs_sup_lt; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `dd:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `sqrt c * dd` THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[REAL_ARITH `C * sqrt c * x = sqrt c * (C * x)`] THEN
      MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `q:real` THEN DISCH_THEN(X_CHOOSE_THEN `y1:A` (X_CHOOSE_THEN `y2:A`
        STRIP_ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `c:real`; `U:A->bool`; `y1:A`; `y2:A`]
                    P2BCS_DIST_IN_CMUL) THEN
      ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`y1:A`; `y2:A`] THEN
      ASM_REWRITE_TAC[]];
    (* ratio *)
    REWRITE_TAC[rfs_sup_lt; IN_ELIM_THM] THEN
    EXISTS_TAC `dr:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `q:real` THEN DISCH_THEN(X_CHOOSE_THEN `y2:A` (X_CHOOSE_THEN `y1:A`
      STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "pt" (fun th -> MP_TAC(MP (SPEC `y1:A` th) (ASSUME `(y1:A) IN U`))) THEN
    USE_THEN "pt" (fun th -> MP_TAC(MP (SPEC `y2:A` th) (ASSUME `(y2:A) IN U`))) THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    SUBGOAL_THEN
     `(mfd_scalar atlas (g:A->real^3^3) y2 / c) / (mfd_scalar atlas g y1 / c) =
      mfd_scalar atlas g y2 / mfd_scalar atlas g y1`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD; ASM_SIMP_TAC[]];
    (* volume *)
    FIRST_X_ASSUM(X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_has_volume")) (concl th) &&
      is_exists(concl th) &&
      not (can (find_term (fun t -> try fst(dest_var t) = "r" with Failure _ -> false))
               (concl th)))) THEN
    EXISTS_TAC `sqrt(c pow dimindex(:3)) * v` THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `U:A->bool`; `v:real`; `c:real`]
                    MFD_HAS_VOLUME_SCALE) THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[DIMINDEX_3] THEN
      SUBGOAL_THEN
       `C * inv(sqrt(inv c * sup(IMAGE (mfd_scalar atlas (g:A->real^3^3)) U)) pow 3) =
        (c * sqrt c) * (C * inv(sqrt(sup(IMAGE (mfd_scalar atlas g) U)) pow 3))`
      SUBST1_TAC THENL
       [REWRITE_TAC[SQRT_MUL; SQRT_INV] THEN
        SUBGOAL_THEN `sqrt c pow 2 = c /\
                      &0 < sqrt(sup(IMAGE (mfd_scalar atlas (g:A->real^3^3)) U))`
        MP_TAC THENL
         [ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; SQRT_POS_LT]; ALL_TAC] THEN
        UNDISCH_TAC `&0 < sqrt c` THEN CONV_TAC REAL_FIELD;
        MATCH_MP_TAC REAL_LT_LMUL THEN ASM_SIMP_TAC[REAL_LT_MUL]]];
    (* clause 7 *)
    FIRST_X_ASSUM(X_CHOOSE_THEN `d7:real` STRIP_ASSUME_TAC o check (fun th ->
      is_exists(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_ball")) (concl th))) THEN
    EXISTS_TAC `d7:real` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2BCS_C7_CMUL THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    (* gradient *)
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      (try fst(dest_const(fst(strip_comb(concl th)))) = "rfs_sup_lt" with Failure _ -> false) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_scalar_grad2")) (concl th)))
    THEN REWRITE_TAC[rfs_sup_lt; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `dg:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `dg:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `q:real` THEN DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "pt" (fun th ->
      ACCEPT_TAC(CONJUNCT1(CONJUNCT2(MP (SPEC `y:A` th) (ASSUME `(y:A) IN U`)))));
    (* Laplacian *)
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      (try fst(dest_const(fst(strip_comb(concl th)))) = "rfs_sup_lt" with Failure _ -> false) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_scalar_lap")) (concl th)))
    THEN REWRITE_TAC[rfs_sup_lt; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `dl:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `dl:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `q:real` THEN DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "pt" (fun th ->
      ACCEPT_TAC(CONJUNCT2(CONJUNCT2(MP (SPEC `y:A` th) (ASSUME `(y:A) IN U`)))))]);;

let P2BCS_CAP_CMUL = prove
 (`!top atlas (g:A->real^3^3) C eps U Y c.
     &0 < c /\ riemannian_metric atlas g
     ==> (rfs_cap (top,atlas) (\w. c %% g w) C eps U Y <=> rfs_cap (top,atlas) g C eps U Y)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `\w. c %% (g:A->real^3^3) w`; `C:real`; `eps:real`; `U:A->bool`;
                   `Y:A->bool`; `inv c`] P2BCS_CAP_CMUL_IMP) THEN
    ASM_SIMP_TAC[REAL_LT_INV_EQ; RIEMANNIAN_METRIC_CMUL; MATRIX_CMUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; MATRIX_CMUL_LID; ETA_AX];
    DISCH_TAC THEN MATCH_MP_TAC P2BCS_CAP_CMUL_IMP THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* C-components (joinable points and bounded distances on a compact          *)
(* component, from MFD_MTOPOLOGY), round components, and the canonical       *)
(* neighbourhoods.                                                           *)
(* ------------------------------------------------------------------------- *)

let P2BCS_SECT_CMUL = prove
 (`!top atlas (g:A->real^N^N) c x u v.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ &0 < c /\
     x IN topspace top
     ==> mfd_sectional atlas (\w. c %% g w) x u v = mfd_sectional atlas g x u v / c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`] P2BCS_LOCAL_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[mfd_sectional; METRIC_LOCAL_CMUL; ETA_AX] THEN
  MATCH_MP_TAC APX_LSECTIONAL_SCALE THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) x))
                    (FST(chart_at atlas x))` THEN
  ASM_REWRITE_TAC[]);;

let P2BCS_COMPONENT_DIST = prove
 (`!top atlas (g:A->real^N^N) U.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     U IN connected_components_of top /\ compact_in top U
     ==> (!x y. x IN U /\ y IN U ==> mfd_joinable (top,atlas) x y) /\
         (?D. !x y. x IN U /\ y IN U ==> mfd_dist (top,atlas) g x y <= D)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(U:A->bool) IN connected_components_of top` THEN
  REWRITE_TAC[connected_components_of; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:A` (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  ABBREV_TAC `K = connected_component_of top (x0:A)` THEN
  SUBGOAL_THEN `!y:A. mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) x0 y <=> y IN K`
  ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN ASM_SIMP_TAC[MFD_JOINABLE_CONNECTED_COMPONENT] THEN REWRITE_TAC[IN];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y:A. x IN K /\ y IN K ==> mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) x y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `x0:A` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x0:A`; `x:A`]
                  MFD_JOINABLE_SYM) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x0:A`] MFD_MTOPOLOGY) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x0:A`] MFD_METRIC) THEN
  ASM_REWRITE_TAC[SET_RULE `!s:A->bool. {y | y IN s} = s`] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `mbounded (mfd_metric (top,atlas) (g:A->real^N^N) x0) K` MP_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_MBOUNDED THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; SUBSET_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[MBOUNDED_ALT] THEN STRIP_TAC THEN EXISTS_TAC `b:real` THEN
  ASM_MESON_TAC[]);;

let P2BCS_SUP_SCALE = prove
 (`!s t c. &0 < c /\ ~(s = {}) /\ (?b. !x. x IN s ==> x <= b) /\
           (!y. y IN t <=> ?x. x IN s /\ y = c * x)
           ==> sup t = c * sup s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `b:real`) ASSUME_TAC))) THEN
  SUBGOAL_THEN `t = IMAGE (\x. c * x) (s:real->bool)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[EXTENSION; IN_IMAGE] THEN MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real. x`; `s:real->bool`; `c:real`] P2BCS_SUP_IMAGE_CMUL) THEN
  ASM_REWRITE_TAC[IMAGE_ID; ETA_AX] THEN ANTS_TAC THENL
   [EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[]; SIMP_TAC[]]);;

let P2BCS_CCOMP_CMUL_IMP = prove
 (`!top atlas (g:A->real^3^3) C U c.
     hausdorff_space top /\ &0 < c /\ riemannian_metric atlas g /\
     rfs_c_component (top,atlas) g C U
     ==> rfs_c_component (top,atlas) (\w. c %% g w) C U`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  SUBGOAL_THEN `?x0:A. x0 IN U` (X_CHOOSE_TAC `x0:A`) THENL
   [UNDISCH_TAC `rfs_c_component (top,atlas) (g:A->real^3^3) C U` THEN
    REWRITE_TAC[rfs_c_component] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP NONEMPTY_CONNECTED_COMPONENTS_OF) THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `C:real`; `U:A->bool`; `x0:A`] P2B_C_COMPONENT_SCALAR) THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_TAC `B:real`)
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  UNDISCH_TAC `rfs_c_component (top,atlas) (g:A->real^3^3) C U` THEN
  REWRITE_TAC[rfs_c_component] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONNECTED_COMPONENTS_OF_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `U:A->bool`] P2BCS_COMPONENT_DIST) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `D:real`)) THEN
  SUBGOAL_THEN
   `!w. w IN U
        ==> mfd_scalar atlas (\w. c %% (g:A->real^3^3) w) w = mfd_scalar atlas g w / c /\
            sqrt(rfs_scalar_grad2 atlas (\w. c %% g w) w) /
            (mfd_scalar atlas (\w. c %% g w) w * sqrt(mfd_scalar atlas (\w. c %% g w) w)) =
            sqrt(rfs_scalar_grad2 atlas g w) /
            (mfd_scalar atlas g w * sqrt(mfd_scalar atlas g w)) /\
            abs(rfs_scalar_lap atlas (\w. c %% g w) w +
                &2 * rfs_ric_norm2 atlas (\w. c %% g w) w) /
            mfd_scalar atlas (\w. c %% g w) w pow 2 =
            abs(rfs_scalar_lap atlas g w + &2 * rfs_ric_norm2 atlas g w) /
            mfd_scalar atlas g w pow 2`
  (LABEL_TAC "pt") THENL
   [X_GEN_TAC `w:A` THEN DISCH_TAC THEN MATCH_MP_TAC P2BCS_CMUL_RATIOS THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (mfd_scalar atlas (\w. c %% (g:A->real^3^3) w)) U =
    IMAGE (\w. inv c * mfd_scalar atlas g w) U`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN X_GEN_TAC `q:real` THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `w:A` THEN
    ASM_CASES_TAC `(w:A) IN U` THEN ASM_SIMP_TAC[real_div; REAL_MUL_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sup(IMAGE (mfd_scalar atlas (\w. c %% (g:A->real^3^3) w)) U) =
    inv c * sup(IMAGE (mfd_scalar atlas g) U) /\
    inf(IMAGE (mfd_scalar atlas (\w. c %% (g:A->real^3^3) w)) U) =
    inv c * inf(IMAGE (mfd_scalar atlas g) U)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2BCS_SUP_IMAGE_CMUL THEN ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC GRGD_INF_SCALE THEN ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN
      REWRITE_TAC[IMAGE_EQ_EMPTY; FORALL_IN_IMAGE; IN_IMAGE] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[REAL_LT_IMP_LE]; MESON_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sup {mfd_dist (top,atlas) (\w. c %% (g:A->real^3^3) w) x y | x IN U /\ y IN U} =
    sqrt c * sup {mfd_dist (top,atlas) g x y | x IN U /\ y IN U}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BCS_SUP_SCALE THEN ASM_SIMP_TAC[SQRT_POS_LT] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      EXISTS_TAC `mfd_dist (top,atlas) (g:A->real^3^3) x0 x0` THEN
      MAP_EVERY EXISTS_TAC [`x0:A`; `x0:A`] THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `D:real` THEN ASM_MESON_TAC[];
      X_GEN_TAC `q:real` THEN EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `x:A` (X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC)) THEN
        EXISTS_TAC `mfd_dist (top,atlas) (g:A->real^3^3) x y` THEN
        CONJ_TAC THENL [MAP_EVERY EXISTS_TAC [`x:A`; `y:A`] THEN ASM_REWRITE_TAC[];
                        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_DIST_SCALE THEN
                        ASM_SIMP_TAC[]];
        DISCH_THEN(X_CHOOSE_THEN `q0:real` (CONJUNCTS_THEN2
          (X_CHOOSE_THEN `x:A` (X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC)) ASSUME_TAC)) THEN
        MAP_EVERY EXISTS_TAC [`x:A`; `y:A`] THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC MFD_DIST_SCALE THEN ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt c /\
                !z. inv(sqrt(inv c * z)) = sqrt c * inv(sqrt z)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT] THEN
    REWRITE_TAC[SQRT_MUL; SQRT_INV; REAL_INV_MUL; REAL_INV_INV];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* positive sectional *)
    MAP_EVERY X_GEN_TAC [`x:A`; `u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `c:real`; `x:A`; `u:real^3`; `v:real^3`] P2BCS_SECT_CMUL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[];
    (* sectional lower bound *)
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "rfs_inf_gt" with Failure _ -> false)) THEN
    REWRITE_TAC[rfs_inf_gt; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `ds:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `ds / c` THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `inv C * inv c * sup(IMAGE (mfd_scalar atlas (g:A->real^3^3)) U) =
        inv c * (inv C * sup(IMAGE (mfd_scalar atlas g) U)) /\ ds / c = inv c * ds`
      (CONJUNCTS_THEN SUBST1_TAC) THENL
       [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_LMUL THEN ASM_SIMP_TAC[REAL_LT_INV_EQ]];
      X_GEN_TAC `q:real` THEN
      DISCH_THEN(X_CHOOSE_THEN `x:A` (X_CHOOSE_THEN `u:real^3` (X_CHOOSE_THEN `v:real^3`
        STRIP_ASSUME_TAC))) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `g:A->real^3^3`; `c:real`; `x:A`; `u:real^3`; `v:real^3`]
                    P2BCS_SECT_CMUL) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`x:A`; `u:real^3`; `v:real^3`] THEN ASM_REWRITE_TAC[]];
    (* diameter, lower *)
    ONCE_REWRITE_TAC[REAL_ARITH `inv C * sqrt c * x = sqrt c * (inv C * x)`] THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[];
    (* diameter, upper *)
    ONCE_REWRITE_TAC[REAL_ARITH `C * sqrt c * x = sqrt c * (C * x)`] THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[];
    (* gradient *)
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      (try fst(dest_const(fst(strip_comb(concl th)))) = "rfs_sup_lt" with Failure _ -> false) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_scalar_grad2")) (concl th)))
    THEN REWRITE_TAC[rfs_sup_lt; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `dg:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `dg:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `q:real` THEN DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "pt" (fun th ->
      ACCEPT_TAC(CONJUNCT1(CONJUNCT2(MP (SPEC `y:A` th) (ASSUME `(y:A) IN U`)))));
    (* Laplacian *)
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      (try fst(dest_const(fst(strip_comb(concl th)))) = "rfs_sup_lt" with Failure _ -> false) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_scalar_lap")) (concl th)))
    THEN REWRITE_TAC[rfs_sup_lt; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `dl:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `dl:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `q:real` THEN DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "pt" (fun th ->
      ACCEPT_TAC(CONJUNCT2(CONJUNCT2(MP (SPEC `y:A` th) (ASSUME `(y:A) IN U`)))))]);;

let P2BCS_CCOMP_CMUL = prove
 (`!top atlas (g:A->real^3^3) C U c.
     hausdorff_space top /\ &0 < c /\ riemannian_metric atlas g
     ==> (rfs_c_component (top,atlas) (\w. c %% g w) C U <=>
          rfs_c_component (top,atlas) g C U)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `\w. c %% (g:A->real^3^3) w`; `C:real`; `U:A->bool`; `inv c`]
                  P2BCS_CCOMP_CMUL_IMP) THEN
    ASM_SIMP_TAC[REAL_LT_INV_EQ; RIEMANNIAN_METRIC_CMUL; MATRIX_CMUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; MATRIX_CMUL_LID; ETA_AX];
    DISCH_TAC THEN MATCH_MP_TAC P2BCS_CCOMP_CMUL_IMP THEN ASM_REWRITE_TAC[]]);;

let P2BCS_ROUND_CMUL = prove
 (`!top atlas (g:A->real^3^3) eps U c.
     &0 < c
     ==> (rfs_round_component (top,atlas) (\w. c %% g w) eps U <=>
          rfs_round_component (top,atlas) g eps U)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_round_component; MATRIX_CMUL_ASSOC] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `q:real` (X_CHOOSE_THEN `g1:A->real^3^3` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`q * c:real`; `g1:A->real^3^3`] THEN
    ASM_SIMP_TAC[REAL_LT_MUL];
    DISCH_THEN(X_CHOOSE_THEN `q:real` (X_CHOOSE_THEN `g1:A->real^3^3` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`q / c:real`; `g1:A->real^3^3`] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_DIV_RMUL; REAL_LT_IMP_NZ]]);;

let P2BCS_CANON_CMUL = prove
 (`!top atlas (g:A->real^3^3) C eps x U c.
     hausdorff_space top /\ &0 < c /\ riemannian_metric atlas g
     ==> (rfs_canonical_nbhd (top,atlas) (\w. c %% g w) C eps x U <=>
          rfs_canonical_nbhd (top,atlas) g C eps x U)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_canonical_nbhd] THEN
  ASM_SIMP_TAC[P2BCS_NECK_CMUL; P2BCS_CAP_CMUL; P2BCS_CCOMP_CMUL; P2BCS_ROUND_CMUL]);;

