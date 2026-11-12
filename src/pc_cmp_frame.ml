(* ========================================================================= *)
(* Unit pc_cmp_frame (comparison-geometry layer CMP): parallel orthonormal   *)
(* frames along a curve and frame coordinates of fields; the Jacobi equation *)
(* in frame coordinates (a'' = -R a with R symmetric); the matrix ODE of the *)
(* Jacobi matrix: Wronskian symmetry, the derivative of the inverse, the     *)
(* Riccati equation of e.S e for S = A' A^-1, Jacobi's formula for det A.    *)
(* Frames and Jacobi fields enter as hypotheses (their existence is          *)
(* MFD_PARALLEL_EXISTS_UNIQUE / MFD_JACOBI_EXISTS_UNIQUE of the pc_geo       *)
(* units), so this unit does not need their proofs.                          *)
(* ========================================================================= *)

needs "src/pc_geo_covd.ml";;
needs "src/pc_lrg_evol.ml";;
needs "src/pc_cmp_ode.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Vocabulary; inner products of parallel fields are constant.               *)
(* ========================================================================= *)

(* gamma is a C^1 curve on every compact subinterval of the open interval J  *)
(* (the hypothesis of the covariant-derivative lemmas of pc_geo_covd).       *)

let cmp_curve_on = new_definition
 `cmp_curve_on (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
               (gamma:real->A) (J:real->bool) <=>
    real_open J /\ is_realinterval J /\
    (!a b. a <= b /\ real_interval[a,b] SUBSET J
           ==> mfd_c1_curve (top,atlas) gamma a b)`;;

(* The frame matrix (columns E 1 t, ..., E N t, preferred coordinates at    *)
(* gamma t), parallel orthonormal frames along gamma on J, the frame        *)
(* coordinates of a field Y, and the curvature matrix                        *)
(* R_ij = <E_i, R(E_j,T)T> along gamma (T the velocity).                     *)

let cmp_fmat = new_definition
 `cmp_fmat (E:num->real->real^N) (t:real) = (lambda i j. E j t$i):real^N^N`;;

let cmp_pframe = new_definition
 `cmp_pframe (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
             (gamma:real->A) (J:real->bool) (E:num->real->real^N) <=>
    (!j. 1 <= j /\ j <= dimindex(:N) ==> mfd_parallel atlas g gamma J (E j)) /\
    (!t. t IN J ==> transp(cmp_fmat E t) ** g(gamma t) ** cmp_fmat E t = mat 1)`;;

let cmp_fcoord = new_definition
 `cmp_fcoord (g:A->real^N^N) (gamma:real->A) (E:num->real->real^N)
             (Y:real->real^N) (t:real) =
    transp(cmp_fmat E t) ** g(gamma t) ** Y t`;;

let cmp_rmat = new_definition
 `cmp_rmat (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (gamma:real->A)
           (E:num->real->real^N) (t:real) =
    (lambda i j. E i t dot
                 (g(gamma t) **
                  mfd_riemann atlas g (gamma t) (E j t) (mfd_vel atlas gamma t)
                                                   (mfd_vel atlas gamma t))):real^N^N`;;

(* Inner products of parallel fields are constant on J (MFD_COVD_METRIC). *)

let CMPF_PARALLEL_INNER = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J Y1 Y2 s t.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        cmp_curve_on (top,atlas) gamma J /\
        mfd_parallel atlas g gamma J Y1 /\ mfd_parallel atlas g gamma J Y2 /\
        s IN J /\ t IN J
        ==> Y1 s dot (g(gamma s) ** Y2 s) = Y1 t dot (g(gamma t) ** Y2 t)`,
  REWRITE_TAC[cmp_curve_on; mfd_parallel] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\r. (Y1:real->real^N) r dot ((g:A->real^N^N)((gamma:real->A) r) ** Y2 r)`;
                 `J:real->bool`] HAS_REAL_DERIVATIVE_ZERO_CONSTANT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                   `Y1:real->real^N`; `Y2:real->real^N`; `x:real`] MFD_COVD_METRIC) THEN
    ASM_SIMP_TAC[DOT_LZERO; MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_ADD_RID;
                 LIFT_NUM];
    DISCH_THEN(X_CHOOSE_TAC `c:real`) THEN RULE_ASSUM_TAC BETA_RULE THEN
    ASM_SIMP_TAC[]]);;

(* Entries of the Gram matrix of the frame. *)

let CMPF_FMAT_GRAM = prove
 (`!(E:num->real->real^N) (G:real^N^N) t i j.
        1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
        ==> (transp(cmp_fmat E t) ** G ** cmp_fmat E t)$i$j = E i t dot (G ** E j t)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[matrix_mul; transp; cmp_fmat; LAMBDA_BETA; dot; matrix_vector_mul] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LAMBDA_BETA] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LAMBDA_BETA]);;

(* A family of parallel fields orthonormal at one time is a frame on J. *)

let CMPF_PFRAME_FROM_POINT = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (E:num->real->real^N) t0.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        cmp_curve_on (top,atlas) gamma J /\ t0 IN J /\
        (!j. 1 <= j /\ j <= dimindex(:N) ==> mfd_parallel atlas g gamma J (E j)) /\
        transp(cmp_fmat E t0) ** g(gamma t0) ** cmp_fmat E t0 = mat 1
        ==> cmp_pframe atlas g gamma J E`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cmp_pframe] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
  REWRITE_TAC[CART_EQ] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CMPF_FMAT_GRAM] THEN
  MATCH_MP_TAC CMPF_PARALLEL_INNER THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                        `J:real->bool`] THEN
  ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* Frame coordinates.                                                        *)
(* ========================================================================= *)

let CMPF_FCOORD_COMPONENT = prove
 (`!(g:A->real^N^N) (gamma:real->A) (E:num->real->real^N) Y t i.
        1 <= i /\ i <= dimindex(:N)
        ==> (cmp_fcoord g gamma E Y t)$i = E i t dot (g(gamma t) ** Y t)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[cmp_fcoord; matrix_vector_mul; transp; cmp_fmat; LAMBDA_BETA; dot] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LAMBDA_BETA]);;

(* The frame matrix is invertible, with inverse (transp F) G. *)

let CMPF_FRAME_RIGHT_INVERSE = prove
 (`!(Q:real^N^N) (G:real^N^N).
        transp Q ** G ** Q = mat 1 ==> Q ** transp Q ** G = mat 1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`transp(Q:real^N^N) ** (G:real^N^N)`; `Q:real^N^N`]
    MATRIX_LEFT_RIGHT_INVERSE) THEN
  ASM_REWRITE_TAC[GSYM MATRIX_MUL_ASSOC]);;

let CMPF_EXPAND = prove
 (`!atlas (g:A->real^N^N) (gamma:real->A) J (E:num->real->real^N) Y t.
        cmp_pframe atlas g gamma J E /\ t IN J
        ==> Y t = cmp_fmat E t ** cmp_fcoord g gamma E Y t`,
  REWRITE_TAC[cmp_pframe; cmp_fcoord] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CMPF_FRAME_RIGHT_INVERSE) THEN
  REWRITE_TAC[MATRIX_MUL_ASSOC] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LID]);;

(* In an orthonormal frame the metric becomes the dot product of the        *)
(* coordinates.                                                              *)

let CMPF_FCOORD_DOT = prove
 (`!atlas (g:A->real^N^N) (gamma:real->A) J (E:num->real->real^N) Y1 Y2 t.
        cmp_pframe atlas g gamma J E /\ t IN J
        ==> Y1 t dot (g(gamma t) ** Y2 t) =
            cmp_fcoord g gamma E Y1 t dot cmp_fcoord g gamma E Y2 t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `gamma:real->A`; `J:real->bool`; `E:num->real->real^N`]
    CMPF_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `a1 = cmp_fcoord (g:A->real^N^N) (gamma:real->A) (E:num->real->real^N) Y1 t` THEN
  ABBREV_TAC `a2 = cmp_fcoord (g:A->real^N^N) (gamma:real->A) (E:num->real->real^N) Y2 t` THEN
  SUBGOAL_THEN `(Y1:real->real^N) t = cmp_fmat E t ** a1 /\
                (Y2:real->real^N) t = cmp_fmat E t ** a2`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [MAP_EVERY EXPAND_TAC ["a1"; "a2"] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM DOT_MATRIX_TRANSP_RMUL; MATRIX_VECTOR_MUL_ASSOC] THEN
  UNDISCH_TAC `cmp_pframe atlas (g:A->real^N^N) (gamma:real->A) J (E:num->real->real^N)` THEN
  REWRITE_TAC[cmp_pframe] THEN DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[MATRIX_MUL_ASSOC] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LID]);;

(* Frame coordinates differentiate to the frame coordinates of the          *)
(* covariant derivative.                                                     *)

let CMPF_FCOORD_DERIV = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (E:num->real->real^N) Y t.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        cmp_curve_on (top,atlas) gamma J /\ cmp_pframe atlas g gamma J E /\
        mfd_field_diff atlas gamma Y J /\ t IN J
        ==> ((\s. cmp_fcoord g gamma E Y (drop s)) has_vector_derivative
             cmp_fcoord g gamma E (mfd_covd atlas g gamma Y) t) (at (lift t))`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [HAS_VECTOR_DERIVATIVE_COMPONENTWISE_AT] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CMPF_FCOORD_COMPONENT] THEN
  UNDISCH_TAC `cmp_pframe atlas (g:A->real^N^N) (gamma:real->A) J (E:num->real->real^N)` THEN
  REWRITE_TAC[cmp_pframe] THEN
  DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT1) THEN ASM_REWRITE_TAC[mfd_parallel] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `cmp_curve_on (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
                 (gamma:real->A) J` THEN
  REWRITE_TAC[cmp_curve_on] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                 `(E:num->real->real^N) i`; `Y:real->real^N`; `t:real`]
    MFD_COVD_METRIC) THEN
  ASM_SIMP_TAC[DOT_LZERO; REAL_ADD_LID]);;

(* ========================================================================= *)
(* The curvature matrix and the Jacobi equation in frame coordinates.        *)
(* ========================================================================= *)

let CMPF_FMAT_TRANSP_ROW = prove
 (`!(E:num->real->real^N) t i.
        1 <= i /\ i <= dimindex(:N) ==> (transp(cmp_fmat E t))$i = E i t`,
  SIMP_TAC[CART_EQ; transp; cmp_fmat; LAMBDA_BETA]);;

let CMPF_FMAT_MUL = prove
 (`!(E:num->real->real^N) t a.
        cmp_fmat E t ** a = vsum(1..dimindex(:N)) (\j. a$j % E j t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MATRIX_VECTOR_COLUMN] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN SIMP_TAC[CMPF_FMAT_TRANSP_ROW]);;

(* The preferred-chart data at a point: a metric field around the chart     *)
(* point, equal to g x there.                                                *)

let CMPF_LOCAL_METRIC = prove
 (`!top atlas (g:A->real^N^N) x.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        riemannian_metric atlas g /\ x IN topspace top
        ==> metric_field (IMAGE (SND(chart_at atlas x)) (FST(chart_at atlas x)))
                         (metric_local atlas (chart_at atlas x) g) /\
            SND(chart_at atlas x) x IN
            IMAGE (SND(chart_at atlas x)) (FST(chart_at atlas x)) /\
            metric_local atlas (chart_at atlas x) g (SND(chart_at atlas x) x) = g x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC METRIC_LOCAL_AT THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[]]);;

(* Symmetries of the curvature at a point of the manifold. *)

let CMPF_RIEMANN_PAIR_SYM = prove
 (`!top atlas (g:A->real^N^N) x u v.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        riemannian_metric atlas g /\ x IN topspace top
        ==> u dot (g x ** mfd_riemann atlas g x v w w) =
            v dot (g x ** mfd_riemann atlas g x u w w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] CMPF_LOCAL_METRIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[mfd_riemann] THEN
  MATCH_MP_TAC LRIEMANN_PAIR_SYM THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                    (FST(chart_at atlas x))` THEN
  ASM_REWRITE_TAC[]);;

let CMPF_RIEMANN_TANGENT = prove
 (`!top atlas (g:A->real^N^N) x u w.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        riemannian_metric atlas g /\ x IN topspace top
        ==> w dot (g x ** mfd_riemann atlas g x u w w) = &0 /\
            mfd_riemann atlas g x w w u = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] CMPF_LOCAL_METRIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[mfd_riemann] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                          (FST(chart_at atlas x))`;
                   `metric_local atlas (chart_at atlas x) (g:A->real^N^N)`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x`;
                   `u:real^N`; `w:real^N`; `w:real^N`; `w:real^N`]
      LRIEMANN_METRIC_ANTISYM) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                          (FST(chart_at atlas x))`;
                   `metric_local atlas (chart_at atlas x) (g:A->real^N^N)`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x`;
                   `w:real^N`; `w:real^N`; `u:real^N`] LRIEMANN_ANTISYM) THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC]);;

let CMPF_RIEMANN_LINEAR = prove
 (`!top atlas (g:A->real^N^N) x v w.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        riemannian_metric atlas g /\ x IN topspace top
        ==> linear (\u. mfd_riemann atlas g x u v w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] CMPF_LOCAL_METRIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REWRITE_TAC[mfd_riemann] THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                        (FST(chart_at atlas x))`;
                 `metric_local atlas (chart_at atlas x) (g:A->real^N^N)`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x`]
    LRIEMANN_TRILINEAR) THEN
  ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* The curvature matrix is symmetric, vanishes on the tangent direction, and *)
(* gives the Jacobi equation in frame coordinates.                           *)
(* ========================================================================= *)

let CMPF_RMAT_SYM = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) (E:num->real->real^N) t.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        gamma t IN topspace top
        ==> transp(cmp_rmat atlas g gamma E t) = cmp_rmat atlas g gamma E t`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[CART_EQ; TRANSP_COMPONENT; cmp_rmat; LAMBDA_BETA] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CMPF_RIEMANN_PAIR_SYM THEN
  EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]);;

let CMPF_RMAT_TANGENT = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) (E:num->real->real^N) t c j.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        gamma t IN topspace top /\ E 1 t = c % mfd_vel atlas gamma t /\
        1 <= j /\ j <= dimindex(:N)
        ==> cmp_rmat atlas g gamma E t$1$j = &0 /\
            cmp_rmat atlas g gamma E t$j$1 = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 <= dimindex(:N)` ASSUME_TAC THENL
   [REWRITE_TAC[DIMINDEX_GE_1]; ALL_TAC] THEN
  ASM_SIMP_TAC[cmp_rmat; LAMBDA_BETA; LE_REFL] THEN CONJ_TAC THENL
   [REWRITE_TAC[DOT_LMUL] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `(gamma:real->A) t`; `(E:num->real->real^N) j t`;
                   `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) t`]
      CMPF_RIEMANN_TANGENT) THEN
    ASM_SIMP_TAC[REAL_MUL_RZERO];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `(gamma:real->A) t`;
                   `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) t`;
                   `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) t`]
      CMPF_RIEMANN_LINEAR) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[REWRITE_RULE[] (MATCH_MP LINEAR_CMUL th)]) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `(gamma:real->A) t`;
                   `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) t`;
                   `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) t`]
      CMPF_RIEMANN_TANGENT) THEN
    ASM_SIMP_TAC[VECTOR_MUL_RZERO; MATRIX_VECTOR_MUL_RZERO; DOT_RZERO]]);;

let CMPF_MATVEC_VSUM = prove
 (`!(A:real^N^M) (f:num->real^N) n.
        A ** vsum(1..n) f = vsum(1..n) (\j. A ** f j)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`\x:real^N. (A:real^N^M) ** x`; `f:num->real^N`; `1..n`]
    LINEAR_VSUM) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR; FINITE_NUMSEG; o_DEF]);;

(* Frame coordinates of R(Y,T)T are R(t) times the coordinates of Y. *)

let CMPF_RIEMANN_FCOORD = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (E:num->real->real^N) Y t.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        cmp_pframe atlas g gamma J E /\ t IN J /\ gamma t IN topspace top
        ==> cmp_fcoord g gamma E
              (\s. mfd_riemann atlas g (gamma s) (Y s) (mfd_vel atlas gamma s)
                                                   (mfd_vel atlas gamma s)) t =
            cmp_rmat atlas g gamma E t ** cmp_fcoord g gamma E Y t`,
  REPEAT STRIP_TAC THEN SIMP_TAC[CART_EQ] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CMPF_FCOORD_COMPONENT] THEN
  SUBGOAL_THEN
   `(Y:real->real^N) t =
    vsum(1..dimindex(:N))
      (\j. cmp_fcoord (g:A->real^N^N) (gamma:real->A) E Y t$j %
           (E:num->real->real^N) j t)`
  (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THENL
   [MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `gamma:real->A`; `J:real->bool`; `E:num->real->real^N`;
                   `Y:real->real^N`; `t:real`] CMPF_EXPAND) THEN
    ASM_REWRITE_TAC[CMPF_FMAT_MUL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(gamma:real->A) t`;
                 `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) t`;
                 `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) t`]
    CMPF_RIEMANN_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (SPEC `dimindex(:N)` (SPEC `1` FINITE_NUMSEG)) o
              MATCH_MP (REWRITE_RULE[IMP_CONJ] LINEAR_VSUM)) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[REWRITE_RULE[o_DEF] th]) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[REWRITE_RULE[] (MATCH_MP LINEAR_CMUL th)]) THEN
  REWRITE_TAC[CMPF_MATVEC_VSUM; MATRIX_VECTOR_MUL_RMUL] THEN
  SIMP_TAC[DOT_RSUM; FINITE_NUMSEG; DOT_RMUL] THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT] THEN
  GEN_REWRITE_TAC RAND_CONV [dot] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[cmp_rmat; LAMBDA_BETA] THEN REWRITE_TAC[REAL_MUL_SYM]);;

(* ========================================================================= *)
(* Jacobi fields along a geodesic in frame coordinates: a' = b, b' = -R a.   *)
(* ========================================================================= *)

let CMPF_GEODESIC_CURVE_ON = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J
        ==> cmp_curve_on (top,atlas) gamma J`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cmp_curve_on] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`]
    GEOL_GEODESIC_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `a:real`; `b:real`]
    MFD_GEODESIC_C1_CURVE) THEN
  ASM_SIMP_TAC[]);;

let CMPF_JACOBI_FCOORD = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (E:num->real->real^N) Y t.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\ cmp_pframe atlas g gamma J E /\
        mfd_jacobi atlas g gamma J Y /\ t IN J
        ==> ((\s. cmp_fcoord g gamma E Y (drop s)) has_vector_derivative
             cmp_fcoord g gamma E (mfd_covd atlas g gamma Y) t) (at (lift t)) /\
            ((\s. cmp_fcoord g gamma E (mfd_covd atlas g gamma Y) (drop s))
             has_vector_derivative
             --(cmp_rmat atlas g gamma E t ** cmp_fcoord g gamma E Y t)) (at (lift t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `cmp_curve_on (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
                              (gamma:real->A) J` ASSUME_TAC THENL
   [MATCH_MP_TAC CMPF_GEODESIC_CURVE_ON THEN EXISTS_TAC `g:A->real^N^N` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) t IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                          `J:real->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `mfd_jacobi atlas (g:A->real^N^N) (gamma:real->A) J Y` THEN
  REWRITE_TAC[mfd_jacobi] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC CMPF_FCOORD_DERIV THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `J:real->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                 `E:num->real->real^N`; `mfd_covd atlas (g:A->real^N^N) (gamma:real->A) Y`;
                 `t:real`] CMPF_FCOORD_DERIV) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                 `E:num->real->real^N`; `Y:real->real^N`; `t:real`]
    CMPF_RIEMANN_FCOORD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[cmp_fcoord; GSYM MATRIX_VECTOR_MUL_RNEG] THEN
  REPEAT AP_TERM_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
  VECTOR_ARITH_TAC);;

(* ========================================================================= *)
(* The matrix ODE A' = B, B' = -R A (columns a j, b j): the Wronskian A^T B  *)
(* is symmetric when A vanishes at one time.                                 *)
(* ========================================================================= *)

let CMPF_FMAT_GRAM2 = prove
 (`!(a:num->real->real^N) (b:num->real->real^N) t i j.
        1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
        ==> (transp(cmp_fmat a t) ** cmp_fmat b t)$i$j = a i t dot b j t`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[matrix_mul; transp; cmp_fmat; LAMBDA_BETA; dot] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LAMBDA_BETA]);;

let CMPF_DOT_DERIV = prove
 (`!(u:real->real^N) (v:real->real^N) u' v' t.
        ((\s. u(drop s)) has_vector_derivative u') (at (lift t)) /\
        ((\s. v(drop s)) has_vector_derivative v') (at (lift t))
        ==> ((\s. lift(u(drop s) dot v(drop s))) has_vector_derivative
             lift(u t dot v' + u' dot v t)) (at (lift t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^N y:real^N. lift(x dot y)`; `\s. (u:real->real^N)(drop s)`;
                 `\s. (v:real->real^N)(drop s)`; `u':real^N`; `v':real^N`; `lift t`]
    HAS_VECTOR_DERIVATIVE_BILINEAR_AT) THEN
  ASM_REWRITE_TAC[BILINEAR_DOT; LIFT_ADD; LIFT_DROP]);;

let CMPF_WRONSKIAN = prove
 (`!(a:num->real->real^N) b R J t0.
        is_realinterval J /\ t0 IN J /\
        (!j t. 1 <= j /\ j <= dimindex(:N) /\ t IN J
               ==> ((\s. a j (drop s)) has_vector_derivative b j t) (at (lift t)) /\
                   ((\s. b j (drop s)) has_vector_derivative --(R t ** a j t))
                   (at (lift t))) /\
        (!t. t IN J ==> transp(R t) = R t) /\
        (!j. 1 <= j /\ j <= dimindex(:N) ==> a j t0 = vec 0)
        ==> !t. t IN J
                ==> transp(cmp_fmat a t) ** cmp_fmat b t =
                    transp(cmp_fmat b t) ** cmp_fmat a t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  REWRITE_TAC[CART_EQ] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[CMPF_FMAT_GRAM2] THEN
  MP_TAC(ISPECL [`\s. (a:num->real->real^N) i s dot (b:num->real->real^N) j s -
                       b i s dot a j s`;
                 `J:real->bool`] HAS_REAL_DERIVATIVE_ZERO_CONSTANT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF; LIFT_SUB] THEN
    SUBGOAL_THEN
     `&0 = ((a:num->real->real^N) i x dot --((R:real->real^N^N) x ** a j x) +
            (b:num->real->real^N) i x dot b j x) -
           (b i x dot b j x + --(R x ** a i x) dot a j x)`
    SUBST1_TAC THENL
     [REWRITE_TAC[DOT_LNEG; DOT_RNEG] THEN
      ONCE_REWRITE_TAC[DOT_SYM] THEN
      REWRITE_TAC[GSYM DOT_MATRIX_TRANSP_RMUL] THEN
      FIRST_X_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(x:real) IN (J:real->bool)`)]) THEN
      REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[LIFT_SUB; LIFT_ADD] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN CONJ_TAC THEN
    REWRITE_TAC[GSYM LIFT_ADD] THEN MATCH_MP_TAC CMPF_DOT_DERIV THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `c:real`) THEN RULE_ASSUM_TAC BETA_RULE THEN
  MATCH_MP_TAC(REAL_ARITH `x - y = &0 ==> x = y`) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(t:real) IN (J:real->bool)`)]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t0:real`) THEN ASM_SIMP_TAC[DOT_LZERO; DOT_RZERO] THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Calculus of matrix curves (vectorized): products, the matrix of         *)
(* columns, the inverse; the shape operator S = B A^-1 is symmetric when   *)
(* A^T B is.                                                               *)
(* ========================================================================= *)

let CMPF_HAS_VD_MATMUL = prove
 (`!(P:real->real^N^N) (Q:real->real^N^N) P' Q' t.
        ((\s. vectorize(P(drop s))) has_vector_derivative vectorize P') (at (lift t)) /\
        ((\s. vectorize(Q(drop s))) has_vector_derivative vectorize Q') (at (lift t))
        ==> ((\s. vectorize(P(drop s) ** Q(drop s))) has_vector_derivative
             vectorize(P t ** Q' + P' ** Q t)) (at (lift t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\(m1:real^(N,N)finite_prod) (m2:real^(N,N)finite_prod).
       (vectorize:real^N^N->real^(N,N)finite_prod)
         ((matrify m1:real^N^N) ** (matrify m2:real^N^N))`;
    `\s. (vectorize:real^N^N->real^(N,N)finite_prod) ((P:real->real^N^N) (drop s))`;
    `\s. (vectorize:real^N^N->real^(N,N)finite_prod) ((Q:real->real^N^N) (drop s))`;
    `(vectorize:real^N^N->real^(N,N)finite_prod) P'`;
    `(vectorize:real^N^N->real^(N,N)finite_prod) Q'`; `lift t`]
    HAS_VECTOR_DERIVATIVE_BILINEAR_AT) THEN
  ASM_REWRITE_TAC[LRG_BILINEAR_MATRIX_MUL; MATRIFY_VECTORIZE; LIFT_DROP] THEN
  REWRITE_TAC[VECTORIZE_ADD]);;

let CMPF_HAS_VD_MATVEC = prove
 (`!(P:real->real^N^N) P' (e:real^N) t.
        ((\s. vectorize(P(drop s))) has_vector_derivative vectorize P') (at (lift t))
        ==> ((\s. P(drop s) ** e) has_vector_derivative P' ** e) (at (lift t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\(m:real^(N,N)finite_prod) (v:real^N). (matrify m:real^N^N) ** v`;
    `\s. (vectorize:real^N^N->real^(N,N)finite_prod) ((P:real->real^N^N) (drop s))`;
    `\s:real^1. (e:real^N)`;
    `(vectorize:real^N^N->real^(N,N)finite_prod) P'`; `vec 0:real^N`; `lift t`]
    HAS_VECTOR_DERIVATIVE_BILINEAR_AT) THEN
  ASM_REWRITE_TAC[LRG_BILINEAR_MATRIFY_MUL; MATRIFY_VECTORIZE; LIFT_DROP;
                  HAS_VECTOR_DERIVATIVE_CONST; MATRIX_VECTOR_MUL_RZERO;
                  VECTOR_ADD_LID]);;

(* The matrix with columns a j has the matrix with columns b j as          *)
(* derivative when each column does.                                         *)

let CMPF_HAS_VD_FMAT = prove
 (`!(a:num->real->real^N) (b:num->real->real^N) t.
        (!j. 1 <= j /\ j <= dimindex(:N)
             ==> ((\s. a j (drop s)) has_vector_derivative b j t) (at (lift t)))
        ==> ((\s. vectorize(cmp_fmat a (drop s))) has_vector_derivative
             vectorize(cmp_fmat b t)) (at (lift t))`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [HAS_VECTOR_DERIVATIVE_COMPONENTWISE_AT] THEN
  REWRITE_TAC[DIMINDEX_FINITE_PROD] THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  MP_TAC(SPEC `k:num` LRG_VECTORIZE_INDEX) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[VECTORIZE_COMPONENT; cmp_fmat; LAMBDA_BETA] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `1 + (k - 1) MOD dimindex(:N)`) THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC LAND_CONV [HAS_VECTOR_DERIVATIVE_COMPONENTWISE_AT] THEN
  DISCH_THEN(MP_TAC o SPEC `1 + (k - 1) DIV dimindex(:N)`) THEN
  ASM_REWRITE_TAC[]);;

(* Derivative of the inverse of a matrix curve. *)

let CMPF_HAS_VD_MATRIX_INV = prove
 (`!(P:real->real^N^N) P' t.
        ((\s. vectorize(P(drop s))) has_vector_derivative vectorize P') (at (lift t)) /\
        ~(det(P t) = &0)
        ==> ((\s. vectorize(matrix_inv(P(drop s)))) has_vector_derivative
             vectorize(--(matrix_inv(P t) ** P' ** matrix_inv(P t)))) (at (lift t))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `S = {x:real^(N,N)finite_prod | ~(det(matrify x:real^N^N) = &0)}` THEN
  SUBGOAL_THEN `open (S:real^(N,N)finite_prod->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN
    MP_TAC(ISPECL [`\x:real^(N,N)finite_prod. lift(det(matrify x:real^N^N))`;
                   `{y:real^1 | ~(y = vec 0)}`] CONTINUOUS_OPEN_PREIMAGE_UNIV) THEN
    REWRITE_TAC[IN_ELIM_THM; GSYM LIFT_NUM; LIFT_EQ] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
      REWRITE_TAC[LRG_DET_DIFFERENTIABLE];
      REWRITE_TAC[SET_RULE `{y | ~(y = a)} = (:real^1) DELETE a`] THEN
      SIMP_TAC[OPEN_DELETE; OPEN_UNIV]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`matrify:real^(N,N)finite_prod->real^N^N`; `S:real^(N,N)finite_prod->bool`;
                 `(vectorize:real^N^N->real^(N,N)finite_prod) ((P:real->real^N^N) t)`]
    LRG_HAS_DERIVATIVE_MATRIX_INV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[IN_ELIM_THM; MATRIFY_VECTORIZE] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[o_DEF; VECTORIZE_MATRIFY; SMOOTH_MAP_ON_ID];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIFY_VECTORIZE] THEN
  SUBGOAL_THEN
   `frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o matrify)
      (at (vectorize((P:real->real^N^N) t))) = (\h. h)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    REWRITE_TAC[o_DEF; VECTORIZE_MATRIFY; HAS_DERIVATIVE_ID];
    ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o BETA_RULE o REWRITE_RULE[o_DEF]) THEN
  UNDISCH_TAC
   `((\s. (vectorize:real^N^N->real^(N,N)finite_prod) ((P:real->real^N^N) (drop s)))
     has_vector_derivative vectorize P') (at (lift t))` THEN
  REWRITE_TAC[has_vector_derivative] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`\s. (vectorize:real^N^N->real^(N,N)finite_prod) ((P:real->real^N^N) (drop s))`;
    `(vectorize:real^N^N->real^(N,N)finite_prod) o
     (\z:real^(N,N)finite_prod. matrix_inv(matrify z:real^N^N))`;
    `\x:real^1. drop x % (vectorize:real^N^N->real^(N,N)finite_prod) P'`;
    `\h:real^(N,N)finite_prod.
       (vectorize:real^N^N->real^(N,N)finite_prod)
         (--(matrix_inv((P:real->real^N^N) t) ** matrify h ** matrix_inv(P t)))`;
    `lift t`] DIFF_CHAIN_AT) THEN
  REWRITE_TAC[o_DEF; MATRIFY_VECTORIZE; LIFT_DROP] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^1` THEN
  REWRITE_TAC[MATRIFY_CMUL; MATRIFY_VECTORIZE; MATRIX_MUL_LMUL; MATRIX_MUL_RMUL] THEN
  REWRITE_TAC[MATRIX_NEG_MINUS1; MATRIX_CMUL_ASSOC; VECTORIZE_CMUL; VECTOR_MUL_ASSOC] THEN
  REWRITE_TAC[REAL_MUL_SYM]);;

(* S = B A^-1 is symmetric when A is invertible and A^T B symmetric. *)

let CMPF_SHAPE_SYM = prove
 (`!(A:real^N^N) (B:real^N^N).
        invertible A /\ transp A ** B = transp B ** A
        ==> transp(B ** matrix_inv A) = B ** matrix_inv A`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MATRIX_INV) THEN
  SUBGOAL_THEN
   `transp(matrix_inv(A:real^N^N)) ** (transp A ** B) ** matrix_inv A =
    transp(matrix_inv A) ** (transp B ** A) ** matrix_inv A`
  MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MATRIX_MUL_ASSOC] THEN
  REWRITE_TAC[GSYM MATRIX_TRANSP_MUL] THEN ASM_REWRITE_TAC[TRANSP_MAT] THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN ASM_REWRITE_TAC[MATRIX_MUL_LID; MATRIX_MUL_RID] THEN
  MESON_TAC[]);;

(* ========================================================================= *)
(* The Riccati equation of the shape operator S = B A^-1 and Jacobi's        *)
(* formula for det A, for matrix curves with A' = B, B' = -R A.              *)
(* ========================================================================= *)

let CMPF_SHAPE_DERIV = prove
 (`!(A:real->real^N^N) (B:real->real^N^N) (R:real^N^N) t.
        ((\s. vectorize(A(drop s))) has_vector_derivative vectorize(B t)) (at (lift t)) /\
        ((\s. vectorize(B(drop s))) has_vector_derivative vectorize(--(R ** A t)))
        (at (lift t)) /\
        ~(det(A t) = &0)
        ==> ((\s. vectorize(B(drop s) ** matrix_inv(A(drop s)))) has_vector_derivative
             vectorize(--R - (B t ** matrix_inv(A t)) ** (B t ** matrix_inv(A t))))
            (at (lift t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`B:real->real^N^N`; `\s. matrix_inv((A:real->real^N^N) s)`;
                 `--((R:real^N^N) ** (A:real->real^N^N) t)`;
                 `--(matrix_inv((A:real->real^N^N) t) ** B t ** matrix_inv(A t))`;
                 `t:real`] CMPF_HAS_VD_MATMUL) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CMPF_HAS_VD_MATRIX_INV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `invertible((A:real->real^N^N) t)` MP_TAC THENL
   [ASM_REWRITE_TAC[INVERTIBLE_DET_NZ]; ALL_TAC] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MATRIX_INV) THEN
  REWRITE_TAC[MATRIX_MUL_RNEG; MATRIX_MUL_LNEG; GSYM MATRIX_MUL_ASSOC] THEN
  ASM_REWRITE_TAC[MATRIX_MUL_RID] THEN
  REWRITE_TAC[MATRIX_MUL_ASSOC; MATRIX_SUB; MATRIX_NEG_NEG] THEN
  REWRITE_TAC[MATRIX_ADD_SYM]);;

(* The Riccati equation of e.(S e): (e.S e)' = -e.R e - |S e|^2 when S is   *)
(* symmetric.                                                                *)

let CMPF_RICCATI_QUAD = prove
 (`!(A:real->real^N^N) (B:real->real^N^N) (R:real^N^N) (e:real^N) t.
        ((\s. vectorize(A(drop s))) has_vector_derivative vectorize(B t)) (at (lift t)) /\
        ((\s. vectorize(B(drop s))) has_vector_derivative vectorize(--(R ** A t)))
        (at (lift t)) /\
        ~(det(A t) = &0) /\
        transp(B t ** matrix_inv(A t)) = B t ** matrix_inv(A t)
        ==> ((\s. lift(e dot ((B(drop s) ** matrix_inv(A(drop s))) ** e)))
             has_vector_derivative
             lift(--(e dot (R ** e)) -
                  ((B t ** matrix_inv(A t)) ** e) dot ((B t ** matrix_inv(A t)) ** e)))
            (at (lift t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\s. (B:real->real^N^N) s ** matrix_inv((A:real->real^N^N) s)`;
                 `--(R:real^N^N) - (B t ** matrix_inv((A:real->real^N^N) t)) **
                                    (B t ** matrix_inv(A t))`;
                 `e:real^N`; `t:real`] CMPF_HAS_VD_MATVEC) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC CMPF_SHAPE_DERIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`\s:real. (e:real^N)`;
                 `\s. ((B:real->real^N^N) s ** matrix_inv((A:real->real^N^N) s)) ** e`;
                 `vec 0:real^N`;
                 `(--(R:real^N^N) - (B t ** matrix_inv((A:real->real^N^N) t)) **
                                    (B t ** matrix_inv(A t))) ** e`;
                 `t:real`] CMPF_DOT_DERIV) THEN
  ASM_REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST; DOT_LZERO; REAL_ADD_RID] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ABBREV_TAC `S = (B:real->real^N^N) t ** matrix_inv((A:real->real^N^N) t)` THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB; MATRIX_VECTOR_MUL_LNEG; DOT_RSUB;
              DOT_RNEG] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  SUBGOAL_THEN `(e:real^N) dot ((S:real^N^N) ** S ** e) = (S ** e) dot (S ** e)`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV)
      [GSYM(ASSUME `transp(S:real^N^N) = S`)] THEN
    REWRITE_TAC[DOT_MATRIX_TRANSP_RMUL];
    REAL_ARITH_TAC]);;

(* Jacobi's formula: (det A)' = det A tr(A^-1 A'). *)

let CMPF_DET_DERIV = prove
 (`!(A:real->real^N^N) (B:real^N^N) t.
        ((\s. vectorize(A(drop s))) has_vector_derivative vectorize B) (at (lift t)) /\
        ~(det(A t) = &0)
        ==> ((\s. lift(det(A(drop s)))) has_vector_derivative
             lift(det(A t) * trace(matrix_inv(A t) ** B))) (at (lift t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\s. (A:real->real^N^N) (drop s)`; `B:real^N^N`; `lift t`]
    LRG_HAS_DERIVATIVE_DET_CURVE) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `cofactor((A:real->real^N^N) t) = det(A t) %% transp(matrix_inv(A t))`
  SUBST1_TAC THENL
   [MP_TAC(ISPEC `(A:real->real^N^N) t` MATRIX_INV_COFACTOR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[TRANSP_MATRIX_CMUL; TRANSP_TRANSP; MATRIX_CMUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; MATRIX_CMUL_LID];
    ALL_TAC] THEN
  REWRITE_TAC[trace; MATRIX_CMUL_COMPONENT; TRANSP_COMPONENT] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[matrix_mul; LAMBDA_BETA; GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The Jacobi matrix of N Jacobi fields in a parallel frame: A' = B, B' = -R *)
(* A, and A^T B symmetric when all fields vanish at t0.                      *)
(* ========================================================================= *)

let CMPF_FMAT_LMUL = prove
 (`!(M:real^N^N) (a:num->real->real^N) t.
        cmp_fmat (\j s. M ** a j s) t = M ** cmp_fmat a t`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[CART_EQ; cmp_fmat; LAMBDA_BETA; matrix_mul; matrix_vector_mul] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA]);;

let CMPF_FMAT_NEG = prove
 (`!(a:num->real->real^N) t. cmp_fmat (\j s. --(a j s)) t = --(cmp_fmat a t)`,
  SIMP_TAC[CART_EQ; cmp_fmat; LAMBDA_BETA; MATRIX_NEG_COMPONENT;
           VECTOR_NEG_COMPONENT]);;

let CMPF_JACOBI_MATRIX = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (E:num->real->real^N)
    (Y:num->real->real^N) t0.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\ cmp_pframe atlas g gamma J E /\
        (!j. 1 <= j /\ j <= dimindex(:N) ==> mfd_jacobi atlas g gamma J (Y j)) /\
        t0 IN J /\ (!j. 1 <= j /\ j <= dimindex(:N) ==> Y j t0 = vec 0)
        ==> !t. t IN J
                ==> ((\s. vectorize(cmp_fmat (\j. cmp_fcoord g gamma E (Y j)) (drop s)))
                     has_vector_derivative
                     vectorize(cmp_fmat (\j. cmp_fcoord g gamma E
                                               (mfd_covd atlas g gamma (Y j))) t))
                    (at (lift t)) /\
                    ((\s. vectorize(cmp_fmat (\j. cmp_fcoord g gamma E
                                                    (mfd_covd atlas g gamma (Y j)))
                                             (drop s)))
                     has_vector_derivative
                     vectorize(--(cmp_rmat atlas g gamma E t **
                                  cmp_fmat (\j. cmp_fcoord g gamma E (Y j)) t)))
                    (at (lift t)) /\
                    transp(cmp_fmat (\j. cmp_fcoord g gamma E (Y j)) t) **
                    cmp_fmat (\j. cmp_fcoord g gamma E (mfd_covd atlas g gamma (Y j))) t =
                    transp(cmp_fmat (\j. cmp_fcoord g gamma E
                                           (mfd_covd atlas g gamma (Y j))) t) **
                    cmp_fmat (\j. cmp_fcoord g gamma E (Y j)) t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!j t. 1 <= j /\ j <= dimindex(:N) /\ t IN J
          ==> ((\s. cmp_fcoord g gamma E ((Y:num->real->real^N) j) (drop s))
               has_vector_derivative
               cmp_fcoord g gamma E (mfd_covd atlas (g:A->real^N^N) (gamma:real->A) (Y j)) t)
              (at (lift t)) /\
              ((\s. cmp_fcoord g gamma E (mfd_covd atlas g gamma (Y j)) (drop s))
               has_vector_derivative
               --(cmp_rmat atlas g gamma (E:num->real->real^N) t **
                  cmp_fcoord g gamma E (Y j) t)) (at (lift t))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CMPF_JACOBI_FCOORD THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `J:real->bool`] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`\j. cmp_fcoord (g:A->real^N^N) (gamma:real->A) (E:num->real->real^N)
                         ((Y:num->real->real^N) j)`;
                   `\j. cmp_fcoord (g:A->real^N^N) (gamma:real->A) (E:num->real->real^N)
                         (mfd_covd atlas g gamma ((Y:num->real->real^N) j))`;
                   `t:real`] CMPF_HAS_VD_FMAT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`\j. cmp_fcoord (g:A->real^N^N) (gamma:real->A) (E:num->real->real^N)
                         (mfd_covd atlas g gamma ((Y:num->real->real^N) j))`;
                   `\j s. --(cmp_rmat atlas (g:A->real^N^N) (gamma:real->A)
                              (E:num->real->real^N) s **
                             cmp_fcoord g gamma E ((Y:num->real->real^N) j) s)`;
                   `t:real`] CMPF_HAS_VD_FMAT) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM CMPF_FMAT_LMUL; GSYM CMPF_FMAT_NEG] THEN
    SIMP_TAC[CART_EQ; cmp_fmat; LAMBDA_BETA];
    MP_TAC(ISPECL [`\j. cmp_fcoord (g:A->real^N^N) (gamma:real->A) (E:num->real->real^N)
                         ((Y:num->real->real^N) j)`;
                   `\j. cmp_fcoord (g:A->real^N^N) (gamma:real->A) (E:num->real->real^N)
                         (mfd_covd atlas g gamma ((Y:num->real->real^N) j))`;
                   `cmp_rmat atlas (g:A->real^N^N) (gamma:real->A) (E:num->real->real^N)`;
                   `J:real->bool`; `t0:real`] CMPF_WRONSKIAN) THEN
    REWRITE_TAC[ETA_AX] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THENL
       [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`]
          GEOL_GEODESIC_BASIC) THEN ASM_SIMP_TAC[];
        X_GEN_TAC `s:real` THEN DISCH_TAC THEN MATCH_MP_TAC CMPF_RMAT_SYM THEN
        EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
        MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                              `J:real->bool`] THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `j:num` THEN STRIP_TAC THEN
        ASM_SIMP_TAC[cmp_fcoord; MATRIX_VECTOR_MUL_RZERO]];
      DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[]]]);;

(* Coordinates of the frame fields and of zero. *)

let CMPF_FCOORD_FRAME = prove
 (`!atlas (g:A->real^N^N) (gamma:real->A) J (E:num->real->real^N) j t.
        cmp_pframe atlas g gamma J E /\ t IN J /\ 1 <= j /\ j <= dimindex(:N)
        ==> cmp_fcoord g gamma E (E j) t = basis j`,
  REPEAT STRIP_TAC THEN SIMP_TAC[CART_EQ] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CMPF_FCOORD_COMPONENT; BASIS_COMPONENT] THEN
  UNDISCH_TAC `cmp_pframe atlas (g:A->real^N^N) (gamma:real->A) J (E:num->real->real^N)` THEN
  REWRITE_TAC[cmp_pframe] THEN DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `\M:real^N^N. M$i$j`) THEN
  ASM_SIMP_TAC[CMPF_FMAT_GRAM; MAT_COMPONENT] THEN
  MESON_TAC[]);;

let CMPF_FCOORD_ZERO = prove
 (`!(g:A->real^N^N) (gamma:real->A) (E:num->real->real^N) Y t.
        Y t = vec 0 ==> cmp_fcoord g gamma E Y t = vec 0`,
  SIMP_TAC[cmp_fcoord; MATRIX_VECTOR_MUL_RZERO]);;

let CMPF_FMAT_BASIS = prove
 (`cmp_fmat (\j s. basis j) t = mat 1:real^N^N`,
  SIMP_TAC[CART_EQ; cmp_fmat; LAMBDA_BETA; MAT_COMPONENT; BASIS_COMPONENT] THEN
  MESON_TAC[]);;

