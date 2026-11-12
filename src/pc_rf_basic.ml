(* ========================================================================= *)
(* Unit pc_rf_basic: Ricci flow basics and the model flows.  Ricci flows on  *)
(* manifolds, parabolic rescaling, time translation and restriction to       *)
(* subintervals, the round metric of the unit 3-sphere and its shrinking     *)
(* flow, and the shrinking round cylinder S^2 x R as a flow on real^3 minus  *)
(* the origin.                                                               *)
(*                                                                           *)
(* First the definitions.                                                    *)
(* ========================================================================= *)

needs "src/pc_mfd_riem.ml";;
needs "src/pc_mfd_examples.ml";;
needs "src/pc_lrg_scale.ml";;

prioritize_real();;
type_invention_error := true;;

(* The matrix of the Ricci form in preferred coordinates. *)

let mfd_ricci_matrix = new_definition
 `mfd_ricci_matrix (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (x:A) =
    (lambda i j. mfd_ricci atlas g x (basis i) (basis j)):real^N^N`;;

(* A Ricci flow on the open time interval (a,b) on a manifold with a smooth *)
(* atlas (needed: otherwise chart_at is a junk value at uncovered points): a *)
(* family of Riemannian metrics, jointly smooth in time and chart           *)
(* coordinates, whose entries in preferred coordinates satisfy              *)
(* d/dt g = -2 Ric.  (Chart Jacobians do not depend on time, so this is the *)
(* Ricci flow equation in every chart.)                                     *)

let ricci_flow_on = new_definition
 `ricci_flow_on (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
                (a:real) (b:real) (g:real->A->real^N^N) <=>
    smooth_manifold_atlas top atlas /\ a < b /\
    (!t. a < t /\ t < b ==> riemannian_metric atlas (g t)) /\
    (!c. c IN atlas
         ==> smooth_map_on (interval(lift a,lift b) PCROSS IMAGE (SND c) (FST c))
               (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                    (metric_local atlas c (g(drop(fstcart z))) (sndcart z)))) /\
    (!t x i j. a < t /\ t < b /\ x IN topspace top /\
               1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
               ==> ((\s. g s x$i$j) has_real_derivative
                    (--(&2) * mfd_ricci_matrix atlas (g t) x$i$j)) (atreal t))`;;

(* Smoothness up to the initial time: every chart representative extends    *)
(* smoothly past t = a.                                                      *)

let ricci_flow_from = new_definition
 `ricci_flow_from (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
                  (a:real) (b:real) (g:real->A->real^N^N) <=>
    ricci_flow_on (top,atlas) a b g /\
    riemannian_metric atlas (g a) /\
    !c. c IN atlas
        ==> ?e F. &0 < e /\
                  smooth_map_on
                    (interval(lift(a - e),lift b) PCROSS IMAGE (SND c) (FST c)) F /\
                  !t y. a <= t /\ t < b /\ y IN IMAGE (SND c) (FST c)
                        ==> F(pastecart (lift t) y) =
                            (vectorize:real^N^N->real^(N,N)finite_prod)
                            (metric_local atlas c (g t) y)`;;

(* The round metric of the unit 3-sphere in preferred (stereographic)       *)
(* coordinates; both stereographic charts give the same formula.            *)

let round3_metric = new_definition
 `round3_metric (x:real^4) =
    (&4 / (&1 + norm(SND(chart_at sphere3_atlas x) x) pow 2) pow 2) %% (mat 1:real^3^3)`;;

(* The shrinking round cylinder S^2 x R as real^3 minus the origin: the S^2  *)
(* factor has scalar curvature 1/(1-t), the line factor stays fixed.         *)

let cylinder_flow = new_definition
 `cylinder_flow (t:real) (y:real^3) =
    (&2 / norm y pow 2) %%
    ((&1 - t) %% (mat 1:real^3^3) + (t / norm y pow 2) %% ((lambda i j. y$i * y$j):real^3^3))`;;


(* ========================================================================= *)
(* General facts (matrix entries, scale invariance of Ric on a manifold,     *)
(* affine reparametrization of time in smooth families) and the invariances  *)
(* of the Ricci flow: subintervals, time translation, parabolic rescaling.   *)
(* ========================================================================= *)

let RFB_BASIS_DOT_MATRIX = prove
 (`!(A:real^N^N) i j.
        1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
        ==> basis i dot (A ** basis j) = A$i$j`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MATRIX_VECTOR_MUL_BASIS; DOT_BASIS] THEN
  ASM_SIMP_TAC[column; LAMBDA_BETA]);;

let RFB_MFD_RICCI_MATRIX_COMPONENT = prove
 (`!atlas (g:A->real^N^N) x i j.
        1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
        ==> mfd_ricci_matrix atlas g x$i$j =
            mfd_ricci atlas g x (basis i) (basis j)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[mfd_ricci_matrix; LAMBDA_BETA]);;

(* Ricci curvature on a manifold is invariant under constant rescaling. *)

let RFB_MFD_RICCI_CMUL = prove
 (`!top atlas (g:A->real^N^N) k x.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        &0 < k /\ x IN topspace top
        ==> mfd_ricci atlas (\x. k %% g x) x = mfd_ricci atlas g x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mfd_ricci; METRIC_LOCAL_CMUL; FUN_EQ_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC LRICCI_SCALE THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                    (FST(chart_at atlas x))` THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[riemannian_metric]) THEN ASM_SIMP_TAC[]);;

(* Projections of a product are smooth, and so are their composites. *)

let RFB_SMOOTH_FSTCART = prove
 (`!S. open S ==> smooth_map_on S (\z:real^(M,N)finite_sum. fstcart z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smooth_map_on] THEN GEN_TAC THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN THEN
  ASM_REWRITE_TAC[LINEAR_FSTCART; ETA_AX]);;

let RFB_SMOOTH_SNDCART = prove
 (`!S. open S ==> smooth_map_on S (\z:real^(M,N)finite_sum. sndcart z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smooth_map_on] THEN GEN_TAC THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN THEN
  ASM_REWRITE_TAC[LINEAR_SNDCART; ETA_AX]);;

let RFB_SMOOTH_SNDCART_COMPOSE = prove
 (`!S Tn (f:real^N->real^P).
        open S /\ open Tn /\ (!z:real^(M,N)finite_sum. z IN S ==> sndcart z IN Tn) /\
        smooth_map_on Tn f
        ==> smooth_map_on S (\z. f(sndcart z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z:real^(M,N)finite_sum. (f:real^N->real^P)(sndcart z)) =
                f o (\z. sndcart z)` SUBST1_TAC THENL
   [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `Tn:real^N->bool` THEN
  ASM_SIMP_TAC[RFB_SMOOTH_SNDCART; SUBSET; FORALL_IN_IMAGE]);;

let RFB_SMOOTH_LIFT_TIME = prove
 (`!S. open S ==> smooth_map_on S (\z:real^(1,N)finite_sum. lift(drop(fstcart z)))`,
  SIMP_TAC[LIFT_DROP; RFB_SMOOTH_FSTCART]);;

(* An affine change of the time variable in a smooth family on a product.  *)

let RFB_SMOOTH_TIME_AFFINE = prove
 (`!(Fm:real^(1,N)finite_sum->real^M) S a b a' b' p r.
        open S /\ smooth_map_on (interval(lift a,lift b) PCROSS S) Fm /\
        (!t. a' < t /\ t < b' ==> a < p * t + r /\ p * t + r < b)
        ==> smooth_map_on (interval(lift a',lift b') PCROSS S)
              (\z. Fm(pastecart (lift(p * drop(fstcart z) + r)) (sndcart z)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z. (Fm:real^(1,N)finite_sum->real^M)
          (pastecart (lift(p * drop(fstcart z) + r)) (sndcart z))) =
    Fm o (\z. pastecart (lift(p * drop(fstcart z) + r)) (sndcart z))`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `interval(lift a,lift b) PCROSS (S:real^N->bool)` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; PASTECART_IN_PCROSS] THEN
    SIMP_TAC[IN_INTERVAL_1; LIFT_DROP] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`interval(lift a',lift b') PCROSS (S:real^N->bool)`;
                   `\z:real^(1,N)finite_sum. lift(p * drop(fstcart z))`;
                   `\z:real^(1,N)finite_sum. lift r`] SMOOTH_MAP_ON_LIFT_ADD) THEN
    REWRITE_TAC[LIFT_DROP; SMOOTH_MAP_ON_CONST] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN
    MP_TAC(ISPECL [`interval(lift a',lift b') PCROSS (S:real^N->bool)`; `p:real`;
                   `\z:real^(1,N)finite_sum. fstcart z`] SMOOTH_MAP_ON_LIFT_CMUL) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN
    REWRITE_TAC[smooth_map_on] THEN GEN_TAC THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; LINEAR_FSTCART; ETA_AX];
    REWRITE_TAC[smooth_map_on] THEN GEN_TAC THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; LINEAR_SNDCART; ETA_AX]]);;

(* ------------------------------------------------------------------------- *)
(* Restriction to a subinterval, time translation, parabolic rescaling.      *)
(* ------------------------------------------------------------------------- *)

let RICCI_FLOW_SUBINTERVAL = prove
 (`!top atlas a b a' b' (g:real->A->real^N^N).
        ricci_flow_on (top,atlas) a b g /\ a <= a' /\ a' < b' /\ b' <= b
        ==> ricci_flow_on (top,atlas) a' b' g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `interval(lift a,lift b) PCROSS
                IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN
    REWRITE_TAC[SUBSET_REFL; SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let RFB_ATLAS_IMAGE_OPEN = prove
 (`!top atlas (c:(A->bool)#(A->real^N)).
        smooth_manifold_atlas top atlas /\ c IN atlas
        ==> open (IMAGE (SND c) (FST c))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
                SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[PAIR] THEN SIMP_TAC[]);;

let RICCI_FLOW_TRANSLATE = prove
 (`!top atlas a b (g:real->A->real^N^N) s.
        ricci_flow_on (top,atlas) a b g
        ==> ricci_flow_on (top,atlas) (a + s) (b + s) (\t. g (t - s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[REAL_LT_RADD] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    MP_TAC(ISPECL
     [`\z:real^(1,N)finite_sum.
         (vectorize:real^N^N->real^(N,N)finite_prod)
         (metric_local atlas (c:(A->bool)#(A->real^N))
            ((g:real->A->real^N^N) (drop(fstcart z))) (sndcart z))`;
      `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
      `a:real`; `b:real`; `a + s:real`; `b + s:real`; `&1`; `--s:real`]
     RFB_SMOOTH_TIME_AFFINE) THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP;
                REAL_MUL_LID; GSYM real_sub] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[RFB_ATLAS_IMAGE_OPEN]; REAL_ARITH_TAC];
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `i:num`; `j:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`t - s:real`; `x:A`; `i:num`; `j:num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`\u:real. u - s`; `\u:real. (g:real->A->real^N^N) u x$i$j`;
                   `&1 - &0`;
                   `--(&2) * mfd_ricci_matrix atlas ((g:real->A->real^N^N) (t - s))
                                              (x:A)$i$j`;
                   `t:real`] REAL_DIFF_CHAIN_ATREAL) THEN
    ASM_REWRITE_TAC[o_DEF] THEN ANTS_TAC THENL
     [REWRITE_TAC[REAL_DIFF_CONV `((\u. u - s) has_real_derivative f') (atreal t)`];
      REWRITE_TAC[REAL_SUB_RZERO; REAL_MUL_RID]]]);;

let RFB_RESCALE_TIME = prove
 (`!a b q t. &0 < q /\ q * a < t /\ t < q * b ==> a < t / q /\ t / q < b`,
  SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC);;

let RICCI_FLOW_RESCALE = prove
 (`!top atlas a b (g:real->A->real^N^N) q.
        ricci_flow_on (top,atlas) a b g /\ &0 < q
        ==> ricci_flow_on (top,atlas) (q * a) (q * b) (\t x. q %% g (t / q) x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_LT_LMUL] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN
    ASM_REWRITE_TAC[ETA_AX] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[RFB_RESCALE_TIME];
    X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    REWRITE_TAC[METRIC_LOCAL_CMUL; VECTORIZE_CMUL; ETA_AX] THEN
    SUBGOAL_THEN `open(IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))`
    ASSUME_TAC THENL [ASM_MESON_TAC[RFB_ATLAS_IMAGE_OPEN]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN
    SUBGOAL_THEN `!z:real^(1,N)finite_sum. drop(fstcart z) / q = inv q * drop(fstcart z)`
    (fun th -> ONCE_REWRITE_TAC[th]) THENL
     [REWRITE_TAC[real_div; REAL_MUL_SYM]; ALL_TAC] THEN
    MP_TAC(ISPECL
     [`\z:real^(1,N)finite_sum.
         (vectorize:real^N^N->real^(N,N)finite_prod)
         (metric_local atlas (c:(A->bool)#(A->real^N))
            ((g:real->A->real^N^N) (drop(fstcart z))) (sndcart z))`;
      `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
      `a:real`; `b:real`; `q * a:real`; `q * b:real`; `inv q:real`; `&0`]
     RFB_SMOOTH_TIME_AFFINE) THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; REAL_ADD_RID] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`a:real`; `b:real`; `q:real`; `t:real`] RFB_RESCALE_TIME) THEN
    ASM_REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `i:num`; `j:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `a < t / q /\ t / q < b` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[RFB_RESCALE_TIME]; ALL_TAC] THEN
    SUBGOAL_THEN
     `mfd_ricci_matrix atlas (\x. q %% (g:real->A->real^N^N) (t / q) x) (x:A)$i$j =
      mfd_ricci_matrix atlas (g (t / q)) x$i$j`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[RFB_MFD_RICCI_MATRIX_COMPONENT] THEN
      AP_THM_TAC THEN AP_THM_TAC THEN MATCH_MP_TAC RFB_MFD_RICCI_CMUL THEN
      EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`t / q:real`; `x:A`; `i:num`; `j:num`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\u:real. u / q`; `\u:real. (g:real->A->real^N^N) u x$i$j`;
                   `&1 / q`;
                   `--(&2) * mfd_ricci_matrix atlas ((g:real->A->real^N^N) (t / q))
                                              (x:A)$i$j`;
                   `t:real`] REAL_DIFF_CHAIN_ATREAL) THEN
    ASM_REWRITE_TAC[o_DEF] THEN ANTS_TAC THENL
     [REWRITE_TAC[REAL_DIFF_CONV `((\u. u / q) has_real_derivative f') (atreal t)`];
      DISCH_TAC] THEN
    REWRITE_TAC[MATRIX_CMUL_COMPONENT] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `q:real` o
                  MATCH_MP HAS_REAL_DERIVATIVE_LMUL_ATREAL) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM];
      UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD]]);;

(* ========================================================================= *)
(* The round metric of the unit 3-sphere.  In both stereographic charts the  *)
(* representative is 4/(1+|y|^2)^2 times the identity (the transition map is *)
(* the inversion y/|y|^2, whose derivative is conformal with factor          *)
(* 1/|y|^2); hence Ric = 2 g, sectional curvature 1, and (1 - 4t) g is       *)
(* a Ricci flow on t < 1/4.                                                  *)
(* ========================================================================= *)

(* Matrices are determined by their bilinear forms; congruences by a linear *)
(* map in terms of dot products.                                             *)

let RFB_MATRIX_EQ_DOT = prove
 (`!(A:real^N^N) B. (!u v. u dot (A ** v) = u dot (B ** v)) ==> A = B`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MATRIX_EQ] THEN X_GEN_TAC `v:real^N` THEN
  ONCE_REWRITE_TAC[GSYM VECTOR_EQ_LDOT] THEN ASM_REWRITE_TAC[]);;

let RFB_CONGRUENCE_DOT = prove
 (`!(f:real^N->real^N) (M:real^N^N) u v.
        linear f
        ==> u dot ((transp(matrix f) ** M ** matrix f) ** v) =
            f u dot (M ** f v)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
  ASM_SIMP_TAC[MATRIX_WORKS]);;

(* The derivative of the inversion y -> y/|y|^2 away from the origin. *)

let RFB_INVERSION_HAS_DERIVATIVE = prove
 (`!a:real^N.
        ~(a = vec 0)
        ==> ((\z. inv(norm z pow 2) % z) has_derivative
             (\h. inv(norm a pow 2) % h -
                  (&2 * (a dot h) / (norm a pow 2) pow 2) % a)) (at a)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(norm(a:real^N) pow 2 = &0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_EQ_0; NORM_EQ_0] THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`\z:real^N. inv(norm z pow 2)`;
                 `\h:real^N. --inv((norm(a:real^N) pow 2) pow 2) * (&2 * (a dot h))`;
                 `\z:real^N. z`; `\h:real^N. h`; `a:real^N`]
                HAS_DERIVATIVE_MUL_AT) THEN
  REWRITE_TAC[HAS_DERIVATIVE_ID] THEN ANTS_TAC THENL
   [MP_TAC(ISPECL [`inv:real->real`; `--inv((norm(a:real^N) pow 2) pow 2)`;
                   `\x:real^N. lift(norm x pow 2)`;
                   `\h:real^N. &2 % lift(a dot h)`; `a:real^N`]
                  LRG_HAS_DERIVATIVE_REAL_COMPOSE) THEN
    ASM_SIMP_TAC[LIFT_DROP; HAS_DERIVATIVE_SQNORM_AT; HAS_REAL_DERIVATIVE_INV_BASIC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM] THEN REWRITE_TAC[LIFT_CMUL; VECTOR_MUL_ASSOC];
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `h:real^N` THEN
    REWRITE_TAC[VECTOR_ARITH `x + y:real^N = x - z <=> y = --z`] THEN
    REWRITE_TAC[GSYM VECTOR_MUL_LNEG] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `~(norm(a:real^N) pow 2 = &0)` THEN CONV_TAC REAL_FIELD]);;

(* The two stereographic charts. *)

let RFB_SPHERE3_ATLAS_CASES = prove
 (`!c. c IN sphere3_atlas <=>
       c = (sphere(vec 0:real^4,&1) DELETE basis 4,stereo3_n) \/
       c = (sphere(vec 0:real^4,&1) DELETE --(basis 4),stereo3_s)`,
  REWRITE_TAC[sphere3_atlas; IN_INSERT; NOT_IN_EMPTY]);;

let RFB_SPHERE3_CHART_FACTS = prove
 (`!c y. c IN sphere3_atlas
         ==> IMAGE (SND c) (FST c) = (:real^3) /\
             chart_inv c y IN FST c /\ SND c (chart_inv c y) = y /\
             FST c SUBSET sphere(vec 0:real^4,&1)`,
  REWRITE_TAC[RFB_SPHERE3_ATLAS_CASES] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[FST; SND; STEX_SPHERE3_CHART_INV; STEX_STEREO3_HOMEOMORPHISMS;
                  STEX_STEREO3_N_INV_IN; STEX_STEREO3_N_RIGHT;
                  STEX_STEREO3_S_INV_IN; STEX_STEREO3_S_RIGHT; DELETE_SUBSET]);;

let RFB_SPHERE3_TRANS_NS = prove
 (`!x. x IN sphere(vec 0:real^4,&1) DELETE basis 4 /\
       x IN sphere(vec 0:real^4,&1) DELETE --(basis 4)
       ==> ~(stereo3_n x = vec 0) /\
           stereo3_s x = inv(norm(stereo3_n x) pow 2) % stereo3_n x`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(stereo3_n x = vec 0)` ASSUME_TAC THENL
   [MP_TAC(CONJUNCT1 STEX_STEREO3_ZERO) THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^4`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN ASM SET_TAC[];
    ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `sphere3_atlas`;
                 `sphere(vec 0:real^4,&1) DELETE basis 4`; `stereo3_n`;
                 `sphere(vec 0:real^4,&1) DELETE --(basis 4)`; `stereo3_s`;
                 `x:real^4`] CHART_TRANS_AT) THEN
  ASM_REWRITE_TAC[SPHERE3_ATLAS; RFB_SPHERE3_ATLAS_CASES] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[STEX_SPHERE3_CHART_TRANS]);;

let RFB_SPHERE3_TRANS_SN = prove
 (`!x. x IN sphere(vec 0:real^4,&1) DELETE --(basis 4) /\
       x IN sphere(vec 0:real^4,&1) DELETE basis 4
       ==> ~(stereo3_s x = vec 0) /\
           stereo3_n x = inv(norm(stereo3_s x) pow 2) % stereo3_s x`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(stereo3_s x = vec 0)` ASSUME_TAC THENL
   [MP_TAC(CONJUNCT2 STEX_STEREO3_ZERO) THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^4`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN ASM SET_TAC[];
    ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `sphere3_atlas`;
                 `sphere(vec 0:real^4,&1) DELETE --(basis 4)`; `stereo3_s`;
                 `sphere(vec 0:real^4,&1) DELETE basis 4`; `stereo3_n`;
                 `x:real^4`] CHART_TRANS_AT) THEN
  ASM_REWRITE_TAC[SPHERE3_ATLAS; RFB_SPHERE3_ATLAS_CASES] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[STEX_SPHERE3_CHART_TRANS]);;

let RFB_SPHERE3_TRANS = prove
 (`!c1 c2 x.
        c1 IN sphere3_atlas /\ c2 IN sphere3_atlas /\ ~(c1 = c2) /\
        x IN FST c1 /\ x IN FST c2
        ==> ~(SND c1 x = vec 0) /\
            SND c2 x = inv(norm(SND c1 x) pow 2) % SND c1 x /\
            (!z. ~(z = vec 0) ==> chart_trans c1 c2 z = inv(norm z pow 2) % z)`,
  REWRITE_TAC[RFB_SPHERE3_ATLAS_CASES] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN REWRITE_TAC[FST; SND] THEN
  DISCH_TAC THEN
  ASM_MESON_TAC[STEX_SPHERE3_CHART_TRANS; RFB_SPHERE3_TRANS_NS;
                RFB_SPHERE3_TRANS_SN]);;

(* The round metric is invariant under the inversion: congruence by the    *)
(* derivative of y/|y|^2 turns 4/(1+|y'|^2)^2 delta at y' = y/|y|^2 into   *)
(* 4/(1+|y|^2)^2 delta at y.                                                *)

let RFB_INVERSION_ROUND = prove
 (`!y:real^3.
        ~(y = vec 0)
        ==> transp(matrix(\h. inv(norm y pow 2) % h -
                              (&2 * (y dot h) / (norm y pow 2) pow 2) % y)) **
            ((&4 / (&1 + norm(inv(norm y pow 2) % y) pow 2) pow 2) %% mat 1) **
            matrix(\h. inv(norm y pow 2) % h -
                       (&2 * (y dot h) / (norm y pow 2) pow 2) % y) =
            (&4 / (&1 + norm y pow 2) pow 2) %% mat 1`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RFB_MATRIX_EQ_DOT THEN
  MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN
  W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) RFB_CONGRUENCE_DOT (lhand w))) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC LRG_HAS_DERIVATIVE_IMP_LINEAR THEN
    MAP_EVERY EXISTS_TAC [`\z:real^3. inv(norm z pow 2) % z`; `at(y:real^3)`] THEN
    ASM_SIMP_TAC[RFB_INVERSION_HAS_DERIVATIVE];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `&0 < (y:real^3) dot y` MP_TAC THENL
   [ASM_REWRITE_TAC[DOT_POS_LT]; ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID; DOT_RMUL; DOT_LMUL;
              DOT_LSUB; DOT_RSUB; NORM_POW_2] THEN
  REWRITE_TAC[DOT_SYM] THEN CONV_TAC REAL_FIELD);;

let RFB_SPHERE3_PAIR = prove
 (`!c1 c2 x.
        c1 IN sphere3_atlas /\ c2 IN sphere3_atlas /\ x IN FST c1 /\ x IN FST c2
        ==> transp(matrix(chart_jac c1 c2 x)) **
            ((&4 / (&1 + norm(SND c2 x) pow 2) pow 2) %% mat 1) **
            matrix(chart_jac c1 c2 x) =
            (&4 / (&1 + norm(SND c1 x) pow 2) pow 2) %% mat 1`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `c1:(real^4->bool)#(real^4->real^3) = c2` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `sphere3_atlas`;
                   `FST(c1:(real^4->bool)#(real^4->real^3))`;
                   `SND(c1:(real^4->bool)#(real^4->real^3))`; `x:real^4`]
                  CHART_JAC_SELF) THEN
    ASM_REWRITE_TAC[PAIR; SPHERE3_ATLAS] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[MATRIX_ID; TRANSP_MAT; MATRIX_MUL_LID; MATRIX_MUL_RID];
    MP_TAC(SPECL [`c1:(real^4->bool)#(real^4->real^3)`;
                  `c2:(real^4->bool)#(real^4->real^3)`; `x:real^4`]
                 RFB_SPHERE3_TRANS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `chart_jac (c1:(real^4->bool)#(real^4->real^3)) c2 (x:real^4) =
      (\h. inv(norm(SND c1 x) pow 2) % h -
           (&2 * (SND c1 x dot h) / (norm(SND c1 x) pow 2) pow 2) % SND c1 x)`
    SUBST1_TAC THENL
     [REWRITE_TAC[chart_jac] THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `frechet_derivative (\z:real^3. inv(norm z pow 2) % z)
                    (at(SND (c1:(real^4->bool)#(real^4->real^3)) x))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
        EXISTS_TAC `(:real^3) DELETE vec 0` THEN
        ASM_SIMP_TAC[IN_DELETE; IN_UNIV; LRG_CYL_OPEN];
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
        ASM_SIMP_TAC[RFB_INVERSION_HAS_DERIVATIVE]];
      ASM_SIMP_TAC[RFB_INVERSION_ROUND]]]);;

(* The chart representatives of the round metric. *)

let RFB_ROUND3_LOCAL = prove
 (`!c y. c IN sphere3_atlas
         ==> metric_local sphere3_atlas c round3_metric y =
             (&4 / (&1 + norm y pow 2) pow 2) %% mat 1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:(real^4->bool)#(real^4->real^3)`; `y:real^3`]
               RFB_SPHERE3_CHART_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `sphere3_atlas`;
                 `chart_inv (c:(real^4->bool)#(real^4->real^3)) (y:real^3)`]
                CHART_AT) THEN
  REWRITE_TAC[SPHERE3_ATLAS; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
  REWRITE_TAC[metric_local; round3_metric] THEN
  MP_TAC(SPECL [`c:(real^4->bool)#(real^4->real^3)`;
                `chart_at sphere3_atlas
                   (chart_inv (c:(real^4->bool)#(real^4->real^3)) (y:real^3))`;
                `chart_inv (c:(real^4->bool)#(real^4->real^3)) (y:real^3)`]
               RFB_SPHERE3_PAIR) THEN
  ASM_REWRITE_TAC[]);;

let RFB_ROUND3_LOCAL_FUN = prove
 (`!c. c IN sphere3_atlas
       ==> metric_local sphere3_atlas c round3_metric =
           (\y. (&4 / (&1 + norm y pow 2) pow 2) %% mat 1)`,
  SIMP_TAC[FUN_EQ_THM; RFB_ROUND3_LOCAL]);;

let RFB_SPHERE3_IMAGE = prove
 (`!c. c IN sphere3_atlas ==> IMAGE (SND c) (FST c) = (:real^3)`,
  MESON_TAC[RFB_SPHERE3_CHART_FACTS]);;

(* ------------------------------------------------------------------------- *)
(* The main results on the round 3-sphere.                                   *)
(* ------------------------------------------------------------------------- *)

let ROUND3_METRIC = prove
 (`riemannian_metric sphere3_atlas round3_metric`,
  REWRITE_TAC[riemannian_metric] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[RFB_ROUND3_LOCAL_FUN; RFB_SPHERE3_IMAGE; LRG_SPH_METRIC]);;

let ROUND3_RICCI = prove
 (`!x u v. x IN sphere(vec 0:real^4,&1)
           ==> mfd_ricci sphere3_atlas round3_metric x u v =
               &2 * (u dot (round3_metric x ** v))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `sphere3_atlas`;
                 `x:real^4`] CHART_AT) THEN
  ASM_REWRITE_TAC[SPHERE3_ATLAS; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[mfd_ricci; RFB_ROUND3_LOCAL_FUN; LRICCI_ROUND_SPHERE_3] THEN
  REWRITE_TAC[round3_metric; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID; DOT_RMUL] THEN
  REAL_ARITH_TAC);;

let ROUND3_SECTIONAL = prove
 (`!x u v. x IN sphere(vec 0:real^4,&1) /\ ~collinear {vec 0,u,v}
           ==> mfd_sectional sphere3_atlas round3_metric x u v = &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `sphere3_atlas`;
                 `x:real^4`] CHART_AT) THEN
  ASM_REWRITE_TAC[SPHERE3_ATLAS; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[mfd_sectional; RFB_ROUND3_LOCAL_FUN; LRG_SPH_SECTIONAL]);;

let RFB_SPHERE3_TIME_DERIV = prove
 (`!c t. ((\s. (&1 - &4 * s) * c) has_real_derivative (--(&4) * c)) (atreal t)`,
  REPEAT GEN_TAC THEN
  MP_TAC(REAL_DIFF_CONV `((\s. (&1 - &4 * s) * (c:real)) has_real_derivative f')
                         (atreal t)`) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let RFB_SPHERE3_FLOW_SMOOTH = prove
 (`!S. open S
       ==> smooth_map_on S
             (\z:real^(1,3)finite_sum.
                (&1 - &4 * drop(fstcart z)) %
                (&4 / (&1 + norm(sndcart z) pow 2) pow 2) %
                (vectorize:real^3^3->real^(3,3)finite_prod) (mat 1))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^(1,3)finite_sum->bool`;
                 `\z:real^(1,3)finite_sum. lift(&1 - &4 * drop(fstcart z))`;
                 `\z:real^(1,3)finite_sum.
                    (&4 / (&1 + norm(sndcart z) pow 2) pow 2) %
                    (vectorize:real^3^3->real^(3,3)finite_prod) (mat 1)`]
                SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`S:real^(1,3)finite_sum->bool`;
                   `\z:real^(1,3)finite_sum. lift(&1)`;
                   `\z:real^(1,3)finite_sum. lift(&4 * drop(fstcart z))`]
                  SMOOTH_MAP_ON_LIFT_SUB) THEN
    REWRITE_TAC[LIFT_DROP; SMOOTH_MAP_ON_CONST] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`S:real^(1,3)finite_sum->bool`; `&4`;
                   `\z:real^(1,3)finite_sum. fstcart z`] SMOOTH_MAP_ON_LIFT_CMUL) THEN
    ASM_SIMP_TAC[RFB_SMOOTH_FSTCART];
    MP_TAC(ISPECL [`S:real^(1,3)finite_sum->bool`;
                   `\z:real^(1,3)finite_sum.
                      lift(&4 / (&1 + norm(sndcart z) pow 2) pow 2)`;
                   `\z:real^(1,3)finite_sum.
                      (vectorize:real^3^3->real^(3,3)finite_prod) (mat 1)`]
                  SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
    ASM_REWRITE_TAC[LIFT_DROP; SMOOTH_MAP_ON_CONST] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`S:real^(1,3)finite_sum->bool`; `(:real^3)`;
                   `\x:real^3. lift(&4 / (&1 + norm x pow 2) pow 2)`]
                  RFB_SMOOTH_SNDCART_COMPOSE) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; LRG_SPH_SMOOTH_C]]);;

let SHRINKING_SPHERE3_FLOW = prove
 (`!a. a < &1 / &4
       ==> ricci_flow_on (subtopology euclidean (sphere(vec 0:real^4,&1)),
                          sphere3_atlas) a (&1 / &4)
                         (\t x. (&1 - &4 * t) %% round3_metric x)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ricci_flow_on; SPHERE3_ATLAS; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN
    REWRITE_TAC[ETA_AX; ROUND3_METRIC] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `c:(real^4->bool)#(real^4->real^3)` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[METRIC_LOCAL_CMUL; ETA_AX; RFB_ROUND3_LOCAL; RFB_SPHERE3_IMAGE;
                 VECTORIZE_CMUL] THEN
    MATCH_MP_TAC RFB_SPHERE3_FLOW_SMOOTH THEN
    SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV];
    MAP_EVERY X_GEN_TAC [`t:real`; `x:real^4`; `i:num`; `j:num`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[RFB_MFD_RICCI_MATRIX_COMPONENT] THEN
    SUBGOAL_THEN
     `mfd_ricci sphere3_atlas (\x. (&1 - &4 * t) %% round3_metric x) x =
      mfd_ricci sphere3_atlas round3_metric x`
    SUBST1_TAC THENL
     [MATCH_MP_TAC RFB_MFD_RICCI_CMUL THEN
      EXISTS_TAC `subtopology euclidean (sphere(vec 0:real^4,&1))` THEN
      ASM_REWRITE_TAC[SPHERE3_ATLAS; ROUND3_METRIC; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[ROUND3_RICCI; RFB_BASIS_DOT_MATRIX; MATRIX_CMUL_COMPONENT] THEN
    MP_TAC(SPECL [`round3_metric x$i$j`; `t:real`] RFB_SPHERE3_TIME_DERIV) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Metric fields (pointwise equality, constant multiples) and                *)
(* open subsets of real^N with the identity chart: there the chart          *)
(* representative is the metric itself, so Ricci and scalar curvature on the *)
(* manifold are those of the local theory.                                   *)
(* ========================================================================= *)

let RFB_METRIC_FIELD_EQ = prove
 (`!U (G:real^N->real^N^N) G'.
        metric_field U G /\ (!z. z IN U ==> G' z = G z) ==> metric_field U G'`,
  REWRITE_TAC[metric_field] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `(vectorize:real^N^N->real^(N,N)finite_prod) o (G:real^N->real^N^N)` THEN
    ASM_SIMP_TAC[o_THM];
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[]]);;

let RFB_METRIC_FIELD_CMUL = prove
 (`!U (G:real^N->real^N^N) k.
        metric_field U G /\ &0 < k ==> metric_field U (\z. k %% G z)`,
  REWRITE_TAC[metric_field] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN
     `(vectorize:real^N^N->real^(N,N)finite_prod) o (\z. k %% (G:real^N->real^N^N) z) =
      (\z. k % (vectorize o G) z)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; VECTORIZE_CMUL];
      MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[ETA_AX]];
    ASM_SIMP_TAC[TRANSP_MATRIX_CMUL];
    REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[]]);;

(* The identity chart of an open set. *)

let RFB_OPEN_SET_CHART_AT = prove
 (`!U (x:real^N). x IN U ==> chart_at (open_set_atlas U) x = (U,(\x. x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[chart_at; open_set_atlas; IN_SING] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ; FST] THEN ASM_MESON_TAC[]);;

let RFB_OPEN_SET_ATLAS_CASES = prove
 (`!U (c:(real^N->bool)#(real^N->real^N)).
        c IN open_set_atlas U <=> c = (U,(\x. x))`,
  REWRITE_TAC[open_set_atlas; IN_SING]);;

let RFB_OPEN_SET_METRIC_LOCAL = prove
 (`!U (g:real^N->real^N^N) z.
        open U /\ z IN U
        ==> metric_local (open_set_atlas U) (U,(\x. x)) g z = g z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (U:real^N->bool)`; `open_set_atlas (U:real^N->bool)`;
                 `U:real^N->bool`; `\x:real^N. x`] CHART_INV) THEN
  ASM_SIMP_TAC[OPEN_SET_ATLAS; RFB_OPEN_SET_ATLAS_CASES] THEN
  DISCH_THEN(MP_TAC o SPEC `z:real^N` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[metric_local] THEN ASM_SIMP_TAC[RFB_OPEN_SET_CHART_AT] THEN
  MP_TAC(ISPECL [`subtopology euclidean (U:real^N->bool)`; `open_set_atlas (U:real^N->bool)`;
                 `U:real^N->bool`; `\x:real^N. x`; `z:real^N`] CHART_JAC_SELF) THEN
  ASM_SIMP_TAC[OPEN_SET_ATLAS; RFB_OPEN_SET_ATLAS_CASES] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MATRIX_ID; TRANSP_MAT; MATRIX_MUL_LID; MATRIX_MUL_RID]);;

let RFB_OPEN_SET_RIEMANNIAN = prove
 (`!U (g:real^N->real^N^N).
        open U /\ metric_field U g ==> riemannian_metric (open_set_atlas U) g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[riemannian_metric; RFB_OPEN_SET_ATLAS_CASES] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[FST; SND; IMAGE_ID] THEN
  MATCH_MP_TAC RFB_METRIC_FIELD_EQ THEN EXISTS_TAC `g:real^N->real^N^N` THEN
  ASM_SIMP_TAC[RFB_OPEN_SET_METRIC_LOCAL]);;

let RFB_OPEN_SET_MFD_RICCI = prove
 (`!U (g:real^N->real^N^N) x.
        open U /\ x IN U ==> mfd_ricci (open_set_atlas U) g x = lricci g x`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[mfd_ricci; RFB_OPEN_SET_CHART_AT] THEN
  REWRITE_TAC[FUN_EQ_THM; SND] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC LRICCI_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_SIMP_TAC[RFB_OPEN_SET_METRIC_LOCAL]);;

let RFB_OPEN_SET_MFD_SCALAR = prove
 (`!U (g:real^N->real^N^N) x.
        open U /\ x IN U ==> mfd_scalar (open_set_atlas U) g x = lscalar g x`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[mfd_scalar; RFB_OPEN_SET_CHART_AT] THEN
  REWRITE_TAC[SND] THEN
  MATCH_MP_TAC LSCALAR_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_SIMP_TAC[RFB_OPEN_SET_METRIC_LOCAL]);;

(* ========================================================================= *)
(* The shrinking round cylinder.  On real^3 minus the origin,                *)
(* cylinder_flow t = (1 - t) h^* g0 with g0 = (2/|z|^2) delta and h the      *)
(* radial power map y -> (|y|^2)^e y, where (2e+1)^2 (1-t) = 1 (so h is      *)
(* y -> |y|^(alpha-1) y with alpha = 1/sqrt(1-t)).  Hence Ric(g(t)) is the   *)
(* pullback of Ric(g0), equal to Ric(g0) by the explicit formula, and the    *)
(* scalar curvature is 1/(1-t).                                              *)
(* ========================================================================= *)

(* The radial power maps. *)

let RFB_PW_POS = prove
 (`!e y:real^N. ~(y = vec 0) ==> &0 < (norm y pow 2) rpow e`,
  SIMP_TAC[RPOW_POS_LT; LRG_CYL_POS]);;

let RFB_PW_NONZERO = prove
 (`!e y:real^N. ~(y = vec 0) ==> ~(((norm y pow 2) rpow e) % y = vec 0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `y:real^N`] RFB_PW_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `(norm(y:real^N) pow 2) rpow e % y = vec 0` THEN
  ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ]);;

let RFB_PW_NORM2 = prove
 (`!e y:real^N.
        ~(y = vec 0)
        ==> norm(((norm y pow 2) rpow e) % y) pow 2 =
            (norm y pow 2) rpow (&2 * e + &1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^N) pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LRG_CYL_POS]; ALL_TAC] THEN
  REWRITE_TAC[NORM_MUL; REAL_POW_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`; RPOW_POS_LE; REAL_LT_IMP_LE] THEN
  ASM_SIMP_TAC[RPOW_ADD] THEN REWRITE_TAC[RPOW_POW; REAL_POW_1] THEN
  SUBGOAL_THEN `(norm(y:real^N) pow 2) rpow (&2 * e) =
                (norm y pow 2) rpow e * (norm y pow 2) rpow e`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM RPOW_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    CONV_TAC REAL_RING]);;

let RFB_PW_INV = prove
 (`!e e' y:real^N.
        ~(y = vec 0) /\ (&2 * e + &1) * e' + e = &0
        ==> ((norm(((norm y pow 2) rpow e) % y) pow 2) rpow e') %
            (((norm y pow 2) rpow e) % y) = y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^N) pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LRG_CYL_POS]; ALL_TAC] THEN
  ASM_SIMP_TAC[RFB_PW_NORM2; RPOW_RPOW; REAL_LT_IMP_LE; VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[GSYM RPOW_ADD] THEN ASM_REWRITE_TAC[RPOW_0; VECTOR_MUL_LID]);;

let RFB_PW_SMOOTH = prove
 (`!e. smooth_map_on ((:real^N) DELETE vec 0) (\y. ((norm y pow 2) rpow e) % y)`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`(:real^N) DELETE vec 0`; `\y:real^N. lift((norm y pow 2) rpow e)`;
                 `\y:real^N. y`] SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
  REWRITE_TAC[LIFT_DROP; LRG_CYL_OPEN; SMOOTH_MAP_ON_ID] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`(:real^N) DELETE vec 0`; `\y:real^N. lift(norm y pow 2)`; `e:real`]
                SMOOTH_MAP_ON_LIFT_RPOW) THEN
  REWRITE_TAC[LIFT_DROP; LRG_CYL_OPEN] THEN DISCH_THEN MATCH_MP_TAC THEN
  SIMP_TAC[IN_DELETE; IN_UNIV; LRG_CYL_POS] THEN
  MP_TAC(ISPECL [`(:real^N) DELETE vec 0`; `\y:real^N. y`]
                SMOOTH_MAP_ON_NORM_POW2_OPEN) THEN
  REWRITE_TAC[LRG_CYL_OPEN; SMOOTH_MAP_ON_ID]);;

let RFB_IMAGE_INVOLUTIVE = prove
 (`!(f:real^N->real^N) g s.
        (!x. x IN s ==> f x IN s) /\ (!x. x IN s ==> g x IN s) /\
        (!y. y IN s ==> f(g y) = y)
        ==> IMAGE f s = s`,
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN MESON_TAC[]);;

let RFB_PW_DIFFEO = prove
 (`!e e'. (&2 * e + &1) * e' + e = &0
          ==> diffeomorphism_on ((:real^N) DELETE vec 0) ((:real^N) DELETE vec 0)
                (\y. ((norm y pow 2) rpow e) % y) (\y. ((norm y pow 2) rpow e') % y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(&2 * e' + &1) * e + e' = &0` ASSUME_TAC THENL
   [POP_ASSUM MP_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  REWRITE_TAC[diffeomorphism_on; LRG_CYL_OPEN; RFB_PW_SMOOTH] THEN
  REWRITE_TAC[IN_DELETE; IN_UNIV] THEN
  SUBGOAL_THEN
   `(!y:real^N. ~(y = vec 0)
                ==> ((norm(((norm y pow 2) rpow e) % y) pow 2) rpow e') %
                    (((norm y pow 2) rpow e) % y) = y) /\
    (!y:real^N. ~(y = vec 0)
                ==> ((norm(((norm y pow 2) rpow e') % y) pow 2) rpow e) %
                    (((norm y pow 2) rpow e') % y) = y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RFB_PW_INV THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC RFB_IMAGE_INVOLUTIVE THENL
   [EXISTS_TAC `\y:real^N. ((norm y pow 2) rpow e') % y`;
    EXISTS_TAC `\y:real^N. ((norm y pow 2) rpow e) % y`] THEN
  ASM_SIMP_TAC[IN_DELETE; IN_UNIV; RFB_PW_NONZERO]);;

(* The derivative of a radial power map. *)

let RFB_PW_HAS_DERIVATIVE = prove
 (`!e y:real^N.
        ~(y = vec 0)
        ==> ((\z. ((norm z pow 2) rpow e) % z) has_derivative
             (\v. ((norm y pow 2) rpow e) % v +
                  (e * (norm y pow 2) rpow (e - &1) * &2 * (y dot v)) % y)) (at y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z:real^N. (norm z pow 2) rpow e`;
                 `\v:real^N. e * (norm(y:real^N) pow 2) rpow (e - &1) * &2 * (y dot v)`;
                 `\z:real^N. z`; `\v:real^N. v`; `y:real^N`] HAS_DERIVATIVE_MUL_AT) THEN
  REWRITE_TAC[HAS_DERIVATIVE_ID] THEN ANTS_TAC THENL
   [MP_TAC(ISPECL [`\x:real. x rpow e`; `e * (norm(y:real^N) pow 2) rpow (e - &1)`;
                   `\x:real^N. lift(norm x pow 2)`; `\h:real^N. &2 % lift(y dot h)`;
                   `y:real^N`] LRG_HAS_DERIVATIVE_REAL_COMPOSE) THEN
    ASM_SIMP_TAC[LIFT_DROP; HAS_DERIVATIVE_SQNORM_AT; HAS_REAL_DERIVATIVE_RPOW;
                 LRG_CYL_POS] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
    REWRITE_TAC[LIFT_CMUL; VECTOR_MUL_ASSOC; REAL_MUL_ASSOC];
    REWRITE_TAC[]]);;

let RFB_PW_FRECHET = prove
 (`!e y:real^N.
        ~(y = vec 0)
        ==> frechet_derivative (\z. ((norm z pow 2) rpow e) % z) (at y) =
            (\v. ((norm y pow 2) rpow e) % v +
                 (e * (norm y pow 2) rpow (e - &1) * &2 * (y dot v)) % y) /\
            linear(frechet_derivative (\z. ((norm z pow 2) rpow e) % z) (at y))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o SPEC `e:real` o MATCH_MP
    (REWRITE_RULE[IMP_CONJ; RIGHT_FORALL_IMP_THM]
      (ONCE_REWRITE_RULE[SWAP_FORALL_THM] RFB_PW_HAS_DERIVATIVE))) THEN
  FIRST_ASSUM(ASSUME_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LRG_HAS_DERIVATIVE_IMP_LINEAR THEN
  MAP_EVERY EXISTS_TAC [`\z:real^N. ((norm z pow 2) rpow e) % z`; `at(y:real^N)`] THEN
  ASM_REWRITE_TAC[]);;

(* The rank-one matrix y y^T. *)

let RFB_OUTER_MUL = prove
 (`!y v:real^N. ((lambda i j. y$i * y$j):real^N^N) ** v = (y dot v) % y`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[CART_EQ; MATRIX_VECTOR_MUL_COMPONENT; LAMBDA_BETA; VECTOR_MUL_COMPONENT] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[dot] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:N)) (\i. (y:real^N)$k * y$i * (v:real^N)$i)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[LAMBDA_BETA; REAL_MUL_ASSOC];
    REWRITE_TAC[SUM_LMUL] THEN REAL_ARITH_TAC]);;

(* The exponent of the radial map at time t. *)

let RFB_CYL_EXPONENT = prove
 (`!t. t < &1 ==> ?e. &0 < &2 * e + &1 /\ (&2 * e + &1) pow 2 * (&1 - t) = &1`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `(inv(sqrt(&1 - t)) - &1) / &2` THEN
  REWRITE_TAC[REAL_ARITH `&2 * (x - &1) / &2 + &1 = x`] THEN
  SUBGOAL_THEN `&0 < &1 - t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_INV; SQRT_POS_LT; REAL_POW_INV; SQRT_POW_2; REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC);;

(* The cylinder flow at time t is (1 - t) times a pullback of the round      *)
(* cylinder metric g0 = (2/|z|^2) delta.                                     *)

let RFB_CYL_PULLBACK = prove
 (`!t e y:real^3.
        (&2 * e + &1) pow 2 * (&1 - t) = &1 /\ ~(y = vec 0)
        ==> cylinder_flow t y =
            (&1 - t) %% mpullback (\z:real^3. ((norm z pow 2) rpow e) % z)
                                  (\z. (&2 / norm z pow 2) %% mat 1) y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`e:real`; `y:real^3`] RFB_PW_FRECHET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC RFB_MATRIX_EQ_DOT THEN
  MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN
  REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN
  ASM_SIMP_TAC[LRG_MPULLBACK_DOT] THEN
  ASM_REWRITE_TAC[cylinder_flow; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_ADD_RDISTRIB;
                  MATRIX_VECTOR_MUL_LID; RFB_OUTER_MUL] THEN
  REWRITE_TAC[DOT_RMUL; DOT_LMUL; DOT_RADD; DOT_LADD; NORM_POW_2] THEN
  SUBGOAL_THEN `&0 < (y:real^3) dot y` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_POS_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[RPOW_SUB; RPOW_POW; REAL_POW_1] THEN
  SUBGOAL_THEN `&0 < ((y:real^3) dot y) rpow e` MP_TAC THENL
   [ASM_SIMP_TAC[RPOW_POS_LT]; ALL_TAC] THEN
  UNDISCH_TAC `&0 < (y:real^3) dot y` THEN
  UNDISCH_TAC `(&2 * e + &1) pow 2 * (&1 - t) = &1` THEN
  REWRITE_TAC[DOT_SYM] THEN CONV_TAC REAL_FIELD);;

(* Ricci and scalar curvature of the cylinder flow at every time t < 1. *)

let RFB_CYL_SETUP = prove
 (`!t. t < &1
       ==> ?e. (&2 * e + &1) pow 2 * (&1 - t) = &1 /\
               diffeomorphism_on ((:real^3) DELETE vec 0) ((:real^3) DELETE vec 0)
                 (\y. ((norm y pow 2) rpow e) % y)
                 (\y. ((norm y pow 2) rpow (--e / (&2 * e + &1))) % y) /\
               metric_field ((:real^3) DELETE vec 0)
                 (mpullback (\z:real^3. ((norm z pow 2) rpow e) % z)
                            (\z. (&2 / norm z pow 2) %% mat 1)) /\
               (!y. y IN (:real^3) DELETE vec 0
                    ==> cylinder_flow t y =
                        (&1 - t) %% mpullback (\z:real^3. ((norm z pow 2) rpow e) % z)
                                              (\z. (&2 / norm z pow 2) %% mat 1) y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `t:real` RFB_CYL_EXPONENT) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[IN_DELETE; IN_UNIV; RFB_CYL_PULLBACK] THEN
  SUBGOAL_THEN
   `diffeomorphism_on ((:real^3) DELETE vec 0) ((:real^3) DELETE vec 0)
      (\y. ((norm y pow 2) rpow e) % y)
      (\y. ((norm y pow 2) rpow (--e / (&2 * e + &1))) % y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RFB_PW_DIFFEO THEN UNDISCH_TAC `&0 < &2 * e + &1` THEN
    CONV_TAC REAL_FIELD;
    ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
  MAP_EVERY EXISTS_TAC
   [`(:real^3) DELETE vec 0`;
    `\y:real^3. ((norm y pow 2) rpow (--e / (&2 * e + &1))) % y`] THEN
  ASM_REWRITE_TAC[LRG_CYL_METRIC]);;

let RFB_CYL_RICCI = prove
 (`!t y u v:real^3.
        t < &1 /\ ~(y = vec 0)
        ==> lricci (cylinder_flow t) y u v =
            ((u dot v) - (u dot y) * (v dot y) / norm y pow 2) / norm y pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `t:real` RFB_CYL_SETUP) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `lricci (\z. (&1 - t) %%
                mpullback (\z:real^3. ((norm z pow 2) rpow e) % z)
                          (\z. (&2 / norm z pow 2) %% mat 1) z) y u v` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRICCI_LOCAL THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    ASM_SIMP_TAC[LRG_CYL_OPEN; IN_DELETE; IN_UNIV];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `lricci (mpullback (\z:real^3. ((norm z pow 2) rpow e) % z)
                      (\z. (&2 / norm z pow 2) %% mat 1)) y u v` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRICCI_SCALE THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    ASM_REWRITE_TAC[IN_DELETE; IN_UNIV] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `(:real^3) DELETE vec 0`;
                 `\z:real^3. ((norm z pow 2) rpow e) % z`;
                 `\z:real^3. ((norm z pow 2) rpow (--e / (&2 * e + &1))) % z`;
                 `\z:real^3. (&2 / norm z pow 2) %% (mat 1:real^3^3)`;
                 `y:real^3`; `u:real^3`; `v:real^3`] LRICCI_PULLBACK) THEN
  ASM_REWRITE_TAC[LRG_CYL_METRIC; IN_DELETE; IN_UNIV] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`e:real`; `y:real^3`] RFB_PW_NONZERO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[LRICCI_ROUND_CYLINDER] THEN
  MP_TAC(ISPECL [`e:real`; `y:real^3`] RFB_PW_FRECHET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[DOT_RMUL; DOT_LMUL; DOT_RADD; DOT_LADD; NORM_POW_2] THEN
  SUBGOAL_THEN `&0 < (y:real^3) dot y` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_POS_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[RPOW_SUB; RPOW_POW; REAL_POW_1] THEN
  SUBGOAL_THEN `&0 < ((y:real^3) dot y) rpow e` MP_TAC THENL
   [ASM_SIMP_TAC[RPOW_POS_LT]; ALL_TAC] THEN
  UNDISCH_TAC `&0 < (y:real^3) dot y` THEN
  REWRITE_TAC[DOT_SYM] THEN CONV_TAC REAL_FIELD);;

let RFB_CYL_SCALAR = prove
 (`!t y:real^3.
        t < &1 /\ ~(y = vec 0) ==> lscalar (cylinder_flow t) y = &1 / (&1 - t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `t:real` RFB_CYL_SETUP) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `lscalar (\z. (&1 - t) %%
                 mpullback (\z:real^3. ((norm z pow 2) rpow e) % z)
                           (\z. (&2 / norm z pow 2) %% mat 1) z) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LSCALAR_LOCAL THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    ASM_SIMP_TAC[LRG_CYL_OPEN; IN_DELETE; IN_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^3) DELETE vec 0`;
                 `mpullback (\z:real^3. ((norm z pow 2) rpow e) % z)
                            (\z. (&2 / norm z pow 2) %% (mat 1:real^3^3))`;
                 `&1 - t`; `y:real^3`] LSCALAR_SCALE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_DELETE; IN_UNIV] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `(:real^3) DELETE vec 0`;
                 `\z:real^3. ((norm z pow 2) rpow e) % z`;
                 `\z:real^3. ((norm z pow 2) rpow (--e / (&2 * e + &1))) % z`;
                 `\z:real^3. (&2 / norm z pow 2) %% (mat 1:real^3^3)`;
                 `y:real^3`] LSCALAR_PULLBACK) THEN
  ASM_REWRITE_TAC[LRG_CYL_METRIC; IN_DELETE; IN_UNIV] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`e:real`; `y:real^3`] RFB_PW_NONZERO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[LSCALAR_ROUND_CYLINDER]);;

let RFB_CYL_METRIC_FIELD = prove
 (`!t. t < &1 ==> metric_field ((:real^3) DELETE vec 0) (cylinder_flow t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `t:real` RFB_CYL_SETUP) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC RFB_METRIC_FIELD_EQ THEN
  EXISTS_TAC
   `\z. (&1 - t) %%
        mpullback (\z:real^3. ((norm z pow 2) rpow e) % z)
                  (\z. (&2 / norm z pow 2) %% mat 1) z` THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN
  ASM_REWRITE_TAC[ETA_AX] THEN ASM_REAL_ARITH_TAC);;

(* Joint smoothness of the cylinder flow in time and space. *)

let RFB_OUTER_SMOOTH = prove
 (`smooth_map_on (:real^3)
     (\y:real^3. (vectorize:real^3^3->real^(3,3)finite_prod)
                 ((lambda i j. y$i * y$j):real^3^3))`,
  MP_TAC(ISPECL [`(:real^3)`; `\y:real^3. ((lambda i j. y$i * y$j):real^3^3)`]
                LRG_SMOOTH_VECTORIZE) THEN
  REWRITE_TAC[OPEN_UNIV; o_DEF] THEN DISCH_THEN SUBST1_TAC THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN
  MP_TAC(ISPECL [`(:real^3)`; `\y:real^3. lift(y$i)`; `\y:real^3. lift(y$j)`]
                SMOOTH_MAP_ON_LIFT_MUL) THEN
  SIMP_TAC[LIFT_DROP; OPEN_UNIV; SMOOTH_MAP_ON_LIFT_COORDINATE]);;

let RFB_CYL_FLOW_SMOOTH = prove
 (`!S. open S /\ (!z:real^(1,3)finite_sum. z IN S ==> ~(sndcart z = vec 0))
       ==> smooth_map_on S
             (\z. (vectorize:real^3^3->real^(3,3)finite_prod)
                  (cylinder_flow (drop(fstcart z)) (sndcart z)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[cylinder_flow; VECTORIZE_CMUL; VECTORIZE_ADD] THEN
  SUBGOAL_THEN
   `smooth_map_on S (\z:real^(1,3)finite_sum. lift(norm(sndcart z) pow 2))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`S:real^(1,3)finite_sum->bool`;
                   `\z:real^(1,3)finite_sum. sndcart z`]
                  SMOOTH_MAP_ON_NORM_POW2_OPEN) THEN
    ASM_SIMP_TAC[RFB_SMOOTH_SNDCART];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^(1,3)finite_sum. z IN S ==> ~(norm(sndcart z) pow 2 = &0)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_EQ_0; NORM_EQ_0]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`S:real^(1,3)finite_sum->bool`;
    `\z:real^(1,3)finite_sum. lift(&2 / norm(sndcart z) pow 2)`;
    `\z:real^(1,3)finite_sum.
       (&1 - drop(fstcart z)) % (vectorize:real^3^3->real^(3,3)finite_prod) (mat 1) +
       (drop(fstcart z) / norm(sndcart z) pow 2) %
       (vectorize:real^3^3->real^(3,3)finite_prod)
       ((lambda i j. (sndcart z)$i * (sndcart z)$j):real^3^3)`]
   SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`S:real^(1,3)finite_sum->bool`;
                   `\z:real^(1,3)finite_sum. lift(&2)`;
                   `\z:real^(1,3)finite_sum. lift(norm(sndcart z) pow 2)`]
                  SMOOTH_MAP_ON_LIFT_DIV) THEN
    ASM_SIMP_TAC[LIFT_DROP; SMOOTH_MAP_ON_CONST];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`S:real^(1,3)finite_sum->bool`;
                   `\z:real^(1,3)finite_sum. lift(&1 - drop(fstcart z))`;
                   `\z:real^(1,3)finite_sum.
                      (vectorize:real^3^3->real^(3,3)finite_prod) (mat 1)`]
                  SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
    REWRITE_TAC[LIFT_DROP; SMOOTH_MAP_ON_CONST] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`S:real^(1,3)finite_sum->bool`;
                   `\z:real^(1,3)finite_sum. lift(&1)`;
                   `\z:real^(1,3)finite_sum. lift(drop(fstcart z))`]
                  SMOOTH_MAP_ON_LIFT_SUB) THEN
    ASM_SIMP_TAC[LIFT_DROP; SMOOTH_MAP_ON_CONST; RFB_SMOOTH_FSTCART];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`S:real^(1,3)finite_sum->bool`;
    `\z:real^(1,3)finite_sum. lift(drop(fstcart z) / norm(sndcart z) pow 2)`;
    `\z:real^(1,3)finite_sum.
       (vectorize:real^3^3->real^(3,3)finite_prod)
       ((lambda i j. (sndcart z)$i * (sndcart z)$j):real^3^3)`]
   SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`S:real^(1,3)finite_sum->bool`;
                   `\z:real^(1,3)finite_sum. lift(drop(fstcart z))`;
                   `\z:real^(1,3)finite_sum. lift(norm(sndcart z) pow 2)`]
                  SMOOTH_MAP_ON_LIFT_DIV) THEN
    ASM_SIMP_TAC[LIFT_DROP; RFB_SMOOTH_FSTCART];
    MP_TAC(ISPECL [`S:real^(1,3)finite_sum->bool`; `(:real^3)`;
                   `\y:real^3. (vectorize:real^3^3->real^(3,3)finite_prod)
                               ((lambda i j. y$i * y$j):real^3^3)`]
                  RFB_SMOOTH_SNDCART_COMPOSE) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; RFB_OUTER_SMOOTH]]);;

let RFB_CYL_TIME_DERIV = prove
 (`!A B C D t.
        ((\s. A * ((&1 - s) * B + s / C * D)) has_real_derivative
         (A * (D / C - B))) (atreal t)`,
  REPEAT GEN_TAC THEN
  MP_TAC(REAL_DIFF_CONV
   `((\s. A * ((&1 - s) * B + s / C * D)) has_real_derivative f') (atreal t)`) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The main results on the cylinder.                                         *)
(* ------------------------------------------------------------------------- *)

let CYLINDER_FLOW_SCALAR = prove
 (`!t y. t < &1 /\ ~(y = vec 0)
         ==> mfd_scalar (open_set_atlas ((:real^3) DELETE vec 0))
                        (cylinder_flow t) y = &1 / (&1 - t)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[RFB_OPEN_SET_MFD_SCALAR; LRG_CYL_OPEN; IN_DELETE; IN_UNIV;
               RFB_CYL_SCALAR]);;

let SHRINKING_CYLINDER_FLOW = prove
 (`!a. a < &1
       ==> ricci_flow_on (subtopology euclidean ((:real^3) DELETE vec 0),
                          open_set_atlas ((:real^3) DELETE vec 0)) a (&1)
                         cylinder_flow`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ricci_flow_on; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  ASM_SIMP_TAC[OPEN_SET_ATLAS; LRG_CYL_OPEN] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFB_OPEN_SET_RIEMANNIAN THEN
    ASM_SIMP_TAC[LRG_CYL_OPEN; RFB_CYL_METRIC_FIELD];
    REWRITE_TAC[RFB_OPEN_SET_ATLAS_CASES] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[FST; SND; IMAGE_ID] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC
     `\z:real^(1,3)finite_sum. (vectorize:real^3^3->real^(3,3)finite_prod)
                               (cylinder_flow (drop(fstcart z)) (sndcart z))` THEN
    SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; LRG_CYL_OPEN] THEN CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART] THEN
      SIMP_TAC[RFB_OPEN_SET_METRIC_LOCAL; LRG_CYL_OPEN];
      MATCH_MP_TAC RFB_CYL_FLOW_SMOOTH THEN
      SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; LRG_CYL_OPEN] THEN
      REWRITE_TAC[FORALL_IN_PCROSS; SNDCART_PASTECART; IN_DELETE] THEN
      SIMP_TAC[]];
    MAP_EVERY X_GEN_TAC [`t:real`; `x:real^3`; `i:num`; `j:num`] THEN
    REWRITE_TAC[IN_DELETE; IN_UNIV] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[RFB_MFD_RICCI_MATRIX_COMPONENT; RFB_OPEN_SET_MFD_RICCI;
                 LRG_CYL_OPEN; IN_DELETE; IN_UNIV; RFB_CYL_RICCI] THEN
    ASM_SIMP_TAC[DOT_BASIS_BASIS; DOT_BASIS] THEN
    REWRITE_TAC[cylinder_flow; MATRIX_CMUL_COMPONENT; MATRIX_ADD_COMPONENT] THEN
    ASM_SIMP_TAC[MAT_COMPONENT; LAMBDA_BETA] THEN
    MP_TAC(SPECL [`&2 / norm(x:real^3) pow 2`; `if i:num = j then &1 else &0`;
                  `norm(x:real^3) pow 2`; `(x:real^3)$i * x$j`; `t:real`]
                 RFB_CYL_TIME_DERIV) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC]);;

