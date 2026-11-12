(* ========================================================================= *)
(* Unit pc_cmp_regf (comparison-geometry layer CMP): smooth regular fields   *)
(* (Petersen Sec 12.1, the isotopy lemma), CMP_R6_REGULAR_FIELD.  Near a     *)
(* compact set K of regular points of d_p there is a smooth unit field Z     *)
(* making a uniformly obtuse angle with every minimizing direction to p.     *)
(* Route: in the chart at a regular point x0 the regular direction v0, kept  *)
(* constant in chart coordinates, stays uniformly obtuse near x0 (limits of  *)
(* minimizing vectors are minimizing: the chart form of exp is continuous);  *)
(* finitely many such fields are glued by cutoffs (MFD_SMOOTH_CUTOFF) and    *)
(* normalized.                                                               *)
(* ========================================================================= *)

needs "src/pc_cmp_crit.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Chart facts.  Vectors at x in the coordinates of a chart c                *)
(* and of the preferred chart; the metric in c is the local metric.  The    *)
(* uniform lower bound of a continuous family of positive definite forms on  *)
(* a compact set (a copy of P4_FAMILY_LOWER of pc_p4_width, which this layer *)
(* does not load).                                                           *)
(* ========================================================================= *)

let CMPRF_JAC_FACTS = prove
 (`!top atlas (g:A->real^N^N) (c:(A->bool)#(A->real^N)) (x:A).
        smooth_manifold_atlas top atlas /\ c IN atlas /\ x IN FST c
        ==> linear(chart_jac c (chart_at atlas x) x) /\
            linear(chart_jac (chart_at atlas x) c x) /\
            (!v. chart_jac c (chart_at atlas x) x (chart_jac (chart_at atlas x) c x v) = v) /\
            (!v. chart_jac (chart_at atlas x) c x (chart_jac c (chart_at atlas x) x v) = v) /\
            (!a b. chart_jac c (chart_at atlas x) x a dot
                   (g x ** chart_jac c (chart_at atlas x) x b) =
                   a dot (metric_local atlas c g (SND c x) ** b))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `linear(chart_jac (c:(A->bool)#(A->real^N)) (chart_at atlas (x:A)) x) /\
    linear(chart_jac (chart_at atlas x) c x)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                     `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                     `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`; `x:A`]
        CHART_JAC_LINEAR);
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                     `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                     `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`; `x:A`]
        CHART_JAC_LINEAR)] THEN
    ASM_REWRITE_TAC[PAIR; IN_INTER];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`; `x:A`]
      CHART_JAC_INVERSE) THEN
    ASM_REWRITE_TAC[PAIR; IN_INTER; FUN_EQ_THM; o_THM];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`; `x:A`]
      CHART_JAC_INVERSE) THEN
    ASM_REWRITE_TAC[PAIR; IN_INTER; FUN_EQ_THM; o_THM];
    REPEAT GEN_TAC THEN REWRITE_TAC[metric_local] THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
    ASM_SIMP_TAC[MATRIX_WORKS]]);;

let CMPRF_FAMILY_LOWER = prove
 (`!(G:real^M->real^N^N) S.
        compact S /\ (\z. vectorize(G z)) continuous_on S /\
        (!z v. z IN S /\ ~(v = vec 0) ==> &0 < v dot (G z ** v))
        ==> ?m. &0 < m /\
                !z v. z IN S ==> m * norm v pow 2 <= v dot (G z ** v)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `S:real^M->bool = {}` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY; REAL_LT_01]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\p:real^(M,N)finite_sum.
       sndcart p dot ((G:real^M->real^N^N) (fstcart p) ** sndcart p)`;
    `(S:real^M->bool) PCROSS sphere(vec 0:real^N,&1)`] CONTINUOUS_ATTAINS_INF) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_PCROSS THEN ASM_REWRITE_TAC[COMPACT_SPHERE];
      ASM_REWRITE_TAC[PCROSS_EQ_EMPTY; SPHERE_EQ_EMPTY] THEN REAL_ARITH_TAC;
      REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_SNDCART];
        ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_MATRIX_VECTOR_MUL THEN CONJ_TAC THENL
       [ALL_TAC;
        MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_SNDCART]] THEN
      SUBGOAL_THEN
       `(vectorize:real^N^N->real^(N,N)finite_prod) o
        (\p:real^(M,N)finite_sum. (G:real^M->real^N^N) (fstcart p)) =
        (\z. vectorize(G z)) o fstcart`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_FSTCART];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `S:real^M->bool` THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; FSTCART_PASTECART] THEN
        SIMP_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_IN_PCROSS; FORALL_IN_PCROSS; FSTCART_PASTECART;
              SNDCART_PASTECART; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `z0:real^M` (X_CHOOSE_THEN `u0:real^N`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `m = u0 dot ((G:real^M->real^N^N) z0 ** u0)` THEN
  SUBGOAL_THEN `&0 < m` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN UNDISCH_TAC `norm(u0:real^N) = &1` THEN
    ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `m:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`z:real^M`; `v:real^N`] THEN DISCH_TAC THEN
  ASM_CASES_TAC `v:real^N = vec 0` THENL
   [ASM_REWRITE_TAC[NORM_0; DOT_LZERO] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`z:real^M`; `inv(norm v) % v:real^N`]) THEN
  ASM_REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0; GRGD_QUAD_HOMOG] THEN
  SUBGOAL_THEN `&0 < norm(v:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `q = v dot ((G:real^M->real^N^N) z ** v)` THEN
  ABBREV_TAC `n = norm(v:real^N)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `q = (inv n * inv n * q) * n pow 2` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < n` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
  ASM_REWRITE_TAC[REAL_MUL_ASSOC]);;

(* ========================================================================= *)
(* Limits of minimizing vectors.  In the coordinates of a chart              *)
(* c0, if exp(y_n, w_n) = p with |w_n|^2 = d(y_n, p)^2 and (y_n, w_n) tends  *)
(* to (y0, w0), then (y0, w0) is minimizing as well (the chart form of exp   *)
(* has smooth local representatives, GEOF_EXP_CHART_LOCAL_REP).              *)
(* ========================================================================= *)

let CMPRF_EXP_CHART_LIMIT = prove
 (`!top atlas (g:A->real^N^N) c0 (z:num->real^(N,N)finite_sum) z0 (q:A).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ c0 IN atlas /\
        z0 IN mfd_exp_chart_dom (top,atlas) g c0 /\ (z --> z0) sequentially /\
        (!n. mfd_exp_chart (top,atlas) g c0 (z n) = q)
        ==> mfd_exp_chart (top,atlas) g c0 z0 = q`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `c0:(A->bool)#(A->real^N)`; `z0:real^(N,N)finite_sum`]
    GEOF_EXP_CHART_LOCAL_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:real^(N,N)finite_sum->bool` (X_CHOOSE_THEN
    `c:(A->bool)#(A->real^N)` (X_CHOOSE_THEN `Fr:real^(N,N)finite_sum->real^N`
    STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `?N. !n. N <= n ==> (z:num->real^(N,N)finite_sum) n IN W`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `open(W:real^(N,N)finite_sum->bool)` THEN REWRITE_TAC[open_def] THEN
    DISCH_THEN(MP_TAC o SPEC `z0:real^(N,N)finite_sum`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `((z:num->real^(N,N)finite_sum) --> z0) sequentially` THEN
    REWRITE_TAC[LIM_SEQUENTIALLY] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN ASM_MESON_TAC[DIST_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:A) IN FST(c:(A->bool)#(A->real^N)) /\
                !n. N <= n ==> (Fr:real^(N,N)finite_sum->real^N)((z:num->real^(N,N)finite_sum) n) = SND c q`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[LE_REFL]; ASM_MESON_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `(Fr:real^(N,N)finite_sum->real^N) z0 = SND (c:(A->bool)#(A->real^N)) q`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
    EXISTS_TAC `\n. (Fr:real^(N,N)finite_sum->real^N)((z:num->real^(N,N)finite_sum) n)` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LIM_CONTINUOUS_FUNCTION THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`Fr:real^(N,N)finite_sum->real^N`; `W:real^(N,N)finite_sum->bool`]
        CONTINUOUS_ON_EQ_CONTINUOUS_AT) THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
      MATCH_MP_TAC LIM_EVENTUALLY THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_MESON_TAC[]);;

let CMPRF_MIN_LIMIT = prove
 (`!top atlas (g:A->real^N^N) (p:A) c0 (y:num->real^N) (w:num->real^N) y0 w0.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ c0 IN atlas /\
        (!n. y n IN IMAGE (SND c0) (FST c0)) /\ y0 IN IMAGE (SND c0) (FST c0) /\
        (y --> y0) sequentially /\ (w --> w0) sequentially /\
        (!n. mfd_exp_chart (top,atlas) g c0 (pastecart (y n) (w n)) = p) /\
        (!n. w n dot (metric_local atlas c0 g (y n) ** w n) =
             mfd_dist (top,atlas) g (chart_inv c0 (y n)) p pow 2)
        ==> mfd_exp_chart (top,atlas) g c0 (pastecart y0 w0) = p /\
            w0 dot (metric_local atlas c0 g y0 ** w0) =
            mfd_dist (top,atlas) g (chart_inv c0 y0) p pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c0:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND (c0:(A->bool)#(A->real^N))) (FST c0))
                  (metric_local atlas c0 (g:A->real^N^N))` ASSUME_TAC THENL
   [ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
  ABBREV_TAC `U = IMAGE (SND (c0:(A->bool)#(A->real^N))) (FST c0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CMPRF_EXP_CHART_LIMIT THEN
    EXISTS_TAC `\n. pastecart ((y:num->real^N) n) ((w:num->real^N) n)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[GEOF_EXP_CHART_DOM; PASTECART_IN_PCROSS; IN_UNIV; geo_cpt;
                  FSTCART_PASTECART] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `chart_inv (c0:(A->bool)#(A->real^N)) y0 IN topspace top` ASSUME_TAC THENL
       [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`] MFD_HOPF_RINOW) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
      DISCH_THEN(fun th -> ASM_SIMP_TAC[th; IN_UNIV]);
      MATCH_MP_TAC LIM_PASTECART THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
  EXISTS_TAC `\n. (w:num->real^N) n dot
                  (metric_local atlas (c0:(A->bool)#(A->real^N)) (g:A->real^N^N) (y n) ** w n)` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [REWRITE_TAC[TENDSTO_REAL] THEN
    MP_TAC(ISPECL
     [`\z:real^(N,N)finite_sum. lift(sndcart z dot
         (metric_local atlas (c0:(A->bool)#(A->real^N)) (g:A->real^N^N) (fstcart z) **
          sndcart z))`;
      `(U:real^N->bool) PCROSS (:real^N)`] CONTINUOUS_ON_SEQUENTIALLY) THEN
    MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_SNDCART];
        ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_MATRIX_VECTOR_MUL THEN CONJ_TAC THENL
       [ALL_TAC;
        MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_SNDCART]] THEN
      SUBGOAL_THEN
       `(vectorize:real^N^N->real^(N,N)finite_prod) o
        (\z:real^(N,N)finite_sum.
           metric_local atlas (c0:(A->bool)#(A->real^N)) (g:A->real^N^N) (fstcart z)) =
        (vectorize o metric_local atlas c0 g) o fstcart`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_FSTCART];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_MESON_TAC[metric_field];
          REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; FSTCART_PASTECART] THEN
          SIMP_TAC[]]];
      DISCH_THEN(MP_TAC o SPECL [`\n. pastecart ((y:num->real^N) n) ((w:num->real^N) n)`;
                                 `pastecart (y0:real^N) (w0:real^N)`]) THEN
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV; o_DEF; FSTCART_PASTECART;
                      SNDCART_PASTECART] THEN
      ANTS_TAC THENL [MATCH_MP_TAC LIM_PASTECART THEN ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REALLIM_POW THEN
  SUBGOAL_THEN
   `continuous_map (subtopology euclidean U,euclideanreal)
      (\y. mfd_dist (top,atlas) (g:A->real^N^N) p
             (chart_inv (c0:(A->bool)#(A->real^N)) y))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\y. mfd_dist (top,atlas) (g:A->real^N^N) p
             (chart_inv (c0:(A->bool)#(A->real^N)) y)) =
      (\x. mfd_dist (top,atlas) g p x) o chart_inv c0`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `top:A topology` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`]
        MFDC_CHART_INV_CONTINUOUS) THEN
      ASM_REWRITE_TAC[PAIR; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN SIMP_TAC[];
      MATCH_MP_TAC MFD_DIST_CONTINUOUS_RIGHT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sequentially`; `subtopology euclidean (U:real^N->bool)`; `euclideanreal`;
                 `y:num->real^N`;
                 `\y. mfd_dist (top,atlas) (g:A->real^N^N) p
                        (chart_inv (c0:(A->bool)#(A->real^N)) y)`;
                 `y0:real^N`] CONTINUOUS_MAP_LIMIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LIMIT_SUBTOPOLOGY; LIMIT_EUCLIDEAN; EVENTUALLY_TRUE]; ALL_TAC] THEN
  REWRITE_TAC[GSYM tendsto_real_def; o_DEF] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`] MFD_DIST_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]));;

(* ========================================================================= *)
(* The local field.  At a regular point x0 the regular vector                *)
(* v0, kept constant in the coordinates of c0 = chart_at x0, makes a         *)
(* uniformly obtuse angle with all minimizing vectors near x0 (by           *)
(* contradiction: Bolzano-Weierstrass in chart coordinates, CMPRF_MIN_LIMIT, *)
(* regularity at x0).                                                        *)
(* ========================================================================= *)

let CMPRF_CHART_MINS = prove
 (`!top atlas (g:A->real^N^N) (p:A) c (x:A) w.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ c IN atlas /\ x IN FST c /\
        mfd_exp (top,atlas) g x w = p /\ mfd_tnorm g x w = mfd_dist (top,atlas) g x p
        ==> mfd_exp_chart (top,atlas) g c
              (pastecart (SND c x) (chart_jac (chart_at atlas x) c x w)) = p /\
            chart_jac (chart_at atlas x) c x w dot
            (metric_local atlas c g (SND c x) ** chart_jac (chart_at atlas x) c x w) =
            mfd_dist (top,atlas) g x p pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `c:(A->bool)#(A->real^N)`; `x:A`] CMPRF_JAC_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[mfd_exp_chart; FSTCART_PASTECART; SNDCART_PASTECART] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM((fun th -> REWRITE_TAC[GSYM th]) o check (fun th ->
    is_forall(concl th) && can (find_term (fun t -> try fst(dest_const t) = "metric_local"
      with Failure _ -> false)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM(ASSUME `mfd_tnorm (g:A->real^N^N) x w = mfd_dist (top,atlas) g x p`);
              ASSUME `!v. mfd_tnorm (g:A->real^N^N) x v pow 2 = v dot (g x ** v)`]);;

let CMPRF_CHART_DIST_CONT = prove
 (`!top atlas (g:A->real^N^N) (p:A) c.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ c IN atlas
        ==> (lift o (\y. mfd_dist (top,atlas) g (chart_inv c y) p))
            continuous_on IMAGE (SND c) (FST c)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM CONTINUOUS_MAP_EUCLIDEAN; GSYM CONTINUOUS_MAP_EQ_LIFT] THEN
  SUBGOAL_THEN
   `(\y. mfd_dist (top,atlas) (g:A->real^N^N) (chart_inv (c:(A->bool)#(A->real^N)) y) p) =
    (\x. mfd_dist (top,atlas) g p x) o chart_inv c`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN MATCH_MP_TAC MFD_DIST_SYM THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `top:A topology` THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
      MFDC_CHART_INV_CONTINUOUS) THEN
    ASM_REWRITE_TAC[PAIR; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN SIMP_TAC[];
    MATCH_MP_TAC MFD_DIST_CONTINUOUS_RIGHT THEN ASM_REWRITE_TAC[]]);;

(* The quadratic expression a . (G(y) b(y)) along a sequence. *)

let CMPRF_QUAD_LIMIT = prove
 (`!(G:real^N->real^N^N) U a (y:num->real^N) (w:num->real^N) y0 w0.
        (vectorize o G) continuous_on U /\ (!n. y n IN U) /\ y0 IN U /\
        (y --> y0) sequentially /\ (w --> w0) sequentially
        ==> ((\n. a dot (G(y n) ** w n)) ---> a dot (G y0 ** w0)) sequentially /\
            ((\n. w n dot (G(y n) ** w n)) ---> w0 dot (G y0 ** w0)) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\z:real^(N,N)finite_sum. (G:real^N->real^N^N)(fstcart z) ** sndcart z) continuous_on
                ((U:real^N->bool) PCROSS (:real^N))` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_MATRIX_VECTOR_MUL THEN CONJ_TAC THENL
     [ALL_TAC; MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_SNDCART]] THEN
    SUBGOAL_THEN
     `(vectorize:real^N^N->real^(N,N)finite_prod) o
      (\z:real^(N,N)finite_sum. (G:real^N->real^N^N) (fstcart z)) =
      (vectorize o G) o fstcart`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_FSTCART];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; FSTCART_PASTECART] THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(((\z:real^(N,N)finite_sum. (G:real^N->real^N^N)(fstcart z) ** sndcart z) o
                 (\n. pastecart ((y:num->real^N) n) ((w:num->real^N) n))) -->
                 G y0 ** w0) sequentially` MP_TAC THENL
   [MP_TAC(ISPECL [`\z:real^(N,N)finite_sum. (G:real^N->real^N^N)(fstcart z) ** sndcart z`;
                   `(U:real^N->bool) PCROSS (:real^N)`] CONTINUOUS_ON_SEQUENTIALLY) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`\n. pastecart ((y:num->real^N) n) ((w:num->real^N) n)`;
                               `pastecart (y0:real^N) (w0:real^N)`]) THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC LIM_PASTECART THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[o_DEF; FSTCART_PASTECART; SNDCART_PASTECART] THEN DISCH_TAC THEN
  CONJ_TAC THEN REWRITE_TAC[TENDSTO_REAL] THENL
   [MP_TAC(ISPECL [`sequentially`; `\x y:real^N. lift(x dot y)`;
                   `\n:num. (a:real^N)`;
                   `\n. (G:real^N->real^N^N)((y:num->real^N) n) ** (w:num->real^N) n`;
                   `a:real^N`; `(G:real^N->real^N^N) y0 ** w0`] LIM_BILINEAR) THEN
    ASM_REWRITE_TAC[BILINEAR_DOT; o_DEF; LIM_CONST];
    MP_TAC(ISPECL [`sequentially`; `\x y:real^N. lift(x dot y)`;
                   `w:num->real^N`;
                   `\n. (G:real^N->real^N^N)((y:num->real^N) n) ** (w:num->real^N) n`;
                   `w0:real^N`; `(G:real^N->real^N^N) y0 ** w0`] LIM_BILINEAR) THEN
    ASM_REWRITE_TAC[BILINEAR_DOT; o_DEF]]);;

(* The local field in chart coordinates. *)

let CMPRF_LOCAL_CHART = prove
 (`!top atlas (g:A->real^N^N) (p:A) c0 y0 v0.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ c0 IN atlas /\
        y0 IN IMAGE (SND c0) (FST c0) /\
        (!w. mfd_exp_chart (top,atlas) g c0 (pastecart y0 w) = p /\
             w dot (metric_local atlas c0 g y0 ** w) =
             mfd_dist (top,atlas) g (chart_inv c0 y0) p pow 2
             ==> v0 dot (metric_local atlas c0 g y0 ** w) < &0)
        ==> ?r c M. &0 < r /\ ball(y0,r) SUBSET IMAGE (SND c0) (FST c0) /\ &0 < c /\
                    (!y. y IN ball(y0,r) ==> v0 dot (metric_local atlas c0 g y ** v0) <= M) /\
                    !y w. y IN ball(y0,r) /\
                          mfd_exp_chart (top,atlas) g c0 (pastecart y w) = p /\
                          w dot (metric_local atlas c0 g y ** w) =
                          mfd_dist (top,atlas) g (chart_inv c0 y) p pow 2
                          ==> v0 dot (metric_local atlas c0 g y ** w) <=
                              --c * sqrt(w dot (metric_local atlas c0 g y ** w))`,
  INTRO_TAC "!top atlas g p c0 y0 v0; haus smooth riem comp c0at y0im reg" THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND (c0:(A->bool)#(A->real^N))) (FST c0))
                  (metric_local atlas c0 (g:A->real^N^N))` ASSUME_TAC THENL
   [ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `c0:(A->bool)#(A->real^N)`] CMPRF_CHART_DIST_CONT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `U = IMAGE (SND (c0:(A->bool)#(A->real^N))) (FST c0)` THEN
  ABBREV_TAC `G = metric_local atlas (c0:(A->bool)#(A->real^N)) (g:A->real^N^N)` THEN
  ABBREV_TAC `dd = \y. mfd_dist (top,atlas) (g:A->real^N^N)
                         (chart_inv (c0:(A->bool)#(A->real^N)) y) p` THEN
  SUBGOAL_THEN `!y. mfd_dist (top,atlas) (g:A->real^N^N)
                      (chart_inv (c0:(A->bool)#(A->real^N)) y) p = dd y`
  (LABEL_TAC "ddeq") THENL
   [EXPAND_TAC "dd" THEN REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "ddeq" (fun th ->
    RULE_ASSUM_TAC(fun th' -> if concl th' = concl th then th' else REWRITE_RULE[th] th') THEN
    REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `open (U:real^N->bool) /\ (vectorize o (G:real^N->real^N^N)) continuous_on U`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[metric_field];
      MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_MESON_TAC[metric_field]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?r0. &0 < r0 /\ cball(y0:real^N,r0) SUBSET U` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_CONTAINS_CBALL]; ALL_TAC] THEN
  SUBGOAL_THEN `(y0:real^N) IN cball(y0,r0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CENTRE_IN_CBALL; REAL_LT_IMP_LE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^N->real^N^N`; `cball(y0:real^N,r0)`] CMPRF_FAMILY_LOWER) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_CBALL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[GSYM o_DEF] THEN REWRITE_TAC[o_DEF; ETA_AX] THEN
      ASM_REWRITE_TAC[GSYM o_DEF];
      REPEAT STRIP_TAC THEN UNDISCH_TAC `metric_field U (G:real^N->real^N^N)` THEN
      REWRITE_TAC[metric_field] THEN
      DISCH_THEN(MP_TAC o SPEC `z:real^N` o CONJUNCT2 o CONJUNCT2) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ASM_SIMP_TAC[]]];
    DISCH_THEN(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`\y:real^N. (dd:real^N->real) y pow 2`; `cball(y0:real^N,r0)`]
    CONTINUOUS_ATTAINS_SUP) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_CBALL] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[GSYM o_DEF] THEN ASM_REWRITE_TAC[o_DEF] THEN
    UNDISCH_TAC `(lift o (dd:real^N->real)) continuous_on U` THEN
    REWRITE_TAC[o_DEF];
    DISCH_THEN(X_CHOOSE_THEN `y1:real^N` (STRIP_ASSUME_TAC o BETA_RULE))] THEN
  MP_TAC(ISPECL [`\y:real^N. v0 dot ((G:real^N->real^N^N) y ** v0)`; `cball(y0:real^N,r0)`]
    CONTINUOUS_ATTAINS_SUP) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_CBALL] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_MATRIX_VECTOR_MUL THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `y2:real^N` (STRIP_ASSUME_TAC o BETA_RULE))] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(LABEL_TAC "neg" o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  SUBGOAL_THEN
   `!n. ?y w. y IN ball(y0:real^N, r0 / (&n + &1)) /\
              mfd_exp_chart (top,atlas) (g:A->real^N^N) (c0:(A->bool)#(A->real^N))
                (pastecart y w) = p /\
              w dot ((G:real^N->real^N^N) y ** w) = (dd:real^N->real) y pow 2 /\
              --(inv(&n + &1)) * sqrt(w dot (G y ** w)) < v0 dot (G y ** w)`
  MP_TAC THENL
   [X_GEN_TAC `n:num` THEN
    USE_THEN "neg" (MP_TAC o SPECL [`r0 / (&n + &1)`; `inv(&n + &1)`;
                                    `v0 dot ((G:real^N->real^N^N) y2 ** v0)`]) THEN
    REMOVE_THEN "neg" (K ALL_TAC) THEN
    SUBGOAL_THEN `&0 < r0 / (&n + &1) /\ ball(y0:real^N, r0 / (&n + &1)) SUBSET U /\
                  &0 < inv(&n + &1) /\
                  (!y. y IN ball(y0, r0 / (&n + &1))
                       ==> v0 dot ((G:real^N->real^N^N) y ** v0) <= v0 dot (G y2 ** v0))`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 < &n + &1` ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `ball(y0:real^N, r0 / (&n + &1)) SUBSET cball(y0,r0)` ASSUME_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(y0:real^N, r0 / (&n + &1))` THEN
        REWRITE_TAC[BALL_SUBSET_CBALL] THEN MATCH_MP_TAC SUBSET_CBALL THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= r0 * &n ==> r0 <= r0 * (&n + &1)`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POS];
        ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_INV_EQ] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; REAL_NOT_LE] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:real^N` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `w:real^N` THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `yy:num->real^N` (X_CHOOSE_THEN `ww:num->real^N`
    (LABEL_TAC "seq"))) THEN
  SUBGOAL_THEN `!n. (yy:num->real^N) n IN cball(y0,r0)` (LABEL_TAC "yyc") THENL
   [X_GEN_TAC `n:num` THEN USE_THEN "seq" (MP_TAC o CONJUNCT1 o SPEC `n:num`) THEN
    REWRITE_TAC[IN_BALL; IN_CBALL] THEN
    SUBGOAL_THEN `r0 / (&n + &1) <= r0` MP_TAC THENL
     [SUBGOAL_THEN `&0 < &n + &1` ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= r0 * &n ==> r0 <= r0 * (&n + &1)`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POS];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `((yy:num->real^N) --> y0) sequentially` ASSUME_TAC THENL
   [REWRITE_TAC[LIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(SPEC `e / r0` REAL_ARCH_INV) THEN ASM_SIMP_TAC[REAL_LT_DIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN EXISTS_TAC `N:num` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    USE_THEN "seq" (MP_TAC o CONJUNCT1 o SPEC `n:num`) THEN
    REWRITE_TAC[IN_BALL] THEN
    MP_TAC(ISPECL [`y0:real^N`; `(yy:num->real^N) n`] DIST_SYM) THEN
    MATCH_MP_TAC(REAL_ARITH `b < e ==> a = c ==> a < b ==> c < e`) THEN
    SUBGOAL_THEN `inv(&n + &1) <= inv(&N)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_SIMP_TAC[REAL_OF_NUM_LT; LE_1; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `r0 * inv(&N) < e` ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ];
      ALL_TAC] THEN
    REWRITE_TAC[real_div] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `r0 * inv(&N)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `D2 = (dd:real^N->real) y1 pow 2` THEN
  SUBGOAL_THEN `&0 <= D2` ASSUME_TAC THENL
   [EXPAND_TAC "D2" THEN REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. (ww:num->real^N) n IN cball(vec 0, sqrt(D2 / m))` (LABEL_TAC "wwc") THENL
   [X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_CBALL_0] THEN MATCH_MP_TAC REAL_LE_RSQRT THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(ww:num->real^N) n dot ((G:real^N->real^N^N) ((yy:num->real^N) n) ** ww n)` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    USE_THEN "seq" (fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2(CONJUNCT2(SPEC `n:num` th)))]) THEN
    EXPAND_TAC "D2" THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`vec 0:real^N`; `sqrt(D2 / m)`] COMPACT_CBALL) THEN
  REWRITE_TAC[compact] THEN DISCH_THEN(MP_TAC o SPEC `ww:num->real^N`) THEN
  USE_THEN "wwc" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^N` (X_CHOOSE_THEN `sub:num->num` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `c0:(A->bool)#(A->real^N)`;
                 `(yy:num->real^N) o (sub:num->num)`; `(ww:num->real^N) o (sub:num->num)`;
                 `y0:real^N`; `l:real^N`] CMPRF_MIN_LIMIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "ddeq" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[o_THM] THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN USE_THEN "yyc" (MP_TAC o SPEC `(sub:num->num) n`) THEN ASM SET_TAC[];
      MATCH_MP_TAC LIM_SUBSEQUENCE THEN ASM_REWRITE_TAC[];
      GEN_TAC THEN USE_THEN "seq" (fun th -> REWRITE_TAC[SPEC `(sub:num->num) n` th]);
      GEN_TAC THEN USE_THEN "seq" (fun th -> REWRITE_TAC[SPEC `(sub:num->num) n` th])];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> USE_THEN "reg" (MP_TAC o C MATCH_MP
    (REWRITE_RULE[ASSUME `metric_local atlas (c0:(A->bool)#(A->real^N)) (g:A->real^N^N) = G`;
                  ASSUME `!y. mfd_dist (top,atlas) (g:A->real^N^N)
                                (chart_inv (c0:(A->bool)#(A->real^N)) y) p = dd y`] th))) THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LE) THEN
  EXISTS_TAC `\n. --(sqrt D2) * inv(&n + &1)` THEN
  EXISTS_TAC `\n. v0 dot ((G:real^N->real^N^N) ((yy:num->real^N) ((sub:num->num) n)) **
                          (ww:num->real^N) (sub n))` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `&0 = --(sqrt D2) * &0` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REALLIM_LMUL THEN
    MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN EXISTS_TAC `\n. inv(&n)` THEN
    REWRITE_TAC[REALLIM_1_OVER_N; EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `1` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_OF_NUM_LT; LE_1]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &n + &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ABS_INV; REAL_ARITH `&0 < x ==> abs x = x`] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`G:real^N->real^N^N`; `U:real^N->bool`; `v0:real^N`;
                   `(yy:num->real^N) o (sub:num->num)`; `(ww:num->real^N) o (sub:num->num)`;
                   `y0:real^N`; `l:real^N`] CMPRF_QUAD_LIMIT) THEN
    ASM_REWRITE_TAC[o_THM] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [GEN_TAC THEN USE_THEN "yyc" (MP_TAC o SPEC `(sub:num->num) n`) THEN ASM SET_TAC[];
        MATCH_MP_TAC LIM_SUBSEQUENCE THEN ASM_REWRITE_TAC[]];
      SIMP_TAC[]];
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN
    DISCH_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "seq" (STRIP_ASSUME_TAC o SPEC `(sub:num->num) n`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `--(inv(&((sub:num->num) n) + &1)) *
                sqrt((ww:num->real^N) (sub n) dot
                     ((G:real^N->real^N^N) ((yy:num->real^N) (sub n)) ** ww (sub n)))` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[REAL_LT_IMP_LE]] THEN
    REWRITE_TAC[REAL_MUL_LNEG; REAL_LE_NEG2] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN MP_TAC(SPEC `(sub:num->num) n` REAL_POS) THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV2 THEN
      MP_TAC(SPEC `sub:num->num` MONOTONE_BIGGER) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POS_LE THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
      REWRITE_TAC[REAL_LE_POW_2] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN USE_THEN "yyc" (fun th -> REWRITE_TAC[th])]]);;

(* ========================================================================= *)
(* The local field on the manifold.  Near a regular point x0                 *)
(* the field V(x) = J(c0 -> chart_at x) v0 satisfies <V(x), w> <= -c |w|   *)
(* for every minimizing vector w at x, and |V| <= M.                        *)
(* ========================================================================= *)

let CMPRF_EXP_JOINABLE = prove
 (`!top atlas (g:A->real^N^N) (x:A) w.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ x IN topspace top
        ==> mfd_joinable (top,atlas) x (mfd_exp (top,atlas) g x w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`] MFD_HOPF_RINOW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  DISCH_THEN(MP_TAC o SPECL [`x:A`; `w:real^N`]) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `w:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `w:real^N`; `&1`] MFD_EXP_RADIAL) THEN
  ASM_REWRITE_TAC[IN_UNIV; VECTOR_MUL_LID] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `mfd_geo (top,atlas) (g:A->real^N^N) x w`; `(:real)`;
                 `&0`; `&1`] GEOH_GEO_SEG_DIST) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN SIMP_TAC[]);;

let CMPRF_LOCAL = prove
 (`!top atlas (g:A->real^N^N) (p:A) (x0:A) v0.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ x0 IN topspace top /\
        (!w. w IN mfd_exp_dom (top,atlas) g x0 /\ mfd_exp (top,atlas) g x0 w = p /\
             mfd_tnorm g x0 w = mfd_dist (top,atlas) g x0 p
             ==> v0 dot (g x0 ** w) < &0)
        ==> ?U c M. open_in top U /\ x0 IN U /\ U SUBSET FST(chart_at atlas x0) /\ &0 < c /\
                    (!x. x IN U
                         ==> mfd_tnorm g x
                               (chart_jac (chart_at atlas x0) (chart_at atlas x) x v0) <= M) /\
                    !x w. x IN U /\ mfd_exp (top,atlas) g x w = p /\
                          mfd_tnorm g x w = mfd_dist (top,atlas) g x p
                          ==> chart_jac (chart_at atlas x0) (chart_at atlas x) x v0 dot
                              (g x ** w) <= --c * mfd_tnorm g x w`,
  INTRO_TAC "!top atlas g p x0 v0; haus smooth riem comp x0top reg" THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x0:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x0:A)` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c0:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `y0 = SND (c0:(A->bool)#(A->real^N)) x0` THEN
  SUBGOAL_THEN `(y0:real^N) IN IMAGE (SND (c0:(A->bool)#(A->real^N))) (FST c0) /\
                chart_inv c0 y0 = (x0:A)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "y0" THEN ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_local atlas (c0:(A->bool)#(A->real^N)) (g:A->real^N^N) y0 = g x0`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["y0"; "c0"] THEN MATCH_MP_TAC METRIC_LOCAL_AT THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `chart_jac (c0:(A->bool)#(A->real^N)) c0 x0 = (\h:real^N. h)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`; `x0:A`]
      CHART_JAC_SELF) THEN
    ASM_REWRITE_TAC[PAIR];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `c0:(A->bool)#(A->real^N)`; `y0:real^N`; `v0:real^N`]
    CMPRF_LOCAL_CHART) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
    USE_THEN "reg" MATCH_MP_TAC THEN
    SUBGOAL_THEN `mfd_exp (top,atlas) (g:A->real^N^N) x0 w = p` ASSUME_TAC THENL
     [UNDISCH_TAC `mfd_exp_chart (top,atlas) (g:A->real^N^N) (c0:(A->bool)#(A->real^N))
                     (pastecart y0 w) = p` THEN
      ASM_REWRITE_TAC[mfd_exp_chart; FSTCART_PASTECART; SNDCART_PASTECART];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `mfd_exp_dom (top,atlas) (g:A->real^N^N) x0 = (:real^N)`
        (fun th -> REWRITE_TAC[th; IN_UNIV]) THEN
      MATCH_MP_TAC GEOH_GEO_COMPLETE_DOM THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`] MFD_HOPF_RINOW) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[mfd_tnorm] THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
      try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "dot" with Failure _ -> false)) THEN
    MATCH_MP_TAC POW_2_SQRT THEN MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `mfd_exp (top,atlas) (g:A->real^N^N) x0 w = p`)) THEN
    MATCH_MP_TAC CMPRF_EXP_JOINABLE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `M:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "Mb") (LABEL_TAC "main")))))))) THEN
  EXISTS_TAC `{x | x IN FST (c0:(A->bool)#(A->real^N)) /\ SND c0 x IN ball(y0:real^N,r)}` THEN
  MAP_EVERY EXISTS_TAC [`c:real`; `sqrt M`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                   `y0:real^N`; `r:real`] MFDC_CHART_BALL_OPEN) THEN
    ASM_REWRITE_TAC[PAIR];
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[CENTRE_IN_BALL];
    SET_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `c0:(A->bool)#(A->real^N)`; `x:A`] CMPRF_JAC_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] GEOG_G_SYM_POS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[mfd_tnorm] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
    FIRST_X_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "metric_local"
                               with Failure _ -> false)) (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "chart_jac"
                               with Failure _ -> false)) (concl th))) THEN
    USE_THEN "Mb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN MAP_EVERY X_GEN_TAC [`x:A`; `w:real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= mfd_dist (top,atlas) (g:A->real^N^N) x p` ASSUME_TAC THENL
     [MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[] THEN
      SUBST1_TAC(SYM(ASSUME `mfd_exp (top,atlas) (g:A->real^N^N) x w = p`)) THEN
      MATCH_MP_TAC CMPRF_EXP_JOINABLE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `c0:(A->bool)#(A->real^N)`; `x:A`] CMPRF_JAC_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`; `c0:(A->bool)#(A->real^N)`; `x:A`; `w:real^N`]
      CMPRF_CHART_MINS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ABBREV_TAC `wh = chart_jac (chart_at atlas (x:A)) (c0:(A->bool)#(A->real^N)) x w` THEN
    SUBGOAL_THEN `w = chart_jac (c0:(A->bool)#(A->real^N)) (chart_at atlas (x:A)) x wh`
    SUBST1_TAC THENL [EXPAND_TAC "wh" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "metric_local"
                               with Failure _ -> false)) (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "chart_jac"
                               with Failure _ -> false)) (concl th))) THEN
    SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) x p =
                  sqrt(wh dot (metric_local atlas (c0:(A->bool)#(A->real^N)) g (SND c0 x) ** wh))`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC POW_2_SQRT THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "main" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[]]);;

(* ========================================================================= *)
(* Covering a compact set by compact pieces inside given open                *)
(* neighbourhoods (closed chart balls, MFDC_LOCAL_BALL, MFDC_CHART_COMPACT), *)
(* and the smoothness of one glued term chi(x) J(c -> c')(x) v in a chart.   *)
(* ========================================================================= *)

let CMPRF_COVER = prove
 (`!top atlas (K:A->bool) (UU:A->A->bool).
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        compact_in top K /\ (!x. x IN K ==> open_in top (UU x) /\ x IN UU x)
        ==> ?Fs CC. FINITE Fs /\ Fs SUBSET K /\
                    (!x. x IN Fs ==> compact_in top (CC x) /\ CC x SUBSET UU x) /\
                    K SUBSET UNIONS (IMAGE CC Fs)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?UP PH RR. !x:A. x IN K
        ==> (UP x,PH x) IN atlas /\ x IN UP x /\ &0 < RR x /\
            cball((PH x:A->real^N) x,&2 * RR x) SUBSET IMAGE (PH x) (UP x INTER UU x)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN MATCH_MP_TAC MFDC_LOCAL_BALL THEN
    EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `NN = \x:A. {z | z IN UP x /\ (PH x:A->real^N) z IN ball(PH x x,RR x)}` THEN
  ABBREV_TAC `CC = \x:A. {z | z IN UP x /\ (PH x:A->real^N) z IN cball(PH x x,RR x)}` THEN
  SUBGOAL_THEN `!x:A. x IN K
                      ==> open_in top (NN x) /\ x IN NN x /\ NN x SUBSET CC x /\
                          compact_in top (CC x) /\ CC x SUBSET UU x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o check (fun th ->
      can (find_term ((=) `RR:A->real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXPAND_TAC ["NN"; "CC"] THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `cball((PH:A->A->real^N) x x,RR x) SUBSET IMAGE (PH x) (UP x)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `cball((PH:A->A->real^N) x x,&2 * RR x)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_CBALL THEN ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `(UP:A->A->bool) x`; `(PH:A->A->real^N) x`; `(PH:A->A->real^N) x x`;
                     `(RR:A->real) x`] MFDC_CHART_BALL_OPEN) THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[SUBSET; BALL_SUBSET_CBALL];
      MATCH_MP_TAC MFDC_CHART_COMPACT THEN EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN
      REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[COMPACT_CBALL];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `z:A` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(PH:A->A->real^N) x z IN IMAGE (PH x) (UP x INTER UU x)` MP_TAC THENL
       [MATCH_MP_TAC(SET_RULE `!s t (a:real^N). a IN s /\ s SUBSET t ==> a IN t`) THEN
        EXISTS_TAC `cball((PH:A->A->real^N) x x,&2 * RR x)` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(PH:A->A->real^N) x z IN cball (PH x x,RR x)` THEN
        REWRITE_TAC[IN_CBALL] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
      DISCH_THEN(X_CHOOSE_THEN `z':A` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `(UP:A->A->bool) x`; `(PH:A->A->real^N) x`; `z:A`; `z':A`]
        SMOOTH_MANIFOLD_ATLAS_CHART_INJ) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `IMAGE (NN:A->A->bool) K` o CONJUNCT2 o
    GEN_REWRITE_RULE I [compact_in] o check (fun th -> concl th = `compact_in top (K:A->bool)`)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[]; REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`NN:A->A->bool`; `K:A->bool`; `V:(A->bool)->bool`] FINITE_SUBSET_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `Fs:A->bool` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`Fs:A->bool`; `CC:A->A->bool`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  UNDISCH_TAC `(K:A->bool) SUBSET UNIONS V` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN ASM_MESON_TAC[SUBSET]);;

let CMPRF_TERM_SMOOTH = prove
 (`!top atlas (chi:A->real) c c' (v:real^N) L.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        c IN atlas /\ c' IN atlas /\ mfd_smooth atlas (\x. lift(chi x)) /\
        compact_in top L /\ L SUBSET FST c /\
        (!x. x IN topspace top DIFF L ==> chi x = &0)
        ==> smooth_map_on (IMAGE (SND c') (FST c'))
              (\y. chi(chart_inv c' y) % chart_jac c c' (chart_inv c' y) v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c':(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on (IMAGE (SND (c':(A->bool)#(A->real^N))) (FST c'))
                  (\y. lift((chi:A->real)(chart_inv c' y)))` ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x. lift((chi:A->real) x))` THEN
    REWRITE_TAC[mfd_smooth] THEN DISCH_THEN(MP_TAC o SPEC `c':(A->bool)#(A->real^N)`) THEN
    ASM_REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y0:real^N` THEN DISCH_TAC THEN
  ABBREV_TAC `P0 = chart_inv (c':(A->bool)#(A->real^N)) y0` THEN
  SUBGOAL_THEN `(P0:A) IN FST (c':(A->bool)#(A->real^N)) /\ SND c' P0 = y0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "P0" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `(P0:A) IN FST (c:(A->bool)#(A->real^N))` THENL
   [EXISTS_TAC `IMAGE (SND (c':(A->bool)#(A->real^N))) (FST c' INTER FST (c:(A->bool)#(A->real^N)))` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET];
      REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `P0:A` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `\y. drop(lift((chi:A->real)(chart_inv (c':(A->bool)#(A->real^N)) y))) %
                    frechet_derivative (chart_trans (c:(A->bool)#(A->real^N)) c')
                      (at (chart_trans c' c y)) v` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[LIFT_DROP; IN_IMAGE; IN_INTER] THEN X_GEN_TAC `y:real^N` THEN
      DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
      ASM_SIMP_TAC[chart_trans; chart_jac];
      ALL_TAC] THEN
    MATCH_MP_TAC(BETA_RULE(ISPECL
      [`IMAGE (SND (c':(A->bool)#(A->real^N))) (FST c' INTER FST (c:(A->bool)#(A->real^N)))`;
       `\a:real^1 w:real^N. drop a % w`;
       `\y. lift((chi:A->real)(chart_inv (c':(A->bool)#(A->real^N)) y))`;
       `\y. frechet_derivative (chart_trans (c:(A->bool)#(A->real^N)) c')
               (at (chart_trans c' c y)) (v:real^N)`] SMOOTH_MAP_ON_BILINEAR_OPEN)) THEN
    REWRITE_TAC[BILINEAR_DROP_MUL] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (SND (c':(A->bool)#(A->real^N))) (FST c')` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\y. frechet_derivative (chart_trans (c:(A->bool)#(A->real^N)) c')
              (at (chart_trans c' c y)) (v:real^N)) =
      (\z. frechet_derivative (chart_trans c c') (at z) v) o chart_trans c' c`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER FST (c':(A->bool)#(A->real^N)))` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET];
      MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; chart_trans] THEN
      X_GEN_TAC `x:A` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
      REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST(c':(A->bool)#(A->real^N))`; `SND(c':(A->bool)#(A->real^N))`;
                     `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
        CHART_TRANS_SMOOTH) THEN
      ASM_REWRITE_TAC[PAIR];
      MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN CONJ_TAC THENL
       [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
        ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET];
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                       `FST(c':(A->bool)#(A->real^N))`; `SND(c':(A->bool)#(A->real^N))`]
          CHART_TRANS_SMOOTH) THEN
        ASM_REWRITE_TAC[PAIR]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((P0:A) IN L)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `closed_in top (L:A->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `IMAGE (SND (c':(A->bool)#(A->real^N))) (FST c' INTER (topspace top DIFF L))` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_DIFF THEN
    ASM_REWRITE_TAC[OPEN_IN_TOPSPACE];
    REWRITE_TAC[IN_IMAGE; IN_INTER; IN_DIFF] THEN EXISTS_TAC `P0:A` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `\y:real^N. vec 0:real^N` THEN
    REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER; IN_DIFF] THEN X_GEN_TAC `y:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `(chi:A->real) x = &0` (fun th -> REWRITE_TAC[th; VECTOR_MUL_LZERO]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DIFF]]);;

(* ========================================================================= *)
(* The glued field.  Pointwise facts: the triangle inequality                *)
(* for the tangent norm (through an orthonormal frame), and finite bounds.   *)
(* ========================================================================= *)

let CMPRF_TNORM_VSUM_LE = prove
 (`!top atlas (g:A->real^N^N) (y:A) (s:A->bool) (f:A->real^N) (a:A->real).
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ y IN topspace top /\
        FINITE s /\ (!x. x IN s ==> &0 <= a x)
        ==> mfd_tnorm g y (vsum s (\x. a x % f x)) <=
            sum s (\x. a x * mfd_tnorm g y (f x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `y:A`] GEOJ_ONB) THEN
  ASM_REWRITE_TAC[GSYM mfd_orthonormal_frame] THEN
  DISCH_THEN(X_CHOOSE_TAC `E:real^N^N`) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CMPQ_FRAME_INVERTIBLE) THEN
  SUBGOAL_THEN `!v. mfd_tnorm (g:A->real^N^N) y v = norm(matrix_inv(E:real^N^N) ** v)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`g:A->real^N^N`; `y:A`; `E:real^N^N`; `matrix_inv(E:real^N^N) ** v`]
      CMPP_TNORM_FRAME) THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `matrix_inv(E:real^N^N) ** vsum s (\x. (a:A->real) x % (f:A->real^N) x) =
                vsum s (\x. a x % (matrix_inv E ** f x))` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`\v:real^N. matrix_inv(E:real^N^N) ** v`;
                   `\x. (a:A->real) x % (f:A->real^N) x`; `s:A->bool`] LINEAR_VSUM) THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR; o_DEF; MATRIX_VECTOR_MUL_RMUL];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum s (\x:A. norm((a:A->real) x % (matrix_inv(E:real^N^N) ** f x)))` THEN
  ASM_SIMP_TAC[VSUM_NORM] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[NORM_MUL; REAL_ARITH `&0 <= a ==> abs a = a`]);;

let CMPRF_FINITE_BOUNDS = prove
 (`!(s:A->bool) (cc:A->real) (MM:A->real).
        FINITE s /\ ~(s = {}) /\ (!x. x IN s ==> &0 < cc x)
        ==> ?c0 M0. &0 < c0 /\ &0 < M0 /\ !x. x IN s ==> c0 <= cc x /\ MM x <= M0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `IMAGE (cc:A->real) s` INF_FINITE) THEN
  MP_TAC(ISPEC `IMAGE (MM:A->real) s` SUP_FINITE) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE; IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x1:A` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x2:A` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`inf(IMAGE (cc:A->real) s)`; `max (&1) (sup(IMAGE (MM:A->real) s))`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[]; REAL_ARITH_TAC;
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(REAL_ARITH `m <= s ==> m <= max (&1) s`) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `MM:A->real`)) (concl th) && is_forall(concl th))) THEN
      ASM_REWRITE_TAC[]]]);;

(* Normalizing a smooth field by a smooth metric on an open set of real^N.  *)

let CMPRF_SMOOTH_NORMALIZE = prove
 (`!s (G:real^N->real^N^N) (R:real^N->real^N).
        open s /\ smooth_map_on s ((vectorize:real^N^N->real^(N,N)finite_prod) o G) /\
        smooth_map_on s R /\ (!y. y IN s ==> &0 < R y dot (G y ** R y))
        ==> smooth_map_on s (\y. inv(sqrt(R y dot (G y ** R y))) % R y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`; `R:real^N->real^N`]
         LRG_SMOOTH_MATVEC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `R:real^N->real^N`;
                 `\y:real^N. (G:real^N->real^N^N) y ** (R:real^N->real^N) y`]
         SMOOTH_MAP_ON_DOT_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\y:real^N. lift((R:real^N->real^N) y dot
                  ((G:real^N->real^N^N) y ** R y))`] SMOOTH_MAP_ON_LIFT_SQRT) THEN
  ASM_SIMP_TAC[LIFT_DROP] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\y:real^N. lift(sqrt((R:real^N->real^N) y dot
                  ((G:real^N->real^N^N) y ** R y)))`] SMOOTH_MAP_ON_LIFT_INV) THEN
  ASM_SIMP_TAC[LIFT_DROP; SQRT_EQ_0; REAL_LT_IMP_NZ] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\y:real^N. lift(inv(sqrt((R:real^N->real^N) y dot
                  ((G:real^N->real^N^N) y ** R y))))`; `R:real^N->real^N`]
          SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
  ASM_SIMP_TAC[LIFT_DROP]);;

(* Smoothness of the normalized glued field in an arbitrary chart c'.      *)

let CMPRF_GLUE_SMOOTH = prove
 (`!top atlas (g:A->real^N^N) (Fs:A->bool) (vv:A->real^N) (chi:A->A->real)
    (LL:A->A->bool) (W:A->bool) (c':(A->bool)#(A->real^N)) (Zp:A->real^N).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ FINITE Fs /\ Fs SUBSET topspace top /\
        c' IN atlas /\ open_in top W /\
        (!x. x IN Fs
             ==> mfd_smooth atlas (\y. lift(chi x y)) /\ compact_in top (LL x) /\
                 LL x SUBSET FST(chart_at atlas x) /\
                 (!y. y IN topspace top DIFF LL x ==> chi x y = &0)) /\
        (\y. vsum Fs (\x. chi x y %
                chart_jac (chart_at atlas x) (chart_at atlas y) y (vv x))) = Zp /\
        (!y. y IN W ==> &0 < mfd_tnorm g y (Zp y))
        ==> smooth_map_on (IMAGE (SND c') (FST c' INTER W))
              (mfd_vrep atlas (\y. inv(mfd_tnorm g y (Zp y)) % Zp y) c')`,
  INTRO_TAC "!top atlas g Fs vv chi LL W c' Zp; haus smooth riem fin Fst c'at Wo data Zpdef pos" THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c':(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `FST(c':(A->bool)#(A->real^N)) SUBSET topspace top /\
                (W:A->bool) SUBSET topspace top` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  ABBREV_TAC `R = \y:real^N. vsum Fs (\x:A. (chi:A->A->real) x (chart_inv c' y) %
       chart_jac (chart_at atlas x) c' (chart_inv c' y) ((vv:A->real^N) x))` THEN
  SUBGOAL_THEN `open(IMAGE (SND (c':(A->bool)#(A->real^N))) (FST c' INTER W))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (IMAGE (SND (c':(A->bool)#(A->real^N))) (FST c'))
                  (R:real^N->real^N)` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN
    MP_TAC(ISPECL [`IMAGE (SND (c':(A->bool)#(A->real^N))) (FST c')`;
      `\x:A y:real^N. (chi:A->A->real) x (chart_inv c' y) %
          chart_jac (chart_at atlas x) c' (chart_inv c' y) ((vv:A->real^N) x)`;
      `Fs:A->bool`] SMOOTH_MAP_ON_VSUM_OPEN) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    USE_THEN "data" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:A) IN Fs`))) THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MAP_EVERY (MP_TAC o ASSUME) [`(x:A) IN Fs`; `(Fs:A->bool) SUBSET topspace top`] THEN
      SET_TAC[];
      STRIP_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(chi:A->A->real) x`; `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`; `c':(A->bool)#(A->real^N)`;
                   `(vv:A->real^N) x`; `(LL:A->A->bool) x`] CMPRF_TERM_SMOOTH) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (IMAGE (SND (c':(A->bool)#(A->real^N))) (FST c'))
                  ((vectorize:real^N^N->real^(N,N)finite_prod) o
                   metric_local atlas c' (g:A->real^N^N))` ASSUME_TAC THENL
   [USE_THEN "riem" (MP_TAC o SPEC `c':(A->bool)#(A->real^N)` o
                     REWRITE_RULE[riemannian_metric]) THEN
    ASM_REWRITE_TAC[metric_field] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN IMAGE (SND (c':(A->bool)#(A->real^N))) (FST c' INTER W)
        ==> mfd_vrep atlas (\y. inv(mfd_tnorm (g:A->real^N^N) y ((Zp:A->real^N) y)) % Zp y)
                     c' y =
              inv(sqrt((R:real^N->real^N) y dot (metric_local atlas c' g y ** R y))) % R y /\
            &0 < R y dot (metric_local atlas c' g y ** R y)`
  (LABEL_TAC "pt") THENL
   [X_GEN_TAC `y:real^N` THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `P:A` (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `chart_inv (c':(A->bool)#(A->real^N)) (SND c' (P:A)) = P` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(P:A) IN topspace top` ASSUME_TAC THENL
     [MAP_EVERY (MP_TAC o ASSUME) [`(P:A) IN FST(c':(A->bool)#(A->real^N))`;
                                  `FST(c':(A->bool)#(A->real^N)) SUBSET topspace top`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `c':(A->bool)#(A->real^N)`; `P:A`] CMPRF_JAC_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lin1") (CONJUNCTS_THEN2 (LABEL_TAC "lin2")
      (CONJUNCTS_THEN2 (LABEL_TAC "inv1") (CONJUNCTS_THEN2 (LABEL_TAC "inv2")
       (LABEL_TAC "met"))))) THEN
    SUBGOAL_THEN `chart_jac (chart_at atlas P) c' (P:A) ((Zp:A->real^N) P) =
                  (R:real^N->real^N) (SND c' P)` (LABEL_TAC "i") THENL
     [EXPAND_TAC "Zp" THEN EXPAND_TAC "R" THEN
      REWRITE_TAC[ASSUME `chart_inv (c':(A->bool)#(A->real^N)) (SND c' (P:A)) = P`] THEN
      MP_TAC(ISPECL [`chart_jac (chart_at atlas P) (c':(A->bool)#(A->real^N)) (P:A)`;
                     `\x:A. (chi:A->A->real) x P %
                        chart_jac (chart_at atlas x) (chart_at atlas P) P ((vv:A->real^N) x)`;
                     `Fs:A->bool`] LINEAR_VSUM) THEN
      USE_THEN "lin2" (fun th -> REWRITE_TAC[th; o_DEF; ASSUME `FINITE(Fs:A->bool)`]) THEN
      DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      USE_THEN "lin2" (fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
      ASM_CASES_TAC `(chi:A->A->real) x P = &0` THEN
      ASM_REWRITE_TAC[VECTOR_MUL_LZERO] THEN AP_TERM_TAC THEN
      USE_THEN "data" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:A) IN Fs`))) THEN STRIP_TAC THEN
      SUBGOAL_THEN `(P:A) IN FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))` ASSUME_TAC THENL
       [MAP_EVERY (MP_TAC o ASSUME)
         [`~((chi:A->A->real) x P = &0)`; `(P:A) IN topspace top`;
          `!y. y IN topspace top DIFF (LL:A->A->bool) x ==> (chi:A->A->real) x y = &0`;
          `(LL:A->A->bool) x SUBSET FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`] THEN
        SET_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        MAP_EVERY (MP_TAC o ASSUME) [`(x:A) IN Fs`; `(Fs:A->bool) SUBSET topspace top`] THEN
        SET_TAC[];
        STRIP_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `P:A`] CHART_AT) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
        `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
        `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
        `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (P:A))`;
        `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (P:A))`;
        `FST(c':(A->bool)#(A->real^N))`; `SND(c':(A->bool)#(A->real^N))`; `P:A`]
        CHART_JAC_CHAIN) THEN
      ASM_REWRITE_TAC[PAIR; IN_INTER] THEN
      DISCH_THEN(MP_TAC o C AP_THM `(vv:A->real^N) x`) THEN REWRITE_TAC[o_THM];
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) P ((Zp:A->real^N) P) =
                  sqrt((R:real^N->real^N) (SND c' P) dot
                       (metric_local atlas c' g (SND c' (P:A)) ** R (SND c' P)))`
    (LABEL_TAC "ii") THENL
     [REWRITE_TAC[mfd_tnorm] THEN AP_TERM_TAC THEN
      USE_THEN "i" (fun th -> REWRITE_TAC[SYM th]) THEN
      USE_THEN "met" (MP_TAC o SPECL
        [`chart_jac (chart_at atlas P) c' (P:A) ((Zp:A->real^N) P)`;
         `chart_jac (chart_at atlas P) c' (P:A) ((Zp:A->real^N) P)`]) THEN
      USE_THEN "inv1" (fun th -> REWRITE_TAC[th]);
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[mfd_vrep;
                  ASSUME `chart_inv (c':(A->bool)#(A->real^N)) (SND c' (P:A)) = P`] THEN
      USE_THEN "lin2" (fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
      USE_THEN "i" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "ii" (fun th -> REWRITE_TAC[th]);
      ONCE_REWRITE_TAC[GSYM SQRT_LT_0] THEN USE_THEN "ii" (SUBST1_TAC o SYM) THEN
      USE_THEN "pos" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `\y:real^N. inv(sqrt((R:real^N->real^N) y dot
                (metric_local atlas c' (g:A->real^N^N) y ** R y))) % R y` THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    USE_THEN "pt" (fun th -> REWRITE_TAC[CONJUNCT1(MATCH_MP th (ASSUME
      `(y:real^N) IN IMAGE (SND (c':(A->bool)#(A->real^N))) (FST c' INTER W)`))]);
    MATCH_MP_TAC CMPRF_SMOOTH_NORMALIZE THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (SND (c':(A->bool)#(A->real^N))) (FST c')` THEN
      ASM_REWRITE_TAC[ETA_AX] THEN SET_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (SND (c':(A->bool)#(A->real^N))) (FST c')` THEN
      ASM_REWRITE_TAC[ETA_AX] THEN SET_TAC[];
      USE_THEN "pt" (fun th -> MESON_TAC[th])]]);;

(* The glued field and its properties, from the local data on a finite     *)
(* index set Fs: fields V x (constant vv x in chart_at x) obtuse on UU x,   *)
(* cutoffs chi x equal to 1 on VV x and vanishing off a compact LL x in     *)
(* UU x; K is covered by the VV x.                                          *)

let CMPRF_GLUE = prove
 (`!top atlas (g:A->real^N^N) (p:A) K (Fs:A->bool) (vv:A->real^N) (UU:A->A->bool)
    (cc:A->real) (MM:A->real) (chi:A->A->real) (LL:A->A->bool) (VV:A->A->bool).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ p IN topspace top /\
        (!x. x IN K ==> mfd_joinable (top,atlas) p x /\ ~(x = p)) /\
        FINITE Fs /\ ~(Fs = {}) /\ Fs SUBSET topspace top /\
        K SUBSET UNIONS (IMAGE VV Fs) /\
        (!x. x IN Fs
             ==> UU x SUBSET FST(chart_at atlas x) /\ &0 < cc x /\
                 (!y. y IN UU x
                      ==> mfd_tnorm g y
                            (chart_jac (chart_at atlas x) (chart_at atlas y) y (vv x)) <= MM x) /\
                 (!y w. y IN UU x /\ mfd_exp (top,atlas) g y w = p /\
                        mfd_tnorm g y w = mfd_dist (top,atlas) g y p
                        ==> chart_jac (chart_at atlas x) (chart_at atlas y) y (vv x) dot
                            (g y ** w) <= --(cc x) * mfd_tnorm g y w) /\
                 mfd_smooth atlas (\y. lift(chi x y)) /\ (!y. &0 <= chi x y) /\
                 open_in top (VV x) /\ (!y. y IN VV x ==> chi x y = &1) /\
                 compact_in top (LL x) /\ LL x SUBSET UU x /\
                 (!y. y IN topspace top DIFF LL x ==> chi x y = &0))
        ==> ?W Z c. open_in top W /\ K SUBSET W /\ &0 < c /\
                    (!c'. c' IN atlas
                          ==> smooth_map_on (IMAGE (SND c') (FST c' INTER W))
                                            (mfd_vrep atlas Z c')) /\
                    (!x. x IN W ==> Z x dot (g x ** Z x) = &1) /\
                    !x v. x IN W /\ v IN mfd_exp_dom (top,atlas) g x /\
                          mfd_exp (top,atlas) g x v = p /\
                          mfd_tnorm g x v = mfd_dist (top,atlas) g x p
                          ==> Z x dot (g x ** v) <= --c * mfd_tnorm g x v`,
  INTRO_TAC "!top atlas g p K Fs vv UU cc MM chi LL VV; haus smooth riem comp ptop Kj fin ne Fst cov data" THEN
  MP_TAC(ISPECL [`Fs:A->bool`; `cc:A->real`; `MM:A->real`] CMPRF_FINITE_BOUNDS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c0:real` (X_CHOOSE_THEN `M0:real` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `Zp = \y:A. vsum Fs (\x:A. (chi:A->A->real) x y %
                        chart_jac (chart_at atlas x) (chart_at atlas y) y ((vv:A->real^N) x))` THEN
  ABBREV_TAC `Sm = \y:A. sum Fs (\x:A. (chi:A->A->real) x y)` THEN
  ABBREV_TAC `W = (UNIONS (IMAGE (VV:A->A->bool) Fs) INTER
                   {y | mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) p y}) DIFF {p:A}` THEN
  SUBGOAL_THEN `!x y. x IN Fs /\ y IN topspace top /\ ~((chi:A->A->real) x y = &0)
                      ==> y IN (UU:A->A->bool) x`
  (LABEL_TAC "supp") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "data" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:A) IN Fs`))) THEN
    STRIP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (W:A->bool) /\ (K:A->bool) SUBSET W /\ W SUBSET topspace top`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_DIFF THEN CONJ_TAC THENL
       [MATCH_MP_TAC OPEN_IN_INTER THEN CONJ_TAC THENL
         [MATCH_MP_TAC OPEN_IN_UNIONS THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
          X_GEN_TAC `x:A` THEN DISCH_TAC THEN
          USE_THEN "data" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:A) IN Fs`))) THEN
          SIMP_TAC[];
          MATCH_MP_TAC MFD_JOINABLE_OPEN THEN ASM_REWRITE_TAC[]];
        MP_TAC(ISPEC `top:A topology` T1_SPACE_CLOSED_IN_SING) THEN
        ASM_SIMP_TAC[HAUSDORFF_IMP_T1_SPACE]];
      REWRITE_TAC[SUBSET; IN_DIFF; IN_INTER; IN_ELIM_THM; IN_SING] THEN
      X_GEN_TAC `y:A` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN ASM SET_TAC[];
      REWRITE_TAC[SUBSET; IN_DIFF; IN_INTER; IN_ELIM_THM] THEN
      MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN W ==> &1 <= (Sm:A->real) y` (LABEL_TAC "S1") THENL
   [X_GEN_TAC `y:A` THEN EXPAND_TAC "W" THEN
    REWRITE_TAC[IN_DIFF; IN_INTER; IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC)
      ASSUME_TAC) ASSUME_TAC) THEN
    USE_THEN "data" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:A) IN Fs`))) THEN
    STRIP_TAC THEN EXPAND_TAC "Sm" THEN
    MP_TAC(ISPECL [`\x:A. (chi:A->A->real) x y`; `Fs:A->bool`; `x:A`] SUM_DELETE) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`Fs DELETE (x:A)`] (ISPEC `\x:A. (chi:A->A->real) x y` (GEN `f:A->real` SUM_POS_LE))) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_DELETE] THEN X_GEN_TAC `x':A` THEN STRIP_TAC THEN
      USE_THEN "data" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x':A) IN Fs`))) THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(chi:A->A->real) x y = &1` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y w. y IN topspace top /\ mfd_exp (top,atlas) (g:A->real^N^N) y w = p /\
          mfd_tnorm g y w = mfd_dist (top,atlas) g y p
          ==> (Zp:A->real^N) y dot (g y ** w) <=
              --((Sm:A->real) y * c0) * mfd_tnorm g y w`
  (LABEL_TAC "obt") THENL
   [REPEAT STRIP_TAC THEN MAP_EVERY EXPAND_TAC ["Zp"; "Sm"] THEN
    SIMP_TAC[DOT_LSUM; DOT_LMUL; ASSUME `FINITE (Fs:A->bool)`] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `y:A`] GEOD_TNORM_BASIC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum Fs (\x:A. (chi:A->A->real) x y * (--c0 * mfd_tnorm (g:A->real^N^N) y w))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
      ASM_CASES_TAC `(chi:A->A->real) x y = &0` THENL
       [ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_LE_REFL]; ALL_TAC] THEN
      SUBGOAL_THEN `(y:A) IN (UU:A->A->bool) x` ASSUME_TAC THENL
       [USE_THEN "supp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "data" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(x:A) IN Fs`))) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `--((cc:A->real) x) * mfd_tnorm (g:A->real^N^N) y w` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `cc:A->real`)) (concl th) && is_forall(concl th))) THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[REAL_MUL_LNEG; REAL_LE_NEG2] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_SIMP_TAC[]];
      REWRITE_TAC[SUM_RMUL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN topspace top
        ==> mfd_tnorm (g:A->real^N^N) y ((Zp:A->real^N) y) <= (Sm:A->real) y * M0`
  (LABEL_TAC "nb") THENL
   [REPEAT STRIP_TAC THEN MAP_EVERY EXPAND_TAC ["Zp"; "Sm"] THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum Fs (\x:A. (chi:A->A->real) x y *
                  mfd_tnorm (g:A->real^N^N) y
                    (chart_jac (chart_at atlas x) (chart_at atlas y) y ((vv:A->real^N) x)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CMPRF_TNORM_VSUM_LE THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      USE_THEN "data" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:A) IN Fs`))) THEN SIMP_TAC[];
      REWRITE_TAC[GSYM SUM_RMUL] THEN MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      ASM_CASES_TAC `(chi:A->A->real) x y = &0` THENL
       [ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_LE_REFL]; ALL_TAC] THEN
      SUBGOAL_THEN `(y:A) IN (UU:A->A->bool) x` ASSUME_TAC THENL
       [USE_THEN "supp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "data" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(x:A) IN Fs`))) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(MM:A->real) x` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN W ==> &0 < mfd_tnorm (g:A->real^N^N) y ((Zp:A->real^N) y)`
  (LABEL_TAC "pos") THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:A) IN topspace top /\
                  mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) y p /\ ~(y = p)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(y:A) IN W` THEN EXPAND_TAC "W" THEN
      REWRITE_TAC[IN_DIFF; IN_INTER; IN_ELIM_THM; IN_SING] THEN
      MESON_TAC[MFD_JOINABLE_IN_TOPSPACE; MFD_JOINABLE_SYM; ASSUME `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool)`];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `y:A`; `p:A`] MFD_COMPLETE_MINIMIZING_GEODESIC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `&0 < mfd_dist (top,atlas) (g:A->real^N^N) y p` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `y:A`; `p:A`] MFD_DIST_EQ_0) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `y:A`; `p:A`] MFD_DIST_POS_LE) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "obt" (fun th -> MP_TAC(MATCH_MP th (CONJ (ASSUME `(y:A) IN topspace top`)
      (CONJ (ASSUME `mfd_exp (top,atlas) (g:A->real^N^N) y w = p`)
            (ASSUME `mfd_tnorm (g:A->real^N^N) y w = mfd_dist (top,atlas) g y p`))))) THEN
    USE_THEN "S1" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(y:A) IN W`))) THEN
    ASM_CASES_TAC `(Zp:A->real^N) y = vec 0` THENL
     [ASM_REWRITE_TAC[DOT_LZERO] THEN DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < a * t ==> &0 <= --a * t ==> b`) THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `y:A`; `(Zp:A->real^N) y`] GEOD_TNORM_EQ_0) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `y:A`] GEOD_TNORM_BASIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPEC `(Zp:A->real^N) y` (ASSUME `!v. &0 <= mfd_tnorm (g:A->real^N^N) y v`)) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`W:A->bool`; `\y:A. inv(mfd_tnorm (g:A->real^N^N) y ((Zp:A->real^N) y)) % Zp y`;
    `c0 / M0`] THEN
  ASM_SIMP_TAC[REAL_LT_DIV] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `c':(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `Fs:A->bool`; `vv:A->real^N`; `chi:A->A->real`; `LL:A->A->bool`;
                   `W:A->bool`; `c':(A->bool)#(A->real^N)`; `Zp:A->real^N`]
                  CMPRF_GLUE_SMOOTH) THEN
    DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    USE_THEN "data" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:A) IN Fs`))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(UU:A->A->bool) x` THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    USE_THEN "pos" (fun th -> ASSUME_TAC(MATCH_MP th (ASSUME `(y:A) IN W`))) THEN
    SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `y:A`] GEOD_TNORM_BASIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN
    FIRST_X_ASSUM((fun th -> REWRITE_TAC[GSYM th]) o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> try fst(dest_const t) = "real_pow"
        with Failure _ -> false)) (concl th))) THEN
    UNDISCH_TAC `&0 < mfd_tnorm (g:A->real^N^N) y ((Zp:A->real^N) y)` THEN
    CONV_TAC REAL_FIELD;
    MAP_EVERY X_GEN_TAC [`y:A`; `w:real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "pos" (fun th -> ASSUME_TAC(MATCH_MP th (ASSUME `(y:A) IN W`))) THEN
    USE_THEN "obt" (fun th -> ASSUME_TAC(MATCH_MP th (CONJ (ASSUME `(y:A) IN topspace top`)
      (CONJ (ASSUME `mfd_exp (top,atlas) (g:A->real^N^N) y w = p`)
            (ASSUME `mfd_tnorm (g:A->real^N^N) y w = mfd_dist (top,atlas) g y p`))))) THEN
    USE_THEN "nb" (fun th -> ASSUME_TAC(MATCH_MP th (ASSUME `(y:A) IN topspace top`))) THEN
    USE_THEN "S1" (fun th -> ASSUME_TAC(MATCH_MP th (ASSUME `(y:A) IN W`))) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `y:A`] GEOD_TNORM_BASIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN
    UNDISCH_TAC `mfd_tnorm (g:A->real^N^N) y w = mfd_dist (top,atlas) g y p` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `&0 <= mfd_tnorm (g:A->real^N^N) y w` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(mfd_tnorm (g:A->real^N^N) y ((Zp:A->real^N) y)) *
      --(((c0 / M0) * mfd_tnorm g y w) * mfd_tnorm g y (Zp y))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `--(Sm (y:A) * c0) * mfd_tnorm (g:A->real^N^N) y w` THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `((c0 / M0) * mfd_tnorm (g:A->real^N^N) y w) * mfd_tnorm g y ((Zp:A->real^N) y) <=
                    ((c0 / M0) * mfd_tnorm g y w) * (Sm (y:A) * M0)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_DIV; REAL_LT_IMP_LE]; ALL_TAC] THEN
      SUBGOAL_THEN `((c0 / M0) * mfd_tnorm (g:A->real^N^N) y w) * (Sm (y:A) * M0) =
                    Sm y * c0 * mfd_tnorm g y w` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < M0` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      UNDISCH_TAC `&0 < mfd_tnorm (g:A->real^N^N) y ((Zp:A->real^N) y)` THEN
      CONV_TAC REAL_FIELD]]);;

(* ========================================================================= *)
(* The regular field near a compact set of regular points                   *)
(* (general A and N), then CMP_R6_REGULAR_FIELD.                            *)
(* ========================================================================= *)

let CMPRF_REGULAR_FIELD_GEN = prove
 (`!top atlas (g:A->real^N^N) (p:A) K.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ p IN topspace top /\
        compact_in top K /\ (!x. x IN K ==> mfd_joinable (top,atlas) p x) /\
        (!x. x IN K
             ==> ?v. !w. w IN mfd_exp_dom (top,atlas) g x /\
                         mfd_exp (top,atlas) g x w = p /\
                         mfd_tnorm g x w = mfd_dist (top,atlas) g x p
                         ==> v dot (g x ** w) < &0)
        ==> ?W Z c. open_in top W /\ K SUBSET W /\ &0 < c /\
                    (!c'. c' IN atlas
                          ==> smooth_map_on (IMAGE (SND c') (FST c' INTER W))
                                            (mfd_vrep atlas Z c')) /\
                    (!x. x IN W ==> Z x dot (g x ** Z x) = &1) /\
                    !x v. x IN W /\ v IN mfd_exp_dom (top,atlas) g x /\
                          mfd_exp (top,atlas) g x v = p /\
                          mfd_tnorm g x v = mfd_dist (top,atlas) g x p
                          ==> Z x dot (g x ** v) <= --c * mfd_tnorm g x v`,
  INTRO_TAC "!top atlas g p K; haus smooth riem comp ptop Kc Kj Kr" THEN
  SUBGOAL_THEN `(K:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE]; ALL_TAC] THEN
  ASM_CASES_TAC `K:A->bool = {}` THENL
   [MAP_EVERY EXISTS_TAC [`{}:A->bool`; `\x:A. vec 0:real^N`; `&1`] THEN
    ASM_REWRITE_TAC[OPEN_IN_EMPTY; EMPTY_SUBSET; NOT_IN_EMPTY; INTER_EMPTY;
                    IMAGE_CLAUSES; REAL_LT_01] THEN
    X_GEN_TAC `c':(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `\y:real^N. vec 0:real^N` THEN
    REWRITE_TAC[NOT_IN_EMPTY; SMOOTH_MAP_ON_CONST];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((p:A) IN K)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    USE_THEN "Kr" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(p:A) IN K`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N` (MP_TAC o SPEC `vec 0:real^N`)) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`] MFD_EXP_DOM) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`] MFD_DIST_REFL) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`] GEOD_TNORM_BASIC) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th))) THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_LT_REFL];
    ALL_TAC] THEN
  USE_THEN "Kr" (MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `vv:A->real^N` (LABEL_TAC "vv")) THEN
  SUBGOAL_THEN
   `!x0:A. x0 IN K
           ==> ?U c M. open_in top U /\ x0 IN U /\ U SUBSET FST(chart_at atlas x0) /\
                       &0 < c /\
                       (!x. x IN U
                            ==> mfd_tnorm (g:A->real^N^N) x
                                  (chart_jac (chart_at atlas x0) (chart_at atlas x) x
                                             ((vv:A->real^N) x0)) <= M) /\
                       !x w. x IN U /\ mfd_exp (top,atlas) g x w = p /\
                             mfd_tnorm g x w = mfd_dist (top,atlas) g x p
                             ==> chart_jac (chart_at atlas x0) (chart_at atlas x) x
                                           (vv x0) dot (g x ** w) <=
                                 --c * mfd_tnorm g x w`
  MP_TAC THENL
   [X_GEN_TAC `x0:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`; `x0:A`; `(vv:A->real^N) x0`] CMPRF_LOCAL) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC;
        MAP_EVERY (MP_TAC o ASSUME) [`(x0:A) IN K`; `(K:A->bool) SUBSET topspace top`] THEN
        SET_TAC[];
        USE_THEN "vv" (fun th -> ACCEPT_TAC(MATCH_MP th (ASSUME `(x0:A) IN K`)))];
      DISCH_THEN ACCEPT_TAC];
    DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
    DISCH_THEN(X_CHOOSE_THEN `UU:A->A->bool` (X_CHOOSE_THEN `cc:A->real`
      (X_CHOOSE_THEN `MM:A->real` (LABEL_TAC "loc"))))] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `K:A->bool`; `UU:A->A->bool`] CMPRF_COVER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    USE_THEN "loc" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:A) IN K`))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Fs:A->bool` (X_CHOOSE_THEN `CC:A->A->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "CC") ASSUME_TAC))))) THEN
  SUBGOAL_THEN
   `!x:A. x IN Fs
          ==> ?chi:A->real V L.
                mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\y. lift(chi y)) /\
                (!y. &0 <= chi y /\ chi y <= &1) /\
                open_in top V /\ (CC:A->A->bool) x SUBSET V /\
                (!y. y IN V ==> chi y = &1) /\
                compact_in top L /\ L SUBSET (UU:A->A->bool) x /\
                (!y. y IN topspace top DIFF L ==> chi y = &0)`
  MP_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:A) IN K` ASSUME_TAC THENL
     [MAP_EVERY (MP_TAC o ASSUME) [`(x:A) IN Fs`; `(Fs:A->bool) SUBSET K`] THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "loc" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:A) IN K`))) THEN STRIP_TAC THEN
    USE_THEN "CC" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:A) IN Fs`))) THEN STRIP_TAC THEN
    MATCH_MP_TAC MFD_SMOOTH_CUTOFF THEN ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
    DISCH_THEN(X_CHOOSE_THEN `chi:A->A->real` (X_CHOOSE_THEN `VV:A->A->bool`
      (X_CHOOSE_THEN `LL:A->A->bool` (LABEL_TAC "cut"))))] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `p:A`; `K:A->bool`; `Fs:A->bool`; `vv:A->real^N`; `UU:A->A->bool`;
                 `cc:A->real`; `MM:A->real`; `chi:A->A->real`; `LL:A->A->bool`;
                 `VV:A->A->bool`] CMPRF_GLUE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN CONJ_TAC THENL
       [USE_THEN "Kj" (fun th -> ACCEPT_TAC(MATCH_MP th (ASSUME `(x:A) IN K`)));
        DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC `~((p:A) IN K)` THEN ASM_REWRITE_TAC[]];
      FIRST_ASSUM ACCEPT_TAC;
      DISCH_TAC THEN
      UNDISCH_TAC `(K:A->bool) SUBSET UNIONS (IMAGE (CC:A->A->bool) Fs)` THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; UNIONS_0; SUBSET_EMPTY];
      MAP_EVERY (MP_TAC o ASSUME) [`(Fs:A->bool) SUBSET K`; `(K:A->bool) SUBSET topspace top`] THEN
      SET_TAC[];
      SUBGOAL_THEN `!x:A. x IN Fs ==> (CC:A->A->bool) x SUBSET (VV:A->A->bool) x` MP_TAC THENL
       [USE_THEN "cut" (fun th -> MESON_TAC[th]); ALL_TAC] THEN
      UNDISCH_TAC `(K:A->bool) SUBSET UNIONS (IMAGE (CC:A->A->bool) Fs)` THEN
      SET_TAC[];
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(x:A) IN K` ASSUME_TAC THENL
       [MAP_EVERY (MP_TAC o ASSUME) [`(x:A) IN Fs`; `(Fs:A->bool) SUBSET K`] THEN SET_TAC[];
        ALL_TAC] THEN
      USE_THEN "loc" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:A) IN K`))) THEN
      USE_THEN "cut" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:A) IN Fs`))) THEN
      DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
      ASM_SIMP_TAC[]];
    DISCH_THEN ACCEPT_TAC]);;

(* The regular-field theorem as a statement constant (used in            *)
(* pc_soul_ball), proved from CMPRF_REGULAR_FIELD_GEN.                   *)

let CMP_R6_REGULAR_FIELD_STATEMENT = new_definition
 `CMP_R6_REGULAR_FIELD_STATEMENT (w:B->bool) <=>
    !top atlas g p K.
       hausdorff_space top /\ smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
       riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ p IN topspace top /\
       compact_in top K /\ (!x. x IN K ==> mfd_joinable (top,atlas) p x) /\
       (!x. x IN K ==> p2b_dist_regular (top,atlas) g p x)
       ==> ?W Z c. open_in top W /\ K SUBSET W /\ &0 < c /\
                   (!c'. c' IN atlas
                         ==> smooth_map_on (IMAGE (SND c') (FST c' INTER W))
                                           (mfd_vrep atlas Z c')) /\
                   (!x. x IN W ==> Z x dot (g x ** Z x) = &1) /\
                   !x v. x IN W /\ v IN mfd_exp_dom (top,atlas) g x /\
                         mfd_exp (top,atlas) g x v = p /\
                         mfd_tnorm g x v = mfd_dist (top,atlas) g x p
                         ==> Z x dot (g x ** v) <= --c * mfd_tnorm g x v`;;

let CMP_R6_REGULAR_FIELD = prove
 (`!w:B->bool. CMP_R6_REGULAR_FIELD_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[CMP_R6_REGULAR_FIELD_STATEMENT; p2b_dist_regular] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CMPRF_REGULAR_FIELD_GEN THEN
  ASM_REWRITE_TAC[]);;

