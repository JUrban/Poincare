(* ========================================================================= *)
(* Unit pc_rfa_mfd: the curvature norm on a manifold: chart independence of  *)
(* |Rm|^2, the manifold form of the evolution inequality of |Rm|^2 (the case *)
(* m = 0 of the evolution of |nabla^m Rm|^2) and the regularity of |Rm|^2    *)
(* along a Ricci flow.                                                       *)
(* ========================================================================= *)

needs "src/pc_lrg_flowsmooth.ml";;
needs "src/pc_rfa_rmnorm.ml";;
needs "src/pc_rfa_sec.ml";;
needs "src/pc_rfa_maxp.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The curvature norm read in the preferred chart (rfa_rmd2), locality, and  *)
(* chart independence.                                                       *)
(* ========================================================================= *)

let rfa_rmd2 = new_definition
 `rfa_rmd2 l (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (x:A) =
    lrm_deriv_norm2 l (metric_local atlas (chart_at atlas x) g)
                    (SND(chart_at atlas x) x)`;;

let RFA_LLAP_LOCAL = prove
 (`!(G:real^N->real^N^N) f g s y.
        open s /\ y IN s /\ (!z. z IN s ==> f z = g z)
        ==> llap G f y = llap G g y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[llap] THEN
  SUBGOAL_THEN
   `!z. z IN s ==> frechet_derivative (\w. lift((f:real^N->real) w)) (at z) =
                   frechet_derivative (\w. lift(g w)) (at z)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. frechet_derivative
          (\z. frechet_derivative (\w. lift((f:real^N->real) w)) (at z) (basis j)) (at y) =
        frechet_derivative
          (\z. frechet_derivative (\w. lift(g w)) (at z) (basis j)) (at y)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[]);;

let RFA_LRM_NORM2_0_LOCAL = prove
 (`!(G1:real^N->real^N^N) G2 s y.
        open s /\ y IN s /\ (!z. z IN s ==> G1 z = G2 z)
        ==> lrm_deriv_norm2 0 G1 y = lrm_deriv_norm2 0 G2 y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lrm_deriv_norm2; lnabla_iter; ADD_CLAUSES] THEN
  MATCH_MP_TAC LRG_LTNORM2_EQ THEN ASM_SIMP_TAC[] THEN
  GEN_TAC THEN REWRITE_TAC[lrm4] THEN ASM_SIMP_TAC[] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC LRIEMANN_LOCAL THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let RFA_RMD2_0_CHART = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) c x.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        c IN atlas /\ x IN FST c
        ==> rfa_rmd2 0 atlas g x = lrm_deriv_norm2 0 (metric_local atlas c g) (SND c x)`,
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `g:A->real^N^N`; `U:A->bool`; `phi:A->real^N`; `x:A`] THEN
  STRIP_TAC THEN REWRITE_TAC[rfa_rmd2] THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`,
           `cc:(A->bool)#(A->real^N)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `psi:A->real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in top (U:A->bool) /\ open_in top (V:A->bool)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART);
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `V:A->bool`; `psi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART)] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (phi:A->real^N) (U INTER V)) /\
                open(IMAGE (psi:A->real^N) (U INTER V))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THENL
     [EXISTS_TAC `U:A->bool`; EXISTS_TAC `V:A->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_INTER] THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lrm_deriv_norm2 0
                (mpullback (chart_trans (U,phi) (V,psi))
                           (metric_local atlas (V,psi) (g:A->real^N^N))) (phi(x:A))` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`0`; `IMAGE (psi:A->real^N) (U INTER V)`;
                   `IMAGE (phi:A->real^N) (U INTER V)`;
                   `chart_trans (U:A->bool,phi:A->real^N) (V,psi)`;
                   `chart_trans (V:A->bool,psi:A->real^N) (U,phi)`;
                   `metric_local atlas (V:A->bool,psi:A->real^N) (g:A->real^N^N)`;
                   `(phi:A->real^N) x`] LRM_DERIV_NORM2_PULLBACK) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
        EXISTS_TAC `IMAGE (psi:A->real^N) V` THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL
         [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^N))->bool)
                                         (g:A->real^N^N)` THEN
          REWRITE_TAC[riemannian_metric] THEN
          DISCH_THEN(MP_TAC o SPEC `(V:A->bool,psi:A->real^N)`) THEN
          ASM_REWRITE_TAC[FST; SND];
          SET_TAC[]];
        MATCH_MP_TAC CHART_TRANS_DIFFEO THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[IN_INTER]];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CHART_TRANS_AT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC RFA_LRM_NORM2_0_LOCAL THEN
    EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER V)` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[IN_INTER];
      REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `x':A` THEN STRIP_TAC THEN
      MATCH_MP_TAC METRIC_LOCAL_TRANS THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[IN_INTER]]]);;

(* The evolution inequality of |Rm|^2 on a manifold. *)

let RFA_RMD2_EVOLUTION_0 = prove
 (`?C. &0 <= C /\
     !(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b
      (g:real->A->real^N^N) t x.
        ricci_flow_on (top,atlas) a b g /\ a < t /\ t < b /\ x IN topspace top
        ==> ?d. ((\s. rfa_rmd2 0 atlas (g s) x) has_real_derivative d) (atreal t) /\
                d <= rfa_lap atlas (g t) (rfa_rmd2 0 atlas (g t)) x -
                     &2 * rfa_rmd2 (0 + 1) atlas (g t) x +
                     C * sqrt(rfa_rmd2 0 atlas (g t) x) *
                     sum(0..0) (\i. sqrt(rfa_rmd2 i atlas (g t) x) *
                                    sqrt(rfa_rmd2 (0 - i) atlas (g t) x))`,
  X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "A10"))
    (INST_TYPE [`:N`,`:N`] RFA_LRM_NORM2_EVOLUTION_0) THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `a:real`; `b:real`; `g:real->A->real^N^N`; `t:real`; `x:A`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) atlas /\
                riemannian_metric atlas ((g:real->A->real^N^N) t)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `g:real->A->real^N^N`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`]
         LRG_RICCI_FLOW_ON_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  USE_THEN "A10" (MP_TAC o SPECL
   [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
           (FST(chart_at atlas x))`;
    `a:real`; `b:real`;
    `\t. metric_local (atlas:((A->bool)#(A->real^N))->bool) (chart_at atlas (x:A))
                      ((g:real->A->real^N^N) t)`;
    `t:real`; `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN REWRITE_TAC[rfa_lap] THEN
  SUBGOAL_THEN
   `llap (metric_local atlas (chart_at atlas x) ((g:real->A->real^N^N) t))
         (\y. rfa_rmd2 0 atlas (g t) (chart_inv (chart_at atlas (x:A)) y))
         (SND(chart_at atlas x) x) =
    llap (metric_local atlas (chart_at atlas x) (g t))
         (lrm_deriv_norm2 0 (metric_local atlas (chart_at atlas x) (g t)))
         (SND(chart_at atlas x) x)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC RFA_LLAP_LOCAL THEN
    EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                      (FST(chart_at atlas x))` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN BETA_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(g:real->A->real^N^N) t`;
                   `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`;
                   `chart_inv (chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) z`]
           RFA_RMD2_0_CHART) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[rfa_rmd2] THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Joint smoothness in (t,y) of |Rm|^2 for smooth families of                *)
(* metrics (via pc_lrg_flowsmooth), and of rfa_rmd2 0 read in any chart     *)
(* along a Ricci flow.                                                       *)
(* ========================================================================= *)

let RFA_LSMOOTH_LRM4 = prove
 (`!U ta tb (G:real->real^N->real^N^N) u.
     lrg_lsmooth U ta tb G
     ==> smooth_map_on (interval(lift ta,lift tb) PCROSS U)
           (\z. lift(lrm4 (G (drop(fstcart z))) (sndcart z) u))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
  REWRITE_TAC[lrm4] THEN
  SUBGOAL_THEN
   `(\z. lift((u:num->real^N) 3 dot
              ((G:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z) **
               lriemann (G (drop(fstcart z))) (sndcart z) (u 1) (u 2) (u 4)))) =
    (\x. lift(u 3 dot x)) o
    (\z. G (drop(fstcart z)) (sndcart z) **
         lriemann (G (drop(fstcart z))) (sndcart z) (u 1) (u 2) (u 4))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[LINEAR_LIFT_DOT] THEN
  MATCH_MP_TAC LRG_SMOOTH_MATVEC THEN ASM_SIMP_TAC[LRG_LSMOOTH_LRIEMANN] THEN
  ASM_REWRITE_TAC[o_DEF]);;

let RFA_LSMOOTH_LRM_NORM2_0 = prove
 (`!U ta tb (G:real->real^N->real^N^N).
     lrg_lsmooth U ta tb G
     ==> smooth_map_on (interval(lift ta,lift tb) PCROSS U)
           (\z. lift(lrm_deriv_norm2 0 (G (drop(fstcart z))) (sndcart z)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
  REWRITE_TAC[lrm_deriv_norm2; lnabla_iter; ADD_CLAUSES; ltnorm2] THEN
  MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM_REAL THEN ASM_REWRITE_TAC[LRG_INDEX_TUPLES_FINITE] THEN
  X_GEN_TAC `i:num->num` THEN DISCH_TAC THEN
  MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM_REAL THEN ASM_REWRITE_TAC[LRG_INDEX_TUPLES_FINITE] THEN
  X_GEN_TAC `j:num->num` THEN DISCH_TAC THEN
  MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL_REAL THEN ASM_SIMP_TAC[RFA_LSMOOTH_LRM4] THEN
  MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL_REAL THEN ASM_SIMP_TAC[RFA_LSMOOTH_LRM4] THEN
  MATCH_MP_TAC LRG_SMOOTH_LIFT_PRODUCT_REAL THEN
  ASM_SIMP_TAC[FINITE_NUMSEG; LRG_LSMOOTH_GINV_ENTRY]);;

let RFA_LRICCI_FLOW_LSMOOTH = prove
 (`!U a b (G:real->real^N->real^N^N).
     lricci_flow U a b G ==> lrg_lsmooth U a b G`,
  REWRITE_TAC[lricci_flow; lrg_lsmooth] THEN MESON_TAC[]);;

let RFA_RMD2_CHART_SMOOTH = prove
 (`!(top:A topology) atlas a b (g:real->A->real^N^N) c.
     ricci_flow_on (top,atlas) a b g /\ c IN atlas
     ==> smooth_map_on
           (interval(lift a,lift b) PCROSS IMAGE (SND c) (FST c INTER topspace top))
           (\z. lift(rfa_rmd2 0 atlas (g (drop(fstcart z))) (chart_inv c (sndcart z))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology)
                  (atlas:((A->bool)#(A->real^N))->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `FST c INTER topspace top = FST (c:(A->bool)#(A->real^N))` SUBST1_TAC THENL
   [MP_TAC(MATCH_MP OPEN_IN_SUBSET
      (ASSUME `open_in top (FST(c:(A->bool)#(A->real^N)))`)) THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `g:real->A->real^N^N`; `c:(A->bool)#(A->real^N)`]
         LRG_RICCI_FLOW_ON_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o MATCH_MP RFA_LRICCI_FLOW_LSMOOTH) THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `\z. lift(lrm_deriv_norm2 0
                    ((\t. metric_local atlas (c:(A->bool)#(A->real^N))
                                       ((g:real->A->real^N^N) t)) (drop(fstcart z)))
                    (sndcart z))` THEN
  ASM_SIMP_TAC[RFA_LSMOOTH_LRM_NORM2_0; OPEN_PCROSS; OPEN_INTERVAL] THEN
  REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; FSTCART_PASTECART;
              SNDCART_PASTECART; IN_INTERVAL_1; LIFT_DROP] THEN
  MAP_EVERY X_GEN_TAC [`s:real^1`; `y:real^N`] THEN STRIP_TAC THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g:real->A->real^N^N) (drop s)`; `c:(A->bool)#(A->real^N)`;
                 `chart_inv (c:(A->bool)#(A->real^N)) y`] RFA_RMD2_0_CHART) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `ricci_flow_on (top:A topology,atlas:((A->bool)#(A->real^N))->bool) a b
                               (g:real->A->real^N^N)` THEN
    REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[]]);;

(* ========================================================================= *)
(* Positive definiteness is uniform and open.                                *)
(* ========================================================================= *)

let RFA_POSDEF_LOWER = prove
 (`!A:real^N^N.
        (!v. ~(v = vec 0) ==> &0 < v dot (A ** v))
        ==> ?m. &0 < m /\ !v. m * norm v pow 2 <= v dot (A ** v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\v:real^N. v dot ((A:real^N^N) ** v)`; `sphere(vec 0:real^N,&1)`]
         CONTINUOUS_ATTAINS_INF) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_SPHERE; SPHERE_EQ_EMPTY; o_DEF] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
    MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR];
    ALL_TAC] THEN
  REWRITE_TAC[IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `v0:real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `v0 dot ((A:real^N^N) ** v0)` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[NORM_0; REAL_ARITH `~(&0 = &1)`];
    ALL_TAC] THEN
  X_GEN_TAC `v:real^N` THEN ASM_CASES_TAC `v:real^N = vec 0` THENL
   [ASM_REWRITE_TAC[NORM_0; DOT_LZERO] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `inv(norm v) % v:real^N`) THEN
  ASM_SIMP_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM; REAL_MUL_LINV; NORM_EQ_0] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN
  SUBGOAL_THEN `&0 < norm(v:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `q = v dot ((A:real^N^N) ** v)` THEN
  ABBREV_TAC `n = norm(v:real^N)` THEN
  ABBREV_TAC `m = v0 dot ((A:real^N^N) ** v0)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `m * n pow 2 <= (inv n * inv n * q) * n pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `y = q ==> x <= y ==> x <= q`) THEN
  UNDISCH_TAC `&0 < n` THEN CONV_TAC REAL_FIELD);;

let RFA_POSDEF_PERTURB = prove
 (`!(A:real^N^N) B m.
        &0 < m /\ (!v. m * norm v pow 2 <= v dot (A ** v)) /\
        norm(vectorize(B - A)) <= m / &2
        ==> !v. ~(v = vec 0) ==> &0 < v dot (B ** v)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `v dot ((B:real^N^N) ** v) = v dot (A ** v) + v dot ((B - A) ** v)`
  SUBST1_TAC THENL
   [REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB; DOT_RSUB] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`v:real^N`; `((B:real^N^N) - A) ** v`] NORM_CAUCHY_SCHWARZ_ABS) THEN
  MP_TAC(ISPECL [`(B:real^N^N) - A`; `v:real^N`] COMPATIBLE_NORM_VECTORIZE) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N`) THEN
  SUBGOAL_THEN `&0 < norm(v:real^N)` MP_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  UNDISCH_TAC `norm(vectorize((B:real^N^N) - A)) <= m / &2` THEN
  UNDISCH_TAC `&0 < m` THEN
  ABBREV_TAC `n = norm(v:real^N)` THEN
  ABBREV_TAC `d = norm(vectorize((B:real^N^N) - A))` THEN
  ABBREV_TAC `p = norm(((B:real^N^N) - A) ** v)` THEN
  ABBREV_TAC `q = v dot ((A:real^N^N) ** v)` THEN
  ABBREV_TAC `r = v dot (((B:real^N^N) - A) ** v)` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `n * p <= n * (d * n)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `n * (d * n) <= n * (m / &2 * n)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < m * n pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `n * (m / &2 * n) = (m * n pow 2) / &2` ASSUME_TAC THENL
   [CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Continuity of |Rm|^2 up to the initial time.  A smooth                    *)
(* extension of the metric past the initial time is symmetrised, it stays   *)
(* positive definite near every point of [a,b) x V, and there it is a smooth *)
(* family of metrics whose curvature norm agrees with the original one.      *)
(* ========================================================================= *)

let RFA_SYMM_EXT = prove
 (`!O V a b (Gc:real->real^N->real^N^N)
    (FF:real^(1,N)finite_sum->real^(N,N)finite_prod).
     open O /\ smooth_map_on O FF /\
     (!t y. a <= t /\ t < b /\ y IN V ==> transp(Gc t y) = Gc t y) /\
     (!t y. a <= t /\ t < b /\ y IN V ==> FF(pastecart (lift t) y) = vectorize(Gc t y))
     ==> ?Fs. smooth_map_on O Fs /\
              (!w. transp(matrify(Fs w)) = matrify(Fs w):real^N^N) /\
              (!t y. a <= t /\ t < b /\ y IN V
                     ==> Fs(pastecart (lift t) y) = vectorize(Gc t y))`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `(\m. vectorize(inv(&2) %% (matrify m + transp(matrify m)):real^N^N)) o
              (FF:real^(1,N)finite_sum->real^(N,N)finite_prod)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[linear; MATRIFY_ADD; MATRIFY_CMUL; TRANSP_MATRIX_ADD; TRANSP_MATRIX_CMUL;
                GSYM VECTORIZE_ADD; GSYM VECTORIZE_CMUL] THEN
    CONJ_TAC THEN REPEAT GEN_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[CART_EQ; MATRIX_ADD_COMPONENT; MATRIX_CMUL_COMPONENT] THEN
    REPEAT STRIP_TAC THEN REAL_ARITH_TAC;
    GEN_TAC THEN REWRITE_TAC[o_THM; MATRIFY_VECTORIZE; TRANSP_MATRIX_CMUL;
                             TRANSP_MATRIX_ADD; TRANSP_TRANSP] THEN
    AP_TERM_TAC THEN MATCH_ACCEPT_TAC MATRIX_ADD_SYM;
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[o_THM; MATRIFY_VECTORIZE] THEN AP_TERM_TAC THEN
    REWRITE_TAC[CART_EQ; MATRIX_ADD_COMPONENT; MATRIX_CMUL_COMPONENT] THEN
    REPEAT STRIP_TAC THEN REAL_ARITH_TAC]);;

let RFA_PCROSS_BOX_DIST = prove
 (`!w0:real^(1,N)finite_sum t y d.
        abs(t - drop(fstcart w0)) < d /\ dist(y,sndcart w0) < d
        ==> dist(pastecart (lift t) y,w0) < &2 * d`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [GSYM PASTECART_FST_SND] THEN
  REWRITE_TAC[dist; PASTECART_SUB] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `norm(lift t - fstcart(w0:real^(1,N)finite_sum)) + norm(y - sndcart w0)` THEN
  REWRITE_TAC[NORM_PASTECART_LE] THEN
  SUBGOAL_THEN `norm(lift t - fstcart(w0:real^(1,N)finite_sum)) = abs(t - drop(fstcart w0))`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [GSYM LIFT_DROP] THEN
    REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT];
    ALL_TAC] THEN
  UNDISCH_TAC `dist(y:real^N,sndcart(w0:real^(1,N)finite_sum)) < d` THEN
  REWRITE_TAC[dist] THEN ASM_REAL_ARITH_TAC);;

let RFA_LOCAL_LSMOOTH = prove
 (`!O (Fs:real^(1,N)finite_sum->real^(N,N)finite_prod) w0.
     open O /\ smooth_map_on O Fs /\ w0 IN O /\
     (!w. transp(matrify(Fs w)) = matrify(Fs w):real^N^N) /\
     (!v. ~(v = vec 0) ==> &0 < v dot (matrify(Fs w0):real^N^N ** v))
     ==> ?d. &0 < d /\
             interval(lift(drop(fstcart w0) - d),lift(drop(fstcart w0) + d)) PCROSS
             ball(sndcart w0,d) SUBSET O /\
             lrg_lsmooth (ball(sndcart w0,d)) (drop(fstcart w0) - d) (drop(fstcart w0) + d)
               (\t y. matrify(Fs(pastecart (lift t) y)))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP RFA_POSDEF_LOWER) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(Fs:real^(1,N)finite_sum->real^(N,N)finite_prod) continuous at w0`
  MP_TAC THENL
   [MP_TAC(ISPECL [`O:real^(1,N)finite_sum->bool`;
                   `Fs:real^(1,N)finite_sum->real^(N,N)finite_prod`]
           SMOOTH_MAP_ON_CONTINUOUS_ON) THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `m / &2`) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o SPEC `w0:real^(1,N)finite_sum` o
              GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d1 d2 / &2` THEN
  ABBREV_TAC `d = min d1 d2 / &2` THEN
  SUBGOAL_THEN `&0 < d /\ &2 * d <= d1 /\ &2 * d <= d2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `t0 = drop(fstcart(w0:real^(1,N)finite_sum))` THEN
  ABBREV_TAC `y0 = sndcart(w0:real^(1,N)finite_sum)` THEN
  SUBGOAL_THEN
   `!t y. abs(t - t0) < d /\ dist(y:real^N,y0) < d
          ==> pastecart (lift t) y IN (O:real^(1,N)finite_sum->bool) /\
              dist(pastecart (lift t) y,w0) < d1`
  (LABEL_TAC "box") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`w0:real^(1,N)finite_sum`; `t:real`; `y:real^N`; `d:real`]
           RFA_PCROSS_BOX_DIST) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `ball(w0:real^(1,N)finite_sum,d2) SUBSET O` THEN
      REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
      ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                IN_BALL; DROP_ADD; DROP_SUB; LIFT_DROP] THEN
    MAP_EVERY X_GEN_TAC [`s:real^1`; `y:real^N`] THEN STRIP_TAC THEN
    USE_THEN "box" (MP_TAC o SPECL [`drop s`; `y:real^N`]) THEN
    REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
     [ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[lrg_lsmooth; OPEN_BALL] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN REWRITE_TAC[metric_field; OPEN_BALL] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[o_DEF; VECTORIZE_MATRIFY] THEN
      SUBGOAL_THEN
       `(\y. (Fs:real^(1,N)finite_sum->real^(N,N)finite_prod) (pastecart (lift t) y)) =
        Fs o (\y:real^N. pastecart (lift t) y)`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
      EXISTS_TAC `O:real^(1,N)finite_sum->bool` THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_BALL] THEN X_GEN_TAC `y:real^N` THEN
        DISCH_TAC THEN USE_THEN "box" (MP_TAC o SPECL [`t:real`; `y:real^N`]) THEN
        ANTS_TAC THENL
         [ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
          SIMP_TAC[]];
        MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
        REWRITE_TAC[OPEN_BALL; SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_ID]];
      X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_BALL] THEN DISCH_TAC THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC RFA_POSDEF_PERTURB THEN
      EXISTS_TAC `matrify((Fs:real^(1,N)finite_sum->real^(N,N)finite_prod) w0):real^N^N` THEN
      EXISTS_TAC `m:real` THEN ASM_REWRITE_TAC[VECTORIZE_SUB; VECTORIZE_MATRIFY] THEN
      USE_THEN "box" (MP_TAC o SPECL [`t:real`; `y:real^N`]) THEN
      ANTS_TAC THENL
       [ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN
      DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN
      REWRITE_TAC[dist] THEN REAL_ARITH_TAC];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `O:real^(1,N)finite_sum->bool` THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                  IN_BALL; DROP_ADD; DROP_SUB; LIFT_DROP] THEN
      MAP_EVERY X_GEN_TAC [`s:real^1`; `y:real^N`] THEN STRIP_TAC THEN
      USE_THEN "box" (MP_TAC o SPECL [`drop s`; `y:real^N`]) THEN
      REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
       [ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        SIMP_TAC[]];
      REWRITE_TAC[VECTORIZE_MATRIFY; LIFT_DROP; PASTECART_FST_SND; ETA_AX] THEN
      ASM_REWRITE_TAC[]]]);;

let RFA_EXT_RMNORM_CONTINUOUS = prove
 (`!V a b e (Gc:real->real^N->real^N^N)
    (FF:real^(1,N)finite_sum->real^(N,N)finite_prod).
     open V /\ &0 < e /\
     (!t. a <= t /\ t < b ==> metric_field V (Gc t)) /\
     smooth_map_on (interval(lift(a - e),lift b) PCROSS V) FF /\
     (!t y. a <= t /\ t < b /\ y IN V ==> FF(pastecart (lift t) y) = vectorize(Gc t y))
     ==> (\w. lift(lrm_deriv_norm2 0 (Gc (drop(fstcart w))) (sndcart w))) continuous_on
         {w | a <= drop(fstcart w) /\ drop(fstcart w) < b /\ sndcart w IN V}`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `O = interval(lift(a - e),lift b) PCROSS (V:real^N->bool)` THEN
  SUBGOAL_THEN `open(O:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`O:real^(1,N)finite_sum->bool`; `V:real^N->bool`; `a:real`; `b:real`;
                 `Gc:real->real^N->real^N^N`;
                 `FF:real^(1,N)finite_sum->real^(N,N)finite_prod`] RFA_SYMM_EXT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Fs:real^(1,N)finite_sum->real^(N,N)finite_prod`
    STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; IN_ELIM_THM] THEN
  X_GEN_TAC `w0:real^(1,N)finite_sum` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(w0:real^(1,N)finite_sum) IN O` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN
    ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v. ~(v = vec 0)
        ==> &0 < v dot (matrify((Fs:real^(1,N)finite_sum->real^(N,N)finite_prod) w0)
                        :real^N^N ** v)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `matrify((Fs:real^(1,N)finite_sum->real^(N,N)finite_prod) w0):real^N^N =
      (Gc:real->real^N->real^N^N) (drop(fstcart w0)) (sndcart w0)`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [GSYM PASTECART_FST_SND] THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV o LAND_CONV)
        [GSYM LIFT_DROP] THEN
      ASM_SIMP_TAC[MATRIFY_VECTORIZE];
      ALL_TAC] THEN
    UNDISCH_TAC `!t. a <= t /\ t < b ==> metric_field V ((Gc:real->real^N->real^N^N) t)` THEN
    DISCH_THEN(MP_TAC o SPEC `drop(fstcart(w0:real^(1,N)finite_sum))`) THEN
    ASM_REWRITE_TAC[metric_field] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`O:real^(1,N)finite_sum->bool`;
                 `Fs:real^(1,N)finite_sum->real^(N,N)finite_prod`;
                 `w0:real^(1,N)finite_sum`] RFA_LOCAL_LSMOOTH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RFA_LSMOOTH_LRM_NORM2_0) THEN DISCH_TAC THEN
  MATCH_MP_TAC CONTINUOUS_TRANSFORM_WITHIN THEN
  EXISTS_TAC
   `\w. lift(lrm_deriv_norm2 0
              ((\t y. matrify((Fs:real^(1,N)finite_sum->real^(N,N)finite_prod)
                                (pastecart (lift t) y)):real^N^N) (drop(fstcart w)))
              (sndcart w))` THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
   [X_GEN_TAC `w:real^(1,N)finite_sum` THEN STRIP_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC RFA_LRM_NORM2_0_LOCAL THEN
    EXISTS_TAC `ball(sndcart(w0:real^(1,N)finite_sum),d)` THEN
    REWRITE_TAC[OPEN_BALL; IN_BALL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `dist(w0:real^(1,N)finite_sum,w)` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[dist; GSYM SNDCART_SUB; NORM_SNDCART];
        ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^N) IN V` ASSUME_TAC THENL
     [UNDISCH_TAC
       `interval(lift(drop(fstcart(w0:real^(1,N)finite_sum)) - d),
                 lift(drop(fstcart w0) + d)) PCROSS ball(sndcart w0,d) SUBSET O` THEN
      EXPAND_TAC "O" THEN
      REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
      DISCH_THEN(MP_TAC o SPECL [`fstcart(w0:real^(1,N)finite_sum)`; `z:real^N`]) THEN
      ASM_REWRITE_TAC[IN_BALL; IN_INTERVAL_1; DROP_ADD; DROP_SUB; LIFT_DROP] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[LIFT_DROP; MATRIFY_VECTORIZE];
    MATCH_MP_TAC CONTINUOUS_AT_WITHIN THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON) THEN
    SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_PCROSS; OPEN_INTERVAL; OPEN_BALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM PASTECART_FST_SND] THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; IN_BALL; DIST_REFL;
                DROP_ADD; DROP_SUB; LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* |Rm|^2 is jointly continuous on [a,b) x M along a Ricci flow              *)
(* that is smooth up to the initial time (ricci_flow_from).                   *)
(* ========================================================================= *)

let RFA_RICCI_FLOW_FROM_METRIC = prove
 (`!(top:A topology) atlas a b (g:real->A->real^N^N) t.
     ricci_flow_from (top,atlas) a b g /\ a <= t /\ t < b
     ==> smooth_manifold_atlas top atlas /\ riemannian_metric atlas (g t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ricci_flow_from; ricci_flow_on] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `t:real = a` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let RFA_RMD2_CHART_CONTINUOUS = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b
    (g:real->A->real^N^N) c.
     ricci_flow_from (top,atlas) a b g /\ c IN atlas
     ==> continuous_map
           (subtopology
             (prod_topology (subtopology euclideanreal {t | a <= t /\ t < b})
                            (subtopology top (topspace top)))
             {z | z IN topspace(prod_topology (subtopology euclideanreal
                                                 {t | a <= t /\ t < b})
                                               (subtopology top (topspace top))) /\
                  SND z IN FST c},
            euclideanreal)
           (\z. rfa_rmd2 0 atlas (g (FST z)) (SND z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology)
                  (atlas:((A->bool)#(A->real^N))->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ricci_flow_from; ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `ricci_flow_from (top:A topology,atlas:((A->bool)#(A->real^N))->bool) a b
                                 (g:real->A->real^N^N)` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  REWRITE_TAC[ricci_flow_from] THEN
  DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)` o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real`
   (X_CHOOSE_THEN `FF:real^(1,N)finite_sum->real^(N,N)finite_prod` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`; `a:real`; `b:real`;
                 `e:real`;
                 `\t. metric_local atlas (c:(A->bool)#(A->real^N)) ((g:real->A->real^N^N) t)`;
                 `FF:real^(1,N)finite_sum->real^(N,N)finite_prod`]
         RFA_EXT_RMNORM_CONTINUOUS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `a:real`; `b:real`; `g:real->A->real^N^N`; `t:real`]
           RFA_RICCI_FLOW_FROM_METRIC) THEN
    ASM_REWRITE_TAC[riemannian_metric] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o BETA_RULE) THEN
  SUBGOAL_THEN
   `continuous_map
     (subtopology euclidean
       {w | a <= drop(fstcart w) /\ drop(fstcart w) < b /\
            sndcart w IN IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)},
      euclideanreal)
     (\w. lrm_deriv_norm2 0
           (metric_local atlas (c:(A->bool)#(A->real^N))
                         ((g:real->A->real^N^N) (drop(fstcart w)))) (sndcart w))`
  ASSUME_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_EQ_LIFT; CONTINUOUS_MAP_EUCLIDEAN; o_DEF] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
  EXISTS_TAC
   `(\w. lrm_deriv_norm2 0
          (metric_local atlas (c:(A->bool)#(A->real^N))
                        ((g:real->A->real^N^N) (drop(fstcart w)))) (sndcart w)) o
    (\z:real#A. pastecart (lift(FST z)) (SND c (SND z)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_PROD_TOPOLOGY; IN_INTER; IN_ELIM_THM;
                FORALL_PAIR_THM; IN_CROSS; TOPSPACE_EUCLIDEANREAL; IN_UNIV;
                o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; FST; SND] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC RFA_RMD2_0_CHART THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `a:real`; `b:real`; `g:real->A->real^N^N`; `t:real`]
           RFA_RICCI_FLOW_FROM_METRIC) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology euclidean
               {w | a <= drop(fstcart w) /\ drop(fstcart w) < b /\
                    sndcart w IN IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)}` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; TOPSPACE_PROD_TOPOLOGY;
                IN_INTER; IN_ELIM_THM; FORALL_PAIR_THM; IN_CROSS; FST; SND;
                TOPSPACE_EUCLIDEANREAL; IN_UNIV; FSTCART_PASTECART; SNDCART_PASTECART;
                LIFT_DROP] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `(\z:real#A. pastecart (lift(FST z)) (SND(c:(A->bool)#(A->real^N)) (SND z))) =
    (\(x,y). pastecart x y) o (\z. lift(FST z),SND c (SND z))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FORALL_PAIR_THM; FST; SND]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `prod_topology (euclidean:(real^1)topology) (euclidean:(real^N)topology)` THEN
  REWRITE_TAC[CONTINUOUS_MAP_PASTECART; CONTINUOUS_MAP_PAIRED] THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `euclideanreal` THEN
    REWRITE_TAC[CONTINUOUS_MAP_LIFT; ETA_AX] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
    MP_TAC(ISPECL [`subtopology euclideanreal {t | a <= t /\ t < b}`;
                   `subtopology (top:A topology) (topspace top)`] CONTINUOUS_MAP_FST) THEN
    SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY];
    ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology (top:A topology) (FST(c:(A->bool)#(A->real^N)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
      MP_TAC(ISPECL [`subtopology euclideanreal {t | a <= t /\ t < b}`;
                     `subtopology (top:A topology) (topspace top)`] CONTINUOUS_MAP_SND) THEN
      SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; TOPSPACE_PROD_TOPOLOGY;
                  IN_INTER; IN_ELIM_THM; FORALL_PAIR_THM; IN_CROSS; FST; SND] THEN
      SIMP_TAC[]];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
           SMOOTH_MANIFOLD_ATLAS_CHART) THEN
    ASM_REWRITE_TAC[PAIR] THEN
    DISCH_THEN(fun th -> MP_TAC(MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP
                                 (last(CONJUNCTS th)))) THEN
    REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; ETA_AX] THEN SIMP_TAC[]]);;

let RFA_RMD2_CONTINUOUS = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b (g:real->A->real^N^N).
     ricci_flow_from (top,atlas) a b g
     ==> continuous_map
           (prod_topology (subtopology euclideanreal {t | a <= t /\ t < b})
                          (subtopology top (topspace top)),
            euclideanreal)
           (\z. rfa_rmd2 0 atlas (g (FST z)) (SND z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology)
                  (atlas:((A->bool)#(A->real^N))->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ricci_flow_from; ricci_flow_on]; ALL_TAC] THEN
  MATCH_MP_TAC(INST_TYPE [`:real#A`,`:A`; `:real`,`:B`;
                          `:(A->bool)#(A->real^N)`,`:K`] PASTING_LEMMA) THEN
  MAP_EVERY EXISTS_TAC
   [`\c:(A->bool)#(A->real^N). \z:real#A.
       rfa_rmd2 0 atlas ((g:real->A->real^N^N) (FST z)) (SND z)`;
    `\c:(A->bool)#(A->real^N).
       {z:real#A | z IN topspace(prod_topology
                                   (subtopology euclideanreal {t | a <= t /\ t < b})
                                   (subtopology top (topspace top))) /\
                   SND z IN FST c}`;
    `atlas:((A->bool)#(A->real^N))->bool`] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
      EXISTS_TAC `subtopology (top:A topology) (topspace top)` THEN
      REWRITE_TAC[CONTINUOUS_MAP_SND; SUBTOPOLOGY_TOPSPACE] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC RFA_RMD2_CHART_CONTINUOUS THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN
    REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; TOPSPACE_SUBTOPOLOGY; IN_CROSS; IN_INTER;
                IN_ELIM_THM] THEN
    STRIP_TAC THEN
    EXISTS_TAC `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `x:A`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN
    SIMP_TAC[IN_ELIM_THM; IN_CROSS; IN_INTER; TOPSPACE_PROD_TOPOLOGY;
             TOPSPACE_SUBTOPOLOGY; FST; SND] THEN
    ASM_REWRITE_TAC[]]);;

