(* ========================================================================= *)
(* pc_mfd_level4: the Gauss equation and the Hessian of restrictions on a    *)
(* regular level set of a 3-manifold.  In the preferred adapted chart (from  *)
(* e) and the preferred ambient chart c at x, k = SND c o e is a local       *)
(* diffeomorphism, the ambient metric in e-coordinates is                    *)
(* Ge = mpullback k G_c, the leaf representative is the slice metric of Ge   *)
(* (LVS_METRIC_LOCAL) and f o chart_inv c o k = u + y3; the local results of *)
(* pc_mfd_level3 transfer by the pullback lemmas.                            *)
(* Main results: LVS_GAUSS (R_N = R - 2 Ric(n,n) + 2 det(h^-1 II)),          *)
(* LVS_HESS, LVS_GAUSS_FRAME, LVS_II_PUSHFORWARD, LVS_TRACE_SPLIT.           *)
(* Sources: MT p. 215 (proof of Prop 9.46); Petersen Thm 3.2.4.              *)
(* ========================================================================= *)

needs "src/pc_mfd_level2.ml";;
needs "src/pc_mfd_level3.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The Hessian cmp_lhess is local and natural under diffeomorphisms (as in   *)
(* the proof of LLAP_PULLBACK).                                              *)
(* ------------------------------------------------------------------------- *)

let LVS_LHESS_LOCAL = prove
 (`!(G1:real^N->real^N^N) G2 f1 f2 s y a b.
     open s /\ y IN s /\ (!z. z IN s ==> G1 z = G2 z /\ f1 z = f2 z)
     ==> cmp_lhess G1 f1 y a b = cmp_lhess G2 f2 y a b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cmp_lhess] THEN
  MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `s:real^N->bool` THEN
  ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN
  MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `s:real^N->bool` THEN
  ASM_SIMP_TAC[]);;

let LVS_LHESS_PULLBACK = prove
 (`!U U' (h:real^N->real^N) h' G f y a b.
     metric_field U G /\ diffeomorphism_on U' U h h' /\
     smooth_map_on U (\z. lift(f z)) /\ y IN U'
     ==> cmp_lhess (mpullback h G) (f o h) y a b =
         cmp_lhess G f (h y) (frechet_derivative h (at y) a)
                             (frechet_derivative h (at y) b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                 `h':real^N->real^N`; `y:real^N`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[diffeomorphism_on]
    (ASSUME `diffeomorphism_on (U':real^N->bool) U (h:real^N->real^N) h'`)) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `f:real^N->real`] LRG_DF_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!z u. z IN U'
          ==> drop(frechet_derivative
                    (\w. lift(((f:real^N->real) o (h:real^N->real^N)) w))
                    (at z) (u 1)) =
              ltpullback h
                (\z u. drop(frechet_derivative (\w. lift(f w)) (at z) (u 1)))
                z u`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[ltpullback] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
                   `h':real^N->real^N`; `f:real^N->real`; `z:real^N`]
           LRG_COMPOSE_DERIV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  REWRITE_TAC[cmp_lhess] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `lnabla 1 (mpullback h G)
      (ltpullback (h:real^N->real^N)
        (\z u. drop(frechet_derivative (\w. lift((f:real^N->real) w))
                                       (at z) (u 1))))
      y (\m. if m = 1 then a else b)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `U':real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN ASM_SIMP_TAC[];
    MP_TAC(BETA_RULE(ISPECL
      [`1`; `U:real^N->bool`; `U':real^N->bool`; `h:real^N->real^N`;
       `h':real^N->real^N`; `G:real^N->real^N^N`;
       `\z u. drop(frechet_derivative (\w. lift((f:real^N->real) w))
                                      (at z) ((u:num->real^N) 1))`;
       `y:real^N`; `\m. if m = 1 then (a:real^N) else b`] LNABLA_PULLBACK)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[ltpullback] THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Adapted coordinates.  For an adapted chart from e and an ambient chart c, *)
(* the inverse adapted chart read in c is (SND c o e) o lvs_iota near the    *)
(* slice; its derivative is D(SND c o e) o lvs_iota; the leaf representative *)
(* is the slice metric of mpullback (SND c o e) G_c.                         *)
(* ------------------------------------------------------------------------- *)

let LVS_KSLICE = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) W f u s e e' c z.
     smooth_manifold_atlas top atlas /\
     mfd_diffeo euclidean (open_set_atlas (:real^3)) s top atlas (IMAGE e s) e e' /\
     IMAGE e s SUBSET W /\ (!y. y IN s ==> f(e y) = u + y$3) /\
     c IN atlas /\ lvs_iota z IN {y | y IN s /\ e y IN FST c}
     ==> frechet_derivative
           (\w. SND c (chart_inv (IMAGE e s INTER lvs_set W f u,
                                  (\x. lvs_proj(e' x))) w)) (at z) =
         frechet_derivative (SND c o e) (at (lvs_iota z)) o lvs_iota`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `s:real^3->bool`; `e:real^3->A`; `e':A->real^3`;
                 `c:(A->bool)#(A->real^3)`] LVS_PARAM_CHART_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `sc = {y | y IN s /\ (e:real^3->A) y IN FST(c:(A->bool)#(A->real^3))}` THEN
  MATCH_MP_TAC(GSYM FRECHET_DERIVATIVE_AT) THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
  EXISTS_TAC `(SND(c:(A->bool)#(A->real^3)) o (e:real^3->A)) o lvs_iota` THEN
  EXISTS_TAC `{w:real^2 | lvs_iota w IN sc}` THEN
  ASM_SIMP_TAC[LVS_OPEN_IOTA_PREIMAGE; IN_ELIM_THM] THEN CONJ_TAC THENL
   [X_GEN_TAC `w:real^2` THEN EXPAND_TAC "sc" THEN
    REWRITE_TAC[IN_ELIM_THM; o_THM] THEN STRIP_TAC THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC LVS_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`;
                          `atlas:((A->bool)#(A->real^3))->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC DIFF_CHAIN_AT THEN
    SIMP_TAC[HAS_DERIVATIVE_LINEAR; LVS_IOTA_LINEAR] THEN
    REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `sc:real^3->bool` THEN ASM_REWRITE_TAC[]]);;

let LVS_LEAF_REP_SLICE = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) W f u s e e' c z.
     smooth_manifold_atlas top atlas /\ open_in top W /\ lvs_regular atlas W f u /\
     mfd_diffeo euclidean (open_set_atlas (:real^3)) s top atlas (IMAGE e s) e e' /\
     IMAGE e s SUBSET W /\ (!y. y IN s ==> f(e y) = u + y$3) /\
     c IN atlas /\ lvs_iota z IN {y | y IN s /\ e y IN FST c}
     ==> metric_local (lvs_atlas top atlas W f u)
                      (IMAGE e s INTER lvs_set W f u,(\x. lvs_proj(e' x)))
                      (lvs_metric top atlas g W f u) z =
         lvs_hslice (mpullback (SND c o e) (metric_local atlas c g)) z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_ELIM_THM]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `W:A->bool`; `f:A->real`; `u:real`; `s:real^3->bool`;
                 `e:real^3->A`; `e':A->real^3`] LVS_ADAPTED_LEAF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (LABEL_TAC "im"))) THEN
  SUBGOAL_THEN
   `chart_inv (IMAGE (e:real^3->A) s INTER lvs_set W f u,
               (\x. lvs_proj((e':A->real^3) x))) z = e(lvs_iota z)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LVS_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`;
                          `atlas:((A->bool)#(A->real^3))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `W:A->bool`; `f:A->real`; `u:real`;
                 `(IMAGE (e:real^3->A) s INTER lvs_set W f u,
                   (\x. lvs_proj((e':A->real^3) x)))`;
                 `c:(A->bool)#(A->real^3)`; `z:real^2`] LVS_METRIC_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FST; SND] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LVS_ATLAS_MEMBER THEN ASM_REWRITE_TAC[];
      USE_THEN "im" SUBST1_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM]];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `W:A->bool`; `f:A->real`; `u:real`; `s:real^3->bool`;
                 `e:real^3->A`; `e':A->real^3`; `c:(A->bool)#(A->real^3)`;
                 `z:real^2`] LVS_KSLICE) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `linear(frechet_derivative (SND(c:(A->bool)#(A->real^3)) o (e:real^3->A))
                              (at (lvs_iota z)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `s:real^3->bool`; `e:real^3->A`; `e':A->real^3`;
                   `c:(A->bool)#(A->real^3)`] LVS_PARAM_CHART_SMOOTH) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `{y | y IN s /\ (e:real^3->A) y IN FST(c:(A->bool)#(A->real^3))}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_COMPOSE; LVS_IOTA_LINEAR; LVS_HSLICE_TRANSP; mpullback;
               o_THM] THEN
  REWRITE_TAC[MATRIX_TRANSP_MUL; MATRIX_MUL_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* The e-coordinate package at a point x of the leaf (an adapted e with x in *)
(* its image, the preferred chart c of atlas at x), and the transfer of      *)
(* |grad f|^2 and of the normal to the coordinates of c.                     *)
(* ------------------------------------------------------------------------- *)

let LVS_DROP_LINEAR_DOT = prove
 (`!L:real^N->real^1. linear L
     ==> !w. drop(L w) = ((lambda i. drop(L(basis i))):real^N) dot w`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
                         [GSYM(MATCH_MP MATRIX_WORKS th)]) THEN
  SIMP_TAC[drop; matrix_vector_mul; dot; matrix; LAMBDA_BETA; DIMINDEX_1;
           LE_REFL] THEN
  REWRITE_TAC[REAL_MUL_SYM]);;

let LVS_ECOORD_FACTS = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) W f u s e e' x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     open_in top W /\ lvs_regular atlas W f u /\
     mfd_diffeo euclidean (open_set_atlas (:real^3)) s top atlas (IMAGE e s) e e' /\
     IMAGE e s SUBSET W /\ (!y. y IN s ==> f(e y) = u + y$3) /\
     x IN IMAGE e s INTER lvs_set W f u
     ==> chart_at atlas x IN atlas /\ x IN FST(chart_at atlas x) /\
         x IN topspace top /\
         e' x IN {y | y IN s /\ e y IN FST(chart_at atlas x)} /\ e(e' x) = x /\
         lvs_iota(lvs_proj(e' x)) = e' x /\
         diffeomorphism_on {y | y IN s /\ e y IN FST(chart_at atlas x)}
           (IMAGE (SND(chart_at atlas x)) (FST(chart_at atlas x) INTER IMAGE e s))
           (SND(chart_at atlas x) o e) (e' o chart_inv (chart_at atlas x)) /\
         metric_field
           (IMAGE (SND(chart_at atlas x)) (FST(chart_at atlas x) INTER IMAGE e s))
           (metric_local atlas (chart_at atlas x) g) /\
         metric_field {y | y IN s /\ e y IN FST(chart_at atlas x)}
           (mpullback (SND(chart_at atlas x) o e)
                      (metric_local atlas (chart_at atlas x) g)) /\
         smooth_map_on
           (IMAGE (SND(chart_at atlas x)) (FST(chart_at atlas x) INTER IMAGE e s))
           (\z. lift(f(chart_inv (chart_at atlas x) z))) /\
         (!y. y IN {y | y IN s /\ e y IN FST(chart_at atlas x)}
              ==> f(chart_inv (chart_at atlas x) ((SND(chart_at atlas x) o e) y)) =
                  u + y$3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN IMAGE (e:real^3->A) s` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:A) IN IMAGE (e:real^3->A) s INTER lvs_set W f u` THEN
    SIMP_TAC[IN_INTER];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `s:real^3->bool`; `e:real^3->A`; `e':A->real^3`]
                LVS_DIFFEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
    MP_TAC(SPEC `x:A` (last(CONJUNCTS th)))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN STRIP_ASSUME_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `W:A->bool`; `f:A->real`; `u:real`; `s:real^3->bool`;
                 `e:real^3->A`; `e':A->real^3`] LVS_ADAPTED_LEAF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `x:A` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (e:real^3->A) s SUBSET topspace top` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^3))->bool) x`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN

  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `s:real^3->bool`; `e:real^3->A`; `e':A->real^3`;
                 `chart_at (atlas:((A->bool)#(A->real^3))->bool) x`] LVS_PARAM_CHART_DIFFEO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `metric_field
      (IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) x)) (FST(chart_at atlas x) INTER IMAGE (e:real^3->A) s))
      (metric_local atlas (chart_at atlas x) (g:A->real^3^3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) x)) (FST(chart_at atlas x))` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^3))->bool) g` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTER_SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THEN
  FIRST
   [ASM_REWRITE_TAC[] THEN NO_TAC;
    MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
    MAP_EVERY EXISTS_TAC
     [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) x)) (FST(chart_at atlas x) INTER IMAGE (e:real^3->A) s)`;
      `(e':A->real^3) o chart_inv (chart_at (atlas:((A->bool)#(A->real^3))->bool) x)`] THEN
    ASM_REWRITE_TAC[] THEN NO_TAC;
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) x)) (FST(chart_at atlas x) INTER W)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [lvs_regular]) THEN
    REWRITE_TAC[mfd_smooth_on] THEN
    DISCH_THEN(MP_TAC o SPEC `chart_at (atlas:((A->bool)#(A->real^3))->bool) x`) THEN
    ASM_REWRITE_TAC[o_DEF] THEN NO_TAC;
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
    ASM_SIMP_TAC[] THEN NO_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Transfer of |grad f|^2 and of the normal.  With k = SND c o e and         *)
(* Ge = mpullback k G_c: |grad f|^2 at x is e3.Ge^-1 e3 at e' x, and         *)
(* D k (Ge^-1 e3) = g(x)^-1 df (the gradient of f in the chart c).           *)
(* ------------------------------------------------------------------------- *)

let LVS_GRAD2_TRANSFER = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) W f u s e e' x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     open_in top W /\ lvs_regular atlas W f u /\
     mfd_diffeo euclidean (open_set_atlas (:real^3)) s top atlas (IMAGE e s) e e' /\
     IMAGE e s SUBSET W /\ (!y. y IN s ==> f(e y) = u + y$3) /\
     x IN IMAGE e s INTER lvs_set W f u
     ==> lgrad2 (metric_local atlas (chart_at atlas x) g)
                (f o chart_inv (chart_at atlas x)) (SND(chart_at atlas x) x) =
         basis 3 dot
         (matrix_inv(mpullback (SND(chart_at atlas x) o e)
                       (metric_local atlas (chart_at atlas x) g) (e' x)) ** basis 3)`,

  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `W:A->bool`; `f:A->real`; `u:real`;
                 `s:real^3->bool`; `e:real^3->A`; `e':A->real^3`; `x:A`]
                LVS_ECOORD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  REWRITE_TAC[lvs_df] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) x` THEN
  ABBREV_TAC `sc = {y | y IN s /\ (e:real^3->A) y IN FST(c:(A->bool)#(A->real^3))}` THEN
  ABBREV_TAC `O = IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER IMAGE (e:real^3->A) s)` THEN
  ABBREV_TAC `k = SND(c:(A->bool)#(A->real^3)) o (e:real^3->A)` THEN
  ABBREV_TAC `k' = (e':A->real^3) o chart_inv (c:(A->bool)#(A->real^3))` THEN
  ABBREV_TAC `Gc = metric_local (atlas:((A->bool)#(A->real^3))->bool) c (g:A->real^3^3)` THEN
  SUBGOAL_THEN `(k:real^3->real^3) ((e':A->real^3) x) = SND(c:(A->bool)#(A->real^3)) x`
  ASSUME_TAC THENL [EXPAND_TAC "k" THEN ASM_REWRITE_TAC[o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `open (sc:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN sc ==> (\z. lift(((\y. (f:A->real)(chart_inv (c:(A->bool)#(A->real^3)) y)) o k) z)) y =
                    (\z:real^3. lift(u + z$3)) y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    AP_TERM_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`O:real^3->bool`; `sc:real^3->bool`; `k:real^3->real^3`;
                   `k':real^3->real^3`; `Gc:real^3->real^3^3`;
                   `(f:A->real) o chart_inv (c:(A->bool)#(A->real^3))`;
                   `(e':A->real^3) x`] LGRAD2_PULLBACK) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[o_THM] THEN ASM_REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM o REWRITE_RULE[ASSUME
      `(k:real^3->real^3) ((e':A->real^3) x) = SND(c:(A->bool)#(A->real^3)) x`]) THEN
    SUBGOAL_THEN
     `lgrad2 (mpullback k Gc) (((f:A->real) o chart_inv (c:(A->bool)#(A->real^3))) o (k:real^3->real^3))
             ((e':A->real^3) x) =
      lgrad2 (mpullback k Gc) (\w. u + w$3) (e' x)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC LGRAD2_LOCAL THEN EXISTS_TAC `sc:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      REWRITE_TAC[o_THM] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun t -> t = `u:real`)) (concl th) &&
        can (find_term (fun t -> t = `sc:real^3->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[o_THM; LIFT_EQ];
      REWRITE_TAC[LVS_LGRAD2_Y3]]);;

let LVS_NORMAL_TRANSFER = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) W f u s e e' x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     open_in top W /\ lvs_regular atlas W f u /\
     mfd_diffeo euclidean (open_set_atlas (:real^3)) s top atlas (IMAGE e s) e e' /\
     IMAGE e s SUBSET W /\ (!y. y IN s ==> f(e y) = u + y$3) /\
     x IN IMAGE e s INTER lvs_set W f u
     ==> frechet_derivative (SND(chart_at atlas x) o e) (at (e' x))
           (matrix_inv(mpullback (SND(chart_at atlas x) o e)
                         (metric_local atlas (chart_at atlas x) g) (e' x)) ** basis 3) =
         matrix_inv(g x) ** lvs_df atlas f x`,

  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `W:A->bool`; `f:A->real`; `u:real`;
                 `s:real^3->bool`; `e:real^3->A`; `e':A->real^3`; `x:A`]
                LVS_ECOORD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  REWRITE_TAC[lvs_df] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) x` THEN
  ABBREV_TAC `sc = {y | y IN s /\ (e:real^3->A) y IN FST(c:(A->bool)#(A->real^3))}` THEN
  ABBREV_TAC `O = IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER IMAGE (e:real^3->A) s)` THEN
  ABBREV_TAC `k = SND(c:(A->bool)#(A->real^3)) o (e:real^3->A)` THEN
  ABBREV_TAC `k' = (e':A->real^3) o chart_inv (c:(A->bool)#(A->real^3))` THEN
  ABBREV_TAC `Gc = metric_local (atlas:((A->bool)#(A->real^3))->bool) c (g:A->real^3^3)` THEN
  SUBGOAL_THEN `(k:real^3->real^3) ((e':A->real^3) x) = SND(c:(A->bool)#(A->real^3)) x`
  ASSUME_TAC THENL [EXPAND_TAC "k" THEN ASM_REWRITE_TAC[o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `open (sc:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN sc ==> (\z. lift(((\y. (f:A->real)(chart_inv (c:(A->bool)#(A->real^3)) y)) o k) z)) y =
                    (\z:real^3. lift(u + z$3)) y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    AP_TERM_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`O:real^3->bool`; `sc:real^3->bool`; `k:real^3->real^3`;
                 `k':real^3->real^3`; `(e':A->real^3) x`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  ABBREV_TAC `D = frechet_derivative (k:real^3->real^3) (at ((e':A->real^3) x))` THEN
  SUBGOAL_THEN `(g:A->real^3^3) x = Gc(SND(c:(A->bool)#(A->real^3)) x)` ASSUME_TAC THENL
   [EXPAND_TAC "Gc" THEN EXPAND_TAC "c" THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC METRIC_LOCAL_AT THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `invertible((g:A->real^3^3) x)` ASSUME_TAC THENL
   [MATCH_MP_TAC LVS_POSDEF_INVERTIBLE THEN
    ASM_MESON_TAC[RIEMANNIAN_METRIC_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `invertible(mpullback (k:real^3->real^3) Gc ((e':A->real^3) x))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`sc:real^3->bool`; `mpullback (k:real^3->real^3) Gc`;
                   `(e':A->real^3) x`] LRG_METRIC_INVERTIBLE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `X = matrix_inv(mpullback (k:real^3->real^3) Gc ((e':A->real^3) x)) **
                  basis 3` THEN
  SUBGOAL_THEN `mpullback (k:real^3->real^3) Gc ((e':A->real^3) x) ** X = basis 3`
  ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  ABBREV_TAC
   `dF = (lambda i. drop(frechet_derivative (\y. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^3)) y)))
                          (at (SND(c:(A->bool)#(A->real^3)) x)) (basis i))):real^3` THEN
  SUBGOAL_THEN `!v:real^3. (D:real^3->real^3) v dot dF = v$3` ASSUME_TAC THENL
   [X_GEN_TAC `v:real^3` THEN EXPAND_TAC "dF" THEN
    ONCE_REWRITE_TAC[DOT_SYM] THEN
    SUBGOAL_THEN
     `linear(frechet_derivative (\y. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^3)) y)))
                                (at (SND(c:(A->bool)#(A->real^3)) x)))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `O:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[diffeomorphism_on];
      ALL_TAC] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP LVS_DROP_LINEAR_DOT th)]) THEN
    MP_TAC(ISPECL [`O:real^3->bool`; `sc:real^3->bool`; `k:real^3->real^3`;
                   `k':real^3->real^3`; `\y. (f:A->real)(chart_inv (c:(A->bool)#(A->real^3)) y)`;
                   `(e':A->real^3) x`] LRG_COMPOSE_DERIV) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^3`) THEN
    EXPAND_TAC "D" THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN
     `frechet_derivative (\z. lift(((\y. (f:A->real)(chart_inv (c:(A->bool)#(A->real^3)) y)) o
                                     (k:real^3->real^3)) z)) (at ((e':A->real^3) x)) =
      frechet_derivative (\z:real^3. lift(u + z$3)) (at (e' x))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
      EXISTS_TAC `sc:real^3->bool` THEN ASM_SIMP_TAC[];
      REWRITE_TAC[LVS_AFFINE3_DERIV; LIFT_DROP]];
    ALL_TAC] THEN
  SUBGOAL_THEN `invertible(transp(matrix(D:real^3->real^3)))` ASSUME_TAC THENL
   [REWRITE_TAC[INVERTIBLE_TRANSP] THEN EXPAND_TAC "D" THEN
    MATCH_MP_TAC LRG_DIFFEO_JACOBIAN_INVERTIBLE THEN
    MAP_EVERY EXISTS_TAC [`O:real^3->bool`; `sc:real^3->bool`; `k':real^3->real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(D:real^3->real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `transp(matrix(D:real^3->real^3)) ** dF = basis 3` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM VECTOR_EQ_LDOT] THEN X_GEN_TAC `v:real^3` THEN
    REWRITE_TAC[DOT_MATRIX_TRANSP_RMUL] THEN ASM_SIMP_TAC[MATRIX_WORKS] THEN
    SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `transp(matrix(D:real^3->real^3)) ** ((g:A->real^3^3) x ** D X) = basis 3`
  ASSUME_TAC THENL
   [UNDISCH_TAC `mpullback (k:real^3->real^3) Gc ((e':A->real^3) x) ** X = basis 3` THEN
    REWRITE_TAC[mpullback] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[GSYM MATRIX_WORKS; MATRIX_VECTOR_MUL_ASSOC; MATRIX_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:A->real^3^3) x ** (D:real^3->real^3) X = dF` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `transp(matrix(D:real^3->real^3)) ** ((g:A->real^3^3) x ** D X) =
      transp(matrix D) ** dF`
    MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM
      `\v:real^3. matrix_inv(transp(matrix(D:real^3->real^3))) ** v`) THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID;
                 MATRIX_MUL_LID];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `\v:real^3. matrix_inv((g:A->real^3^3) x) ** v` o
    check (fun th -> concl th = `(g:A->real^3^3) x ** (D:real^3->real^3) X = dF`)) THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID;
               MATRIX_MUL_LID]);;

(* ------------------------------------------------------------------------- *)
(* The second fundamental form in e-coordinates and the Gauss equation       *)
(* R_N = R - 2 Ric(n,n) + 2 det(h^-1 II) on the leaf.                        *)
(* ------------------------------------------------------------------------- *)

let LVS_II_TRANSFER = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) W f u s e e' x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     open_in top W /\ lvs_regular atlas W f u /\
     mfd_diffeo euclidean (open_set_atlas (:real^3)) s top atlas (IMAGE e s) e e' /\
     IMAGE e s SUBSET W /\ (!y. y IN s ==> f(e y) = u + y$3) /\
     x IN IMAGE e s INTER lvs_set W f u /\
     chart_at (lvs_atlas top atlas W f u) x =
       (IMAGE e s INTER lvs_set W f u,(\x. lvs_proj(e' x)))
     ==> lvs_II top atlas g W f u x =
         lvs_IIloc (mpullback (SND(chart_at atlas x) o e)
                              (metric_local atlas (chart_at atlas x) g))
                   (lvs_proj(e' x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `W:A->bool`; `f:A->real`; `u:real`;
                 `s:real^3->bool`; `e:real^3->A`; `e':A->real^3`; `x:A`]
                LVS_ECOORD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `W:A->bool`; `f:A->real`; `u:real`;
                 `s:real^3->bool`; `e:real^3->A`; `e':A->real^3`; `x:A`]
                LVS_GRAD2_TRANSFER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `W:A->bool`; `f:A->real`; `u:real`; `s:real^3->bool`;
                 `e:real^3->A`; `e':A->real^3`;
                 `chart_at (atlas:((A->bool)#(A->real^3))->bool) x`;
                 `lvs_proj((e':A->real^3) x)`] LVS_KSLICE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[lvs_II; lvs_IIloc; lvs_jac] THEN ASM_REWRITE_TAC[SND] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) x` THEN
  ABBREV_TAC `sc = {y | y IN s /\ (e:real^3->A) y IN FST(c:(A->bool)#(A->real^3))}` THEN
  ABBREV_TAC `O = IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER IMAGE (e:real^3->A) s)` THEN
  ABBREV_TAC `k = SND(c:(A->bool)#(A->real^3)) o (e:real^3->A)` THEN
  ABBREV_TAC `Gc = metric_local (atlas:((A->bool)#(A->real^3))->bool) c (g:A->real^3^3)` THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; DIMINDEX_2] THEN
  X_GEN_TAC `a:num` THEN STRIP_TAC THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN
  REWRITE_TAC[o_THM] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `SND(c:(A->bool)#(A->real^3)) x = (k:real^3->real^3)((e':A->real^3) x)`
  SUBST1_TAC THENL [EXPAND_TAC "k" THEN ASM_REWRITE_TAC[o_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`O:real^3->bool`; `sc:real^3->bool`; `k:real^3->real^3`;
                 `(e':A->real^3) o chart_inv (c:(A->bool)#(A->real^3))`;
                 `Gc:real^3->real^3^3`;
                 `\y. (f:A->real)(chart_inv (c:(A->bool)#(A->real^3)) y)`;
                 `(e':A->real^3) x`;
                 `lvs_iota(basis a)`; `lvs_iota(basis b)`] LVS_LHESS_PULLBACK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  SUBGOAL_THEN
   `cmp_lhess (mpullback (k:real^3->real^3) Gc)
      ((\y. (f:A->real)(chart_inv (c:(A->bool)#(A->real^3)) y)) o k)
      ((e':A->real^3) x) (lvs_iota(basis a)) (lvs_iota(basis b)) =
    cmp_lhess (mpullback k Gc) (\w. u + w$3) (e' x)
      (lvs_iota(basis a)) (lvs_iota(basis b))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LVS_LHESS_LOCAL THEN EXISTS_TAC `sc:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> t = `u:real`)) (concl th) &&
      can (find_term (fun t -> t = `sc:real^3->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[o_THM];
    ALL_TAC] THEN
  MATCH_MP_TAC LVS_LHESS_Y3 THEN EXISTS_TAC `sc:real^3->bool` THEN
  ASM_REWRITE_TAC[]);;

let LVS_PREFERRED_ADAPTED = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) W f u x.
     smooth_manifold_atlas top atlas /\ open_in top W /\ lvs_regular atlas W f u /\
     x IN lvs_set W f u
     ==> ?s e e'. mfd_diffeo euclidean (open_set_atlas (:real^3)) s top atlas
                             (IMAGE e s) e e' /\
                  IMAGE e s SUBSET W /\ (!y. y IN s ==> f(e y) = u + y$3) /\
                  x IN IMAGE e s INTER lvs_set W f u /\
                  chart_at (lvs_atlas top atlas W f u) x =
                  (IMAGE e s INTER lvs_set W f u,(\x. lvs_proj(e' x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology top (lvs_set W f u):A topology`;
                 `lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool) W f u`;
                 `x:A`] CHART_AT) THEN
  ASM_SIMP_TAC[LVS_MANIFOLD; LVS_TOPSPACE] THEN
  ABBREV_TAC `c2 = chart_at (lvs_atlas top (atlas:((A->bool)#(A->real^3))->bool)
                                       W f u) x` THEN
  REWRITE_TAC[LVS_ATLAS_IN] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `s:real^3->bool` (X_CHOOSE_THEN `e:real^3->A`
     (X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC))) ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`s:real^3->bool`; `e:real^3->A`; `e':A->real^3`] THEN
  UNDISCH_TAC `(x:A) IN FST(c2:(A->bool)#(A->real^2))` THEN
  ASM_REWRITE_TAC[FST]);;

let LVS_GAUSS = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) W f u x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     open_in top W /\ lvs_regular atlas W f u /\ x IN lvs_set W f u
     ==> mfd_scalar (lvs_atlas top atlas W f u) (lvs_metric top atlas g W f u) x =
         mfd_scalar atlas g x -
         &2 * mfd_ricci atlas g x (lvs_normal atlas g f x) (lvs_normal atlas g f x) +
         &2 * det(matrix_inv(lvs_metric top atlas g W f u x) **
                  lvs_II top atlas g W f u x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `W:A->bool`; `f:A->real`; `u:real`; `x:A`]
                LVS_PREFERRED_ADAPTED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` (X_CHOOSE_THEN `e:real^3->A`
    (X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `W:A->bool`; `f:A->real`; `u:real`;
                 `s:real^3->bool`; `e:real^3->A`; `e':A->real^3`; `x:A`]
                LVS_II_TRANSFER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `W:A->bool`; `f:A->real`; `u:real`;
                 `s:real^3->bool`; `e:real^3->A`; `e':A->real^3`; `x:A`]
                LVS_GRAD2_TRANSFER) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `W:A->bool`; `f:A->real`; `u:real`;
                 `s:real^3->bool`; `e:real^3->A`; `e':A->real^3`; `x:A`]
                LVS_NORMAL_TRANSFER) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `W:A->bool`; `f:A->real`; `u:real`;
                 `s:real^3->bool`; `e:real^3->A`; `e':A->real^3`; `x:A`]
                LVS_ECOORD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[mfd_scalar; mfd_ricci; lvs_normal] THEN
  ASM_REWRITE_TAC[SND] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) x` THEN
  ABBREV_TAC `sc = {y | y IN s /\ (e:real^3->A) y IN FST(c:(A->bool)#(A->real^3))}` THEN
  ABBREV_TAC `O = IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER IMAGE (e:real^3->A) s)` THEN
  ABBREV_TAC `k = SND(c:(A->bool)#(A->real^3)) o (e:real^3->A)` THEN
  ABBREV_TAC `Gc = metric_local (atlas:((A->bool)#(A->real^3))->bool) c (g:A->real^3^3)` THEN
  SUBGOAL_THEN `open (sc:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
  SUBGOAL_THEN `(k:real^3->real^3)((e':A->real^3) x) = SND(c:(A->bool)#(A->real^3)) x`
  ASSUME_TAC THENL [EXPAND_TAC "k" THEN ASM_REWRITE_TAC[o_THM]; ALL_TAC] THEN
  (* the leaf representative near the chart point is the slice metric *)
  SUBGOAL_THEN
   `lscalar (metric_local (lvs_atlas top atlas W f u)
               (IMAGE (e:real^3->A) s INTER lvs_set W f u,(\x. lvs_proj((e':A->real^3) x)))
               (lvs_metric top atlas (g:A->real^3^3) W f u))
            (lvs_proj(e' x)) =
    lscalar (lvs_hslice (mpullback (k:real^3->real^3) Gc)) (lvs_proj(e' x))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LSCALAR_LOCAL THEN EXISTS_TAC `{w:real^2 | lvs_iota w IN sc}` THEN
    ASM_SIMP_TAC[LVS_OPEN_IOTA_PREIMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN
    MAP_EVERY EXPAND_TAC ["k"; "Gc"] THEN
    MATCH_MP_TAC LVS_LEAF_REP_SLICE THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `lvs_iota w IN sc` THEN EXPAND_TAC "sc" THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sc:real^3->bool`; `mpullback (k:real^3->real^3) Gc`;
                 `lvs_proj((e':A->real^3) x)`] LVS_LOCAL_GAUSS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`O:real^3->bool`; `sc:real^3->bool`; `k:real^3->real^3`;
                 `(e':A->real^3) o chart_inv (c:(A->bool)#(A->real^3))`;
                 `Gc:real^3->real^3^3`; `(e':A->real^3) x`] LSCALAR_PULLBACK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`O:real^3->bool`; `sc:real^3->bool`; `k:real^3->real^3`;
                 `(e':A->real^3) o chart_inv (c:(A->bool)#(A->real^3))`;
                 `Gc:real^3->real^3^3`; `(e':A->real^3) x`] LRICCI_PULLBACK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`O:real^3->bool`; `sc:real^3->bool`; `k:real^3->real^3`;
                 `(e':A->real^3) o chart_inv (c:(A->bool)#(A->real^3))`;
                 `(e':A->real^3) x`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  ASM_SIMP_TAC[LINEAR_CMUL] THEN
  SUBGOAL_THEN
   `lvs_metric top (atlas:((A->bool)#(A->real^3))->bool) g W f u x =
    lvs_hslice (mpullback (k:real^3->real^3) Gc) (lvs_proj((e':A->real^3) x))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `W:A->bool`; `f:A->real`; `u:real`; `x:A`]
                  LVS_METRIC_AT) THEN
    ASM_REWRITE_TAC[SND] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MAP_EVERY EXPAND_TAC ["k"; "Gc"] THEN
    MATCH_MP_TAC LVS_LEAF_REP_SLICE THEN ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(e':A->real^3) x IN sc` THEN
    EXPAND_TAC "sc" THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The Hessian of the restriction of a smooth function h to the leaf:        *)
(* Hess_N h(v,w) = Hess h(Jv,Jw) - dh(n) II(v,w) in the preferred charts     *)
(* (the left side is p2b_mfd_hess of the leaf).                              *)
(* ------------------------------------------------------------------------- *)

let LVS_IILOC_DOT = prove
 (`!S (G:real^3->real^3^3) z v w.
     metric_field S G /\ lvs_iota z IN S
     ==> v dot (lvs_IIloc G z ** w) =
         --((christoffel G (lvs_iota z) (lvs_iota v) (lvs_iota w))$3) /
         sqrt(basis 3 dot (matrix_inv(G(lvs_iota z)) ** basis 3))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `G:real^3->real^3^3`; `z:real^2`;
                 `v:real^2`; `w:real^2`] LVS_GAMMA3_BILINEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[lvs_IIloc] THEN
  SIMP_TAC[dot; matrix_vector_mul; LAMBDA_BETA; DIMINDEX_2; SUM_2; ARITH] THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let LVS_HESS = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) W f u (h:A->real) x v w.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     open_in top W /\ lvs_regular atlas W f u /\
     mfd_smooth_on atlas W (\x. lift(h x)) /\ x IN lvs_set W f u
     ==> cmp_lhess (metric_local (lvs_atlas top atlas W f u)
                                 (chart_at (lvs_atlas top atlas W f u) x)
                                 (lvs_metric top atlas g W f u))
                   (\z. h(chart_inv (chart_at (lvs_atlas top atlas W f u) x) z))
                   (SND(chart_at (lvs_atlas top atlas W f u) x) x) v w =
         cmp_lhess (metric_local atlas (chart_at atlas x) g)
                   (\y. h(chart_inv (chart_at atlas x) y))
                   (SND(chart_at atlas x) x)
                   (lvs_jac top atlas W f u x v) (lvs_jac top atlas W f u x w) -
         drop(frechet_derivative (\y. lift(h(chart_inv (chart_at atlas x) y)))
                                 (at (SND(chart_at atlas x) x))
                                 (lvs_normal atlas g f x)) *
         (v dot (lvs_II top atlas g W f u x ** w))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `W:A->bool`; `f:A->real`; `u:real`; `x:A`]
                LVS_PREFERRED_ADAPTED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` (X_CHOOSE_THEN `e:real^3->A`
    (X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `W:A->bool`; `f:A->real`; `u:real`;
                 `s:real^3->bool`; `e:real^3->A`; `e':A->real^3`; `x:A`]
                LVS_II_TRANSFER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `W:A->bool`; `f:A->real`; `u:real`;
                 `s:real^3->bool`; `e:real^3->A`; `e':A->real^3`; `x:A`]
                LVS_GRAD2_TRANSFER) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `W:A->bool`; `f:A->real`; `u:real`;
                 `s:real^3->bool`; `e:real^3->A`; `e':A->real^3`; `x:A`]
                LVS_NORMAL_TRANSFER) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `W:A->bool`; `f:A->real`; `u:real`;
                 `s:real^3->bool`; `e:real^3->A`; `e':A->real^3`; `x:A`]
                LVS_ECOORD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `W:A->bool`; `f:A->real`; `u:real`; `s:real^3->bool`;
                 `e:real^3->A`; `e':A->real^3`;
                 `chart_at (atlas:((A->bool)#(A->real^3))->bool) x`;
                 `lvs_proj((e':A->real^3) x)`] LVS_KSLICE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[lvs_normal; lvs_jac] THEN ASM_REWRITE_TAC[SND] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) x` THEN
  ABBREV_TAC `sc = {y | y IN s /\ (e:real^3->A) y IN FST(c:(A->bool)#(A->real^3))}` THEN
  ABBREV_TAC `O = IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER IMAGE (e:real^3->A) s)` THEN
  ABBREV_TAC `k = SND(c:(A->bool)#(A->real^3)) o (e:real^3->A)` THEN
  ABBREV_TAC `Gc = metric_local (atlas:((A->bool)#(A->real^3))->bool) c (g:A->real^3^3)` THEN
  SUBGOAL_THEN `open (sc:real^3->bool) /\ open (O:real^3->bool) /\
                IMAGE (k:real^3->real^3) sc = O` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on sc O (k:real^3->real^3)
                   ((e':A->real^3) o chart_inv (c:(A->bool)#(A->real^3)))` THEN
    SIMP_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  SUBGOAL_THEN `(k:real^3->real^3)((e':A->real^3) x) = SND(c:(A->bool)#(A->real^3)) x`
  ASSUME_TAC THENL [EXPAND_TAC "k" THEN ASM_REWRITE_TAC[o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `SND(c:(A->bool)#(A->real^3)) x IN O` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (k:real^3->real^3) sc = O` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `(k:real^3->real^3)((e':A->real^3) x) = SND(c:(A->bool)#(A->real^3)) x` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on O (\z. lift((h:A->real)(chart_inv (c:(A->bool)#(A->real^3)) z)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[SYM(ASSUME `IMAGE (SND(c:(A->bool)#(A->real^3)))
                               (FST c INTER IMAGE (e:real^3->A) s) = O`)] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER W)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `mfd_smooth_on (atlas:((A->bool)#(A->real^3))->bool) W
                               (\x. lift((h:A->real) x))` THEN
    REWRITE_TAC[mfd_smooth_on] THEN
    DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^3)`) THEN
    ASM_REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on sc
      (\y. lift(((\y. (h:A->real)(chart_inv (c:(A->bool)#(A->real^3)) y)) o
                 (k:real^3->real^3)) y))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\y. lift(((\y. (h:A->real)(chart_inv (c:(A->bool)#(A->real^3)) y)) o
                 (k:real^3->real^3)) y)) =
      (\z. lift(h(chart_inv c z))) o k` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `O:real^3->bool` THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN
    UNDISCH_TAC `diffeomorphism_on sc O (k:real^3->real^3)
                   ((e':A->real^3) o chart_inv (c:(A->bool)#(A->real^3)))` THEN
    SIMP_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cmp_lhess (metric_local (lvs_atlas top atlas W f u)
               (IMAGE (e:real^3->A) s INTER lvs_set W f u,(\x. lvs_proj((e':A->real^3) x)))
               (lvs_metric top atlas (g:A->real^3^3) W f u))
     (\z. (h:A->real)(chart_inv (IMAGE e s INTER lvs_set W f u,(\x. lvs_proj(e' x))) z))
     (lvs_proj(e' x)) v w =
    cmp_lhess (lvs_hslice (mpullback (k:real^3->real^3) Gc))
     (\z. ((\y. h(chart_inv (c:(A->bool)#(A->real^3)) y)) o k)(lvs_iota z))
     (lvs_proj(e' x)) v w`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LVS_LHESS_LOCAL THEN EXISTS_TAC `{w:real^2 | lvs_iota w IN sc}` THEN
    ASM_SIMP_TAC[LVS_OPEN_IOTA_PREIMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["k"; "Gc"] THEN
      MATCH_MP_TAC LVS_LEAF_REP_SLICE THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `lvs_iota z IN sc` THEN EXPAND_TAC "sc" THEN SIMP_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "k" THEN REWRITE_TAC[o_THM] THEN
    UNDISCH_TAC `lvs_iota z IN sc` THEN EXPAND_TAC "sc" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `chart_inv (IMAGE (e:real^3->A) s INTER lvs_set W f u,
                 (\x. lvs_proj((e':A->real^3) x))) z = e(lvs_iota z)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC LVS_CHART_INV THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`;
                            `atlas:((A->bool)#(A->real^3))->bool`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `c:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sc:real^3->bool`; `mpullback (k:real^3->real^3) Gc`;
                 `(\y. (h:A->real)(chart_inv (c:(A->bool)#(A->real^3)) y)) o
                  (k:real^3->real^3)`;
                 `lvs_proj((e':A->real^3) x)`; `v:real^2`; `w:real^2`]
                LVS_LOCAL_HESS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`O:real^3->bool`; `sc:real^3->bool`; `k:real^3->real^3`;
                 `(e':A->real^3) o chart_inv (c:(A->bool)#(A->real^3))`;
                 `Gc:real^3->real^3^3`;
                 `\y. (h:A->real)(chart_inv (c:(A->bool)#(A->real^3)) y)`;
                 `(e':A->real^3) x`;
                 `lvs_iota v`; `lvs_iota w`] LVS_LHESS_PULLBACK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`O:real^3->bool`; `sc:real^3->bool`; `k:real^3->real^3`;
                 `(e':A->real^3) o chart_inv (c:(A->bool)#(A->real^3))`;
                 `\y. (h:A->real)(chart_inv (c:(A->bool)#(A->real^3)) y)`;
                 `(e':A->real^3) x`] LRG_COMPOSE_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[o_THM] THEN
  MP_TAC(ISPECL [`sc:real^3->bool`; `mpullback (k:real^3->real^3) Gc`;
                 `lvs_proj((e':A->real^3) x)`; `v:real^2`; `w:real^2`]
                LVS_IILOC_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`sc:real^3->bool`; `mpullback (k:real^3->real^3) Gc`;
                 `(e':A->real^3) x`; `lvs_iota w`; `lvs_iota v`] CHRISTOFFEL_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `linear(frechet_derivative (\y. lift((h:A->real)(chart_inv (c:(A->bool)#(A->real^3)) y)))
                              (at (SND c x)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `O:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
  REWRITE_TAC[DROP_CMUL] THEN
  MP_TAC(ISPECL [`sc:real^3->bool`; `mpullback (k:real^3->real^3) Gc`;
                 `(e':A->real^3) x`] LVS_G33_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `g3 = basis 3 dot (matrix_inv(mpullback (k:real^3->real^3) Gc ((e':A->real^3) x)) **
                                basis 3)` THEN
  ABBREV_TAC
   `dd = drop(frechet_derivative (\y. lift((h:A->real)(chart_inv (c:(A->bool)#(A->real^3)) y)))
               (at (SND c x)) (matrix_inv((g:A->real^3^3) x) ** lvs_df atlas f x))` THEN
  ABBREV_TAC
   `gm = (christoffel (mpullback (k:real^3->real^3) Gc) ((e':A->real^3) x)
            (lvs_iota v) (lvs_iota w))$3` THEN
  SUBGOAL_THEN `sqrt g3 pow 2 = g3 /\ &0 < sqrt g3` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; SQRT_POS_LT]; ALL_TAC] THEN
  UNDISCH_TAC `sqrt g3 pow 2 = g3` THEN UNDISCH_TAC `&0 < sqrt g3` THEN
  CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* The second fundamental form in pushforward form,                          *)
(* II(v,w) = Hess f(Jv,Jw) / |grad f|; the trace splitting                   *)
(* tr_g B = tr_h(J^T B J) + B(n,n); the orthonormal-frame form of the Gauss  *)
(* equation (MT's R_N = 2 (K_M(e1,e2) + det S)).                             *)
(* ------------------------------------------------------------------------- *)

let LVS_II_PUSHFORWARD = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) W f u x v w.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     open_in top W /\ lvs_regular atlas W f u /\ x IN lvs_set W f u
     ==> v dot (lvs_II top atlas g W f u x ** w) =
         cmp_lhess (metric_local atlas (chart_at atlas x) g)
                   (\y. f(chart_inv (chart_at atlas x) y)) (SND(chart_at atlas x) x)
                   (lvs_jac top atlas W f u x v) (lvs_jac top atlas W f u x w) /
         sqrt(lgrad2 (metric_local atlas (chart_at atlas x) g)
                     (f o chart_inv (chart_at atlas x)) (SND(chart_at atlas x) x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `W:A->bool`; `f:A->real`; `u:real`; `x:A`]
                LVS_PREFERRED_ADAPTED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` (X_CHOOSE_THEN `e:real^3->A`
    (X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `W:A->bool`; `f:A->real`; `u:real`;
                 `s:real^3->bool`; `e:real^3->A`; `e':A->real^3`; `x:A`]
                LVS_II_TRANSFER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `W:A->bool`; `f:A->real`; `u:real`;
                 `s:real^3->bool`; `e:real^3->A`; `e':A->real^3`; `x:A`]
                LVS_GRAD2_TRANSFER) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `W:A->bool`; `f:A->real`; `u:real`;
                 `s:real^3->bool`; `e:real^3->A`; `e':A->real^3`; `x:A`]
                LVS_ECOORD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `W:A->bool`; `f:A->real`; `u:real`; `s:real^3->bool`;
                 `e:real^3->A`; `e':A->real^3`;
                 `chart_at (atlas:((A->bool)#(A->real^3))->bool) x`;
                 `lvs_proj((e':A->real^3) x)`] LVS_KSLICE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[lvs_jac] THEN ASM_REWRITE_TAC[SND] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) x` THEN
  ABBREV_TAC `sc = {y | y IN s /\ (e:real^3->A) y IN FST(c:(A->bool)#(A->real^3))}` THEN
  ABBREV_TAC `O = IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER IMAGE (e:real^3->A) s)` THEN
  ABBREV_TAC `k = SND(c:(A->bool)#(A->real^3)) o (e:real^3->A)` THEN
  ABBREV_TAC `Gc = metric_local (atlas:((A->bool)#(A->real^3))->bool) c (g:A->real^3^3)` THEN
  MP_TAC(ISPECL [`sc:real^3->bool`; `mpullback (k:real^3->real^3) Gc`;
                 `lvs_proj((e':A->real^3) x)`; `v:real^2`; `w:real^2`]
                LVS_IILOC_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[o_THM] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `SND(c:(A->bool)#(A->real^3)) x = (k:real^3->real^3)((e':A->real^3) x)`
  SUBST1_TAC THENL [EXPAND_TAC "k" THEN ASM_REWRITE_TAC[o_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`O:real^3->bool`; `sc:real^3->bool`; `k:real^3->real^3`;
                 `(e':A->real^3) o chart_inv (c:(A->bool)#(A->real^3))`;
                 `Gc:real^3->real^3^3`;
                 `\y. (f:A->real)(chart_inv (c:(A->bool)#(A->real^3)) y)`;
                 `(e':A->real^3) x`;
                 `lvs_iota v`; `lvs_iota w`] LVS_LHESS_PULLBACK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  SUBGOAL_THEN
   `cmp_lhess (mpullback (k:real^3->real^3) Gc)
      ((\y. (f:A->real)(chart_inv (c:(A->bool)#(A->real^3)) y)) o k)
      ((e':A->real^3) x) (lvs_iota v) (lvs_iota w) =
    cmp_lhess (mpullback k Gc) (\w. u + w$3) (e' x) (lvs_iota v) (lvs_iota w)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LVS_LHESS_LOCAL THEN EXISTS_TAC `sc:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `diffeomorphism_on sc O (k:real^3->real^3)
                     ((e':A->real^3) o chart_inv (c:(A->bool)#(A->real^3)))` THEN
      SIMP_TAC[diffeomorphism_on];
      ALL_TAC] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> t = `u:real`)) (concl th) &&
      can (find_term (fun t -> t = `sc:real^3->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[o_THM];
    ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC LVS_LHESS_Y3 THEN EXISTS_TAC `sc:real^3->bool` THEN
  ASM_REWRITE_TAC[]);;

let LVS_VEC3_EXPAND = prove
 (`!y:real^3. y = y$1 % basis 1 + y$2 % basis 2 + y$3 % basis 3`,
  GEN_TAC THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC);;

let LVS_IOTA_BASIS = prove
 (`transp(matrix lvs_iota) ** basis 1:real^3 = basis 1:real^2 /\
   transp(matrix lvs_iota) ** basis 2:real^3 = basis 2:real^2 /\
   matrix lvs_iota ** basis 1:real^2 = basis 1:real^3 /\
   matrix lvs_iota ** basis 2:real^2 = basis 2:real^3`,
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM VECTOR_EQ_LDOT] THEN X_GEN_TAC `w:real^2` THEN
    REWRITE_TAC[DOT_MATRIX_TRANSP_RMUL] THEN SIMP_TAC[MATRIX_WORKS; LVS_IOTA_LINEAR] THEN
    SIMP_TAC[DOT_BASIS; DIMINDEX_2; DIMINDEX_3; ARITH; LVS_IOTA_COMPONENT];
    REWRITE_TAC[GSYM VECTOR_EQ_LDOT] THEN X_GEN_TAC `w:real^2` THEN
    REWRITE_TAC[DOT_MATRIX_TRANSP_RMUL] THEN SIMP_TAC[MATRIX_WORKS; LVS_IOTA_LINEAR] THEN
    SIMP_TAC[DOT_BASIS; DIMINDEX_2; DIMINDEX_3; ARITH; LVS_IOTA_COMPONENT];
    SIMP_TAC[MATRIX_WORKS; LVS_IOTA_LINEAR] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; LVS_IOTA_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; DIMINDEX_3; ARITH];
    SIMP_TAC[MATRIX_WORKS; LVS_IOTA_LINEAR] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; LVS_IOTA_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; DIMINDEX_3; ARITH]]);;

let LVS_TRACE_DOT = prove
 (`!A:real^N^N. trace A = sum(1..dimindex(:N)) (\i. basis i dot (A ** basis i))`,
  GEN_TAC THEN REWRITE_TAC[trace] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  REPEAT STRIP_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[DOT_BASIS; MATRIX_VECTOR_MUL_BASIS; column; LAMBDA_BETA]);;

let LVS_TRACE_SPLIT_LOCAL = prove
 (`!(G0:real^3^3) (Be:real^3^3).
     transp G0 = G0 /\ (!v. ~(v = vec 0) ==> &0 < v dot (G0 ** v))
     ==> trace(matrix_inv G0 ** Be) =
         trace(matrix_inv(transp(matrix lvs_iota) ** G0 ** matrix lvs_iota) **
               (transp(matrix lvs_iota) ** Be ** matrix lvs_iota)) +
         ((matrix_inv G0 ** basis 3) dot (Be ** (matrix_inv G0 ** basis 3))) /
         (basis 3 dot (matrix_inv G0 ** basis 3))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!y:real^3. (matrix_inv (G0:real^3^3) ** basis 3) dot ((Be:real^3^3) ** y) =
               y$1 * ((matrix_inv G0 ** basis 3) dot (Be ** basis 1)) +
               y$2 * ((matrix_inv G0 ** basis 3) dot (Be ** basis 2)) +
               y$3 * ((matrix_inv G0 ** basis 3) dot (Be ** basis 3))`
  (fun th -> SUBST1_TAC(SPEC `matrix_inv (G0:real^3^3) ** basis 3` th)) THENL
   [GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [LVS_VEC3_EXPAND] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL;
                DOT_RADD; DOT_RMUL];
    ALL_TAC] THEN
  REWRITE_TAC[LVS_TRACE_DOT; DIMINDEX_2; DIMINDEX_3; SUM_2; SUM_3] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  MP_TAC(ISPECL [`G0:real^3^3`; `basis 1:real^3`; `(Be:real^3^3) ** basis 1`]
                LVS_BLOCK_INV) THEN
  MP_TAC(ISPECL [`G0:real^3^3`; `basis 2:real^3`; `(Be:real^3^3) ** basis 2`]
                LVS_BLOCK_INV) THEN
  MP_TAC(ISPECL [`G0:real^3^3`; `basis 3:real^3`; `(Be:real^3^3) ** basis 3`]
                LVS_BLOCK_INV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[LVS_IOTA_BASIS; LVS_IOTA_TRANSP_E3; DOT_LZERO] THEN
  SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH] THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let LVS_CONG_INV = prove
 (`!(D:real^3^3) (G:real^3^3).
     invertible D /\ invertible G
     ==> matrix_inv G = D ** matrix_inv(transp D ** G ** D) ** transp D`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `invertible(transp(D:real^3^3))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INVERTIBLE_TRANSP]; ALL_TAC] THEN
  SUBGOAL_THEN `invertible((G:real^3^3) ** (D:real^3^3))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INVERTIBLE_MATRIX_MUL]; ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_INV_MUL] THEN
  REWRITE_TAC[MATRIX_MUL_ASSOC] THEN
  ASM_SIMP_TAC[MATRIX_INV; MATRIX_MUL_LID] THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN
  ASM_SIMP_TAC[MATRIX_INV; MATRIX_MUL_RID]);;

(* Pointwise normal form of the leaf data at x: in the e-coordinates of
   the preferred adapted chart, with the metric field G, the slice point z
   and the coordinate change D to the preferred ambient chart, the induced
   metric, the second fundamental form, the Jacobian and the normal are
   the local slice objects of pc_mfd_level3. *)

let LVS_POINT_FORM = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) W f u x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     open_in top W /\ lvs_regular atlas W f u /\ x IN lvs_set W f u
     ==> ?S (G:real^3->real^3^3) z (D:real^3->real^3).
           metric_field S G /\ lvs_iota z IN S /\
           linear D /\ invertible(matrix D) /\
           G(lvs_iota z) = transp(matrix D) ** g x ** matrix D /\
           lvs_metric top atlas g W f u x = lvs_hslice G z /\
           lvs_II top atlas g W f u x = lvs_IIloc G z /\
           (!v. lvs_jac top atlas W f u x v = D(lvs_iota v)) /\
           lvs_normal atlas g f x =
             inv(sqrt(basis 3 dot (matrix_inv(G(lvs_iota z)) ** basis 3))) %
             D(matrix_inv(G(lvs_iota z)) ** basis 3)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `W:A->bool`; `f:A->real`; `u:real`; `x:A`]
                LVS_PREFERRED_ADAPTED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` (X_CHOOSE_THEN `e:real^3->A`
    (X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `W:A->bool`; `f:A->real`; `u:real`;
                 `s:real^3->bool`; `e:real^3->A`; `e':A->real^3`; `x:A`]
                LVS_II_TRANSFER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `W:A->bool`; `f:A->real`; `u:real`;
                 `s:real^3->bool`; `e:real^3->A`; `e':A->real^3`; `x:A`]
                LVS_GRAD2_TRANSFER) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `W:A->bool`; `f:A->real`; `u:real`;
                 `s:real^3->bool`; `e:real^3->A`; `e':A->real^3`; `x:A`]
                LVS_NORMAL_TRANSFER) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `W:A->bool`; `f:A->real`; `u:real`;
                 `s:real^3->bool`; `e:real^3->A`; `e':A->real^3`; `x:A`]
                LVS_ECOORD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `W:A->bool`; `f:A->real`; `u:real`; `s:real^3->bool`;
                 `e:real^3->A`; `e':A->real^3`;
                 `chart_at (atlas:((A->bool)#(A->real^3))->bool) x`;
                 `lvs_proj((e':A->real^3) x)`] LVS_KSLICE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) x` THEN
  ABBREV_TAC `sc = {y | y IN s /\ (e:real^3->A) y IN FST(c:(A->bool)#(A->real^3))}` THEN
  ABBREV_TAC `O = IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER IMAGE (e:real^3->A) s)` THEN
  ABBREV_TAC `k = SND(c:(A->bool)#(A->real^3)) o (e:real^3->A)` THEN
  ABBREV_TAC `Gc = metric_local (atlas:((A->bool)#(A->real^3))->bool) c (g:A->real^3^3)` THEN
  MP_TAC(ISPECL [`O:real^3->bool`; `sc:real^3->bool`; `k:real^3->real^3`;
                 `(e':A->real^3) o chart_inv (c:(A->bool)#(A->real^3))`;
                 `(e':A->real^3) x`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  SUBGOAL_THEN `invertible(matrix(frechet_derivative (k:real^3->real^3)
                                    (at ((e':A->real^3) x))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_DIFFEO_JACOBIAN_INVERTIBLE THEN
    MAP_EVERY EXISTS_TAC [`O:real^3->bool`; `sc:real^3->bool`;
                          `(e':A->real^3) o chart_inv (c:(A->bool)#(A->real^3))`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(k:real^3->real^3)((e':A->real^3) x) = SND(c:(A->bool)#(A->real^3)) x`
  ASSUME_TAC THENL [EXPAND_TAC "k" THEN ASM_REWRITE_TAC[o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `(Gc:real^3->real^3^3)(SND(c:(A->bool)#(A->real^3)) x) = (g:A->real^3^3) x`
  ASSUME_TAC THENL
   [EXPAND_TAC "Gc" THEN EXPAND_TAC "c" THEN MATCH_MP_TAC METRIC_LOCAL_AT THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lvs_metric top (atlas:((A->bool)#(A->real^3))->bool) g W f u x =
    lvs_hslice (mpullback (k:real^3->real^3) Gc) (lvs_proj((e':A->real^3) x))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `W:A->bool`; `f:A->real`; `u:real`; `x:A`]
                  LVS_METRIC_AT) THEN
    ASM_REWRITE_TAC[SND] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MAP_EVERY EXPAND_TAC ["k"; "Gc"] THEN
    MATCH_MP_TAC LVS_LEAF_REP_SLICE THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(e':A->real^3) x IN sc` THEN
    EXPAND_TAC "sc" THEN SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`sc:real^3->bool`; `mpullback (k:real^3->real^3) Gc`;
                        `lvs_proj((e':A->real^3) x)`;
                        `frechet_derivative (k:real^3->real^3) (at ((e':A->real^3) x))`] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[mpullback]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[lvs_jac] THEN ASM_REWRITE_TAC[SND; o_THM];
    ALL_TAC] THEN
  REWRITE_TAC[lvs_normal] THEN ASM_REWRITE_TAC[]);;

(* The trace decomposition in the normal form (local algebra). *)

let LVS_TRACE_SPLIT_FORM = prove
 (`!(G0:real^3^3) (h:real^2^2) (J:real^2->real^3) (n:real^3) (B:real^3^3).
     (?S (G:real^3->real^3^3) z (D:real^3->real^3).
        metric_field S G /\ lvs_iota z IN S /\
        linear D /\ invertible(matrix D) /\
        G(lvs_iota z) = transp(matrix D) ** G0 ** matrix D /\
        h = lvs_hslice G z /\ (!v. J v = D(lvs_iota v)) /\
        n = inv(sqrt(basis 3 dot (matrix_inv(G(lvs_iota z)) ** basis 3))) %
            D(matrix_inv(G(lvs_iota z)) ** basis 3))
     ==> trace(matrix_inv G0 ** B) =
         trace(matrix_inv h ** (transp(matrix J) ** B ** matrix J)) +
         n dot (B ** n)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3->bool` (X_CHOOSE_THEN `G:real^3->real^3^3`
    (X_CHOOSE_THEN `z:real^2` (X_CHOOSE_THEN `D:real^3->real^3`
      STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `J = (D:real^3->real^3) o lvs_iota` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBST1_TAC(ASSUME `h = lvs_hslice (G:real^3->real^3^3) z`) THEN
  SUBST1_TAC(ASSUME
   `n = inv(sqrt(basis 3 dot (matrix_inv((G:real^3->real^3^3)(lvs_iota z)) **
                              basis 3))) %
        (D:real^3->real^3)(matrix_inv(G(lvs_iota z)) ** basis 3)`) THEN
  UNDISCH_TAC `(G:real^3->real^3^3)(lvs_iota z) =
               transp(matrix(D:real^3->real^3)) ** G0 ** matrix D` THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `G:real^3->real^3^3`; `lvs_iota(z:real^2)`]
                LVS_G33_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `transp((G:real^3->real^3^3)(lvs_iota z)) = G(lvs_iota z) /\
    (!v. ~(v = vec 0) ==> &0 < v dot (G(lvs_iota z) ** v))`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  REWRITE_TAC[LVS_HSLICE_TRANSP] THEN
  SIMP_TAC[MATRIX_COMPOSE; LVS_IOTA_LINEAR; ASSUME `linear(D:real^3->real^3)`] THEN
  REWRITE_TAC[GSYM(MATCH_MP MATRIX_WORKS (ASSUME `linear(D:real^3->real^3)`))] THEN
  ABBREV_TAC `Ge0 = (G:real^3->real^3^3)(lvs_iota z)` THEN
  ABBREV_TAC `M = matrix(D:real^3->real^3)` THEN
  SUBGOAL_THEN `invertible(Ge0:real^3^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC LVS_POSDEF_INVERTIBLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `invertible(G0:real^3^3)` ASSUME_TAC THENL
   [MP_TAC(ASSUME `invertible(Ge0:real^3^3)`) THEN
    REWRITE_TAC[SYM(ASSUME `transp(M:real^3^3) ** (G0:real^3^3) ** M = Ge0`)] THEN
    REWRITE_TAC[INVERTIBLE_MATRIX_MUL] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`M:real^3^3`; `G0:real^3^3`] LVS_CONG_INV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `transp(M:real^3^3) ** (G0:real^3^3) ** M = Ge0`] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `trace(((M:real^3^3) ** matrix_inv Ge0 ** transp M) ** (B:real^3^3)) =
    trace(matrix_inv Ge0 ** (transp M ** B ** M))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN
    GEN_REWRITE_TAC LAND_CONV [TRACE_MUL_SYM] THEN
    REWRITE_TAC[GSYM MATRIX_MUL_ASSOC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Ge0:real^3^3`; `transp(M:real^3^3) ** (B:real^3^3) ** M`]
                LVS_TRACE_SPLIT_LOCAL) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[MATRIX_TRANSP_MUL; GSYM MATRIX_MUL_ASSOC] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN
  REWRITE_TAC[REAL_EQ_ADD_LCANCEL] THEN
  ABBREV_TAC `g3 = basis 3 dot (matrix_inv(Ge0:real^3^3) ** basis 3)` THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  SUBGOAL_THEN `inv(sqrt g3) * inv(sqrt g3) = inv g3` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_INV_MUL; GSYM REAL_POW_2] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC SQRT_POW_2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

(* LVS_TRACE_SPLIT: tr_g B = tr_h(J^T B J) + B(n,n). *)

let LVS_TRACE_SPLIT = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) W f u x (B:real^3^3).
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     open_in top W /\ lvs_regular atlas W f u /\ x IN lvs_set W f u
     ==> trace(matrix_inv(g x) ** B) =
         trace(matrix_inv(lvs_metric top atlas g W f u x) **
               (transp(matrix(lvs_jac top atlas W f u x)) ** B **
                matrix(lvs_jac top atlas W f u x))) +
         lvs_normal atlas g f x dot (B ** lvs_normal atlas g f x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LVS_TRACE_SPLIT_FORM THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `W:A->bool`; `f:A->real`; `u:real`; `x:A`]
                LVS_POINT_FORM) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The orthonormal-frame form of the Gauss equation (MT's                    *)
(* R_N = 2 (K_M(e1,e2) + det S), with det S = S11 S22 - S12^2 in an          *)
(* orthonormal frame) and the symmetry of the second fundamental form.      *)
(* ------------------------------------------------------------------------- *)

(* The frame statement in the normal form (local algebra). *)

let LVS_FRAME_FORM = prove
 (`!(G0:real^3^3) (h:real^2^2) (sf:real^2^2) (J:real^2->real^3) (n:real^3).
     (?S (G:real^3->real^3^3) z (D:real^3->real^3).
        metric_field S G /\ lvs_iota z IN S /\
        linear D /\ invertible(matrix D) /\
        G(lvs_iota z) = transp(matrix D) ** G0 ** matrix D /\
        h = lvs_hslice G z /\ sf = lvs_IIloc G z /\ (!v. J v = D(lvs_iota v)) /\
        n = inv(sqrt(basis 3 dot (matrix_inv(G(lvs_iota z)) ** basis 3))) %
            D(matrix_inv(G(lvs_iota z)) ** basis 3))
     ==> ?v1 v2:real^2.
           v1 dot (h ** v1) = &1 /\ v2 dot (h ** v2) = &1 /\
           v1 dot (h ** v2) = &0 /\
           J v1 dot (G0 ** J v1) = &1 /\ J v2 dot (G0 ** J v2) = &1 /\
           J v1 dot (G0 ** J v2) = &0 /\
           J v1 dot (G0 ** n) = &0 /\ J v2 dot (G0 ** n) = &0 /\
           n dot (G0 ** n) = &1 /\
           det(matrix_inv h ** sf) =
           (v1 dot (sf ** v1)) * (v2 dot (sf ** v2)) - (v1 dot (sf ** v2)) pow 2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3->bool` (X_CHOOSE_THEN `G:real^3->real^3^3`
    (X_CHOOSE_THEN `z:real^2` (X_CHOOSE_THEN `D:real^3->real^3`
      STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN
   `!a b:real^3. (D:real^3->real^3) a dot ((G0:real^3^3) ** D b) =
                 a dot ((G:real^3->real^3^3)(lvs_iota z) ** b)`
  (LABEL_TAC "dg") THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[ASSUME `(G:real^3->real^3^3)(lvs_iota z) =
                        transp(matrix(D:real^3->real^3)) ** (G0:real^3^3) ** matrix D`] THEN
    REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
    SIMP_TAC[MATRIX_WORKS; ASSUME `linear(D:real^3->real^3)`];
    ALL_TAC] THEN
  UNDISCH_TAC `(G:real^3->real^3^3)(lvs_iota z) =
               transp(matrix(D:real^3->real^3)) ** (G0:real^3^3) ** matrix D` THEN
  DISCH_THEN(K ALL_TAC) THEN
  SUBGOAL_THEN `invertible((G:real^3->real^3^3)(lvs_iota z))` ASSUME_TAC THENL
   [MATCH_MP_TAC LVS_POSDEF_INVERTIBLE THEN ASM_MESON_TAC[metric_field];
    ALL_TAC] THEN
  SUBGOAL_THEN `invertible(lvs_hslice (G:real^3->real^3^3) z)` ASSUME_TAC THENL
   [MATCH_MP_TAC LVS_POSDEF_INVERTIBLE THEN
    MP_TAC(MATCH_MP LVS_HSLICE_METRIC (ASSUME `metric_field S (G:real^3->real^3^3)`)) THEN
    REWRITE_TAC[metric_field; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^2` o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `J = (D:real^3->real^3) o lvs_iota` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBST1_TAC(ASSUME `h = lvs_hslice (G:real^3->real^3^3) z`) THEN
  SUBST1_TAC(ASSUME `sf = lvs_IIloc (G:real^3->real^3^3) z`) THEN
  SUBST1_TAC(ASSUME
   `n = inv(sqrt(basis 3 dot (matrix_inv((G:real^3->real^3^3)(lvs_iota z)) **
                              basis 3))) %
        (D:real^3->real^3)(matrix_inv(G(lvs_iota z)) ** basis 3)`) THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `G:real^3->real^3^3`; `z:real^2`]
                LVS_SLICE_FRAMES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `S2:real^2^2` (X_CHOOSE_THEN `S3:real^3^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 (LABEL_TAC "i1" o SYM)
          (CONJUNCTS_THEN2 (LABEL_TAC "i2" o SYM) (LABEL_TAC "e3"))))))))) THEN
  (* the G0-unit normal is D of the third frame vector *)
  SUBGOAL_THEN
   `inv(sqrt(basis 3 dot (matrix_inv((G:real^3->real^3^3)(lvs_iota z)) ** basis 3))) %
    (D:real^3->real^3)(matrix_inv(G(lvs_iota z)) ** basis 3) =
    D(transp(S3:real^3^3) ** basis 3)`
  SUBST1_TAC THENL
   [USE_THEN "e3" (fun th -> REWRITE_TAC[th]) THEN
    SIMP_TAC[LINEAR_CMUL; ASSUME `linear(D:real^3->real^3)`];
    ALL_TAC] THEN
  (* orthonormality of the two frames *)
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= 2 /\ 1 <= j /\ j <= 2
          ==> (transp(S2:real^2^2) ** basis i) dot
              (lvs_hslice (G:real^3->real^3^3) z ** (transp S2 ** basis j)) =
              if i = j then &1 else &0`
  (LABEL_TAC "o2") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_GFRAME_ORTHO THEN
    ASM_REWRITE_TAC[DIMINDEX_2];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
          ==> (transp(S3:real^3^3) ** basis i) dot
              ((G:real^3->real^3^3)(lvs_iota z) ** (transp S3 ** basis j)) =
              if i = j then &1 else &0`
  (LABEL_TAC "o3") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_GFRAME_ORTHO THEN
    ASM_REWRITE_TAC[DIMINDEX_3];
    ALL_TAC] THEN
  (* the determinant in the frame *)
  SUBGOAL_THEN
   `!v w. v dot (lvs_IIloc (G:real^3->real^3^3) z ** w) =
          --((christoffel G (lvs_iota z) (lvs_iota v) (lvs_iota w))$3) /
          sqrt(basis 3 dot (matrix_inv(G(lvs_iota z)) ** basis 3))`
  (LABEL_TAC "iid") THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC LVS_IILOC_DOT THEN
    EXISTS_TAC `S:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `det(matrix_inv(lvs_hslice (G:real^3->real^3^3) z) ** lvs_IIloc G z) =
    ((transp(S2:real^2^2) ** basis 1) dot (lvs_IIloc G z ** (transp S2 ** basis 1))) *
    ((transp S2 ** basis 2) dot (lvs_IIloc G z ** (transp S2 ** basis 2))) -
    ((transp S2 ** basis 1) dot (lvs_IIloc G z ** (transp S2 ** basis 2))) pow 2`
  (LABEL_TAC "det") THENL
   [MP_TAC(ISPECL [`S:real^3->bool`; `G:real^3->real^3^3`; `z:real^2`; `S2:real^2^2`]
                  LVS_DET_SLICE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MP_TAC(ISPECL [`S:real^3->bool`; `G:real^3->real^3^3`; `lvs_iota(z:real^2)`;
                   `lvs_iota(transp(S2:real^2^2) ** basis 2)`;
                   `lvs_iota(transp(S2:real^2^2) ** basis 1)`] CHRISTOFFEL_SYM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "iid" (fun th -> REWRITE_TAC[th]) THEN
    MP_TAC(ISPECL [`S:real^3->bool`; `G:real^3->real^3^3`; `lvs_iota(z:real^2)`]
                  LVS_G33_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ABBREV_TAC `g33 = basis 3 dot (matrix_inv((G:real^3->real^3^3)(lvs_iota z)) ** basis 3)` THEN
    SUBGOAL_THEN `&0 < sqrt g33 /\ sqrt g33 pow 2 = g33` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
    ABBREV_TAC `r = sqrt g33` THEN
    UNDISCH_TAC `r pow 2 = g33` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`transp(S2:real^2^2) ** basis 1:real^2`;
                        `transp(S2:real^2^2) ** basis 2:real^2`] THEN
  REWRITE_TAC[o_THM] THEN
  USE_THEN "i1" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "i2" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "dg" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "det" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "o2" (fun o2 -> USE_THEN "o3" (fun o3 -> SIMP_TAC[o2; o3; ARITH])));;

(* MT's form of the Gauss equation at x: an orthonormal frame of the leaf
   whose pushforward, with the unit normal, is orthonormal for g x, and
   det S = S11 S22 - S12^2 in that frame.  With LVS_GAUSS this gives
   R_N = R - 2 Ric(n,n) + 2 (S11 S22 - S12^2). *)

let LVS_GAUSS_FRAME = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) W f u x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     open_in top W /\ lvs_regular atlas W f u /\ x IN lvs_set W f u
     ==> ?v1 v2:real^2.
           v1 dot (lvs_metric top atlas g W f u x ** v1) = &1 /\
           v2 dot (lvs_metric top atlas g W f u x ** v2) = &1 /\
           v1 dot (lvs_metric top atlas g W f u x ** v2) = &0 /\
           lvs_jac top atlas W f u x v1 dot (g x ** lvs_jac top atlas W f u x v1) = &1 /\
           lvs_jac top atlas W f u x v2 dot (g x ** lvs_jac top atlas W f u x v2) = &1 /\
           lvs_jac top atlas W f u x v1 dot (g x ** lvs_jac top atlas W f u x v2) = &0 /\
           lvs_jac top atlas W f u x v1 dot (g x ** lvs_normal atlas g f x) = &0 /\
           lvs_jac top atlas W f u x v2 dot (g x ** lvs_normal atlas g f x) = &0 /\
           lvs_normal atlas g f x dot (g x ** lvs_normal atlas g f x) = &1 /\
           det(matrix_inv(lvs_metric top atlas g W f u x) **
               lvs_II top atlas g W f u x) =
           (v1 dot (lvs_II top atlas g W f u x ** v1)) *
           (v2 dot (lvs_II top atlas g W f u x ** v2)) -
           (v1 dot (lvs_II top atlas g W f u x ** v2)) pow 2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LVS_FRAME_FORM THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `W:A->bool`; `f:A->real`; `u:real`; `x:A`]
                LVS_POINT_FORM) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* The second fundamental form is symmetric. *)

let LVS_II_SYM = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) W f u x v w.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     open_in top W /\ lvs_regular atlas W f u /\ x IN lvs_set W f u
     ==> v dot (lvs_II top atlas g W f u x ** w) =
         w dot (lvs_II top atlas g W f u x ** v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `W:A->bool`; `f:A->real`; `u:real`; `x:A`]
                LVS_POINT_FORM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3->bool` (X_CHOOSE_THEN `G:real^3->real^3^3`
    (X_CHOOSE_THEN `z:real^2` (X_CHOOSE_THEN `D:real^3->real^3`
      STRIP_ASSUME_TAC)))) THEN
  SUBST1_TAC(ASSUME `lvs_II top (atlas:((A->bool)#(A->real^3))->bool)
                       (g:A->real^3^3) W f u x = lvs_IIloc (G:real^3->real^3^3) z`) THEN
  SUBGOAL_THEN
   `!v w. v dot (lvs_IIloc (G:real^3->real^3^3) z ** w) =
          --((christoffel G (lvs_iota z) (lvs_iota v) (lvs_iota w))$3) /
          sqrt(basis 3 dot (matrix_inv(G(lvs_iota z)) ** basis 3))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC LVS_IILOC_DOT THEN
    EXISTS_TAC `S:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `G:real^3->real^3^3`; `lvs_iota(z:real^2)`;
                 `lvs_iota(v:real^2)`; `lvs_iota(w:real^2)`] CHRISTOFFEL_SYM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REFL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Regularity in any chart.  lvs_regular (preferred charts) is               *)
(* equivalent to mfd_regular_on (all charts) on the level set; a nonzero     *)
(* |grad f|^2 gives regularity; |grad f|^2 as a quadratic form in lvs_df.    *)
(* ------------------------------------------------------------------------- *)

(* The derivative of f is nonzero in every chart at a point of an adapted
   parametrization (the argument of LVS_REGULAR_ADAPTED, for any chart). *)

let LVS_ADAPTED_DERIV_NZ = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) W f u s e e' c x.
     smooth_manifold_atlas top atlas /\ open_in top W /\
     mfd_smooth_on atlas W (\x. lift(f x)) /\
     mfd_diffeo euclidean (open_set_atlas (:real^3)) s top atlas (IMAGE e s) e e' /\
     (!y. y IN s ==> f(e y) = u + y$3) /\ x IN IMAGE e s /\ x IN W /\
     c IN atlas /\ x IN FST c
     ==> ~(frechet_derivative (\y. lift(f(chart_inv c y))) (at (SND c x)) =
           (\h. vec 0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(x:A) IN IMAGE (e:real^3->A) s` THEN REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:real^3`
    (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `s:real^3->bool`; `e:real^3->A`; `e':A->real^3`;
                 `c:(A->bool)#(A->real^3)`] LVS_PARAM_CHART_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `y0 IN {y | y IN s /\ (e:real^3->A) y IN FST(c:(A->bool)#(A->real^3))}`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC
   `K = frechet_derivative (SND(c:(A->bool)#(A->real^3)) o (e:real^3->A)) (at y0)` THEN
  SUBGOAL_THEN
   `((SND(c:(A->bool)#(A->real^3)) o (e:real^3->A)) has_derivative K) (at y0)`
  ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `{y | y IN s /\ (e:real^3->A) y IN FST(c:(A->bool)#(A->real^3))}` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `D = frechet_derivative (\y. lift((f:A->real)(chart_inv c y)))
                           (at (SND(c:(A->bool)#(A->real^3)) x))` THEN
  SUBGOAL_THEN
   `((\y. lift((f:A->real)(chart_inv c y))) has_derivative D)
    (at (SND(c:(A->bool)#(A->real^3)) x))`
  ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER W)` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`;
                            `atlas:((A->bool)#(A->real^3))->bool`] THEN
      ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
      ASM_MESON_TAC[MFDM_CHART];
      UNDISCH_TAC `mfd_smooth_on (atlas:((A->bool)#(A->real^3))->bool) W
                                 (\x. lift((f:A->real) x))` THEN
      REWRITE_TAC[mfd_smooth_on] THEN
      DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^3)`) THEN
      ASM_REWRITE_TAC[o_DEF];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(((\y. lift((f:A->real)(chart_inv c y))) o
      (SND(c:(A->bool)#(A->real^3)) o (e:real^3->A))) has_derivative
     ((D:real^3->real^1) o (K:real^3->real^3))) (at y0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[o_THM] THEN
    UNDISCH_TAC `((\y. lift((f:A->real)(chart_inv c y))) has_derivative D)
                 (at (SND(c:(A->bool)#(A->real^3)) x))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(((\y. lift((f:A->real)(chart_inv c y))) o
      (SND(c:(A->bool)#(A->real^3)) o (e:real^3->A))) has_derivative
     (\h. lift(h$3))) (at y0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    EXISTS_TAC `\y:real^3. lift(u + y$3)` THEN
    EXISTS_TAC `{y | y IN s /\ (e:real^3->A) y IN FST(c:(A->bool)#(A->real^3))}` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM; o_THM] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
      SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^3)) (SND c ((e:real^3->A) y)) =
                    e y` SUBST1_TAC THENL
       [ASM_MESON_TAC[MFDM_CHART]; ASM_SIMP_TAC[]];
      REWRITE_TAC[LIFT_ADD] THEN
      GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV o ABS_CONV)
        [GSYM VECTOR_ADD_LID] THEN
      MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN
      REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
      MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
      REWRITE_TAC[LINEAR_LIFT_COMPONENT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(D:real^3->real^1) o (K:real^3->real^3) = (\h. lift(h$3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_AT THEN
    EXISTS_TAC `(\y. lift((f:A->real)(chart_inv c y))) o
                (SND(c:(A->bool)#(A->real^3)) o (e:real^3->A))` THEN
    EXISTS_TAC `y0:real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  UNDISCH_TAC `(D:real^3->real^1) o (K:real^3->real^3) = (\h. lift(h$3))` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `basis 3:real^3`) THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH; GSYM DROP_EQ; LIFT_DROP;
           DROP_VEC] THEN
  REAL_ARITH_TAC);;

(* Regularity from mfd_regular_on (all charts) on the level set. *)

let LVS_REGULAR_MFD = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) W f u.
     smooth_manifold_atlas top atlas /\ open_in top W /\
     mfd_smooth_on atlas W (\x. lift(f x)) /\
     mfd_regular_on atlas (lvs_set W f u) f
     ==> lvs_regular atlas W f u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lvs_regular] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[LVS_SET_SUBSET; OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `mfd_regular_on (atlas:((A->bool)#(A->real^3))->bool)
                              (lvs_set W f u) f` THEN
  REWRITE_TAC[mfd_regular_on] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[IN_INTER]);;

(* The preferred-chart regularity is chart independent. *)

let LVS_REGULAR_ALT = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) W f u.
     smooth_manifold_atlas top atlas /\ open_in top W
     ==> (lvs_regular atlas W f u <=>
          mfd_smooth_on atlas W (\x. lift(f x)) /\
          mfd_regular_on atlas (lvs_set W f u) f)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `mfd_smooth_on (atlas:((A->bool)#(A->real^3))->bool) W
                                (\x. lift((f:A->real) x))` ASSUME_TAC THENL
     [ASM_MESON_TAC[lvs_regular]; ALL_TAC] THEN
    ASM_REWRITE_TAC[mfd_regular_on; IN_INTER] THEN
    MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^3)`; `x:A`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:A) IN W` ASSUME_TAC THENL
     [ASM_MESON_TAC[LVS_SET_SUBSET; SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `W:A->bool`; `f:A->real`; `u:real`; `x:A`]
                  LVS_PREFERRED_ADAPTED) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` (X_CHOOSE_THEN `e:real^3->A`
      (X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `(x:A) IN IMAGE (e:real^3->A) s` ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_INTER]; ALL_TAC] THEN
    MATCH_MP_TAC LVS_ADAPTED_DERIV_NZ THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `W:A->bool`; `u:real`;
                          `s:real^3->bool`; `e:real^3->A`; `e':A->real^3`] THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC THEN MATCH_MP_TAC LVS_REGULAR_MFD THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]]);;

(* A nonzero |grad f|^2 (in the preferred chart) gives regularity. *)

let LVS_REGULAR_GRAD2 = prove
 (`!(atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) W f u.
     mfd_smooth_on atlas W (\x. lift(f x)) /\
     (!x. x IN lvs_set W f u
          ==> ~(lgrad2 (metric_local atlas (chart_at atlas x) g)
                       (f o chart_inv (chart_at atlas x))
                       (SND(chart_at atlas x) x) = &0))
     ==> lvs_regular atlas W f u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lvs_regular] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[CONTRAPOS_THM] THEN
  DISCH_TAC THEN REWRITE_TAC[lgrad2; o_THM] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[DROP_VEC; REAL_MUL_LZERO; REAL_MUL_RZERO; SUM_0]);;

(* |grad f|^2 in the preferred chart as the quadratic form of lvs_df. *)

let LVS_GRAD2 = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) f x.
     smooth_manifold_atlas top atlas /\ x IN topspace top
     ==> lgrad2 (metric_local atlas (chart_at atlas x) g)
                (f o chart_inv (chart_at atlas x)) (SND(chart_at atlas x) x) =
         lvs_df atlas f x dot (matrix_inv(g x) ** lvs_df atlas f x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `x:A`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[lgrad2; lvs_df; o_THM] THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `d = frechet_derivative
          (\y. lift((f:A->real)
                (chart_inv (chart_at (atlas:((A->bool)#(A->real^3))->bool) x) y)))
          (at (SND(chart_at atlas x) x))` THEN
  ABBREV_TAC `M = matrix_inv((g:A->real^3^3) x)` THEN
  REWRITE_TAC[dot; matrix_vector_mul; DIMINDEX_3; SUM_3] THEN
  SIMP_TAC[LAMBDA_BETA; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC);;

