(* ========================================================================= *)
(* pc_p2b_kglob (Part 2B, a step of the proof of P2B_SPLIT_ROUND_STATEMENT:  *)
(* the compact leaf and the global product).                                 *)
(*                                                                           *)
(* P2BKG_SHELL_PRIMITIVE: for a parallel field X on an open W and an         *)
(* mfd_param psi of a shell annulus r1 r2 of real^3 into W, the 1-form       *)
(* omega = g(X,.) has a primitive h on psi(shell): smooth there, with        *)
(* derivative in every chart c the chart form p2bkg_cform                    *)
(* (metric_local c g ** mfd_vrep X c).  Route: a parallel field lowered by   *)
(* the metric is closed in coordinates (P2BPC_PARALLEL_LOWER_CLOSED), the    *)
(* pullback p2bkg_pform by psi agrees locally with the pullback of the chart *)
(* form (P2BKG_PFORM_LOCAL) and is closed, P2BPC_SHELL_EXACT (pc_p2b_poinc)  *)
(* gives a primitive on the shell, pushed forward by the inverse             *)
(* parametrization.                                                          *)
(*                                                                           *)
(* The estimate P2BKG_SHELL_OSC: a primitive whose slab pullbacks are        *)
(* e-close to kappa e_3 varies by at most 2 e (4 + log r2 - log r1)          *)
(* from kappa log(norm y) + const.  Zero sets of almost-height functions     *)
(* are compact (P2BKG_LEVEL_SET_COMPACT) and the level sets of the shell     *)
(* primitive are regular for a unit X (P2BKG_LEVEL_REGULAR, dh(X) = 1;       *)
(* P2BKG_SHELL_PRIMITIVE_REGULAR).                                           *)
(*                                                                           *)
(* The orbit form, in flow-box coordinates of pc_p2b_kfl: for a compact      *)
(* connected nonempty level set L of a primitive of g(X,.) and level sets of *)
(* every thickness, (y,r) |-> Phi_r(y) is a bijection L x R -> M             *)
(* (P2BKG_ORBIT_BIJECTIVE: flow-out open and closed, leaf transport, no      *)
(* returns); shells with the logarithmic estimate give compact nonempty      *)
(* thick level sets (P2BKG_SHELL_THICK_FAMILY).                              *)
(* ========================================================================= *)

needs "src/pc_p2b_poinc.ml";;
needs "src/pc_lrg.ml";;
needs "src/pc_p2b_splitreq.ml";;
needs "src/pc_mfd_riem.ml";;
needs "src/pc_mfd_level.ml";;
needs "src/pc_p2b_parkit.ml";;
needs "src/pc_p2b_kfl.ml";;
needs "src/pc_grg_isom.ml";;

prioritize_real();;
type_invention_error := true;;

(* P2BPC.P7 A parallel vector field lowered by the metric is a closed       *)
(* covector field (coordinate form): if D W = -Gamma(., W) on U then the    *)
(* Jacobian of G W is symmetric, (G W)' e_i . e_j = W . G Gamma(e_i, e_j)   *)
(* (metric compatibility LRG_MDERIV_CHRISTOFFEL and CHRISTOFFEL_SYM).       *)

let P2BPC_PARALLEL_LOWER_CLOSED = prove
 (`!U (G:real^N->real^N^N) (W:real^N->real^N).
     metric_field U G /\ smooth_map_on U W /\
     (!z w. z IN U ==> frechet_derivative W (at z) w + christoffel G z w (W z) = vec 0)
     ==> smooth_map_on U (\z. G z ** W z) /\
         !y i j. y IN U /\ 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
                 ==> (partial_derivative i (\z. G z ** W z) y)$j =
                     (partial_derivative j (\z. G z ** W z) y)$i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open (U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_SMOOTH_MATVEC THEN ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y:real^N`; `i:num`; `j:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!d. frechet_derivative (\z. (G:real^N->real^N^N) z ** (W:real^N->real^N) z) (at y) d =
        mderiv G y d ** W y - G y ** christoffel G y d (W y)`
  ASSUME_TAC THENL
   [X_GEN_TAC `d:real^N` THEN
    MP_TAC(ISPECL [`G:real^N->real^N^N`;
                   `frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                        (G:real^N->real^N^N)) (at y)`;
                   `W:real^N->real^N`; `frechet_derivative (W:real^N->real^N) (at y)`;
                   `y:real^N`] LRG_HAS_DERIVATIVE_MATVEC) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [ASM_MESON_TAC[LRG_METRIC_FIELD_DIFF];
        MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
                       SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
        ASM_MESON_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
    REWRITE_TAC[mderiv] THEN
    SUBGOAL_THEN `frechet_derivative (W:real^N->real^N) (at y) d =
                  --(christoffel (G:real^N->real^N^N) y d (W y))` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^N`; `d:real^N`]) THEN ASM_REWRITE_TAC[] THEN
      VECTOR_ARITH_TAC;
      REWRITE_TAC[MATRIX_VECTOR_MUL_RNEG] THEN VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. 1 <= b /\ b <= dimindex(:N)
          ==> (mderiv (G:real^N->real^N^N) y (basis a) ** (W:real^N->real^N) y -
               G y ** christoffel G y (basis a) (W y))$b =
              W y dot (G y ** christoffel G y (basis a) (basis b))`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `!v:real^N. v$b = basis b dot v` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_SIMP_TAC[DOT_BASIS]; ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `basis b:real^N`;
                   `basis a:real^N`; `(W:real^N->real^N) y`] LRG_MDERIV_CHRISTOFFEL) THEN
    ASM_REWRITE_TAC[DOT_RSUB] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[partial_derivative] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC CHRISTOFFEL_SYM THEN
  EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]);;

(* P2BKG.K2 The 1-form omega = g(X,.) of a parallel field X in a chart c:   *)
(* p2bkg_cform atlas g X c = metric_local c g ** mfd_vrep X c is smooth and *)
(* closed on the chart image of FST c INTER W.                              *)

let p2bkg_cform = new_definition
 `p2bkg_cform (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) (X:A->real^3)
              (c:(A->bool)#(A->real^3)) =
    \y:real^3. metric_local atlas c g y ** mfd_vrep atlas X c y`;;

let P2BKG_CFORM_CLOSED = prove
 (`!top atlas (g:A->real^3^3) X W c.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ open_in top W /\
     p2b_parallel_on atlas g W X /\ c IN atlas
     ==> open (IMAGE (SND c) (FST c INTER W)) /\
         smooth_map_on (IMAGE (SND c) (FST c INTER W)) (p2bkg_cform atlas g X c) /\
         !y i j. y IN IMAGE (SND c) (FST c INTER W) /\
                 1 <= i /\ i <= dimindex(:3) /\ 1 <= j /\ j <= dimindex(:3)
                 ==> (partial_derivative i (p2bkg_cform atlas g X c) y)$j =
                     (partial_derivative j (p2bkg_cform atlas g X c) y)$i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `U = IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c INTER W)` THEN
  SUBGOAL_THEN `open (U:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN
    MATCH_MP_TAC OPEN_IN_INTER THEN ASM_MESON_TAC[MFDM_CHART];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `metric_field U (metric_local atlas (c:(A->bool)#(A->real^3)) (g:A->real^3^3))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (g:A->real^3^3)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^3)`) THEN
    ASM_REWRITE_TAC[metric_field] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `U SUBSET IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` ASSUME_TAC THENL
     [EXPAND_TAC "U" THEN SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` THEN ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `p2b_parallel_on atlas (g:A->real^3^3) W X` THEN
  REWRITE_TAC[p2b_parallel_on] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `c:(A->bool)#(A->real^3)`)
                             (MP_TAC o SPEC `c:(A->bool)#(A->real^3)`)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `metric_local atlas (c:(A->bool)#(A->real^3)) (g:A->real^3^3)`;
                 `mfd_vrep atlas (X:A->real^3) (c:(A->bool)#(A->real^3))`]
                P2BPC_PARALLEL_LOWER_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[p2bkg_cform] THEN MESON_TAC[]);;

(* P2BKG.K3 Parametrizations: the chart representative SND c o psi is      *)
(* smooth on the open set of parameters mapped into FST c; the pullback     *)
(* p2bkg_pform of omega = g(X,.) by psi agrees there with the pullback of  *)
(* the chart form p2bkg_cform through SND c o psi.                          *)

let P2BKG_PARAM_CHART_SMOOTH = prove
 (`!top atlas s (psi:real^3->A) c.
     smooth_manifold_atlas top atlas /\ open s /\ mfd_param top atlas s psi /\ c IN atlas
     ==> open {z | z IN s /\ psi z IN FST c} /\
         smooth_map_on {z | z IN s /\ psi z IN FST c} (\z. SND c (psi z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `mfd_param top atlas s (psi:real^3->A)` THEN REWRITE_TAC[mfd_param] THEN
  DISCH_THEN(X_CHOOSE_TAC `psi':A->real^3`) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[OPEN_IN] THEN MATCH_MP_TAC MFDM_OPEN_IN_PREIMAGE THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[GSYM OPEN_IN] THEN
    ASM_MESON_TAC[MFDM_CHART];
    ALL_TAC] THEN
  UNDISCH_TAC `mfd_diffeo euclidean (open_set_atlas (:real^3)) s (top:A topology)
                (atlas:((A->bool)#(A->real^3))->bool)
                (IMAGE (psi:real^3->A) s) psi psi'` THEN
  REWRITE_TAC[mfd_diffeo; mfd_smooth_map] THEN
  DISCH_THEN(MP_TAC o SPECL [`((:real^3),(\x:real^3. x))`; `c:(A->bool)#(A->real^3)`] o
             CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[open_set_atlas; IN_SING; FST; SND; IMAGE_ID; IN_UNIV; INTER_UNIV] THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ] SMOOTH_MAP_ON_EQ) THEN
  SIMP_TAC[IN_ELIM_THM; o_THM; MFDM_CHART_INV_ID; IN_UNIV]);;

let p2bkg_pform = new_definition
 `p2bkg_pform (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) (X:A->real^3)
              (psi:real^3->A) =
    \y. (lambda j. X(psi y) dot
                   (g(psi y) **
                    frechet_derivative (\z. SND(chart_at atlas (psi y)) (psi z)) (at y)
                                       (basis j))):real^3`;;

let P2BKG_PFORM_LOCAL = prove
 (`!top atlas (g:A->real^3^3) X s (psi:real^3->A) c y.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ open s /\
     mfd_param top atlas s psi /\ c IN atlas /\ y IN s /\ psi y IN FST c
     ==> p2bkg_pform atlas g X psi y =
         p2bpc_pull (\z. SND c (psi z)) (p2bkg_cform atlas g X c) y`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `x = (psi:real^3->A) y` THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFDM_CHART; OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  ABBREV_TAC `c' = chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)` THEN
  SUBGOAL_THEN `(c':(A->bool)#(A->real^3)) IN atlas /\ x IN FST c'` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c'" THEN MATCH_MP_TAC CHART_AT THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `s:real^3->bool`;
                 `psi:real^3->A`; `c:(A->bool)#(A->real^3)`] P2BKG_PARAM_CHART_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `s:real^3->bool`;
                 `psi:real^3->A`; `c':(A->bool)#(A->real^3)`] P2BKG_PARAM_CHART_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `tau = \z. SND (c:(A->bool)#(A->real^3)) ((psi:real^3->A) z)` THEN
  ABBREV_TAC `tau' = \z. SND (c':(A->bool)#(A->real^3)) ((psi:real^3->A) z)` THEN
  SUBGOAL_THEN `((tau:real^3->real^3) has_derivative frechet_derivative tau (at y)) (at y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    EXISTS_TAC `{z:real^3 | z IN s /\ (psi:real^3->A) z IN FST (c:(A->bool)#(A->real^3))}` THEN
    EXPAND_TAC "tau" THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  ABBREV_TAC `J = chart_jac (c:(A->bool)#(A->real^3)) c' (x:A)` THEN
  SUBGOAL_THEN `linear (J:real^3->real^3) /\
                (!v. J(chart_jac c' (c:(A->bool)#(A->real^3)) (x:A) v) = v)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `FST(c:(A->bool)#(A->real^3))`; `SND(c:(A->bool)#(A->real^3))`;
                     `FST(c':(A->bool)#(A->real^3))`; `SND(c':(A->bool)#(A->real^3))`; `x:A`]
        CHART_JAC_LINEAR) THEN
      ASM_REWRITE_TAC[PAIR; IN_INTER];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `FST(c':(A->bool)#(A->real^3))`; `SND(c':(A->bool)#(A->real^3))`;
                     `FST(c:(A->bool)#(A->real^3))`; `SND(c:(A->bool)#(A->real^3))`; `x:A`]
        CHART_JAC_INVERSE) THEN
      ASM_REWRITE_TAC[PAIR; IN_INTER; FUN_EQ_THM; o_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v. frechet_derivative (tau':real^3->real^3) (at y) v =
                    (J:real^3->real^3) (frechet_derivative (tau:real^3->real^3) (at y) v)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `((tau':real^3->real^3) has_derivative
                   ((J:real^3->real^3) o frechet_derivative (tau:real^3->real^3) (at y)))
                  (at y)`
    (fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th); o_THM]) THEN
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    MAP_EVERY EXISTS_TAC
     [`chart_trans (c:(A->bool)#(A->real^3)) c' o (tau:real^3->real^3)`;
      `{z:real^3 | z IN s /\ (psi:real^3->A) z IN FST (c:(A->bool)#(A->real^3))} INTER
       {z | z IN s /\ psi z IN FST (c':(A->bool)#(A->real^3))}`] THEN
    ASM_SIMP_TAC[OPEN_INTER; IN_INTER; IN_ELIM_THM] THEN CONJ_TAC THENL
     [X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
      MAP_EVERY EXPAND_TAC ["tau"; "tau'"] THEN REWRITE_TAC[o_THM; chart_trans] THEN
      AP_TERM_TAC THEN ASM_MESON_TAC[MFDM_CHART];
      MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(tau:real^3->real^3) y = SND (c:(A->bool)#(A->real^3)) (x:A)` SUBST1_TAC THENL
       [EXPAND_TAC "tau" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "J" THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `FST(c:(A->bool)#(A->real^3))`; `SND(c:(A->bool)#(A->real^3))`;
                     `FST(c':(A->bool)#(A->real^3))`; `SND(c':(A->bool)#(A->real^3))`; `x:A`]
        CHART_TRANS_HAS_DERIVATIVE) THEN
      ASM_REWRITE_TAC[PAIR; IN_INTER]];
    ALL_TAC] THEN
  SUBGOAL_THEN `transp((g:A->real^3^3) x) = g x` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `x:A`] METRIC_LOCAL_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `riemannian_metric atlas (g:A->real^3^3)` THEN
    REWRITE_TAC[riemannian_metric; metric_field] THEN
    DISCH_THEN(MP_TAC o SPEC `c':(A->bool)#(A->real^3)`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `SND (c':(A->bool)#(A->real^3)) x`) THEN
    ANTS_TAC THENL [REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(tau:real^3->real^3) y = SND (c:(A->bool)#(A->real^3)) (x:A)` ASSUME_TAC THENL
   [EXPAND_TAC "tau" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^3)) (SND c (x:A)) = x` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFDM_CHART]; ALL_TAC] THEN
  REWRITE_TAC[p2bkg_pform; p2bpc_pull; p2bkg_cform; metric_local; mfd_vrep] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CART_EQ] THEN SIMP_TAC[LAMBDA_BETA] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[MATRIX_WORKS; DOT_MATRIX_TRANSP_LMUL] THEN
  REWRITE_TAC[GSYM DOT_MATRIX_TRANSP_LMUL] THEN ASM_REWRITE_TAC[]);;

(* P2BKG.K4 The pullback p2bkg_pform of omega = g(X,.) by a parametrization *)
(* psi of an open s into W (X parallel on W) is smooth and closed on s.     *)

let P2BKG_PARTIAL_LOCAL = prove
 (`!(f:real^3->real^3) f' N y i.
     open N /\ y IN N /\ (!z. z IN N ==> f z = f' z) /\ f' differentiable at y
     ==> partial_derivative i f y = partial_derivative i f' y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[partial_derivative] THEN AP_THM_TAC THEN
  SUBGOAL_THEN `((f:real^3->real^3) has_derivative frechet_derivative f' (at y)) (at y)`
  (fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
  MAP_EVERY EXISTS_TAC [`f':real^3->real^3`; `N:real^3->bool`] THEN
  ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN ASM_MESON_TAC[]);;

let P2BKG_PFORM_CLOSED = prove
 (`!top atlas (g:A->real^3^3) X W s (psi:real^3->A).
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ open_in top W /\
     p2b_parallel_on atlas g W X /\ open s /\ mfd_param top atlas s psi /\
     IMAGE psi s SUBSET W
     ==> smooth_map_on s (p2bkg_pform atlas g X psi) /\
         !y i j. y IN s /\ 1 <= i /\ i <= dimindex(:3) /\ 1 <= j /\ j <= dimindex(:3)
                 ==> (partial_derivative i (p2bkg_pform atlas g X psi) y)$j =
                     (partial_derivative j (p2bkg_pform atlas g X psi) y)$i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* the local data at a parameter y0 *)
  SUBGOAL_THEN
   `!y0. y0 IN s
         ==> ?N c. open N /\ y0 IN N /\ N SUBSET s /\ c IN atlas /\
                   smooth_map_on N (p2bpc_pull (\z. SND c ((psi:real^3->A) z))
                                               (p2bkg_cform atlas (g:A->real^3^3) X c)) /\
                   (!y i j. y IN N /\ 1 <= i /\ i <= dimindex(:3) /\
                            1 <= j /\ j <= dimindex(:3)
                            ==> (partial_derivative i (p2bpc_pull (\z. SND c (psi z))
                                                        (p2bkg_cform atlas g X c)) y)$j =
                                (partial_derivative j (p2bpc_pull (\z. SND c (psi z))
                                                        (p2bkg_cform atlas g X c)) y)$i) /\
                   (!y. y IN N ==> p2bkg_pform atlas g X psi y =
                                   p2bpc_pull (\z. SND c (psi z)) (p2bkg_cform atlas g X c) y)`
  ASSUME_TAC THENL
   [X_GEN_TAC `y0:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(psi:real^3->A) y0 IN topspace top` ASSUME_TAC THENL
     [UNDISCH_TAC `mfd_param top atlas s (psi:real^3->A)` THEN REWRITE_TAC[mfd_param] THEN
      DISCH_THEN(X_CHOOSE_THEN `psi':A->real^3` (MP_TAC o MATCH_MP MFD_DIFFEO_MAPS)) THEN
      REWRITE_TAC[continuous_map; TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) ((psi:real^3->A) y0)` THEN
    SUBGOAL_THEN `(c:(A->bool)#(A->real^3)) IN atlas /\ (psi:real^3->A) y0 IN FST c`
    STRIP_ASSUME_TAC THENL [EXPAND_TAC "c" THEN MATCH_MP_TAC CHART_AT THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `s:real^3->bool`;
                   `psi:real^3->A`; `c:(A->bool)#(A->real^3)`] P2BKG_PARAM_CHART_SMOOTH) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `X:A->real^3`; `W:A->bool`; `c:(A->bool)#(A->real^3)`] P2BKG_CFORM_CLOSED) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `{z:real^3 | z IN s /\ (psi:real^3->A) z IN FST (c:(A->bool)#(A->real^3))}` THEN
    EXISTS_TAC `c:(A->bool)#(A->real^3)` THEN
    SUBGOAL_THEN `IMAGE (\z. SND (c:(A->bool)#(A->real^3)) ((psi:real^3->A) z))
                        {z:real^3 | z IN s /\ psi z IN FST c} SUBSET
                  IMAGE (SND c) (FST c INTER W)` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN
      STRIP_TAC THEN REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `(psi:real^3->A) z` THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[IN_ELIM_THM];
      SET_TAC[];
      MATCH_MP_TAC P2BPC_PULL_SMOOTH THEN
      EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c INTER W)` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2BPC_PULL_CLOSED THEN
      EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c INTER W)` THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      MATCH_MP_TAC P2BKG_PFORM_LOCAL THEN
      EXISTS_TAC `top:A topology` THEN EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y0:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y0:real^3`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:real^3->bool` (X_CHOOSE_THEN `c:(A->bool)#(A->real^3)`
      STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `N:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `p2bpc_pull (\z. SND (c:(A->bool)#(A->real^3)) ((psi:real^3->A) z))
                           (p2bkg_cform atlas (g:A->real^3^3) X c)` THEN
    ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`y0:real^3`; `i:num`; `j:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y0:real^3`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:real^3->bool` (X_CHOOSE_THEN `c:(A->bool)#(A->real^3)`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN
     `!k. partial_derivative k (p2bkg_pform atlas (g:A->real^3^3) X (psi:real^3->A)) y0 =
          partial_derivative k (p2bpc_pull (\z. SND (c:(A->bool)#(A->real^3)) (psi z))
                                           (p2bkg_cform atlas g X c)) y0`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN MATCH_MP_TAC P2BKG_PARTIAL_LOCAL THEN EXISTS_TAC `N:real^3->bool` THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `N:real^3->bool` THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* P2BKG.K5 A primitive of omega = g(X,.) on the image of a shell           *)
(* parametrization: P2BPC_SHELL_EXACT for p2bkg_pform, pushed forward by    *)
(* the inverse parametrization; its differential in every chart is the     *)
(* chart form p2bkg_cform.                                                   *)

let P2BKG_INV_CHART_SMOOTH = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) s (psi:real^3->A) psi' c.
     smooth_manifold_atlas top atlas /\
     mfd_diffeo euclidean (open_set_atlas (:real^3)) s top atlas (IMAGE psi s) psi psi' /\
     c IN atlas
     ==> open (IMAGE (SND c) (FST c INTER IMAGE psi s)) /\
         smooth_map_on (IMAGE (SND c) (FST c INTER IMAGE psi s)) (\z. psi'(chart_inv c z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
    ASM_MESON_TAC[MFDM_CHART; mfd_diffeo];
    UNDISCH_TAC `mfd_diffeo euclidean (open_set_atlas (:real^3)) s (top:A topology)
                  (atlas:((A->bool)#(A->real^3))->bool) (IMAGE (psi:real^3->A) s) psi psi'` THEN
    REWRITE_TAC[mfd_diffeo; mfd_smooth_map] THEN
    DISCH_THEN(MP_TAC o SPECL [`c:(A->bool)#(A->real^3)`; `((:real^3),(\x:real^3. x))`] o
               CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[open_set_atlas; IN_SING; FST; SND; IN_UNIV;
                    SET_RULE `{x:A | x IN s} = s`] THEN
    MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ] SMOOTH_MAP_ON_EQ) THEN
    SIMP_TAC[o_THM]]);;

let P2BKG_SHELL_PRIMITIVE = prove
 (`!top atlas (g:A->real^3^3) X W r1 r2 (psi:real^3->A).
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ open_in top W /\
     p2b_parallel_on atlas g W X /\ &0 < r1 /\ r1 < r2 /\
     mfd_param top atlas (annulus r1 r2) psi /\ IMAGE psi (annulus r1 r2) SUBSET W
     ==> ?h:A->real.
            mfd_smooth_on atlas (IMAGE psi (annulus r1 r2)) (\x. lift(h x)) /\
            !c z. c IN atlas /\ z IN IMAGE (SND c) (FST c INTER IMAGE psi (annulus r1 r2))
                  ==> ((\y. lift(h(chart_inv c y))) has_derivative
                       (\u. lift(p2bkg_cform atlas g X c z dot u))) (at z)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `S = annulus r1 r2:real^3->bool` THEN
  SUBGOAL_THEN `open (S:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[P2BPC_ANNULUS_OPEN]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `W:A->bool`; `S:real^3->bool`; `psi:real^3->A`]
                P2BKG_PFORM_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`r1:real`; `r2:real`;
                 `p2bkg_pform atlas (g:A->real^3^3) X (psi:real^3->A)`] P2BPC_SHELL_EXACT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `hS:real^3->real^1` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `mfd_param top atlas S (psi:real^3->A)` THEN REWRITE_TAC[mfd_param] THEN
  DISCH_THEN(X_CHOOSE_TAC `psi':A->real^3`) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  EXISTS_TAC `\x:A. drop((hS:real^3->real^1)((psi':A->real^3) x))` THEN
  SUBGOAL_THEN
   `!c:(A->bool)#(A->real^3). c IN atlas
        ==> open (IMAGE (SND c) (FST c INTER IMAGE (psi:real^3->A) (S:real^3->bool))) /\
            smooth_map_on (IMAGE (SND c) (FST c INTER IMAGE psi S))
                          (\z. (psi':A->real^3)(chart_inv c z)) /\
            IMAGE (\z. psi'(chart_inv c z)) (IMAGE (SND c) (FST c INTER IMAGE psi S))
              SUBSET S`
  ASSUME_TAC THENL
   [X_GEN_TAC `c:(A->bool)#(A->real^3)` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `S:real^3->bool`;
                   `psi:real^3->A`; `psi':A->real^3`; `c:(A->bool)#(A->real^3)`]
                  P2BKG_INV_CHART_SMOOTH) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^3)) (SND c (x:A)) = x` SUBST1_TAC THENL
     [ASM_MESON_TAC[MFDM_CHART]; ASM SET_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[mfd_smooth_on; LIFT_DROP] THEN X_GEN_TAC `c:(A->bool)#(A->real^3)` THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^3)`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(\x:A. (hS:real^3->real^1)((psi':A->real^3) x)) o
                  chart_inv (c:(A->bool)#(A->real^3)) =
                  hS o (\z. psi'(chart_inv c z))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `S:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^3)`; `z:real^3`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^3)`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  ABBREV_TAC `x = chart_inv (c:(A->bool)#(A->real^3)) z` THEN
  SUBGOAL_THEN `(x:A) IN FST (c:(A->bool)#(A->real^3)) /\ SND c x = z /\
                x IN IMAGE (psi:real^3->A) (S:real^3->bool)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^3) IN IMAGE (SND (c:(A->bool)#(A->real^3)))
                                       (FST c INTER IMAGE (psi:real^3->A) (S:real^3->bool))` THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `x0:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(x:A) = x0` SUBST1_TAC THENL
     [EXPAND_TAC "x" THEN ASM_MESON_TAC[MFDM_CHART]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `y = (psi':A->real^3) x` THEN
  SUBGOAL_THEN `(y:real^3) IN (S:real^3->bool) /\ (psi:real^3->A) y = x` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `OC = IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c INTER IMAGE (psi:real^3->A) S)` THEN
  ABBREV_TAC `sig = \z. (psi':A->real^3)(chart_inv (c:(A->bool)#(A->real^3)) z)` THEN
  ABBREV_TAC `tau = \z. SND (c:(A->bool)#(A->real^3)) ((psi:real^3->A) z)` THEN
  SUBGOAL_THEN `((sig:real^3->real^3) has_derivative frechet_derivative sig (at z)) (at z)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    EXISTS_TAC `OC:real^3->bool` THEN EXPAND_TAC "sig" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(sig:real^3->real^3) z = y` ASSUME_TAC THENL
   [EXPAND_TAC "sig" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `S:real^3->bool`;
                 `psi:real^3->A`; `c:(A->bool)#(A->real^3)`] P2BKG_PARAM_CHART_SMOOTH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[mfd_param] THEN ASM_MESON_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
  SUBGOAL_THEN `((tau:real^3->real^3) has_derivative frechet_derivative tau (at y)) (at y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    EXISTS_TAC `{z:real^3 | z IN S /\ (psi:real^3->A) z IN FST (c:(A->bool)#(A->real^3))}` THEN
    EXPAND_TAC "tau" THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  (* D tau(y) o D sig(z) = identity, since tau o sig = identity on OC *)
  SUBGOAL_THEN `!u. frechet_derivative (tau:real^3->real^3) (at y)
                      (frechet_derivative (sig:real^3->real^3) (at z) u) = u`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`sig:real^3->real^3`; `tau:real^3->real^3`;
                   `frechet_derivative (sig:real^3->real^3) (at z)`;
                   `frechet_derivative (tau:real^3->real^3) (at y)`; `z:real^3`]
                  DIFF_CHAIN_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `((\x:real^3. x) has_derivative
                   (frechet_derivative (tau:real^3->real^3) (at y) o
                    frechet_derivative (sig:real^3->real^3) (at z))) (at z)` ASSUME_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
      MAP_EVERY EXISTS_TAC [`(tau:real^3->real^3) o (sig:real^3->real^3)`; `OC:real^3->bool`] THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
      MAP_EVERY EXPAND_TAC ["tau"; "sig"] THEN REWRITE_TAC[o_THM] THEN
      UNDISCH_TAC `(w:real^3) IN OC` THEN EXPAND_TAC "OC" THEN
      REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
      DISCH_THEN(X_CHOOSE_THEN `x1:A` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^3)) w = x1` SUBST1_TAC THENL
       [ASM_MESON_TAC[MFDM_CHART]; ASM_MESON_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\x:real^3. x`; `\h:real^3. h`;
                   `frechet_derivative (tau:real^3->real^3) (at y) o
                    frechet_derivative (sig:real^3->real^3) (at z)`; `z:real^3`]
                  FRECHET_DERIVATIVE_UNIQUE_AT) THEN
    ASM_REWRITE_TAC[HAS_DERIVATIVE_ID] THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_DROP] THEN
  SUBGOAL_THEN `(\y. (hS:real^3->real^1)((psi':A->real^3)(chart_inv (c:(A->bool)#(A->real^3)) y))) =
                hS o sig` SUBST1_TAC THENL
   [EXPAND_TAC "sig" THEN REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`sig:real^3->real^3`; `hS:real^3->real^1`;
                 `frechet_derivative (sig:real^3->real^3) (at z)`;
                 `\v. lift(p2bkg_pform atlas (g:A->real^3^3) X (psi:real^3->A) y dot v)`;
                 `z:real^3`] DIFF_CHAIN_AT) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC P2BPC_HAS_DERIVATIVE_EQ_DERIV THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `u:real^3` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `S:real^3->bool`; `psi:real^3->A`; `c:(A->bool)#(A->real^3)`;
                 `y:real^3`] P2BKG_PFORM_LOCAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[mfd_param] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(\z. SND (c:(A->bool)#(A->real^3)) ((psi:real^3->A) z)) = tau` SUBST1_TAC THENL
   [EXPAND_TAC "tau" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(tau:real^3->real^3) differentiable at y` ASSUME_TAC THENL
   [ASM_MESON_TAC[differentiable]; ALL_TAC] THEN
  ASM_SIMP_TAC[P2BPC_PULL_DOT] THEN
  SUBGOAL_THEN `(tau:real^3->real^3) y = z` SUBST1_TAC THENL
   [EXPAND_TAC "tau" THEN ASM_REWRITE_TAC[]; REWRITE_TAC[]]);;

(* P2BKG.K6 An oscillation bound on the shell: if the slab pullbacks of w   *)
(* are within e of kappa e_3 on the pieces norm(pr2 z) <= 1 (the closed     *)
(* lower and upper half-shells), then a primitive h of w moves at most 2 (2 *)
(* + log r2 - log r1) e away from kappa log(norm y) + const.                *)

let P2BKG_B1_CONVEX = prove
 (`!a b. convex {z:real^3 | norm(p2bpc_pr2 z) <= &1 /\ a < z$3 /\ z$3 < b}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{z:real^3 | norm(p2bpc_pr2 z) <= &1 /\ a < z$3 /\ z$3 < b} =
                {z | p2bpc_pr2 z IN cball(vec 0,&1)} INTER {z | z$3 > a} INTER {z | z$3 < b}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_CBALL_0; real_gt]; ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC CONVEX_INTER THEN CONJ_TAC) THEN
  SIMP_TAC[CONVEX_LINEAR_PREIMAGE; P2BPC_PR2_LINEAR; CONVEX_CBALL;
           CONVEX_HALFSPACE_COMPONENT_GT; CONVEX_HALFSPACE_COMPONENT_LT]);;

let P2BKG_B1_DIST = prove
 (`!a b z z':real^3.
     norm(p2bpc_pr2 z) <= &1 /\ a < z$3 /\ z$3 < b /\
     norm(p2bpc_pr2 z') <= &1 /\ a < z'$3 /\ z'$3 < b
     ==> norm(z - z') <= &4 + (b - a)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!w:real^3. norm(p2bpc_pr2 w) <= &1 ==> abs(w$1) <= &1 /\ abs(w$2) <= &1`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`p2bpc_pr2 (w:real^3)`; `1`] COMPONENT_LE_NORM) THEN
    MP_TAC(ISPECL [`p2bpc_pr2 (w:real^3)`; `2`] COMPONENT_LE_NORM) THEN
    REWRITE_TAC[DIMINDEX_2; ARITH; P2BPC_PR2_COMPONENTS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:3)) (\i. abs((z - z':real^3)$i))` THEN
  REWRITE_TAC[NORM_LE_L1] THEN
  REWRITE_TAC[DIMINDEX_3; SUM_3; VECTOR_SUB_COMPONENT] THEN
  FIRST_ASSUM(MP_TAC o SPEC `z:real^3`) THEN FIRST_X_ASSUM(MP_TAC o SPEC `z':real^3`) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P2BKG_ANN_N_INV_B1 = prove
 (`!y:real^3. ~(y = vec 0) /\ y$3 <= &0 ==> norm(p2bpc_pr2(p2bpc_ann_n_inv y)) <= &1`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(y:real^3) - y$3` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `norm(y:real^3) pow 2 = y$1 pow 2 + y$2 pow 2 + y$3 pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_POW_2; DOT_3] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[vector_norm] THEN MATCH_MP_TAC REAL_LE_LSQRT THEN REWRITE_TAC[REAL_POS] THEN
  REWRITE_TAC[DOT_2; P2BPC_PR2_COMPONENTS] THEN
  SIMP_TAC[p2bpc_ann_n_inv; LAMBDA_BETA; DIMINDEX_3; ARITH] THEN
  ABBREV_TAC `n = norm(y:real^3)` THEN ABBREV_TAC `d = n - (y:real^3)$3` THEN
  SUBGOAL_THEN `~(d = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(n + (y:real^3)$3) / d` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    UNDISCH_TAC `~(d = &0)` THEN
    UNDISCH_TAC `n pow 2 = (y:real^3)$1 pow 2 + y$2 pow 2 + y$3 pow 2` THEN
    UNDISCH_TAC `n - (y:real^3)$3 = d` THEN CONV_TAC REAL_FIELD;
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC]);;

let P2BKG_ANN_S_INV_B1 = prove
 (`!y:real^3. ~(y = vec 0) /\ &0 <= y$3 ==> norm(p2bpc_pr2(p2bpc_ann_s_inv y)) <= &1`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(y:real^3) + y$3` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `norm(y:real^3) pow 2 = y$1 pow 2 + y$2 pow 2 + y$3 pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_POW_2; DOT_3] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[vector_norm] THEN MATCH_MP_TAC REAL_LE_LSQRT THEN REWRITE_TAC[REAL_POS] THEN
  REWRITE_TAC[DOT_2; P2BPC_PR2_COMPONENTS] THEN
  SIMP_TAC[p2bpc_ann_s_inv; LAMBDA_BETA; DIMINDEX_3; ARITH] THEN
  ABBREV_TAC `n = norm(y:real^3)` THEN ABBREV_TAC `d = n + (y:real^3)$3` THEN
  SUBGOAL_THEN `~(d = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(n - (y:real^3)$3) / d` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    UNDISCH_TAC `~(d = &0)` THEN
    UNDISCH_TAC `n pow 2 = (y:real^3)$1 pow 2 + y$2 pow 2 + y$3 pow 2` THEN
    UNDISCH_TAC `n + (y:real^3)$3 = d` THEN CONV_TAC REAL_FIELD;
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC]);;

let P2BKG_ONORM_LIFT_DOT = prove
 (`!a:real^N. onorm(\v. lift(a dot v)) <= norm a`,
  GEN_TAC THEN
  MP_TAC(ISPEC `\v:real^N. lift(a dot v)` ONORM) THEN REWRITE_TAC[LINEAR_LIFT_DOT] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
  X_GEN_TAC `v:real^N` THEN REWRITE_TAC[NORM_LIFT] THEN
  REWRITE_TAC[REAL_ABS_LE; NORM_CAUCHY_SCHWARZ_ABS]);;

(* The slab primitive gN z = h(ann_n z) - kappa z$3 moves by at most e on   *)
(* the convex piece, per unit distance.                                       *)

let P2BKG_SHELL_PIECE_OSC = prove
 (`!r1 r2 (w:real^3->real^3) (h:real^3->real^1) kappa e (an:real^3->real^3).
     &0 < r1 /\ r1 < r2 /\
     (!y. y IN annulus r1 r2 ==> (h has_derivative (\v. lift(w y dot v))) (at y)) /\
     (!z. norm(an z) = exp(z$3)) /\ smooth_map_on (:real^3) an /\
     (!z. norm(p2bpc_pr2 z) <= &1 /\ log r1 < z$3 /\ z$3 < log r2
          ==> norm(p2bpc_pull an w z - kappa % basis 3) <= e)
     ==> !z z'. norm(p2bpc_pr2 z) <= &1 /\ log r1 < z$3 /\ z$3 < log r2 /\
                norm(p2bpc_pr2 z') <= &1 /\ log r1 < z'$3 /\ z'$3 < log r2
                ==> abs((drop(h(an z)) - kappa * z$3) - (drop(h(an z')) - kappa * z'$3))
                    <= e * (&4 + (log r2 - log r1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `B = {z:real^3 | norm(p2bpc_pr2 z) <= &1 /\ log r1 < z$3 /\ z$3 < log r2}` THEN
  SUBGOAL_THEN `!z:real^3. z IN B ==> (an:real^3->real^3) z IN annulus r1 r2` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "B" THEN REWRITE_TAC[IN_ELIM_THM; annulus] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`log r1`; `(z:real^3)$3`] REAL_EXP_MONO_LT) THEN
    MP_TAC(SPECL [`(z:real^3)$3`; `log r2`] REAL_EXP_MONO_LT) THEN
    SUBGOAL_THEN `&0 < r2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[EXP_LOG];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^3. z IN B
               ==> ((\z. lift(drop((h:real^3->real^1)((an:real^3->real^3) z)) - kappa * z$3))
                    has_derivative
                    (\v. lift((p2bpc_pull an (w:real^3->real^3) z - kappa % basis 3) dot v)))
                   (at z within B)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
    SUBGOAL_THEN `(an:real^3->real^3) differentiable at z` ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^3)` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      ALL_TAC] THEN
    SUBGOAL_THEN `(\z. lift(drop((h:real^3->real^1)((an:real^3->real^3) z)) - kappa * z$3)) =
                  (\z. (h o an) z - kappa % lift(z$3))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_SUB; LIFT_CMUL; LIFT_DROP]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\v. lift((p2bpc_pull an (w:real^3->real^3) z - kappa % basis 3) dot v)) =
      (\v. (\v. lift(w(an z) dot v)) (frechet_derivative (an:real^3->real^3) (at z) v) -
           kappa % lift(v$3))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `v:real^3` THEN
      ASM_SIMP_TAC[DOT_LSUB; DOT_LMUL; P2BPC_PULL_DOT; DOT_BASIS; DIMINDEX_3; ARITH;
                   LIFT_SUB; LIFT_CMUL];
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN CONJ_TAC THENL
     [REWRITE_TAC[o_DEF] THEN
      MP_TAC(ISPECL [`an:real^3->real^3`; `h:real^3->real^1`;
                     `frechet_derivative (an:real^3->real^3) (at z)`;
                     `\v. lift((w:real^3->real^3)((an:real^3->real^3) z) dot v)`; `z:real^3`]
                    DIFF_CHAIN_AT) THEN
      REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
      MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN REWRITE_TAC[HAS_DERIVATIVE_LIFT_COMPONENT]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z. lift(drop((h:real^3->real^1)((an:real^3->real^3) z)) - kappa * z$3)`;
                 `\z v. lift((p2bpc_pull an (w:real^3->real^3) z - kappa % basis 3) dot v)`;
                 `B:real^3->bool`; `e:real`] DIFFERENTIABLE_BOUND) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "B" THEN REWRITE_TAC[P2BKG_B1_CONVEX];
      ASM_REWRITE_TAC[];
      X_GEN_TAC `z:real^3` THEN EXPAND_TAC "B" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm(p2bpc_pull an (w:real^3->real^3) z - kappa % basis 3)` THEN
      REWRITE_TAC[P2BKG_ONORM_LIFT_DOT] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`z:real^3`; `z':real^3`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`z:real^3`; `z':real^3`]) THEN
  EXPAND_TAC "B" THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT] THEN
  MP_TAC(ISPECL [`log r1`; `log r2`; `z:real^3`; `z':real^3`] P2BKG_B1_DIST) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= e` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(p2bpc_pull an (w:real^3->real^3) z - kappa % basis 3)` THEN
    ASM_SIMP_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  REPEAT DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `e * norm(z - z':real^3)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]);;

let P2BKG_SHELL_OSC = prove
 (`!r1 r2 (w:real^3->real^3) (h:real^3->real^1) kappa e.
     &0 < r1 /\ r1 < r2 /\
     (!y. y IN annulus r1 r2 ==> (h has_derivative (\v. lift(w y dot v))) (at y)) /\
     (!z. norm(p2bpc_pr2 z) <= &1 /\ log r1 < z$3 /\ z$3 < log r2
          ==> norm(p2bpc_pull p2bpc_ann_n w z - kappa % basis 3) <= e /\
              norm(p2bpc_pull p2bpc_ann_s w z - kappa % basis 3) <= e)
     ==> !y y'. y IN annulus r1 r2 /\ y' IN annulus r1 r2
                ==> abs((drop(h y) - kappa * log(norm y)) -
                        (drop(h y') - kappa * log(norm y')))
                    <= &2 * e * (&4 + (log r2 - log r1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`r1:real`; `r2:real`; `w:real^3->real^3`; `h:real^3->real^1`; `kappa:real`;
                 `e:real`; `p2bpc_ann_n`] P2BKG_SHELL_PIECE_OSC) THEN
  ASM_SIMP_TAC[P2BPC_ANN_N_NORM; P2BPC_ANN_N_SMOOTH; OPEN_UNIV] THEN DISCH_THEN(LABEL_TAC "pn") THEN
  MP_TAC(ISPECL [`r1:real`; `r2:real`; `w:real^3->real^3`; `h:real^3->real^1`; `kappa:real`;
                 `e:real`; `p2bpc_ann_s`] P2BKG_SHELL_PIECE_OSC) THEN
  ASM_SIMP_TAC[P2BPC_ANN_S_NORM; P2BPC_ANN_S_SMOOTH; OPEN_UNIV] THEN DISCH_THEN(LABEL_TAC "ps") THEN
  SUBGOAL_THEN `&0 < r2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^3. y IN annulus r1 r2
               ==> ~(y = vec 0) /\ log r1 < log(norm y) /\ log(norm y) < log r2`
  (LABEL_TAC "ann") THENL
   [GEN_TAC THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[LOG_MONO_LT; GSYM NORM_POS_LT];
    ALL_TAC] THEN
  ABBREV_TAC `G = \y:real^3. drop((h:real^3->real^1) y) - kappa * log(norm y)` THEN
  SUBGOAL_THEN
   `!y:real^3. y IN annulus r1 r2 /\ y$3 <= &0
               ==> (norm(p2bpc_pr2(p2bpc_ann_n_inv y)) <= &1 /\
                    log r1 < p2bpc_ann_n_inv y$3 /\ p2bpc_ann_n_inv y$3 < log r2) /\
                   drop(h(p2bpc_ann_n(p2bpc_ann_n_inv y))) - kappa * p2bpc_ann_n_inv y$3 = G y`
  (LABEL_TAC "fn") THENL
   [GEN_TAC THEN STRIP_TAC THEN USE_THEN "ann" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `p2bpc_ann_n_inv (y:real^3)$3 = log(norm y)` SUBST1_TAC THENL
     [SIMP_TAC[p2bpc_ann_n_inv; LAMBDA_BETA; DIMINDEX_3; ARITH]; ALL_TAC] THEN
    ASM_SIMP_TAC[P2BKG_ANN_N_INV_B1] THEN
    SUBGOAL_THEN `~(norm(y:real^3) = y$3)` ASSUME_TAC THENL
     [UNDISCH_TAC `~(y:real^3 = vec 0)` THEN REWRITE_TAC[GSYM NORM_POS_LT] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[P2BPC_ANN_N_RIGHT] THEN EXPAND_TAC "G" THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^3. y IN annulus r1 r2 /\ &0 <= y$3
               ==> (norm(p2bpc_pr2(p2bpc_ann_s_inv y)) <= &1 /\
                    log r1 < p2bpc_ann_s_inv y$3 /\ p2bpc_ann_s_inv y$3 < log r2) /\
                   drop(h(p2bpc_ann_s(p2bpc_ann_s_inv y))) - kappa * p2bpc_ann_s_inv y$3 = G y`
  (LABEL_TAC "fs") THENL
   [GEN_TAC THEN STRIP_TAC THEN USE_THEN "ann" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `p2bpc_ann_s_inv (y:real^3)$3 = log(norm y)` SUBST1_TAC THENL
     [SIMP_TAC[p2bpc_ann_s_inv; LAMBDA_BETA; DIMINDEX_3; ARITH]; ALL_TAC] THEN
    ASM_SIMP_TAC[P2BKG_ANN_S_INV_B1] THEN
    SUBGOAL_THEN `~(norm(y:real^3) = --(y$3))` ASSUME_TAC THENL
     [UNDISCH_TAC `~(y:real^3 = vec 0)` THEN REWRITE_TAC[GSYM NORM_POS_LT] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[P2BPC_ANN_S_RIGHT] THEN EXPAND_TAC "G" THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `ye = ((r1 + r2) / &2) % basis 1:real^3` THEN
  SUBGOAL_THEN `(ye:real^3) IN annulus r1 r2 /\ ye$3 = &0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ye" THEN
    SIMP_TAC[annulus; IN_ELIM_THM; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH;
             VECTOR_MUL_COMPONENT; BASIS_COMPONENT] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN annulus r1 r2
                           ==> abs((G:real^3->real) y - G ye) <= e * (&4 + (log r2 - log r1))`
  (LABEL_TAC "toe") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(y:real^3)$3 <= &0` THENL
     [USE_THEN "fn" (MP_TAC o SPEC `y:real^3`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
      USE_THEN "fn" (MP_TAC o SPEC `ye:real^3`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
      USE_THEN "pn" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `&0 <= (y:real^3)$3` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "fs" (MP_TAC o SPEC `y:real^3`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
      USE_THEN "fs" (MP_TAC o SPEC `ye:real^3`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
      USE_THEN "ps" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y:real^3`; `y':real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `drop((h:real^3->real^1) y) - kappa * log(norm y) = (G:real^3->real) y /\
                drop(h y') - kappa * log(norm y') = G y'` (CONJUNCTS_THEN SUBST1_TAC) THENL
   [EXPAND_TAC "G" THEN REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "toe" (MP_TAC o SPEC `y:real^3`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "toe" (MP_TAC o SPEC `y':real^3`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* P2BKG.K7 The level set of an almost-height function on the shell is       *)
(* compact: if abs(f y - kappa log(norm y)) <= delta with delta < kappa a    *)
(* on annulus(exp(-a), exp a), the zero set of f lies in the closed          *)
(* sub-shell exp(-delta/kappa) <= norm y <= exp(delta/kappa).                *)

let P2BKG_LEVEL_SUBSHELL = prove
 (`!a kappa delta (f:real^3->real^1) y.
     &0 < kappa /\ y IN annulus (exp(--a)) (exp a) /\
     abs(drop(f y) - kappa * log(norm y)) <= delta /\ f y = vec 0
     ==> exp(--(delta / kappa)) <= norm y /\ norm y <= exp(delta / kappa)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [MP_TAC(SPEC `--a` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `abs(drop((f:real^3->real^1) y) - kappa * log(norm y)) <= delta` THEN
  ASM_REWRITE_TAC[DROP_VEC; REAL_SUB_LZERO; REAL_ABS_NEG; REAL_ABS_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < k ==> abs k = k`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs(log(norm(y:real^3))) <= delta / kappa` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM(MATCH_MP EXP_LOG (ASSUME `&0 < norm(y:real^3)`))] THEN
  REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC);;

let P2BKG_LEVEL_SET_COMPACT = prove
 (`!a kappa delta (f:real^3->real^1).
     &0 < kappa /\ delta < kappa * a /\
     f continuous_on annulus (exp(--a)) (exp a) /\
     (!y. y IN annulus (exp(--a)) (exp a)
          ==> abs(drop(f y) - kappa * log(norm y)) <= delta)
     ==> compact {y | y IN annulus (exp(--a)) (exp a) /\ f y = vec 0}`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `{y:real^3 | y IN annulus (exp(--a)) (exp a) /\ (f:real^3->real^1) y = vec 0} = {}` THEN
  ASM_REWRITE_TAC[COMPACT_EMPTY] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN(X_CHOOSE_THEN `y0:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 <= delta` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs(drop((f:real^3->real^1) y0) - kappa * log(norm(y0:real^3)))` THEN
    ASM_SIMP_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  ABBREV_TAC `K0 = cball(vec 0:real^3,exp(delta / kappa)) DIFF ball(vec 0,exp(--(delta / kappa)))` THEN
  SUBGOAL_THEN `(K0:real^3->bool) SUBSET annulus (exp(--a)) (exp a)` ASSUME_TAC THENL
   [EXPAND_TAC "K0" THEN
    REWRITE_TAC[SUBSET; annulus; IN_DIFF; IN_CBALL_0; IN_BALL_0; IN_ELIM_THM; REAL_NOT_LT] THEN
    SUBGOAL_THEN `delta / kappa < a` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_EXP_MONO_LT] THEN GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `exp(--(delta / kappa))` THEN
      ASM_REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `exp(delta / kappa)` THEN
      ASM_REWRITE_TAC[REAL_EXP_MONO_LT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `{y:real^3 | y IN annulus (exp(--a)) (exp a) /\ f y = vec 0} =
                {y | y IN K0 /\ (f:real^3->real^1) y = vec 0}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "K0" THEN
      REWRITE_TAC[IN_DIFF; IN_CBALL_0; IN_BALL_0; REAL_NOT_LT] THEN
      MATCH_MP_TAC(TAUT `(a /\ b) ==> (b /\ a)`) THEN
      MATCH_MP_TAC P2BKG_LEVEL_SUBSHELL THEN
      MAP_EVERY EXISTS_TAC [`a:real`; `f:real^3->real^1`] THEN ASM_SIMP_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC CLOSED_IN_COMPACT THEN EXISTS_TAC `K0:real^3->bool` THEN CONJ_TAC THENL
   [EXPAND_TAC "K0" THEN SIMP_TAC[COMPACT_DIFF; COMPACT_CBALL; OPEN_BALL];
    MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE_CONSTANT THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]]);;

(* P2BKG.K8 Regularity of the level sets of the shell primitive: a smooth h *)
(* on V whose chart derivatives are the chart forms of omega = g(X,.) (the  *)
(* output of P2BKG_SHELL_PRIMITIVE) has every level set regular in the      *)
(* sense of pc_mfd_level when X is a unit field, since dh(X) = g(X,X) = 1   *)
(* in the preferred chart.                                                  *)

let P2BKG_LEVEL_REGULAR = prove
 (`!top atlas (g:A->real^3^3) X V (h:A->real) u.
     smooth_manifold_atlas top atlas /\ V SUBSET topspace top /\
     mfd_smooth_on atlas V (\x. lift(h x)) /\
     (!c z. c IN atlas /\ z IN IMAGE (SND c) (FST c INTER V)
            ==> ((\y. lift(h(chart_inv c y))) has_derivative
                 (\v. lift(p2bkg_cform atlas g X c z dot v))) (at z)) /\
     (!x. x IN V ==> X x dot (g x ** X x) = &1)
     ==> lvs_regular atlas V h u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[lvs_regular; lvs_set; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `((\y. lift((h:A->real)(chart_inv (chart_at atlas x) y))) has_derivative
     (\v. lift(p2bkg_cform atlas (g:A->real^3^3) (X:A->real^3) (chart_at atlas x)
                           (SND(chart_at atlas x) x) dot v)))
    (at (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) x) x))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[FUN_EQ_THM; NOT_FORALL_THM] THEN EXISTS_TAC `(X:A->real^3) x` THEN
  REWRITE_TAC[p2bkg_cform] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `x:A`] METRIC_LOCAL_AT) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `X:A->real^3`; `x:A`] P2BX0_VREP_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `((g:A->real^3^3) x ** (X:A->real^3) x) dot X x = &1` SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN REAL_ARITH_TAC);;

(* The shell primitive with regular level sets (combination of             *)
(* P2BKG_SHELL_PRIMITIVE and P2BKG_LEVEL_REGULAR).                          *)

let P2BKG_SHELL_PRIMITIVE_REGULAR = prove
 (`!top atlas (g:A->real^3^3) X W r1 r2 (psi:real^3->A).
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ open_in top W /\
     p2b_parallel_on atlas g W X /\ &0 < r1 /\ r1 < r2 /\
     mfd_param top atlas (annulus r1 r2) psi /\ IMAGE psi (annulus r1 r2) SUBSET W /\
     (!x. x IN W ==> X x dot (g x ** X x) = &1)
     ==> ?h:A->real.
            mfd_smooth_on atlas (IMAGE psi (annulus r1 r2)) (\x. lift(h x)) /\
            (!c z. c IN atlas /\ z IN IMAGE (SND c) (FST c INTER IMAGE psi (annulus r1 r2))
                   ==> ((\y. lift(h(chart_inv c y))) has_derivative
                        (\u. lift(p2bkg_cform atlas g X c z dot u))) (at z)) /\
            (!u. lvs_regular atlas (IMAGE psi (annulus r1 r2)) h u)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `W:A->bool`; `r1:real`; `r2:real`; `psi:real^3->A`]
                P2BKG_SHELL_PRIMITIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `h:A->real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `h:A->real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `u:real` THEN
  MATCH_MP_TAC P2BKG_LEVEL_REGULAR THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `g:A->real^3^3`; `X:A->real^3`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `W:A->bool`] OPEN_IN_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ASM SET_TAC[]]);;

(* P2BKG.K9 The compact leaf on the shell (glue): if psi is an mfd_param of *)
(* the shell annulus(exp(-a), exp a) and h is smooth on its image with      *)
(* abs((h o psi - c0) - kappa log(norm y)) <= delta < kappa a, then         *)
(* the level set of h at c0 in psi(shell) is the psi-image of a compact     *)
(* subset of the shell, hence compact in top.                               *)

let P2BKG_LEAF_COMPACT = prove
 (`!top atlas (psi:real^3->A) (h:A->real) a kappa delta c0.
     smooth_manifold_atlas top atlas /\
     mfd_param top atlas (annulus (exp(--a)) (exp a)) psi /\
     mfd_smooth_on atlas (IMAGE psi (annulus (exp(--a)) (exp a))) (\x. lift(h x)) /\
     &0 < kappa /\ delta < kappa * a /\
     (!y. y IN annulus (exp(--a)) (exp a)
          ==> abs((h(psi y) - c0) - kappa * log(norm y)) <= delta)
     ==> lvs_set (IMAGE psi (annulus (exp(--a)) (exp a))) h c0 =
         IMAGE psi {y | y IN annulus (exp(--a)) (exp a) /\ h(psi y) = c0} /\
         compact {y | y IN annulus (exp(--a)) (exp a) /\ h(psi y) = c0} /\
         compact_in top (lvs_set (IMAGE psi (annulus (exp(--a)) (exp a))) h c0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `S = annulus (exp(--a)) (exp a):real^3->bool` THEN
  UNDISCH_TAC `mfd_param top (atlas:((A->bool)#(A->real^3))->bool) S psi` THEN
  REWRITE_TAC[mfd_param] THEN DISCH_THEN(X_CHOOSE_TAC `e':A->real^3`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `S:real^3->bool`; `psi:real^3->A`; `e':A->real^3`] LVS_DIFFEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\y. lift((h:A->real)((psi:real^3->A) y))) continuous_on S` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN
    SUBGOAL_THEN `(\y. lift((h:A->real)((psi:real^3->A) y))) = (\x. lift(h x)) o psi`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC LVS_PARAM_SMOOTH_COMPOSE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `IMAGE (psi:real^3->A) S`; `e':A->real^3`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `{y | y IN S /\ (h:A->real)((psi:real^3->A) y) = c0} =
                {y | y IN S /\ (\y. lift(h(psi y) - c0)) y = vec 0}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; GSYM LIFT_NUM; LIFT_EQ; REAL_SUB_0]; ALL_TAC] THEN
  SUBGOAL_THEN `compact {y | y IN S /\ (\y. lift((h:A->real)((psi:real^3->A) y) - c0)) y = vec 0}`
  ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC P2BKG_LEVEL_SET_COMPACT THEN
    MAP_EVERY EXISTS_TAC [`kappa:real`; `delta:real`] THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
    REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lvs_set (IMAGE (psi:real^3->A) S) h c0 =
                IMAGE psi {y | y IN S /\ (\y. lift((h:A->real)(psi y) - c0)) y = vec 0}`
  ASSUME_TAC THENL
   [REWRITE_TAC[lvs_set; EXTENSION; IN_ELIM_THM; IN_IMAGE; GSYM LIFT_NUM; LIFT_EQ;
                REAL_SUB_0] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_COMPACT_IN THEN
  EXISTS_TAC `subtopology euclidean (S:real^3->bool)` THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC BETA_RULE THEN
  ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN] THEN SET_TAC[]);;

(* P2BKG.K10 Primitives of omega = g(X,.) read through smooth maps of real^3 *)
(* (flow boxes): the vocabulary p2bkg_prim (h smooth on V with the chart     *)
(* forms of omega as chart derivatives), the derivative of h o Fm for a      *)
(* smooth map Fm (FB2: a |-> dFm(z) a . g X), and the z3-invariance of that  *)
(* form for the flow charts of pc_p2b_kfl (FB3).                             *)

let p2bkg_prim = new_definition
 `p2bkg_prim (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) (X:A->real^3)
             (V:A->bool) (h:A->real) <=>
    mfd_smooth_on atlas V (\x. lift(h x)) /\
    !c z. c IN atlas /\ z IN IMAGE (SND c) (FST c INTER V)
          ==> ((\y. lift(h(chart_inv c y))) has_derivative
               (\u. lift(p2bkg_cform atlas g X c z dot u))) (at z)`;;

let P2BKG_PRIM_MAP_DERIV = prove
 (`!top atlas (g:A->real^3^3) (X:A->real^3) V h (Fm:real^3->A) z.
     smooth_manifold_atlas top atlas /\ continuous_map (euclidean,top) Fm /\
     mfd_smooth_map (open_set_atlas (:real^3)) atlas (:real^3) Fm /\
     open_in top V /\ p2bkg_prim atlas g X V h /\ Fm z IN V
     ==> ((\y. lift(h(Fm y))) has_derivative
          (\a. lift(mfd_differential (open_set_atlas (:real^3)) atlas Fm z a dot
                    (g(Fm z) ** X(Fm z))))) (at z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bkg_prim] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(Fm:real^3->A) z IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `Fm:real^3->A`;
                 `z:real^3`] P2BKF_SMOOTH_DIFFABLE) THEN
  ASM_REWRITE_TAC[FRECHET_DERIVATIVE_WORKS] THEN
  REWRITE_TAC[GSYM MFD_DIFFERENTIAL_OPEN_SET_ATLAS] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(Fm:real^3->A) z`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^3))->bool) ((Fm:real^3->A) z)`]
                MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `p2bkg_cform atlas (g:A->real^3^3) (X:A->real^3) (chart_at atlas ((Fm:real^3->A) z))
                (SND(chart_at atlas (Fm z)) (Fm z)) = g(Fm z) ** X(Fm z)`
  ASSUME_TAC THENL
   [REWRITE_TAC[p2bkg_cform] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `g:A->real^3^3`; `(Fm:real^3->A) z`] METRIC_LOCAL_AT) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `X:A->real^3`; `(Fm:real^3->A) z`] P2BX0_VREP_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
    REFL_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) ((Fm:real^3->A) z)` THEN
  ABBREV_TAC `D = mfd_differential (open_set_atlas (:real^3))
                    (atlas:((A->bool)#(A->real^3))->bool) (Fm:real^3->A) z` THEN
  SUBGOAL_THEN
   `((\y. lift((h:A->real)(chart_inv c y))) has_derivative
     (\u. lift(p2bkg_cform atlas (g:A->real^3^3) (X:A->real^3) c
                           (SND c ((Fm:real^3->A) z)) dot u)))
    (at (SND (c:(A->bool)#(A->real^3)) (Fm z)))`
  MP_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    EXISTS_TAC `(Fm:real^3->A) z` THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  SUBGOAL_THEN
   `(((\y. lift((h:A->real)(chart_inv c y))) o
      (\y. SND (c:(A->bool)#(A->real^3)) ((Fm:real^3->A) y))) has_derivative
     ((\u. lift(((g:A->real^3^3)(Fm z) ** (X:A->real^3)(Fm z)) dot u)) o D)) (at z)`
  MP_TAC THENL
   [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\u. lift(((g:A->real^3^3)((Fm:real^3->A) z) ** (X:A->real^3)(Fm z)) dot u)) o
    (D:real^3->real^3) =
    (\a. lift(D a dot (g(Fm z) ** X(Fm z))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN
    MATCH_ACCEPT_TAC DOT_SYM;
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
  EXISTS_TAC `(\y. lift((h:A->real)(chart_inv c y))) o
              (\y. SND (c:(A->bool)#(A->real^3)) ((Fm:real^3->A) y))` THEN
  EXISTS_TAC `{y:real^3 | (Fm:real^3->A) y IN FST(c:(A->bool)#(A->real^3))}` THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; o_THM] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`Fm:real^3->A`; `euclidean:(real^3)topology`; `top:A topology`;
                   `FST(c:(A->bool)#(A->real^3))`] OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV; GSYM OPEN_IN];
    ASM_SIMP_TAC[]]);;

let P2BKG_FMAP_FORM_SHIFT = prove
 (`!top atlas (g:A->real^3^3) (X:A->real^3) x0 u1 u2 z t a.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) X /\
     x0 IN topspace top
     ==> mfd_differential (open_set_atlas (:real^3)) atlas
           (p2bkf_fmap (top,atlas) g X x0 u1 u2) (z + t % basis 3) a dot
         (g(p2bkf_fmap (top,atlas) g X x0 u1 u2 (z + t % basis 3)) **
          X(p2bkf_fmap (top,atlas) g X x0 u1 u2 (z + t % basis 3))) =
         mfd_differential (open_set_atlas (:real^3)) atlas
           (p2bkf_fmap (top,atlas) g X x0 u1 u2) z a dot
         (g(p2bkf_fmap (top,atlas) g X x0 u1 u2 z) **
          X(p2bkf_fmap (top,atlas) g X x0 u1 u2 z))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `g:A->real^3^3`; `X:A->real^3`; `x0:A`; `u1:real^3`; `u2:real^3`;
                 `z:real^3`; `t:real`; `a:real^3`; `basis 3:real^3`]
                P2BKF_FMAP_METRIC_INV2) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `x0:A`; `u1:real^3`; `u2:real^3`; `z + t % basis 3:real^3`]
                P2BKF_FMAP_D3) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `x0:A`; `u1:real^3`; `u2:real^3`; `z:real^3`]
                P2BKF_FMAP_D3) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  DISCH_THEN ACCEPT_TAC);;

(* P2BKG.K11 Primitives in flow boxes: h o fmap(. + s e3) has the           *)
(* s-independent derivative a |-> dfmap(z) a . g X (FB2 + FB3), so two      *)
(* such compositions differ by a constant on a convex set (FB4); h grows at *)
(* unit rate along vertical segments that stay in V (P1), hence along the   *)
(* orbits Phi_t y = fmap_y(t e3).                                           *)

let P2BKG_FMAP_SHIFT_DERIV = prove
 (`!top atlas (g:A->real^3^3) (X:A->real^3) V h x0 u1 u2 s z.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) X /\
     x0 IN topspace top /\ open_in top V /\ p2bkg_prim atlas g X V h /\
     p2bkf_fmap (top,atlas) g X x0 u1 u2 (z + s % basis 3) IN V
     ==> ((\y. lift(h(p2bkf_fmap (top,atlas) g X x0 u1 u2 (y + s % basis 3)))) has_derivative
          (\a. lift(mfd_differential (open_set_atlas (:real^3)) atlas
                      (p2bkf_fmap (top,atlas) g X x0 u1 u2) z a dot
                    (g(p2bkf_fmap (top,atlas) g X x0 u1 u2 z) **
                     X(p2bkf_fmap (top,atlas) g X x0 u1 u2 z))))) (at z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!a. mfd_differential (open_set_atlas (:real^3)) atlas
          (p2bkf_fmap (top,atlas) (g:A->real^3^3) (X:A->real^3) x0 u1 u2) (z + s % basis 3) a dot
        (g(p2bkf_fmap (top,atlas) g X x0 u1 u2 (z + s % basis 3)) **
         X(p2bkf_fmap (top,atlas) g X x0 u1 u2 (z + s % basis 3))) =
        mfd_differential (open_set_atlas (:real^3)) atlas
          (p2bkf_fmap (top,atlas) g X x0 u1 u2) z a dot
        (g(p2bkf_fmap (top,atlas) g X x0 u1 u2 z) ** X(p2bkf_fmap (top,atlas) g X x0 u1 u2 z))`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC P2BKG_FMAP_FORM_SHIFT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `x0:A`; `u1:real^3`; `u2:real^3`] P2BKF_FMAP_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `V:A->bool`; `h:A->real`;
                 `p2bkf_fmap (top,atlas) (g:A->real^3^3) (X:A->real^3) x0 u1 u2`;
                 `z + s % basis 3:real^3`] P2BKG_PRIM_MAP_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `((\y:real^3. y + s % basis 3) has_derivative (\a. a)) (at z)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\y:real^3. y`; `\a:real^3. a`; `\y:real^3. s % basis 3:real^3`;
                   `\a:real^3. vec 0:real^3`; `at (z:real^3)`] HAS_DERIVATIVE_ADD) THEN
    REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST; VECTOR_ADD_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(((\w. lift((h:A->real)(p2bkf_fmap (top,atlas) (g:A->real^3^3) (X:A->real^3) x0 u1 u2 w))) o
      (\y:real^3. y + s % basis 3)) has_derivative
     ((\a. lift(mfd_differential (open_set_atlas (:real^3)) atlas
                  (p2bkf_fmap (top,atlas) g X x0 u1 u2) z a dot
                (g(p2bkf_fmap (top,atlas) g X x0 u1 u2 z) **
                 X(p2bkf_fmap (top,atlas) g X x0 u1 u2 z)))) o (\a. a))) (at z)`
  MP_TAC THENL
   [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[o_DEF]]);;

let P2BKG_FMAP_PRIM_CONST = prove
 (`!top atlas (g:A->real^3^3) (X:A->real^3) V1 h1 V2 h2 x0 u1 u2 s1 s2 B.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) X /\
     x0 IN topspace top /\ open_in top V1 /\ p2bkg_prim atlas g X V1 h1 /\
     open_in top V2 /\ p2bkg_prim atlas g X V2 h2 /\ convex B /\
     (!z. z IN B ==> p2bkf_fmap (top,atlas) g X x0 u1 u2 (z + s1 % basis 3) IN V1 /\
                     p2bkf_fmap (top,atlas) g X x0 u1 u2 (z + s2 % basis 3) IN V2)
     ==> ?k. !z. z IN B
                 ==> h1(p2bkf_fmap (top,atlas) g X x0 u1 u2 (z + s1 % basis 3)) =
                     h2(p2bkf_fmap (top,atlas) g X x0 u1 u2 (z + s2 % basis 3)) + k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\z. lift((h1:A->real)(p2bkf_fmap (top,atlas) (g:A->real^3^3) (X:A->real^3) x0 u1 u2
                            (z + s1 % basis 3))) -
         lift((h2:A->real)(p2bkf_fmap (top,atlas) g X x0 u1 u2 (z + s2 % basis 3)))`;
    `B:real^3->bool`] HAS_DERIVATIVE_ZERO_CONSTANT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
    SUBGOAL_THEN
     `(\h:real^3. vec 0:real^1) =
      (\a. lift(mfd_differential (open_set_atlas (:real^3)) atlas
                  (p2bkf_fmap (top,atlas) (g:A->real^3^3) (X:A->real^3) x0 u1 u2) z a dot
                (g(p2bkf_fmap (top,atlas) g X x0 u1 u2 z) **
                 X(p2bkf_fmap (top,atlas) g X x0 u1 u2 z))) -
           lift(mfd_differential (open_set_atlas (:real^3)) atlas
                  (p2bkf_fmap (top,atlas) g X x0 u1 u2) z a dot
                (g(p2bkf_fmap (top,atlas) g X x0 u1 u2 z) **
                 X(p2bkf_fmap (top,atlas) g X x0 u1 u2 z))))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; VECTOR_SUB_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN CONJ_TAC THEN
    MATCH_MP_TAC P2BKG_FMAP_SHIFT_DERIV THENL
     [EXISTS_TAC `V1:A->bool`; EXISTS_TAC `V2:A->bool`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `c:real^1`) THEN EXISTS_TAC `drop c` THEN
  X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM `drop`) THEN REWRITE_TAC[DROP_SUB; LIFT_DROP] THEN
  REAL_ARITH_TAC);;

let P2BKG_FMAP_PRIM_VERTICAL = prove
 (`!top atlas (g:A->real^3^3) (X:A->real^3) V h x0 u1 u2 z s.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) X /\
     (!x. x IN topspace top ==> X x dot (g x ** X x) = &1) /\
     x0 IN topspace top /\ open_in top V /\ p2bkg_prim atlas g X V h /\ &0 <= s /\
     (!t. &0 <= t /\ t <= s ==> p2bkf_fmap (top,atlas) g X x0 u1 u2 (z + t % basis 3) IN V)
     ==> h(p2bkf_fmap (top,atlas) g X x0 u1 u2 (z + s % basis 3)) =
         h(p2bkf_fmap (top,atlas) g X x0 u1 u2 z) + s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `x0:A`; `u1:real^3`; `u2:real^3`] P2BKF_FMAP_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\x:real^1. lift((h:A->real)(p2bkf_fmap (top,atlas) (g:A->real^3^3) (X:A->real^3) x0 u1 u2
                                  (z + drop x % basis 3))) - x`;
    `interval[lift(&0),lift s]`] HAS_DERIVATIVE_ZERO_CONSTANT) THEN
  REWRITE_TAC[CONVEX_INTERVAL] THEN ANTS_TAC THENL
   [X_GEN_TAC `x:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
    ABBREV_TAC `w = z + drop x % basis 3:real^3` THEN
    SUBGOAL_THEN `p2bkf_fmap (top,atlas) (g:A->real^3^3) (X:A->real^3) x0 u1 u2 w IN V`
    ASSUME_TAC THENL [EXPAND_TAC "w" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `X:A->real^3`; `V:A->bool`; `h:A->real`;
                   `p2bkf_fmap (top,atlas) (g:A->real^3^3) (X:A->real^3) x0 u1 u2`;
                   `w:real^3`] P2BKG_PRIM_MAP_DERIV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `((\x:real^1. z + drop x % basis 3:real^3) has_derivative
                   (\y. drop y % basis 3)) (at x)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`\x:real^1. z:real^3`; `\y:real^1. vec 0:real^3`;
                     `\x:real^1. drop x % basis 3:real^3`; `\y:real^1. drop y % basis 3:real^3`;
                     `at (x:real^1)`] HAS_DERIVATIVE_ADD) THEN
      REWRITE_TAC[HAS_DERIVATIVE_CONST; VECTOR_ADD_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC HAS_DERIVATIVE_VMUL_DROP THEN REWRITE_TAC[HAS_DERIVATIVE_ID];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(((\v. lift((h:A->real)(p2bkf_fmap (top,atlas) (g:A->real^3^3) (X:A->real^3) x0 u1 u2 v))) o
        (\x:real^1. z + drop x % basis 3)) has_derivative
       ((\a. lift(mfd_differential (open_set_atlas (:real^3)) atlas
                    (p2bkf_fmap (top,atlas) g X x0 u1 u2) w a dot
                  (g(p2bkf_fmap (top,atlas) g X x0 u1 u2 w) **
                   X(p2bkf_fmap (top,atlas) g X x0 u1 u2 w)))) o
        (\y. drop y % basis 3))) (at x)`
    MP_TAC THENL
     [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\a. lift(mfd_differential (open_set_atlas (:real^3)) atlas
                  (p2bkf_fmap (top,atlas) (g:A->real^3^3) (X:A->real^3) x0 u1 u2) w a dot
                (g(p2bkf_fmap (top,atlas) g X x0 u1 u2 w) **
                 X(p2bkf_fmap (top,atlas) g X x0 u1 u2 w)))) o
      (\y:real^1. drop y % basis 3) = (\y. y)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `y:real^1` THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `p2bkf_fmap (top,atlas) (g:A->real^3^3) (X:A->real^3) x0 u1 u2`;
                     `w:real^3`] P2BKF_SMOOTH_DIFFABLE) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
      REWRITE_TAC[GSYM MFD_DIFFERENTIAL_OPEN_SET_ATLAS; ETA_AX] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `X:A->real^3`; `x0:A`; `u1:real^3`; `u2:real^3`; `w:real^3`]
                    P2BKF_FMAP_D3) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DOT_LMUL] THEN
      SUBGOAL_THEN
       `(X:A->real^3)(p2bkf_fmap (top,atlas) (g:A->real^3^3) X x0 u1 u2 w) dot
        (g(p2bkf_fmap (top,atlas) g X x0 u1 u2 w) ** X(p2bkf_fmap (top,atlas) g X x0 u1 u2 w)) =
        &1`
      SUBST1_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
        REWRITE_TAC[REAL_MUL_RID; LIFT_DROP]];
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(\h:real^1. vec 0:real^1) = (\y. y - y)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; VECTOR_SUB_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN REWRITE_TAC[HAS_DERIVATIVE_ID] THEN
    UNDISCH_TAC
     `(((\v. lift((h:A->real)(p2bkf_fmap (top,atlas) (g:A->real^3^3) (X:A->real^3) x0 u1 u2 v))) o
        (\x:real^1. z + drop x % basis 3)) has_derivative (\y. y)) (at x)` THEN
    REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `c:real^1`) THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `lift s` th) THEN MP_TAC(SPEC `lift(&0)` th)) THEN
  ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; REAL_LE_REFL] THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `lift((h:A->real)(p2bkf_fmap (top,atlas) (g:A->real^3^3) (X:A->real^3) x0 u1 u2
                       (z + s % basis 3))) - lift s =
    lift(h(p2bkf_fmap (top,atlas) g X x0 u1 u2 z)) - lift(&0)`
  MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM LIFT_SUB; LIFT_EQ] THEN REAL_ARITH_TAC);;

let P2BKG_PHI_ADD = prove
 (`!top atlas (g:A->real^N^N) (X:A->real^N) y s t.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) X /\
     y IN topspace top
     ==> p2bkf_phi (top,atlas) g X t (p2bkf_phi (top,atlas) g X s y) =
         p2bkf_phi (top,atlas) g X (s + t) y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2bkf_phi] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `X:A->real^N`; `y:A`] P2BKF_ORBIT_SHIFT) THEN
  ASM_SIMP_TAC[]);;

let P2BKG_ORBIT_PRIM = prove
 (`!top atlas (g:A->real^3^3) (X:A->real^3) V h y s.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) X /\
     (!x. x IN topspace top ==> X x dot (g x ** X x) = &1) /\
     y IN topspace top /\ open_in top V /\ p2bkg_prim atlas g X V h /\ &0 <= s /\
     (!t. &0 <= t /\ t <= s ==> p2bkf_phi (top,atlas) g X t y IN V)
     ==> h(p2bkf_phi (top,atlas) g X s y) = h y + s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. p2bkf_fmap (top,atlas) (g:A->real^3^3) (X:A->real^3) y (vec 0) (vec 0)
          (vec 0 + t % basis 3) = p2bkf_phi (top,atlas) g X t y`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `X:A->real^3`; `y:A`; `vec 0:real^3`; `vec 0:real^3`; `vec 0:real^3`; `t:real`]
                  P2BKF_FMAP_SHIFT) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `X:A->real^3`; `y:A`; `vec 0:real^3`; `vec 0:real^3`; `vec 0:real^3`]
                  P2BKF_FMAP_D0) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `V:A->bool`; `h:A->real`; `y:A`; `vec 0:real^3`; `vec 0:real^3`;
                 `vec 0:real^3`; `s:real`] P2BKG_FMAP_PRIM_VERTICAL) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `y:A`; `vec 0:real^3`; `vec 0:real^3`; `vec 0:real^3`]
                P2BKF_FMAP_D0) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN SIMP_TAC[]);;

let P2BKG_ORBIT_PRIM_GEN = prove
 (`!top atlas (g:A->real^3^3) (X:A->real^3) V h y s.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) X /\
     (!x. x IN topspace top ==> X x dot (g x ** X x) = &1) /\
     y IN topspace top /\ open_in top V /\ p2bkg_prim atlas g X V h /\
     (!t. (&0 <= t /\ t <= s) \/ (s <= t /\ t <= &0) ==> p2bkf_phi (top,atlas) g X t y IN V)
     ==> h(p2bkf_phi (top,atlas) g X s y) = h y + s`,
  REPEAT STRIP_TAC THEN DISJ_CASES_TAC(REAL_ARITH `&0 <= s \/ s <= &0`) THENL
   [MATCH_MP_TAC P2BKG_ORBIT_PRIM THEN EXISTS_TAC `V:A->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `s:real`; `y:A`] P2BKF_PHI_INVERSE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `V:A->bool`; `h:A->real`;
                 `p2bkf_phi (top,atlas) (g:A->real^3^3) (X:A->real^3) s y`; `--s`]
                P2BKG_ORBIT_PRIM) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `X:A->real^3`; `y:A`; `s:real`; `t:real`] P2BKG_PHI_ADD) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* P2BKG.K12 The flow-out of a level set of a primitive is open: in the     *)
(* flow box at a point y of the level set, every z near 0 reaches the level *)
(* set along its vertical line, so fmap(z) is an orbit point of the level   *)
(* set; the flow-out is invariant under the flow.                           *)

let P2BKG_FLOWOUT_LOCAL = prove
 (`!top atlas (g:A->real^3^3) (X:A->real^3) V h c0 y.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) X /\
     (!x. x IN topspace top ==> X x dot (g x ** X x) = &1) /\
     open_in top V /\ p2bkg_prim atlas g X V h /\ y IN lvs_set V h c0
     ==> ?N. open_in top N /\ y IN N /\
             !x. x IN N ==> ?r y'. y' IN lvs_set V h c0 /\ p2bkf_phi (top,atlas) g X r y' = x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(y:A) IN lvs_set V h c0` THEN REWRITE_TAC[lvs_set; IN_ELIM_THM] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(g:A->real^3^3) y ** (X:A->real^3) y`; `(X:A->real^3) y`] P2BKF_HCOMPLEMENT) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `u1:real^3` (X_CHOOSE_THEN `u2:real^3`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `Fm = p2bkf_fmap (top,atlas) (g:A->real^3^3) (X:A->real^3) y u1 u2` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `y:A`; `u1:real^3`; `u2:real^3`] P2BKF_FMAP_PARAM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `V0:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `y:A`; `u1:real^3`; `u2:real^3`] P2BKF_FMAP_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `y:A`; `u1:real^3`; `u2:real^3`; `vec 0:real^3`]
                P2BKF_FMAP_D0) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `!z t. (Fm:real^3->A)(z + t % basis 3) =
                      p2bkf_phi (top,atlas) (g:A->real^3^3) (X:A->real^3) t (Fm z)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "Fm" THEN MATCH_MP_TAC P2BKF_FMAP_SHIFT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open {z:real^3 | z IN V0 /\ (Fm:real^3->A) z IN V}` ASSUME_TAC THENL
   [SUBGOAL_THEN `{z:real^3 | z IN V0 /\ (Fm:real^3->A) z IN V} =
                  V0 INTER {z | z IN topspace euclidean /\ Fm z IN V}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; TOPSPACE_EUCLIDEAN; IN_UNIV]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[OPEN_IN] THEN
    MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `vec 0:real^3`) THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(\z. lift((h:A->real)((Fm:real^3->A) z))) continuous at (vec 0)` MP_TAC THENL
   [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN REWRITE_TAC[differentiable] THEN
    EXISTS_TAC `\a. lift(mfd_differential (open_set_atlas (:real^3)) atlas (Fm:real^3->A)
                           (vec 0) a dot ((g:A->real^3^3)(Fm(vec 0)) ** (X:A->real^3)(Fm(vec 0))))` THEN
    MATCH_MP_TAC P2BKG_PRIM_MAP_DERIV THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `V:A->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
  ASM_REWRITE_TAC[REAL_HALF; DIST_LIFT] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (Fm:real^3->A) (ball(vec 0,min d (e / &2)))` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `V0:real^3->bool`] THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `ball(vec 0:real^3,e)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 0:real^3` THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL; REAL_LT_MIN; REAL_HALF];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_BALL_0; REAL_LT_MIN] THEN
  X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
  ABBREV_TAC `t = c0 - (h:A->real)((Fm:real^3->A) z)` THEN
  SUBGOAL_THEN `abs t < e / &2` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[DIST_0] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!tau. abs tau <= abs t ==> (Fm:real^3->A)(z + tau % basis 3) IN V`
  ASSUME_TAC THENL
   [X_GEN_TAC `tau:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `z + tau % basis 3 IN ball(vec 0:real^3,e)` MP_TAC THENL
     [REWRITE_TAC[IN_BALL_0] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `norm(z:real^3) + norm(tau % basis 3:real^3)` THEN
      REWRITE_TAC[NORM_TRIANGLE] THEN
      SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC;
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Fm:real^3->A) z IN V` ASSUME_TAC THENL
   [MP_TAC(SPEC `&0` (ASSUME `!tau. abs tau <= abs t ==> (Fm:real^3->A)(z + tau % basis 3) IN V`)) THEN
    REWRITE_TAC[REAL_ABS_0; REAL_ABS_POS; VECTOR_MUL_LZERO; VECTOR_ADD_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Fm:real^3->A) z IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(h:A->real)(p2bkf_phi (top,atlas) (g:A->real^3^3) (X:A->real^3) t
                               ((Fm:real^3->A) z)) = h(Fm z) + t`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BKG_ORBIT_PRIM_GEN THEN EXISTS_TAC `V:A->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `tau:real` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM(ASSUME `!z t. (Fm:real^3->A)(z + t % basis 3) =
                               p2bkf_phi (top,atlas) (g:A->real^3^3) (X:A->real^3) t (Fm z)`)] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`--t:real`; `p2bkf_phi (top,atlas) (g:A->real^3^3) (X:A->real^3) t ((Fm:real^3->A) z)`] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[lvs_set; IN_ELIM_THM] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM(ASSUME `!z t. (Fm:real^3->A)(z + t % basis 3) =
                               p2bkf_phi (top,atlas) (g:A->real^3^3) (X:A->real^3) t (Fm z)`)] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN REAL_ARITH_TAC];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `X:A->real^3`; `t:real`; `(Fm:real^3->A) z`] P2BKF_PHI_INVERSE) THEN
    ASM_SIMP_TAC[]]);;

let P2BKG_FLOWOUT_OPEN = prove
 (`!top atlas (g:A->real^3^3) (X:A->real^3) V h c0.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) X /\
     (!x. x IN topspace top ==> X x dot (g x ** X x) = &1) /\
     open_in top V /\ p2bkg_prim atlas g X V h
     ==> open_in top {x | ?r y. y IN lvs_set V h c0 /\ p2bkf_phi (top,atlas) g X r y = x}`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
  REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `r:real`; `y:A`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `V:A->bool`; `h:A->real`; `c0:real`; `y:A`]
                P2BKG_FLOWOUT_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `N:A->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:A) IN lvs_set V h c0` THEN REWRITE_TAC[lvs_set; IN_ELIM_THM] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `--r`] P2BKF_PHI_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `{x':A | x' IN topspace top /\
                      p2bkf_phi (top,atlas) (g:A->real^3^3) (X:A->real^3) (--r) x' IN N}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[ETA_AX];
    REWRITE_TAC[IN_ELIM_THM] THEN EXPAND_TAC "x" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `X:A->real^3`; `r:real`; `y:A`] P2BKF_PHI_INVERSE) THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x':A` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p2bkf_phi (top,atlas) (g:A->real^3^3) (X:A->real^3) (--r) x'`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r':real` (X_CHOOSE_THEN `y':A` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`r' + r:real`; `y':A`] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(y':A) IN topspace top` ASSUME_TAC THENL
     [UNDISCH_TAC `(y':A) IN lvs_set V h c0` THEN REWRITE_TAC[lvs_set; IN_ELIM_THM] THEN
      ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `X:A->real^3`; `y':A`; `r':real`; `r:real`] P2BKG_PHI_ADD) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `X:A->real^3`; `--r`; `x':A`] P2BKF_PHI_INVERSE) THEN
    ASM_SIMP_TAC[REAL_NEG_NEG]]);;

(* P2BKG.K13 The flow-out of a compact level set of a primitive is the      *)
(* whole connected manifold: it is open (K12), and by a Lebesgue number of  *)
(* the open flow-out around the compact level set and the isometries Phi_r  *)
(* its complement is open too.                                              *)

let P2BKG_PHI_0 = prove
 (`!top atlas (g:A->real^N^N) (X:A->real^N) y.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     y IN topspace top
     ==> p2bkf_phi (top,atlas) g X (&0) y = y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2bkf_phi] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `y:A`; `(X:A->real^N) y`] MFD_GEO_MAXIMAL) THEN
  ASM_SIMP_TAC[]);;

let P2BKG_FLOWOUT_ALL = prove
 (`!top atlas (g:A->real^3^3) (X:A->real^3) V h c0.
     hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
     p2b_parallel_on atlas g (topspace top) X /\
     (!x. x IN topspace top ==> X x dot (g x ** X x) = &1) /\
     open_in top V /\ p2bkg_prim atlas g X V h /\
     compact_in top (lvs_set V h c0) /\ ~(lvs_set V h c0 = {})
     ==> !x. x IN topspace top
             ==> ?r y. y IN lvs_set V h c0 /\ p2bkf_phi (top,atlas) g X r y = x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lvs_set V (h:A->real) c0 SUBSET topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:A->bool`; `h:A->real`; `c0:real`] LVS_SET_SUBSET) THEN
    MP_TAC(ISPECL [`top:A topology`; `V:A->bool`] OPEN_IN_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top {x:A | ?r y. y IN lvs_set V h c0 /\
                                         p2bkf_phi (top,atlas) (g:A->real^3^3) (X:A->real^3) r y = x}`
  MP_TAC THENL
   [MATCH_MP_TAC P2BKG_FLOWOUT_OPEN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `L = lvs_set V (h:A->real) c0` THEN
  ABBREV_TAC `E = {x:A | ?r y. y IN L /\
                               p2bkf_phi (top,atlas) (g:A->real^3^3) (X:A->real^3) r y = x}` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `!x:A. (?r y. y IN L /\ p2bkf_phi (top,atlas) (g:A->real^3^3) (X:A->real^3) r y = x)
                      <=> x IN E`
  (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "E" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `(L:A->bool) SUBSET E` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `y:A` THEN
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`&0`; `y:A`] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2BKG_PHI_0 THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(E:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:A`; `r:real`; `y:A`] THEN STRIP_TAC THEN EXPAND_TAC "x" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `X:A->real^3`; `r:real`; `y:A`] P2BKF_PHI_INVERSE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r x:A. x IN topspace top /\
                        p2bkf_phi (top,atlas) (g:A->real^3^3) (X:A->real^3) r x IN E
                        ==> x IN E`
  (LABEL_TAC "inv") THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "E" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `s:real` (X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`s + --r:real`; `y:A`] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `X:A->real^3`; `y:A`; `s:real`; `--r:real`] P2BKG_PHI_ADD) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `X:A->real^3`; `r:real`; `x:A`] P2BKF_PHI_INVERSE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o
    check (fun th -> is_neg(concl th))) THEN
  DISCH_THEN(X_CHOOSE_TAC `y0:A`) THEN
  SUBGOAL_THEN `(y0:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `m = mfd_metric (top,atlas) (g:A->real^3^3) (y0:A)` THEN
  SUBGOAL_THEN `{y:A | mfd_joinable (top,atlas:((A->bool)#(A->real^3))->bool) y0 y} =
                topspace top` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `y:A` THEN EQ_TAC THENL
     [MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
      DISCH_TAC THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mtopology m = (top:A topology) /\ mspace m = topspace top /\
                (!x y. mdist m (x,y) = mfd_dist (top,atlas) (g:A->real^3^3) x y)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `y0:A`] MFD_METRIC) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `y0:A`] MFD_MTOPOLOGY) THEN
    ASM_REWRITE_TAC[SUBTOPOLOGY_TOPSPACE] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:A metric`; `L:A->bool`; `{E:A->bool}`] LEBESGUE_NUMBER) THEN
  ASM_REWRITE_TAC[IN_SING; UNIONS_1; FORALL_UNWIND_THM2; UNWIND_THM2] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "leb"))) THEN
  SUBGOAL_THEN `!x x':A. x IN topspace top /\ x' IN E /\
                         mfd_dist (top,atlas) (g:A->real^3^3) x x' < eps ==> x IN E`
  (LABEL_TAC "near") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `?s y. y IN L /\
                        p2bkf_phi (top,atlas) (g:A->real^3^3) (X:A->real^3) s y = (x':A)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x':A) IN E` THEN EXPAND_TAC "E" THEN REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "inv" (MATCH_MP_TAC o SPECL [`--s:real`; `x:A`]) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `p2bkf_phi (top,atlas) (g:A->real^3^3) (X:A->real^3) (--s) x' = y`
    ASSUME_TAC THENL
     [EXPAND_TAC "x'" THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `X:A->real^3`; `s:real`; `y:A`] P2BKF_PHI_INVERSE) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x':A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `g:A->real^3^3`; `X:A->real^3`; `--s:real`] P2BKF_PHI_ISOMETRY) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `p2bkf_phi (top,atlas) (g:A->real^3^3) (X:A->real^3) (--s)`;
                   `p2bkf_phi (top,atlas) (g:A->real^3^3) (X:A->real^3) (--(--s))`]
                  MFD_DIST_ISOMETRY) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`x':A`; `x:A`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `X:A->real^3`; `--s:real`; `x:A`] P2BKF_PHI_INVERSE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    USE_THEN "leb" (MP_TAC o SPEC `y:A`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_MBALL] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `x':A`; `x:A`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (topspace top DIFF (E:A->bool))` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN X_GEN_TAC `x:A` THEN REWRITE_TAC[IN_DIFF] THEN
    STRIP_TAC THEN EXISTS_TAC `mball m (x:A,eps)` THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_MBALL];
      MATCH_MP_TAC CENTRE_IN_MBALL THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `x':A` THEN
      REWRITE_TAC[IN_MBALL] THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN UNDISCH_TAC `~((x:A) IN E)` THEN REWRITE_TAC[] THEN
      USE_THEN "near" MATCH_MP_TAC THEN EXISTS_TAC `x':A` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `E:A->bool` o GEN_REWRITE_RULE I [CONNECTED_SPACE_CLOPEN_IN] o
    check (fun th -> concl th = `connected_space (top:A topology)`)) THEN
  ASM_REWRITE_TAC[closed_in] THEN ASM SET_TAC[]);;

(* P2BKG.K14 Leaf transport and injectivity of the orbit map: if Phi_r maps *)
(* one point of a connected level set L of a primitive into a closed level  *)
(* set L' of another primitive, it maps all of L into L' (open-closed in L, *)
(* by FB4 in a flow box); a return Phi_c(L) meets L with c > 0 is then      *)
(* excluded by a level set whose orbits stay in its domain for times <= c   *)
(* (the primitive grows by c along such an orbit).                          *)

let P2BKG_TRANSPORT_LOCAL = prove
 (`!top atlas (g:A->real^3^3) (X:A->real^3) V h c0 V' h' c0' r y.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) X /\
     (!x. x IN topspace top ==> X x dot (g x ** X x) = &1) /\
     open_in top V /\ p2bkg_prim atlas g X V h /\
     open_in top V' /\ p2bkg_prim atlas g X V' h' /\
     y IN lvs_set V h c0 /\ p2bkf_phi (top,atlas) g X r y IN lvs_set V' h' c0'
     ==> ?N. open_in top N /\ y IN N /\
             !y'. y' IN N /\ y' IN lvs_set V h c0
                  ==> p2bkf_phi (top,atlas) g X r y' IN lvs_set V' h' c0'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lvs_set; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(g:A->real^3^3) y ** (X:A->real^3) y`; `(X:A->real^3) y`] P2BKF_HCOMPLEMENT) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `u1:real^3` (X_CHOOSE_THEN `u2:real^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `V':A->bool`; `h':A->real`; `V:A->bool`; `h:A->real`;
                 `y:A`; `u1:real^3`; `u2:real^3`; `r:real`; `&0`] P2BKG_FMAP_PRIM_CONST) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN DISCH_THEN(LABEL_TAC "pc") THEN
  SUBGOAL_THEN `!z t. p2bkf_fmap (top,atlas) (g:A->real^3^3) (X:A->real^3) y u1 u2 (z + t % basis 3) =
                      p2bkf_phi (top,atlas) g X t (p2bkf_fmap (top,atlas) g X y u1 u2 z)`
  (LABEL_TAC "shift") THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC P2BKF_FMAP_SHIFT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `Fm = p2bkf_fmap (top,atlas) (g:A->real^3^3) (X:A->real^3) y u1 u2` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `y:A`; `u1:real^3`; `u2:real^3`] P2BKF_FMAP_PARAM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `V0:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `y:A`; `u1:real^3`; `u2:real^3`] P2BKF_FMAP_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `y:A`; `u1:real^3`; `u2:real^3`; `r:real`]
                P2BKF_FMAP_TRANSL_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `y:A`; `u1:real^3`; `u2:real^3`; `vec 0:real^3`]
                P2BKF_FMAP_D0) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `(Fm:real^3->A)(vec 0 + r % basis 3) =
                p2bkf_phi (top,atlas) (g:A->real^3^3) (X:A->real^3) r y`
  ASSUME_TAC THENL
   [USE_THEN "shift" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open {z:real^3 | z IN V0 /\ (Fm:real^3->A) z IN V /\ Fm(z + r % basis 3) IN V'}`
  MP_TAC THENL
   [SUBGOAL_THEN `{z:real^3 | z IN V0 /\ (Fm:real^3->A) z IN V /\ Fm(z + r % basis 3) IN V'} =
                  V0 INTER {z | z IN topspace euclidean /\ Fm z IN V} INTER
                  {z | z IN topspace euclidean /\ (Fm o (\z. z + r % basis 3)) z IN V'}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; TOPSPACE_EUCLIDEAN; IN_UNIV; o_THM];
      ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[OPEN_IN] THEN MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `vec 0:real^3`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ball"))) THEN
  USE_THEN "pc" (MP_TAC o SPEC `ball(vec 0:real^3,e)`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[CONVEX_BALL] THEN USE_THEN "ball" MP_TAC THEN SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` (LABEL_TAC "k")) THEN
  SUBGOAL_THEN `k = c0' - c0` ASSUME_TAC THENL
   [USE_THEN "k" (MP_TAC o SPEC `vec 0:real^3`) THEN
    REWRITE_TAC[CENTRE_IN_BALL] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (Fm:real^3->A) (ball(vec 0,e))` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `V0:real^3->bool`] THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN USE_THEN "ball" MP_TAC THEN SET_TAC[];
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 0:real^3` THEN ASM_REWRITE_TAC[CENTRE_IN_BALL];
    REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^3` THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `(Fm:real^3->A)(z + r % basis 3) IN V'` ASSUME_TAC THENL
     [UNDISCH_TAC `z IN ball(vec 0:real^3,e)` THEN USE_THEN "ball" MP_TAC THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "shift" (fun th -> REWRITE_TAC[GSYM th]) THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "k" (MP_TAC o SPEC `z:real^3`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let P2BKG_LEAF_TRANSPORT = prove
 (`!top atlas (g:A->real^3^3) (X:A->real^3) V h c0 V' h' c0' r.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) X /\
     (!x. x IN topspace top ==> X x dot (g x ** X x) = &1) /\
     open_in top V /\ p2bkg_prim atlas g X V h /\
     open_in top V' /\ p2bkg_prim atlas g X V' h' /\
     connected_in top (lvs_set V h c0) /\ closed_in top (lvs_set V' h' c0') /\
     (?y0. y0 IN lvs_set V h c0 /\ p2bkf_phi (top,atlas) g X r y0 IN lvs_set V' h' c0')
     ==> !y. y IN lvs_set V h c0 ==> p2bkf_phi (top,atlas) g X r y IN lvs_set V' h' c0'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `L = lvs_set V (h:A->real) c0` THEN
  ABBREV_TAC `L' = lvs_set V' (h':A->real) c0'` THEN
  SUBGOAL_THEN `(L:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN MP_TAC(ISPECL [`V:A->bool`; `h:A->real`; `c0:real`] LVS_SET_SUBSET) THEN
    MP_TAC(ISPECL [`top:A topology`; `V:A->bool`] OPEN_IN_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `B = {y:A | y IN L /\
                         p2bkf_phi (top,atlas) (g:A->real^3^3) (X:A->real^3) r y IN L'}` THEN
  SUBGOAL_THEN `B:A->bool = L` MP_TAC THENL
   [ALL_TAC; EXPAND_TAC "B" THEN SET_TAC[]] THEN
  UNDISCH_TAC `connected_in top (L:A->bool)` THEN REWRITE_TAC[connected_in] THEN
  DISCH_THEN(MP_TAC o SPEC `B:A->bool` o GEN_REWRITE_RULE I [CONNECTED_SPACE_CLOPEN_IN] o
    CONJUNCT2) THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
  SUBGOAL_THEN `topspace top INTER L:A->bool = L` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(a /\ b) /\ ~c ==> (a /\ b ==> c \/ d) ==> d`) THEN CONJ_TAC THENL
   [ALL_TAC; EXPAND_TAC "B" THEN ASM SET_TAC[]] THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN X_GEN_TAC `y:A` THEN
    EXPAND_TAC "B" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `X:A->real^3`; `V:A->bool`; `h:A->real`; `c0:real`; `V':A->bool`;
                   `h':A->real`; `c0':real`; `r:real`; `y:A`] P2BKG_TRANSPORT_LOCAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `N:A->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `N INTER L:A->bool` THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN EXISTS_TAC `N:A->bool` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[IN_INTER];
      EXPAND_TAC "B" THEN REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN
      X_GEN_TAC `x:A` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[CLOSED_IN_SUBTOPOLOGY] THEN
    EXISTS_TAC `{x:A | x IN topspace top /\
                       p2bkf_phi (top,atlas) (g:A->real^3^3) (X:A->real^3) r x IN L'}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAP_PREIMAGE THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[ETA_AX] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `X:A->real^3`; `r:real`] P2BKF_PHI_SMOOTH) THEN
      ASM_SIMP_TAC[];
      EXPAND_TAC "B" THEN UNDISCH_TAC `(L:A->bool) SUBSET topspace top` THEN SET_TAC[]]]);;

let P2BKG_ORBIT_INJECTIVE = prove
 (`!top atlas (g:A->real^3^3) (X:A->real^3) V h c0.
     hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
     p2b_parallel_on atlas g (topspace top) X /\
     (!x. x IN topspace top ==> X x dot (g x ** X x) = &1) /\
     open_in top V /\ p2bkg_prim atlas g X V h /\
     compact_in top (lvs_set V h c0) /\ connected_in top (lvs_set V h c0) /\
     ~(lvs_set V h c0 = {}) /\
     (!tk. ?V' h' c0'. open_in top V' /\ p2bkg_prim atlas g X V' h' /\
                      compact_in top (lvs_set V' h' c0') /\ ~(lvs_set V' h' c0' = {}) /\
                      !z s. z IN lvs_set V' h' c0' /\ abs s <= tk
                            ==> p2bkf_phi (top,atlas) g X s z IN V')
     ==> !y y' r r'. y IN lvs_set V h c0 /\ y' IN lvs_set V h c0 /\
                     p2bkf_phi (top,atlas) g X r y = p2bkf_phi (top,atlas) g X r' y'
                     ==> y = y' /\ r = r'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lvs_set V (h:A->real) c0 SUBSET topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:A->bool`; `h:A->real`; `c0:real`] LVS_SET_SUBSET) THEN
    MP_TAC(ISPECL [`top:A topology`; `V:A->bool`] OPEN_IN_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y1 y2 c. y1 IN lvs_set V h c0 /\ y2 IN lvs_set V h c0 /\ &0 < c
              ==> ~(p2bkf_phi (top,atlas) (g:A->real^3^3) (X:A->real^3) c y1 = y2)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `!y. y IN lvs_set V h c0
                      ==> p2bkf_phi (top,atlas) (g:A->real^3^3) (X:A->real^3) c y IN
                          lvs_set V h c0`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `X:A->real^3`; `V:A->bool`; `h:A->real`; `c0:real`; `V:A->bool`;
                     `h:A->real`; `c0:real`; `c:real`] P2BKG_LEAF_TRANSPORT) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[COMPACT_IN_IMP_CLOSED_IN] THEN EXISTS_TAC `y1:A` THEN ASM_REWRITE_TAC[];
        SIMP_TAC[]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `V'':A->bool` (X_CHOOSE_THEN `h'':A->real`
      (X_CHOOSE_THEN `c0'':real` STRIP_ASSUME_TAC)) o SPEC `c:real`) THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `z:A` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o
      check (fun th -> is_neg(concl th) && free_in `V'':A->bool` (concl th))) THEN
    SUBGOAL_THEN `(z:A) IN topspace top` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:A) IN lvs_set V'' h'' c0''` THEN REWRITE_TAC[lvs_set; IN_ELIM_THM] THEN
      ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `X:A->real^3`; `V:A->bool`; `h:A->real`; `c0:real`] P2BKG_FLOWOUT_ALL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `z:A`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r0:real` (X_CHOOSE_THEN `w0:A` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `!y. y IN lvs_set V h c0
                      ==> p2bkf_phi (top,atlas) (g:A->real^3^3) (X:A->real^3) r0 y IN
                          lvs_set V'' h'' c0''`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `X:A->real^3`; `V:A->bool`; `h:A->real`; `c0:real`; `V'':A->bool`;
                     `h'':A->real`; `c0'':real`; `r0:real`] P2BKG_LEAF_TRANSPORT) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[COMPACT_IN_IMP_CLOSED_IN] THEN EXISTS_TAC `w0:A` THEN ASM_REWRITE_TAC[];
        SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(w0:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `p2bkf_phi (top,atlas) (g:A->real^3^3) (X:A->real^3) c z IN lvs_set V'' h'' c0''`
    ASSUME_TAC THENL
     [EXPAND_TAC "z" THEN
      SUBGOAL_THEN
       `p2bkf_phi (top,atlas) (g:A->real^3^3) (X:A->real^3) c (p2bkf_phi (top,atlas) g X r0 w0) =
        p2bkf_phi (top,atlas) g X r0 (p2bkf_phi (top,atlas) g X c w0)`
      SUBST1_TAC THENL
       [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                       `X:A->real^3`; `w0:A`; `r0:real`; `c:real`] P2BKG_PHI_ADD) THEN
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                       `X:A->real^3`; `w0:A`; `c:real`; `r0:real`] P2BKG_PHI_ADD) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `X:A->real^3`; `V'':A->bool`; `h'':A->real`; `z:A`; `c:real`]
                  P2BKG_ORBIT_PRIM) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `p2bkf_phi (top,atlas) (g:A->real^3^3) (X:A->real^3) c z IN lvs_set V'' h'' c0''` THEN
    UNDISCH_TAC `(z:A) IN lvs_set V'' h'' c0''` THEN
    REWRITE_TAC[lvs_set; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y:A`; `y':A`; `r:real`; `r':real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:A) IN topspace top /\ (y':A) IN topspace top` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `p2bkf_phi (top,atlas) (g:A->real^3^3) (X:A->real^3) (r - r') y = y'`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `X:A->real^3`; `y:A`; `r:real`; `--r'`] P2BKG_PHI_ADD) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `X:A->real^3`; `r':real`; `y':A`] P2BKF_PHI_INVERSE) THEN
    ASM_REWRITE_TAC[real_sub] THEN STRIP_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISJ_CASES_TAC(REAL_ARITH `r - r' = &0 \/ &0 < r - r' \/ &0 < --(r - r')`) THENL
   [SUBGOAL_THEN `r:real = r'` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p2bkf_phi (top,atlas) (g:A->real^3^3) (X:A->real^3) (r - r') y = y'` THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `X:A->real^3`; `y:A`] P2BKG_PHI_0) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM DISJ_CASES_TAC THENL
   [ASM_MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`y':A`; `y:A`; `--(r - r')`]) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `X:A->real^3`; `r - r'`; `y:A`] P2BKF_PHI_INVERSE) THEN
    ASM_SIMP_TAC[]]);;

(* P2BKG.K15 Thick level sets from the shell estimate: if the primitive h   *)
(* on psi(shell(exp(-a), exp a)) satisfies abs(h(psi y) - c0 - kappa        *)
(* log(norm y)) <= delta, the orbits from its c0-level set stay in          *)
(* psi(shell) for times s with abs s + delta < kappa a: before leaving, the *)
(* orbit stays in psi of a compact sub-shell (h grows at unit rate), which  *)
(* is closed (first exit time argument).                                    *)

let P2BKG_BETWEEN_SCALE = prove
 (`!s tau t. &0 <= tau /\ ((&0 <= t /\ t <= tau * s) \/ (tau * s <= t /\ t <= &0))
             ==> ?t'. &0 <= t' /\ t' <= tau /\ t = t' * s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  ASM_CASES_TAC `s = &0` THENL
   [EXISTS_TAC `&0` THEN
    UNDISCH_TAC `(&0 <= t /\ t <= tau * s) \/ (tau * s <= t /\ t <= &0)` THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `t / s` THEN ASM_SIMP_TAC[REAL_DIV_RMUL] THEN
  SUBGOAL_THEN `&0 < s \/ s < &0` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THENL
   [SUBGOAL_THEN `&0 <= tau * s` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_MUL_LZERO] THEN
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `t / s = (--t) / (--s)` SUBST1_TAC THENL
     [REWRITE_TAC[real_div; REAL_INV_NEG; REAL_NEG_MUL2]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < --s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= tau * --s` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_RNEG] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_MUL_LZERO; REAL_MUL_RNEG] THEN
    ASM_REAL_ARITH_TAC]);;

let P2BKG_ORBIT_CURVE_CONT = prove
 (`!top atlas (g:A->real^N^N) (X:A->real^N) z s.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) X /\
     z IN topspace top
     ==> continuous_map (subtopology euclideanreal (:real),top)
                        (\tau. p2bkf_phi (top,atlas) g X (tau * s) z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `X:A->real^N`; `z:A`] P2BKF_ORBIT) THEN
  ASM_REWRITE_TAC[mfd_geodesic] THEN STRIP_TAC THEN REWRITE_TAC[p2bkf_phi] THEN
  SUBGOAL_THEN `(\tau. mfd_geo (top,atlas) (g:A->real^N^N) z ((X:A->real^N) z) (tau * s)) =
                mfd_geo (top,atlas) g z (X z) o (\tau. tau * s)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology euclideanreal (:real)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM TOPSPACE_EUCLIDEANREAL; SUBTOPOLOGY_TOPSPACE] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_RMUL THEN REWRITE_TAC[CONTINUOUS_MAP_ID]);;

let P2BKG_SHELL_THICK = prove
 (`!top atlas (g:A->real^3^3) (X:A->real^3) (psi:real^3->A) h a kappa delta c0.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) X /\
     (!x. x IN topspace top ==> X x dot (g x ** X x) = &1) /\
     mfd_param top atlas (annulus (exp(--a)) (exp a)) psi /\
     p2bkg_prim atlas g X (IMAGE psi (annulus (exp(--a)) (exp a))) h /\ &0 < kappa /\
     (!y. y IN annulus (exp(--a)) (exp a)
          ==> abs((h(psi y) - c0) - kappa * log(norm y)) <= delta)
     ==> !z s. z IN lvs_set (IMAGE psi (annulus (exp(--a)) (exp a))) h c0 /\
               abs s + delta < kappa * a
               ==> p2bkf_phi (top,atlas) g X s z IN IMAGE psi (annulus (exp(--a)) (exp a))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`z:A`; `s:real`] THEN STRIP_TAC THEN
  ABBREV_TAC `S = annulus (exp(--a)) (exp a):real^3->bool` THEN
  UNDISCH_TAC `mfd_param top (atlas:((A->bool)#(A->real^3))->bool) S psi` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  REWRITE_TAC[mfd_param] THEN DISCH_THEN(X_CHOOSE_TAC `e':A->real^3`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `S:real^3->bool`; `psi:real^3->A`; `e':A->real^3`] LVS_DIFFEO_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `V = IMAGE (psi:real^3->A) S` THEN
  UNDISCH_TAC `(z:A) IN lvs_set V h c0` THEN REWRITE_TAC[lvs_set; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:A) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `R = (abs s + delta) / kappa` THEN
  SUBGOAL_THEN `R < a` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `K = cball(vec 0:real^3,exp R) DIFF ball(vec 0,exp(--R))` THEN
  SUBGOAL_THEN `(K:real^3->bool) SUBSET S` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[SUBSET; annulus; IN_DIFF; IN_CBALL_0; IN_BALL_0; IN_ELIM_THM; REAL_NOT_LT] THEN
    GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `exp(--R)` THEN
      ASM_REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `exp R` THEN
      ASM_REWRITE_TAC[REAL_EXP_MONO_LT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed_in top (IMAGE (psi:real^3->A) K)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `S:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "K" THEN
    SIMP_TAC[COMPACT_DIFF; COMPACT_CBALL; OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (psi:real^3->A) K SUBSET V` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN V /\ abs((h:A->real) x - c0) <= abs s ==> x IN IMAGE (psi:real^3->A) K`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN EXPAND_TAC "V" THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(MP (SPEC `y:real^3` (ASSUME
     `!y:real^3. y IN S ==> abs(((h:A->real)((psi:real^3->A) y) - c0) - kappa * log(norm y))
                            <= delta`)) (ASSUME `(y:real^3) IN S`)) THEN
    DISCH_TAC THEN
    UNDISCH_TAC `(y:real^3) IN S` THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
     [MP_TAC(SPEC `--a` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `abs((h:A->real) x - c0) <= abs s` THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `abs(log(norm(y:real^3))) <= R` ASSUME_TAC THENL
     [EXPAND_TAC "R" THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      SUBGOAL_THEN `kappa * abs(log(norm(y:real^3))) = abs(kappa * log(norm y))` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_ABS_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < k ==> abs k = k`];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    EXPAND_TAC "K" THEN REWRITE_TAC[IN_DIFF; IN_CBALL_0; IN_BALL_0; REAL_NOT_LT] THEN
    ONCE_REWRITE_TAC[GSYM(MATCH_MP EXP_LOG (ASSUME `&0 < norm(y:real^3)`))] THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!tau. &0 <= tau /\ tau <= &1 /\
          (!t. &0 <= t /\ t <= tau
               ==> p2bkf_phi (top,atlas) (g:A->real^3^3) (X:A->real^3) (t * s) z IN V)
          ==> p2bkf_phi (top,atlas) g X (tau * s) z IN IMAGE (psi:real^3->A) K`
  (LABEL_TAC "C") THENL
   [X_GEN_TAC `tau:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    SUBGOAL_THEN
     `(h:A->real)(p2bkf_phi (top,atlas) (g:A->real^3^3) (X:A->real^3) (tau * s) z) =
      h z + tau * s`
    ASSUME_TAC THENL
     [MATCH_MP_TAC P2BKG_ORBIT_PRIM_GEN THEN EXISTS_TAC `V:A->bool` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `t:real` THEN DISCH_TAC THEN
      MP_TAC(SPECL [`s:real`; `tau:real`; `t:real`] P2BKG_BETWEEN_SCALE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `t':real` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_ARITH `(c + x) - c = x`; REAL_ABS_MUL] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= &1 * y ==> x <= y`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `X:A->real^3`; `z:A`; `s:real`] P2BKG_ORBIT_CURVE_CONT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  ABBREV_TAC `Bad = {tau | &0 <= tau /\ tau <= &1 /\
                           ~(p2bkf_phi (top,atlas) (g:A->real^3^3) (X:A->real^3) (tau * s) z IN V)}` THEN
  SUBGOAL_THEN `&1 IN Bad` ASSUME_TAC THENL
   [EXPAND_TAC "Bad" THEN ASM_REWRITE_TAC[IN_ELIM_THM; REAL_MUL_LID] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `Bad:real->bool` INF) THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; EXISTS_TAC `&0` THEN EXPAND_TAC "Bad" THEN
                    SIMP_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  ABBREV_TAC `ts = inf Bad` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "inf1") (LABEL_TAC "inf2")) THEN
  SUBGOAL_THEN `&0 <= ts /\ ts <= &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "inf2" MATCH_MP_TAC THEN EXPAND_TAC "Bad" THEN SIMP_TAC[IN_ELIM_THM];
      USE_THEN "inf1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!tau. &0 <= tau /\ tau < ts
          ==> p2bkf_phi (top,atlas) (g:A->real^3^3) (X:A->real^3) (tau * s) z IN V`
  (LABEL_TAC "good") THENL
   [X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(tau:real) IN Bad` MP_TAC THENL
     [EXPAND_TAC "Bad" THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      DISCH_TAC THEN
      SUBGOAL_THEN `ts <= tau:real` MP_TAC THENL
       [USE_THEN "inf1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2bkf_phi (top,atlas) (g:A->real^3^3) (X:A->real^3) (ts * s) z IN V`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `ts = &0` THENL
     [ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                     `X:A->real^3`; `z:A`] P2BKG_PHI_0) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `p2bkf_phi (top,atlas) (g:A->real^3^3) (X:A->real^3) (ts * s) z IN
                  IMAGE (psi:real^3->A) K` MP_TAC THENL
     [ALL_TAC; ASM SET_TAC[]] THEN
    GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`;
                   `\tau. p2bkf_phi (top,atlas) (g:A->real^3^3) (X:A->real^3) (tau * s) z`;
                   `(:real)`; `topspace top DIFF IMAGE (psi:real^3->A) K`; `ts:real`]
                  P2BKF_EVENTUALLY_IN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_OPEN_UNIV; IN_UNIV; IN_DIFF] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `closed_in top (IMAGE (psi:real^3->A) K)` THEN SIMP_TAC[closed_in];
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `X:A->real^3`; `ts * s:real`; `z:A`]
                      P2BKF_PHI_INVERSE) THEN
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNIV; IN_DIFF] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `ts - min ts d / &2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[DE_MORGAN_THM] THEN DISJ2_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "C" MATCH_MP_TAC THEN
    REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN USE_THEN "good" MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`;
                 `\tau. p2bkf_phi (top,atlas) (g:A->real^3^3) (X:A->real^3) (tau * s) z`;
                 `(:real)`; `V:A->bool`; `ts:real`] P2BKF_EVENTUALLY_IN) THEN
  ASM_REWRITE_TAC[REAL_OPEN_UNIV; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?b. b IN Bad /\ b < ts + d` STRIP_ASSUME_TAC THENL
   [REFUTE_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; REAL_NOT_LT]) THEN
    SUBGOAL_THEN `ts + d <= ts` MP_TAC THENL
     [USE_THEN "inf2" MATCH_MP_TAC THEN ASM_MESON_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `ts <= b:real` ASSUME_TAC THENL
   [USE_THEN "inf1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(b:real) IN Bad` THEN EXPAND_TAC "Bad" THEN REWRITE_TAC[IN_ELIM_THM] THEN
  STRIP_TAC THEN UNDISCH_TAC
   `~(p2bkf_phi (top,atlas) (g:A->real^3^3) (X:A->real^3) (b * s) z IN V)` THEN
  REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

(* P2BKG.K16 The global product, orbit form: for a compact connected        *)
(* nonempty level set L of a primitive and level sets of every thickness,   *)
(* (y,r) |-> Phi_r(y) is a bijection L x R -> M; shells with the            *)
(* logarithmic estimate supply such thick level sets (nonempty by the       *)
(* intermediate value theorem along a ray).                                 *)

let P2BKG_ORBIT_BIJECTIVE = prove
 (`!top atlas (g:A->real^3^3) (X:A->real^3) V h c0.
     hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
     p2b_parallel_on atlas g (topspace top) X /\
     (!x. x IN topspace top ==> X x dot (g x ** X x) = &1) /\
     open_in top V /\ p2bkg_prim atlas g X V h /\
     compact_in top (lvs_set V h c0) /\ connected_in top (lvs_set V h c0) /\
     ~(lvs_set V h c0 = {}) /\
     (!tk. ?V' h' c0'. open_in top V' /\ p2bkg_prim atlas g X V' h' /\
                      compact_in top (lvs_set V' h' c0') /\ ~(lvs_set V' h' c0' = {}) /\
                      !z s. z IN lvs_set V' h' c0' /\ abs s <= tk
                            ==> p2bkf_phi (top,atlas) g X s z IN V')
     ==> (!x. x IN topspace top
              ==> ?r y. y IN lvs_set V h c0 /\ p2bkf_phi (top,atlas) g X r y = x) /\
         (!y y' r r'. y IN lvs_set V h c0 /\ y' IN lvs_set V h c0 /\
                      p2bkf_phi (top,atlas) g X r y = p2bkf_phi (top,atlas) g X r' y'
                      ==> y = y' /\ r = r')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2BKG_FLOWOUT_ALL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2BKG_ORBIT_INJECTIVE THEN ASM_REWRITE_TAC[]]);;

let P2BKG_SHELL_LEVEL_NONEMPTY = prove
 (`!top atlas (psi:real^3->A) (h:A->real) a kappa delta c0.
     smooth_manifold_atlas top atlas /\
     mfd_param top atlas (annulus (exp(--a)) (exp a)) psi /\
     mfd_smooth_on atlas (IMAGE psi (annulus (exp(--a)) (exp a))) (\x. lift(h x)) /\
     &0 < kappa /\ &0 <= delta /\ delta < kappa * a /\
     (!y. y IN annulus (exp(--a)) (exp a)
          ==> abs((h(psi y) - c0) - kappa * log(norm y)) <= delta)
     ==> ~(lvs_set (IMAGE psi (annulus (exp(--a)) (exp a))) h c0 = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `S = annulus (exp(--a)) (exp a):real^3->bool` THEN
  UNDISCH_TAC `mfd_param top (atlas:((A->bool)#(A->real^3))->bool) S psi` THEN
  REWRITE_TAC[mfd_param] THEN DISCH_THEN(X_CHOOSE_TAC `e':A->real^3`) THEN
  SUBGOAL_THEN `(\y. lift((h:A->real)((psi:real^3->A) y))) continuous_on S` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN
    SUBGOAL_THEN `(\y. lift((h:A->real)((psi:real^3->A) y))) = (\x. lift(h x)) o psi`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC LVS_PARAM_SMOOTH_COMPOSE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `IMAGE (psi:real^3->A) S`; `e':A->real^3`] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `S:real^3->bool`; `psi:real^3->A`; `e':A->real^3`] LVS_DIFFEO_FACTS) THEN
    ASM_SIMP_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `delta / kappa < a` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= delta / kappa` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE]; ALL_TAC] THEN
  ABBREV_TAC `b = (delta / kappa + a) / &2` THEN
  SUBGOAL_THEN `delta < kappa * b /\ b < a /\ &0 < b` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `delta / kappa < b` MP_TAC THENL
       [EXPAND_TAC "b" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN REAL_ARITH_TAC;
      EXPAND_TAC "b" THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "b" THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. exp(--b) <= t /\ t <= exp b ==> t % basis 1 IN (S:real^3->bool)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[annulus; IN_ELIM_THM; NORM_MUL] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
    SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL
     [MP_TAC(SPEC `--b` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `exp(--b)` THEN
      ASM_REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `exp b` THEN
      ASM_REWRITE_TAC[REAL_EXP_MONO_LT]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^1. lift((h:A->real)((psi:real^3->A)(drop x % basis 1)) - c0)`;
                 `lift(exp(--b))`; `lift(exp b)`; `&0`; `1`] IVT_INCREASING_COMPONENT_ON_1) THEN
  REWRITE_TAC[LIFT_DROP; DIMINDEX_1; LE_REFL; GSYM drop] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      SUBGOAL_THEN `(\x:real^1. lift((h:A->real)((psi:real^3->A)(drop x % basis 1)))) =
                    (\y. lift(h(psi y))) o (\x. drop x % basis 1)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN
        REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `S:real^3->bool` THEN
        ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1; LIFT_DROP] THEN
        ASM_MESON_TAC[]];
      REWRITE_TAC[DROP_SUB; LIFT_DROP] THEN
      MP_TAC(SPEC `exp(--b) % basis 1:real^3`
        (ASSUME `!y:real^3. y IN S ==> abs(((h:A->real)((psi:real^3->A) y) - c0) -
                                           kappa * log(norm y)) <= delta`)) THEN
      ANTS_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[REAL_LE_REFL; REAL_EXP_MONO_LE] THEN
                      ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[NORM_MUL] THEN SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
      REWRITE_TAC[REAL_ABS_EXP; LOG_EXP] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[DROP_SUB; LIFT_DROP] THEN
      MP_TAC(SPEC `exp b % basis 1:real^3`
        (ASSUME `!y:real^3. y IN S ==> abs(((h:A->real)((psi:real^3->A) y) - c0) -
                                           kappa * log(norm y)) <= delta`)) THEN
      ANTS_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
                      ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[NORM_MUL] THEN SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
      REWRITE_TAC[REAL_ABS_EXP; LOG_EXP] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_SUB] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^1` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; lvs_set; IN_ELIM_THM; IN_IMAGE] THEN
  EXISTS_TAC `(psi:real^3->A)(drop x % basis 1)` THEN CONJ_TAC THENL
   [EXISTS_TAC `drop x % basis 1:real^3` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC]);;

let P2BKG_SHELL_THICK_FAMILY = prove
 (`!top atlas (g:A->real^3^3) (X:A->real^3).
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_complete (top,atlas) g /\ p2b_parallel_on atlas g (topspace top) X /\
     (!x. x IN topspace top ==> X x dot (g x ** X x) = &1) /\
     (!tk. ?psi h a kappa delta c0.
            mfd_param top atlas (annulus (exp(--a)) (exp a)) psi /\
            p2bkg_prim atlas g X (IMAGE psi (annulus (exp(--a)) (exp a))) h /\
            &0 < kappa /\ &0 <= delta /\ tk + delta < kappa * a /\
            (!y. y IN annulus (exp(--a)) (exp a)
                 ==> abs((h(psi y) - c0) - kappa * log(norm y)) <= delta))
     ==> !tk. ?V' h' c0'. open_in top V' /\ p2bkg_prim atlas g X V' h' /\
                         compact_in top (lvs_set V' h' c0') /\ ~(lvs_set V' h' c0' = {}) /\
                         !z s. z IN lvs_set V' h' c0' /\ abs s <= tk
                               ==> p2bkf_phi (top,atlas) g X s z IN V'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `tk:real` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `abs tk`) THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:real^3->A` (X_CHOOSE_THEN `h:A->real`
    (X_CHOOSE_THEN `a:real` (X_CHOOSE_THEN `kappa:real` (X_CHOOSE_THEN `delta:real`
    (X_CHOOSE_THEN `c0:real` STRIP_ASSUME_TAC)))))) THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (psi:real^3->A) (annulus (exp(--a)) (exp a))`; `h:A->real`;
                        `c0:real`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `delta < kappa * a` ASSUME_TAC THENL
   [MP_TAC(SPEC `tk:real` REAL_ABS_POS) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_smooth_on (atlas:((A->bool)#(A->real^3))->bool)
                              (IMAGE (psi:real^3->A) (annulus (exp(--a)) (exp a)))
                              (\x. lift((h:A->real) x))` ASSUME_TAC THENL
   [UNDISCH_TAC `p2bkg_prim atlas (g:A->real^3^3) (X:A->real^3)
                   (IMAGE (psi:real^3->A) (annulus (exp(--a)) (exp a))) h` THEN
    SIMP_TAC[p2bkg_prim];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `mfd_param top (atlas:((A->bool)#(A->real^3))->bool)
                           (annulus (exp(--a)) (exp a)) psi` THEN
    REWRITE_TAC[mfd_param] THEN DISCH_THEN(X_CHOOSE_TAC `e':A->real^3`) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `annulus (exp(--a)) (exp a):real^3->bool`; `psi:real^3->A`; `e':A->real^3`]
                  LVS_DIFFEO_FACTS) THEN
    ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `psi:real^3->A`;
                   `h:A->real`; `a:real`; `kappa:real`; `delta:real`; `c0:real`]
                  P2BKG_LEAF_COMPACT) THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC P2BKG_SHELL_LEVEL_NONEMPTY THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `kappa:real`; `delta:real`] THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`z:A`; `s:real`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `X:A->real^3`; `psi:real^3->A`; `h:A->real`; `a:real`; `kappa:real`;
                   `delta:real`; `c0:real`] P2BKG_SHELL_THICK) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

