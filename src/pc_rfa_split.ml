(* ========================================================================= *)
(* Unit pc_rfa_split: parallel fields from one chart to the vocabulary of    *)
(* Part 2B (p2b_parallel_on, p2b_locally_split of pc_p2b_splitreq), flatness *)
(* at a point, local splitting at an interior time, and the per-time         *)
(* dichotomy of the statement P2B_REQ_RFA_SMP_SPLIT_PT_STATEMENT at interior *)
(* times.                                                                    *)
(* ========================================================================= *)

needs "src/pc_rfa_null.ml";;
needs "src/pc_geo_covd.ml";;
needs "src/pc_p2b_splitreq.ml";;
needs "src/pc_rfa_smax1.ml";;

prioritize_real();;
type_invention_error := true;;


(* ========================================================================= *)
(* A field given in one chart: representatives in all charts,                *)
(* smoothness, the parallel equation and unit length (p2b_parallel_on).     *)
(* ========================================================================= *)

(* Vector fields given by their representative V0 in one chart c0: the      *)
(* preferred-coordinate field X x = J(c0 -> chart_at x) V0(c0 x), its        *)
(* representative in any chart, smoothness of the representatives, and the  *)
(* transfer of the parallel equation and of unit length to every chart.     *)

let RFA_VREP_FROM_CHART = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) c0 c (V0:real^N->real^N) x.
     smooth_manifold_atlas top atlas /\ c0 IN atlas /\ c IN atlas /\
     x IN FST c0 /\ x IN FST c
     ==> mfd_vrep atlas (\x. chart_jac c0 (chart_at atlas x) x (V0 (SND c0 x))) c (SND c x) =
         chart_jac c0 c x (V0 (SND c0 x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[mfd_vrep] THEN ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `x:A`] CHART_JAC_CHAIN) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th; o_THM]));;

(* The set W of points whose c0-coordinates lie in N0 is open. *)

let RFA_CHART_PREIMAGE_OPEN = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) c0 N0.
     smooth_manifold_atlas top atlas /\ c0 IN atlas /\ open N0
     ==> open_in top {x | x IN FST c0 /\ SND c0 x IN N0}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c0:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC MFDM_OPEN_IN_PREIMAGE THEN EXISTS_TAC `euclidean:(real^N)topology` THEN
  ASM_REWRITE_TAC[GSYM OPEN_IN] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`]
         SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  REWRITE_TAC[PAIR] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP o CONJUNCT2 o CONJUNCT2) THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; ETA_AX] THEN SIMP_TAC[]);;

(* The representative of the transported field in any chart c is smooth on *)
(* the chart image of FST c INTER W, W = {x in FST c0 | c0 x IN N0}.        *)

let RFA_VREP_SMOOTH_FROM_CHART = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) c0 c N0 (V0:real^N->real^N).
     smooth_manifold_atlas top atlas /\ c0 IN atlas /\ c IN atlas /\
     open N0 /\ smooth_map_on N0 V0
     ==> smooth_map_on
           (IMAGE (SND c) (FST c INTER {x | x IN FST c0 /\ SND c0 x IN N0}))
           (mfd_vrep atlas (\x. chart_jac c0 (chart_at atlas x) x (V0 (SND c0 x))) c)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `W = {x:A | x IN FST c0 /\ SND (c0:(A->bool)#(A->real^N)) x IN N0}` THEN
  ABBREV_TAC `O = IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER W)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `c0:(A->bool)#(A->real^N)`]
         GEOL_CHART_TRANS_FACTS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c0:(A->bool)#(A->real^N)`; `c:(A->bool)#(A->real^N)`]
         GEOL_CHART_TRANS_FACTS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c0:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open_in top (W:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN MATCH_MP_TAC RFA_CHART_PREIMAGE_OPEN THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (O:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET];
    ALL_TAC] THEN
  ABBREV_TAC `tau = chart_trans (c:(A->bool)#(A->real^N)) c0` THEN
  SUBGOAL_THEN
   `!y. y IN O
        ==> chart_inv (c:(A->bool)#(A->real^N)) y IN FST c /\
            chart_inv c y IN W /\ chart_inv c y IN FST (c0:(A->bool)#(A->real^N)) /\
            SND c (chart_inv c y) = y /\
            (tau:real^N->real^N) y = SND c0 (chart_inv c y) /\
            (tau:real^N->real^N) y IN N0 /\
            y IN IMAGE (SND c) (FST c INTER FST c0) /\
            tau y IN IMAGE (SND c0) (FST c0 INTER FST c)`
  ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:A) IN FST c0 /\ SND (c0:(A->bool)#(A->real^N)) x IN N0`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x:A) IN W` THEN EXPAND_TAC "W" THEN REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN EXPAND_TAC "tau" THEN ASM_SIMP_TAC[] THEN
    CONJ_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC
   `\y. matrix(frechet_derivative (chart_trans (c0:(A->bool)#(A->real^N)) c)
                                  (at ((tau:real^N->real^N) y))) ** (V0:real^N->real^N)(tau y)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c0:(A->bool)#(A->real^N)`; `c:(A->bool)#(A->real^N)`;
                   `V0:real^N->real^N`; `chart_inv (c:(A->bool)#(A->real^N)) y`]
           RFA_VREP_FROM_CHART) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[chart_jac] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `frechet_derivative (chart_trans (c0:(A->bool)#(A->real^N)) c)
                    (at (SND c0 (chart_inv (c:(A->bool)#(A->real^N)) y)))` MATRIX_WORKS) THEN
    ANTS_TAC THENL [ALL_TAC; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
    MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN REWRITE_TAC[differentiable] THEN
    EXISTS_TAC `chart_jac (c0:(A->bool)#(A->real^N)) c (chart_inv c y)` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `chart_inv (c:(A->bool)#(A->real^N)) y` o
      check (fun th -> can (term_match [] `!x:A. x IN FST (c0:(A->bool)#(A->real^N)) INTER FST c
             ==> (chart_trans c0 c has_derivative chart_jac c0 c x) (at (SND c0 x))`) (concl th))) THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  MATCH_MP_TAC LRG_SMOOTH_MATVEC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `(vectorize:real^N^N->real^(N,N)finite_prod) o
      (\y. matrix(frechet_derivative (chart_trans (c0:(A->bool)#(A->real^N)) c)
                                     (at ((tau:real^N->real^N) y)))) =
      (vectorize o (\z. matrix(frechet_derivative (chart_trans c0 c) (at z)))) o tau`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `IMAGE (SND(c0:(A->bool)#(A->real^N))) (FST c0 INTER FST (c:(A->bool)#(A->real^N)))` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER FST (c0:(A->bool)#(A->real^N)))` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MATCH_MP_TAC LRG_SMOOTH_JACOBIAN THEN ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `(\y. (V0:real^N->real^N) ((tau:real^N->real^N) y)) = V0 o tau`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `N0:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER FST (c0:(A->bool)#(A->real^N)))` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]]);;

(* The parallel equation transfers from the chart c0 to every chart c.     *)

let RFA_VREP_PARALLEL_FROM_CHART = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) c0 c N0 (V0:real^N->real^N) y z.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     c0 IN atlas /\ c IN atlas /\ open N0 /\ smooth_map_on N0 V0 /\
     (!y z. y IN N0
            ==> frechet_derivative V0 (at y) z +
                christoffel (metric_local atlas c0 g) y z (V0 y) = vec 0) /\
     y IN IMAGE (SND c) (FST c INTER {x | x IN FST c0 /\ SND c0 x IN N0})
     ==> frechet_derivative
           (mfd_vrep atlas (\x. chart_jac c0 (chart_at atlas x) x (V0 (SND c0 x))) c) (at y) z +
         christoffel (metric_local atlas c g) y z
           (mfd_vrep atlas (\x. chart_jac c0 (chart_at atlas x) x (V0 (SND c0 x))) c y) =
         vec 0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (LABEL_TAC "par0") ASSUME_TAC))))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c0:(A->bool)#(A->real^N)`; `c:(A->bool)#(A->real^N)`; `N0:real^N->bool`;
                 `V0:real^N->real^N`] RFA_VREP_SMOOTH_FROM_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `W = {x:A | x IN FST c0 /\ SND (c0:(A->bool)#(A->real^N)) x IN N0}` THEN
  ABBREV_TAC `O = IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER W)` THEN
  ABBREV_TAC `Z = mfd_vrep atlas (\x. chart_jac (c0:(A->bool)#(A->real^N))
                                       (chart_at atlas x) x ((V0:real^N->real^N) (SND c0 x)))
                       (c:(A->bool)#(A->real^N))` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `c0:(A->bool)#(A->real^N)`]
         GEOL_CHART_TRANS_FACTS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c0:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open_in top (W:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN MATCH_MP_TAC RFA_CHART_PREIMAGE_OPEN THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (O:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET];
    ALL_TAC] THEN
  ABBREV_TAC `tau = chart_trans (c:(A->bool)#(A->real^N)) c0` THEN
  SUBGOAL_THEN
   `!y. y IN O
        ==> chart_inv (c:(A->bool)#(A->real^N)) y IN FST c /\
            chart_inv c y IN FST (c0:(A->bool)#(A->real^N)) /\
            SND c (chart_inv c y) = y /\
            (tau:real^N->real^N) y = SND c0 (chart_inv c y) /\
            (tau:real^N->real^N) y IN N0 /\
            y IN IMAGE (SND c) (FST c INTER FST (c0:(A->bool)#(A->real^N)))`
  (LABEL_TAC "Ofacts") THENL
   [EXPAND_TAC "O" THEN REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:A) IN FST c0 /\ SND (c0:(A->bool)#(A->real^N)) x IN N0`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x:A) IN W` THEN EXPAND_TAC "W" THEN REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN EXPAND_TAC "tau" THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN O` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN EXPAND_TAC "W" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "Ofacts" (fun th -> MP_TAC(MP (SPEC `y:real^N` th) (ASSUME `(y:real^N) IN O`))) THEN
  STRIP_TAC THEN
  ABBREV_TAC `x = chart_inv (c:(A->bool)#(A->real^N)) y` THEN
  (* the relation D tau (Z w) = V0 (tau w) on O *)
  SUBGOAL_THEN
   `!w. w IN O ==> frechet_derivative (tau:real^N->real^N) (at w) ((Z:real^N->real^N) w) =
                   (V0:real^N->real^N) (tau w)`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    USE_THEN "Ofacts" (fun th -> MP_TAC(MP (SPEC `w:real^N` th) (ASSUME `(w:real^N) IN O`))) THEN
    ABBREV_TAC `xw = chart_inv (c:(A->bool)#(A->real^N)) w` THEN STRIP_TAC THEN
    SUBGOAL_THEN `frechet_derivative (tau:real^N->real^N) (at w) =
                  chart_jac (c:(A->bool)#(A->real^N)) c0 xw`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `xw:A` o check (fun th -> can (term_match []
        `!x:A. x IN FST (c:(A->bool)#(A->real^N)) INTER FST c0
               ==> ((tau:real^N->real^N) has_derivative chart_jac c c0 x) (at (SND c x))`)
        (concl th))) THEN
      ASM_REWRITE_TAC[IN_INTER];
      ALL_TAC] THEN
    SUBGOAL_THEN `(Z:real^N->real^N) w =
                  chart_jac (c0:(A->bool)#(A->real^N)) c xw ((V0:real^N->real^N) (SND c0 xw))`
    SUBST1_TAC THENL
     [EXPAND_TAC "Z" THEN
      UNDISCH_TAC `SND (c:(A->bool)#(A->real^N)) xw = w` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC RFA_VREP_FROM_CHART THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `xw:A`] CHART_JAC_INVERSE) THEN
    ASM_REWRITE_TAC[PAIR; IN_INTER] THEN
    DISCH_THEN(MP_TAC o C AP_THM `(V0:real^N->real^N) (SND (c0:(A->bool)#(A->real^N)) xw)`) THEN
    REWRITE_TAC[o_THM] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(tau:real^N->real^N) differentiable (at y) /\
                (Z:real^N->real^N) differentiable (at y) /\
                (V0:real^N->real^N) differentiable (at (tau y))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER FST (c0:(A->bool)#(A->real^N)))`;
      EXISTS_TAC `O:real^N->bool`;
      EXISTS_TAC `N0:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* differentiating the relation at y *)
  SUBGOAL_THEN `!w. w IN O ==> (tau:real^N->real^N) differentiable (at w)` ASSUME_TAC THENL
   [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER FST (c0:(A->bool)#(A->real^N)))` THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "Ofacts" (fun th -> MP_TAC(MP (SPEC `w:real^N` th) (ASSUME `(w:real^N) IN O`))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\w. frechet_derivative (tau:real^N->real^N) (at w) ((Z:real^N->real^N) w)) has_derivative
     (\u. frechet_derivative tau (at y) (frechet_derivative Z (at y) u) +
          frechet_derivative (\w. frechet_derivative tau (at w) (Z y)) (at y) u)) (at y)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\w:real^N. frechet_derivative (tau:real^N->real^N) (at w)`;
                   `Z:real^N->real^N`; `frechet_derivative (Z:real^N->real^N) (at y)`;
                   `O:real^N->bool`; `y:real^N`] LRG_HAS_DERIVATIVE_LINFAM) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN CONJ_TAC THENL
     [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      ASM_SIMP_TAC[];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c INTER FST (c0:(A->bool)#(A->real^N)))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(((V0:real^N->real^N) o (tau:real^N->real^N)) has_derivative
     (frechet_derivative V0 (at (tau y)) o frechet_derivative tau (at y))) (at y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. frechet_derivative (tau:real^N->real^N) (at y)
          (frechet_derivative (Z:real^N->real^N) (at y) u) +
        dd2 tau y u (Z y) =
        frechet_derivative (V0:real^N->real^N) (at (tau y)) (frechet_derivative tau (at y) u)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`\w. frechet_derivative (tau:real^N->real^N) (at w) ((Z:real^N->real^N) w)`;
      `(V0:real^N->real^N) o (tau:real^N->real^N)`;
      `\u. frechet_derivative (tau:real^N->real^N) (at y)
             (frechet_derivative (Z:real^N->real^N) (at y) u) +
           frechet_derivative (\w. frechet_derivative tau (at w) (Z y)) (at y) u`;
      `frechet_derivative (V0:real^N->real^N) (at ((tau:real^N->real^N) y)) o
       frechet_derivative tau (at y)`;
      `O:real^N->bool`; `y:real^N`] LRG_HAS_DERIVATIVE_UNIQUE_OPEN) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[o_THM]; ALL_TAC] THEN
    DISCH_THEN(fun th -> X_GEN_TAC `u:real^N` THEN MP_TAC(AP_THM th `u:real^N`)) THEN
    REWRITE_TAC[o_THM; dd2];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear (frechet_derivative (tau:real^N->real^N) (at y))` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "par0" (fun th -> MP_TAC(MP (SPECL [`(tau:real^N->real^N) y`;
    `frechet_derivative (tau:real^N->real^N) (at y) z`] th)
    (ASSUME `(tau:real^N->real^N) y IN N0`))) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `c:(A->bool)#(A->real^N)`; `c0:(A->bool)#(A->real^N)`; `x:A`; `z:real^N`;
                 `(Z:real^N->real^N) y`] GEOC_CHRISTOFFEL_TRANS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `chart_trans (c:(A->bool)#(A->real^N)) c0 = tau`;
              ASSUME `SND (c:(A->bool)#(A->real^N)) x = y`;
              SYM(ASSUME `(tau:real^N->real^N) y = SND (c0:(A->bool)#(A->real^N)) x`)] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `frechet_derivative (tau:real^N->real^N) (at y) ((Z:real^N->real^N) y) =
                (V0:real^N->real^N) (tau y)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (tau:real^N->real^N) (at y)
      (frechet_derivative (Z:real^N->real^N) (at y) z +
       christoffel (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)) y z (Z y)) =
    vec 0`
  MP_TAC THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N` o check (fun th -> can (term_match []
      `!u. frechet_derivative (tau:real^N->real^N) (at y)
             (frechet_derivative (Z:real^N->real^N) (at y) u) + dd2 tau y u (Z y) =
           frechet_derivative (V0:real^N->real^N) (at (tau y))
             (frechet_derivative tau (at y) u)`) (concl th))) THEN
    UNDISCH_TAC
     `frechet_derivative (tau:real^N->real^N) (at y)
        (christoffel (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)) y z
                     ((Z:real^N->real^N) y)) =
      christoffel (metric_local atlas c0 g) (tau y) (frechet_derivative tau (at y) z)
        (frechet_derivative tau (at y) (Z y)) +
      dd2 tau y z (Z y)` THEN
    REWRITE_TAC[ASSUME `frechet_derivative (tau:real^N->real^N) (at y) ((Z:real^N->real^N) y) =
                        (V0:real^N->real^N) (tau y)`] THEN
    UNDISCH_TAC
     `frechet_derivative (V0:real^N->real^N) (at ((tau:real^N->real^N) y))
        (frechet_derivative tau (at y) z) +
      christoffel (metric_local atlas (c0:(A->bool)#(A->real^N)) (g:A->real^N^N)) (tau y)
        (frechet_derivative tau (at y) z) (V0 (tau y)) = vec 0` THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `frechet_derivative (tau:real^N->real^N) (at y) =
                chart_jac (c:(A->bool)#(A->real^N)) c0 x`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o check (fun th -> can (term_match []
      `!x:A. x IN FST (c:(A->bool)#(A->real^N)) INTER FST c0
             ==> ((tau:real^N->real^N) has_derivative chart_jac c c0 x) (at (SND c x))`)
      (concl th))) THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                 `x:A`] CHART_JAC_INVERSE) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `x:A`] CHART_JAC_LINEAR) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER] THEN DISCH_TAC THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o AP_TERM `chart_jac (c0:(A->bool)#(A->real^N)) c x`) THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[REWRITE_RULE[FUN_EQ_THM; o_THM] th]) THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_0 th]));;

(* Unit length transfers from the chart c0 to preferred coordinates, and   *)
(* the packaged result: a parallel unit field on W in the sense of          *)
(* p2b_parallel_on.                                                         *)

let RFA_VFIELD_UNIT_FROM_CHART = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) c0 (V0:real^N->real^N) x.
     smooth_manifold_atlas top atlas /\ c0 IN atlas /\ x IN FST c0 /\
     V0 (SND c0 x) dot (metric_local atlas c0 g (SND c0 x) ** V0 (SND c0 x)) = &1
     ==> chart_jac c0 (chart_at atlas x) x (V0 (SND c0 x)) dot
         (g x ** chart_jac c0 (chart_at atlas x) x (V0 (SND c0 x))) = &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c0:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `p = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  UNDISCH_TAC `(V0:real^N->real^N) (SND (c0:(A->bool)#(A->real^N)) x) dot
               (metric_local atlas c0 (g:A->real^N^N) (SND c0 x) ** V0 (SND c0 x)) = &1` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                 `FST(p:(A->bool)#(A->real^N))`; `SND(p:(A->bool)#(A->real^N))`;
                 `g:A->real^N^N`; `x:A`] METRIC_LOCAL_TRANS) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[mpullback] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                 `FST(p:(A->bool)#(A->real^N))`; `SND(p:(A->bool)#(A->real^N))`;
                 `x:A`] CHART_TRANS_AT) THEN
  ASM_REWRITE_TAC[PAIR] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                 `FST(p:(A->bool)#(A->real^N))`; `SND(p:(A->bool)#(A->real^N))`;
                 `x:A`] CHART_JAC_LINEAR) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM chart_jac] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  REWRITE_TAC[DOT_MATRIX_TRANSP_RMUL] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MATRIX_WORKS th]));;

let RFA_PARALLEL_ON_FROM_CHART = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) c0 N0 (V0:real^N->real^N).
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ c0 IN atlas /\
     open N0 /\ N0 SUBSET IMAGE (SND c0) (FST c0) /\ smooth_map_on N0 V0 /\
     (!y z. y IN N0
            ==> frechet_derivative V0 (at y) z +
                christoffel (metric_local atlas c0 g) y z (V0 y) = vec 0) /\
     (!y. y IN N0 ==> V0 y dot (metric_local atlas c0 g y ** V0 y) = &1)
     ==> open_in top {x | x IN FST c0 /\ SND c0 x IN N0} /\
         p2b_parallel_on atlas g {x | x IN FST c0 /\ SND c0 x IN N0}
           (\x. chart_jac c0 (chart_at atlas x) x (V0 (SND c0 x))) /\
         (!x. x IN {x | x IN FST c0 /\ SND c0 x IN N0}
              ==> (\x. chart_jac c0 (chart_at atlas x) x (V0 (SND c0 x))) x dot
                  (g x ** (\x. chart_jac c0 (chart_at atlas x) x (V0 (SND c0 x))) x) = &1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RFA_CHART_PREIMAGE_OPEN THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[p2b_parallel_on] THEN CONJ_TAC THENL
     [X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
      MATCH_MP_TAC RFA_VREP_SMOOTH_FROM_CHART THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^N)`; `y:real^N`; `z:real^N`] THEN
      STRIP_TAC THEN MATCH_MP_TAC RFA_VREP_PARALLEL_FROM_CHART THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `N0:real^N->bool`] THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    MATCH_MP_TAC RFA_VFIELD_UNIT_FROM_CHART THEN EXISTS_TAC `top:A topology` THEN
    ASM_SIMP_TAC[]]);;


(* ========================================================================= *)
(* Flatness at a point and local splitting at an interior time.              *)
(* ========================================================================= *)

(* Flat at a point: lambda >= 0 and R = 0 give vanishing sectional          *)
(* curvatures (P >= 0 with trace R/2 = 0).                                  *)

let RFA_FLAT_POINT = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) x u v.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top /\
     &0 <= mfd_sec_min atlas g x /\ mfd_scalar atlas g x = &0 /\ ~collinear {vec 0,u,v}
     ==> mfd_sectional atlas g x u v = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)`;
                 `x:A`] RFA_SECMIN_CHART_3D) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)` THEN
  ABBREV_TAC `G = metric_local atlas (c:(A->bool)#(A->real^3)) (g:A->real^3^3)` THEN
  ABBREV_TAC `y = SND (c:(A->bool)#(A->real^3)) x` THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c))
                             (G:real^3->real^3^3) /\
                (y:real^3) IN IMAGE (SND c) (FST c)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "G" THEN
      UNDISCH_TAC `riemannian_metric atlas (g:A->real^3^3)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "y" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)`; `G:real^3->real^3^3`;
                 `y:real^3`; `S:real^3^3`] RFA_P3_FRAME_SCALARS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `lscalar (G:real^3->real^3^3) y = &0` SUBST1_TAC THENL
   [UNDISCH_TAC `mfd_scalar atlas (g:A->real^3^3) x = &0` THEN
    REWRITE_TAC[mfd_scalar] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  ABBREV_TAC `p1 = lpcurv (G:real^3->real^3^3) y (\m. transp(S:real^3^3) ** basis 1)` THEN
  ABBREV_TAC `p2 = lpcurv (G:real^3->real^3^3) y (\m. transp(S:real^3^3) ** basis 2)` THEN
  ABBREV_TAC `p3 = lpcurv (G:real^3->real^3^3) y (\m. transp(S:real^3^3) ** basis 3)` THEN
  SUBGOAL_THEN `p1 = &0 /\ p2 = &0 /\ p3 = &0` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `&0 <= mfd_sec_min atlas (g:A->real^3^3) x` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[mfd_sectional] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)`; `G:real^3->real^3^3`;
                 `y:real^3`; `u:real^3`; `v:real^3`] RFA_SEC_AS_PCURV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)`; `G:real^3->real^3^3`;
                 `y:real^3`; `S:real^3^3`; `w:real^3`; `w:real^3`] RFA_FRAME3_P) THEN
  ASM_REWRITE_TAC[COND_ID] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

(* Smoothness of the normalization of a nonvanishing smooth field. *)

let RFA_GNORMALIZE_SMOOTH = prove
 (`!U (G:real^N->real^N^N) (Y:real^N->real^N).
     metric_field U G /\ smooth_map_on U Y /\ (!y. y IN U ==> ~(Y y = vec 0))
     ==> smooth_map_on U (\y. inv(sqrt(Y y dot (G y ** Y y))) % Y y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN U ==> &0 < (Y:real^N->real^N) y dot ((G:real^N->real^N^N) y ** Y y)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LRG_METRIC_POS THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`;
    `\y. lift(inv(sqrt((Y:real^N->real^N) y dot ((G:real^N->real^N^N) y ** Y y))))`;
    `Y:real^N->real^N`] SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`U:real^N->bool`;
    `\y. lift(sqrt((Y:real^N->real^N) y dot ((G:real^N->real^N^N) y ** Y y)))`]
    SMOOTH_MAP_ON_LIFT_INV) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`;
      `\y. lift((Y:real^N->real^N) y dot ((G:real^N->real^N^N) y ** Y y))`]
      SMOOTH_MAP_ON_LIFT_SQRT) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LRG_SMOOTH_MATVEC THEN ASM_REWRITE_TAC[ETA_AX] THEN
    ASM_MESON_TAC[metric_field];
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x = &0)`) THEN
    MATCH_MP_TAC SQRT_POS_LT THEN ASM_SIMP_TAC[]]);;

(* Locally split at an interior time where lambda = 0, lambda >= 0 before, *)
(* and R > 0 everywhere.                                                    *)

let RFA_SPLIT_AT_TIME = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3) t0.
     ricci_flow_on (top,atlas) a b g /\ a < t0 /\ t0 < b /\
     (!t x. a < t /\ t <= t0 /\ x IN topspace top ==> &0 <= mfd_sec_min atlas (g t) x) /\
     (!x. x IN topspace top ==> mfd_sec_min atlas (g t0) x = &0) /\
     (!x. x IN topspace top ==> &0 < mfd_scalar atlas (g t0) x)
     ==> p2b_locally_split (top,atlas) (g t0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[p2b_locally_split] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) /\
                riemannian_metric atlas ((g:real->A->real^3^3) t0)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(g:real->A->real^3^3) t0`; `chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)`;
                 `x:A`] RFA_SECMIN_CHART_3D) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < mfd_scalar atlas ((g:real->A->real^3^3) t0) x` MP_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[mfd_scalar] THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)` THEN
  ABBREV_TAC `G = metric_local atlas (c0:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)` THEN
  ABBREV_TAC `y1 = SND (c0:(A->bool)#(A->real^3)) x` THEN
  ABBREV_TAC `V = IMAGE (SND (c0:(A->bool)#(A->real^3))) (FST c0)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `metric_field V (G:real^3->real^3^3) /\ (y1:real^3) IN V` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["V"; "G"; "y1"] THEN CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas ((g:real->A->real^3^3) t0)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?b0:real^3. &0 < lpcurv (G:real^3->real^3^3) y1 (\m. b0)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:real^3->bool`; `G:real^3->real^3^3`; `y1:real^3`; `S:real^3^3`]
           RFA_P3_FRAME_SCALARS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_CASES_TAC `&0 < lpcurv (G:real^3->real^3^3) y1 (\m. transp(S:real^3^3) ** basis 1)` THENL
     [EXISTS_TAC `transp(S:real^3^3) ** basis 1` THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `&0 < lpcurv (G:real^3->real^3^3) y1 (\m. transp(S:real^3^3) ** basis 2)` THENL
     [EXISTS_TAC `transp(S:real^3^3) ** basis 2` THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    EXISTS_TAC `transp(S:real^3^3) ** basis 3` THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `N0 = {y:real^3 | y IN V /\ &0 < lpcurv (G:real^3->real^3^3) y (\m. b0)}` THEN
  SUBGOAL_THEN `open (N0:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "N0" THEN
    SUBGOAL_THEN
     `{y:real^3 | y IN V /\ &0 < lpcurv (G:real^3->real^3^3) y (\m. b0)} =
      {y | y IN V /\ (\y. lift(lpcurv G y (\m. b0))) y IN {x:real^1 | x$1 > &0}}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; GSYM drop; LIFT_DROP; real_gt]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      MP_TAC(ISPECL [`V:real^3->bool`; `G:real^3->real^3^3`] RFA_LPCURV_FIELD) THEN
      ASM_SIMP_TAC[];
      ASM_MESON_TAC[metric_field]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(N0:real^3->bool) SUBSET V /\ (y1:real^3) IN N0 /\
                (!y. y IN N0 ==> &0 < lpcurv (G:real^3->real^3^3) y (\m. b0))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "N0" THEN REWRITE_TAC[IN_ELIM_THM; SUBSET] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field N0 (G:real^3->real^3^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `V:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `Yf = \w. matrix_inv((G:real^3->real^3^3) w) **
             ((lambda k. lpcurv G w (\m. if m = 1 then b0 else basis k)):real^3)` THEN
  SUBGOAL_THEN `smooth_map_on N0 (Yf:real^3->real^3) /\
                (!w. w IN N0 ==> ~((Yf:real^3->real^3) w = vec 0))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `V:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "Yf" THEN MATCH_MP_TAC RFA_PFIELD_SMOOTH THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`V:real^3->bool`; `G:real^3->real^3^3`; `w:real^3`; `b0:real^3`;
                     `b0:real^3`] RFA_PFIELD_DOT) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      UNDISCH_TAC `(Yf:real^3->real^3) w = vec 0` THEN EXPAND_TAC "Yf" THEN
      REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DOT_LZERO; COND_ID] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(&0 = x)`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `V0 = \w. inv(sqrt((Yf:real^3->real^3) w dot ((G:real^3->real^3^3) w ** Yf w))) %
                       Yf w` THEN
  SUBGOAL_THEN
   `smooth_map_on N0 (V0:real^3->real^3) /\
    (!y. y IN N0 ==> (V0:real^3->real^3) y dot ((G:real^3->real^3^3) y ** V0 y) = &1) /\
    (!y z. y IN N0
           ==> frechet_derivative (V0:real^3->real^3) (at y) z +
               christoffel (G:real^3->real^3^3) y z (V0 y) = vec 0)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "V0" THEN MATCH_MP_TAC RFA_GNORMALIZE_SMOOTH THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN EXPAND_TAC "V0" THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC RFA_GNORM_UNIT THEN EXISTS_TAC `N0:real^3->bool` THEN ASM_SIMP_TAC[];
      MAP_EVERY X_GEN_TAC [`y:real^3`; `z:real^3`] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                     `b:real`; `g:real->A->real^3^3`; `c0:(A->bool)#(A->real^3)`; `t0:real`;
                     `N0:real^3->bool`; `b0:real^3`; `y:real^3`; `z:real^3`]
             RFA_PARALLEL_CHART) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [UNDISCH_TAC `(N0:real^3->bool) SUBSET V` THEN EXPAND_TAC "V" THEN SIMP_TAC[];
          ASM_SIMP_TAC[]];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[lcovd] THEN
      SUBGOAL_THEN
       `(\w. inv(sqrt((matrix_inv((G:real^3->real^3^3) w) **
                      ((lambda k. lpcurv G w (\m. if m = 1 then b0 else basis k)):real^3)) dot
                     (G w ** (matrix_inv(G w) **
                      ((lambda k. lpcurv G w (\m. if m = 1 then b0 else basis k)):real^3))))) %
             (matrix_inv(G w) **
              ((lambda k. lpcurv G w (\m. if m = 1 then b0 else basis k)):real^3))) =
        (V0:real^3->real^3)`
      (fun th -> REWRITE_TAC[th]) THEN
      MAP_EVERY EXPAND_TAC ["V0"; "Yf"] THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(g:real->A->real^3^3) t0`; `c0:(A->bool)#(A->real^3)`; `N0:real^3->bool`;
                 `V0:real^3->real^3`] RFA_PARALLEL_ON_FROM_CHART) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(N0:real^3->bool) SUBSET V` THEN EXPAND_TAC "V" THEN SIMP_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`{x:A | x IN FST c0 /\ SND (c0:(A->bool)#(A->real^3)) x IN N0}`;
    `\x. chart_jac (c0:(A->bool)#(A->real^3)) (chart_at atlas x) x
                   ((V0:real^3->real^3) (SND c0 x))`] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]);;


(* ========================================================================= *)
(* The strong maximum principle for lambda and for R at                      *)
(* interior times, the per-time dichotomy and the split statement for       *)
(* t1 < b.                                                                  *)
(* ========================================================================= *)

(* Positivity at (t1,x) of a function jointly continuous on [a,b) x M      *)
(* persists slightly earlier.                                               *)

let RFA_POS_BEFORE = prove
 (`!(top:A topology) (f:real->A->real) a b t1 x.
     a < t1 /\ t1 < b /\ x IN topspace top /\
     continuous_map
       (prod_topology (subtopology euclideanreal {t | a <= t /\ t < b})
                      (subtopology top (topspace top)),
        euclideanreal) (\z. f (FST z) (SND z)) /\
     &0 < f t1 x
     ==> ?s. a < s /\ s < t1 /\ &0 < f s x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\s. (f:real->A->real) s x) real_continuous_on {s | a <= s /\ s < b}`
  MP_TAC THENL
   [REWRITE_TAC[RFA_REAL_CONTINUOUS_ON_EQ_CONTINUOUS_MAP] THEN
    MP_TAC(BETA_RULE(ISPECL
      [`subtopology euclideanreal {t | a <= t /\ t < b}`;
       `subtopology (top:A topology) (topspace top)`;
       `f:real->A->real`; `x:A`] RFA_SLICE_CONTINUOUS_LEFT)) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER];
    ALL_TAC] THEN
  REWRITE_TAC[real_continuous_on; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `t1:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `(f:real->A->real) t1 x / &2`) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t1 - min d (t1 - a) / &2` THEN
  REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t1 - min d (t1 - a) / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

(* lambda = 0 at (t1,p) forces lambda = 0 on (a,t1] x M (strong maximum   *)
(* principle for lambda, interior time t1).                                  *)

let RFA_SECMIN_ZERO_BEFORE = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3) t1 p.
     ricci_flow_on (top,atlas) a b g /\ connected_space top /\
     (!t x. a < t /\ t < b /\ x IN topspace top ==> &0 <= mfd_sec_min atlas (g t) x) /\
     a < t1 /\ t1 < b /\ p IN topspace top /\ mfd_sec_min atlas (g t1) p = &0
     ==> !t x. a < t /\ t <= t1 /\ x IN topspace top ==> mfd_sec_min atlas (g t) x = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(&0 < mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
                         ((g:real->A->real^3^3) t) x)`
  MP_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `?s. a < s /\ s < t1 /\ &0 < mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
                                                  ((g:real->A->real^3^3) s) x`
    STRIP_ASSUME_TAC THENL
     [ASM_CASES_TAC `t:real = t1` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN
        MP_TAC(ISPECL [`top:A topology`;
                       `\t x. mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
                                ((g:real->A->real^3^3) t) (x:A)`;
                       `(a + t1) / &2`; `b:real`; `t1:real`; `x:A`] RFA_POS_BEFORE) THEN
        REWRITE_TAC[] THEN ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          MATCH_MP_TAC RFA_SECMIN_CONTINUOUS_GEN THEN REPEAT CONJ_TAC THENL
           [ASM_MESON_TAC[ricci_flow_on];
            REPEAT STRIP_TAC THEN
            UNDISCH_TAC `ricci_flow_on (top,atlas) a b (g:real->A->real^3^3)` THEN
            REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
            ASM_REAL_ARITH_TAC;
            MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                           `a:real`; `b:real`; `g:real->A->real^3^3`; `(a + t1) / &2`]
                   RFA_RICCI_FLOW_ON_EXT) THEN
            ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
          DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
          EXISTS_TAC `s:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
        EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                   `b:real`; `g:real->A->real^3^3`; `s:real`; `x:A`] RFA_SECMIN_STRONG) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`t1:real`; `p:A`]) THEN ASM_REWRITE_TAC[REAL_LT_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real`; `x:A`] (ASSUME
    `!t x. a < t /\ t < b /\ x IN topspace top
           ==> &0 <= mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
                                 ((g:real->A->real^3^3) t) x`)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* The strong maximum principle for R >= 0 along a 3D Ricci flow with      *)
(* sec >= 0 (RFA_STRONG_MAXP_SCALAR with c = 0).                           *)

let RFA_SCALAR_STRONG_SEC = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3) t0 x0.
     hausdorff_space top /\ connected_space top /\ ricci_flow_on (top,atlas) a b g /\
     (!t x. a < t /\ t < b /\ x IN topspace top ==> &0 <= mfd_sec_min atlas (g t) x) /\
     a < t0 /\ t0 < b /\ x0 IN topspace top /\ &0 < mfd_scalar atlas (g t0) x0
     ==> !t x. t0 < t /\ t < b /\ x IN topspace top ==> &0 < mfd_scalar atlas (g t) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) /\
                a < b /\ (!t. a < t /\ t < b ==> riemannian_metric atlas ((g:real->A->real^3^3) t))`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`u:A->bool`; `n:3->bool`] RFA_STRONG_MAXP_SCALAR) THEN
  REWRITE_TAC[RFA_STRONG_MAXP_SCALAR_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL
    [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
     `g:real->A->real^3^3`;
     `\t x. mfd_scalar (atlas:((A->bool)#(A->real^3))->bool) ((g:real->A->real^3^3) t) (x:A)`;
     `\t:real x:A. &0`; `t0:real`; `x0:A`]) THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID; ETA_AX] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `cc:(A->bool)#(A->real^3)` THEN DISCH_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `ricci_flow_on (top,atlas) a b (g:real->A->real^3^3)` THEN
      REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                     `b:real`; `g:real->A->real^3^3`; `cc:(A->bool)#(A->real^3)`]
             RFA_MFD_SCALAR_CHART_SMOOTH) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `FST cc INTER topspace top = FST (cc:(A->bool)#(A->real^3))`
      SUBST1_TAC THENL
       [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `cc:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1) THEN
        SET_TAC[];
        SIMP_TAC[]]];
    REPEAT STRIP_TAC THEN EXISTS_TAC `&0` THEN REWRITE_TAC[REAL_ABS_NUM; REAL_LE_REFL];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&6 * mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
                                ((g:real->A->real^3^3) t) x` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC RFA_SCALAR_GE_6SECMIN THEN EXISTS_TAC `top:A topology` THEN
      ASM_SIMP_TAC[]];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                   `b:real`; `g:real->A->real^3^3`; `t:real`; `x:A`]
           RFA_MFD_SCALAR_EVOLUTION) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    EXISTS_TAC
     `rfa_lap atlas ((g:real->A->real^3^3) t) (mfd_scalar atlas (g t)) x +
      &2 * ltnorm2 2 (metric_local atlas (chart_at atlas x) (g t))
                     (lric2 (metric_local atlas (chart_at atlas x) (g t)))
                     (SND(chart_at atlas (x:A)) x)` THEN
    ASM_REWRITE_TAC[REAL_LE_ADDR] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC LTNORM2_POS THEN
    EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                      (FST(chart_at atlas x))` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`]
           CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `metric_field (IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                          (FST(chart_at atlas x)))
                   (metric_local atlas (chart_at atlas x) ((g:real->A->real^3^3) t))`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `riemannian_metric (atlas:((A->bool)#(A->real^3))->bool)
                                      ((g:real->A->real^3^3) t)` MP_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[LRG_LRIC2_FIELD; FUN_IN_IMAGE]]);;

(* R = 0 at (t1,p) forces R = 0 on (a,t1] x M (interior t1, sec >= 0).     *)

let RFA_SCALAR_ZERO_BEFORE = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3) t1 p.
     hausdorff_space top /\ connected_space top /\ ricci_flow_on (top,atlas) a b g /\
     (!t x. a < t /\ t < b /\ x IN topspace top ==> &0 <= mfd_sec_min atlas (g t) x) /\
     a < t1 /\ t1 < b /\ p IN topspace top /\ mfd_scalar atlas (g t1) p = &0
     ==> !t x. a < t /\ t <= t1 /\ x IN topspace top ==> mfd_scalar atlas (g t) x = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) /\
                (!t. a < t /\ t < b ==> riemannian_metric atlas ((g:real->A->real^3^3) t))`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  SUBGOAL_THEN `!t x. a < t /\ t < b /\ x IN topspace top
                      ==> &0 <= mfd_scalar (atlas:((A->bool)#(A->real^3))->bool)
                                           ((g:real->A->real^3^3) t) x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&6 * mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
                                ((g:real->A->real^3^3) t) x` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC RFA_SCALAR_GE_6SECMIN THEN EXISTS_TAC `top:A topology` THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(&0 < mfd_scalar (atlas:((A->bool)#(A->real^3))->bool)
                         ((g:real->A->real^3^3) t) x)`
  MP_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `?s. a < s /\ s < t1 /\ &0 < mfd_scalar (atlas:((A->bool)#(A->real^3))->bool)
                                                 ((g:real->A->real^3^3) s) x`
    STRIP_ASSUME_TAC THENL
     [ASM_CASES_TAC `t:real = t1` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN
        MP_TAC(ISPECL [`top:A topology`;
                       `\t x. mfd_scalar (atlas:((A->bool)#(A->real^3))->bool)
                                ((g:real->A->real^3^3) t) (x:A)`;
                       `(a + t1) / &2`; `b:real`; `t1:real`; `x:A`] RFA_POS_BEFORE) THEN
        REWRITE_TAC[] THEN ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          MATCH_MP_TAC RFA_MFD_SCALAR_CONTINUOUS_GEN THEN REPEAT CONJ_TAC THENL
           [FIRST_ASSUM ACCEPT_TAC;
            REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
            MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                           `a:real`; `b:real`; `g:real->A->real^3^3`; `(a + t1) / &2`]
                   RFA_RICCI_FLOW_ON_EXT) THEN
            ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
          DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
          EXISTS_TAC `s:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
        EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                   `b:real`; `g:real->A->real^3^3`; `s:real`; `x:A`] RFA_SCALAR_STRONG_SEC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`t1:real`; `p:A`]) THEN ASM_REWRITE_TAC[REAL_LT_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real`; `x:A`] (ASSUME
    `!t x. a < t /\ t < b /\ x IN topspace top
           ==> &0 <= mfd_scalar (atlas:((A->bool)#(A->real^3))->bool)
                                ((g:real->A->real^3^3) t) x`)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* The per-time dichotomy at an interior time where lambda = 0 everywhere: *)
(* flat, or (R > 0 somewhere, hence everywhere) locally split.              *)

let RFA_DICHOTOMY_AT_TIME = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3) t.
     hausdorff_space top /\ connected_space top /\ ricci_flow_on (top,atlas) a b g /\
     (!t x. a < t /\ t < b /\ x IN topspace top ==> &0 <= mfd_sec_min atlas (g t) x) /\
     a < t /\ t < b /\
     (!x. x IN topspace top ==> mfd_sec_min atlas (g t) x = &0)
     ==> (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                  ==> mfd_sectional atlas (g t) x u v = &0) \/
         p2b_locally_split (top,atlas) (g t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) /\
                (!t. a < t /\ t < b ==> riemannian_metric atlas ((g:real->A->real^3^3) t))`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  ASM_CASES_TAC `!x. x IN topspace top
                     ==> mfd_scalar (atlas:((A->bool)#(A->real^3))->bool)
                                    ((g:real->A->real^3^3) t) x = &0` THENL
   [DISJ1_TAC THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_FLAT_POINT THEN
    EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  DISJ2_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
  REWRITE_TAC[NOT_IMP] THEN DISCH_THEN(X_CHOOSE_THEN `x0:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < mfd_scalar (atlas:((A->bool)#(A->real^3))->bool)
                                ((g:real->A->real^3^3) t) x0`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(x = &0) ==> &0 < x`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&6 * mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
                                ((g:real->A->real^3^3) t) x0` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC RFA_SCALAR_GE_6SECMIN THEN EXISTS_TAC `top:A topology` THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`;
                 `\t x. mfd_scalar (atlas:((A->bool)#(A->real^3))->bool)
                          ((g:real->A->real^3^3) t) (x:A)`;
                 `(a + t) / &2`; `b:real`; `t:real`; `x0:A`] RFA_POS_BEFORE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC RFA_MFD_SCALAR_CONTINUOUS_GEN THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                     `a:real`; `b:real`; `g:real->A->real^3^3`; `(a + t) / &2`]
             RFA_RICCI_FLOW_ON_EXT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                 `b:real`; `g:real->A->real^3^3`; `s:real`; `x0:A`] RFA_SCALAR_STRONG_SEC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MATCH_MP_TAC RFA_SPLIT_AT_TIME THEN
  MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

(* The split statement for an interior time t1 < b: the per-time dichotomy *)
(* after a zero plane at (p,t1), and flatness up to t1 if R(t1,p) = 0.      *)

let RFA_SPLIT_PT_INTERIOR = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3) p t1.
     hausdorff_space top /\ connected_space top /\ ricci_flow_on (top,atlas) a b g /\
     (!t x u v. a < t /\ t < b /\ x IN topspace top /\ ~collinear {vec 0,u,v}
                ==> &0 <= mfd_sectional atlas (g t) x u v) /\
     a < t1 /\ t1 < b /\ p IN topspace top
     ==> (!u1 v1. ~collinear {vec 0,u1,v1} /\ mfd_sectional atlas (g t1) p u1 v1 = &0
                  ==> !t. a < t /\ t <= t1
                          ==> (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                                       ==> mfd_sectional atlas (g t) x u v = &0) \/
                              p2b_locally_split (top,atlas) (g t)) /\
         (mfd_scalar atlas (g t1) p = &0
          ==> !t x u v. a < t /\ t <= t1 /\ x IN topspace top /\ ~collinear {vec 0,u,v}
                        ==> mfd_sectional atlas (g t) x u v = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) /\
                (!t. a < t /\ t < b ==> riemannian_metric atlas ((g:real->A->real^3^3) t))`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  SUBGOAL_THEN `!t x. a < t /\ t < b /\ x IN topspace top
                      ==> &0 <= mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
                                            ((g:real->A->real^3^3) t) x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_SECMIN_NONNEG THEN
    REWRITE_TAC[DIMINDEX_3; ARITH] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`u1:real^3`; `v1:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
                              ((g:real->A->real^3^3) t1) p = &0`
    ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &0 ==> x = &0`) THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> can (term_match []
          `mfd_sectional (atlas:((A->bool)#(A->real^3))->bool) ((g:real->A->real^3^3) t1)
                         p u1 v1 = &0`) (concl th))) THEN
        MATCH_MP_TAC RFA_SEC_GE_SECMIN THEN EXISTS_TAC `top:A topology` THEN
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                   `b:real`; `g:real->A->real^3^3`; `t1:real`; `p:A`]
           RFA_SECMIN_ZERO_BEFORE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC RFA_DICHOTOMY_AT_TIME THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                 `b:real`; `g:real->A->real^3^3`; `t1:real`; `p:A`]
         RFA_SCALAR_ZERO_BEFORE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_FLAT_POINT THEN
  EXISTS_TAC `top:A topology` THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM ACCEPT_TAC]);;


