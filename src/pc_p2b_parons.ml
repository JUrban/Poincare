(* ========================================================================= *)
(* pc_p2b_parons: congruence, locality and scalar multiples of               *)
(* p2b_parallel_on (pc_p2b_splitreq): P2BPF_PARALLEL_ON_EQ,                  *)
(* P2BPF_PARALLEL_ON_LOCAL, P2BPF_PARALLEL_CMUL.  A separate unit so that    *)
(* pc_p2b_x1 and pc_p2b_sround can use them without pc_p2b_parfield.         *)
(* ========================================================================= *)

needs "src/pc_p2b_splitreq.ml";;
needs "src/pc_mfd_maps.ml";;
needs "src/pc_mfd_riem.ml";;
needs "src/pc_lrg.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The three lemmas.                                                         *)
(* ========================================================================= *)

let P2BPF_PARALLEL_ON_EQ = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) g W (X:A->real^N) X'.
     smooth_manifold_atlas top atlas /\ open_in top W /\ (!y. y IN W ==> X' y = X y) /\
     p2b_parallel_on atlas g W X
     ==> p2b_parallel_on atlas g W X'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2b_parallel_on] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!c. c IN atlas
        ==> open (IMAGE (SND c) (FST c INTER W)) /\
            !u. u IN IMAGE (SND c) (FST c INTER W)
                ==> mfd_vrep atlas (X':A->real^N) c u = mfd_vrep atlas X c u`
  ASSUME_TAC THENL
   [X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                     `FST(c:(A->bool)#(A->real^N)) INTER (W:A->bool)`] CHART_IMAGE_OPEN) THEN
      ASM_REWRITE_TAC[PAIR; INTER_SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[mfd_vrep]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `mfd_vrep atlas (X:A->real^N) c` THEN
    ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^N)`; `u:real^N`; `z:real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `frechet_derivative (mfd_vrep atlas (X':A->real^N) c) (at u) =
                  frechet_derivative (mfd_vrep atlas X c) (at u)` SUBST1_TAC THENL
     [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
      EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER W)` THEN ASM_SIMP_TAC[];
      ASM_SIMP_TAC[]]]);;

let P2BPF_PARALLEL_ON_LOCAL = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) g W (X:A->real^N).
     smooth_manifold_atlas top atlas /\ open_in top W /\
     (!x. x IN W ==> ?W'. open_in top W' /\ x IN W' /\ W' SUBSET W /\ p2b_parallel_on atlas g W' X)
     ==> p2b_parallel_on atlas g W X`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[p2b_parallel_on] THEN CONJ_TAC THENL
   [X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                     `FST(c:(A->bool)#(A->real^N)) INTER (W:A->bool)`] CHART_IMAGE_OPEN) THEN
      ASM_REWRITE_TAC[PAIR; INTER_SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MFDM_CHART];
      ALL_TAC] THEN
    X_GEN_TAC `u0:real^N` THEN REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `x0:A` (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x0:A`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `W':A->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER W')` THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                     `FST(c:(A->bool)#(A->real^N)) INTER (W':A->bool)`] CHART_IMAGE_OPEN) THEN
      ASM_REWRITE_TAC[PAIR; INTER_SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MFDM_CHART];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
      UNDISCH_TAC `p2b_parallel_on atlas (g:A->real^N^N) W' (X:A->real^N)` THEN
      REWRITE_TAC[p2b_parallel_on] THEN ASM_MESON_TAC[]];
    MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^N)`; `u0:real^N`; `z:real^N`] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `x0:A` (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC))) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x0:A`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `W':A->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `p2b_parallel_on atlas (g:A->real^N^N) W' (X:A->real^N)` THEN
    REWRITE_TAC[p2b_parallel_on] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]]);;

let P2BPF_PARALLEL_CMUL = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) g W (X:A->real^N) a.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ open_in top W /\
     p2b_parallel_on atlas g W X
     ==> p2b_parallel_on atlas g W (\y. a % X y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2b_parallel_on] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!c. c IN atlas
        ==> open (IMAGE (SND c) (FST c INTER W)) /\
            !u. u IN IMAGE (SND c) (FST c INTER W)
                ==> mfd_vrep atlas (\y. a % (X:A->real^N) y) c u = a % mfd_vrep atlas X c u`
  ASSUME_TAC THENL
   [X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                     `FST(c:(A->bool)#(A->real^N)) INTER (W:A->bool)`] CHART_IMAGE_OPEN) THEN
      ASM_REWRITE_TAC[PAIR; INTER_SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MFDM_CHART];
      X_GEN_TAC `u:real^N` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `u IN IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` ASSUME_TAC THENL
       [UNDISCH_TAC `u IN IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER W)` THEN SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) u IN FST c /\
                    chart_inv c u IN topspace top` STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC[] THEN ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `chart_inv (c:(A->bool)#(A->real^N)) u`] CHART_AT) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool)
                           (chart_inv (c:(A->bool)#(A->real^N)) u))`;
                     `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool)
                           (chart_inv (c:(A->bool)#(A->real^N)) u))`;
                     `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                     `chart_inv (c:(A->bool)#(A->real^N)) u`] CHART_JAC_LINEAR) THEN
      ASM_REWRITE_TAC[PAIR; IN_INTER] THEN DISCH_TAC THEN
      ASM_SIMP_TAC[mfd_vrep; LINEAR_CMUL]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `\u. a % mfd_vrep atlas (X:A->real^N) c u` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_SIMP_TAC[ETA_AX]];
    MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^N)`; `u:real^N`; `z:real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `frechet_derivative (mfd_vrep atlas (\y. a % (X:A->real^N) y) c) (at u) z =
                  a % frechet_derivative (mfd_vrep atlas X c) (at u) z` SUBST1_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `frechet_derivative (\u. a % mfd_vrep atlas (X:A->real^N) c u) (at u) z` THEN
      CONJ_TAC THENL
       [AP_THM_TAC THEN MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
        EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER W)` THEN ASM_SIMP_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER W)`;
                     `mfd_vrep atlas (X:A->real^N) c`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
      ASM_SIMP_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `u:real^N`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o MATCH_MP HAS_DERIVATIVE_CMUL) THEN
      DISCH_THEN(MP_TAC o SPEC `a:real`) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]);
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `bilinear (christoffel (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)) u)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC CHRISTOFFEL_BILINEAR THEN
      EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN CONJ_TAC THENL
       [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
        REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `u IN IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER W)` THEN SET_TAC[]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[BILINEAR_RMUL; GSYM VECTOR_ADD_LDISTRIB; VECTOR_MUL_RZERO]]);;

