(* ========================================================================= *)
(* pc_p2b_parkit (Part 2B): the chart kit for parallel vector fields, a      *)
(* separate unit so that units using only this kit (pc_p2b_kfl) do not load  *)
(* pc_p2b_x0.  Contents: P2BX0_DDPAR, P2BX0_LRIEMANN_PARALLEL (a parallel    *)
(* field kills the curvature), P2BX0_LNABLA_PAR_SLOT(_V), P2BX0_LRM4_PAR,    *)
(* P2BX0_NABLA_W_RM, P2BX0_NABLA_W_RIC, P2BX0_LRIC2_PAR,                     *)
(* P2BX0_NABLA_RIC_W12, P2BX0_LRICCI_PAR (Ric kills a parallel field),       *)
(* P2BX0_VREP_DOT, P2BX0_VREP_AT, P2BX0_LSCALAR_CHART.  It needs LRG, its    *)
(* tensor and evolution layers, and the mfd base units.                      *)
(* ========================================================================= *)

needs "src/pc_lrg_tensor.ml";;
needs "src/pc_lrg_evol.ml";;
needs "src/pc_mfd_maps.ml";;
needs "src/pc_mfd_riem.ml";;

prioritize_real();;
type_invention_error := true;;

(* X0.10a A parallel field is annihilated by the curvature: if            *)
(* D_w W = -Gamma(w, W) on an open set, then R(u,v) W = 0 (differentiate   *)
(* the parallel equation, LRG_HAS_DERIVATIVE_LINFAM, and use the symmetry  *)
(* of second derivatives LRG_SECOND_DERIVATIVE_SYM).                       *)

let P2BX0_DDPAR = prove
 (`!U (G:real^N->real^N^N) (W:real^N->real^N) y u v.
     metric_field U G /\ y IN U /\ smooth_map_on U W /\
     (!z w. z IN U ==> frechet_derivative W (at z) w + christoffel G z w (W z) = vec 0)
     ==> frechet_derivative (\z. frechet_derivative W (at z) v) (at y) u =
         christoffel G y v (christoffel G y u (W y)) -
         frechet_derivative (\z. christoffel G z v (W y)) (at y) u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open (U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (\z. frechet_derivative (W:real^N->real^N) (at z) v) (at y) =
    frechet_derivative (\z. --(christoffel (G:real^N->real^N^N) z v (W z))) (at y)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`z:real^N`; `v:real^N`]) THEN ASM_REWRITE_TAC[] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z w. christoffel (G:real^N->real^N^N) z v w`; `W:real^N->real^N`;
                 `frechet_derivative (W:real^N->real^N) (at y)`; `U:real^N->bool`;
                 `y:real^N`] LRG_HAS_DERIVATIVE_LINFAM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ETA_AX] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`]
                    LRG_CHRISTOFFEL_LINEAR) THEN
      ASM_SIMP_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC LRG_CHRISTOFFEL_DIFF THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `W:real^N->real^N`; `y:real^N`; `v:real^N`]
                    LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o BETA_RULE) THEN
  SUBGOAL_THEN
   `((\z. --(christoffel (G:real^N->real^N^N) z v ((W:real^N->real^N) z))) has_derivative
     (\h. --(christoffel G y v (frechet_derivative W (at y) h) +
             frechet_derivative (\z. christoffel G z v (W y)) (at y) h))) (at y)`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_NEG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  SUBGOAL_THEN `frechet_derivative (W:real^N->real^N) (at y) u =
                --(christoffel (G:real^N->real^N^N) y u (W y))` SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^N`; `u:real^N`]) THEN ASM_REWRITE_TAC[] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
                LRG_CHRISTOFFEL_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `v:real^N` o CONJUNCT1) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP LINEAR_NEG th]) THEN
  VECTOR_ARITH_TAC);;

let P2BX0_LRIEMANN_PARALLEL = prove
 (`!U (G:real^N->real^N^N) (W:real^N->real^N) y u v.
     metric_field U G /\ y IN U /\ smooth_map_on U W /\
     (!z w. z IN U ==> frechet_derivative W (at z) w + christoffel G z w (W z) = vec 0)
     ==> lriemann G y u v (W y) = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open (U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `W:real^N->real^N`; `y:real^N`; `u:real^N`; `v:real^N`]
                LRG_SECOND_DERIVATIVE_SYM) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `W:real^N->real^N`; `y:real^N`;
                 `u:real^N`; `v:real^N`] P2BX0_DDPAR) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `W:real^N->real^N`; `y:real^N`;
                 `v:real^N`; `u:real^N`] P2BX0_DDPAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[lriemann] THEN VECTOR_ARITH_TAC);;

(* X0.10b A tensor that vanishes whenever slot i carries the parallel field *)
(* W has vanishing covariant derivative there: if T z (u[i := W z]) = 0 on  *)
(* U for all u, then (nabla T)(u[i := W y]) = 0 (product rule              *)
(* LRG_HAS_DERIVATIVE_LINFAM in slot i; the other Christoffel terms keep W  *)
(* in slot i).                                                               *)

let P2BX0_LNABLA_PAR_SLOT = prove
 (`!k U (G:real^N->real^N^N) (Tf:real^N->(num->real^N)->real) (W:real^N->real^N) i y u.
     metric_field U G /\ ltensor_field k U Tf /\
     (!u. smooth_map_on U (\x. lift(Tf x u))) /\
     y IN U /\ 1 <= i /\ i <= k /\ smooth_map_on U W /\
     (!z w. z IN U ==> frechet_derivative W (at z) w + christoffel G z w (W z) = vec 0) /\
     (!z u. z IN U ==> Tf z (\m. if m = i then W z else u m) = &0)
     ==> lnabla k G Tf y (\m. if m = i then W y else u m) = &0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "tf")
    (CONJUNCTS_THEN2 (LABEL_TAC "sm") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "par") (LABEL_TAC "zero"))))))))) THEN
  SUBGOAL_THEN `open (U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  ABBREV_TAC `L = \z (w:real^N). lift((Tf:real^N->(num->real^N)->real) z
                                       (\m. if m = i then w else u m))` THEN
  SUBGOAL_THEN `!z. z IN U ==> linear ((L:real^N->real^N->real^1) z)` ASSUME_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN EXPAND_TAC "L" THEN
    USE_THEN "tf" (MP_TAC o REWRITE_RULE[ltensor_field]) THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`i:num`; `u:num->real^N`] o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. (\z. (L:real^N->real^N->real^1) z w) differentiable at y`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^N` THEN EXPAND_TAC "L" THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`U:real^N->bool`;
                   `\x. lift((Tf:real^N->(num->real^N)->real) x
                              (\m. if m = i then w else u m))`; `y:real^N`; `w:real^N`]
                  LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
    USE_THEN "sm" (fun th -> ASM_SIMP_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `(W:real^N->real^N) differentiable at y` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `W:real^N->real^N`; `y:real^N`; `y:real^N`]
                  LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:real^N->real^N->real^1`; `W:real^N->real^N`;
                 `frechet_derivative (W:real^N->real^N) (at y)`; `U:real^N->bool`;
                 `y:real^N`] LRG_HAS_DERIVATIVE_LINFAM) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o BETA_RULE) THEN
  SUBGOAL_THEN
   `!h. (L:real^N->real^N->real^1) y (frechet_derivative (W:real^N->real^N) (at y) h) +
        frechet_derivative (\z. L z (W y)) (at y) h = vec 0`
  (LABEL_TAC "D0") THENL
   [SUBGOAL_THEN
     `frechet_derivative (\z. (L:real^N->real^N->real^1) z ((W:real^N->real^N) z)) (at y) =
      frechet_derivative (\z. vec 0) (at y)`
    MP_TAC THENL
     [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN EXPAND_TAC "L" THEN
      REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN USE_THEN "zero" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
    REWRITE_TAC[FRECHET_DERIVATIVE_CONST_AT; FUN_EQ_THM];
    ALL_TAC] THEN
  ABBREV_TAC `d = (u:num->real^N) (k + 1)` THEN
  SUBGOAL_THEN
   `frechet_derivative (\z. (L:real^N->real^N->real^1) z ((W:real^N->real^N) y)) (at y) d =
    L y (christoffel (G:real^N->real^N^N) y d (W y))`
  ASSUME_TAC THENL
   [USE_THEN "D0" (MP_TAC o SPEC `d:real^N`) THEN
    SUBGOAL_THEN `frechet_derivative (W:real^N->real^N) (at y) d =
                  --(christoffel (G:real^N->real^N^N) y d (W y))` SUBST1_TAC THENL
     [USE_THEN "par" (MP_TAC o SPECL [`y:real^N`; `d:real^N`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; VECTOR_ARITH_TAC];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check (fun th ->
      can (term_match [] `!z. z IN U ==> linear ((L:real^N->real^N->real^1) z)`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP LINEAR_NEG th]) THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[lnabla] THEN
  SUBGOAL_THEN `~((k:num) + 1 = i)` (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `i <= (k:num)` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\z. lift((Tf:real^N->(num->real^N)->real) z (\m. if m = i then (W:real^N->real^N) y
                                                     else u m))) =
    (\z. (L:real^N->real^N->real^1) z (W y))`
  SUBST1_TAC THENL [EXPAND_TAC "L" THEN REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "L" THEN REWRITE_TAC[LIFT_DROP] THEN
  SUBGOAL_THEN
   `sum(1..k) (\j. (Tf:real^N->(num->real^N)->real) y
                     (\m. if m = j
                          then christoffel (G:real^N->real^N^N) y d
                                 (if j = i then (W:real^N->real^N) y else u j)
                          else if m = i then W y else u m)) =
    sum(1..k) (\j. if j = i then Tf y (\m. if m = i then christoffel G y d (W y) else u m)
                   else &0)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN ASM_CASES_TAC `j:num = i` THENL
     [ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
      X_GEN_TAC `m:num` THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN
      USE_THEN "zero" (MP_TAC o SPECL [`y:real^N`;
        `\m. if m = j then christoffel (G:real^N->real^N^N) y d ((u:num->real^N) j)
             else u m`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `m:num` THEN
      ASM_CASES_TAC `m:num = i` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `m:num = j` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_DELTA; IN_NUMSEG] THEN ASM_REWRITE_TAC[REAL_SUB_REFL]);;

(* X0.10c Consequences for the curvature: for a parallel field W on U,     *)
(* Rm vanishes with W in slot 3 or 4, nabla_W Rm = 0 (second Bianchi       *)
(* identity LRM4_BIANCHI2), nabla_W Ric = 0 (LRG_NRM_CONTRACT13), and      *)
(* Ric(W,.) = 0 with (nabla Ric)(W,.) = 0.                                  *)

let P2BX0_LNABLA_PAR_SLOT_V = prove
 (`!k U (G:real^N->real^N^N) (Tf:real^N->(num->real^N)->real) (W:real^N->real^N) i y v.
     metric_field U G /\ ltensor_field k U Tf /\
     (!u. smooth_map_on U (\x. lift(Tf x u))) /\
     y IN U /\ 1 <= i /\ i <= k /\ smooth_map_on U W /\
     (!z w. z IN U ==> frechet_derivative W (at z) w + christoffel G z w (W z) = vec 0) /\
     (!z u. z IN U ==> Tf z (\m. if m = i then W z else u m) = &0) /\
     v i = W y
     ==> lnabla k G Tf y v = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `Tf:real^N->(num->real^N)->real`; `W:real^N->real^N`; `i:num`; `y:real^N`;
                 `v:num->real^N`] P2BX0_LNABLA_PAR_SLOT) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `m:num` THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let P2BX0_LRM4_PAR = prove
 (`!U (G:real^N->real^N^N) (W:real^N->real^N).
     metric_field U G /\ smooth_map_on U W /\
     (!z w. z IN U ==> frechet_derivative W (at z) w + christoffel G z w (W z) = vec 0)
     ==> (!z u. z IN U ==> lrm4 G z (\m. if m = 3 then W z else u m) = &0) /\
         (!z u. z IN U ==> lrm4 G z (\m. if m = 4 then W z else u m) = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[lrm4] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`;
                   `(u:num->real^N) 1`; `(u:num->real^N) 2`; `(u:num->real^N) 4`;
                   `(W:real^N->real^N) z`] LRIEMANN_METRIC_ANTISYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `W:real^N->real^N`; `z:real^N`;
                   `(u:num->real^N) 1`; `(u:num->real^N) 2`] P2BX0_LRIEMANN_PARALLEL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_NEG_0];
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `W:real^N->real^N`; `z:real^N`;
                   `(u:num->real^N) 1`; `(u:num->real^N) 2`] P2BX0_LRIEMANN_PARALLEL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO]]);;

let P2BX0_NABLA_W_RM = prove
 (`!U (G:real^N->real^N^N) (W:real^N->real^N) y a b c d.
     metric_field U G /\ y IN U /\ smooth_map_on U W /\
     (!z w. z IN U ==> frechet_derivative W (at z) w + christoffel G z w (W z) = vec 0)
     ==> lnabla 4 G (lrm4 G) y
           (\m. if m = 1 then a else if m = 2 then b else if m = 3 then c
                else if m = 4 then d else W y) = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `a:real^N`; `b:real^N`;
                 `c:real^N`; `d:real^N`; `(W:real^N->real^N) y`] LRM4_BIANCHI2) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `W:real^N->real^N`]
                P2BX0_LRM4_PAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `lnabla 4 G (lrm4 (G:real^N->real^N^N)) y
      (\m. if m = 1 then a else if m = 2 then b else if m = 3 then d
           else if m = 4 then (W:real^N->real^N) y else c) = &0 /\
    lnabla 4 G (lrm4 G) y
      (\m. if m = 1 then a else if m = 2 then b else if m = 3 then W y
           else if m = 4 then c else d) = &0`
  (fun th -> REWRITE_TAC[th; REAL_ADD_RID]) THEN
  CONJ_TAC THEN MATCH_MP_TAC P2BX0_LNABLA_PAR_SLOT_V THEN
  MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `W:real^N->real^N`] THENL
   [EXISTS_TAC `4`; EXISTS_TAC `3`] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let P2BX0_NABLA_W_RIC = prove
 (`!U (G:real^N->real^N^N) (W:real^N->real^N) y p q.
     metric_field U G /\ y IN U /\ smooth_map_on U W /\
     (!z w. z IN U ==> frechet_derivative W (at z) w + christoffel G z w (W z) = vec 0)
     ==> lnabla 2 G (lric2 G) y
           (\m. if m = 1 then p else if m = 2 then q else W y) = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `p:real^N`; `q:real^N`;
                 `(W:real^N->real^N) y`] LRG_NRM_CONTRACT13) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN X_GEN_TAC `c:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ENTIRE] THEN DISJ2_TAC THEN
  MATCH_MP_TAC P2BX0_NABLA_W_RM THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let P2BX0_LRIC2_PAR = prove
 (`!U (G:real^N->real^N^N) (W:real^N->real^N).
     metric_field U G /\ smooth_map_on U W /\
     (!z w. z IN U ==> frechet_derivative W (at z) w + christoffel G z w (W z) = vec 0)
     ==> (!z u. z IN U ==> lric2 G z (\m. if m = 1 then W z else u m) = &0) /\
         (!z u. z IN U ==> lric2 G z (\m. if m = 2 then W z else u m) = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[lric2] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `!z w. z IN U ==> lricci (G:real^N->real^N^N) z w ((W:real^N->real^N) z) = &0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[lricci] THEN MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `W:real^N->real^N`; `z:real^N`;
                   `basis i:real^N`; `w:real^N`] P2BX0_LRIEMANN_PARALLEL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VEC_COMPONENT];
    ALL_TAC] THEN
  CONJ_TAC THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`;
                 `(W:real^N->real^N) z`; `(u:num->real^N) 2`] LRICCI_SYM) THEN
  ASM_SIMP_TAC[]);;

let P2BX0_NABLA_RIC_W12 = prove
 (`!U (G:real^N->real^N^N) (W:real^N->real^N) y v.
     metric_field U G /\ y IN U /\ smooth_map_on U W /\
     (!z w. z IN U ==> frechet_derivative W (at z) w + christoffel G z w (W z) = vec 0) /\
     (v 1 = W y \/ v 2 = W y)
     ==> lnabla 2 G (lric2 G) y v = &0`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC DISJ_CASES_TAC)))) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRG_LRIC2_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `W:real^N->real^N`]
                P2BX0_LRIC2_PAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC P2BX0_LNABLA_PAR_SLOT_V THEN
  MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `W:real^N->real^N`] THENL
   [EXISTS_TAC `1`; EXISTS_TAC `2`] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

(* X0.10h-a The Ricci tensor kills a parallel field: Ric(W,.) = 0 and     *)
(* Ric(.,W) = 0 (contraction of P2BX0_LRM4_PAR).                           *)

let P2BX0_LRICCI_PAR = prove
 (`!U (G:real^N->real^N^N) (W:real^N->real^N) y.
     metric_field U G /\ smooth_map_on U W /\
     (!z w. z IN U ==> frechet_derivative W (at z) w + christoffel G z w (W z) = vec 0) /\
     y IN U
     ==> !w. lricci G y (W y) w = &0 /\ lricci G y w (W y) = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `w:real^N` THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `W:real^N->real^N`]
                P2BX0_LRIC2_PAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN (MP_TAC o SPECL [`y:real^N`; `\m:num. (w:real^N)`])) THEN
  ASM_REWRITE_TAC[lric2] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

(* X0.10l Chart bookkeeping: chart representatives preserve the length of a *)
(* vector field, the representative in the preferred chart at x is X x,     *)
(* and the scalar curvature in any chart.                                   *)

let P2BX0_VREP_DOT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (X:A->real^N) c y.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ y IN IMAGE (SND c) (FST c)
     ==> mfd_vrep atlas X c y dot (metric_local atlas c g y ** mfd_vrep atlas X c y) =
         X(chart_inv c y) dot (g(chart_inv c y) ** X(chart_inv c y))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `P = chart_inv (c:(A->bool)#(A->real^N)) y` THEN
  SUBGOAL_THEN `(P:A) IN FST (c:(A->bool)#(A->real^N))` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(P:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[mfd_vrep; metric_local] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `P:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c' = chart_at (atlas:((A->bool)#(A->real^N))->bool) (P:A)` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `linear(chart_jac (c:(A->bool)#(A->real^N)) c' P) /\
    !v. chart_jac c c' P (chart_jac c' c P v) = v`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                     `FST(c':(A->bool)#(A->real^N))`; `SND(c':(A->bool)#(A->real^N))`; `P:A`]
        CHART_JAC_LINEAR) THEN
      ASM_REWRITE_TAC[PAIR; IN_INTER];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST(c':(A->bool)#(A->real^N))`; `SND(c':(A->bool)#(A->real^N))`;
                     `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`; `P:A`]
        CHART_JAC_INVERSE) THEN
      ASM_REWRITE_TAC[PAIR; IN_INTER; FUN_EQ_THM; o_THM]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL] THEN
  ASM_SIMP_TAC[MATRIX_WORKS]);;

let P2BX0_VREP_AT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (X:A->real^N) x.
     smooth_manifold_atlas top atlas /\ x IN topspace top
     ==> mfd_vrep atlas X (chart_at atlas x) (SND(chart_at atlas x) x) = X x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[mfd_vrep] THEN ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`; `x:A`]
                CHART_JAC_SELF) THEN
  ASM_REWRITE_TAC[PAIR] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

let P2BX0_LSCALAR_CHART = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) c y.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ c IN atlas /\
     y IN IMAGE (SND c) (FST c)
     ==> lscalar (metric_local atlas c g) y = mfd_scalar atlas g (chart_inv c y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `P = chart_inv (c:(A->bool)#(A->real^N)) y` THEN
  SUBGOAL_THEN `(P:A) IN FST (c:(A->bool)#(A->real^N)) /\ SND c P = y` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(P:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `P:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REWRITE_TAC[mfd_scalar] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (P:A))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (P:A))`;
                 `g:A->real^N^N`; `P:A`] LSCALAR_CHART_TRANS) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER]);;

