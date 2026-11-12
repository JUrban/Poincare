(* ========================================================================= *)
(* Unit pc_p3e_limscal: under smooth convergence on compact subsets of an    *)
(* open set Om (rfs_limit_metric), the scalar curvature of the time slices   *)
(* converges at every point of Om to that of the limit metric.  General (any *)
(* manifold, any limit metric); a small separate unit, used by pc_p2c_sing,  *)
(* pc_p2c_horns and pc_p3e_curvpersist.                                      *)
(* ========================================================================= *)

needs "src/pc_lrg_stab.ml";;
needs "src/pc_rfs_history.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The scalar curvature converges pointwise under smooth                     *)
(* convergence on compact subsets (rfs_limit_metric), from the lck           *)
(* convergence of order 2 at the point (LCK_CURVATURE_STABILITY).  General:  *)
(* any manifold, any limit metric gl; the time family only needs to be      *)
(* Riemannian on some interval before ts.                                    *)
(* ------------------------------------------------------------------------- *)

let P3E_LIMIT_SCALAR = prove
 (`!(top:A topology) atlas Om ts (g:real->A->real^3^3) gl y.
     smooth_manifold_atlas top atlas /\
     rfs_limit_metric (top,atlas) Om ts g gl /\ open_in top Om /\ y IN Om /\
     (?d0. &0 < d0 /\ !t. ts - d0 < t /\ t < ts ==> riemannian_metric atlas (g t))
     ==> !e. &0 < e
             ==> ?d. &0 < d /\
                     !t. ts - d < t /\ t < ts
                         ==> abs(mfd_scalar atlas (g t) y - mfd_scalar atlas gl y) < e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC))))) THEN
  REWRITE_TAC[rfs_limit_metric] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "MF") (LABEL_TAC "CV")) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) (y:A)` THEN
  SUBGOAL_THEN `c IN (atlas:((A->bool)#(A->real^3))->bool) /\ (y:A) IN FST c`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC CHART_AT THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `S = IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER Om)` THEN
  SUBGOAL_THEN `metric_field S (metric_local (atlas:((A->bool)#(A->real^3))->bool) c gl)`
  ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN USE_THEN "MF" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `SND(c:(A->bool)#(A->real^3)) y IN S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `y:A` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sqrt(abs(lrm_deriv_norm2 0
                    (metric_local (atlas:((A->bool)#(A->real^3))->bool) c gl)
                    (SND(c:(A->bool)#(A->real^3)) y)))`; `e / &2`]
                (INST_TYPE [`:3`,`:N`] LCK_CURVATURE_STABILITY)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ST"))) THEN
  USE_THEN "CV" (MP_TAC o SPECL [`{y:A}`; `2`; `eta pow 2`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; COMPACT_IN_SING; SING_SUBSET]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D1"))) THEN
  EXISTS_TAC `min d0 d1` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric (atlas:((A->bool)#(A->real^3))->bool) ((g:real->A->real^3^3) t)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field S (metric_local (atlas:((A->bool)#(A->real^3))->bool) c
                                 ((g:real->A->real^3^3) t))` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^3))->bool)
                     ((g:real->A->real^3^3) t)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `metric_field S (metric_local (atlas:((A->bool)#(A->real^3))->bool) c gl)` THEN
      SIMP_TAC[metric_field];
      EXPAND_TAC "S" THEN SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_scalar] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= e / &2 /\ &0 < e ==> x < e`) THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "ST" (MP_TAC o SPECL [`S:real^3->bool`;
                                 `metric_local (atlas:((A->bool)#(A->real^3))->bool) c gl`;
                                 `metric_local (atlas:((A->bool)#(A->real^3))->bool) c
                                    ((g:real->A->real^3^3) t)`;
                                 `SND(c:(A->bool)#(A->real^3)) y`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SIMP_TAC[SQRT_POW_2; REAL_ABS_POS] THEN REAL_ARITH_TAC;
      USE_THEN "D1" (MP_TAC o SPECL [`t:real`; `y:A`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[IN_SING] THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]];
    SIMP_TAC[]]);;

