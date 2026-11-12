(* ========================================================================= *)
(* Unit pc_sch_b1chart: the explicit pancake chart for the cancellation cut, *)
(* part H2 of the one-saddle base case of the smooth Schoenflies induction   *)
(* (H1 pc_sch_b1cls, H2 this unit, H3 pc_sch_b1canc, H4 pc_sch_base1).  A    *)
(* collar of S whose layers near the left branch point are vertical          *)
(* translates of S, a push of the planar disc that brings the cap tip next   *)
(* to the saddle, an explicit cutoff, and the chart of pc_sch_vflow,         *)
(* explicit near the path from the saddle to the cap tip.                    *)
(* ========================================================================= *)

needs "src/pc_sch_b1cls.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The translate collar.  G = (1 - mu) g + mu (g(x/|x|) +                    *)
(* (|x| - 1) kap e3), with mu a bump of g(x/|x|) around a point l of S.      *)
(* ------------------------------------------------------------------------- *)

let schy_tn_mu = new_definition
 `schy_tn_mu (l:real^3) (d:real) (g:real^3->real^3) (x:real^3) =
    smooth_bump d (&2 * d) (g(inv(norm x) % x) - l)`;;

let schy_tn_G = new_definition
 `schy_tn_G (l:real^3) (d:real) (kap:real) (g:real^3->real^3) (x:real^3) =
    (&1 - schy_tn_mu l d g x) % g x +
    schy_tn_mu l d g x % (g(inv(norm x) % x) + (norm x - &1) % (kap % basis 3))`;;

let SCHY_TN_SMOOTH = prove
 (`!(l:real^3) d kap (g:real^3->real^3) g'.
     sch_neck g g' /\ &0 < d
     ==> smooth_map_on (annulus (&1 / &2) (&2)) (schy_tn_G l d kap g)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `W = annulus (&1 / &2) (&2):real^3->bool` THEN
  SUBGOAL_THEN `open (W:real^3->bool) /\ W SUBSET {x:real^3 | ~(x = vec 0)} /\
                smooth_map_on W (g:real^3->real^3)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[OPEN_ANNULUS] THEN
    CONJ_TAC THENL [MATCH_MP_TAC SMT_SUBSET_NONZERO_ANNULUS THEN REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `sch_neck (g:real^3->real^3) g'` THEN SIMP_TAC[sch_neck; diffeomorphism_on];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on W (\x:real^3. (g:real^3->real^3)(inv(norm x) % x))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\x:real^3. (g:real^3->real^3)(inv(norm x) % x)) =
                  g o (\x. inv(norm x) % x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `W:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
       [UNDISCH_TAC `(W:real^3->bool) SUBSET {x:real^3 | ~(x = vec 0)}` THEN
        UNDISCH_TAC `(x:real^3) IN W` THEN SET_TAC[];
        ALL_TAC] THEN
      EXPAND_TAC "W" THEN MATCH_MP_TAC SCH5_SPHERE_IN_ANNULUS THEN
      REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN
      ASM_REWRITE_TAC[SMOOTH_MAP_ON_NORMALIZE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on W (\x:real^3. lift(schy_tn_mu l d (g:real^3->real^3) x))`
  ASSUME_TAC THENL
   [REWRITE_TAC[schy_tn_mu] THEN
    SUBGOAL_THEN `(\x:real^3. lift(smooth_bump d (&2 * d)
                     ((g:real^3->real^3)(inv(norm x) % x) - l))) =
                  (\y. lift(smooth_bump d (&2 * d) y)) o (\x. g(inv(norm x) % x) - l)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^3)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST];
      MATCH_MP_TAC SMOOTH_BUMP_SMOOTH THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on W (\x:real^3. lift(norm x - &1))` ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_LIFT_NORM_NONZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `schy_tn_G l d kap (g:real^3->real^3) =
    (\x. drop(lift(&1 - schy_tn_mu l d g x)) % g x +
         drop(lift(schy_tn_mu l d g x)) %
         (g(inv(norm x) % x) + drop(lift(norm x - &1)) % (kap % basis 3)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; schy_tn_G; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[ETA_AX] THEN
    REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST];
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST]]);;

let SCHY_TN_SPHERE = prove
 (`!(l:real^3) d kap (g:real^3->real^3) t.
     t IN sphere(vec 0,&1) ==> schy_tn_G l d kap g t = g t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SPHERE_0] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[schy_tn_G; REAL_INV_1; VECTOR_MUL_LID; REAL_SUB_REFL; VECTOR_MUL_LZERO;
                  VECTOR_ADD_RID] THEN
  VECTOR_ARITH_TAC);;

let SCHY_TN_RAY = prove
 (`!(l:real^3) d kap (g:real^3->real^3) t s.
     t IN sphere(vec 0,&1) /\ &0 < s
     ==> schy_tn_mu l d g (s % t) = schy_tn_mu l d g t /\
         schy_tn_G l d kap g (s % t) =
         (&1 - schy_tn_mu l d g t) % g(s % t) +
         schy_tn_mu l d g t % (g t + (s - &1) % (kap % basis 3))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SPHERE_0] THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm(s % t:real^3) = s /\ inv(norm(s % t:real^3)) % (s % t) = t`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < s ==> abs s = s`; VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `schy_tn_mu l d (g:real^3->real^3) (s % t) = schy_tn_mu l d g t`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[schy_tn_mu; REAL_INV_1; VECTOR_MUL_LID]; ALL_TAC] THEN
  ASM_REWRITE_TAC[schy_tn_G; REAL_INV_1; VECTOR_MUL_LID]);;

let SCHY_NORMAL_DOT = prove
 (`!(g:real^3->real^3) g' t v.
     sch_neck g g' /\ t IN sphere(vec 0,&1)
     ==> sch5v_grad g' (g t) dot frechet_derivative g (at t) v = &2 * (t dot v)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(t:real^3) IN annulus (&1 / &2) (&2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SCH5_SPHERE_IN_ANNULUS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `t:real^3`;
                 `frechet_derivative (g:real^3->real^3) (at t) v`] SCH5V_GRAD_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `t:real^3`] SCH5_NECK_FACTS) THEN
  ASM_SIMP_TAC[]);;

(* The radial derivative of G at the sphere, through the ray s |-> s t.      *)

let SCHY_RAY_VDERIV = prove
 (`!(k:real^3->real^3) t.
     k differentiable (at t)
     ==> ((k o (\s:real^1. drop s % t)) has_vector_derivative
          frechet_derivative k (at t) t) (at (lift(&1)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((\s:real^1. drop s % (t:real^3)) has_derivative (\h. drop h % t))
                (at (lift(&1)))` ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN
    CONJ_TAC THEN REPEAT GEN_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FRECHET_DERIVATIVE_WORKS]) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(((k:real^3->real^3) o (\s:real^1. drop s % t)) has_derivative
                 (frechet_derivative k (at t) o (\h:real^1. drop h % t))) (at (lift(&1)))`
  MP_TAC THENL
   [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[LIFT_DROP; VECTOR_MUL_LID]; ALL_TAC] THEN
  REWRITE_TAC[has_vector_derivative] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN
  SUBGOAL_THEN `linear(frechet_derivative (k:real^3->real^3) (at t))` ASSUME_TAC THENL
   [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
  ASM_SIMP_TAC[LINEAR_CMUL]);;

let SCHY_TN_RADIAL_DERIV = prove
 (`!(l:real^3) d kap (g:real^3->real^3) g' t.
     sch_neck g g' /\ &0 < d /\ t IN sphere(vec 0,&1)
     ==> frechet_derivative (schy_tn_G l d kap g) (at t) t =
         (&1 - schy_tn_mu l d g t) % frechet_derivative g (at t) t +
         schy_tn_mu l d g t % (kap % basis 3)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `G = schy_tn_G l d kap (g:real^3->real^3)` THEN
  ABBREV_TAC `m = schy_tn_mu l d (g:real^3->real^3) t` THEN
  SUBGOAL_THEN `(t:real^3) IN annulus (&1 / &2) (&2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SCH5_SPHERE_IN_ANNULUS]; ALL_TAC] THEN
  SUBGOAL_THEN `(G:real^3->real^3) differentiable (at t) /\
                (g:real^3->real^3) differentiable (at t)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN
      ASM_REWRITE_TAC[OPEN_ANNULUS] THEN EXPAND_TAC "G" THEN MATCH_MP_TAC SCHY_TN_SMOOTH THEN
      EXISTS_TAC `g':real^3->real^3` THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `t:real^3`] SCH5_NECK_FACTS) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_AT THEN
  EXISTS_TAC `(G:real^3->real^3) o (\s:real^1. drop s % t)` THEN
  EXISTS_TAC `lift(&1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SCHY_RAY_VDERIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `\s:real^1. (&1 - m) % (g:real^3->real^3)(drop s % t) +
                         m % (g t + (drop s - &1) % (kap % basis 3))` THEN
  EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP; o_THM] THEN
    DISCH_TAC THEN EXPAND_TAC "G" THEN EXPAND_TAC "m" THEN
    MP_TAC(ISPECL [`l:real^3`; `d:real`; `kap:real`; `g:real^3->real^3`; `t:real^3`;
                   `drop s`] SCHY_TN_RAY) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_CMUL THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `t:real^3`] SCHY_RAY_VDERIV) THEN
    ASM_REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_CMUL THEN
  SUBGOAL_THEN `(\s:real^1. (g:real^3->real^3) t + (drop s - &1) % (kap % basis 3)) =
                (\s. (g t - kap % basis 3) + drop s % (kap % basis 3))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`\s:real^1. (g:real^3->real^3) t - kap % basis 3`; `vec 0:real^3`;
                 `\s:real^1. drop s % (kap % basis 3:real^3)`; `kap % basis 3:real^3`;
                 `at (lift(&1))`] HAS_VECTOR_DERIVATIVE_ADD) THEN
  REWRITE_TAC[VECTOR_ADD_LID; HAS_VECTOR_DERIVATIVE_CONST] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[has_vector_derivative] THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
  REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN CONJ_TAC THEN REPEAT GEN_TAC THEN
  VECTOR_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Derivative helpers, the normal of S at the left branch point              *)
(* lpt is not horizontal, and the translate collar: a collar of S equal to g *)
(* on the sphere whose layers near lpt are the vertical translates of S.     *)
(* ------------------------------------------------------------------------- *)

let SCHY_VDERIV3 = prove
 (`!(f1:real^1->real) f2 f3 d1 d2 d3 s0.
     ((\s. lift(f1 s)) has_vector_derivative lift d1) (at s0) /\
     ((\s. lift(f2 s)) has_vector_derivative lift d2) (at s0) /\
     ((\s. lift(f3 s)) has_vector_derivative lift d3) (at s0)
     ==> ((\s:real^1. vector[f1 s; f2 s; f3 s]:real^3) has_vector_derivative
          vector[d1; d2; d3]) (at s0)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [HAS_VECTOR_DERIVATIVE_COMPONENTWISE_AT] THEN
  REWRITE_TAC[DIMINDEX_3; FORALL_3; VECTOR_3] THEN ASM_REWRITE_TAC[]);;

let SCHY_RVD0 = prove
 (`!f:real->real d.
     (f has_real_derivative d) (atreal (&0))
     ==> ((\s:real^1. lift(f(drop s))) has_vector_derivative lift d) (at (lift(&0)))`,
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF]);;

let SCHY_CURVE_CHAIN = prove
 (`!(Fv:real^3->real^N) (c:real^1->real^3) w s0.
     Fv differentiable (at (c s0)) /\ (c has_vector_derivative w) (at s0)
     ==> ((Fv o c) has_vector_derivative frechet_derivative Fv (at (c s0)) w) (at s0)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FRECHET_DERIVATIVE_WORKS]) THEN DISCH_TAC THEN
  UNDISCH_TAC `((c:real^1->real^3) has_vector_derivative w) (at s0)` THEN
  REWRITE_TAC[has_vector_derivative] THEN DISCH_TAC THEN
  SUBGOAL_THEN `((Fv:real^3->real^N) o (c:real^1->real^3) has_derivative
                 frechet_derivative Fv (at (c s0)) o (\h:real^1. drop h % w)) (at s0)` MP_TAC THENL
   [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN
  SUBGOAL_THEN `linear(frechet_derivative (Fv:real^3->real^N) (at (c(s0:real^1))))` ASSUME_TAC THENL
   [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
  ASM_SIMP_TAC[LINEAR_CMUL]);;

let SCHY_CONST_ALONG_CURVE = prove
 (`!(Fv:real^3->real^N) (c:real^1->real^3) w s0 k d.
     Fv differentiable (at (c s0)) /\ (c has_vector_derivative w) (at s0) /\ &0 < d /\
     (!s. dist(s,s0) < d ==> Fv(c s) = k)
     ==> frechet_derivative Fv (at (c s0)) w = vec 0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_AT THEN
  EXISTS_TAC `(Fv:real^3->real^N) o (c:real^1->real^3)` THEN EXISTS_TAC `s0:real^1` THEN
  CONJ_TAC THENL [MATCH_MP_TAC SCHY_CURVE_CHAIN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `\s:real^1. (k:real^N)` THEN EXISTS_TAC `d:real` THEN
  ASM_REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST; o_THM] THEN
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

let SCHY_GRAD_FD = prove
 (`!(g:real^3->real^3) g' t w.
     sch_neck g g' /\ t IN annulus (&1 / &2) (&2)
     ==> sch5v_grad g' (g t) dot w =
         drop(frechet_derivative (\y. lift(norm(g' y) pow 2)) (at (g t)) w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `t:real^3`] SCH5V_RHO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[DROP_CMUL; LIFT_DROP] THEN
  MATCH_MP_TAC SCH5V_GRAD_DOT THEN ASM_REWRITE_TAC[]);;

let SCHY_GRAD_LPT = prove
 (`!(g:real^3->real^3) g' r e.
     sch_neck g g' /\ schy_chart (IMAGE g (sphere(vec 0,&1))) r /\ &0 < e /\ &16 * e < r pow 2
     ==> (sch5v_grad g' (schy_lpt e))$2 = &0 /\
         (sch5v_grad g' (schy_lpt e))$1 = &2 * sqrt e * (sch5v_grad g' (schy_lpt e))$3 /\
         ~((sch5v_grad g' (schy_lpt e))$3 = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`] SCHY_BRANCH_IN_LEVEL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[sch_level; IN_ELIM_THM] THEN STRIP_TAC THEN
  UNDISCH_TAC `schy_lpt e IN IMAGE (g:real^3->real^3) (sphere(vec 0,&1))` THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `t:real^3` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    concl th = `schy_lpt e = (g:real^3->real^3) t`)) THEN
  SUBGOAL_THEN `(t:real^3) IN annulus (&1 / &2) (&2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SCH5_SPHERE_IN_ANNULUS]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [schy_chart] o
    check (fun th -> can (term_match [] `schy_chart s r`) (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CH"))) THEN
  SUBGOAL_THEN `r pow 2 < r` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `x = r * r /\ r * r < r * &1 ==> x < r`) THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt e /\ sqrt e pow 2 = e /\ e < r` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Fq = \y:real^3. lift(norm((g':real^3->real^3) y) pow 2)` THEN
  SUBGOAL_THEN `(Fq:real^3->real^1) differentiable (at (schy_lpt e))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `t:real^3`] SCH5V_RHO_DERIV) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "Fq" THEN MESON_TAC[differentiable];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) ==> Fq y = lift(&1)`
  (LABEL_TAC "F1") THENL
   [X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC) THEN EXPAND_TAC "Fq" THEN
    ASM_REWRITE_TAC[LIFT_EQ] THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `u:real^3`] SCH5_NECK_FACTS) THEN
    ASM_SIMP_TAC[SCH5_SPHERE_IN_ANNULUS] THEN
    UNDISCH_TAC `(u:real^3) IN sphere(vec 0,&1)` THEN SIMP_TAC[IN_SPHERE_0] THEN
    REPEAT STRIP_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. sch5v_grad g' (schy_lpt e) dot w =
                    drop(frechet_derivative (Fq:real^3->real^1) (at (schy_lpt e)) w)`
  (LABEL_TAC "GD") THENL
   [GEN_TAC THEN EXPAND_TAC "Fq" THEN
    UNDISCH_TAC `(g:real^3->real^3) t = schy_lpt e` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC SCHY_GRAD_FD THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. abs s < sqrt e
                    ==> vector[--(sqrt e); s; e - s pow 2]:real^3 IN
                          IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) /\
                        vector[s - sqrt e; &0; (s - sqrt e) pow 2]:real^3 IN
                          IMAGE (g:real^3->real^3) (sphere(vec 0,&1))` (LABEL_TAC "ONS") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `s pow 2 < e /\ (s - sqrt e) pow 2 < &4 * e` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `sqrt e pow 2 = e` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[REAL_POW_2] THEN
        MATCH_MP_TAC(REAL_ARITH `abs(s * s) = abs s * abs s /\ abs s * abs s < q * q
                                  ==> s * s < q * q`) THEN
        REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `abs(s - sqrt e) < &2 * sqrt e` MP_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        DISCH_TAC THEN
        SUBGOAL_THEN `&4 * e = (&2 * sqrt e) pow 2` SUBST1_TAC THENL
         [ASM_REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[REAL_POW_2] THEN
        MATCH_MP_TAC(REAL_ARITH `abs(x * x) = abs x * abs x /\ abs x * abs x < q * q
                                  ==> x * x < q * q`) THEN
        REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    CONJ_TAC THEN USE_THEN "CH" (fun th -> W(fun (_,w) -> MP_TAC(SPEC (lhand w) th))) THEN
    REWRITE_TAC[VECTOR_3] THEN
    (ANTS_TAC THENL
      [CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_NEG; ARITH] THEN
       ASM_REWRITE_TAC[] THEN
       SUBGOAL_THEN `&0 <= s pow 2 /\ &0 <= (s - sqrt e) pow 2` STRIP_ASSUME_TAC THENL
        [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
       ASM_REAL_ARITH_TAC;
       DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_POW_NEG; ARITH] THEN ASM_REWRITE_TAC[] THEN
       CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC]);
    ALL_TAC] THEN
  ABBREV_TAC `c1 = \s:real^1. vector[--(sqrt e); drop s; e - drop s pow 2]:real^3` THEN
  ABBREV_TAC `c2 = \s:real^1. vector[drop s - sqrt e; &0; (drop s - sqrt e) pow 2]:real^3` THEN
  SUBGOAL_THEN
   `((c1:real^1->real^3) has_vector_derivative vector[&0; &1; &0]) (at (lift(&0))) /\
    ((c2:real^1->real^3) has_vector_derivative vector[&1; &0; --(&2 * sqrt e)]) (at (lift(&0)))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c1" THEN EXPAND_TAC "c2" THEN
    CONJ_TAC THEN MATCH_MP_TAC SCHY_VDERIV3 THEN REPEAT CONJ_TAC THENL
     [MP_TAC(SPECL [`\x:real. --(sqrt e)`; `&0`] SCHY_RVD0);
      MP_TAC(SPECL [`\x:real. x`; `&1`] SCHY_RVD0);
      MP_TAC(SPECL [`\x:real. e - x pow 2`; `&0`] SCHY_RVD0);
      MP_TAC(SPECL [`\x:real. x - sqrt e`; `&1`] SCHY_RVD0);
      MP_TAC(SPECL [`\x:real. &0`; `&0`] SCHY_RVD0);
      MP_TAC(SPECL [`\x:real. (x - sqrt e) pow 2`; `--(&2 * sqrt e)`] SCHY_RVD0)] THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REAL_DIFF_TAC THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_1] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(c1:real^1->real^3) (lift(&0)) = schy_lpt e /\
                (c2:real^1->real^3) (lift(&0)) = schy_lpt e` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c1" THEN EXPAND_TAC "c2" THEN
    REWRITE_TAC[schy_lpt; LIFT_DROP; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
    REWRITE_TAC[REAL_SUB_LZERO; REAL_POW_NEG; ARITH] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (Fq:real^3->real^1) (at (schy_lpt e)) (vector[&0; &1; &0]) = vec 0 /\
    frechet_derivative (Fq:real^3->real^1) (at (schy_lpt e)) (vector[&1; &0; --(&2 * sqrt e)]) =
    vec 0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`Fq:real^3->real^1`; `c1:real^1->real^3`;
                     `vector[&0; &1; &0]:real^3`; `lift(&0)`; `lift(&1)`; `sqrt e`]
        SCHY_CONST_ALONG_CURVE);
      MP_TAC(ISPECL [`Fq:real^3->real^1`; `c2:real^1->real^3`;
                     `vector[&1; &0; --(&2 * sqrt e)]:real^3`; `lift(&0)`; `lift(&1)`; `sqrt e`]
        SCHY_CONST_ALONG_CURVE)] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    X_GEN_TAC `s:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
    DISCH_TAC THEN USE_THEN "F1" MATCH_MP_TAC THEN
    EXPAND_TAC "c1" THEN EXPAND_TAC "c2" THEN
    USE_THEN "ONS" (MP_TAC o SPEC `drop s`) THEN
    (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]);
    ALL_TAC] THEN
  SUBGOAL_THEN `sch5v_grad g' (schy_lpt e) dot vector[&0; &1; &0] = &0 /\
                sch5v_grad g' (schy_lpt e) dot vector[&1; &0; --(&2 * sqrt e)] = &0`
  MP_TAC THENL [ASM_REWRITE_TAC[DROP_VEC]; ALL_TAC] THEN
  REWRITE_TAC[DOT_3; VECTOR_3] THEN STRIP_TAC THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `t:real^3`; `t:real^3`]
    SCHY_NORMAL_DOT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `(g:real^3->real^3) t = schy_lpt e` THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `sch5v_grad g' (schy_lpt e) = vec 0` SUBST1_TAC THENL
   [UNDISCH_TAC `(sch5v_grad g' (schy_lpt e))$3 = &0` THEN DISCH_THEN(fun th ->
      RULE_ASSUM_TAC(REWRITE_RULE[th; REAL_MUL_LZERO; REAL_ADD_RID]) THEN ASSUME_TAC th) THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VEC_COMPONENT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[DOT_LZERO] THEN UNDISCH_TAC `(t:real^3) IN sphere(vec 0,&1)` THEN
  REWRITE_TAC[IN_SPHERE_0; NORM_EQ_1] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The translate collar.  Near lpt the layers of the new collar              *)
(* gt are the translates S + s e3: |gt'(y)|^2 = (1 + (y3 - f(y1,y2)) / K)^2.  *)
(* ------------------------------------------------------------------------- *)

let SCHY_GRAD3_SIGN_NEAR = prove
 (`!(g:real^3->real^3) g' p.
     sch_neck g g' /\ p IN IMAGE g (annulus (&1 / &2) (&2)) /\ ~((sch5v_grad g' p)$3 = &0)
     ==> ?d. &0 < d /\
             !x. dist(x,p) < d ==> &0 < (sch5v_grad g' p)$3 * (sch5v_grad g' x)$3`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(sch5v_grad (g':real^3->real^3)) continuous (at p)` MP_TAC THENL
   [MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`] SCH5V_GRAD_SMOOTH) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON) THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`] SCH5V_NECK_OPEN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_at] THEN
  DISCH_THEN(MP_TAC o SPEC `abs((sch5v_grad (g':real^3->real^3) p)$3) / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN EXISTS_TAC `d:real` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[dist] THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs((sch5v_grad (g':real^3->real^3) x)$3 - (sch5v_grad g' p)$3) <
                abs((sch5v_grad g' p)$3) / &2` MP_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `norm(sch5v_grad (g':real^3->real^3) x - sch5v_grad g' p)` THEN
    ASM_REWRITE_TAC[GSYM VECTOR_SUB_COMPONENT] THEN
    SIMP_TAC[COMPONENT_LE_NORM; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  ABBREV_TAC `k = (sch5v_grad (g':real^3->real^3) p)$3` THEN
  ABBREV_TAC `m = (sch5v_grad (g':real^3->real^3) x)$3` THEN DISCH_TAC THEN
  ASM_CASES_TAC `&0 < k` THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `&0 < (--k) * (--m)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]]);;

(* The base point (y1, y2, y1^2 - y2^2) of a point over the planar disc of   *)
(* radius d around (-sqrt e, 0) is within 2d of lpt, and |y'|^2 < 4e.        *)

let SCHY_BASE_NEAR = prove
 (`!(y:real^3) e d.
     &0 < e /\ e < &1 / &16 /\ &0 < d /\ d <= sqrt e /\
     (y$1 + sqrt e) pow 2 + y$2 pow 2 < d pow 2
     ==> norm(vector[y$1; y$2; y$1 pow 2 - y$2 pow 2] - schy_lpt e) < &2 * d /\
         y$1 pow 2 + y$2 pow 2 < &4 * e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `s = sqrt e` THEN
  SUBGOAL_THEN `&0 < s /\ s pow 2 = e` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  ABBREV_TAC `a = (y:real^3)$1 + s` THEN ABBREV_TAC `b = (y:real^3)$2` THEN
  SUBGOAL_THEN `(y:real^3)$1 = a - s` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs a < d /\ abs b < d` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`a:real`; `d:real`] REAL_LT_SQUARE_ABS) THEN
    MP_TAC(ISPECL [`b:real`; `d:real`] REAL_LT_SQUARE_ABS) THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < d ==> abs d = d`] THEN REPEAT DISCH_TAC THEN
    MP_TAC(SPEC `a:real` REAL_LE_POW_2) THEN MP_TAC(SPEC `b:real` REAL_LE_POW_2) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `d pow 2 <= d * s /\ d * s <= e /\ abs a * s < d * s /\
                abs(a * s) = abs a * s` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `s pow 2 = e` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ABS_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < s ==> abs s = s`]];
    ALL_TAC] THEN
  ABBREV_TAC `c = (a - s) pow 2 - b pow 2 - e` THEN
  SUBGOAL_THEN `c = a pow 2 - b pow 2 - &2 * (a * s)` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN UNDISCH_TAC `s pow 2 = e` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `abs c < &3 * d * s` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `a:real` REAL_LE_POW_2) THEN MP_TAC(SPEC `b:real` REAL_LE_POW_2) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> concl th = `(y:real^3)$1 = a - s`)) THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `vector[a - s; b; (a - s) pow 2 - b pow 2] - schy_lpt e =
                  vector[a; b; c]:real^3` SUBST1_TAC THENL
     [REWRITE_TAC[schy_lpt; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
                  VECTOR_SUB_COMPONENT] THEN
      EXPAND_TAC "c" THEN EXPAND_TAC "s" THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `c pow 2 < d pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `(&3 * d * s) pow 2` THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM REAL_LT_SQUARE_ABS] THEN
        SUBGOAL_THEN `abs(&3 * d * s) = &3 * d * s` SUBST1_TAC THENL
         [REWRITE_TAC[REAL_ABS_REFL] THEN
          MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
          ASM_REWRITE_TAC[]];
        SUBGOAL_THEN `(&3 * d * s) pow 2 = (&9 * e) * d pow 2` SUBST1_TAC THENL
         [UNDISCH_TAC `s pow 2 = e` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LT_RMUL THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`norm(vector[a; b; c]:real^3)`; `&2 * d`] REAL_LT_SQUARE_ABS) THEN
    REWRITE_TAC[REAL_ABS_NORM] THEN
    REWRITE_TAC[MATCH_MP (REAL_ARITH `&0 < d ==> abs(&2 * d) = &2 * d`) (ASSUME `&0 < d`)] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[NORM_POW_2; DOT_3; VECTOR_3] THEN REWRITE_TAC[GSYM REAL_POW_2] THEN
    SUBGOAL_THEN `&0 < d pow 2` MP_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    UNDISCH_TAC `c pow 2 < d pow 2` THEN UNDISCH_TAC `a pow 2 + b pow 2 < d pow 2` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(a - s) pow 2 + b pow 2 = a pow 2 + b pow 2 - &2 * (a * s) + e` SUBST1_TAC THENL
   [UNDISCH_TAC `s pow 2 = e` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let SCHY_TRANSLATE_NECK = prove
 (`!(g:real^3->real^3) g' r e.
     sch_neck g g' /\ schy_chart (IMAGE g (sphere(vec 0,&1))) r /\ &0 < e /\
     &16 * e < r pow 2
     ==> ?gt gt' K de.
           sch_neck gt gt' /\
           (!t. t IN sphere(vec 0,&1) ==> gt t = g t) /\
           (!t v. t IN sphere(vec 0,&1) /\ orthogonal t v
                  ==> frechet_derivative gt (at t) v = frechet_derivative g (at t) v) /\
           ~(K = &0) /\ &0 < de /\ de <= sqrt e /\ &2 * de <= abs K /\
           (!y:real^3. (y$1 + sqrt e) pow 2 + y$2 pow 2 < de pow 2 /\
                       abs(y$3 - (y$1 pow 2 - y$2 pow 2)) < de
                       ==> y IN IMAGE gt (annulus (&1 / &2) (&2)) /\
                           norm(gt' y) pow 2 =
                           (&1 + (y$3 - (y$1 pow 2 - y$2 pow 2)) / K) pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`] SCHY_BRANCH_IN_LEVEL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[sch_level; IN_ELIM_THM] THEN STRIP_TAC THEN
  UNDISCH_TAC `schy_lpt e IN IMAGE (g:real^3->real^3) (sphere(vec 0,&1))` THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `tl:real^3` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    concl th = `schy_lpt e = (g:real^3->real^3) tl`)) THEN
  SUBGOAL_THEN `schy_lpt e IN IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2))`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `tl:real^3` THEN
    ASM_SIMP_TAC[SCH5_SPHERE_IN_ANNULUS];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [schy_chart] o
    check (fun th -> can (term_match [] `schy_chart s r`) (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CH"))) THEN
  SUBGOAL_THEN `r pow 2 < r` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `x = r * r /\ r * r < r * &1 ==> x < r`) THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt e /\ sqrt e pow 2 = e /\ e < &1 / &16` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `r:real`; `e:real`]
    SCHY_GRAD_LPT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `kap = (sch5v_grad (g':real^3->real^3) (schy_lpt e))$3` THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `schy_lpt e`]
    SCHY_GRAD3_SIGN_NEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SIGN"))) THEN
  ABBREV_TAC `d = d0 / &4` THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL [EXPAND_TAC "d" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `G = schy_tn_G (schy_lpt e) d kap (g:real^3->real^3)` THEN
  SUBGOAL_THEN `!x y. x IN sphere(vec 0,&1) /\ y IN sphere(vec 0,&1) /\
                      (g:real^3->real^3) x = g y ==> x = y` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `x:real^3`] SCH5_NECK_FACTS) THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `y:real^3`] SCH5_NECK_FACTS) THEN
    ASM_SIMP_TAC[SCH5_SPHERE_IN_ANNULUS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^3->real^3`; `g:real^3->real^3`;
                 `\t:real^3. sch5v_grad (g':real^3->real^3) (g t)`;
                 `annulus (&1 / &2) (&2):real^3->bool`] SCH5_NECK_FROM_TRANSVERSE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[OPEN_ANNULUS; SUBSET; SCH5_SPHERE_IN_ANNULUS] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "G" THEN MATCH_MP_TAC SCHY_TN_SMOOTH THEN
      EXISTS_TAC `g':real^3->real^3` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `sch_neck (g:real^3->real^3) g'` THEN SIMP_TAC[sch_neck; diffeomorphism_on];
      EXPAND_TAC "G" THEN REWRITE_TAC[SCHY_TN_SPHERE];
      MAP_EVERY X_GEN_TAC [`t:real^3`; `v:real^3`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `t:real^3`] SCH5_NECK_FACTS) THEN
      ASM_SIMP_TAC[SCH5_SPHERE_IN_ANNULUS] THEN STRIP_TAC THEN
      SUBGOAL_THEN `frechet_derivative (g':real^3->real^3) (at ((g:real^3->real^3) t))
                      (frechet_derivative g (at t) v) = v` MP_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[ASSUME `frechet_derivative (g:real^3->real^3) (at t) v = vec 0`] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC(ISPEC `frechet_derivative (g':real^3->real^3) (at ((g:real^3->real^3) t))`
        LINEAR_0) THEN
      UNDISCH_TAC `(g':real^3->real^3) differentiable (at ((g:real^3->real^3) t))` THEN
      REWRITE_TAC[FRECHET_DERIVATIVE_WORKS] THEN MESON_TAC[has_derivative];
      REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `t:real^3`; `v:real^3`]
        SCHY_NORMAL_DOT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `orthogonal (t:real^3) v` THEN SIMP_TAC[orthogonal] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `t:real^3` THEN DISCH_TAC THEN EXPAND_TAC "G" THEN
    MP_TAC(ISPECL [`schy_lpt e`; `d:real`; `kap:real`; `g:real^3->real^3`;
                   `g':real^3->real^3`; `t:real^3`] SCHY_TN_RADIAL_DERIV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `t:real^3`; `t:real^3`]
      SCHY_NORMAL_DOT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `(t:real^3) dot t = &1` SUBST1_TAC THENL
     [UNDISCH_TAC `(t:real^3) IN sphere(vec 0,&1)` THEN SIMP_TAC[IN_SPHERE_0; NORM_EQ_1];
      ALL_TAC] THEN
    SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH] THEN
    ABBREV_TAC `m = schy_tn_mu (schy_lpt e) d (g:real^3->real^3) t` THEN
    SUBGOAL_THEN `&0 <= m /\ m <= &1` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "m" THEN REWRITE_TAC[schy_tn_mu; SMOOTH_BUMP_BOUNDS]; ALL_TAC] THEN
    ASM_CASES_TAC `m = &0` THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < kap * (sch5v_grad (g':real^3->real^3) ((g:real^3->real^3) t))$3` ASSUME_TAC THENL
     [ASM_CASES_TAC `norm((g:real^3->real^3) t - schy_lpt e) < &2 * d` THENL
       [USE_THEN "SIGN" MATCH_MP_TAC THEN
        REWRITE_TAC[dist] THEN EXPAND_TAC "d" THEN ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `~(m = &0)` THEN EXPAND_TAC "m" THEN REWRITE_TAC[schy_tn_mu] THEN
        SUBGOAL_THEN `inv(norm(t:real^3)) % t = t` SUBST1_TAC THENL
         [UNDISCH_TAC `(t:real^3) IN sphere(vec 0,&1)` THEN
          SIMP_TAC[IN_SPHERE_0; REAL_INV_1; VECTOR_MUL_LID];
          ALL_TAC] THEN
        SUBGOAL_THEN `smooth_bump d (&2 * d) ((g:real^3->real^3) t - schy_lpt e) = &0`
          (fun th -> REWRITE_TAC[th]) THEN
        MATCH_MP_TAC SMOOTH_BUMP_0 THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < m * (kap * (sch5v_grad (g':real^3->real^3) ((g:real^3->real^3) t))$3)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `m <= &1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (X_CHOOSE_THEN `G':real^3->real^3` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `K = eta / &2 * kap` THEN
  SUBGOAL_THEN `~(K = &0)` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `de = min (sqrt e) (min (d / &2) (abs K / &2))` THEN
  SUBGOAL_THEN `&0 < de /\ de <= sqrt e /\ de <= d / &2 /\ de <= abs K / &2 /\ &2 * de <= abs K`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "de" THEN REWRITE_TAC[REAL_LE_MIN; REAL_LT_MIN] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    UNDISCH_TAC `~(K = &0)` THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`(G:real^3->real^3) o sch5_radial (eta / &2)`;
                        `sch5_radinv (eta / &2) o (G':real^3->real^3)`; `K:real`; `de:real`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  ABBREV_TAC `sg = (y:real^3)$3 - (y$1 pow 2 - y$2 pow 2)` THEN
  MP_TAC(ISPECL [`y:real^3`; `e:real`; `de:real`] SCHY_BASE_NEAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `base = vector[(y:real^3)$1; y$2; y$1 pow 2 - y$2 pow 2]:real^3` THEN
  SUBGOAL_THEN `base IN IMAGE (g:real^3->real^3) (sphere(vec 0,&1))` MP_TAC THENL
   [USE_THEN "CH" (MP_TAC o SPEC `base:real^3`) THEN EXPAND_TAC "base" THEN
    REWRITE_TAC[VECTOR_3] THEN
    ANTS_TAC THENL
     [MP_TAC(SPEC `(y:real^3)$1` REAL_LE_POW_2) THEN MP_TAC(SPEC `(y:real^3)$2` REAL_LE_POW_2) THEN
      ASM_REAL_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `t:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `abs(sg / K) < &1 / &2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_DIV] THEN
    SUBGOAL_THEN `&0 < abs K` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `rho = &1 + sg / K` THEN
  SUBGOAL_THEN `&1 / &2 < rho /\ rho < &3 / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `norm(t:real^3) = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `(t:real^3) IN sphere(vec 0,&1)` THEN REWRITE_TAC[IN_SPHERE_0]; ALL_TAC] THEN
  SUBGOAL_THEN `rho % (t:real^3) IN annulus (&1 / &2) (&2) /\ norm(rho % (t:real^3)) = rho`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[annulus; IN_ELIM_THM; NORM_MUL] THEN ASM_REWRITE_TAC[REAL_MUL_RID] THEN
    ASM_SIMP_TAC[REAL_ARITH `&1 / &2 < rho ==> abs rho = rho`] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(kap = &0) /\ &0 < eta /\ ~(rho = &0)` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 + sg / kap` ASSUME_TAC THENL
   [SUBGOAL_THEN `sg / kap = (eta / &2) * (sg / K)` SUBST1_TAC THENL
     [EXPAND_TAC "K" THEN UNDISCH_TAC `~(kap = &0)` THEN UNDISCH_TAC `&0 < eta` THEN
      CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `abs(y) < &1 ==> &0 < &1 + y`) THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&1 * &1 / &2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `((G:real^3->real^3) o sch5_radial (eta / &2)) (rho % t) = y` ASSUME_TAC THENL
   [REWRITE_TAC[o_THM; sch5_radial] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `((&1 + eta / &2 * (rho - &1)) / rho) % rho % (t:real^3) =
                  (&1 + sg / kap) % t` SUBST1_TAC THENL
     [REWRITE_TAC[VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      UNDISCH_TAC `~(rho = &0)` THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `&1 + sg / K = rho`)) THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `eta / &2 * kap = K`)) THEN
      UNDISCH_TAC `~(kap = &0)` THEN UNDISCH_TAC `&0 < eta` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    EXPAND_TAC "G" THEN
    MP_TAC(ISPECL [`schy_lpt e`; `d:real`; `kap:real`; `g:real^3->real^3`; `t:real^3`;
                   `&1 + sg / kap`] SCHY_TN_RAY) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2 th]) THEN
    SUBGOAL_THEN `schy_tn_mu (schy_lpt e) d (g:real^3->real^3) t = &1` SUBST1_TAC THENL
     [REWRITE_TAC[schy_tn_mu] THEN ASM_REWRITE_TAC[REAL_INV_1; VECTOR_MUL_LID] THEN
      MATCH_MP_TAC SMOOTH_BUMP_1 THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `base = (g:real^3->real^3) t`)) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_REFL; VECTOR_MUL_LZERO; VECTOR_ADD_LID; VECTOR_MUL_LID] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `base = (g:real^3->real^3) t`)) THEN
    EXPAND_TAC "base" THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH; REAL_MUL_RZERO; REAL_ADD_RID; REAL_MUL_RID] THEN
    EXPAND_TAC "sg" THEN UNDISCH_TAC `~(kap = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [EXISTS_TAC `rho % (t:real^3)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(sch5_radinv (eta / &2) o (G':real^3->real^3)) y = rho % t` SUBST1_TAC THENL
   [UNDISCH_TAC `((G:real^3->real^3) o sch5_radial (eta / &2)) (rho % t) = y` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [sch_neck] o check (fun th ->
      can (term_match [] `sch_neck ((G:real^3->real^3) o sch5_radial (eta / &2)) f`) (concl th))) THEN
    REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The field of the cancellation chart.  SCH5V_PANCAKE_FIELD of              *)
(* pc_sch_vflow with one more conclusion: on the 2d-neighbourhood of C the   *)
(* field is exactly basis 3 + sch5v_hfield g' (the cutoff is 1 there).       *)
(* ------------------------------------------------------------------------- *)

let SCHY_PANCAKE_FIELD_X = prove
 (`!(g:real^3->real^3) g' C K0 D.
     sch_neck g g' /\ compact C /\ C SUBSET sch5v_oh g g' /\
     C SUBSET IMAGE g (sphere(vec 0,&1)) /\ compact K0 /\
     IMAGE g (sphere(vec 0,&1)) INTER K0 SUBSET C /\ &0 < D
     ==> ?v B d e.
           smooth_map_on (:real^3) v /\ (!y. ode_vf_maxint v (:real^3) y = (:real^1)) /\
           (!y. norm(v y) <= B) /\ (!y. (v y)$3 = &1) /\
           &0 < d /\ &0 < e /\
           (!x. ~(?y. y IN C /\ dist(y,x) < D) ==> v x = basis 3) /\
           (!x. (?y. y IN C /\ dist(y,x) < &2 * d) ==> v x = basis 3 + sch5v_hfield g' x) /\
           (!x t. (!u. u IN interval[vec 0,t] UNION interval[t,vec 0]
                       ==> ?y. y IN C /\ dist(y,ode_vf_flow v (:real^3) u x) < &2 * d)
                  ==> norm(g'(ode_vf_flow v (:real^3) t x)) pow 2 = norm(g' x) pow 2) /\
           (!x. (?y. y IN C /\ dist(y,x) < &2 * d) ==> x IN IMAGE g (annulus (&1 / &2) (&2))) /\
           (!p q. p IN IMAGE g (sphere(vec 0,&1)) /\ q IN K0 /\ dist(p,q) < e
                  ==> ?y. y IN C /\ dist(y,p) < d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`C:real^3->bool`; `sch5v_oh (g:real^3->real^3) g'`; `D:real`] SCH5V_CUTOFF) THEN
  ASM_SIMP_TAC[SCH5V_OH_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (X_CHOOSE_THEN `chi:real^3->real`
    (X_CHOOSE_THEN `L:real^3->bool` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `chi:real^3->real`; `L:real^3->bool`]
    SCH5V_FIELD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_TAC `B:real`)
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "OFFL") (LABEL_TAC "DOT"))))) THEN
  SUBGOAL_THEN `sch5v_oh (g:real^3->real^3) g' SUBSET IMAGE g (annulus (&1 / &2) (&2))`
  ASSUME_TAC THENL [REWRITE_TAC[sch5v_oh] THEN SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (g:real^3->real^3) (sphere(vec 0,&1))`; `K0:real^3->bool`;
                 `{x:real^3 | ?y. y IN C /\ dist(y,x) < d1 / &2}`] SCH5V_NEAR_COMPACT) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `&0`] SCH5V_SURFACE_COMPACT) THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; SCH5V_OPEN_NBHD] THEN DISCH_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `C:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[DIST_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC
   [`\x:real^3. basis 3 + (chi:real^3->real) x % sch5v_hfield (g':real^3->real^3) x`;
    `B:real`; `d1 / &2`; `e:real`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!y. ode_vf_maxint (\x:real^3. basis 3 + (chi:real^3->real) x %
                                    sch5v_hfield (g':real^3->real^3) x) (:real^3) y = (:real^1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SCH5V_BOUNDED_COMPLETE THEN EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_ARITH `&2 * d1 / &2 = d1`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN USE_THEN "OFFL" MATCH_MP_TAC THEN
    ASM_MESON_TAC[];
    X_GEN_TAC `x:real^3` THEN DISCH_THEN(X_CHOOSE_THEN `y0:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(chi:real^3->real) x = &1` (fun th -> REWRITE_TAC[th; VECTOR_MUL_LID]) THEN
    ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`x:real^3`; `t:real^1`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\x:real^3. basis 3 + (chi:real^3->real) x % sch5v_hfield (g':real^3->real^3) x`;
                   `\z:real^3. lift(norm((g':real^3->real^3) z) pow 2)`;
                   `{x:real^3 | ?y. y IN C /\ dist(y,x) < d1}`; `x:real^3`; `t:real^1`]
      SCH5V_FLOW_FIRST_INTEGRAL) THEN
    REWRITE_TAC[LIFT_EQ] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[SCH5V_OPEN_NBHD; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^3` THEN DISCH_THEN(X_CHOOSE_THEN `y0:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(chi:real^3->real) z = &1 /\ z IN sch5v_oh (g:real^3->real^3) g'`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `z:real^3`]
      SCH5V_RHO_HAS_DERIVATIVE) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN USE_THEN "DOT" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^3` THEN DISCH_THEN(X_CHOOSE_THEN `y0:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(x:real^3) IN sch5v_oh (g:real^3->real^3) g'` MP_TAC THENL
     [ASM_MESON_TAC[]; ASM SET_TAC[]]]);;

(* The planar chart of the disc bounded by C, a compact set K0 containing    *)
(* the disc and its thin collar at height a with S INTER K0 = C, and the    *)
(* distance of the axis part of the disc from C.                             *)



(* ------------------------------------------------------------------------- *)
(* The coordinates Pi(x) = (x1^2 - x2^2, 2 x1 x2, x3), that is               *)
(* U = u^2 for u = x1 + i x2, injective on x1 < 0.  The field V0 with        *)
(* DPi(V0) = (1,0,1), and flows whose Pi-image is a straight line.           *)
(* ------------------------------------------------------------------------- *)

let schy_pi = new_definition
 `schy_pi (x:real^3) = vector[x$1 pow 2 - x$2 pow 2; &2 * x$1 * x$2; x$3]:real^3`;;

let schy_pib = new_definition
 `schy_pib (x:real^3) (y:real^3) =
    vector[x$1 * y$1 - x$2 * y$2; x$1 * y$2 + x$2 * y$1; &0]:real^3`;;

let schy_v0 = new_definition
 `schy_v0 (x:real^3) =
    vector[x$1 / (&2 * (x$1 pow 2 + x$2 pow 2));
           --(x$2) / (&2 * (x$1 pow 2 + x$2 pow 2)); &1]:real^3`;;

let SCHY_PIB_BILINEAR = prove
 (`bilinear schy_pib`,
  REWRITE_TAC[bilinear; linear; schy_pib; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
              VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  REPEAT STRIP_TAC THEN REAL_ARITH_TAC);;

let SCHY_PI_EQ = prove
 (`schy_pi = (\y:real^3. schy_pib y y + vector[&0; &0; y$3])`,
  REWRITE_TAC[FUN_EQ_THM; schy_pi; schy_pib; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
              VECTOR_ADD_COMPONENT] THEN REAL_ARITH_TAC);;

let SCHY_E3_LINEAR = prove
 (`linear (\y:real^3. vector[&0; &0; y$3]:real^3)`,
  REWRITE_TAC[linear; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC);;

let SCHY_PI_DERIV = prove
 (`!x:real^3.
     (schy_pi has_derivative
      (\h. vector[&2 * (x$1 * h$1 - x$2 * h$2); &2 * (x$1 * h$2 + x$2 * h$1); h$3]:real^3))
     (at x)`,
  GEN_TAC THEN REWRITE_TAC[SCHY_PI_EQ] THEN
  SUBGOAL_THEN
   `(\h:real^3. vector[&2 * (x$1 * h$1 - x$2 * h$2); &2 * (x$1 * h$2 + x$2 * h$1); h$3]:real^3) =
    (\h. (schy_pib x h + schy_pib h x) + vector[&0; &0; h$3])` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; schy_pib; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
                VECTOR_ADD_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`schy_pib`; `\y:real^3. y`; `\y:real^3. y`; `\h:real^3. h`; `\h:real^3. h`;
                   `x:real^3`] HAS_DERIVATIVE_BILINEAR_AT) THEN
    REWRITE_TAC[HAS_DERIVATIVE_ID; SCHY_PIB_BILINEAR];
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[SCHY_E3_LINEAR]]);;

let SCHY_PI_FD = prove
 (`!x h:real^3.
     frechet_derivative schy_pi (at x) h =
     vector[&2 * (x$1 * h$1 - x$2 * h$2); &2 * (x$1 * h$2 + x$2 * h$1); h$3]:real^3`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT (SPEC `x:real^3` SCHY_PI_DERIV))]);;

let SCHY_PI_SMOOTH = prove
 (`smooth_map_on (:real^3) schy_pi`,
  REWRITE_TAC[SCHY_PI_EQ] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
  REWRITE_TAC[OPEN_UNIV] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`(:real^3)`; `schy_pib`; `\y:real^3. y`; `\y:real^3. y`]
      SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
    REWRITE_TAC[OPEN_UNIV; SCHY_PIB_BILINEAR; SMOOTH_MAP_ON_ID];
    MP_TAC(ISPECL [`(:real^3)`; `\y:real^3. y`; `\y:real^3. vector[&0; &0; y$3]:real^3`]
      SMOOTH_MAP_ON_LINEAR_O) THEN
    REWRITE_TAC[SMOOTH_MAP_ON_ID; OPEN_UNIV; SCHY_E3_LINEAR; o_DEF]]);;

let SCHY_PI_INJ = prove
 (`!x y:real^3. x$1 < &0 /\ y$1 < &0 /\ schy_pi x = schy_pi y ==> x = y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[schy_pi; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN STRIP_TAC THEN
  SUBGOAL_THEN `((x:real^3)$1 pow 2 + x$2 pow 2) pow 2 = ((y:real^3)$1 pow 2 + y$2 pow 2) pow 2`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[REAL_ARITH
      `(a pow 2 + b pow 2) pow 2 = (a pow 2 - b pow 2) pow 2 + (&2 * a * b) pow 2`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3)$1 pow 2 + x$2 pow 2 = (y:real^3)$1 pow 2 + y$2 pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPEC `2` REAL_POW_EQ) THEN ASM_REWRITE_TAC[ARITH] THEN CONJ_TAC THENL
     [MP_TAC(SPEC `(x:real^3)$1` REAL_LE_POW_2) THEN MP_TAC(SPEC `(x:real^3)$2` REAL_LE_POW_2) THEN
      REAL_ARITH_TAC;
      MP_TAC(SPEC `(y:real^3)$1` REAL_LE_POW_2) THEN MP_TAC(SPEC `(y:real^3)$2` REAL_LE_POW_2) THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3)$1 pow 2 = (y:real^3)$1 pow 2` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^3)$1 pow 2 + x$2 pow 2 = (y:real^3)$1 pow 2 + y$2 pow 2` THEN
    UNDISCH_TAC `(x:real^3)$1 pow 2 - x$2 pow 2 = (y:real^3)$1 pow 2 - y$2 pow 2` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3)$1 = (y:real^3)$1` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^3)$1 pow 2 = (y:real^3)$1 pow 2` THEN
    REWRITE_TAC[GSYM REAL_EQ_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `&2 * (x:real^3)$1 * x$2 = &2 * (y:real^3)$1 * y$2` THEN
  ASM_REWRITE_TAC[REAL_EQ_MUL_LCANCEL; REAL_OF_NUM_EQ; ARITH] THEN
  ASM_SIMP_TAC[REAL_ARITH `y < &0 ==> ~(y = &0)`]);;

let SCHY_PI_V0 = prove
 (`!x:real^3. ~(x$1 pow 2 + x$2 pow 2 = &0)
              ==> frechet_derivative schy_pi (at x) (schy_v0 x) = vector[&1; &0; &1]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SCHY_PI_FD; schy_v0; VECTOR_3] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
  UNDISCH_TAC `~((x:real^3)$1 pow 2 + x$2 pow 2 = &0)` THEN CONV_TAC REAL_FIELD);;

let SCHY_PI_E3 = prove
 (`!x:real^3. frechet_derivative schy_pi (at x) (basis 3) = vector[&0; &0; &1]`,
  SIMP_TAC[SCHY_PI_FD; BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN REAL_ARITH_TAC);;

let SCHY_PI_DINJ = prove
 (`!x h k:real^3.
     ~(x$1 pow 2 + x$2 pow 2 = &0) /\
     frechet_derivative schy_pi (at x) h = frechet_derivative schy_pi (at x) k
     ==> h = k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SCHY_PI_FD; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `((x:real^3)$1 pow 2 + x$2 pow 2) * ((h:real^3)$1 - (k:real^3)$1) = &0 /\
                ((x:real^3)$1 pow 2 + x$2 pow 2) * ((h:real^3)$2 - (k:real^3)$2) = &0`
  MP_TAC THENL
   [UNDISCH_TAC `&2 * ((x:real^3)$1 * (h:real^3)$1 - x$2 * h$2) =
                 &2 * (x$1 * (k:real^3)$1 - x$2 * k$2)` THEN
    UNDISCH_TAC `&2 * ((x:real^3)$1 * (h:real^3)$2 + x$2 * h$1) =
                 &2 * (x$1 * (k:real^3)$2 + x$2 * k$1)` THEN
    CONV_TAC REAL_RING;
    ASM_REWRITE_TAC[REAL_ENTIRE] THEN REAL_ARITH_TAC]);;

let SCHY_FLOW_PI = prove
 (`!(v:real^3->real^3) x t.
     smooth_map_on (:real^3) v /\ (!y. ode_vf_maxint v (:real^3) y = (:real^1)) /\
     (!s. s IN segment[vec 0,t]
          ==> frechet_derivative schy_pi (at (ode_vf_flow v (:real^3) s x))
                (v(ode_vf_flow v (:real^3) s x)) = vector[&1; &0; &1])
     ==> schy_pi(ode_vf_flow v (:real^3) t x) = schy_pi x + drop t % vector[&1; &0; &1]`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D"))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH5V_FLOW_FACTS o CONJ
    (ASSUME `smooth_map_on (:real^3) (v:real^3->real^3)`)) THEN
  MP_TAC(ISPECL [`\s:real^1. schy_pi(ode_vf_flow (v:real^3->real^3) (:real^3) s x) -
                             drop s % vector[&1; &0; &1]:real^3`;
                 `segment[vec 0:real^1,t]`; `vec 0:real^1`; `schy_pi x`]
    HAS_DERIVATIVE_ZERO_UNIQUE) THEN
  REWRITE_TAC[CONVEX_SEGMENT; ENDS_IN_SEGMENT] THEN
  ASM_REWRITE_TAC[DROP_VEC; VECTOR_MUL_LZERO; VECTOR_SUB_RZERO] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
    SUBGOAL_THEN `(\h:real^1. vec 0:real^3) = (\h. drop h % (vector[&1; &0; &1] - vector[&1; &0; &1]))`
    SUBST1_TAC THENL [REWRITE_TAC[VECTOR_SUB_REFL; VECTOR_MUL_RZERO]; ALL_TAC] THEN
    REWRITE_TAC[GSYM has_vector_derivative] THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN
    CONJ_TAC THENL
     [USE_THEN "D" (fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM(MATCH_MP th
        (ASSUME `(s:real^1) IN segment[vec 0,t]`))]) THEN
      MP_TAC(ISPECL [`schy_pi`; `\s:real^1. ode_vf_flow (v:real^3->real^3) (:real^3) s x`;
                     `(v:real^3->real^3)(ode_vf_flow v (:real^3) s x)`; `s:real^1`]
        SCHY_CURVE_CHAIN) THEN
      ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
      MESON_TAC[SCHY_PI_DERIV; differentiable];
      REWRITE_TAC[has_vector_derivative] THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
      MP_TAC(ISPECL [`\s:real^1. s`; `vector[&1; &0; &1]:real^3`] LINEAR_VMUL_DROP) THEN
      REWRITE_TAC[LINEAR_ID]];
    DISCH_THEN(MP_TAC o SPEC `t:real^1`) THEN REWRITE_TAC[ENDS_IN_SEGMENT] THEN
    VECTOR_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The gradient and the horizontal field of a neck whose layers              *)
(* are the vertical translates of z = x1^2 - x2^2: there the field          *)
(* basis 3 + sch5v_hfield g' is V0 (schy_v0), and DPi maps it to (1,0,1).   *)
(* ------------------------------------------------------------------------- *)

let schy_ell = new_definition
 `schy_ell (z:real^3) = lift(z$3 - z$1)`;;

let SCHY_ELL_LINEAR = prove
 (`linear schy_ell`,
  REWRITE_TAC[linear; schy_ell; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
              GSYM LIFT_ADD; GSYM LIFT_CMUL; LIFT_EQ] THEN REAL_ARITH_TAC);;

let SCHY_SIGMA_LIFT = prove
 (`!y:real^3. lift(y$3 - (y$1 pow 2 - y$2 pow 2)) = schy_ell(schy_pi y)`,
  REWRITE_TAC[schy_ell; schy_pi; VECTOR_3]);;

let SCHY_TN_GRAD = prove
 (`!(g':real^3->real^3) K N x.
     ~(K = &0) /\ open N /\ x IN N /\
     (!y. y IN N ==> norm(g' y) pow 2 = (&1 + (y$3 - (y$1 pow 2 - y$2 pow 2)) / K) pow 2)
     ==> sch5v_grad g' x =
         (&2 * (&1 + (x$3 - (x$1 pow 2 - x$2 pow 2)) / K) / K) %
         vector[--(&2 * x$1); &2 * x$2; &1]`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `sg = (x:real^3)$3 - (x$1 pow 2 - x$2 pow 2)` THEN
  ABBREV_TAC `kk = &2 * (&1 + sg / K) / K` THEN
  SUBGOAL_THEN `((\t:real. (&1 + t / K) pow 2) has_real_derivative kk) (atreal sg)`
  ASSUME_TAC THENL
   [EXPAND_TAC "kk" THEN REAL_DIFF_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[REAL_POW_1] THEN UNDISCH_TAC `~(K = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((lift o (\t:real. (&1 + t / K) pow 2) o drop) o schy_ell o schy_pi has_derivative
     (\h. kk % h) o schy_ell o
     (\h:real^3. vector[&2 * (x$1 * h$1 - x$2 * h$2); &2 * (x$1 * h$2 + x$2 * h$1); h$3]:real^3))
    (at x)` ASSUME_TAC THENL
   [MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIFF_CHAIN_AT THEN REWRITE_TAC[SCHY_PI_DERIV] THEN
      MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[SCHY_ELL_LINEAR];
      REWRITE_TAC[o_THM; GSYM SCHY_SIGMA_LIFT] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM HAS_REAL_FRECHET_DERIVATIVE_AT] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\y. lift(norm((g':real^3->real^3) y) pow 2)) has_derivative
     (\h. kk % h) o schy_ell o
     (\h:real^3. vector[&2 * (x$1 * h$1 - x$2 * h$2); &2 * (x$1 * h$2 + x$2 * h$1); h$3]:real^3))
    (at x)` ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    EXISTS_TAC `(lift o (\t:real. (&1 + t / K) pow 2) o drop) o schy_ell o schy_pi` THEN
    EXISTS_TAC `N:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    REWRITE_TAC[o_THM; GSYM SCHY_SIGMA_LIFT; LIFT_DROP] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[sch5v_grad] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  SIMP_TAC[o_THM; schy_ell; BASIS_COMPONENT; DIMINDEX_3; ARITH; VECTOR_3;
           DROP_CMUL; LIFT_DROP] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_MUL_COMPONENT] THEN
  REAL_ARITH_TAC);;

let SCHY_TN_V0 = prove
 (`!(g':real^3->real^3) K N x.
     ~(K = &0) /\ open N /\ x IN N /\
     (!y. y IN N ==> norm(g' y) pow 2 = (&1 + (y$3 - (y$1 pow 2 - y$2 pow 2)) / K) pow 2) /\
     ~(&1 + (x$3 - (x$1 pow 2 - x$2 pow 2)) / K = &0) /\ ~(x$1 pow 2 + x$2 pow 2 = &0)
     ==> basis 3 + sch5v_hfield g' x = schy_v0 x /\
         ~((sch5v_grad g' x)$1 pow 2 + (sch5v_grad g' x)$2 pow 2 = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[sch5v_hfield] THEN
  MP_TAC(ISPECL [`g':real^3->real^3`; `K:real`; `N:real^3->bool`; `x:real^3`] SCHY_TN_GRAD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `kk = &2 * (&1 + ((x:real^3)$3 - (x$1 pow 2 - x$2 pow 2)) / K) / K` THEN
  SUBGOAL_THEN `~(kk = &0)` ASSUME_TAC THENL
   [EXPAND_TAC "kk" THEN UNDISCH_TAC `~(K = &0)` THEN
    UNDISCH_TAC `~(&1 + ((x:real^3)$3 - (x$1 pow 2 - x$2 pow 2)) / K = &0)` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[schy_v0; VECTOR_MUL_COMPONENT; VECTOR_3] THEN CONJ_TAC THENL
   [SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
             VECTOR_MUL_COMPONENT; BASIS_COMPONENT; ARITH] THEN
    UNDISCH_TAC `~(kk = &0)` THEN UNDISCH_TAC `~((x:real^3)$1 pow 2 + x$2 pow 2 = &0)` THEN
    CONV_TAC REAL_FIELD;
    UNDISCH_TAC `~(kk = &0)` THEN UNDISCH_TAC `~((x:real^3)$1 pow 2 + x$2 pow 2 = &0)` THEN
    CONV_TAC REAL_FIELD]);;

(* ------------------------------------------------------------------------- *)
(* The planar side of C near P0 = (-sqrt e, 0).  Near P0 the                 *)
(* projection J of C is the curve x1^2 - x2^2 = e, and its near side          *)
(* x1^2 - x2^2 < e lies outside J (it is joined to the projection of rpt).   *)
(* ------------------------------------------------------------------------- *)

let SCHY_BRANCH_CONN = prove
 (`!k e b. connected (IMAGE (\t:real^1. vector[k * sqrt(e + drop t pow 2); drop t; e]:real^3)
                            (segment[vec 0,lift b]))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
  REWRITE_TAC[CONNECTED_SEGMENT] THEN
  ONCE_REWRITE_TAC[CONTINUOUS_ON_COMPONENTWISE_LIFT] THEN
  REWRITE_TAC[DIMINDEX_3; FORALL_3; VECTOR_3] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_SQRT_COMPOSE THEN REWRITE_TAC[o_DEF; LIFT_ADD] THEN
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN REWRITE_TAC[LIFT_DROP; CONTINUOUS_ON_ID];
    REWRITE_TAC[LIFT_DROP; CONTINUOUS_ON_ID];
    REWRITE_TAC[CONTINUOUS_ON_CONST]]);;

let SCHY_BRANCH_POINT = prove
 (`!(s:real^3->bool) r e k t.
     schy_chart s r /\ &0 < e /\ e < r /\ e + &2 * t pow 2 < r pow 2 /\ (k = &1 \/ k = -- &1)
     ==> vector[k * sqrt(e + t pow 2); t; e] IN s /\ (vector[k * sqrt(e + t pow 2); t; e]:real^3)$3 = e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "K"))))) THEN
  SUBGOAL_THEN `k pow 2 = &1` ASSUME_TAC THENL
   [USE_THEN "K" (DISJ_CASES_THEN SUBST1_TAC) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[VECTOR_3] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [schy_chart] o check (fun th ->
    can (term_match [] `schy_chart s r`) (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(MP_TAC o SPEC `vector[k * sqrt(e + t pow 2); t; e]:real^3`) THEN
  REWRITE_TAC[VECTOR_3] THEN
  SUBGOAL_THEN `&0 <= e + t pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `t:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(k * sqrt(e + t pow 2)) pow 2 = e + t pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_MUL] THEN ASM_SIMP_TAC[SQRT_POW_2; REAL_MUL_LID];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REAL_ARITH_TAC);;

let SCHY_P0_BALL = prove
 (`!e (x:real^2). &0 < e /\ (x$1 + sqrt e) pow 2 + x$2 pow 2 < e
                 ==> x$1 < &0 /\ x$2 pow 2 < e /\ x$1 pow 2 < &4 * e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt e /\ sqrt e pow 2 = e` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `abs((x:real^2)$1 + sqrt e) < sqrt e` ASSUME_TAC THENL
   [SUBGOAL_THEN `abs((x:real^2)$1 + sqrt e) < abs(sqrt e)` MP_TAC THENL
     [REWRITE_TAC[REAL_LT_SQUARE_ABS] THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `(x:real^2)$2` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_ARITH `&0 < s ==> abs s = s`]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MP_TAC(SPEC `(x:real^2)$1 + sqrt e` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `abs((x:real^2)$1) < abs(&2 * sqrt e)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_LT_SQUARE_ABS; REAL_POW_MUL] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let SCHY_SQ_SHRINK = prove
 (`!u a. &0 <= u /\ u <= &1 ==> (u * a) pow 2 <= a pow 2 /\ u pow 2 <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `u pow 2 <= &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_POW_MUL] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]);;

let SCHY_PATH_BOUNDS = prove
 (`!(x:real^2) p e r.
     &0 < e /\ e < r pow 2 /\ x$1 pow 2 + x$2 pow 2 < r pow 2 /\ x$1 pow 2 - x$2 pow 2 < e /\
     p IN segment[x,vector[&0; x$2]] UNION segment[vector[&0; x$2],vec 0] UNION
          segment[vec 0,vector[sqrt e; &0]] /\
     ~(p = vector[sqrt e; &0])
     ==> p$1 pow 2 + p$2 pow 2 < r pow 2 /\ p$1 pow 2 - p$2 pow 2 < e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_UNION; IN_SEGMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
  SUBGOAL_THEN `&0 < sqrt e /\ sqrt e pow 2 = e` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID; REAL_ADD_LID] THENL
   [MP_TAC(ISPECL [`&1 - u`; `(x:real^2)$1`] SCHY_SQ_SHRINK) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    REWRITE_TAC[REAL_ARITH `(&1 - u) * a + u * a = a:real`] THEN ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`&1 - u`; `(x:real^2)$2`] SCHY_SQ_SHRINK) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MP_TAC(SPEC `(x:real^2)$1` REAL_LE_POW_2) THEN
    MP_TAC(SPEC `(&1 - u) * (x:real^2)$2` REAL_LE_POW_2) THEN
    REWRITE_TAC[REAL_POW_2; REAL_MUL_LZERO] THEN
    REWRITE_TAC[GSYM REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`u:real`; `sqrt e`] SCHY_SQ_SHRINK) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `u < &1` ASSUME_TAC THENL
     [UNDISCH_TAC `~((p:real^2)$1 = sqrt e /\ p$2 = &0)` THEN
      ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID] THEN
      ASM_CASES_TAC `u = &1` THEN ASM_REWRITE_TAC[REAL_MUL_LID] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(u * sqrt e) pow 2 < e` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_POW_MUL] THEN ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LT_RMUL THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_1_LT THEN ASM_REWRITE_TAC[ARITH] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_RID; REAL_SUB_RZERO] THEN
    REWRITE_TAC[GSYM REAL_POW_2] THEN ASM_REAL_ARITH_TAC]);;

let SCHY_SIDE = prove
 (`!(g:real^3->real^3) r e C.
     schy_chart (IMAGE g (sphere(vec 0,&1))) r /\ &0 < e /\ &16 * e < r pow 2 /\
     C IN components(sch_level g e) /\ schy_lpt e IN C /\ ~(schy_rpt e IN C) /\
     (!x:real^2. x IN inside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C)
                 ==> ~((vector[x$1; x$2; e]:real^3) IN IMAGE g (sphere(vec 0,&1))))
     ==> !x:real^2. (x$1 + sqrt e) pow 2 + x$2 pow 2 < e
                    ==> (x IN IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C <=>
                         x$1 pow 2 - x$2 pow 2 = e) /\
                        (x$1 pow 2 - x$2 pow 2 < e
                         ==> x IN outside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `S = IMAGE (g:real^3->real^3) (sphere(vec 0,&1))` THEN
  ABBREV_TAC `J = IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C` THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [schy_chart] o check (fun th ->
    can (term_match [] `schy_chart s r`) (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CH"))) THEN
  SUBGOAL_THEN `r pow 2 < r` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `x = r * r /\ r * r < r * &1 ==> x < r`) THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt e /\ sqrt e pow 2 = e /\ e < r` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `C SUBSET sch_level (g:real^3->real^3) e` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN C ==> y IN S /\ y$3 = e` (LABEL_TAC "CL") THENL
   [UNDISCH_TAC `C SUBSET sch_level (g:real^3->real^3) e` THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[SUBSET; sch_level; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p:real^2. p IN J <=> (vector[p$1; p$2; e]:real^3) IN C` (LABEL_TAC "PJ") THENL
   [GEN_TAC THEN EXPAND_TAC "J" THEN REWRITE_TAC[IN_IMAGE] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
      USE_THEN "CL" (fun th -> MP_TAC(MP (SPEC `y:real^3` th) (ASSUME `(y:real^3) IN C`))) THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `vector[(p:real^2)$1; p$2; e]:real^3 = y` (fun th -> ASM_REWRITE_TAC[th]) THEN
      ASM_REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_2];
      DISCH_TAC THEN EXISTS_TAC `vector[(p:real^2)$1; p$2; e]:real^3` THEN
      ASM_REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_3; VECTOR_2]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p:real^2. p$1 pow 2 + p$2 pow 2 < r pow 2 /\ (vector[p$1; p$2; e]:real^3) IN C
                           ==> p$1 pow 2 - p$2 pow 2 = e` (LABEL_TAC "CF") THENL
   [GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "CL" (fun th -> MP_TAC(MP (SPEC `vector[(p:real^2)$1; p$2; e]:real^3` th)
      (ASSUME `(vector[(p:real^2)$1; p$2; e]:real^3) IN C`))) THEN
    REWRITE_TAC[VECTOR_3] THEN STRIP_TAC THEN
    USE_THEN "CH" (MP_TAC o SPEC `vector[(p:real^2)$1; p$2; e]:real^3`) THEN
    REWRITE_TAC[VECTOR_3] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k t. (k = &1 \/ k = -- &1) /\ e + &2 * t pow 2 < r pow 2
                      ==> IMAGE (\s:real^1. vector[k * sqrt(e + drop s pow 2); drop s; e]:real^3)
                                (segment[vec 0,lift t]) SUBSET sch_level (g:real^3->real^3) e`
  (LABEL_TAC "BR") THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; sch_level; IN_ELIM_THM] THEN
    X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `p /\ q ==> p /\ q`) THEN
    MP_TAC(ISPECL [`S:real^3->bool`; `r:real`; `e:real`; `k:real`; `drop s`] SCHY_BRANCH_POINT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `drop s pow 2 <= t pow 2` MP_TAC THENL
       [UNDISCH_TAC `(s:real^1) IN segment[vec 0,lift t]` THEN
        REWRITE_TAC[IN_SEGMENT; VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
        DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[DROP_CMUL; LIFT_DROP; REAL_POW_MUL] THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
        MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC];
      EXPAND_TAC "S" THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. e + &2 * t pow 2 < r pow 2
                    ==> (vector[--(sqrt(e + t pow 2)); t; e]:real^3) IN C` (LABEL_TAC "LB") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`sch_level (g:real^3->real^3) e`;
                   `IMAGE (\s:real^1. vector[-- &1 * sqrt(e + drop s pow 2); drop s; e]:real^3)
                          (segment[vec 0,lift t])`; `C:real^3->bool`] COMPONENTS_MAXIMAL) THEN
    ASM_REWRITE_TAC[SCHY_BRANCH_CONN] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [USE_THEN "BR" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `schy_lpt e` THEN
      ASM_REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 0:real^1` THEN
      REWRITE_TAC[ENDS_IN_SEGMENT; schy_lpt; DROP_VEC] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_ADD_RID; REAL_MUL_LNEG; REAL_MUL_LID];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      DISCH_THEN(MP_TAC o SPEC `lift t`) THEN
      REWRITE_TAC[ENDS_IN_SEGMENT; LIFT_DROP; REAL_MUL_LNEG; REAL_MUL_LID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. e + &2 * t pow 2 < r pow 2
                    ==> ~((vector[sqrt(e + t pow 2); t; e]:real^3) IN C)` (LABEL_TAC "RB") THENL
   [GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`sch_level (g:real^3->real^3) e`;
                   `IMAGE (\s:real^1. vector[&1 * sqrt(e + drop s pow 2); drop s; e]:real^3)
                          (segment[vec 0,lift t])`; `C:real^3->bool`] COMPONENTS_MAXIMAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[SCHY_BRANCH_CONN] THEN CONJ_TAC THENL
       [USE_THEN "BR" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `vector[sqrt(e + t pow 2); t; e]:real^3` THEN
      ASM_REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `lift t` THEN
      REWRITE_TAC[ENDS_IN_SEGMENT; LIFT_DROP; REAL_MUL_LID];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      DISCH_THEN(MP_TAC o SPEC `vec 0:real^1`) THEN
      REWRITE_TAC[ENDS_IN_SEGMENT; DROP_VEC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[REAL_ADD_RID; REAL_MUL_LID] THEN
      UNDISCH_TAC `~(schy_rpt e IN C)` THEN REWRITE_TAC[schy_rpt] THEN MESON_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`e:real`; `x:real^2`] SCHY_P0_BALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(x:real^2)$1 pow 2 + x$2 pow 2 < r pow 2 /\ e + &2 * x$2 pow 2 < r pow 2`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `x IN (J:real^2->bool) <=> x$1 pow 2 - x$2 pow 2 = e` ASSUME_TAC THENL
   [USE_THEN "PJ" (fun th -> REWRITE_TAC[th]) THEN EQ_TAC THENL
     [DISCH_TAC THEN USE_THEN "CF" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN
      SUBGOAL_THEN `(x:real^2)$1 = --(sqrt(e + x$2 pow 2))` SUBST1_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `x1 < &0 /\ abs x1 = s ==> x1 = --s`) THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SQRT_UNIQUE THEN
        REWRITE_TAC[REAL_ABS_POS; REAL_POW2_ABS] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[] THEN USE_THEN "LB" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `vector[sqrt e; &0]:real^2 IN outside J` ASSUME_TAC THENL
   [MP_TAC(ISPEC `J:real^2->bool` INSIDE_UNION_OUTSIDE) THEN
    REWRITE_TAC[EXTENSION; IN_UNION; IN_DIFF; IN_UNIV] THEN
    DISCH_THEN(MP_TAC o SPEC `vector[sqrt e; &0]:real^2`) THEN
    MATCH_MP_TAC(TAUT `~a /\ ~c ==> (a \/ b <=> ~c) ==> b`) THEN CONJ_TAC THENL
     [DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `vector[sqrt e; &0]:real^2` o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "inside")) (concl th))) THEN
      ASM_REWRITE_TAC[VECTOR_2] THEN
      MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`] SCHY_BRANCH_IN_LEVEL) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[sch_level; IN_ELIM_THM; schy_rpt] THEN
      EXPAND_TAC "S" THEN SIMP_TAC[];
      USE_THEN "PJ" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "RB" (MP_TAC o SPEC `&0`) THEN
      REWRITE_TAC[VECTOR_2; REAL_POW_2; REAL_MUL_LZERO; REAL_ADD_RID; REAL_MUL_RZERO] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `P = segment[x,vector[&0; x$2]:real^2] UNION
                  segment[vector[&0; x$2],vec 0] UNION segment[vec 0,vector[sqrt e; &0]]` THEN
  SUBGOAL_THEN `connected(P:real^2->bool) /\ x IN P /\ vector[sqrt e; &0]:real^2 IN P`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_UNION THEN REWRITE_TAC[CONNECTED_SEGMENT] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONNECTED_UNION THEN REWRITE_TAC[CONNECTED_SEGMENT] THEN
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
        EXISTS_TAC `vec 0:real^2` THEN REWRITE_TAC[ENDS_IN_SEGMENT];
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_UNION] THEN
        EXISTS_TAC `vector[&0; (x:real^2)$2]:real^2` THEN REWRITE_TAC[ENDS_IN_SEGMENT]];
      REWRITE_TAC[IN_UNION; ENDS_IN_SEGMENT];
      REWRITE_TAC[IN_UNION; ENDS_IN_SEGMENT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(P:real^2->bool) SUBSET (:real^2) DIFF J` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIV] THEN X_GEN_TAC `p:real^2` THEN DISCH_TAC THEN
    ASM_CASES_TAC `p = vector[sqrt e; &0]:real^2` THENL
     [UNDISCH_TAC `p = vector[sqrt e; &0]:real^2` THEN DISCH_THEN SUBST1_TAC THEN
      MP_TAC(ISPEC `J:real^2->bool` OUTSIDE_NO_OVERLAP) THEN
      MP_TAC(ASSUME `vector[sqrt e; &0]:real^2 IN outside J`) THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(p:real^2)$1 pow 2 + p$2 pow 2 < r pow 2 /\ p$1 pow 2 - p$2 pow 2 < e`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC SCHY_PATH_BOUNDS THEN EXISTS_TAC `x:real^2` THEN
      UNDISCH_TAC `(p:real^2) IN P` THEN EXPAND_TAC "P" THEN DISCH_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN
    USE_THEN "CF" (MP_TAC o SPEC `p:real^2`) THEN
    USE_THEN "PJ" (fun th -> REWRITE_TAC[GSYM th]) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC OUTSIDE_SAME_COMPONENT THEN EXISTS_TAC `vector[sqrt e; &0]:real^2` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(P:real^2->bool) SUBSET connected_component ((:real^2) DIFF J) (vector[sqrt e; &0])`
  MP_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN
    ASM_REWRITE_TAC[IN]]);;

(* ------------------------------------------------------------------------- *)
(* The planar chart near the model point -e1.  If c maps the                 *)
(* circle to J, the disc to inside J and -e1 to P0, then near -e1 the field  *)
(* Dc^-1(hf) (hf = the horizontal part of V0) points into the disc.         *)
(* ------------------------------------------------------------------------- *)

let schy_f2b = new_definition
 `schy_f2b (x:real^2) (y:real^2) = lift(x$1 * y$1 - x$2 * y$2)`;;

let schy_hf2 = new_definition
 `schy_hf2 (x:real^2) =
    vector[x$1 / (&2 * (x$1 pow 2 + x$2 pow 2)); --(x$2) / (&2 * (x$1 pow 2 + x$2 pow 2))]:real^2`;;

let SCHY_F2B_BILINEAR = prove
 (`bilinear schy_f2b`,
  REWRITE_TAC[bilinear; linear; schy_f2b; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
              GSYM LIFT_ADD; GSYM LIFT_CMUL; LIFT_EQ] THEN
  REPEAT STRIP_TAC THEN REAL_ARITH_TAC);;

let SCHY_F2_DERIV = prove
 (`!x:real^2. ((\y. lift(y$1 pow 2 - y$2 pow 2)) has_derivative
               (\h. lift(&2 * x$1 * h$1 - &2 * x$2 * h$2))) (at x)`,
  GEN_TAC THEN
  SUBGOAL_THEN `(\y:real^2. lift(y$1 pow 2 - y$2 pow 2)) = (\y. schy_f2b y y) /\
                (\h:real^2. lift(&2 * x$1 * h$1 - &2 * x$2 * h$2)) =
                (\h. schy_f2b x h + schy_f2b h x)` (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[FUN_EQ_THM; schy_f2b; GSYM LIFT_ADD; LIFT_EQ] THEN CONJ_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`schy_f2b`; `\y:real^2. y`; `\y:real^2. y`; `\h:real^2. h`; `\h:real^2. h`;
                 `x:real^2`] HAS_DERIVATIVE_BILINEAR_AT) THEN
  REWRITE_TAC[HAS_DERIVATIVE_ID; SCHY_F2B_BILINEAR]);;

let SCHY_BALL_INV_DERIV = prove
 (`!(c:real^2->real^2) c' z k.
     sch_ball c c' /\ z IN ball(vec 0,&2)
     ==> frechet_derivative c (at z) (frechet_derivative c' (at (c z)) k) = k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch_ball] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIFFEOMORPHISM_ON_SYM) THEN
  MP_TAC(ISPECL [`IMAGE (c:real^2->real^2) (ball(vec 0,&2))`; `ball(vec 0:real^2,&2)`;
                 `c':real^2->real^2`; `c:real^2->real^2`; `(c:real^2->real^2) z`; `k:real^2`]
    SCH4_DIFFEO_DERIV_INV) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
  UNDISCH_TAC `diffeomorphism_on (ball(vec 0,&2)) (IMAGE c (ball(vec 0,&2)))
                 (c:real^2->real^2) c'` THEN
  REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN ASM_SIMP_TAC[]);;

let SCHY_SQUEEZE = prove
 (`!p q. (!l. &0 < l /\ l <= &1 ==> abs q <= l * --p) ==> q = &0`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `q = &0` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < abs q` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * (abs p + abs q)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `abs q / (&2 * (abs p + abs q))`) THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV; REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `a / b * c = (a * c) / b`] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  SUBGOAL_THEN `&0 <= abs q * abs p /\ &0 < abs q * abs q /\ abs q * --p <= abs q * abs p`
  MP_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN REAL_ARITH_TAC];
    REAL_ARITH_TAC]);;

let SCHY_BASIS2_EXPAND = prove
 (`!(L:real^2->real^2) k. linear L ==> L k = k$1 % L(basis 1) + k$2 % L(basis 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `k:real^2 = k$1 % basis 1 + k$2 % basis 2` (fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
   [SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
             BASIS_COMPONENT; ARITH] THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL]]);;

let SCHY_CHART_DERIV_SIGN = prove
 (`!(c:real^2->real^2) c' J e.
     sch_ball c c' /\ IMAGE c (sphere(vec 0,&1)) = J /\ IMAGE c (ball(vec 0,&1)) = inside J /\
     c(--basis 1) = vector[--(sqrt e); &0] /\ &0 < e /\
     (!x:real^2. (x$1 + sqrt e) pow 2 + x$2 pow 2 < e
                 ==> (x IN J <=> x$1 pow 2 - x$2 pow 2 = e) /\
                     (x$1 pow 2 - x$2 pow 2 < e ==> x IN outside J))
     ==> (frechet_derivative c' (at (vector[--(sqrt e); &0])) (basis 1))$1 < &0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SIDE")))))) THEN
  SUBGOAL_THEN `&0 < sqrt e /\ sqrt e pow 2 = e` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `--basis 1:real^2 IN ball(vec 0,&2) /\ --basis 1:real^2 IN cball(vec 0,&1)`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[IN_BALL_0; IN_CBALL_0; NORM_NEG; NORM_BASIS; DIMINDEX_2; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (ball(vec 0,&2)) (c:real^2->real^2)` ASSUME_TAC THENL
   [UNDISCH_TAC `sch_ball (c:real^2->real^2) c'` THEN SIMP_TAC[sch_ball; diffeomorphism_on];
    ALL_TAC] THEN
  SUBGOAL_THEN `((c:real^2->real^2) has_derivative frechet_derivative c (at (--basis 1)))
                (at (--basis 1))` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `ball(vec 0:real^2,&2)` THEN ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  ABBREV_TAC `L = frechet_derivative (c:real^2->real^2) (at (--basis 1))` THEN
  SUBGOAL_THEN `linear (L:real^2->real^2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
  SUBGOAL_THEN `?d1. &0 < d1 /\ !w. dist(w,--basis 1) < d1
                                    ==> dist((c:real^2->real^2) w,vector[--(sqrt e); &0]) < sqrt e`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(c:real^2->real^2) continuous (at (--basis 1))` MP_TAC THENL
     [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
      REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `sqrt e`) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^2. w IN cball(vec 0,&1) INTER ball(--basis 1,d1)
                           ==> e <= ((c:real^2->real^2) w)$1 pow 2 - (c w)$2 pow 2`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^2` THEN REWRITE_TAC[IN_INTER; IN_BALL; IN_CBALL_0] THEN STRIP_TAC THEN
    USE_THEN "SIDE" (MP_TAC o SPEC `(c:real^2->real^2) w`) THEN ANTS_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `w:real^2`) THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[dist; NORM_LT_SQUARE; dot; SUM_2; DIMINDEX_2; VECTOR_SUB_COMPONENT;
                  VECTOR_2] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `norm(w:real^2) = &1` THENL
     [SUBGOAL_THEN `(c:real^2->real^2) w IN J` (fun th -> REWRITE_TAC[th]) THENL
       [UNDISCH_TAC `IMAGE (c:real^2->real^2) (sphere(vec 0,&1)) = J` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        ASM_REWRITE_TAC[IN_SPHERE_0];
        REAL_ARITH_TAC];
      SUBGOAL_THEN `(c:real^2->real^2) w IN inside J` ASSUME_TAC THENL
       [UNDISCH_TAC `IMAGE (c:real^2->real^2) (ball(vec 0,&1)) = inside J` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `~((c:real^2->real^2) w IN outside J)` ASSUME_TAC THENL
       [MP_TAC(ISPEC `J:real^2->bool` INSIDE_INTER_OUTSIDE) THEN
        UNDISCH_TAC `(c:real^2->real^2) w IN inside J` THEN SET_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\w:real^2. lift(((c:real^2->real^2) w)$1 pow 2 - (c w)$2 pow 2)`;
                 `\h:real^2. lift(&2 * --(sqrt e) * ((L:real^2->real^2) h)$1 -
                                  &2 * &0 * (L h)$2)`;
                 `--basis 1:real^2`; `cball(vec 0:real^2,&1)`; `d1:real`]
    DROP_DIFFERENTIAL_POS_AT_MINIMUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CONVEX_CBALL; LIFT_DROP] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
      SUBGOAL_THEN `(\w:real^2. lift(((c:real^2->real^2) w)$1 pow 2 - (c w)$2 pow 2)) =
                    (\y. lift(y$1 pow 2 - y$2 pow 2)) o c` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      SUBGOAL_THEN `(\h:real^2. lift(&2 * --(sqrt e) * ((L:real^2->real^2) h)$1 -
                                    &2 * &0 * (L h)$2)) =
                    (\h. lift(&2 * ((c:real^2->real^2)(--basis 1))$1 * h$1 -
                              &2 * (c(--basis 1))$2 * h$2)) o L` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[FUN_EQ_THM; o_THM; VECTOR_2]; ALL_TAC] THEN
      MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[SCHY_F2_DERIV];
      X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `w:real^2` o check (fun th ->
        can (term_match [] `!w:real^2. w IN s ==> e <= f w`) (concl th))) THEN
      ASM_REWRITE_TAC[VECTOR_2; REAL_POW_NEG; ARITH] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_DROP; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_SUB_RZERO] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!y:real^2. y IN cball(vec 0,&1) ==> ((L:real^2->real^2)(y - --basis 1))$1 <= &0`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^2`) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < &2 * sqrt e` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `&2 * --s * x = (&2 * s) * --x`] THEN
    ASM_SIMP_TAC[REAL_LE_MUL_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `p = ((L:real^2->real^2)(basis 1))$1` THEN
  ABBREV_TAC `q = ((L:real^2->real^2)(basis 2))$1` THEN
  SUBGOAL_THEN `!k:real^2. ((L:real^2->real^2) k)$1 = k$1 * p + k$2 * q` ASSUME_TAC THENL
   [GEN_TAC THEN MP_TAC(ISPECL [`L:real^2->real^2`; `k:real^2`] SCHY_BASIS2_EXPAND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    EXPAND_TAC "p" THEN EXPAND_TAC "q" THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p <= &0` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `vec 0:real^2` o check (fun th ->
      can (term_match [] `!y:real^2. y IN s ==> P y`) (concl th))) THEN
    ASM_REWRITE_TAC[CENTRE_IN_CBALL; REAL_POS; VECTOR_SUB_LZERO; VECTOR_NEG_NEG] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `q = &0` ASSUME_TAC THENL
   [MATCH_MP_TAC SCHY_SQUEEZE THEN EXISTS_TAC `p:real` THEN X_GEN_TAC `l:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `!s. s = l \/ s = --l ==> l pow 2 * p + s * q <= &0` MP_TAC THENL
     [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `--basis 1 + vector[l pow 2; s]:real^2` o check (fun th ->
        can (term_match [] `!y:real^2. y IN s ==> P y`) (concl th))) THEN
      ASM_REWRITE_TAC[VECTOR_ARITH `(a + b) - a:real^N = b`; VECTOR_2] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[IN_CBALL_0; NORM_LE_SQUARE; dot; SUM_2; DIMINDEX_2; VECTOR_ADD_COMPONENT;
                  VECTOR_NEG_COMPONENT; VECTOR_2] THEN
      SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
      SUBGOAL_THEN `s * s = l pow 2 /\ l pow 2 * l pow 2 <= l pow 2` MP_TAC THENL
       [CONJ_TAC THENL
         [FIRST_X_ASSUM DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
          GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
          REWRITE_TAC[REAL_LE_POW_2] THEN MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REAL_ARITH_TAC];
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `l:real` th) THEN MP_TAC(SPEC `--l` th)) THEN
    REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `l * (l * p + q) <= l * &0 /\ l * (l * p - q) <= l * &0` MP_TAC THENL
     [UNDISCH_TAC `l pow 2 * p + l * q <= &0` THEN UNDISCH_TAC `l pow 2 * p + --l * q <= &0` THEN
      REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:real^2->real^2`; `c':real^2->real^2`; `--basis 1:real^2`; `basis 1:real^2`]
    SCHY_BALL_INV_DERIV) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `k = frechet_derivative (c':real^2->real^2) (at (vector[--(sqrt e); &0])) (basis 1)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(k:real^2)$1 * p = &1` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `k:real^2` o check (fun th ->
      can (term_match [] `!k:real^2. ((L:real^2->real^2) k)$1 = k$1 * p + k$2 * q`) (concl th))) THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= (k:real^2)$1` THENL
   [SUBGOAL_THEN `&0 <= (k:real^2)$1 * --p` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `(k:real^2)$1 * p = &1` THEN REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let SCHY_DCONT = prove
 (`!(c:real^2->real^2) c' z k.
     sch_ball c c' /\ z IN ball(vec 0,&2)
     ==> (\x. frechet_derivative c' (at (c x)) k) continuous (at z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch_ball; diffeomorphism_on] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x. frechet_derivative (c':real^2->real^2) (at ((c:real^2->real^2) x)) k) =
                (\w. frechet_derivative c' (at w) k) o c` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `ball(vec 0:real^2,&2)` THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    MP_TAC(ISPECL [`IMAGE (c:real^2->real^2) (ball(vec 0,&2))`; `c':real^2->real^2`; `k:real^2`]
      SMOOTH_MAP_ON_FRECHET_DERIVATIVE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS) THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE]]);;

let SCHY_INWARD = prove
 (`!(c:real^2->real^2) c' J e rho.
     sch_ball c c' /\ IMAGE c (sphere(vec 0,&1)) = J /\ IMAGE c (ball(vec 0,&1)) = inside J /\
     c(--basis 1) = vector[--(sqrt e); &0] /\ &0 < e /\ &0 < rho /\
     (!x:real^2. (x$1 + sqrt e) pow 2 + x$2 pow 2 < e
                 ==> (x IN J <=> x$1 pow 2 - x$2 pow 2 = e) /\
                     (x$1 pow 2 - x$2 pow 2 < e ==> x IN outside J))
     ==> ?delta. &0 < delta /\
           !z. dist(z,--basis 1) < delta
               ==> z IN ball(vec 0,&2) /\ dist(c z,vector[--(sqrt e); &0]) < rho /\
                   ?h. z dot h < &0 /\ frechet_derivative c (at z) h = schy_hf2(c z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:real^2->real^2`; `c':real^2->real^2`; `J:real^2->bool`; `e:real`]
    SCHY_CHART_DERIV_SIGN) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < sqrt e /\ sqrt e pow 2 = e` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [sch_ball]) THEN
  REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  SUBGOAL_THEN `--basis 1:real^2 IN ball(vec 0,&2)` ASSUME_TAC THENL
   [SIMP_TAC[IN_BALL_0; NORM_NEG; NORM_BASIS; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^2. z IN ball(vec 0,&2) ==> (c:real^2->real^2) continuous (at z)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `ball(vec 0:real^2,&2)` THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  ABBREV_TAC `Ht = \z:real^2. frechet_derivative (c':real^2->real^2) (at (c z))
                                (vector[(c z)$1; --((c z)$2)])` THEN
  SUBGOAL_THEN `!z:real^2. z IN ball(vec 0,&2)
                           ==> frechet_derivative (c:real^2->real^2) (at z) ((Ht:real^2->real^2) z) =
                               vector[(c z)$1; --((c z)$2)]` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "Ht" THEN MATCH_MP_TAC SCHY_BALL_INV_DERIV THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^2. z IN ball(vec 0,&2)
                ==> z dot (Ht:real^2->real^2) z =
                    ((c:real^2->real^2) z)$1 *
                    (z dot frechet_derivative (c':real^2->real^2) (at (c z)) (basis 1)) -
                    (c z)$2 * (z dot frechet_derivative c' (at (c z)) (basis 2))` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "Ht" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `linear(frechet_derivative (c':real^2->real^2) (at ((c:real^2->real^2) z)))`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`IMAGE (c:real^2->real^2) (ball(vec 0,&2))`; `c':real^2->real^2`;
                     `(c:real^2->real^2) z`] SMOOTH_MAP_ON_DIFFERENTIABLE) THEN
      ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
      REWRITE_TAC[FRECHET_DERIVATIVE_WORKS] THEN MESON_TAC[has_derivative];
      ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> ONCE_REWRITE_TAC[MATCH_MP SCHY_BASIS2_EXPAND th]) THEN
    SIMP_TAC[VECTOR_2; DOT_RADD; DOT_RMUL; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z:real^2. lift(z dot (Ht:real^2->real^2) z)) continuous (at (--basis 1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_TRANSFORM_AT THEN
    EXISTS_TAC `\z:real^2. lift(((c:real^2->real^2) z)$1 *
                    (z dot frechet_derivative (c':real^2->real^2) (at (c z)) (basis 1)) -
                    (c z)$2 * (z dot frechet_derivative c' (at (c z)) (basis 2)))` THEN
    EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN CONJ_TAC THENL
     [X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `dist(z:real^2,--basis 1) < &1` THEN
      REWRITE_TAC[IN_BALL_0; dist] THEN
      MP_TAC(ISPECL [`z:real^2`; `--basis 1:real^2`] NORM_TRIANGLE_SUB) THEN
      SIMP_TAC[NORM_NEG; NORM_BASIS; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[LIFT_SUB; LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_SUB THEN
    CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_MUL THEN
    (CONJ_TAC THENL
      [REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC CONTINUOUS_LIFT_COMPONENT_COMPOSE THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC CONTINUOUS_LIFT_DOT2 THEN REWRITE_TAC[CONTINUOUS_AT_ID] THEN
       MATCH_MP_TAC SCHY_DCONT THEN ASM_REWRITE_TAC[]]);
    ALL_TAC] THEN
  SUBGOAL_THEN `--basis 1 dot (Ht:real^2->real^2)(--basis 1) < &0` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> MP_TAC(MATCH_MP (ASSUME
      `!z:real^2. z IN ball(vec 0,&2)
                  ==> z dot (Ht:real^2->real^2) z =
                      ((c:real^2->real^2) z)$1 *
                      (z dot frechet_derivative (c':real^2->real^2) (at (c z)) (basis 1)) -
                      (c z)$2 * (z dot frechet_derivative c' (at (c z)) (basis 2))`)
      (ASSUME `--basis 1:real^2 IN ball(vec 0,&2)`))) THEN
    ASM_REWRITE_TAC[VECTOR_2; REAL_MUL_LZERO; REAL_SUB_RZERO] THEN DISCH_THEN SUBST1_TAC THEN
    SIMP_TAC[DOT_LNEG; DOT_BASIS; DIMINDEX_2; ARITH] THEN
    REWRITE_TAC[REAL_ARITH `--s * --x = s * x`] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < s * --x ==> s * x < &0`) THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `v0 = --basis 1 dot (Ht:real^2->real^2)(--basis 1)` THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [continuous_at] o check (fun th ->
    can (term_match [] `(\z:real^2. lift(z dot (Ht:real^2->real^2) z)) continuous at x`) (concl th))) THEN
  DISCH_THEN(MP_TAC o SPEC `--v0 / &2`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D2"))) THEN
  SUBGOAL_THEN `(c:real^2->real^2) continuous (at (--basis 1))` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `min rho (sqrt e)`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D1"))) THEN
  EXISTS_TAC `min (min d1 d2) (&1)` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:real^2) IN ball(vec 0,&2)` ASSUME_TAC THENL
   [UNDISCH_TAC `dist(z:real^2,--basis 1) < min (min d1 d2) (&1)` THEN
    REWRITE_TAC[IN_BALL_0; dist] THEN
    MP_TAC(ISPECL [`z:real^2`; `--basis 1:real^2`] NORM_TRIANGLE_SUB) THEN
    SIMP_TAC[NORM_NEG; NORM_BASIS; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `dist((c:real^2->real^2) z,vector[--(sqrt e); &0]) < min rho (sqrt e)`
  ASSUME_TAC THENL
   [USE_THEN "D1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `z dot (Ht:real^2->real^2) z < &0` ASSUME_TAC THENL
   [USE_THEN "D2" (MP_TAC o SPEC `z:real^2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    BETA_TAC THEN REWRITE_TAC[DIST_LIFT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < ((c:real^2->real^2) z)$1 pow 2 + (c z)$2 pow 2` ASSUME_TAC THENL
   [SUBGOAL_THEN `~((c:real^2->real^2) z = vec 0)` MP_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `norm(vector[--(sqrt e); &0]:real^2) = sqrt e` ASSUME_TAC THENL
       [REWRITE_TAC[vector_norm; dot; SUM_2; DIMINDEX_2; VECTOR_2] THEN AP_TERM_TAC THEN
        REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG; REAL_MUL_LZERO; REAL_ADD_RID] THEN
        ASM_REWRITE_TAC[GSYM REAL_POW_2];
        ALL_TAC] THEN
      UNDISCH_TAC `dist((c:real^2->real^2) z,vector[--(sqrt e); &0]) < min rho (sqrt e)` THEN
      ASM_REWRITE_TAC[DIST_0] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VEC_COMPONENT] THEN
    REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b /\ (&0 < a \/ &0 < b) ==> &0 < a + b`) THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN
    ASM_SIMP_TAC[REAL_POW_2; REAL_LT_SQUARE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `dist((c:real^2->real^2) z,vector[--(sqrt e); &0]) < min rho (sqrt e)` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `inv(&2 * (((c:real^2->real^2) z)$1 pow 2 + (c z)$2 pow 2)) %
              (Ht:real^2->real^2) z` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[DOT_RMUL] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < a * --b ==> a * b < &0`) THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(frechet_derivative (c:real^2->real^2) (at z))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ball(vec 0:real^2,&2)`; `c:real^2->real^2`; `z:real^2`]
      SMOOTH_MAP_ON_DIFFERENTIABLE) THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN REWRITE_TAC[FRECHET_DERIVATIVE_WORKS] THEN
    MESON_TAC[has_derivative];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LINEAR_CMUL] THEN
  REWRITE_TAC[schy_hf2; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_MUL_COMPONENT] THEN
  UNDISCH_TAC `&0 < ((c:real^2->real^2) z)$1 pow 2 + (c z)$2 pow 2` THEN
  CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* Rotations of the model plane (multiplication by -w, |w| = 1,              *)
(* so that -e1 goes to w), rotated ball charts, and the explicit form of a   *)
(* flow chart near lpt in the coordinates schy_pi.                           *)
(* ------------------------------------------------------------------------- *)

let schy_rot = new_definition
 `schy_rot (w:real^2) (z:real^2) =
    vector[--(w$1) * z$1 + w$2 * z$2; --(w$2) * z$1 - w$1 * z$2]:real^2`;;

let schy_conj = new_definition
 `schy_conj (w:real^2) = vector[w$1; --(w$2)]:real^2`;;

let SCHY_ROT_FACTS = prove
 (`!w:real^2.
     norm w = &1
     ==> linear (schy_rot w) /\ linear (schy_rot (schy_conj w)) /\
         (!z. norm(schy_rot w z) = norm z) /\
         (!z. schy_rot (schy_conj w) (schy_rot w z) = z) /\
         (!z. schy_rot w (schy_rot (schy_conj w) z) = z) /\
         schy_rot w (--basis 1) = w`,
  GEN_TAC THEN REWRITE_TAC[NORM_EQ_1; dot; SUM_2; DIMINDEX_2] THEN DISCH_TAC THEN
  REWRITE_TAC[linear; schy_rot; schy_conj; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2;
              VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_NEG_COMPONENT] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN TRY(REPEAT CONJ_TAC THEN REAL_ARITH_TAC) THEN
  TRY(UNDISCH_TAC `(w:real^2)$1 * w$1 + w$2 * w$2 = &1` THEN CONV_TAC REAL_RING) THEN
  REWRITE_TAC[vector_norm; dot; SUM_2; DIMINDEX_2; VECTOR_2] THEN AP_TERM_TAC THEN
  UNDISCH_TAC `(w:real^2)$1 * w$1 + w$2 * w$2 = &1` THEN CONV_TAC REAL_RING);;

let SCHY_ROT_IMAGE = prove
 (`!w:real^2 s.
     norm w = &1 /\ (!z. z IN s <=> schy_rot w z IN s) ==> IMAGE (schy_rot w) s = s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "S")) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHY_ROT_FACTS) THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN X_GEN_TAC `y:real^2` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `z:real^2` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
    REMOVE_THEN "S" (fun th -> REWRITE_TAC[GSYM(SPEC `z:real^2` th)]) THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN EXISTS_TAC `schy_rot (schy_conj w) (y:real^2)` THEN
    REMOVE_THEN "S" (fun th -> REWRITE_TAC[SPEC `schy_rot (schy_conj w) (y:real^2)` th]) THEN
    ASM_REWRITE_TAC[]]);;

let SCHY_ROT_RADIAL = prove
 (`!w:real^2 r.
     norm w = &1
     ==> IMAGE (schy_rot w) (ball(vec 0,r)) = ball(vec 0,r) /\
         IMAGE (schy_rot w) (cball(vec 0,r)) = cball(vec 0,r) /\
         IMAGE (schy_rot w) (sphere(vec 0,r)) = sphere(vec 0,r)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SCHY_ROT_IMAGE THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHY_ROT_FACTS) THEN
  ASM_REWRITE_TAC[IN_BALL_0; IN_CBALL_0; IN_SPHERE_0]);;

let SCHY_LINEAR_SMOOTH = prove
 (`!s (g:real^M->real^N). open s /\ linear g ==> smooth_map_on s g`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. x`; `g:real^M->real^N`] SMOOTH_MAP_ON_LINEAR_O) THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; o_DEF; ETA_AX]);;

let SCHY_ROT_CHART = prove
 (`!(c:real^2->real^2) c' w.
     sch_ball c c' /\ norm w = &1
     ==> sch_ball (c o schy_rot w) (schy_rot (schy_conj w) o c') /\
         (!r. IMAGE (c o schy_rot w) (ball(vec 0,r)) = IMAGE c (ball(vec 0,r))) /\
         (!r. IMAGE (c o schy_rot w) (cball(vec 0,r)) = IMAGE c (cball(vec 0,r))) /\
         (!r. IMAGE (c o schy_rot w) (sphere(vec 0,r)) = IMAGE c (sphere(vec 0,r))) /\
         (!z. norm(schy_rot w z) = norm z) /\
         (c o schy_rot w) (--basis 1) = c w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHY_ROT_FACTS) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[IMAGE_o; MATCH_MP SCHY_ROT_RADIAL th]) THEN
  ASM_REWRITE_TAC[o_THM] THEN REWRITE_TAC[sch_ball] THEN
  MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN
  EXISTS_TAC `ball(vec 0:real^2,&2)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    UNDISCH_TAC `sch_ball (c:real^2->real^2) c'` THEN REWRITE_TAC[sch_ball] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[IMAGE_o; MATCH_MP SCHY_ROT_RADIAL th])] THEN
  REWRITE_TAC[diffeomorphism_on; OPEN_BALL] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP SCHY_ROT_RADIAL th]) THEN
  SUBGOAL_THEN `norm(schy_conj w:real^2) = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `norm(w:real^2) = &1` THEN
    REWRITE_TAC[NORM_EQ_1; dot; SUM_2; DIMINDEX_2; schy_conj; VECTOR_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP SCHY_ROT_RADIAL th]) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC SCHY_LINEAR_SMOOTH THEN
  ASM_REWRITE_TAC[OPEN_BALL]);;

let SCHY_THETA_PI = prove
 (`!(v:real^3->real^3) B rho0 e x0 t.
     smooth_map_on (:real^3) v /\ (!y. ode_vf_maxint v (:real^3) y = (:real^1)) /\
     (!y. norm(v y) <= B) /\
     (!x. dist(x,schy_lpt e) < rho0 ==> v x = schy_v0 x /\ ~(x$1 pow 2 + x$2 pow 2 = &0)) /\
     dist(x0,schy_lpt e) < rho0 / &2 /\ B * abs t < rho0 / &2
     ==> schy_pi(ode_vf_flow v (:real^3) (lift t) x0) = schy_pi x0 + t % vector[&1; &0; &1]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`v:real^3->real^3`; `x0:real^3`; `lift t`] SCHY_FLOW_PI) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`v:real^3->real^3`; `B:real`] SCH5V_FLOW_DISPLACEMENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`x0:real^3`; `s:real^1`; `vec 0:real^1`]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH5V_FLOW_FACTS o CONJ
    (ASSUME `smooth_map_on (:real^3) (v:real^3->real^3)`)) THEN
  ASM_REWRITE_TAC[DROP_VEC; REAL_SUB_RZERO] THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs(drop s) <= abs t` ASSUME_TAC THENL
   [UNDISCH_TAC `(s:real^1) IN segment[vec 0,lift t]` THEN
    REWRITE_TAC[IN_SEGMENT; VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[DROP_CMUL; LIFT_DROP; REAL_ABS_MUL] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `dist(ode_vf_flow (v:real^3->real^3) (:real^3) s x0,schy_lpt e) < rho0`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `!a b. d1 <= a + b /\ a < r / &2 /\ b < r / &2 ==> d1 < r`) THEN
    EXISTS_TAC `dist(x0:real^3,schy_lpt e)` THEN
    EXISTS_TAC `norm(ode_vf_flow (v:real^3->real^3) (:real^3) s x0 - x0)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[dist] THEN CONV_TAC NORM_ARITH;
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `B * abs(drop s)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `B * abs t` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm((v:real^3->real^3)(vec 0))` THEN
      ASM_REWRITE_TAC[NORM_POS_LE]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `ode_vf_flow (v:real^3->real^3) (:real^3) s x0` o check (fun th ->
    can (term_match [] `!x. dist(x,schy_lpt e) < rho0 ==> P x`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[SCHY_PI_V0]);;

(* ------------------------------------------------------------------------- *)
(* The cancellation chart.  The translate neck gt, the planar                *)
(* chart c rotated so that c(-e1) = P0, the field v (V0 near lpt), the      *)
(* explicit region near the model point -e1, and the pancake charts.        *)
(* ------------------------------------------------------------------------- *)

let SCHY_CRIT_TANGENT = prove
 (`!(g:real^3->real^3) gt t.
     (!t w. t IN sphere(vec 0,&1) /\ orthogonal t w
            ==> frechet_derivative gt (at t) w = frechet_derivative g (at t) w)
     ==> (sch_crit gt t <=> sch_crit g t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sch_crit] THEN
  ASM_CASES_TAC `(t:real^3) IN sphere(vec 0,&1)` THEN ASM_SIMP_TAC[]);;

let SCHY_TREGION_OPEN = prove
 (`!e de. &0 < de
          ==> open {y:real^3 | (y$1 + sqrt e) pow 2 + y$2 pow 2 < de pow 2 /\
                               abs(y$3 - (y$1 pow 2 - y$2 pow 2)) < de}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SET_RULE `{x:real^3 | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
  MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC THENL
   [SUBGOAL_THEN `{y:real^3 | (y$1 + sqrt e) pow 2 + y$2 pow 2 < de pow 2} =
                  {y | sch5v_pr y IN ball(vector[--(sqrt e); &0],de)}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_BALL; dist] THEN GEN_TAC THEN
      ONCE_REWRITE_TAC[NORM_SUB] THEN
      ASM_SIMP_TAC[NORM_LT_SQUARE; dot; SUM_2; DIMINDEX_2; VECTOR_SUB_COMPONENT; VECTOR_2;
                   sch5v_pr] THEN
      REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN REWRITE_TAC[OPEN_BALL] THEN
      GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN REWRITE_TAC[SCH5V_PR_AT_SMOOTH]];
    SUBGOAL_THEN `{y:real^3 | abs(y$3 - (y$1 pow 2 - y$2 pow 2)) < de} =
                  {y | schy_ell(schy_pi y) IN ball(vec 0,de)}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_BALL_0; GSYM SCHY_SIGMA_LIFT; NORM_LIFT];
      MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN REWRITE_TAC[OPEN_BALL] THEN
      GEN_TAC THEN REWRITE_TAC[GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN REWRITE_TAC[differentiable] THEN
        MESON_TAC[SCHY_PI_DERIV];
        MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN REWRITE_TAC[SCHY_ELL_LINEAR]]]]);;

let SCHY_V0_REGION = prove
 (`!(gt:real^3->real^3) gt' K de e d (v:real^3->real^3) C.
     ~(K = &0) /\ &0 < de /\ de <= sqrt e /\ &2 * de <= abs K /\ &0 < e /\ e < &1 /\ &0 < d /\
     (!y:real^3. (y$1 + sqrt e) pow 2 + y$2 pow 2 < de pow 2 /\
                 abs(y$3 - (y$1 pow 2 - y$2 pow 2)) < de
                 ==> norm(gt' y) pow 2 = (&1 + (y$3 - (y$1 pow 2 - y$2 pow 2)) / K) pow 2) /\
     schy_lpt e IN C /\
     (!x. (?y. y IN C /\ dist(y,x) < &2 * d) ==> v x = basis 3 + sch5v_hfield gt' x)
     ==> !x. dist(x,schy_lpt e) < min (&2 * d) (de / &8)
             ==> v x = schy_v0 x /\ x$1 < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < sqrt e /\ sqrt e pow 2 = e /\ sqrt e < &1` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `sqrt(&1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REWRITE_TAC[]; REWRITE_TAC[SQRT_1; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs((x:real^3)$1 + sqrt e) < de / &8 /\ abs(x$2) < de / &8 /\
                abs(x$3 - e) < de / &8 /\ dist(x,schy_lpt e) < &2 * d` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `dist(x,schy_lpt e) < min (&2 * d) (de / &8)` THEN
    REWRITE_TAC[REAL_LT_MIN; dist] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `norm(x - schy_lpt e)` THEN ASM_REWRITE_TAC[] THENL
     [MP_TAC(ISPECL [`x - schy_lpt e`; `1`] COMPONENT_LE_NORM);
      MP_TAC(ISPECL [`x - schy_lpt e`; `2`] COMPONENT_LE_NORM);
      MP_TAC(ISPECL [`x - schy_lpt e`; `3`] COMPONENT_LE_NORM)] THEN
    REWRITE_TAC[DIMINDEX_3; ARITH; VECTOR_SUB_COMPONENT; schy_lpt; VECTOR_3] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `de / &8 <= &1 / &8` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3)$1 < &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `abs((x:real^3)$3 - (x$1 pow 2 - x$2 pow 2)) < de` ASSUME_TAC THENL
   [SUBGOAL_THEN `abs((x:real^3)$1 pow 2 - e) <= abs(x$1 + sqrt e) * &3 /\
                  (x:real^3)$2 pow 2 <= abs(x$2) * &1` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [SUBGOAL_THEN `(x:real^3)$1 pow 2 - e = (x$1 + sqrt e) * (x$1 - sqrt e)` SUBST1_TAC THENL
         [ASM_REWRITE_TAC[REAL_ARITH `(a + s) * (a - s) = a pow 2 - s pow 2`]; ALL_TAC] THEN
        REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
        ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN REWRITE_TAC[REAL_POW_2] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC];
      MP_TAC(SPEC `(x:real^3)$2` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `((x:real^3)$1 + sqrt e) pow 2 + x$2 pow 2 < de pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(de / &8) pow 2 + (de / &8) pow 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
      REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_POW_DIV] THEN
      SUBGOAL_THEN `&0 < de pow 2` MP_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `v (x:real^3) = basis 3 + sch5v_hfield (gt':real^3->real^3) x` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `schy_lpt e` THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`gt':real^3->real^3`; `K:real`;
                 `{y:real^3 | (y$1 + sqrt e) pow 2 + y$2 pow 2 < de pow 2 /\
                              abs(y$3 - (y$1 pow 2 - y$2 pow 2)) < de}`; `x:real^3`]
    SCHY_TN_V0) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SCHY_TREGION_OPEN THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(REAL_ARITH `abs(a) < &1 / &2 ==> ~(&1 + a = &0)`) THEN
      REWRITE_TAC[REAL_ABS_DIV] THEN
      SUBGOAL_THEN `&0 < abs K` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      MP_TAC(SPEC `(x:real^3)$2` REAL_LE_POW_2) THEN
      SUBGOAL_THEN `&0 < (x:real^3)$1 pow 2` MP_TAC THENL
       [REWRITE_TAC[REAL_POW_2; REAL_LT_SQUARE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REAL_ARITH_TAC];
    SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The headline of H2.  For the cancellation situation, a                    *)
(* translate neck gt with the same sphere, a ball chart c of the planar disc *)
(* bounded by C with c(-e1) = P0, a field v equal to V0 near lpt, the model *)
(* region near -e1 where Dc^-1(hf) points inwards, and pancake charts for    *)
(* all small lam, whose flow stays in the V0 region near the meridian.      *)
(* ------------------------------------------------------------------------- *)

let SCHY_ROT_FAR = prove
 (`!(c0:real^2->real^2) w K0 dax a (C:real^3->bool).
     norm w = &1 /\
     (!z. z IN ball(vec 0,&2) ==> sch5v_at a (c0 z) IN K0) /\
     (!z. z IN ball(vec 0,&2) ==> (sch5v_at a (c0 z) IN C <=> z IN sphere(vec 0,&1))) /\
     (!z y. z IN cball(vec 0,&1 / &2) /\ y IN C ==> dax <= dist(sch5v_at a (c0 z),y))
     ==> (!z. z IN ball(vec 0,&2) ==> sch5v_at a ((c0 o schy_rot w) z) IN K0) /\
         (!z. z IN ball(vec 0,&2)
              ==> (sch5v_at a ((c0 o schy_rot w) z) IN C <=> z IN sphere(vec 0,&1))) /\
         (!z y. z IN cball(vec 0,&1 / &2) /\ y IN C
                ==> dax <= dist(sch5v_at a ((c0 o schy_rot w) z),y))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "K")
    (CONJUNCTS_THEN2 (LABEL_TAC "C") (LABEL_TAC "D")))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHY_ROT_FACTS) THEN
  REWRITE_TAC[o_THM] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN USE_THEN "K" MATCH_MP_TAC THEN
    UNDISCH_TAC `(z:real^2) IN ball(vec 0,&2)` THEN ASM_REWRITE_TAC[IN_BALL_0];
    X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    USE_THEN "C" (MP_TAC o SPEC `schy_rot w (z:real^2)`) THEN
    UNDISCH_TAC `(z:real^2) IN ball(vec 0,&2)` THEN
    REWRITE_TAC[IN_BALL_0; IN_SPHERE_0; ASSUME `!z:real^2. norm(schy_rot w z) = norm z`] THEN
    CONV_TAC TAUT;
    MAP_EVERY X_GEN_TAC [`z:real^2`; `y:real^3`] THEN STRIP_TAC THEN
    USE_THEN "D" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z:real^2) IN cball(vec 0,&1 / &2)` THEN ASM_REWRITE_TAC[IN_CBALL_0]]);;

let SCHY_CANCEL_CHART = prove
 (`!(g:real^3->real^3) g' r e C (Fn:real^2->real^2) Fn' D0.
     sch_neck g g' /\ (!t. sch_crit g t ==> ~((g t)$3 = e)) /\
     schy_chart (IMAGE g (sphere(vec 0,&1))) r /\ &0 < e /\ &16 * e < r pow 2 /\
     C IN components(sch_level g e) /\ FINITE(components(sch_level g e)) /\
     schy_lpt e IN C /\ ~(schy_rpt e IN C) /\
     (!x:real^2. x IN inside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C)
                 ==> ~((vector[x$1; x$2; e]:real^3) IN IMAGE g (sphere(vec 0,&1)))) /\
     sch_neck Fn Fn' /\ C = IMAGE (\x. vector[(Fn x)$1; (Fn x)$2; e]:real^3) (sphere(vec 0,&1)) /\
     &0 < D0
     ==> ?gt gt' (c:real^2->real^2) c' (v:real^3->real^3) B rho0 delta1.
           sch_neck gt gt' /\ (!t. t IN sphere(vec 0,&1) ==> gt t = g t) /\
           (!t w. t IN sphere(vec 0,&1) /\ orthogonal t w
                  ==> frechet_derivative gt (at t) w = frechet_derivative g (at t) w) /\
           sch_ball c c' /\
           C = IMAGE (\z. sch5v_at e (c z)) (sphere(vec 0,&1)) /\
           IMAGE c (ball(vec 0,&1)) = inside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C) /\
           c(--basis 1) = vector[--(sqrt e); &0] /\
           smooth_map_on (:real^3) v /\ (!y. ode_vf_maxint v (:real^3) y = (:real^1)) /\
           (!y. norm(v y) <= B) /\ (!y. (v y)$3 = &1) /\
           (!x. ~(?y. y IN C /\ dist(y,x) < D0) ==> v x = basis 3) /\
           &0 < rho0 /\
           (!x. dist(x,schy_lpt e) < rho0 ==> v x = schy_v0 x /\ x$1 < &0) /\
           &0 < delta1 /\
           (!z. dist(z,--basis 1) < delta1
                ==> z IN ball(vec 0,&2) /\ dist(c z,vector[--(sqrt e); &0]) < rho0 / &2 /\
                    ?h. z dot h < &0 /\ frechet_derivative c (at z) h = schy_hf2(c z)) /\
           !H. &0 < H
               ==> ?lam0. &0 < lam0 /\
                   !lam. &0 < lam /\ lam < lam0
                   ==> B * lam * H < rho0 / &2 /\
                       ?Theta Theta'.
                         (!y. Theta y = ode_vf_flow v (:real^3) (lift(lam * y$3))
                                          (sch5v_at e (c(sch5v_pr y)))) /\
                         diffeomorphism_on (sch5v_slab H) (IMAGE Theta (sch5v_slab H)) Theta Theta' /\
                         (!y. y IN sch5v_slab H ==> (Theta y)$3 = e + lam * y$3) /\
                         (!y. y IN sch5v_slab H /\ y$3 = &0 ==> Theta y = sch5v_at e (c(sch5v_pr y))) /\
                         (!y. y IN sch5v_slab H /\ y$1 pow 2 + y$2 pow 2 < &1 / &4
                              ==> Theta y = sch5v_at (e + lam * y$3) (c(sch5v_pr y))) /\
                         (!y. y IN sch5v_slab H
                              ==> (Theta y IN IMAGE g (sphere(vec 0,&1)) <=>
                                   y$1 pow 2 + y$2 pow 2 = &1)) /\
                         ((!y. y IN sch5v_slab H
                               ==> (Theta y IN inside(IMAGE g (sphere(vec 0,&1))) <=>
                                    y$1 pow 2 + y$2 pow 2 < &1)) \/
                          (!y. y IN sch5v_slab H
                               ==> (Theta y IN outside(IMAGE g (sphere(vec 0,&1))) <=>
                                    y$1 pow 2 + y$2 pow 2 < &1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `C:real^3->bool`)) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`] SCHY_SIDE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `r:real`; `e:real`]
    SCHY_TRANSLATE_NECK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gt:real^3->real^3` (X_CHOOSE_THEN `gt':real^3->real^3`
    (X_CHOOSE_THEN `K:real` (X_CHOOSE_THEN `de:real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "TR")))))))))))) THEN
  SUBGOAL_THEN `IMAGE (gt:real^3->real^3) (sphere(vec 0,&1)) = IMAGE (g:real^3->real^3) (sphere(vec 0,&1))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `!t. t IN sphere(vec 0,&1) ==> (gt:real^3->real^3) t = g t` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. sch_crit (gt:real^3->real^3) t <=> sch_crit (g:real^3->real^3) t` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SCHY_CRIT_TANGENT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `sch_level (gt:real^3->real^3) e = sch_level (g:real^3->real^3) e` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[sch_level]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. sch_crit (gt:real^3->real^3) t ==> ~((gt t)$3 = e)` ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `sch_crit (g:real^3->real^3) t` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(gt:real^3->real^3) t = g t` SUBST1_TAC THENL
     [UNDISCH_TAC `sch_crit (g:real^3->real^3) t` THEN REWRITE_TAC[sch_crit] THEN
      ASM_MESON_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`gt:real^3->real^3`; `gt':real^3->real^3`; `e:real`; `C:real^3->bool`;
                 `Fn:real^2->real^2`; `Fn':real^2->real^2`] SCH5V_PANCAKE_SETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c0:real^2->real^2` (X_CHOOSE_THEN `c0':real^2->real^2`
    (X_CHOOSE_THEN `K0:real^3->bool` (X_CHOOSE_THEN `dax:real` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C = IMAGE (Fn:real^2->real^2) (sphere(vec 0,&1))`
  ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM(check (fun th ->
      is_eq(concl th) && rhs(concl th) = `C:real^3->bool`) th)]) THEN
    REWRITE_TAC[SCHY_PROJ_LEVEL];
    ALL_TAC] THEN
  SUBGOAL_THEN `?w:real^2. w IN sphere(vec 0,&1) /\ (c0:real^2->real^2) w = vector[--(sqrt e); &0]`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `vector[--(sqrt e); &0]:real^2 IN IMAGE (c0:real^2->real^2) (sphere(vec 0,&1))`
    MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(check (fun th ->
        concl th = `IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C =
                    IMAGE (Fn:real^2->real^2) (sphere(vec 0,&1))`) th)]) THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `schy_lpt e` THEN
      ASM_REWRITE_TAC[schy_lpt; VECTOR_3];
      REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(w:real^2) = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `(w:real^2) IN sphere(vec 0,&1)` THEN REWRITE_TAC[IN_SPHERE_0]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c0:real^2->real^2`; `c0':real^2->real^2`; `w:real^2`] SCHY_ROT_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c0:real^2->real^2`; `w:real^2`; `K0:real^3->bool`; `dax:real`; `e:real`;
                 `C:real^3->bool`] SCHY_ROT_FAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `c = (c0:real^2->real^2) o schy_rot w` THEN
  ABBREV_TAC `c' = schy_rot (schy_conj w) o (c0':real^2->real^2)` THEN
  ABBREV_TAC `J = IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C` THEN
  SUBGOAL_THEN `IMAGE (c:real^2->real^2) (sphere(vec 0,&1)) = J /\
                IMAGE (c:real^2->real^2) (ball(vec 0,&1)) = inside J`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `C = IMAGE (\z. sch5v_at e ((c:real^2->real^2) z)) (sphere(vec 0,&1))`
  (ASSUME_TAC o SYM) THENL
   [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM(check (fun th ->
      is_eq(concl th) && rhs(concl th) = `C:real^3->bool`) th)]) THEN
    MATCH_MP_TAC SCHY_LEVEL_AT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`gt:real^3->real^3`; `gt':real^3->real^3`; `C:real^3->bool`;
                 `K0:real^3->bool`; `min D0 (dax / &2)`] SCHY_PANCAKE_FIELD_X) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^3->real^3` (X_CHOOSE_THEN `B:real`
    (X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `ee:real`
      (fun th -> MAP_EVERY (fun (s,t) -> LABEL_TAC s t)
        (zip ["F1";"F2";"F3";"F4";"F5";"F6";"OFF";"F8";"F9";"F10";"F11"] (CONJUNCTS th))))))) THEN
  SUBGOAL_THEN `e < &1` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [schy_chart] o check (fun th ->
      can (term_match [] `schy_chart s r`) (concl th))) THEN STRIP_TAC THEN
    SUBGOAL_THEN `r pow 2 < &1` MP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `x = r * r /\ r * r < &1 * &1 ==> x < &1`) THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`gt:real^3->real^3`; `gt':real^3->real^3`; `K:real`; `de:real`; `e:real`;
                 `d:real`; `v:real^3->real^3`; `C:real^3->bool`] SCHY_V0_REGION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "TR" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]];
    DISCH_TAC] THEN
  ABBREV_TAC `rho0 = min (&2 * d) (de / &8)` THEN
  SUBGOAL_THEN `&0 < rho0` ASSUME_TAC THENL [EXPAND_TAC "rho0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:real^2->real^2`; `c':real^2->real^2`; `J:real^2->bool`; `e:real`;
                 `rho0 / &2`] SCHY_INWARD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `delta1:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&1 <= B` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm((v:real^3->real^3)(vec 0))` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`(v:real^3->real^3)(vec 0)`; `3`] COMPONENT_LE_NORM) THEN
    ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`gt:real^3->real^3`; `gt':real^3->real^3`; `c:real^2->real^2`;
                        `c':real^2->real^2`; `v:real^3->real^3`; `B:real`; `rho0:real`;
                        `delta1:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    USE_THEN "OFF" MATCH_MP_TAC THEN
    UNDISCH_TAC `~(?y:real^3. y IN C /\ dist(y,x) < D0)` THEN
    REWRITE_TAC[CONTRAPOS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `H:real` THEN DISCH_TAC THEN
  ABBREV_TAC `m = min ee (min d (min (dax / &2) (rho0 / &2)))` THEN
  SUBGOAL_THEN `&0 < m /\ m <= ee /\ m <= d /\ m <= dax / &2 /\ m <= rho0 / &2`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "m" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * B * H` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `m / (&2 * B * H)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `lam:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `B * lam * H < m` ASSUME_TAC THENL
   [SUBGOAL_THEN `lam * (&2 * B * H) < m` MP_TAC THENL
     [UNDISCH_TAC `lam < m / (&2 * B * H)` THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < B * lam * H` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`gt:real^3->real^3`; `gt':real^3->real^3`; `e:real`; `C:real^3->bool`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `K0:real^3->bool`; `dax:real`;
                 `v:real^3->real^3`; `B:real`; `d:real`; `ee:real`; `lam:real`; `H:real`]
    SCHY_PANCAKE_CHART_F) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    USE_THEN "OFF" MATCH_MP_TAC THEN
    UNDISCH_TAC `~(?y:real^3. y IN C /\ dist(y,x) < dax / &2)` THEN
    REWRITE_TAC[CONTRAPOS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

