(* ========================================================================= *)
(* Unit pc_sch_b1cls: part H1 of the one-saddle base case of the smooth      *)
(* Schoenflies induction (H1 this unit, H2 pc_sch_b1chart, H3 pc_sch_b1canc, *)
(* H4 pc_sch_base1): the reduction of the one-saddle base case               *)
(* SCH_BASE1_STATEMENT to the cancellation step SCHY_CANCEL_STATEMENT, given *)
(* the chart-given single cut of pc_sch_surg (SCH5S_SINGLE_CUT_CHART, stated *)
(* here as SCHY_CUT_STATEMENT), the level necks and innermost components of  *)
(* pc_sch_level2 (SCH_LEVEL_NECK_STATEMENT, SCH_LEVEL_INNERMOST_STATEMENT)   *)
(* and the saddle-free base case of pc_sch_base0 (SCH_BASE0_STATEMENT),      *)
(* bundled in the single hypothesis SCHY_DEPS.                               *)
(*                                                                           *)
(* Route: normalization of the saddle chart by height-preserving ambient     *)
(* diffeomorphisms (saddle at the origin, S = the graph z = x1^2 - x2^2 near *)
(* 0), an orientability lemma (Jordan curve theorem on S minus a point: the  *)
(* upper or the lower branch points of the saddle lie on different level     *)
(* components), and an induction on the number of components of the level e  *)
(* that cuts innermost components without branch points (the single cut, the *)
(* saddle-free base case, and the gluing of pc_sch_glue).                    *)
(* ========================================================================= *)

(* pc_sch_glue (through pc_sch_collar) first, then pc_sch_vflow: see the    *)
(* note in pc_sch_base0 on the overloading of + after Multivariate/cross.   *)

needs "src/pc_sch_glue.ml";;
needs "src/pc_sch_vflow.ml";;
needs "src/pc_sch_capcol.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The hypothesis bundle SCHY_DEPS and the cancellation step.                *)
(* ------------------------------------------------------------------------- *)

(* The chart-given single cut of pc_sch_surg (SCH5S_SINGLE_CUT_CHART).  The  *)
(* hypotheses below include every chart clause (also the y3 = 0 clause, the  *)
(* link of C with the planar chart c and the innermost condition), the       *)
(* conclusion only some of the clauses of SCH5S_SINGLE_CUT_CHART, so that    *)
(* theorem implies this statement directly (SCHY_CUT_FROM_SURG of            *)
(* pc_sch_b1cut).                                                            *)

let SCHY_CUT_STATEMENT = new_definition
 `SCHY_CUT_STATEMENT <=>
    !(g:real^3->real^3) g' a C (c:real^2->real^2) c' (Theta:real^3->real^3) Theta' H lam.
      sch_neck g g' /\ sch_morse g /\ (!t. sch_crit g t ==> ~((g t)$3 = a)) /\
      C IN components(sch_level g a) /\ FINITE(components(sch_level g a)) /\
      (!x:real^2. x IN inside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C)
                  ==> ~((vector[x$1; x$2; a]:real^3) IN IMAGE g (sphere(vec 0,&1)))) /\
      sch_ball c c' /\
      C = IMAGE (\z. sch5v_at a (c z)) (sphere(vec 0,&1)) /\
      IMAGE c (ball(vec 0,&1)) = inside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C) /\
      &3 / &2 <= H /\ &0 < lam /\
      (!t. sch_crit g t ==> ~((g t)$3 = a + lam / &2) /\ ~((g t)$3 = a - lam / &2)) /\
      diffeomorphism_on (sch5v_slab H) (IMAGE Theta (sch5v_slab H)) Theta Theta' /\
      (!y. y IN sch5v_slab H ==> (Theta y)$3 = a + lam * y$3) /\
      (!y. y IN sch5v_slab H /\ y$3 = &0 ==> Theta y = sch5v_at a (c(sch5v_pr y))) /\
      (!y. y IN sch5v_slab H /\ y$1 pow 2 + y$2 pow 2 < &1 / &4
           ==> Theta y = sch5v_at (a + lam * y$3) (c(sch5v_pr y))) /\
      (!y. y IN sch5v_slab H
           ==> (Theta y IN IMAGE g (sphere(vec 0,&1)) <=> y$1 pow 2 + y$2 pow 2 = &1)) /\
      ((!y. y IN sch5v_slab H
            ==> (Theta y IN inside(IMAGE g (sphere(vec 0,&1))) <=>
                 y$1 pow 2 + y$2 pow 2 < &1)) \/
       (!y. y IN sch5v_slab H
            ==> (Theta y IN outside(IMAGE g (sphere(vec 0,&1))) <=>
                 y$1 pow 2 + y$2 pow 2 < &1)))
      ==> ?g1 g1' g2 g2' e0.
            sch_neck g1 g1' /\ sch_morse g1 /\ sch_neck g2 g2' /\ sch_morse g2 /\
            (!t. sch_crit g1 t ==> ~((g1 t)$3 = a)) /\
            (!t. sch_crit g2 t ==> ~((g2 t)$3 = a)) /\
            sch_slab_config (IMAGE g (sphere(vec 0,&1))) (IMAGE g1 (sphere(vec 0,&1)))
                            (IMAGE g2 (sphere(vec 0,&1))) Theta /\
            &0 < e0 /\ e0 <= &1 / &16 /\
            (!x. x IN sch_capcone
                 ==> g1 x = Theta(sch_cap_collar e0 x) /\
                     g2(sch_flip3 x) = Theta(sch_flip3(sch_cap_collar e0 x))) /\
            CARD(sch_saddles g1) + CARD(sch_saddles g2) = CARD(sch_saddles g) /\
            IMAGE g1 (sch_saddles g1) UNION IMAGE g2 (sch_saddles g2) =
            IMAGE g (sch_saddles g) /\
            DISJOINT (IMAGE g1 (sch_saddles g1)) (IMAGE g2 (sch_saddles g2)) /\
            CARD(components(sch_level g1 a)) + CARD(components(sch_level g2 a)) + 1 =
            CARD(components(sch_level g a)) /\
            (!t. sch_crit g1 t
                 ==> g1 t = Theta(vector[&0; &0; --(&1 / &2)]) \/
                     (?u. sch_crit g u /\ g1 t = g u)) /\
            (!t. sch_crit g2 t
                 ==> g2 t = Theta(vector[&0; &0; &1 / &2]) \/
                     (?u. sch_crit g u /\ g2 t = g u)) /\
            (!u. sch_crit g u
                 ==> (?t. sch_crit g1 t /\ g1 t = g u) \/ (?t. sch_crit g2 t /\ g2 t = g u)) /\
            (!u. sch_crit g u
                 ==> ~((?t. sch_crit g1 t /\ g1 t = g u) /\
                       (?t. sch_crit g2 t /\ g2 t = g u)))`;;

(* All hypotheses of the one-saddle base case in one place: the saddle-free  *)
(* base case (SCH_BASE0), the level necks and innermost components, and the  *)
(* chart-given single cut.  SCHY_DEPS_FROM_STATEMENTS of pc_sch_b1cut        *)
(* derives SCHY_DEPS from the corresponding statements.                      *)

let SCHY_DEPS = new_definition
 `SCHY_DEPS <=>
    SCH_BASE0_STATEMENT /\ SCH_LEVEL_NECK_STATEMENT /\ SCH_LEVEL_INNERMOST_STATEMENT /\
    SCHY_CUT_STATEMENT`;;

(* The normalized saddle chart: near the origin, S is exactly the graph     *)
(* z = x1^2 - x2^2 (a sch_hchart at the origin with ph the identity).       *)

let schy_chart = new_definition
 `schy_chart (s:real^3->bool) (r:real) <=>
    &0 < r /\ r < &1 /\
    !x:real^3. x$1 pow 2 + x$2 pow 2 < r pow 2 /\ abs(x$3) < r
               ==> (x IN s <=> x$3 = x$1 pow 2 - x$2 pow 2)`;;

(* The branch points of the saddle on the levels e and --e.                  *)

let schy_lpt = new_definition
 `schy_lpt (e:real) = vector[--(sqrt e); &0; e]:real^3`;;

let schy_rpt = new_definition
 `schy_rpt (e:real) = vector[sqrt e; &0; e]:real^3`;;

(* The cancellation step (proved in the units H2-H4): a normalized          *)
(* one-saddle sphere whose left branch component on a low regular level e   *)
(* is innermost and misses the right branch point bounds a ball.             *)

let SCHY_CANCEL_STATEMENT = new_definition
 `SCHY_CANCEL_STATEMENT <=>
    !(g:real^3->real^3) g' r e C.
      sch_neck g g' /\ sch_morse g /\ CARD(sch_saddles g) = 1 /\
      (?t0. t0 IN sch_saddles g /\ g t0 = vec 0) /\
      schy_chart (IMAGE g (sphere(vec 0,&1))) r /\
      &0 < e /\ &16 * e < r pow 2 /\ (!t. sch_crit g t ==> ~((g t)$3 = e)) /\
      C IN components(sch_level g e) /\ schy_lpt e IN C /\ ~(schy_rpt e IN C) /\
      (!x:real^2. x IN inside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C)
                  ==> ~((vector[x$1; x$2; e]:real^3) IN IMAGE g (sphere(vec 0,&1))))
      ==> sch_bounds_ball (IMAGE g (sphere(vec 0,&1)))`;;

(* ------------------------------------------------------------------------- *)
(* Height-preserving ambient diffeomorphisms                                 *)
(* x |-> (A(x1,x2), x3 + b) for a diffeomorphism A of the plane, and the    *)
(* transfer of necks, critical points, Morse charts, saddles, levels and     *)
(* bounding balls.                                                           *)
(* ------------------------------------------------------------------------- *)

let schy_hp = new_definition
 `schy_hp (A:real^2->real^2) (b:real) (x:real^3) = sch5v_at (x$3 + b) (A(sch5v_pr x))`;;

let SCHY_HP_FACTS = prove
 (`!(A:real^2->real^2) b x.
     (schy_hp A b x)$3 = x$3 + b /\ sch5v_pr(schy_hp A b x) = A(sch5v_pr x)`,
  REWRITE_TAC[schy_hp; SCH5V_PR_AT]);;

let SCHY_HP_INV = prove
 (`!(A:real^2->real^2) A' b x.
     (!z. A'(A z) = z) ==> schy_hp A' (--b) (schy_hp A b x) = x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[schy_hp; SCH5V_PR_AT] THEN
  ASM_REWRITE_TAC[REAL_ARITH `(x + b) + --b = x:real`] THEN REWRITE_TAC[SCH5V_PR_AT]);;

let SCHY_HP_SMOOTH = prove
 (`!(A:real^2->real^2) b. smooth_map_on (:real^2) A ==> smooth_map_on (:real^3) (schy_hp A b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `schy_hp (A:real^2->real^2) b =
                (\x:real^3. vector[(A(sch5v_pr x))$1; (A(sch5v_pr x))$2; x$3 + b]:real^3)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; schy_hp; sch5v_at]; ALL_TAC] THEN
  MATCH_MP_TAC SCH5C_SV3 THEN REWRITE_TAC[OPEN_UNIV] THEN
  SUBGOAL_THEN `smooth_map_on (:real^3) ((A:real^2->real^2) o sch5v_pr)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^2)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; SCH5V_PR_AT_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. smooth_map_on (:real^3) (\x:real^3. lift(((A:real^2->real^2)(sch5v_pr x))$k))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `(\x:real^3. lift(((A:real^2->real^2)(sch5v_pr x))$k)) =
                  (\z:real^2. lift(z$k)) o ((A:real^2->real^2) o sch5v_pr)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^2)` THEN
    ASM_SIMP_TAC[OPEN_UNIV; SUBSET_UNIV; SCH5C_SR_COMP];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`(:real^3)`; `&1`; `b:real`; `3`] SCH5V_LIFT_AFFINE) THEN
  REWRITE_TAC[OPEN_UNIV; REAL_MUL_LID]);;

let SCHY_HP_DIFFEO = prove
 (`!(A:real^2->real^2) A' b.
     diffeomorphism_on (:real^2) (:real^2) A A'
     ==> diffeomorphism_on (:real^3) (:real^3) (schy_hp A b) (schy_hp A' (--b))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[diffeomorphism_on; IN_UNIV; OPEN_UNIV] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(!x. schy_hp (A':real^2->real^2) (--b) (schy_hp A b x) = x) /\
                (!x. schy_hp (A:real^2->real^2) b (schy_hp A' (--b) x) = x)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN GEN_TAC THENL
     [MATCH_MP_TAC SCHY_HP_INV THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`A':real^2->real^2`; `A:real^2->real^2`; `--b:real`; `x:real^3`]
        SCHY_HP_INV) THEN ASM_REWRITE_TAC[REAL_NEG_NEG]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SCHY_HP_SMOOTH] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN ASM_MESON_TAC[]);;

(* The third component of a derivative only sees the height function.       *)

let SCHY_DERIV3_EQ = prove
 (`!(f:real^3->real^3) (h:real^3->real^3) t b.
     f differentiable (at t) /\ h differentiable (at t) /\ (!x. (h x)$3 = (f x)$3 + b)
     ==> !v. (frechet_derivative h (at t) v)$3 = (frechet_derivative f (at t) v)$3`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `!k:real^3->real^3. k differentiable (at t)
                  ==> ((\x. lift((k x)$3)) has_derivative
                       (\v. lift((frechet_derivative k (at t) v)$3))) (at t)`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`k:real^3->real^3`; `frechet_derivative (k:real^3->real^3) (at t)`;
                   `t:real^3`] HAS_DERIVATIVE_COMPONENTWISE_AT) THEN
    REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    REWRITE_TAC[ASSUME `(k:real^3->real^3) differentiable (at t)`] THEN
    DISCH_THEN(MP_TAC o SPEC `3`) THEN REWRITE_TAC[DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\x. lift(((h:real^3->real^3) x)$3)) has_derivative
                 (\v. lift((frechet_derivative (f:real^3->real^3) (at t) v)$3))) (at t)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\x. lift(((f:real^3->real^3) x)$3)`;
                   `\v. lift((frechet_derivative (f:real^3->real^3) (at t) v)$3)`;
                   `\x:real^3. lift b`; `\v:real^3. vec 0:real^1`; `at (t:real^3)`]
      HAS_DERIVATIVE_ADD) THEN
    ASM_SIMP_TAC[HAS_DERIVATIVE_CONST; VECTOR_ADD_RID; GSYM LIFT_ADD];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. lift(((h:real^3->real^3) x)$3)`;
                 `\v. lift((frechet_derivative (h:real^3->real^3) (at t) v)$3)`;
                 `\v. lift((frechet_derivative (f:real^3->real^3) (at t) v)$3)`; `t:real^3`]
    FRECHET_DERIVATIVE_UNIQUE_AT) THEN
  ASM_SIMP_TAC[FUN_EQ_THM; LIFT_EQ]);;

let SCHY_HP_CRIT = prove
 (`!(A:real^2->real^2) b (g:real^3->real^3) g' t.
     smooth_map_on (:real^2) A /\ sch_neck g g'
     ==> (sch_crit (schy_hp A b o g) t <=> sch_crit g t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[sch_crit] THEN
  ASM_CASES_TAC `(t:real^3) IN sphere(vec 0,&1)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!v. (frechet_derivative (schy_hp (A:real^2->real^2) b o g) (at t) v)$3 =
                    (frechet_derivative (g:real^3->real^3) (at t) v)$3`
    (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC SCHY_DERIV3_EQ THEN EXISTS_TAC `b:real` THEN
  REWRITE_TAC[o_THM; SCHY_HP_FACTS] THEN
  SUBGOAL_THEN `(g:real^3->real^3) differentiable (at t)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `t:real^3`] SCH5_NECK_FACTS) THEN
    ASM_SIMP_TAC[SCH5_SPHERE_IN_ANNULUS];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^3)` THEN
  ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; SCHY_HP_SMOOTH]);;

let SCHY_HP_NECK = prove
 (`!(A:real^2->real^2) A' b (g:real^3->real^3) g'.
     diffeomorphism_on (:real^2) (:real^2) A A' /\ sch_neck g g'
     ==> sch_neck (schy_hp A b o g) (g' o schy_hp A' (--b))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[sch_neck; IMAGE_o] THEN
  MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN
  EXISTS_TAC `IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2))` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[sch_neck]; ALL_TAC] THEN
  MATCH_MP_TAC SCH_DIFFEO_RESTRICT_UNIV THEN
  ASM_SIMP_TAC[SCHY_HP_DIFFEO] THEN
  ASM_MESON_TAC[sch_neck; diffeomorphism_on]);;

let SCHY_HP_AT = prove
 (`!(A:real^2->real^2) b z w. schy_hp A b (sch5v_at (z - b) w) = sch5v_at z (A w)`,
  REWRITE_TAC[schy_hp; SCH5V_PR_AT; REAL_SUB_ADD]);;

let SCHY_HP_HCHART = prove
 (`!(A:real^2->real^2) A' b s (p:real^3) k1 k2.
     diffeomorphism_on (:real^2) (:real^2) A A' /\ sch_hchart s p k1 k2
     ==> sch_hchart (IMAGE (schy_hp A b) s) (schy_hp A b p) k1 k2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch_hchart] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `ph:real^2->real^2`
      (X_CHOOSE_THEN `ph':real^2->real^2` STRIP_ASSUME_TAC)))))) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`r:real`; `(A:real^2->real^2) o (ph:real^2->real^2)`;
                        `(ph':real^2->real^2) o (A':real^2->real^2)`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(!x. (A':real^2->real^2)(A x) = x) /\ (!y. (A:real^2->real^2)(A' y) = y)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on (:real^2) (:real^2) (A:real^2->real^2) A'` THEN
    SIMP_TAC[diffeomorphism_on; IN_UNIV];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN
    EXISTS_TAC `IMAGE (ph:real^2->real^2) (ball(vec 0,r))` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SCH_DIFFEO_RESTRICT_UNIV THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[diffeomorphism_on];
    REWRITE_TAC[o_THM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM sch5v_pr; GSYM SCHY_HP_FACTS] THEN REWRITE_TAC[sch5v_pr];
    MAP_EVERY X_GEN_TAC [`u:real^2`; `z:real`] THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SCHY_HP_FACTS]) THEN
    REWRITE_TAC[o_THM; SCHY_HP_FACTS] THEN
    SUBGOAL_THEN `vector[((A:real^2->real^2)(ph(u:real^2)))$1; (A(ph u))$2; z]:real^3 =
                  schy_hp A b (vector[(ph u)$1; (ph u)$2; z - b])` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM sch5v_at] THEN REWRITE_TAC[SCHY_HP_AT] THEN
      REWRITE_TAC[sch5v_at] THEN
      SUBGOAL_THEN `vector[(ph(u:real^2))$1; (ph u)$2]:real^2 = ph u` (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2];
      ALL_TAC] THEN
    SUBGOAL_THEN `!y. schy_hp (A:real^2->real^2) b y IN IMAGE (schy_hp A b) s <=> y IN s`
      (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN REWRITE_TAC[IN_IMAGE] THEN EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
        FIRST_X_ASSUM(MP_TAC o AP_TERM `schy_hp (A':real^2->real^2) (--b)`) THEN
        ASM_SIMP_TAC[SCHY_HP_INV] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
        DISCH_TAC THEN EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^2`; `z - b:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC]);;

let SCHY_HP_BIJ = prove
 (`!(A:real^2->real^2) A' b.
     diffeomorphism_on (:real^2) (:real^2) A A'
     ==> (!x. schy_hp A' (--b) (schy_hp A b x) = x) /\
         (!x. schy_hp A b (schy_hp A' (--b) x) = x) /\
         (!x y. schy_hp A b x = schy_hp A b y <=> x = y) /\
         (!x s. schy_hp A b x IN IMAGE (schy_hp A b) s <=> x IN s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `b:real` o MATCH_MP SCHY_HP_DIFFEO) THEN
  REWRITE_TAC[diffeomorphism_on; IN_UNIV] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]);;

let SCHY_HP_HCHART_EQ = prove
 (`!(A:real^2->real^2) A' b s (p:real^3) k1 k2.
     diffeomorphism_on (:real^2) (:real^2) A A'
     ==> (sch_hchart (IMAGE (schy_hp A b) s) (schy_hp A b p) k1 k2 <=>
          sch_hchart s p k1 k2)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [ALL_TAC; MATCH_MP_TAC SCHY_HP_HCHART THEN EXISTS_TAC `A':real^2->real^2` THEN
    ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`A':real^2->real^2`; `A:real^2->real^2`; `--b:real`;
                 `IMAGE (schy_hp (A:real^2->real^2) b) s`; `schy_hp (A:real^2->real^2) b p`;
                 `k1:real`; `k2:real`] SCHY_HP_HCHART) THEN
  ASM_SIMP_TAC[DIFFEOMORPHISM_ON_SYM] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `b:real` o MATCH_MP SCHY_HP_BIJ) THEN
  ASM_REWRITE_TAC[GSYM IMAGE_o; o_DEF; IMAGE_ID] THEN
  REWRITE_TAC[ETA_AX; IMAGE_ID]);;

let SCHY_HP_LEVEL_SET = prove
 (`!(A:real^2->real^2) b s a.
     {x | x IN IMAGE (schy_hp A b) s /\ x$3 = a + b} =
     IMAGE (schy_hp A b) {y:real^3 | y IN s /\ y$3 = a}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
  X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) MP_TAC) THEN
    ASM_REWRITE_TAC[SCHY_HP_FACTS] THEN DISCH_TAC THEN EXISTS_TAC `y:real^3` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[SCHY_HP_FACTS] THEN EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[]]);;

let SCHY_HP_MORSE = prove
 (`!(A:real^2->real^2) A' b (g:real^3->real^3) g'.
     diffeomorphism_on (:real^2) (:real^2) A A' /\ sch_neck g g'
     ==> (!t. sch_crit (schy_hp A b o g) t <=> sch_crit g t) /\
         (!t. ((schy_hp A b o g) t)$3 = (g t)$3 + b) /\
         IMAGE (schy_hp A b o g) (sphere(vec 0,&1)) =
         IMAGE (schy_hp A b) (IMAGE g (sphere(vec 0,&1))) /\
         sch_neck (schy_hp A b o g) (g' o schy_hp A' (--b)) /\
         (sch_morse g ==> sch_morse (schy_hp A b o g)) /\
         sch_saddles (schy_hp A b o g) = sch_saddles g /\
         (!a. sch_level (schy_hp A b o g) (a + b) = IMAGE (schy_hp A b) (sch_level g a)) /\
         (sch_bounds_ball (IMAGE (schy_hp A b o g) (sphere(vec 0,&1)))
          ==> sch_bounds_ball (IMAGE g (sphere(vec 0,&1))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) (A:real^2->real^2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `b:real` o MATCH_MP SCHY_HP_BIJ) THEN
  SUBGOAL_THEN `!t. sch_crit (schy_hp (A:real^2->real^2) b o (g:real^3->real^3)) t <=>
                    sch_crit g t`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SCHY_HP_CRIT THEN EXISTS_TAC `g':real^3->real^3` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. ((schy_hp (A:real^2->real^2) b o g) t)$3 = ((g:real^3->real^3) t)$3 + b`
  ASSUME_TAC THENL [REWRITE_TAC[o_THM; SCHY_HP_FACTS]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (schy_hp (A:real^2->real^2) b o (g:real^3->real^3)) (sphere(vec 0,&1)) =
                IMAGE (schy_hp A b) (IMAGE g (sphere(vec 0,&1)))` ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_o]; ALL_TAC] THEN
  SUBGOAL_THEN `!t k1 k2. sch_hchart (IMAGE (schy_hp (A:real^2->real^2) b o (g:real^3->real^3))
                                            (sphere(vec 0,&1)))
                                     ((schy_hp A b o g) t) k1 k2 <=>
                          sch_hchart (IMAGE g (sphere(vec 0,&1))) (g t) k1 k2`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN ASM_REWRITE_TAC[o_THM] THEN MATCH_MP_TAC SCHY_HP_HCHART_EQ THEN
    EXISTS_TAC `A':real^2->real^2` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SCHY_HP_NECK THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[sch_morse] THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[sch_saddles] THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN REWRITE_TAC[sch_level] THEN
    UNDISCH_TAC `IMAGE (schy_hp (A:real^2->real^2) b o (g:real^3->real^3)) (sphere(vec 0,&1)) =
                 IMAGE (schy_hp A b) (IMAGE g (sphere(vec 0,&1)))` THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[SCHY_HP_LEVEL_SET];
    DISCH_TAC THEN MATCH_MP_TAC SCH_BOUNDS_BALL_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`schy_hp (A:real^2->real^2) b`; `schy_hp (A':real^2->real^2) (--b)`] THEN
    ASM_SIMP_TAC[SCHY_HP_DIFFEO] THEN ASM_MESON_TAC[]]);;

let SCHY_HP_COMPONENTS = prove
 (`!(A:real^2->real^2) A' b (l:real^3->bool).
     diffeomorphism_on (:real^2) (:real^2) A A'
     ==> components(IMAGE (schy_hp A b) l) = IMAGE (IMAGE (schy_hp A b)) (components l) /\
         (FINITE(components l)
          ==> FINITE(components(IMAGE (schy_hp A b) l)) /\
              CARD(components(IMAGE (schy_hp A b) l)) = CARD(components l))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `b:real` o MATCH_MP SCHY_HP_BIJ) THEN
  SUBGOAL_THEN `components(IMAGE (schy_hp (A:real^2->real^2) b) l) =
                IMAGE (IMAGE (schy_hp A b)) (components l)` ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPONENTS THEN
    EXISTS_TAC `schy_hp (A':real^2->real^2) (--b)` THEN
    FIRST_ASSUM(MP_TAC o SPEC `b:real` o MATCH_MP SCHY_HP_DIFFEO) THEN
    REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
    REWRITE_TAC[homeomorphism] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      ASM_SIMP_TAC[SUBSET_UNIV; SMOOTH_MAP_ON_CONTINUOUS_ON];
      REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN ASM_REWRITE_TAC[IMAGE_ID] THEN
      REWRITE_TAC[ETA_AX; IMAGE_ID];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      ASM_SIMP_TAC[SUBSET_UNIV; SMOOTH_MAP_ON_CONTINUOUS_ON]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
  MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o AP_TERM `IMAGE (schy_hp (A':real^2->real^2) (--b))`) THEN
  ASM_REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN ASM_REWRITE_TAC[IMAGE_ID] THEN
  REWRITE_TAC[ETA_AX; IMAGE_ID]);;

(* ------------------------------------------------------------------------- *)
(* Normalization of the saddle chart.  A planar map h with                   *)
(* h(0) = 0 and derivative the identity at 0 agrees near 0 with a global    *)
(* diffeomorphism of the plane (the straight-line isotopy x + t(h x - x) is *)
(* an isotopy of embeddings of a small ball; pc_sch_isoext).  Hence a       *)
(* height-preserving ambient diffeomorphism puts the saddle at the origin   *)
(* with the chart map ph the identity (schy_chart).                          *)
(* ------------------------------------------------------------------------- *)

let SCHY_ONORM2 = prove
 (`!(Lm:real^2->real^2) c.
     linear Lm /\ norm(Lm(basis 1)) <= c /\ norm(Lm(basis 2)) <= c ==> onorm Lm <= &2 * c`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ONORM_LE_EQ] THEN X_GEN_TAC `v:real^2` THEN
  SUBGOAL_THEN `(Lm:real^2->real^2) v = v$1 % Lm(basis 1) + v$2 % Lm(basis 2)` SUBST1_TAC THENL
   [SUBGOAL_THEN `v:real^2 = v$1 % basis 1 + v$2 % basis 2`
      (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
     [REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs((v:real^2)$1) * norm((Lm:real^2->real^2)(basis 1)) +
              abs(v$2) * norm(Lm(basis 2))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(NORM_ARITH
      `norm(a:real^2) <= x /\ norm(b:real^2) <= y ==> norm(a + b) <= x + y`) THEN
    REWRITE_TAC[NORM_MUL; REAL_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`v:real^2`; `1`] COMPONENT_LE_NORM) THEN
  MP_TAC(ISPECL [`v:real^2`; `2`] COMPONENT_LE_NORM) THEN
  REWRITE_TAC[DIMINDEX_2; ARITH] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs((v:real^2)$1) * norm((Lm:real^2->real^2)(basis 1)) <= norm v * c /\
                abs((v:real^2)$2) * norm((Lm:real^2->real^2)(basis 2)) <= norm v * c`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE];
    REAL_ARITH_TAC]);;

let SCHY_NEARID = prove
 (`!(h:real^2->real^2) U.
     open U /\ vec 0 IN U /\ smooth_map_on U h /\ h(vec 0) = vec 0 /\
     (!v. frechet_derivative h (at (vec 0)) v = v)
     ==> ?rho Phi Phi'. &0 < rho /\ diffeomorphism_on (:real^2) (:real^2) Phi Phi' /\
                        (!x. x IN cball(vec 0,rho) ==> Phi x = h x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!i. ?d. &0 < d /\
                    !x. x IN ball(vec 0,d)
                        ==> x IN U /\
                            norm(frechet_derivative (h:real^2->real^2) (at x) (basis i) -
                                 basis i) <= &1 / &4`
  MP_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `(\x. frechet_derivative (h:real^2->real^2) (at x) (basis i))
                  continuous at (vec 0)` MP_TAC THENL
     [MP_TAC(ISPECL [`U:real^2->bool`; `h:real^2->real^2`; `basis i:real^2`]
        SMOOTH_MAP_ON_FRECHET_DERIVATIVE) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON) THEN
      ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT];
      ALL_TAC] THEN
    REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `&1 / &4`) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `open(U:real^2->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `vec 0:real^2`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min d1 d2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_BALL; REAL_LT_MIN] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `ball(vec 0:real^2,d2) SUBSET U` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2`) THEN
      SUBGOAL_THEN `dist(x:real^2,vec 0) < d1` (fun th -> REWRITE_TAC[th]) THENL
       [ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[dist] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `rho = min d1 d2 / &2` THEN
  SUBGOAL_THEN `&0 < rho` ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2. x IN ball(vec 0,&2 * rho)
                           ==> x IN U /\
                               onorm(\v. frechet_derivative (h:real^2->real^2) (at x) v - v)
                               <= &1 / &2`
  (LABEL_TAC "ON") THENL
   [X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_BALL] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN ball(vec 0,d1) /\ x IN ball(vec 0,d2)` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[IN_BALL] THEN UNDISCH_TAC `dist(vec 0:real^2,x) < &2 * rho` THEN
      EXPAND_TAC "rho" THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&1 / &2 = &2 * &1 / &4` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SCHY_ONORM2 THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(h:real^2->real^2) differentiable (at x)` ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^2->bool` THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LINEAR_COMPOSE_SUB THEN REWRITE_TAC[LINEAR_ID] THEN
      REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y:real^2. x IN ball(vec 0,&2 * rho) /\ y IN ball(vec 0,&2 * rho)
                             ==> norm(((h:real^2->real^2) x - x) - (h y - y)) <=
                                 &1 / &2 * norm(x - y)`
  (LABEL_TAC "LIP") THENL
   [MATCH_MP_TAC DIFFERENTIABLE_BOUND THEN
    EXISTS_TAC `\x v. frechet_derivative (h:real^2->real^2) (at x) v - v` THEN
    REWRITE_TAC[CONVEX_BALL] THEN CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
    MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN REWRITE_TAC[HAS_DERIVATIVE_ID] THEN
    REWRITE_TAC[ETA_AX; GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^2->bool` THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t (x:real^2). x + t % ((h:real^2->real^2) x - x)`;
                 `ball(vec 0:real^2,&2 * rho)`; `cball(vec 0:real^2,rho)`; `(:real^2)`]
    SCHI_ISOTOPY_EXTENSION_01) THEN
  REWRITE_TAC[OPEN_BALL; COMPACT_CBALL; OPEN_UNIV; IN_UNIV] THEN BETA_TAC THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[smooth_family] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
      SIMP_TAC[OPEN_PCROSS; OPEN_UNIV; OPEN_BALL] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`(:real^1) PCROSS ball(vec 0:real^2,&2 * rho)`; `\z:real^(1,2)finite_sum. z`]
          SMOOTH_MAP_ON_SNDCART_OPEN) THEN
        SIMP_TAC[OPEN_PCROSS; OPEN_UNIV; OPEN_BALL; SMOOTH_MAP_ON_ID] THEN
        REWRITE_TAC[o_DEF; ETA_AX];
        ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN
      SIMP_TAC[OPEN_PCROSS; OPEN_UNIV; OPEN_BALL] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`(:real^1) PCROSS ball(vec 0:real^2,&2 * rho)`; `\z:real^(1,2)finite_sum. z`]
          SMOOTH_MAP_ON_FSTCART_OPEN) THEN
        SIMP_TAC[OPEN_PCROSS; OPEN_UNIV; OPEN_BALL; SMOOTH_MAP_ON_ID] THEN
        REWRITE_TAC[o_DEF; ETA_AX];
        ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
      SIMP_TAC[OPEN_PCROSS; OPEN_UNIV; OPEN_BALL] THEN
      SUBGOAL_THEN `smooth_map_on ((:real^1) PCROSS ball(vec 0:real^2,&2 * rho))
                                  (sndcart:real^(1,2)finite_sum->real^2)` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`(:real^1) PCROSS ball(vec 0:real^2,&2 * rho)`; `\z:real^(1,2)finite_sum. z`]
          SMOOTH_MAP_ON_SNDCART_OPEN) THEN
        SIMP_TAC[OPEN_PCROSS; OPEN_UNIV; OPEN_BALL; SMOOTH_MAP_ON_ID] THEN
        REWRITE_TAC[o_DEF; ETA_AX];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(\z:real^(1,2)finite_sum. (h:real^2->real^2)(sndcart z)) = h o sndcart`
        SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `ball(vec 0:real^2,&2 * rho)` THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV; OPEN_BALL] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; SNDCART_PASTECART] THEN SIMP_TAC[];
        MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `U:real^2->bool` THEN
        ASM_REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[]];
      MAP_EVERY X_GEN_TAC [`t:real`; `x:real^2`; `y:real^2`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `norm((x:real^2) - y) =
                    t * norm(((h:real^2->real^2) y - y) - (h x - x))` ASSUME_TAC THENL
       [SUBGOAL_THEN `(x:real^2) - y = t % (((h:real^2->real^2) y - y) - (h x - x))` SUBST1_TAC THENL
         [UNDISCH_TAC `(x:real^2) + t % ((h:real^2->real^2) x - x) = y + t % (h y - y)` THEN
          VECTOR_ARITH_TAC;
          REWRITE_TAC[NORM_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 <= t ==> abs t = t`]];
        ALL_TAC] THEN
      USE_THEN "LIP" (MP_TAC o SPECL [`y:real^2`; `x:real^2`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      SUBGOAL_THEN `t * norm(((h:real^2->real^2) y - y) - (h x - x)) <=
                    &1 * norm((h y - y) - (h x - x))` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
      REWRITE_TAC[GSYM VECTOR_SUB_EQ; GSYM NORM_EQ_0] THEN
      MP_TAC(ISPEC `(x:real^2) - y` NORM_POS_LE) THEN
      MP_TAC(ISPECL [`x:real^2`; `y:real^2`] NORM_SUB) THEN ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`t:real`; `x:real^2`; `v:real^2`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(h:real^2->real^2) differentiable (at x)` ASSUME_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^2->bool` THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `frechet_derivative (\x:real^2. x + t % ((h:real^2->real^2) x - x)) (at x) =
                    (\v. v + t % (frechet_derivative h (at x) v - v))` ASSUME_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
        MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_DERIVATIVE_ID] THEN
        MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
        REWRITE_TAC[HAS_DERIVATIVE_ID] THEN REWRITE_TAC[ETA_AX; GSYM FRECHET_DERIVATIVE_WORKS] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `frechet_derivative (\x:real^2. x + t % ((h:real^2->real^2) x - x)) (at x) v =
                   vec 0` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[VECTOR_ARITH `v + t % (a - v) = vec 0 <=> v = --(t % (a - v)):real^2`] THEN
      DISCH_TAC THEN
      USE_THEN "ON" (MP_TAC o SPEC `x:real^2`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      SUBGOAL_THEN `norm(frechet_derivative (h:real^2->real^2) (at x) v - v) <= &1 / &2 * norm v`
      ASSUME_TAC THENL
       [MP_TAC(ISPEC `\v. frechet_derivative (h:real^2->real^2) (at x) v - v` ONORM) THEN
        ANTS_TAC THENL
         [MATCH_MP_TAC LINEAR_COMPOSE_SUB THEN REWRITE_TAC[LINEAR_ID; ETA_AX] THEN
          MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        DISCH_THEN(MP_TAC o SPEC `v:real^2` o CONJUNCT1) THEN REWRITE_TAC[] THEN
        MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
        ALL_TAC] THEN
      SUBGOAL_THEN `norm(v:real^2) <= &1 / &2 * norm v` MP_TAC THENL
       [UNDISCH_TAC `v:real^2 = --(t % (frechet_derivative (h:real^2->real^2) (at x) v - v))` THEN
        DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
        REWRITE_TAC[NORM_NEG; NORM_MUL] THEN
        ASM_SIMP_TAC[REAL_ARITH `&0 <= t ==> abs t = t`] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `&1 * norm(frechet_derivative (h:real^2->real^2) (at x) v - v)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
          ASM_REWRITE_TAC[REAL_MUL_LID]];
        REWRITE_TAC[GSYM NORM_EQ_0] THEN MP_TAC(ISPEC `v:real^2` NORM_POS_LE) THEN
        REAL_ARITH_TAC];
      REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Phi:real^2->real^2` (X_CHOOSE_THEN `Phi':real^2->real^2`
    (X_CHOOSE_THEN `L:real^2->bool` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`rho:real`; `Phi:real^2->real^2`; `Phi':real^2->real^2`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[] THEN VECTOR_ARITH_TAC);;

(* The normalization: a height-preserving ambient diffeomorphism puts a     *)
(* saddle at the origin with the exact chart in the form schy_chart.        *)

let SCHY_NORMALIZE = prove
 (`!(g:real^3->real^3) g' t0.
     sch_neck g g' /\ t0 IN sch_saddles g
     ==> ?A A' b r.
           diffeomorphism_on (:real^2) (:real^2) A A' /\
           schy_hp A b (g t0) = vec 0 /\
           schy_chart (IMAGE (schy_hp A b) (IMAGE g (sphere(vec 0,&1)))) r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch_saddles; IN_ELIM_THM; sch_hchart] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `ph:real^2->real^2`
        (X_CHOOSE_THEN `ph':real^2->real^2`
          (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
            (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CH")))))))))) THEN
  ABBREV_TAC `p = (g:real^3->real^3) t0` THEN
  ABBREV_TAC `q = vector[(p:real^3)$1; p$2]:real^2` THEN
  ABBREV_TAC `W = IMAGE (ph:real^2->real^2) (ball(vec 0,r))` THEN
  SUBGOAL_THEN `open(W:real^2->bool) /\ (q:real^2) IN W /\
                (ph':real^2->real^2) q = vec 0 /\
                smooth_map_on W (ph':real^2->real^2) /\
                smooth_map_on (ball(vec 0,r)) (ph:real^2->real^2) /\
                (!u. u IN ball(vec 0,r) ==> ph'((ph:real^2->real^2) u) = u) /\
                diffeomorphism_on W (ball(vec 0,r)) ph' ph`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
    UNDISCH_TAC `diffeomorphism_on (ball(vec 0,r)) W (ph:real^2->real^2) ph'` THEN
    DISCH_THEN(fun th -> ASSUME_TAC(MATCH_MP DIFFEOMORPHISM_ON_SYM th) THEN MP_TAC th) THEN
    REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `vec 0 IN ball(vec 0:real^2,r)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[CENTRE_IN_BALL]; ALL_TAC] THEN
    UNDISCH_TAC `(ph:real^2->real^2) (vec 0) = q` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[] THEN EXPAND_TAC "W" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `M = frechet_derivative (ph:real^2->real^2) (at (vec 0))` THEN
  ABBREV_TAC `L = frechet_derivative (ph':real^2->real^2) (at q)` THEN
  SUBGOAL_THEN `(!v. (M:real^2->real^2)((L:real^2->real^2) v) = v) /\
                (!v. L(M v) = v) /\ linear M /\ linear L` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `vec 0 IN ball(vec 0:real^2,r)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[CENTRE_IN_BALL]; ALL_TAC] THEN
    SUBGOAL_THEN `(ph:real^2->real^2)(vec 0) = q /\ (ph':real^2->real^2) q = vec 0`
    STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`W:real^2->bool`; `ball(vec 0:real^2,r)`; `ph':real^2->real^2`;
                     `ph:real^2->real^2`; `q:real^2`] SCH4_DIFFEO_DERIV_INV) THEN
      ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["M"; "L"] THEN SIMP_TAC[];
      MP_TAC(ISPECL [`ball(vec 0:real^2,r)`; `W:real^2->bool`; `ph:real^2->real^2`;
                     `ph':real^2->real^2`; `vec 0:real^2`] SCH4_DIFFEO_DERIV_INV) THEN
      ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["M"; "L"] THEN SIMP_TAC[];
      EXPAND_TAC "M" THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `ball(vec 0:real^2,r)` THEN
      ASM_REWRITE_TAC[OPEN_BALL];
      EXPAND_TAC "L" THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `W:real^2->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `U = {z:real^2 | z + q IN W}` THEN
  SUBGOAL_THEN `open(U:real^2->bool) /\ vec 0 IN U` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[IN_ELIM_THM; VECTOR_ADD_LID] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\z:real^2. z + q`; `W:real^2->bool`] CONTINUOUS_OPEN_PREIMAGE_UNIV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ADD THEN REWRITE_TAC[CONTINUOUS_AT_ID; CONTINUOUS_CONST];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z:real^2. (M:real^2->real^2)((ph':real^2->real^2)(z + q))`; `U:real^2->bool`]
    SCHY_NEARID) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_ADD_LID] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\z:real^2. (M:real^2->real^2)((ph':real^2->real^2)(z + q))) =
                    M o (ph' o (\z. z + q))` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `W:real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [EXPAND_TAC "U" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[];
        MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
        ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST]];
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[LINEAR_0]; ALL_TAC] THEN
      GEN_TAC THEN
      SUBGOAL_THEN `((\z:real^2. (M:real^2->real^2)((ph':real^2->real^2)(z + q))) has_derivative
                     (\v. M((L:real^2->real^2) v))) (at (vec 0))` MP_TAC THENL
       [SUBGOAL_THEN `(\z:real^2. (M:real^2->real^2)((ph':real^2->real^2)(z + q))) =
                      (M o ph') o (\z. z + q)` SUBST1_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        SUBGOAL_THEN `(\v:real^2. (M:real^2->real^2)((L:real^2->real^2) v)) =
                      (M o L) o (\v. v)` SUBST1_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
         [MP_TAC(ISPECL [`\z:real^2. z`; `\h:real^2. h`; `\z:real^2. q:real^2`;
                         `\h:real^2. vec 0:real^2`; `at(vec 0:real^2)`] HAS_DERIVATIVE_ADD) THEN
          REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST; VECTOR_ADD_RID];
          BETA_TAC THEN REWRITE_TAC[VECTOR_ADD_LID] THEN MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
           [EXPAND_TAC "L" THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
            MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `W:real^2->bool` THEN
            ASM_REWRITE_TAC[];
            MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN ASM_REWRITE_TAC[]]];
        DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real` (X_CHOOSE_THEN `Phi:real^2->real^2`
    (X_CHOOSE_THEN `Phi':real^2->real^2` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `?r1. &0 < r1 /\ r1 <= r /\
                     !u:real^2. u IN ball(vec 0,r1) ==> (ph:real^2->real^2) u - q IN cball(vec 0,rho)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(ph:real^2->real^2) continuous at (vec 0)` MP_TAC THENL
     [MP_TAC(ISPECL [`ball(vec 0:real^2,r)`; `ph:real^2->real^2`] SMOOTH_MAP_ON_CONTINUOUS_ON) THEN
      ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_BALL; CENTRE_IN_BALL];
      ALL_TAC] THEN
    REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `rho:real`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min d r` THEN ASM_REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    X_GEN_TAC `u:real^2` THEN REWRITE_TAC[IN_BALL; IN_CBALL; REAL_LT_MIN] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u:real^2`) THEN
    SUBGOAL_THEN `dist(u:real^2,vec 0) < d` (fun th -> REWRITE_TAC[th]) THENL
     [ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(ph:real^2->real^2)(vec 0) = q` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[dist; VECTOR_SUB_LZERO; NORM_NEG] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `A = \x:real^2. (L:real^2->real^2)((Phi:real^2->real^2)(x - q))` THEN
  ABBREV_TAC `A' = \y:real^2. (Phi':real^2->real^2)((M:real^2->real^2) y) + q` THEN
  SUBGOAL_THEN `diffeomorphism_on (:real^2) (:real^2) (A:real^2->real^2) A'` ASSUME_TAC THENL
   [SUBGOAL_THEN `(A:real^2->real^2) =
                  (L:real^2->real^2) o ((Phi:real^2->real^2) o (\x:real^2. x - q)) /\
                  (A':real^2->real^2) =
                  ((\x:real^2. x + q) o (Phi':real^2->real^2)) o (M:real^2->real^2)`
     (CONJUNCTS_THEN SUBST1_TAC) THENL
     [MAP_EVERY EXPAND_TAC ["A"; "A'"] THEN REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN EXISTS_TAC `(:real^2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN EXISTS_TAC `(:real^2)` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[diffeomorphism_on; OPEN_UNIV; IN_UNIV] THEN
      REWRITE_TAC[VECTOR_ARITH `(x - q) + q:real^2 = x`; VECTOR_ARITH `(x + q) - q:real^2 = x`] THEN
      REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN REPEAT CONJ_TAC THENL
       [X_GEN_TAC `y:real^2` THEN EXISTS_TAC `y + q:real^2` THEN VECTOR_ARITH_TAC;
        X_GEN_TAC `y:real^2` THEN EXISTS_TAC `y - q:real^2` THEN VECTOR_ARITH_TAC;
        MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
        REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST];
        MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
        REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST]];
      REWRITE_TAC[diffeomorphism_on; OPEN_UNIV; IN_UNIV] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN REPEAT CONJ_TAC THENL
       [X_GEN_TAC `y:real^2` THEN EXISTS_TAC `(M:real^2->real^2) y` THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `y:real^2` THEN EXISTS_TAC `(L:real^2->real^2) y` THEN ASM_REWRITE_TAC[];
        MP_TAC(ISPECL [`(:real^2)`; `\x:real^2. x`; `L:real^2->real^2`] SMOOTH_MAP_ON_LINEAR_O) THEN
        ASM_REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID] THEN REWRITE_TAC[o_DEF; ETA_AX];
        MP_TAC(ISPECL [`(:real^2)`; `\x:real^2. x`; `M:real^2->real^2`] SMOOTH_MAP_ON_LINEAR_O) THEN
        ASM_REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID] THEN REWRITE_TAC[o_DEF; ETA_AX]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u:real^2. u IN ball(vec 0,r1) ==> (A:real^2->real^2)(ph u) = u` ASSUME_TAC THENL
   [X_GEN_TAC `u:real^2` THEN DISCH_TAC THEN EXPAND_TAC "A" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(Phi:real^2->real^2)((ph:real^2->real^2) u - q) =
                  (M:real^2->real^2)((ph':real^2->real^2)((ph u - q) + q))` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `(ph:real^2->real^2) u - q` o check
        (fun th -> can (term_match [] `!x:real^2. x IN cball(vec 0,rho) ==> P x`) (concl th))) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `(a - q) + q:real^2 = a`] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(u:real^2) IN ball(vec 0,r1)` THEN UNDISCH_TAC `r1 <= r` THEN
    REWRITE_TAC[IN_BALL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`A:real^2->real^2`; `A':real^2->real^2`; `--((p:real^3)$3)`; `r1:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[schy_hp] THEN
    SUBGOAL_THEN `sch5v_pr (p:real^3) = q` SUBST1_TAC THENL
     [EXPAND_TAC "q" THEN REWRITE_TAC[sch5v_pr]; ALL_TAC] THEN
    SUBGOAL_THEN `(A:real^2->real^2) q = vec 0` SUBST1_TAC THENL
     [SUBGOAL_THEN `q = (ph:real^2->real^2) (vec 0)` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[CENTRE_IN_BALL];
      ALL_TAC] THEN
    REWRITE_TAC[sch5v_at; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VEC_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[schy_chart] THEN
  REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  ABBREV_TAC `u = vector[(x:real^3)$1; x$2]:real^2` THEN
  SUBGOAL_THEN `(u:real^2) IN ball(vec 0,r1)` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[GSYM sch5v_pr] THEN
    ASM_SIMP_TAC[SCH5V_PR_FACTS];
    ALL_TAC] THEN
  MP_TAC(SPEC `--((p:real^3)$3)` (MATCH_MP SCHY_HP_BIJ
    (ASSUME `diffeomorphism_on (:real^2) (:real^2) (A:real^2->real^2) A'`))) THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN STRIP_TAC THEN
  SUBGOAL_THEN `schy_hp (A':real^2->real^2) ((p:real^3)$3) x =
                vector[((ph:real^2->real^2) u)$1; (ph u)$2; (x:real^3)$3 + p$3]` ASSUME_TAC THENL
   [REWRITE_TAC[schy_hp] THEN
    SUBGOAL_THEN `sch5v_pr (x:real^3) = u` SUBST1_TAC THENL
     [EXPAND_TAC "u" THEN REWRITE_TAC[sch5v_pr]; ALL_TAC] THEN
    SUBGOAL_THEN `(A':real^2->real^2) u = (ph:real^2->real^2) u` SUBST1_TAC THENL
     [SUBGOAL_THEN `(A':real^2->real^2) ((A:real^2->real^2) ((ph:real^2->real^2) u)) = ph u`
      MP_TAC THENL
       [UNDISCH_TAC `diffeomorphism_on (:real^2) (:real^2) (A:real^2->real^2) A'` THEN
        SIMP_TAC[diffeomorphism_on; IN_UNIV];
        ASM_SIMP_TAC[]];
      REWRITE_TAC[sch5v_at]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN IMAGE (schy_hp (A:real^2->real^2) (--((p:real^3)$3)))
                                     (IMAGE (g:real^3->real^3) (sphere(vec 0,&1))) <=>
                schy_hp A' (p$3) x IN IMAGE g (sphere(vec 0,&1))` SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`schy_hp (A':real^2->real^2) ((p:real^3)$3) x`;
                                  `IMAGE (g:real^3->real^3) (sphere(vec 0,&1))`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "CH" (MP_TAC o SPECL [`u:real^2`; `(x:real^3)$3 + (p:real^3)$3`]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `(u:real^2) IN ball(vec 0,r1)` THEN UNDISCH_TAC `r1 <= r` THEN
      REWRITE_TAC[IN_BALL] THEN REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    DISCH_THEN SUBST1_TAC] THEN
  EXPAND_TAC "u" THEN REWRITE_TAC[VECTOR_2] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Orientability lemma.  On a collared sphere with the                       *)
(* normalized saddle chart, the two upper branch points of the level e and  *)
(* the two lower branch points of the level --e cannot both lie on single   *)
(* components: otherwise the ascending arc through the saddle closed by an  *)
(* arc of the upper component is a Jordan curve on S whose two sides near   *)
(* the saddle are joined, through the descending arcs and the lower         *)
(* component, without meeting it (Jordan curve theorem in S minus a point). *)
(* ------------------------------------------------------------------------- *)

let SCHY_CONNECTED_SIDE = prove
 (`!(c:real^N->bool) u v.
     connected c /\ open u /\ open v /\ u INTER v = {} /\ c SUBSET u UNION v
     ==> c SUBSET u \/ c SUBSET v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[connected; NOT_EXISTS_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPECL [`u:real^N->bool`; `v:real^N->bool`])
    STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* The topological core, for a sphere-like set s with s minus q homeomorphic *)
(* to the plane.                                                            *)

let SCHY_JORDAN_CORE = prove
 (`!(s:real^3->bool) q (h:real^3->real^2) h' (c:real^1->real^3) p n1 n2 m eps.
     homeomorphism (s DELETE q,(:real^2)) (h,h') /\
     simple_path c /\ pathfinish c = pathstart c /\ path_image c SUBSET s DELETE q /\
     p IN path_image c /\
     connected n1 /\ connected n2 /\ connected m /\
     n1 SUBSET (s DELETE q) DIFF path_image c /\ n2 SUBSET (s DELETE q) DIFF path_image c /\
     m SUBSET (s DELETE q) DIFF path_image c /\
     ~(m INTER n1 = {}) /\ ~(m INTER n2 = {}) /\
     &0 < eps /\ (s INTER ball(p,eps)) DIFF path_image c SUBSET n1 UNION n2
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `!x y. x IN s DELETE q /\ y IN s DELETE q /\ (h:real^3->real^2) x = h y ==> x = y`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `simple_path ((h:real^3->real^2) o (c:real^1->real^3))` ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLE_PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s DELETE (q:real^3)` THEN
      ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `(h:real^3->real^2) o (c:real^1->real^3)` JORDAN_CURVE_THEOREM) THEN
  ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE] THEN
  DISCH_THEN(X_CHOOSE_THEN `ins:real^2->bool` (X_CHOOSE_THEN `out:real^2->bool`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `G = IMAGE (h:real^3->real^2) (path_image c)` THEN
  SUBGOAL_THEN `!k. k SUBSET (s DELETE (q:real^3)) DIFF path_image c /\ connected k
                    ==> IMAGE (h:real^3->real^2) k SUBSET ins \/ IMAGE h k SUBSET out`
  (LABEL_TAC "SIDE") THENL
   [X_GEN_TAC `k:real^3->bool` THEN STRIP_TAC THEN MATCH_MP_TAC SCHY_CONNECTED_SIDE THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s DELETE (q:real^3)` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      EXPAND_TAC "G" THEN
      MP_TAC(ASSUME `k SUBSET (s DELETE (q:real^3)) DIFF path_image c`) THEN
      MP_TAC(ASSUME `path_image (c:real^1->real^3) SUBSET s DELETE q`) THEN
      MP_TAC(ASSUME `!x y. x IN s DELETE q /\ y IN s DELETE q /\ (h:real^3->real^2) x = h y
                           ==> x = y`) THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ins INTER (G:real^2->bool) = {} /\ out INTER G = {}` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ins UNION out = (:real^2) DIFF G` THEN SET_TAC[]; ALL_TAC] THEN
  USE_THEN "SIDE" (MP_TAC o SPEC `n1:real^3->bool`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "SIDE" (MP_TAC o SPEC `n2:real^3->bool`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "SIDE" (MP_TAC o SPEC `m:real^3->bool`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `?w1 w2. open w1 /\ open w2 /\ w1 INTER w2 = {} /\ w2 INTER G = {} /\
                        frontier w2 = G /\
                        IMAGE (h:real^3->real^2) m SUBSET w1 /\
                        (IMAGE h n1 SUBSET w1 \/ IMAGE h n1 SUBSET w2) /\
                        (IMAGE h n2 SUBSET w1 \/ IMAGE h n2 SUBSET w2)`
  MP_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
      can (find_term ((=) `m:real^3->bool`)) (concl th))) THENL
     [MAP_EVERY EXISTS_TAC [`ins:real^2->bool`; `out:real^2->bool`] THEN ASM_REWRITE_TAC[];
      MAP_EVERY EXISTS_TAC [`out:real^2->bool`; `ins:real^2->bool`] THEN
      ONCE_REWRITE_TAC[INTER_COMM] THEN ONCE_REWRITE_TAC[DISJ_SYM] THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  POP_ASSUM_LIST(MAP_EVERY (fun th -> if can (find_term ((=) `ins:real^2->bool`)) (concl th)
                                     then ALL_TAC else ASSUME_TAC th) o rev) THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:real^2->bool` (X_CHOOSE_THEN `w2:real^2->bool`
    (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)))) THEN
  SUBGOAL_THEN `IMAGE (h:real^3->real^2) n1 SUBSET w1` ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
      can (find_term ((=) `n1:real^3->bool`)) (concl th))) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((m:real^3->bool) INTER n1 = {})` THEN
    UNDISCH_TAC `(w1:real^2->bool) INTER w2 = {}` THEN
    UNDISCH_TAC `IMAGE (h:real^3->real^2) m SUBSET w1` THEN
    UNDISCH_TAC `IMAGE (h:real^3->real^2) n1 SUBSET w2` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h:real^3->real^2) n2 SUBSET w1` ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
      can (find_term ((=) `n2:real^3->bool`)) (concl th))) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((m:real^3->bool) INTER n2 = {})` THEN
    UNDISCH_TAC `(w1:real^2->bool) INTER w2 = {}` THEN
    UNDISCH_TAC `IMAGE (h:real^3->real^2) m SUBSET w1` THEN
    UNDISCH_TAC `IMAGE (h:real^3->real^2) n2 SUBSET w2` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3) IN s DELETE q /\ (h:real^3->real^2) p IN G` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (h:real^3->real^2) (path_image c) = G` THEN
     DISCH_THEN(SUBST1_TAC o SYM) THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^3->real^2) p IN closure w2` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!x:real^2 a b. x IN a /\ a SUBSET b ==> x IN b`) THEN
    EXISTS_TAC `G:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `frontier(w2:real^2->bool) = G` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[frontier] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?d. &0 < d /\
                    !w. dist(w,(h:real^3->real^2) p) < d ==> dist((h':real^2->real^3) w,p) < eps`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(h':real^2->real^3) continuous (at ((h:real^3->real^2) p))` MP_TAC THENL
     [UNDISCH_TAC `(h':real^2->real^3) continuous_on (:real^2)` THEN
      SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV];
      ALL_TAC] THEN
    SUBGOAL_THEN `(h':real^2->real^3)((h:real^3->real^2) p) = p` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `eps:real`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(h:real^3->real^2) p IN closure w2` THEN
  REWRITE_TAC[CLOSURE_APPROACHABLE] THEN DISCH_THEN(MP_TAC o SPEC `d:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `dist(w:real^2,(h:real^3->real^2) p) < d`)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(h':real^2->real^3) w IN s DELETE q /\ (h:real^3->real^2)(h' w) = w`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[IN_UNIV]]; ALL_TAC] THEN
  SUBGOAL_THEN `~((h':real^2->real^3) w IN path_image c)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(w:real^2) IN G` MP_TAC THENL
     [UNDISCH_TAC `IMAGE (h:real^3->real^2) (path_image c) = G` THEN
     DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(h':real^2->real^3) w` THEN
      ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h':real^2->real^3) w IN n1 UNION n2` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      is_binary "SUBSET" (concl th) &&
      can (find_term ((=) `eps:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_INTER; IN_BALL] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `(w:real^2) IN w1` MP_TAC THENL
     [UNDISCH_TAC `IMAGE (h:real^3->real^2) n1 SUBSET w1` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      DISCH_THEN(MP_TAC o SPEC `(h':real^2->real^3) w`) THEN ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    SUBGOAL_THEN `(w:real^2) IN w1` MP_TAC THENL
     [UNDISCH_TAC `IMAGE (h:real^3->real^2) n2 SUBSET w1` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      DISCH_THEN(MP_TAC o SPEC `(h':real^2->real^3) w`) THEN ASM_REWRITE_TAC[];
      ASM SET_TAC[]]]);;

(* A collared sphere minus a point is homeomorphic to the plane.            *)

let SCHY_PUNCTURED = prove
 (`!(g:real^3->real^3) g' q.
     sch_neck g g' /\ q IN IMAGE g (sphere(vec 0,&1))
     ==> ?h:real^3->real^2 h'. homeomorphism ((IMAGE g (sphere(vec 0,&1))) DELETE q,(:real^2))
                                             (h,h')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `tq:real^3` STRIP_ASSUME_TAC o REWRITE_RULE[IN_IMAGE]) THEN
  SUBGOAL_THEN `homeomorphism (sphere(vec 0:real^3,&1),IMAGE (g:real^3->real^3) (sphere(vec 0,&1)))
                              (g,g')` ASSUME_TAC THENL
   [UNDISCH_TAC `sch_neck (g:real^3->real^3) g'` THEN
    REWRITE_TAC[sch_neck; diffeomorphism_on] THEN STRIP_TAC THEN
    SUBGOAL_THEN `sphere(vec 0:real^3,&1) SUBSET annulus (&1 / &2) (&2)` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET] THEN MESON_TAC[SCH5_SPHERE_IN_ANNULUS]; ALL_TAC] THEN
    SUBGOAL_THEN `(g:real^3->real^3) continuous_on sphere(vec 0,&1) /\
                  (g':real^3->real^3) continuous_on (IMAGE g (sphere(vec 0,&1)))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THENL
       [EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool`;
        EXISTS_TAC `IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2))`] THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; IMAGE_SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN `!x. x IN sphere(vec 0:real^3,&1) ==> (g':real^3->real^3)(g x) = x`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!x. x IN annulus (&1 / &2) (&2) ==> (g':real^3->real^3)(g x) = x`) (concl th))) THEN
      ASM_SIMP_TAC[SCH5_SPHERE_IN_ANNULUS];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[homeomorphism; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `!(f:real^3->real^3) g s.
      (!x. x IN s ==> f(g x) = x) ==> IMAGE f (IMAGE g s) = s`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(IMAGE (g:real^3->real^3) (sphere(vec 0,&1))) DELETE q homeomorphic
                sphere(vec 0:real^3,&1) DELETE tq` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `g':real^3->real^3`] THEN
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`sphere(vec 0:real^3,&1)`;
                          `IMAGE (g:real^3->real^3) (sphere(vec 0,&1))`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL [SET_TAC[]; SET_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sphere(vec 0:real^3,&1) DELETE tq homeomorphic {x:real^3 | basis 3 dot x = &0}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHIC_PUNCTURED_SPHERE_AFFINE THEN
    ASM_REWRITE_TAC[REAL_LT_01; AFFINE_HYPERPLANE] THEN
    SIMP_TAC[AFF_DIM_HYPERPLANE; BASIS_NONZERO; DIMINDEX_3; ARITH] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `{x:real^3 | basis 3 dot x = &0} homeomorphic (:real^2)` ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHIC_AFFINE_SETS THEN REWRITE_TAC[AFFINE_HYPERPLANE; AFFINE_UNIV] THEN
    SIMP_TAC[AFF_DIM_HYPERPLANE; BASIS_NONZERO; DIMINDEX_3; ARITH; AFF_DIM_UNIV; DIMINDEX_2] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM homeomorphic] THEN
  MATCH_MP_TAC(ISPECL [`(IMAGE (g:real^3->real^3) (sphere(vec 0,&1))) DELETE q`;
                       `sphere(vec 0:real^3,&1) DELETE tq`; `(:real^2)`] HOMEOMORPHIC_TRANS) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(ISPECL [`sphere(vec 0:real^3,&1) DELETE tq`; `{x:real^3 | basis 3 dot x = &0}`;
                       `(:real^2)`] HOMEOMORPHIC_TRANS) THEN
  ASM_REWRITE_TAC[]);;

(* The ascending arc of the normalized saddle from the left to the right    *)
(* branch point of the level e.                                              *)

let schy_aarc = new_definition
 `schy_aarc (e:real) (t:real^1) =
    vector[(&2 * drop t - &1) * sqrt e; &0; ((&2 * drop t - &1) * sqrt e) pow 2]:real^3`;;

let SCHY_AARC = prove
 (`!e. &0 < e
       ==> arc (schy_aarc e) /\ pathstart(schy_aarc e) = schy_lpt e /\
           pathfinish(schy_aarc e) = schy_rpt e /\
           path_image(schy_aarc e) =
           {x:real^3 | x$2 = &0 /\ x$3 = x$1 pow 2 /\ abs(x$1) <= sqrt e}`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < sqrt e /\ sqrt e pow 2 = e` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[arc; path] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
      REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      SUBGOAL_THEN `schy_aarc e =
                    (\t:real^1. vector[(&2 * t$1 - &1) * sqrt e; &0;
                                       ((&2 * t$1 - &1) * sqrt e) pow 2]:real^3)`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; schy_aarc; drop]; ALL_TAC] THEN
      MATCH_MP_TAC SCH5C_SV3 THEN REWRITE_TAC[OPEN_UNIV; SCH5C_SR_CONST] THEN
      SUBGOAL_THEN `smooth_map_on (:real^1) (\t:real^1. lift((&2 * t$1 - &1) * sqrt e))`
      ASSUME_TAC THENL
       [MATCH_MP_TAC SCH5C_SR_MUL THEN REWRITE_TAC[OPEN_UNIV; SCH5C_SR_CONST] THEN
        MATCH_MP_TAC SCH5C_SR_SUB THEN REWRITE_TAC[OPEN_UNIV; SCH5C_SR_CONST] THEN
        MATCH_MP_TAC SCH5C_SR_MUL THEN SIMP_TAC[OPEN_UNIV; SCH5C_SR_CONST; SCH5C_SR_COMP];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SCH5C_SR_POW THEN ASM_REWRITE_TAC[OPEN_UNIV];
      MAP_EVERY X_GEN_TAC [`s:real^1`; `t:real^1`] THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; schy_aarc] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (MP_TAC o AP_TERM `\v:real^3. v$1`))) THEN
      REWRITE_TAC[VECTOR_3] THEN
      ASM_SIMP_TAC[REAL_EQ_MUL_RCANCEL; REAL_LT_IMP_NZ] THEN
      REWRITE_TAC[GSYM DROP_EQ] THEN REAL_ARITH_TAC];
    REWRITE_TAC[pathstart; schy_aarc; schy_lpt; DROP_VEC] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
    ASM_REWRITE_TAC[REAL_ARITH `(&2 * &0 - &1) * s = --s`; REAL_POW_NEG; ARITH];
    REWRITE_TAC[pathfinish; schy_aarc; schy_rpt; DROP_VEC] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
    ASM_REWRITE_TAC[REAL_ARITH `(&2 * &1 - &1) * s = s`];
    REWRITE_TAC[path_image; EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_INTERVAL_1; DROP_VEC] THEN
    X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[schy_aarc; VECTOR_3] THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < s ==> abs s = s`] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      STRIP_TAC THEN EXISTS_TAC `lift(((x:real^3)$1 / sqrt e + &1) / &2)` THEN
      REWRITE_TAC[LIFT_DROP; schy_aarc] THEN
      SUBGOAL_THEN `(&2 * ((x:real^3)$1 / sqrt e + &1) / &2 - &1) * sqrt e = x$1`
      SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < sqrt e` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `abs((x:real^3)$1 / sqrt e) <= &1` MP_TAC THENL
       [ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < s ==> abs s = s`; REAL_LE_LDIV_EQ] THEN
        ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC]]]);;

let SCHY_NORM2 = prove
 (`!a b. norm(vector[a; b]:real^2) = sqrt(a pow 2 + b pow 2)`,
  REWRITE_TAC[vector_norm; DOT_2; VECTOR_2; REAL_POW_2]);;

let SCHY_LEMMA_J = prove
 (`!(g:real^3->real^3) g' r e K K'.
     SCH_LEVEL_NECK_STATEMENT /\
     sch_neck g g' /\ sch_morse g /\ schy_chart (IMAGE g (sphere(vec 0,&1))) r /\
     &0 < e /\ &16 * e < r pow 2 /\ (!t. sch_crit g t ==> ~((g t)$3 = e)) /\
     K IN components(sch_level g e) /\ schy_lpt e IN K /\ schy_rpt e IN K /\
     K' IN components(sch_level g (--e)) /\
     vector[&0; sqrt e; --e] IN K' /\ vector[&0; --(sqrt e); --e] IN K'
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `S = IMAGE (g:real^3->real^3) (sphere(vec 0,&1))` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_binary "schy_chart" (concl th))) THEN
  REWRITE_TAC[schy_chart] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CH"))) THEN
  SUBGOAL_THEN `&0 < sqrt e /\ sqrt e pow 2 = e /\ &4 * sqrt e < r /\ &16 * e < r`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE] THEN
    SUBGOAL_THEN `(&4 * sqrt e) pow 2 < r pow 2` MP_TAC THENL
     [REWRITE_TAC[REAL_POW_MUL] THEN ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `2` THEN
      ASM_REWRITE_TAC[ARITH] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `r pow 2 < r` MP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `x = r * r /\ r * r < r * &1 ==> x < r`) THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `se = sqrt e` THEN
  SUBGOAL_THEN `(K:real^3->bool) SUBSET S /\ (!x. x IN K ==> x$3 = e) /\
                (K':real^3->bool) SUBSET S /\ (!x. x IN K' ==> x$3 = --e) /\
                connected (K':real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`sch_level (g:real^3->real^3) e`; `K:real^3->bool`] IN_COMPONENTS_SUBSET) THEN
    MP_TAC(ISPECL [`sch_level (g:real^3->real^3) (--e)`; `K':real^3->bool`]
      IN_COMPONENTS_SUBSET) THEN
    MP_TAC(ISPECL [`sch_level (g:real^3->real^3) (--e)`; `K':real^3->bool`]
      IN_COMPONENTS_CONNECTED) THEN
    ASM_REWRITE_TAC[sch_level] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `path_connected (K:real^3->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `SCH_LEVEL_NECK_STATEMENT` THEN REWRITE_TAC[SCH_LEVEL_NECK_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPECL [`g:real^3->real^3`; `g':real^3->real^3`; `e:real`;
                               `K:real^3->bool`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `Fn:real^2->real^2` (X_CHOOSE_THEN `Fn':real^2->real^2`
      STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PATH_CONNECTED_CONTINUOUS_IMAGE THEN
    SIMP_TAC[PATH_CONNECTED_SPHERE; DIMINDEX_2; LE_REFL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `annulus (&1 / &2) (&2):real^2->bool` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      SUBGOAL_THEN `(\x:real^2. vector[((Fn:real^2->real^2) x)$1; (Fn x)$2; e]:real^3) =
                    sch5v_at e o Fn` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM; sch5v_at]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^2)` THEN
      REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; SCH5V_PR_AT_SMOOTH] THEN
      UNDISCH_TAC `sch_neck (Fn:real^2->real^2) Fn'` THEN
      SIMP_TAC[sch_neck; diffeomorphism_on];
      REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN
      GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [PATH_CONNECTED_ARCWISE]) THEN
  DISCH_THEN(MP_TAC o SPECL [`schy_rpt e`; `schy_lpt e`]) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[schy_rpt; schy_lpt; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^1->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `e:real` SCHY_AARC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "AI" o REWRITE_RULE[EXTENSION; IN_ELIM_THM])))) THEN
  ABBREV_TAC `c = schy_aarc e ++ b` THEN
  SUBGOAL_THEN `path_image(schy_aarc e) INTER path_image b SUBSET
                {schy_lpt e,schy_rpt e}` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; IN_INSERT; NOT_IN_EMPTY] THEN X_GEN_TAC `x:real^3` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^3)$3 = e` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(x:real^3) IN path_image(schy_aarc e)` THEN
    USE_THEN "AI" (fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^3)$1 = --se \/ x$1 = se` MP_TAC THENL
     [SUBGOAL_THEN `((x:real^3)$1 + se) * (x$1 - se) = &0` MP_TAC THENL
       [UNDISCH_TAC `(x:real^3)$3 = x$1 pow 2` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `se pow 2 = e` THEN CONV_TAC REAL_RING;
        REWRITE_TAC[REAL_ENTIRE] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[schy_lpt; schy_rpt; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `simple_path c /\ pathfinish c = pathstart c /\
                path_image c = path_image(schy_aarc e) UNION path_image(b:real^1->real^3)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SIMPLE_PATH_JOIN_LOOP THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN];
      MATCH_MP_TAC PATH_IMAGE_JOIN THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `q = vector[--(&2 * se); &0; &4 * e]:real^3` THEN
  SUBGOAL_THEN `(q:real^3) IN S /\ ~(q IN path_image c)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "CH" (MP_TAC o SPEC `q:real^3`) THEN EXPAND_TAC "q" THEN
      REWRITE_TAC[VECTOR_3; REAL_POW_NEG; ARITH; REAL_POW_MUL] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ANTS_TAC THENL
       [ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> abs(&4 * e) = &4 * e`] THEN ASM_REAL_ARITH_TAC;
        DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC];
      ASM_REWRITE_TAC[IN_UNION] THEN
      USE_THEN "AI" (fun th -> REWRITE_TAC[th]) THEN EXPAND_TAC "q" THEN
      REWRITE_TAC[VECTOR_3; DE_MORGAN_THM] THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_ABS_NEG] THEN
        ASM_SIMP_TAC[REAL_ARITH `&0 < s ==> abs(&2 * s) = &2 * s`] THEN ASM_REAL_ARITH_TAC;
        DISCH_TAC THEN
        SUBGOAL_THEN `(vector[--(&2 * se); &0; &4 * e]:real^3)$3 = e` MP_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
            `!x:real^3. x IN K ==> x$3 = e`) (concl th))) THEN ASM SET_TAC[];
          REWRITE_TAC[VECTOR_3] THEN ASM_REAL_ARITH_TAC]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `q:real^3`] SCHY_PUNCTURED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^3->real^2` (X_CHOOSE_THEN `h':real^2->real^3`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `phi = \u:real^2. vector[u$1; u$2; u$1 pow 2 - u$2 pow 2]:real^3` THEN
  ABBREV_TAC `n1 = IMAGE (phi:real^2->real^3) (ball(vec 0,se / &2) INTER {u:real^2 | &0 < u$2})` THEN
  ABBREV_TAC `n2 = IMAGE (phi:real^2->real^3) (ball(vec 0,se / &2) INTER {u:real^2 | u$2 < &0})` THEN
  ABBREV_TAC `dp = IMAGE (\t:real^1. vector[&0; drop t; --(drop t pow 2)]:real^3)
                         (interval[lift(se / &4),lift se])` THEN
  ABBREV_TAC `dm = IMAGE (\t:real^1. vector[&0; --(drop t); --(drop t pow 2)]:real^3)
                         (interval[lift(se / &4),lift se])` THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) (phi:real^2->real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "phi" THEN MATCH_MP_TAC SCH5C_SV3 THEN
    SIMP_TAC[OPEN_UNIV; SCH5C_SR_COMP] THEN MATCH_MP_TAC SCH5C_SR_SUB THEN
    SIMP_TAC[OPEN_UNIV; SCH5C_SR_POW; SCH5C_SR_COMP];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u:real^2. norm u < se / &2 ==> (phi:real^2->real^3) u IN S /\
                           ~(phi u = q) /\ abs((phi u)$3) < e / &4 /\ (phi u)$2 = u$2`
  (LABEL_TAC "PH") THENL
   [X_GEN_TAC `u:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(u:real^2)$1 pow 2 + u$2 pow 2 < e / &4` ASSUME_TAC THENL
     [SUBGOAL_THEN `(u:real^2)$1 pow 2 + u$2 pow 2 = norm u pow 2` SUBST1_TAC THENL
       [REWRITE_TAC[NORM_POW_2; DOT_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `norm(u:real^2) pow 2 < (se / &2) pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[NORM_POS_LE; ARITH]; ALL_TAC] THEN
      UNDISCH_TAC `se pow 2 = e` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "phi" THEN REWRITE_TAC[VECTOR_3] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "CH" (MP_TAC o SPEC `vector[(u:real^2)$1; u$2; u$1 pow 2 - u$2 pow 2]:real^3`) THEN
      REWRITE_TAC[VECTOR_3] THEN ANTS_TAC THENL
       [MP_TAC(SPEC `(u:real^2)$1` REAL_LE_POW_2) THEN MP_TAC(SPEC `(u:real^2)$2` REAL_LE_POW_2) THEN
        ASM_REAL_ARITH_TAC;
        SIMP_TAC[]];
      EXPAND_TAC "q" THEN REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
      DISCH_TAC THEN MP_TAC(ISPECL [`u:real^2`; `1`] COMPONENT_LE_NORM) THEN
      REWRITE_TAC[DIMINDEX_2; ARITH] THEN ASM_REAL_ARITH_TAC;
      MP_TAC(SPEC `(u:real^2)$1` REAL_LE_POW_2) THEN MP_TAC(SPEC `(u:real^2)$2` REAL_LE_POW_2) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t:real^1. t IN interval[lift(se / &4),lift se]
                ==> se / &4 <= drop t /\ drop t <= se /\ &0 < drop t /\
                    drop t pow 2 <= e /\ &0 < drop t pow 2`
  (LABEL_TAC "TI") THENL
   [X_GEN_TAC `t:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [UNDISCH_TAC `se pow 2 = e` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
SUBGOAL_THEN `!x:real^3. x IN path_image c ==> &0 <= x$3` (LABEL_TAC "NN") THENL
   [ASM_REWRITE_TAC[IN_UNION] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_POW_2];
      SUBGOAL_THEN `(x:real^3)$3 = e` (fun th -> REWRITE_TAC[th]) THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
          `!x:real^3. x IN K ==> x$3 = e`) (concl th))) THEN ASM SET_TAC[];
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN path_image c ==> (x$2 = &0 \/ x$3 = e)` (LABEL_TAC "NE") THENL
   [ASM_REWRITE_TAC[IN_UNION] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THENL
     [ASM_REWRITE_TAC[];
      DISJ2_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!x:real^3. x IN K ==> x$3 = e`) (concl th))) THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(dp:real^3->bool) SUBSET (S DELETE q) DIFF path_image c /\
                (dm:real^3->bool) SUBSET (S DELETE q) DIFF path_image c /\
                connected (dp:real^3->bool) /\ connected (dm:real^3->bool) /\
                vector[&0; se; --e] IN dp /\ vector[&0; --se; --e] IN dm /\
                (phi:real^2->real^3) (vector[&0; se / &4]) IN dp /\
                phi (vector[&0; --(se / &4)]) IN dm`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `!sg. sg = &1 \/ sg = -- &1
                       ==> IMAGE (\t:real^1. vector[&0; sg * drop t; --(drop t pow 2)]:real^3)
                                 (interval[lift(se / &4),lift se]) SUBSET
                           (S DELETE q) DIFF path_image c /\
                           connected (IMAGE (\t:real^1. vector[&0; sg * drop t; --(drop t pow 2)]:real^3)
                                            (interval[lift(se / &4),lift se])) /\
                           vector[&0; sg * se; --e] IN
                           IMAGE (\t:real^1. vector[&0; sg * drop t; --(drop t pow 2)]:real^3)
                                 (interval[lift(se / &4),lift se]) /\
                           (phi:real^2->real^3) (vector[&0; sg * (se / &4)]) IN
                           IMAGE (\t:real^1. vector[&0; sg * drop t; --(drop t pow 2)]:real^3)
                                 (interval[lift(se / &4),lift se])`
    (LABEL_TAC "D") THENL
     [GEN_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `abs(sg) = &1 /\ sg pow 2 = &1` STRIP_ASSUME_TAC THENL
       [FIRST_X_ASSUM DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF; IN_DELETE] THEN
        X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
        USE_THEN "TI" (MP_TAC o C MATCH_MP (ASSUME `(t:real^1) IN interval[lift(se / &4),lift se]`)) THEN
        STRIP_TAC THEN REPEAT CONJ_TAC THENL
         [USE_THEN "CH" (MP_TAC o SPEC `vector[&0; sg * drop t; --(drop t pow 2)]:real^3`) THEN
          REWRITE_TAC[VECTOR_3; REAL_POW_MUL] THEN ASM_REWRITE_TAC[REAL_MUL_LID] THEN
          ANTS_TAC THENL
           [ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs(--x) = x`] THEN ASM_REAL_ARITH_TAC;
            DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC];
          EXPAND_TAC "q" THEN REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
          ASM_REAL_ARITH_TAC;
          DISCH_TAC THEN
          USE_THEN "NE" (MP_TAC o C MATCH_MP (ASSUME
            `vector[&0; sg * drop t; --(drop(t:real^1) pow 2)]:real^3 IN path_image c`)) THEN
          REWRITE_TAC[VECTOR_3; REAL_ENTIRE] THEN
          SUBGOAL_THEN `~(sg = &0)` (fun th -> REWRITE_TAC[th]) THENL
           [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
        MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN REWRITE_TAC[CONNECTED_INTERVAL] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
        REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
        MATCH_MP_TAC SCH5C_SV3 THEN REWRITE_TAC[OPEN_UNIV; SCH5C_SR_CONST; drop] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC SCH5C_SR_MUL THEN SIMP_TAC[OPEN_UNIV; SCH5C_SR_CONST; SCH5C_SR_COMP];
          MATCH_MP_TAC SCH5C_SR_NEG THEN REWRITE_TAC[OPEN_UNIV] THEN
          MATCH_MP_TAC SCH5C_SR_POW THEN SIMP_TAC[OPEN_UNIV; SCH5C_SR_COMP]];
        REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `lift se` THEN
        REWRITE_TAC[LIFT_DROP; IN_INTERVAL_1; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        EXPAND_TAC "phi" THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `lift(se / &4)` THEN
        REWRITE_TAC[LIFT_DROP; IN_INTERVAL_1; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
                    VECTOR_2] THEN
        REWRITE_TAC[REAL_POW_MUL] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    USE_THEN "D" (MP_TAC o SPEC `&1`) THEN USE_THEN "D" (MP_TAC o SPEC `-- &1`) THEN
    REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_LID] THEN
    MAP_EVERY EXPAND_TAC ["dp"; "dm"] THEN SIMP_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `--(&1) = -- &1`] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `path_image c SUBSET (S:real^3->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET] THEN USE_THEN "AI" (fun th -> REWRITE_TAC[th]) THEN
      X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(x:real^3)$1 pow 2 <= e` ASSUME_TAC THENL
       [UNDISCH_TAC `se pow 2 = e` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        SUBGOAL_THEN `(x:real^3)$1 pow 2 = abs(x$1) pow 2` SUBST1_TAC THENL
         [REWRITE_TAC[REAL_POW2_ABS]; ALL_TAC] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_ABS_POS];
        ALL_TAC] THEN
      USE_THEN "CH" (MP_TAC o SPEC `x:real^3`) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `(x:real^3)$1` REAL_LE_POW_2) THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(vec 0:real^3) IN path_image c` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN USE_THEN "AI" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[VEC_COMPONENT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `connected(n1:real^3->bool) /\ connected(n2:real^3->bool)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [EXPAND_TAC "n1"; EXPAND_TAC "n2"] THEN
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
       ASM_SIMP_TAC[SUBSET_UNIV; SMOOTH_MAP_ON_CONTINUOUS_ON];
       MATCH_MP_TAC CONVEX_CONNECTED THEN MATCH_MP_TAC CONVEX_INTER THEN
       REWRITE_TAC[CONVEX_BALL; CONVEX_HALFSPACE_COMPONENT_LT;
                   REWRITE_RULE[real_gt] CONVEX_HALFSPACE_COMPONENT_GT]]);
    ALL_TAC] THEN
  SUBGOAL_THEN `(n1:real^3->bool) SUBSET (S DELETE q) DIFF path_image c /\
                (n2:real^3->bool) SUBSET (S DELETE q) DIFF path_image c`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [EXPAND_TAC "n1"; EXPAND_TAC "n2"] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_BALL_0; IN_ELIM_THM; IN_DIFF; IN_DELETE] THEN
    X_GEN_TAC `u:real^2` THEN STRIP_TAC THEN
    USE_THEN "PH" (MP_TAC o C MATCH_MP (ASSUME `norm(u:real^2) < se / &2`)) THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN DISCH_TAC THEN
    USE_THEN "NE" (MP_TAC o C MATCH_MP (ASSUME `(phi:real^2->real^3) u IN path_image c`)) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `connected((K':real^3->bool) UNION dp UNION dm)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM UNION_ASSOC] THEN MATCH_MP_TAC CONNECTED_UNION THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_UNION THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `vector[&0; se; --e]:real^3` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_UNION] THEN
      EXISTS_TAC `vector[&0; --se; --e]:real^3` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(K':real^3->bool) UNION dp UNION dm SUBSET (S DELETE q) DIFF path_image c`
  ASSUME_TAC THENL
   [REWRITE_TAC[UNION_SUBSET] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    REWRITE_TAC[SUBSET; IN_DIFF; IN_DELETE] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3)$3 = --e` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `(K':real^3->bool) SUBSET S` THEN UNDISCH_TAC `(x:real^3) IN K'` THEN SET_TAC[];
      DISCH_TAC THEN UNDISCH_TAC `(x:real^3)$3 = --e` THEN
      FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> concl th = `x:real^3 = q`)) THEN
      EXPAND_TAC "q" THEN REWRITE_TAC[VECTOR_3] THEN ASM_REAL_ARITH_TAC;
      DISCH_TAC THEN
      USE_THEN "NN" (MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN path_image c`)) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(((K':real^3->bool) UNION dp UNION dm) INTER n1 = {}) /\
                ~(((K':real^3->bool) UNION dp UNION dm) INTER n2 = {})` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_UNION] THEN CONJ_TAC THENL
     [EXISTS_TAC `(phi:real^2->real^3) (vector[&0; se / &4])` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "n1" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      REWRITE_TAC[IN_INTER; IN_BALL_0; IN_ELIM_THM; VECTOR_2; SCHY_NORM2];
      EXISTS_TAC `(phi:real^2->real^3) (vector[&0; --(se / &4)])` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "n2" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      REWRITE_TAC[IN_INTER; IN_BALL_0; IN_ELIM_THM; VECTOR_2; SCHY_NORM2]] THEN
    REWRITE_TAC[REAL_POW_NEG; ARITH] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_ADD_LID] THEN
    (SUBGOAL_THEN `sqrt((se / &4) pow 2) = se / &4` SUBST1_TAC THENL
      [MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);
    ALL_TAC] THEN
  SUBGOAL_THEN `(S:real^3->bool) INTER ball(vec 0,se / &4) DIFF path_image c SUBSET n1 UNION n2`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; IN_DIFF; IN_BALL_0; IN_UNION] THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^3)$1 pow 2 + x$2 pow 2 < e / &16 /\ abs(x$1) < se / &4 /\
                  abs(x$3) < se / &4` STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`x:real^3`; `1`] COMPONENT_LE_NORM) THEN
      MP_TAC(ISPECL [`x:real^3`; `3`] COMPONENT_LE_NORM) THEN
      REWRITE_TAC[DIMINDEX_3; ARITH] THEN REPEAT DISCH_TAC THEN
      REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
      SUBGOAL_THEN `norm(x:real^3) pow 2 < (se / &4) pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[NORM_POS_LE; ARITH]; ALL_TAC] THEN
      REWRITE_TAC[NORM_POW_2; DOT_3; REAL_POW_DIV] THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `(x:real^3)$3` REAL_LE_POW_2) THEN REWRITE_TAC[REAL_POW_2] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "CH" (MP_TAC o SPEC `x:real^3`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
    SUBGOAL_THEN `~((x:real^3)$2 = &0)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~((x:real^3) IN path_image c)` THEN
      ASM_REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN
      USE_THEN "AI" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `x = (phi:real^2->real^3) (vector[(x:real^3)$1; x$2]) /\
                  norm(vector[(x:real^3)$1; x$2]:real^2) < se / &2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [EXPAND_TAC "phi" THEN REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_2] THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[SCHY_NORM2] THEN MATCH_MP_TAC REAL_LT_LSQRT THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[REAL_POW_DIV] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    EXPAND_TAC "n1" THEN EXPAND_TAC "n2" THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `x:real^3`)) THEN
    REWRITE_TAC[IN_IMAGE] THEN
    SUBGOAL_THEN `!y:real^2. (phi:real^2->real^3) (vector[(x:real^3)$1; x$2]) = phi y <=>
                             y = vector[x$1; x$2]` (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN EXPAND_TAC "phi" THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; DIMINDEX_2; FORALL_2; VECTOR_3; VECTOR_2] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[UNWIND_THM2; IN_INTER; IN_BALL_0; IN_ELIM_THM; VECTOR_2] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SCHY_JORDAN_CORE THEN
  MAP_EVERY EXISTS_TAC
   [`S:real^3->bool`; `q:real^3`; `h:real^3->real^2`; `h':real^2->real^3`; `c:real^1->real^3`;
    `vec 0:real^3`; `n1:real^3->bool`; `n2:real^3->bool`;
    `(K':real^3->bool) UNION dp UNION dm`; `se / &4`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The pancake chart of pc_sch_vflow with its formula.  Copy of              *)
(* the proof of SCH5V_PANCAKE_CHART (pc_sch_vflow) with one more             *)
(* conclusion: Theta is the flow chart y |-> flow(lam y3)(c(y1,y2), a).  The  *)
(* formula gives the location control used for the far cuts (the chart      *)
(* image stays within B lam H of the planar disc of the cut circle).         *)
(* ------------------------------------------------------------------------- *)

let SCHY_PANCAKE_CHART_F = prove
 (`!(g:real^3->real^3) g' a C (c:real^2->real^2) c' K0 dax (v:real^3->real^3) B d e lam H.
     sch_neck g g' /\ sch_ball c c' /\
     C SUBSET IMAGE g (sphere(vec 0,&1)) /\
     (!z. z IN ball(vec 0,&2) ==> sch5v_at a (c z) IN K0) /\
     IMAGE g (sphere(vec 0,&1)) INTER K0 SUBSET C /\
     (!z. z IN ball(vec 0,&2) ==> (sch5v_at a (c z) IN C <=> z IN sphere(vec 0,&1))) /\
     (!z y. z IN cball(vec 0,&1 / &2) /\ y IN C ==> dax <= dist(sch5v_at a (c z),y)) /\
     smooth_map_on (:real^3) v /\ (!y. ode_vf_maxint v (:real^3) y = (:real^1)) /\
     (!y. norm(v y) <= B) /\ (!y. (v y)$3 = &1) /\ &0 < d /\
     (!x. ~(?y. y IN C /\ dist(y,x) < dax / &2) ==> v x = basis 3) /\
     (!x t. (!u. u IN interval[vec 0,t] UNION interval[t,vec 0]
                 ==> ?y. y IN C /\ dist(y,ode_vf_flow v (:real^3) u x) < &2 * d)
            ==> norm(g'(ode_vf_flow v (:real^3) t x)) pow 2 = norm(g' x) pow 2) /\
     (!x. (?y. y IN C /\ dist(y,x) < &2 * d) ==> x IN IMAGE g (annulus (&1 / &2) (&2))) /\
     (!p q. p IN IMAGE g (sphere(vec 0,&1)) /\ q IN K0 /\ dist(p,q) < e
            ==> ?y. y IN C /\ dist(y,p) < d) /\
     &0 < lam /\ B * lam * H < e /\ B * lam * H < d /\
     B * lam * H < dax / &2 /\ &0 < H
     ==> ?Theta Theta'.
           (!y. Theta y = ode_vf_flow v (:real^3) (lift(lam * y$3)) (sch5v_at a (c(sch5v_pr y)))) /\
           diffeomorphism_on (sch5v_slab H) (IMAGE Theta (sch5v_slab H)) Theta Theta' /\
           (!y. y IN sch5v_slab H ==> (Theta y)$3 = a + lam * y$3) /\
           (!y. y IN sch5v_slab H /\ y$3 = &0 ==> Theta y = sch5v_at a (c(sch5v_pr y))) /\
           (!y. y IN sch5v_slab H /\ y$1 pow 2 + y$2 pow 2 < &1 / &4
                ==> Theta y = sch5v_at (a + lam * y$3) (c(sch5v_pr y))) /\
           (!y. y IN sch5v_slab H
                ==> (Theta y IN IMAGE g (sphere(vec 0,&1)) <=>
                     y$1 pow 2 + y$2 pow 2 = &1)) /\
           ((!y. y IN sch5v_slab H
                 ==> (Theta y IN inside(IMAGE g (sphere(vec 0,&1))) <=>
                      y$1 pow 2 + y$2 pow 2 < &1)) \/
            (!y. y IN sch5v_slab H
                 ==> (Theta y IN outside(IMAGE g (sphere(vec 0,&1))) <=>
                      y$1 pow 2 + y$2 pow 2 < &1)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "K0")
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "CS")
   (CONJUNCTS_THEN2 (LABEL_TAC "AX") (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "BD")
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "VERT") (CONJUNCTS_THEN2 (LABEL_TAC "FI")
   (CONJUNCTS_THEN2 (LABEL_TAC "NO") (CONJUNCTS_THEN2 (LABEL_TAC "NEAR")
    STRIP_ASSUME_TAC)))))))))))))))) THEN
  SUBGOAL_THEN `&1 <= B` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm((v:real^3->real^3)(vec 0))` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`(v:real^3->real^3)(vec 0)`; `3`] COMPONENT_LE_NORM) THEN
    ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH5V_FLOW_FACTS o CONJ
    (ASSUME `smooth_map_on (:real^3) (v:real^3->real^3)`)) THEN
  MP_TAC(ISPEC `v:real^3->real^3` SCH5V_FLOW_HEIGHT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "HT") THEN
  MP_TAC(ISPECL [`v:real^3->real^3`; `B:real`] SCH5V_FLOW_DISPLACEMENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "DSP") THEN
  MP_TAC(ISPECL [`ode_vf_flow (v:real^3->real^3) (:real^3)`; `c:real^2->real^2`;
                 `c':real^2->real^2`; `ball(vec 0:real^2,&2)`; `a:real`; `lam:real`;
                 `H:real`] SCH5V_FLOWBOX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    UNDISCH_TAC `sch_ball (c:real^2->real^2) c'` THEN REWRITE_TAC[sch_ball];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SCH5V_SLAB_EQ] THEN
  ABBREV_TAC `Th = \y:real^3. ode_vf_flow (v:real^3->real^3) (:real^3) (lift(lam * y$3))
                                (sch5v_at a ((c:real^2->real^2)(sch5v_pr y)))` THEN
  ABBREV_TAC `E = {x | sch5v_pr(ode_vf_flow (v:real^3->real^3) (:real^3)
                                  (lift(--(x$3 - a))) x) IN IMAGE (c:real^2->real^2) (ball(vec 0,&2)) /\
                       abs((x$3 - a) / lam) < H}` THEN
  ABBREV_TAC `Th' = \x:real^3.
     vector[((c':real^2->real^2)(sch5v_pr(ode_vf_flow (v:real^3->real^3) (:real^3)
              (lift(--(x$3 - a))) x)))$1;
            (c'(sch5v_pr(ode_vf_flow v (:real^3) (lift(--(x$3 - a))) x)))$2;
            (x$3 - a) / lam]:real^3` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `IMAGE (Th:real^3->real^3) (sch5v_slab H) = E` ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on (sch5v_slab H) E (Th:real^3->real^3) Th'` THEN
    SIMP_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`Th:real^3->real^3`; `Th':real^3->real^3`] THEN
  SUBGOAL_THEN `!y. (Th:real^3->real^3) y =
                    ode_vf_flow (v:real^3->real^3) (:real^3) (lift(lam * y$3))
                      (sch5v_at a ((c:real^2->real^2)(sch5v_pr y)))` (LABEL_TAC "TH") THENL
   [EXPAND_TAC "Th" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN sch5v_slab H ==> sch5v_pr y IN ball(vec 0,&2) /\ abs(y$3) < H`
  (LABEL_TAC "NB") THENL
   [REWRITE_TAC[SCH5V_SLAB_EQ; IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN sch5v_slab H
                    ==> ((Th:real^3->real^3) y IN IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) <=>
                         y$1 pow 2 + y$2 pow 2 = &1)`
  (LABEL_TAC "SURF") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "NB" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(y:real^3) IN sch5v_slab H`))) THEN
    STRIP_TAC THEN USE_THEN "TH" (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `(y:real^3)$1 pow 2 + y$2 pow 2 = &1 <=>
                  sch5v_at a ((c:real^2->real^2)(sch5v_pr y)) IN C` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM SCH5V_PR_FACTS] THEN CONV_TAC SYM_CONV THEN
      USE_THEN "CS" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ABBREV_TAC `q = sch5v_at a ((c:real^2->real^2)(sch5v_pr y))` THEN
    SUBGOAL_THEN `(q:real^3) IN K0` ASSUME_TAC THENL
     [EXPAND_TAC "q" THEN USE_THEN "K0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `s = lift(lam * (y:real^3)$3)` THEN
    SUBGOAL_THEN `abs(drop s) <= lam * H` ASSUME_TAC THENL
     [EXPAND_TAC "s" THEN REWRITE_TAC[LIFT_DROP; REAL_ABS_MUL] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < l ==> abs l = l`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `ode_vf_flow (v:real^3->real^3) (:real^3) (vec 0) q = q` (LABEL_TAC "P0") THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `!u. u IN interval[vec 0,s] UNION interval[s,vec 0]
                      ==> dist(q,ode_vf_flow (v:real^3->real^3) (:real^3) u q) <= B * lam * H /\
                          dist(ode_vf_flow (v:real^3->real^3) (:real^3) s q,ode_vf_flow (v:real^3->real^3) (:real^3) u q) <= B * lam * H`
    (LABEL_TAC "SEG") THENL
     [X_GEN_TAC `u:real^1` THEN DISCH_THEN(MP_TAC o MATCH_MP SCH5V_SEGMENT_BOUNDS) THEN
      STRIP_TAC THEN REWRITE_TAC[dist] THEN CONJ_TAC THENL
       [USE_THEN "DSP" (MP_TAC o SPECL [`q:real^3`; `vec 0:real^1`; `u:real^1`]) THEN
        USE_THEN "P0" (fun th -> REWRITE_TAC[th]) THEN
        REWRITE_TAC[DROP_VEC; REAL_SUB_LZERO; REAL_ABS_NEG];
        USE_THEN "DSP" (MP_TAC o SPECL [`q:real^3`; `s:real^1`; `u:real^1`])] THEN
      MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B * abs(drop s)` THEN
      CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(vec 0:real^1) IN interval[vec 0,s] UNION interval[s,vec 0] /\ (s:real^1) IN interval[vec 0,s] UNION interval[s,vec 0]` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[IN_UNION; IN_INTERVAL_1; DROP_VEC] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`] SCH5V_SURFACE_COMPACT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EQ_TAC THEN DISCH_TAC THENL
     [SUBGOAL_THEN `?y0. y0 IN C /\ dist(y0,ode_vf_flow (v:real^3->real^3) (:real^3) s q) < d` STRIP_ASSUME_TAC THENL
       [USE_THEN "NEAR" MATCH_MP_TAC THEN EXISTS_TAC `q:real^3` THEN
        ASM_REWRITE_TAC[] THEN
        USE_THEN "SEG" (fun th -> MP_TAC(CONJUNCT1(MATCH_MP th
          (ASSUME `(s:real^1) IN interval[vec 0,s] UNION interval[s,vec 0]`)))) THEN
        MP_TAC(ISPECL [`q:real^3`; `ode_vf_flow (v:real^3->real^3) (:real^3) s q`] DIST_SYM) THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `!u. u IN interval[vec 0,s] UNION interval[s,vec 0] ==> ?y. y IN C /\ dist(y,ode_vf_flow (v:real^3->real^3) (:real^3) u q) < &2 * d` (LABEL_TAC "CL") THENL
       [X_GEN_TAC `u:real^1` THEN DISCH_TAC THEN EXISTS_TAC `y0:real^3` THEN
        ASM_REWRITE_TAC[] THEN
        USE_THEN "SEG" (fun th -> MP_TAC(CONJUNCT2(MATCH_MP th
          (ASSUME `(u:real^1) IN interval[vec 0,s] UNION interval[s,vec 0]`)))) THEN
        MP_TAC(ISPECL [`y0:real^3`; `ode_vf_flow (v:real^3->real^3) (:real^3) s q`; `ode_vf_flow (v:real^3->real^3) (:real^3) u q`] DIST_TRIANGLE) THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      USE_THEN "FI" (fun th -> MP_TAC(MP (SPECL [`q:real^3`; `s:real^1`] th)
        (ASSUME `!u. u IN interval[vec 0,s] UNION interval[s,vec 0] ==> ?y. y IN C /\ dist(y,ode_vf_flow (v:real^3->real^3) (:real^3) u q) < &2 * d`))) THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `(q:real^3) IN IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2))`
      ASSUME_TAC THENL
       [USE_THEN "NO" MATCH_MP_TAC THEN
        USE_THEN "CL" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(vec 0:real^1) IN interval[vec 0,s] UNION interval[s,vec 0]`))) THEN
        USE_THEN "P0" (fun th -> REWRITE_TAC[th]);
        ALL_TAC] THEN
      SUBGOAL_THEN `ode_vf_flow (v:real^3->real^3) (:real^3) s q IN IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2))` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `ode_vf_flow (v:real^3->real^3) (:real^3) s q`] SCH5V_IN_SURFACE) THEN
      MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `q:real^3`] SCH5V_IN_SURFACE) THEN
      REWRITE_TAC[ASSUME `sch_neck (g:real^3->real^3) g'`;
                  ASSUME `(q:real^3) IN IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2))`;
                  ASSUME `ode_vf_flow (v:real^3->real^3) (:real^3) s q IN IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2))`] THEN
      REPEAT DISCH_TAC THEN
      SUBGOAL_THEN `(q:real^3) IN IMAGE (g:real^3->real^3) (sphere(vec 0,&1))` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) INTER K0 SUBSET C` THEN
      UNDISCH_TAC `(q:real^3) IN K0` THEN SET_TAC[];
      SUBGOAL_THEN `!u. u IN interval[vec 0,s] UNION interval[s,vec 0] ==> ?y. y IN C /\ dist(y,ode_vf_flow (v:real^3->real^3) (:real^3) u q) < &2 * d` (LABEL_TAC "CL") THENL
       [X_GEN_TAC `u:real^1` THEN DISCH_TAC THEN EXISTS_TAC `q:real^3` THEN
        ASM_REWRITE_TAC[] THEN
        USE_THEN "SEG" (fun th -> MP_TAC(CONJUNCT1(MATCH_MP th
          (ASSUME `(u:real^1) IN interval[vec 0,s] UNION interval[s,vec 0]`)))) THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      USE_THEN "FI" (fun th -> MP_TAC(MP (SPECL [`q:real^3`; `s:real^1`] th)
        (ASSUME `!u. u IN interval[vec 0,s] UNION interval[s,vec 0] ==> ?y. y IN C /\ dist(y,ode_vf_flow (v:real^3->real^3) (:real^3) u q) < &2 * d`))) THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `(q:real^3) IN IMAGE (g:real^3->real^3) (sphere(vec 0,&1))` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(q:real^3) IN IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2)) /\
                    ode_vf_flow (v:real^3->real^3) (:real^3) s q IN IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2))`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        USE_THEN "NO" MATCH_MP_TAC THEN
        USE_THEN "CL" (fun th -> MATCH_ACCEPT_TAC(MATCH_MP th (ASSUME `(s:real^1) IN interval[vec 0,s] UNION interval[s,vec 0]`)));
        ALL_TAC] THEN
      MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `ode_vf_flow (v:real^3->real^3) (:real^3) s q`] SCH5V_IN_SURFACE) THEN
      MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `q:real^3`] SCH5V_IN_SURFACE) THEN
      REWRITE_TAC[ASSUME `sch_neck (g:real^3->real^3) g'`;
                  ASSUME `(q:real^3) IN IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2))`;
                  ASSUME `ode_vf_flow (v:real^3->real^3) (:real^3) s q IN IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2))`] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "TH" ACCEPT_TAC;
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN USE_THEN "TH" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "HT" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[SCH5V_PR_AT; LIFT_DROP];
    REPEAT STRIP_TAC THEN USE_THEN "TH" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO; LIFT_NUM];
    REPEAT STRIP_TAC THEN USE_THEN "TH" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "NB" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(y:real^3) IN sch5v_slab H`))) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `sch5v_pr y IN cball(vec 0:real^2,&1 / &2)` ASSUME_TAC THENL
     [REWRITE_TAC[SCH5V_PR_FACTS] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `q = sch5v_at a ((c:real^2->real^2)(sch5v_pr y))` THEN
    MP_TAC(ISPECL [`v:real^3->real^3`; `{x:real^3 | ~(?y. y IN C /\ dist(y,x) < dax / &2)}`;
                   `q:real^3`; `lift(lam * (y:real^3)$3)`; `basis 3:real^3`]
      SCH5V_FLOW_TRANSLATE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM; ASSUME `smooth_map_on (:real^3) (v:real^3->real^3)`;
                  ASSUME `!y. ode_vf_maxint (v:real^3->real^3) (:real^3) y = (:real^1)`] THEN
      CONJ_TAC THENL [USE_THEN "VERT" ACCEPT_TAC; ALL_TAC] THEN
      X_GEN_TAC `u:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN DISCH_TAC THEN
      DISCH_THEN(X_CHOOSE_THEN `y':real^3` STRIP_ASSUME_TAC) THEN
      USE_THEN "AX" (fun th -> MP_TAC(MATCH_MP th (CONJ
        (ASSUME `sch5v_pr y IN cball(vec 0:real^2,&1 / &2)`) (ASSUME `(y':real^3) IN C`)))) THEN
      REWRITE_TAC[ASSUME `sch5v_at a ((c:real^2->real^2)(sch5v_pr y)) = q`] THEN
      MP_TAC(ISPECL [`q:real^3`; `q + drop u % basis 3:real^3`; `y':real^3`] DIST_TRIANGLE) THEN
      SUBGOAL_THEN `dist(q:real^3,q + drop u % basis 3) = abs(drop u)` SUBST1_TAC THENL
       [REWRITE_TAC[NORM_ARITH `dist(x:real^N,x + y) = norm y`; NORM_MUL] THEN
        SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`y':real^3`; `q + drop u % basis 3:real^3`] DIST_SYM) THEN
      SUBGOAL_THEN `abs(drop u) <= lam * H` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs(lam * (y:real^3)$3)` THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[REAL_ABS_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < l ==> abs l = l`] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `lam * H <= B * lam * H` MP_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "q" THEN
    REWRITE_TAC[sch5v_at; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT; LIFT_DROP] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    USE_THEN "SURF" ACCEPT_TAC;
    MATCH_MP_TAC SCH5V_SIDES THEN EXISTS_TAC `Th':real^3->real^3` THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC SCH5V_NECK_SPHERE_HOMEOMORPHIC THEN EXISTS_TAC `g':real^3->real^3` THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      USE_THEN "SURF" ACCEPT_TAC]]);;

let SCHY_PANCAKE_F = prove
 (`!(g:real^3->real^3) g' a C (Fn:real^2->real^2) Fn'.
     sch_neck g g' /\ (!t. sch_crit g t ==> ~((g t)$3 = a)) /\
     C IN components(sch_level g a) /\ FINITE(components(sch_level g a)) /\
     sch_neck Fn Fn' /\
     C = IMAGE (\x. vector[(Fn x)$1; (Fn x)$2; a]:real^3) (sphere(vec 0,&1)) /\
     (!x:real^2. x IN inside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C)
                 ==> ~((vector[x$1; x$2; a]:real^3) IN IMAGE g (sphere(vec 0,&1))))
     ==> ?c c'.
           sch_ball c c' /\
           IMAGE c (sphere(vec 0,&1)) = IMAGE Fn (sphere(vec 0,&1)) /\
           IMAGE c (ball(vec 0,&1)) = inside(IMAGE Fn (sphere(vec 0,&1))) /\
           ?B. &0 < B /\
           !H. &0 < H
               ==> ?lam0. &0 < lam0 /\
                 !lam. &0 < lam /\ lam < lam0
                 ==> ?Theta Theta'.
                       diffeomorphism_on (sch5v_slab H) (IMAGE Theta (sch5v_slab H))
                                         Theta Theta' /\
                       (!y. y IN sch5v_slab H ==> (Theta y)$3 = a + lam * y$3) /\
                       (!y. y IN sch5v_slab H /\ y$3 = &0
                            ==> Theta y = sch5v_at a (c(sch5v_pr y))) /\
                       (!y. y IN sch5v_slab H /\ y$1 pow 2 + y$2 pow 2 < &1 / &4
                            ==> Theta y = sch5v_at (a + lam * y$3) (c(sch5v_pr y))) /\
                       (!y. y IN sch5v_slab H
                            ==> (Theta y IN IMAGE g (sphere(vec 0,&1)) <=>
                                 y$1 pow 2 + y$2 pow 2 = &1)) /\
                       ((!y. y IN sch5v_slab H
                             ==> (Theta y IN inside(IMAGE g (sphere(vec 0,&1))) <=>
                                  y$1 pow 2 + y$2 pow 2 < &1)) \/
                        (!y. y IN sch5v_slab H
                             ==> (Theta y IN outside(IMAGE g (sphere(vec 0,&1))) <=>
                                  y$1 pow 2 + y$2 pow 2 < &1))) /\
                       (!y. y IN sch5v_slab H
                            ==> dist(Theta y,sch5v_at a (c(sch5v_pr y))) <= B * lam * H)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SCH5V_PANCAKE_SETUP) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^2->real^2` (X_CHOOSE_THEN `c':real^2->real^2`
    (X_CHOOSE_THEN `K0:real^3->bool` (X_CHOOSE_THEN `dax:real` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `sch_neck (g:real^3->real^3) g'` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `C:real^3->bool`;
                 `K0:real^3->bool`; `dax / &2`] SCH5V_PANCAKE_FIELD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^3->real^3` (X_CHOOSE_THEN `B:real`
    (X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `&1 <= B` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm((v:real^3->real^3)(vec 0))` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`(v:real^3->real^3)(vec 0)`; `3`] COMPONENT_LE_NORM) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `m = min e (min d (dax / &2))` THEN
  SUBGOAL_THEN `&0 < m /\ m <= e /\ m <= d /\ m <= dax / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`c:real^2->real^2`; `c':real^2->real^2`] THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `B:real` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN X_GEN_TAC `H:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &2 * B * H` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `m / (&2 * B * H)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `lam:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `B * lam * H < m` ASSUME_TAC THENL
   [SUBGOAL_THEN `lam * (&2 * B * H) < m` MP_TAC THENL
     [UNDISCH_TAC `lam < m / (&2 * B * H)` THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < B * lam * H` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `C:real^3->bool`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `K0:real^3->bool`; `dax:real`;
                 `v:real^3->real^3`; `B:real`; `d:real`; `e:real`; `lam:real`; `H:real`]
    SCHY_PANCAKE_CHART_F) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `Theta:real^3->real^3` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `Theta':real^3->real^3` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "FORM")
    (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))) THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN USE_THEN "FORM" (fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`v:real^3->real^3`; `B:real`] SCH5V_FLOW_DISPLACEMENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`sch5v_at a ((c:real^2->real^2)(sch5v_pr y))`;
                             `lift(lam * (y:real^3)$3)`; `vec 0:real^1`]) THEN
  MP_TAC(ISPEC `v:real^3->real^3` SCH5V_FLOW_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th])] THEN
  REWRITE_TAC[GSYM dist; LIFT_DROP; DROP_VEC; REAL_SUB_RZERO] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  UNDISCH_TAC `(y:real^3) IN sch5v_slab H` THEN REWRITE_TAC[SCH5V_SLAB_EQ; IN_ELIM_THM] THEN
  STRIP_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < l ==> abs l = l`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Tools for the far cuts: avoiding finitely many values, the                *)
(* two sides of a slab configuration are separated, the chart part of S is  *)
(* connected, the branches of the level e lie on the branch components, and *)
(* the planar disc of a far innermost component misses the chart disc.      *)
(* ------------------------------------------------------------------------- *)

let SCHY_AVOID_FINITE = prove
 (`!s a. FINITE s /\ &0 < a ==> ?x. &0 < x /\ x < a /\ ~(x IN s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `INFINITE (IMAGE (\n. a / (&n + &2)) (:num))` MP_TAC THENL
   [MATCH_MP_TAC INFINITE_IMAGE THEN REWRITE_TAC[num_INFINITE; IN_UNIV] THEN
    REPEAT GEN_TAC THEN
    ASM_SIMP_TAC[REAL_FIELD `&0 < a /\ &0 < x /\ &0 < y ==> (a / x = a / y <=> x = y)`;
                 REAL_ARITH `&0 < &n + &2`] THEN
    REWRITE_TAC[REAL_EQ_ADD_RCANCEL; REAL_OF_NUM_EQ];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] INFINITE_DIFF_FINITE)) THEN
  DISCH_THEN(MP_TAC o SPEC `s:real->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP INFINITE_NONEMPTY) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_DIFF; IN_IMAGE; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `n:num` ASSUME_TAC) ASSUME_TAC)) THEN
  EXISTS_TAC `x:real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < &n + &2` ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_LDIV_EQ] THEN
  SUBGOAL_THEN `a * &1 < a * (&n + &2)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let SCHY_SEP_SIDE = prove
 (`!(e1:real^N->bool) e2 a x.
     e1 INTER closure e2 = {} /\ e2 INTER closure e1 = {} /\
     connected a /\ a SUBSET e1 UNION e2 /\ x IN a /\ x IN e1
     ==> a SUBSET e1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`e1:real^N->bool`; `e2:real^N->bool`] SEPARATION_CLOSURES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `v:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`a:real^N->bool`; `u:real^N->bool`; `v:real^N->bool`] SCHY_CONNECTED_SIDE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  ASM SET_TAC[]);;

let SCHY_DISJ_UNION = prove
 (`!e1 e2 x1 x2:real^N->bool.
       DISJOINT e1 e2 /\ e1 INTER x2 = {} /\ e2 INTER x1 = {}
       ==> e1 INTER (e2 UNION x2) = {} /\ e2 INTER (e1 UNION x1) = {}`,
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_UNION; NOT_IN_EMPTY] THEN MESON_TAC[]);;

(* The two pieces of a slab configuration: the sides E1, E2 of the tube.    *)

let SCHY_INTER_EMPTY_MONO = prove
 (`!a b c:real^N->bool. b SUBSET c /\ a INTER c = {} ==> a INTER b = {}`,
  SET_TAC[]);;

let SCHY_SLAB_PARTS = prove
 (`!(S:real^3->bool) S1 S2 (Theta:real^3->real^3).
     sch_slab_config S S1 S2 Theta /\ closed S1 /\ closed S2
     ==> ?N Theta' E1 E2.
           open N /\ sch_slab_nbhd SUBSET N /\
           diffeomorphism_on N (IMAGE Theta N) Theta Theta' /\
           (!y. y IN N ==> (Theta y IN S <=> y$1 pow 2 + y$2 pow 2 = &1)) /\
           S = E1 UNION IMAGE Theta sch_lat UNION E2 /\ DISJOINT E1 E2 /\
           S1 = E1 UNION IMAGE Theta sch_cap1 /\ S2 = E2 UNION IMAGE Theta sch_cap2 /\
           E1 INTER S2 = {} /\ E2 INTER S1 = {} /\
           E1 INTER closure E2 = {} /\ E2 INTER closure E1 = {}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch_slab_config] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `N:real^3->bool` (X_CHOOSE_THEN `Theta':real^3->real^3`
    (X_CHOOSE_THEN `E1:real^3->bool` (X_CHOOSE_THEN `E2:real^3->bool`
      (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))))))
    STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`N:real^3->bool`; `Theta':real^3->real^3`; `E1:real^3->bool`;
                        `E2:real^3->bool`] THEN
  SUBGOAL_THEN `sch_cap1 SUBSET (N:real^3->bool) /\ sch_cap2 SUBSET N` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `sch_slab_nbhd` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[sch_cap1; sch_cap2; sch_slab_nbhd; SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THENL
     [MP_TAC(SPEC `--((y:real^3)$3)` SCH6_PROFILE_LE1);
      MP_TAC(SPEC `(y:real^3)$3` SCH6_PROFILE_LE1)] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(E1:real^3->bool) INTER IMAGE Theta sch_cap2 = {} /\
                (E2:real^3->bool) INTER IMAGE Theta sch_cap1 = {}` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^3` THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(y:real^3) IN N` ASSUME_TAC THENL
       [UNDISCH_TAC `(y:real^3) IN sch_cap2` THEN UNDISCH_TAC `sch_cap2 SUBSET (N:real^3->bool)` THEN
        SET_TAC[];
        ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(y:real^3) IN N`) o check (fun th ->
        is_forall(concl th) &&
        can (find_term ((=) `E1:real^3->bool`)) (concl th) &&
        can (find_term ((=) `E2:real^3->bool`)) (concl th))) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      UNDISCH_TAC `(y:real^3) IN sch_cap2` THEN REWRITE_TAC[sch_cap2; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      X_GEN_TAC `x:real^3` THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(y:real^3) IN N` ASSUME_TAC THENL
       [UNDISCH_TAC `(y:real^3) IN sch_cap1` THEN UNDISCH_TAC `sch_cap1 SUBSET (N:real^3->bool)` THEN
        SET_TAC[];
        ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(y:real^3) IN N`) o check (fun th ->
        is_forall(concl th) &&
        can (find_term ((=) `E1:real^3->bool`)) (concl th) &&
        can (find_term ((=) `E2:real^3->bool`)) (concl th))) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      UNDISCH_TAC `(y:real^3) IN sch_cap1` THEN REWRITE_TAC[sch_cap1; IN_ELIM_THM] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(E1:real^3->bool) INTER S2 = {} /\ (E2:real^3->bool) INTER S1 = {}`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SCHY_DISJ_UNION THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closure(E2:real^3->bool) SUBSET S2 /\ closure(E1:real^3->bool) SUBSET S1`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET_UNION];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  MATCH_MP_TAC SCHY_INTER_EMPTY_MONO THENL
   [EXISTS_TAC `S2:real^3->bool`; EXISTS_TAC `S1:real^3->bool`] THEN
  ASM_REWRITE_TAC[]);;

(* The part of S in the chart cylinder of radius r1 <= r is the graph of the *)
(* saddle over the disc of radius r1.                                        *)

let SCHY_CHART_PART = prove
 (`!(s:real^3->bool) r r1.
     schy_chart s r /\ &0 < r1 /\ r1 <= r
     ==> s INTER {x:real^3 | x$1 pow 2 + x$2 pow 2 < r1 pow 2 /\ abs(x$3) < r1} =
         IMAGE (\u:real^2. vector[u$1; u$2; u$1 pow 2 - u$2 pow 2]:real^3) (ball(vec 0,r1)) /\
         connected(s INTER {x:real^3 | x$1 pow 2 + x$2 pow 2 < r1 pow 2 /\ abs(x$3) < r1})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[schy_chart] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "CH"))) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `r1 pow 2 < r1 /\ r1 pow 2 <= r pow 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `x = r * r /\ r * r < r * &1 ==> x < r`) THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u:real^2. norm u < r1 <=> u$1 pow 2 + u$2 pow 2 < r1 pow 2` ASSUME_TAC THENL
   [GEN_TAC THEN SUBGOAL_THEN `(u:real^2)$1 pow 2 + u$2 pow 2 = norm u pow 2` SUBST1_TAC THENL
     [REWRITE_TAC[NORM_POW_2; DOT_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    EQ_TAC THEN DISCH_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[NORM_POS_LE; ARITH];
      MATCH_MP_TAC(REAL_ARITH `&0 <= n /\ &0 < r /\ ~(r <= n) ==> n < r`) THEN
      ASM_REWRITE_TAC[NORM_POS_LE] THEN DISCH_TAC THEN
      SUBGOAL_THEN `r1 pow 2 <= norm(u:real^2) pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `s INTER {x:real^3 | x$1 pow 2 + x$2 pow 2 < r1 pow 2 /\ abs(x$3) < r1} =
                IMAGE (\u:real^2. vector[u$1; u$2; u$1 pow 2 - u$2 pow 2]:real^3)
                      (ball(vec 0,r1))` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_IMAGE; IN_BALL_0] THEN
    X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
     [STRIP_TAC THEN EXISTS_TAC `vector[(x:real^3)$1; x$2]:real^2` THEN
      USE_THEN "CH" (MP_TAC o SPEC `x:real^3`) THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
      ASM_REWRITE_TAC[VECTOR_2] THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_2] THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `u:real^2` (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
      ASM_REWRITE_TAC[VECTOR_3] THEN DISCH_TAC THEN
      SUBGOAL_THEN `abs((u:real^2)$1 pow 2 - u$2 pow 2) < r1` ASSUME_TAC THENL
       [MP_TAC(SPEC `(u:real^2)$1` REAL_LE_POW_2) THEN MP_TAC(SPEC `(u:real^2)$2` REAL_LE_POW_2) THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "CH" (MP_TAC o SPEC `vector[(u:real^2)$1; u$2; u$1 pow 2 - u$2 pow 2]:real^3`) THEN
      REWRITE_TAC[VECTOR_3] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
  REWRITE_TAC[CONNECTED_BALL] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
  REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
  MATCH_MP_TAC SCH5C_SV3 THEN SIMP_TAC[OPEN_UNIV; SCH5C_SR_COMP] THEN
  MATCH_MP_TAC SCH5C_SR_SUB THEN SIMP_TAC[OPEN_UNIV; SCH5C_SR_POW; SCH5C_SR_COMP]);;

(* In the chart, the level e consists of the two branches x1 = -+ sqrt(e +  *)
(* x2^2); each lies on the level component of its branch point.             *)

let SCHY_BRANCH_COMP = prove
 (`!(g:real^3->real^3) r e x.
     schy_chart (IMAGE g (sphere(vec 0,&1))) r /\ &0 < e /\ &16 * e < r pow 2 /\
     x IN IMAGE g (sphere(vec 0,&1)) /\ x$3 = e /\ x$1 pow 2 + x$2 pow 2 < r pow 2
     ==> (x$1 < &0 ==> x IN connected_component (sch_level g e) (schy_lpt e)) /\
         (&0 < x$1 ==> x IN connected_component (sch_level g e) (schy_rpt e))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [schy_chart]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CH"))) THEN
  SUBGOAL_THEN `e < r` ASSUME_TAC THENL
   [SUBGOAL_THEN `r pow 2 < r` MP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `x = r * r /\ r * r < r * &1 ==> x < r`) THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3)$1 pow 2 = e + x$2 pow 2` ASSUME_TAC THENL
   [USE_THEN "CH" (MP_TAC o SPEC `x:real^3`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!sg. sg = &1 \/ sg = -- &1
         ==> sg * x$1 < &0
             ==> (x:real^3) IN connected_component (sch_level g e)
                                 (vector[--(sg * sqrt e); &0; e])`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `sg pow 2 = &1` ASSUME_TAC THENL
     [FIRST_X_ASSUM DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `!a s (x:real^3). a SUBSET s /\ x IN a ==> x IN s`) THEN
    EXISTS_TAC `IMAGE (\t:real^1. vector[--(sg * sqrt(e + drop t pow 2)); drop t; e]:real^3)
                      (segment[vec 0,lift((x:real^3)$2)])` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 0:real^1` THEN
        REWRITE_TAC[ENDS_IN_SEGMENT; DROP_VEC] THEN
        REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_ADD_RID];
        MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN REWRITE_TAC[CONNECTED_SEGMENT] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
        REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
        MATCH_MP_TAC SCH5C_SV3 THEN REWRITE_TAC[OPEN_UNIV; SCH5C_SR_CONST; drop] THEN
        SIMP_TAC[OPEN_UNIV; SCH5C_SR_COMP] THEN
        MATCH_MP_TAC SCH5C_SR_NEG THEN REWRITE_TAC[OPEN_UNIV] THEN
        MATCH_MP_TAC SCH5C_SR_MUL THEN REWRITE_TAC[OPEN_UNIV; SCH5C_SR_CONST] THEN
        MATCH_MP_TAC SCH5C_SR_SQRT THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC SCH5C_SR_ADD THEN SIMP_TAC[OPEN_UNIV; SCH5C_SR_CONST; SCH5C_SR_POW;
                                                SCH5C_SR_COMP];
          X_GEN_TAC `t:real^1` THEN MP_TAC(SPEC `(t:real^1)$1` REAL_LE_POW_2) THEN
          ASM_REAL_ARITH_TAC];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; sch_level; IN_ELIM_THM; VECTOR_3] THEN
        X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
        SUBGOAL_THEN `drop t pow 2 <= (x:real^3)$2 pow 2` ASSUME_TAC THENL
         [UNDISCH_TAC `(t:real^1) IN segment[vec 0,lift((x:real^3)$2)]` THEN
          REWRITE_TAC[SEGMENT_1; DROP_VEC; LIFT_DROP] THEN COND_CASES_TAC THEN
          REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN STRIP_TAC THEN
          ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
          ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `sqrt(e + drop t pow 2) pow 2 = e + drop t pow 2` ASSUME_TAC THENL
         [MATCH_MP_TAC SQRT_POW_2 THEN MP_TAC(SPEC `drop t` REAL_LE_POW_2) THEN
          ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        USE_THEN "CH" (MP_TAC o SPEC
          `vector[--(sg * sqrt(e + drop t pow 2)); drop t; e]:real^3`) THEN
        REWRITE_TAC[VECTOR_3; REAL_POW_NEG; REAL_POW_MUL; ARITH] THEN ASM_REWRITE_TAC[REAL_MUL_LID] THEN
        ANTS_TAC THENL
         [ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> abs e = e`] THEN ASM_REAL_ARITH_TAC;
          DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC]];
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `lift((x:real^3)$2)` THEN
      REWRITE_TAC[ENDS_IN_SEGMENT; LIFT_DROP] THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `sqrt(e + (x:real^3)$2 pow 2) = abs(x$1)` SUBST1_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
          `(x:real^3)$1 pow 2 = e + x$2 pow 2`)) THEN
        REWRITE_TAC[POW_2_SQRT_ABS];
        ALL_TAC] THEN
      FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th))) THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `sg * (x:real^3)$1 < &0` THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THEN DISCH_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `&1`); FIRST_X_ASSUM(MP_TAC o SPEC `-- &1`)] THEN
  REWRITE_TAC[schy_lpt; schy_rpt; REAL_MUL_LID; REAL_MUL_LNEG; REAL_NEG_NEG] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

(* The planar disc of a far innermost component misses the chart disc.      *)

let SCHY_FAR_DISC = prove
 (`!(g:real^3->real^3) r e C.
     schy_chart (IMAGE g (sphere(vec 0,&1))) r /\ &0 < e /\ &16 * e < r pow 2 /\
     C IN components(sch_level g e) /\ ~(schy_lpt e IN C) /\ ~(schy_rpt e IN C) /\
     (!x:real^2. x IN inside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C)
                 ==> ~((vector[x$1; x$2; e]:real^3) IN IMAGE g (sphere(vec 0,&1))))
     ==> !z:real^2. z IN IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C UNION
                         inside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C)
                    ==> r <= norm z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [schy_chart]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CH"))) THEN
  SUBGOAL_THEN `&0 < sqrt e /\ sqrt e pow 2 = e /\ e < r pow 2 /\ e < r` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `r pow 2 < r` MP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `x = r * r /\ r * r < r * &1 ==> x < r`) THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `schy_lpt e IN sch_level (g:real^3->real^3) e /\
                schy_rpt e IN sch_level (g:real^3->real^3) e` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[sch_level; IN_ELIM_THM; schy_lpt; schy_rpt; VECTOR_3] THEN
    CONJ_TAC THEN USE_THEN "CH" (fun th -> W(fun (_,w) ->
      MP_TAC(SPEC (lhand w) th))) THEN
    REWRITE_TAC[VECTOR_3; REAL_POW_NEG; ARITH] THEN ASM_REWRITE_TAC[] THEN
    (ANTS_TAC THENL
      [ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> abs e = e`] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
       ASM_REAL_ARITH_TAC;
       DISCH_THEN SUBST1_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_SUB_RZERO]]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN C ==> r <= norm(vector[x$1; x$2]:real^2)` (LABEL_TAC "FAR") THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN sch_level g e` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`sch_level (g:real^3->real^3) e`; `C:real^3->bool`] IN_COMPONENTS_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(x:real^3) IN C` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^3) IN IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) /\ x$3 = e`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN sch_level g e` THEN REWRITE_TAC[sch_level; IN_ELIM_THM];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^3)$1 pow 2 + x$2 pow 2 < r pow 2` ASSUME_TAC THENL
     [SUBGOAL_THEN `(x:real^3)$1 pow 2 + x$2 pow 2 = norm(vector[x$1; x$2]:real^2) pow 2`
      SUBST1_TAC THENL
       [REWRITE_TAC[NORM_POW_2; DOT_2; VECTOR_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[NORM_POS_LE; ARITH];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `x:real^3`] SCHY_BRANCH_COMP) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((x:real^3)$1 = &0)` ASSUME_TAC THENL
     [DISCH_TAC THEN USE_THEN "CH" (MP_TAC o SPEC `x:real^3`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN MP_TAC(SPEC `(x:real^3)$2` REAL_LE_POW_2) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `C = connected_component (sch_level (g:real^3->real^3) e) x` ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_COMPONENTS] o
        check (fun th -> concl th = `C IN components(sch_level (g:real^3->real^3) e)`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `x0:real^3` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `(x:real^3) IN C` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC CONNECTED_COMPONENT_EQ THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "L") (LABEL_TAC "R")) THEN
    ASM_CASES_TAC `(x:real^3)$1 < &0` THENL
     [SUBGOAL_THEN `schy_lpt e IN connected_component (sch_level (g:real^3->real^3) e) x`
      MP_TAC THENL
       [REWRITE_TAC[IN] THEN MATCH_MP_TAC CONNECTED_COMPONENT_SYM THEN
        ONCE_REWRITE_TAC[GSYM IN] THEN USE_THEN "L" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC [`~(schy_lpt e IN C)`;
                             `C = connected_component (sch_level (g:real^3->real^3) e) x`] THEN
      DISCH_THEN SUBST1_TAC THEN MESON_TAC[];
      SUBGOAL_THEN `&0 < (x:real^3)$1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `schy_rpt e IN connected_component (sch_level (g:real^3->real^3) e) x`
      MP_TAC THENL
       [REWRITE_TAC[IN] THEN MATCH_MP_TAC CONNECTED_COMPONENT_SYM THEN
        ONCE_REWRITE_TAC[GSYM IN] THEN USE_THEN "R" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC [`~(schy_rpt e IN C)`;
                             `C = connected_component (sch_level (g:real^3->real^3) e) x`] THEN
      DISCH_THEN SUBST1_TAC THEN MESON_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^2` THEN REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
   [UNDISCH_TAC `(z:real^2) IN IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C` THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `P = IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C` THEN
  SUBGOAL_THEN `ball(vec 0:real^2,r) SUBSET connected_component ((:real^2) DIFF P) z` (LABEL_TAC "BS") THENL
   [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN
    REWRITE_TAC[CONNECTED_BALL; IN_BALL_0] THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "P" THEN REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIV; IN_BALL_0; IN_IMAGE] THEN
    X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
    SUBGOAL_THEN `r <= norm(vector[(x:real^3)$1; x$2]:real^2)` MP_TAC THENL
     [USE_THEN "FAR" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `vector[--(sqrt e); &0]:real^2 IN inside P` MP_TAC THENL
   [MATCH_MP_TAC INSIDE_SAME_COMPONENT THEN EXISTS_TAC `z:real^2` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[GSYM IN] THEN USE_THEN "BS" (MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_BALL_0; SCHY_NORM2] THEN
    REWRITE_TAC[REAL_POW_NEG; ARITH] THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_ADD_RID] THEN MATCH_MP_TAC REAL_LT_LSQRT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `vector[--(sqrt e); &0]:real^2` o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "inside")) (concl th) &&
    is_forall(concl th))) THEN
  ASM_REWRITE_TAC[VECTOR_2] THEN
  UNDISCH_TAC `schy_lpt e IN sch_level (g:real^3->real^3) e` THEN
  REWRITE_TAC[schy_lpt; sch_level; IN_ELIM_THM] THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The far cut.  Model pieces, the location of the pancake                   *)
(* chart away from the saddle box, the persistence of the saddle chart on   *)
(* one of the two surgered spheres, and the saddle bookkeeping.              *)
(* ------------------------------------------------------------------------- *)

let SCHY_MODEL_PIECES = prove
 (`(!y:real^3. y IN sch_lat
               ==> y IN sch5v_slab(&3 / &2) /\ y$1 pow 2 + y$2 pow 2 = &1 /\ abs(y$3) <= &1) /\
   (!y:real^3. y IN sch_cap1
               ==> y IN sch5v_slab(&3 / &2) /\ y$1 pow 2 + y$2 pow 2 <= &1 /\
                   y$3 <= --(&1 / &2)) /\
   (!y:real^3. y IN sch_cap2
               ==> y IN sch5v_slab(&3 / &2) /\ y$1 pow 2 + y$2 pow 2 <= &1 /\
                   &1 / &2 <= y$3)`,
  REWRITE_TAC[sch_lat; sch_cap1; sch_cap2; sch5v_slab; IN_ELIM_THM] THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MP_TAC(SPEC `--((y:real^3)$3)` SCH_CAP_PROFILE_BOUNDS) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN ASM_REAL_ARITH_TAC;
    MP_TAC(SPEC `(y:real^3)$3` SCH_CAP_PROFILE_BOUNDS) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN ASM_REAL_ARITH_TAC]);;

let SCHY_PR_LIP = prove
 (`!x y:real^3. norm(sch5v_pr x - sch5v_pr y) <= dist(x,y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[dist; NORM_LE; sch5v_pr; DOT_2; DOT_3; VECTOR_SUB_COMPONENT; VECTOR_2] THEN
  MP_TAC(SPEC `(x:real^3)$3 - (y:real^3)$3` REAL_LE_SQUARE) THEN REAL_ARITH_TAC);;

(* Points of the pancake chart over the closed unit disc stay outside the   *)
(* cylinder of radius r1 when the slice c(cball 1) is outside radius r and  *)
(* the chart is d-close to the slice, d < r - r1.                            *)

let SCHY_FAR_LOCATE = prove
 (`!(Theta:real^3->real^3) (c:real^2->real^2) H e d r r1.
     (!z. z IN IMAGE c (cball(vec 0,&1)) ==> r <= norm z) /\
     (!y. y IN sch5v_slab H ==> dist(Theta y,sch5v_at e (c(sch5v_pr y))) <= d) /\
     d < r - r1 /\ &0 <= r1
     ==> !y. y IN sch5v_slab H /\ y$1 pow 2 + y$2 pow 2 <= &1
             ==> r1 pow 2 < ((Theta y)$1) pow 2 + ((Theta y)$2) pow 2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "FD") (CONJUNCTS_THEN2 (LABEL_TAC "DB")
    STRIP_ASSUME_TAC)) THEN
  X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `r <= norm((c:real^2->real^2)(sch5v_pr y))` ASSUME_TAC THENL
   [USE_THEN "FD" MATCH_MP_TAC THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `sch5v_pr y` THEN
    REWRITE_TAC[SCH5V_PR_FACTS] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `dist((Theta:real^3->real^3) y,sch5v_at e ((c:real^2->real^2)(sch5v_pr y))) <= d`
  ASSUME_TAC THENL [USE_THEN "DB" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(sch5v_pr((Theta:real^3->real^3) y) - (c:real^2->real^2)(sch5v_pr y)) <= d`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `dist((Theta:real^3->real^3) y,sch5v_at e ((c:real^2->real^2)(sch5v_pr y)))` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`(Theta:real^3->real^3) y`; `sch5v_at e ((c:real^2->real^2)(sch5v_pr y))`]
      SCHY_PR_LIP) THEN
    REWRITE_TAC[SCH5V_PR_AT];
    ALL_TAC] THEN
  SUBGOAL_THEN `r1 < norm(sch5v_pr((Theta:real^3->real^3) y))` ASSUME_TAC THENL
   [MATCH_MP_TAC(NORM_ARITH `!a b:real^2 d r r1.
       norm(a - b) <= d /\ r <= norm b /\ d < r - r1 ==> r1 < norm a`) THEN
    MAP_EVERY EXISTS_TAC [`(c:real^2->real^2)(sch5v_pr y)`; `d:real`; `r:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((Theta:real^3->real^3) y)$1 pow 2 + ((Theta y)$2) pow 2 =
                norm(sch5v_pr((Theta:real^3->real^3) y)) pow 2` SUBST1_TAC THENL
   [REWRITE_TAC[NORM_POW_2; DOT_2; sch5v_pr; VECTOR_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[ARITH]);;

let SCHY_CHART_SHRINK = prove
 (`!(s:real^3->bool) s' r r1.
     schy_chart s r /\ &0 < r1 /\ r1 <= r /\
     s' INTER {x:real^3 | x$1 pow 2 + x$2 pow 2 < r1 pow 2 /\ abs(x$3) < r1} =
     s INTER {x:real^3 | x$1 pow 2 + x$2 pow 2 < r1 pow 2 /\ abs(x$3) < r1}
     ==> schy_chart s' r1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[schy_chart] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "EQ")))) THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^3) IN s' <=> x IN s` SUBST1_TAC THENL
   [USE_THEN "EQ" (MP_TAC o SPEC `x:real^3` o REWRITE_RULE[EXTENSION]) THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `r1 pow 2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* The connected chart piece lies on one side of the cut.                    *)

let SCHY_PIECE_SIDE = prove
 (`!(E1:real^3->bool) E2 L K1 K2 X.
     connected((E1 UNION L UNION E2) INTER X) /\ ~((E1 UNION L UNION E2) INTER X = {}) /\
     DISJOINT E1 E2 /\ E1 INTER closure E2 = {} /\ E2 INTER closure E1 = {} /\
     L INTER X = {} /\ K1 INTER X = {} /\ K2 INTER X = {}
     ==> ((E1 UNION K1) INTER X = (E1 UNION L UNION E2) INTER X /\ (E2 UNION K2) INTER X = {}) \/
         ((E2 UNION K2) INTER X = (E1 UNION L UNION E2) INTER X /\ (E1 UNION K1) INTER X = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `A = (E1 UNION L UNION E2) INTER (X:real^3->bool)` THEN
  SUBGOAL_THEN `(A:real^3->bool) SUBSET E1 UNION E2` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN UNDISCH_TAC `(L:real^3->bool) INTER X = {}` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?x:real^3. x IN A` (X_CHOOSE_TAC `x:real^3`) THENL
   [UNDISCH_TAC `~(A:real^3->bool = {})` THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `A SUBSET (E1:real^3->bool) \/ A SUBSET E2` MP_TAC THENL
   [SUBGOAL_THEN `(x:real^3) IN E1 \/ x IN E2` STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`(x:real^3) IN A`; `(A:real^3->bool) SUBSET E1 UNION E2`] THEN
      SET_TAC[];
      DISJ1_TAC THEN MATCH_MP_TAC SCHY_SEP_SIDE THEN
      MAP_EVERY EXISTS_TAC [`E2:real^3->bool`; `x:real^3`] THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN MATCH_MP_TAC SCHY_SEP_SIDE THEN
      MAP_EVERY EXISTS_TAC [`E1:real^3->bool`; `x:real^3`] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(A:real^3->bool) SUBSET E1 UNION E2` THEN SET_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THENL [DISJ1_TAC; DISJ2_TAC] THEN POP_ASSUM MP_TAC THEN
  MAP_EVERY UNDISCH_TAC [`DISJOINT (E1:real^3->bool) E2`; `(L:real^3->bool) INTER X = {}`;
                         `(K1:real^3->bool) INTER X = {}`; `(K2:real^3->bool) INTER X = {}`;
                         `(E1 UNION L UNION E2) INTER (X:real^3->bool) = A`] THEN
  SET_TAC[]);;

let SCHY_SADDLES_FINITE = prove
 (`!g:real^3->real^3. sch_morse g ==> FINITE(sch_saddles g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{t | sch_crit (g:real^3->real^3) t}` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[sch_morse]; REWRITE_TAC[sch_saddles; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]]);;

let SCHY_SADDLE_SPLIT = prove
 (`!(g:real^3->real^3) ga gb t0.
     sch_morse ga /\ sch_morse gb /\
     CARD(sch_saddles ga) + CARD(sch_saddles gb) = 1 /\
     IMAGE ga (sch_saddles ga) UNION IMAGE gb (sch_saddles gb) = IMAGE g (sch_saddles g) /\
     t0 IN sch_saddles g /\ g t0 = vec 0 /\
     ~(vec 0 IN IMAGE gb (sphere(vec 0,&1)))
     ==> (?t. t IN sch_saddles ga /\ ga t = vec 0) /\ CARD(sch_saddles ga) = 1 /\
         sch_saddles gb = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(sch_saddles (ga:real^3->real^3)) /\ FINITE(sch_saddles (gb:real^3->real^3))`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[SCHY_SADDLES_FINITE]; ALL_TAC] THEN
  SUBGOAL_THEN `?t. t IN sch_saddles (ga:real^3->real^3) /\ ga t = vec 0`
  (X_CHOOSE_THEN `t1:real^3` STRIP_ASSUME_TAC) THENL
   [SUBGOAL_THEN `vec 0:real^3 IN IMAGE (ga:real^3->real^3) (sch_saddles ga) UNION
                                  IMAGE (gb:real^3->real^3) (sch_saddles gb)` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `t0:real^3` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `sch_saddles (gb:real^3->real^3) SUBSET sphere(vec 0,&1)` MP_TAC THENL
     [REWRITE_TAC[sch_saddles; sch_crit; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `~(vec 0:real^3 IN IMAGE (gb:real^3->real^3) (sphere(vec 0,&1)))` THEN
    REWRITE_TAC[IN_UNION; IN_IMAGE; SUBSET] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(CARD(sch_saddles (ga:real^3->real^3)) = 0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CARD_EQ_0] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `t1:real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD(sch_saddles (gb:real^3->real^3)) = 0` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`CARD(sch_saddles (ga:real^3->real^3)) + CARD(sch_saddles (gb:real^3->real^3)) = 1`;
      `~(CARD(sch_saddles (ga:real^3->real^3)) = 0)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [EXISTS_TAC `t1:real^3` THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `CARD(sch_saddles (ga:real^3->real^3)) + CARD(sch_saddles (gb:real^3->real^3)) = 1` THEN
    ASM_REWRITE_TAC[ADD_CLAUSES];
    UNDISCH_TAC `CARD(sch_saddles (gb:real^3->real^3)) = 0` THEN ASM_SIMP_TAC[CARD_EQ_0]]);;

let SCHY_NECK_COMPACT = prove
 (`!(g:real^3->real^3) g'. sch_neck g g' ==> compact(IMAGE g (sphere(vec 0,&1)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch_neck; diffeomorphism_on] THEN STRIP_TAC THEN
  MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN REWRITE_TAC[COMPACT_SPHERE] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN
  REWRITE_TAC[SCH_ANNULUS_SUBSETS] THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]);;

(* ------------------------------------------------------------------------- *)
(* The far cut step.  schy_box is the saddle box, schy_norm the              *)
(* normalized one-saddle situation at the level e (saddle at the origin,     *)
(* exact chart, the upper branch points on different level components).     *)
(* ------------------------------------------------------------------------- *)

let schy_box = new_definition
 `schy_box (r:real) = {x:real^3 | x$1 pow 2 + x$2 pow 2 < r pow 2 /\ abs(x$3) < r}`;;

let schy_norm = new_definition
 `schy_norm (g:real^3->real^3) g' r e <=>
    sch_neck g g' /\ sch_morse g /\ CARD(sch_saddles g) = 1 /\
    (?t0. t0 IN sch_saddles g /\ g t0 = vec 0) /\
    schy_chart (IMAGE g (sphere(vec 0,&1))) r /\ &0 < e /\ &16 * e < r pow 2 /\
    (!t. sch_crit g t ==> ~((g t)$3 = e)) /\
    ~(schy_rpt e IN connected_component (sch_level g e) (schy_lpt e))`;;

let SCHY_IMAGE_INTER_EMPTY = prove
 (`!(f:real^3->real^3) s t. IMAGE f s INTER t = {} <=> !x. x IN s ==> ~(f x IN t)`,
  SET_TAC[]);;

let SCHY_MODEL_DISC = prove
 (`!y:real^3. y IN sch_lat \/ y IN sch_cap1 \/ y IN sch_cap2
              ==> y IN sch5v_slab(&3 / &2) /\ y$1 pow 2 + y$2 pow 2 <= &1`,
  GEN_TAC THEN STRIP_TAC THENL
   [MP_TAC(SPEC `y:real^3` (CONJUNCT1 SCHY_MODEL_PIECES));
    MP_TAC(SPEC `y:real^3` (CONJUNCT1(CONJUNCT2 SCHY_MODEL_PIECES)));
    MP_TAC(SPEC `y:real^3` (CONJUNCT2(CONJUNCT2 SCHY_MODEL_PIECES)))] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let SCHY_PROJ_LEVEL = prove
 (`!(Fn:real^2->real^2) a s.
     IMAGE (\y:real^3. vector[y$1; y$2]:real^2)
           (IMAGE (\x. vector[(Fn x)$1; (Fn x)$2; a]:real^3) s) = IMAGE Fn s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM IMAGE_o; o_DEF; VECTOR_3] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2]);;

let SCHY_LEVEL_AT = prove
 (`!(Fn:real^2->real^2) (c:real^2->real^2) a s t.
     IMAGE c t = IMAGE Fn s
     ==> IMAGE (\x. vector[(Fn x)$1; (Fn x)$2; a]:real^3) s =
         IMAGE (\z. sch5v_at a (c z)) t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (\z. sch5v_at a ((c:real^2->real^2) z)) t = IMAGE (sch5v_at a) (IMAGE c t)`
  SUBST1_TAC THENL [REWRITE_TAC[GSYM IMAGE_o; o_DEF]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM IMAGE_o; o_DEF; sch5v_at]);;

(* The far cut with the location of the model pieces.                       *)

let SCHY_FAR_CUT = prove
 (`!(g:real^3->real^3) g' r r1 e C.
     SCHY_CUT_STATEMENT /\ SCH_LEVEL_NECK_STATEMENT /\
     sch_neck g g' /\ sch_morse g /\ (!t. sch_crit g t ==> ~((g t)$3 = e)) /\
     schy_chart (IMAGE g (sphere(vec 0,&1))) r /\ &0 < e /\ &16 * e < r pow 2 /\
     &0 < r1 /\ r1 < r /\
     C IN components(sch_level g e) /\ ~(schy_lpt e IN C) /\ ~(schy_rpt e IN C) /\
     (!x:real^2. x IN inside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C)
                 ==> ~((vector[x$1; x$2; e]:real^3) IN IMAGE g (sphere(vec 0,&1))))
     ==> ?g1 g1' g2 g2' (Theta:real^3->real^3) e0 E1 E2.
           sch_neck g1 g1' /\ sch_morse g1 /\ sch_neck g2 g2' /\ sch_morse g2 /\
           (!t. sch_crit g1 t ==> ~((g1 t)$3 = e)) /\
           (!t. sch_crit g2 t ==> ~((g2 t)$3 = e)) /\
           sch_slab_config (IMAGE g (sphere(vec 0,&1))) (IMAGE g1 (sphere(vec 0,&1)))
                           (IMAGE g2 (sphere(vec 0,&1))) Theta /\
           &0 < e0 /\ e0 <= &1 / &16 /\
           (!x. x IN sch_capcone
                ==> g1 x = Theta(sch_cap_collar e0 x) /\
                    g2(sch_flip3 x) = Theta(sch_flip3(sch_cap_collar e0 x))) /\
           CARD(sch_saddles g1) + CARD(sch_saddles g2) = CARD(sch_saddles g) /\
           IMAGE g1 (sch_saddles g1) UNION IMAGE g2 (sch_saddles g2) = IMAGE g (sch_saddles g) /\
           CARD(components(sch_level g1 e)) + CARD(components(sch_level g2 e)) + 1 =
           CARD(components(sch_level g e)) /\
           IMAGE g (sphere(vec 0,&1)) = E1 UNION IMAGE Theta sch_lat UNION E2 /\
           DISJOINT E1 E2 /\
           IMAGE g1 (sphere(vec 0,&1)) = E1 UNION IMAGE Theta sch_cap1 /\
           IMAGE g2 (sphere(vec 0,&1)) = E2 UNION IMAGE Theta sch_cap2 /\
           E1 INTER closure E2 = {} /\ E2 INTER closure E1 = {} /\
           IMAGE Theta sch_lat INTER schy_box r1 = {} /\
           IMAGE Theta sch_cap1 INTER schy_box r1 = {} /\
           IMAGE Theta sch_cap2 INTER schy_box r1 = {} /\
           (!x. x IN IMAGE Theta sch_cap1 ==> ~(x$3 = e)) /\
           (!x. x IN IMAGE Theta sch_cap2 ==> ~(x$3 = e))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "CUT") (CONJUNCTS_THEN2 (LABEL_TAC "LN")
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `FINITE(components(sch_level (g:real^3->real^3) e))` ASSUME_TAC THENL
   [MP_TAC SCH_LEVEL_FINITE THEN REWRITE_TAC[SCH_LEVEL_FINITE_STATEMENT] THEN
    DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `g':real^3->real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {t | sch_crit (g:real^3->real^3) t}` ASSUME_TAC THENL
   [UNDISCH_TAC `sch_morse (g:real^3->real^3)` THEN SIMP_TAC[sch_morse]; ALL_TAC] THEN
  USE_THEN "LN" (MP_TAC o SPECL [`g:real^3->real^3`; `g':real^3->real^3`; `e:real`;
    `C:real^3->bool`] o REWRITE_RULE[SCH_LEVEL_NECK_STATEMENT]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Fn:real^2->real^2` (X_CHOOSE_THEN `Fn':real^2->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CF")))) THEN
  SUBGOAL_THEN `IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C =
                IMAGE (Fn:real^2->real^2) (sphere(vec 0,&1))` (LABEL_TAC "PC") THENL
   [USE_THEN "CF" SUBST1_TAC THEN REWRITE_TAC[SCHY_PROJ_LEVEL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `e:real`; `C:real^3->bool`;
                 `Fn:real^2->real^2`; `Fn':real^2->real^2`] SCHY_PANCAKE_F) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^2->real^2` (X_CHOOSE_THEN `c':real^2->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `B:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "PK")))))))) THEN
  USE_THEN "PK" (MP_TAC o SPEC `&3 / &2`) THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "PL"))) THEN
  MP_TAC(ISPECL [`IMAGE (\t. &2 * (((g:real^3->real^3) t)$3 - e)) {t | sch_crit g t} UNION
                  IMAGE (\t. &2 * (e - ((g:real^3->real^3) t)$3)) {t | sch_crit g t}`;
                 `min lam0 ((r - r1) / (&2 * B))`] SCHY_AVOID_FINITE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[FINITE_UNION] THEN CONJ_TAC THEN MATCH_MP_TAC FINITE_IMAGE THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `lam < lam0 /\ lam * (&2 * B) < r - r1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `lam < min lam0 ((r - r1) / (&2 * B))` THEN REWRITE_TAC[REAL_LT_MIN] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `lam < (r - r1) / (&2 * B)` THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_ARITH `&0 < B ==> &0 < &2 * B`];
    ALL_TAC] THEN
  SUBGOAL_THEN `B * lam * &3 / &2 < r - r1` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < B * lam` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `lam * (&2 * B) < r - r1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "PL" (MP_TAC o SPEC `lam:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Theta:real^3->real^3` (X_CHOOSE_THEN `Theta':real^3->real^3`
    (fun th -> MAP_EVERY (fun (s,t) -> LABEL_TAC s t)
      (zip ["TD";"TH";"T0";"TP";"TS";"TSI";"TB"] (CONJUNCTS th))))) THEN
  SUBGOAL_THEN `!z:real^2. z IN IMAGE (c:real^2->real^2) (cball(vec 0,&1)) ==> r <= norm z`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`] SCHY_FAR_DISC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "PC" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[GSYM BALL_UNION_SPHERE; IMAGE_UNION] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_UNION] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. sch_crit (g:real^3->real^3) t
                    ==> ~((g t)$3 = e + lam / &2) /\ ~((g t)$3 = e - lam / &2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real^3` THEN DISCH_TAC THEN
    UNDISCH_TAC `~(lam IN IMAGE (\t. &2 * (((g:real^3->real^3) t)$3 - e)) {t | sch_crit g t} UNION
                         IMAGE (\t. &2 * (e - ((g:real^3->real^3) t)$3)) {t | sch_crit g t})` THEN
    REWRITE_TAC[IN_UNION; IN_IMAGE; IN_ELIM_THM; DE_MORGAN_THM; NOT_EXISTS_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN (MP_TAC o SPEC `t:real^3`)) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `C = IMAGE (\z. sch5v_at e ((c:real^2->real^2) z)) (sphere(vec 0,&1))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`Fn:real^2->real^2`; `c:real^2->real^2`; `e:real`; `sphere(vec 0:real^2,&1)`;
                   `sphere(vec 0:real^2,&1)`] SCHY_LEVEL_AT) THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "CF" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (c:real^2->real^2) (ball(vec 0,&1)) =
                inside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C)` ASSUME_TAC THENL
   [USE_THEN "PC" SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN sch5v_slab(&3 / &2) /\ y$1 pow 2 + y$2 pow 2 <= &1
                ==> r1 pow 2 < ((Theta:real^3->real^3) y)$1 pow 2 + ((Theta y)$2) pow 2`
  (LABEL_TAC "LOC") THENL
   [MATCH_MP_TAC SCHY_FAR_LOCATE THEN
    MAP_EVERY EXISTS_TAC [`c:real^2->real^2`; `e:real`; `B * lam * &3 / &2`; `r:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN IMAGE (Theta:real^3->real^3) sch_cap1 ==> ~(x$3 = e)` ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MP_TAC(SPEC `y:real^3` (CONJUNCT1(CONJUNCT2 SCHY_MODEL_PIECES))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    USE_THEN "TH" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `&0 < lam * --((y:real^3)$3)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN IMAGE (Theta:real^3->real^3) sch_cap2 ==> ~(x$3 = e)` ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MP_TAC(SPEC `y:real^3` (CONJUNCT2(CONJUNCT2 SCHY_MODEL_PIECES))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    USE_THEN "TH" (MP_TAC o SPEC `y:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `&0 < lam * (y:real^3)$3` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (Theta:real^3->real^3) sch_lat INTER schy_box r1 = {} /\
                IMAGE (Theta:real^3->real^3) sch_cap1 INTER schy_box r1 = {} /\
                IMAGE (Theta:real^3->real^3) sch_cap2 INTER schy_box r1 = {}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SCHY_IMAGE_INTER_EMPTY; schy_box; IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "LOC" (MP_TAC o SPEC `y:real^3`) THEN
    (ANTS_TAC THENL [MATCH_MP_TAC SCHY_MODEL_DISC THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC]);
    ALL_TAC] THEN
  USE_THEN "CUT" (MP_TAC o SPECL [`g:real^3->real^3`; `g':real^3->real^3`; `e:real`;
     `C:real^3->bool`; `c:real^2->real^2`; `c':real^2->real^2`; `Theta:real^3->real^3`;
     `Theta':real^3->real^3`; `&3 / &2`; `lam:real`] o REWRITE_RULE[SCHY_CUT_STATEMENT]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC; MATCH_ACCEPT_TAC REAL_LE_REFL];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g1:real^3->real^3` (X_CHOOSE_THEN `g1':real^3->real^3`
    (X_CHOOSE_THEN `g2:real^3->real^3` (X_CHOOSE_THEN `g2':real^3->real^3`
      (X_CHOOSE_THEN `e0:real` (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))))))) THEN
  MP_TAC(ISPECL [`IMAGE (g:real^3->real^3) (sphere(vec 0,&1))`;
                 `IMAGE (g1:real^3->real^3) (sphere(vec 0,&1))`;
                 `IMAGE (g2:real^3->real^3) (sphere(vec 0,&1))`; `Theta:real^3->real^3`]
    SCHY_SLAB_PARTS) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC SCHY_NECK_COMPACT THEN
      EXISTS_TAC `g1':real^3->real^3` THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC SCHY_NECK_COMPACT THEN
      EXISTS_TAC `g2':real^3->real^3` THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:real^3->bool` (X_CHOOSE_THEN `Theta2:real^3->real^3`
    (X_CHOOSE_THEN `E1:real^3->bool` (X_CHOOSE_THEN `E2:real^3->bool`
      (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)))))) THEN
  MAP_EVERY EXISTS_TAC [`g1:real^3->real^3`; `g1':real^3->real^3`; `g2:real^3->real^3`;
                        `g2':real^3->real^3`; `Theta:real^3->real^3`; `e0:real`;
                        `E1:real^3->bool`; `E2:real^3->bool`] THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* ------------------------------------------------------------------------- *)
(* The far cut step.  The piece that keeps the saddle box                    *)
(* inherits the normalized situation with fewer level components; the other *)
(* piece is saddle-free and bounds a ball (pc_sch_base0), and the gluing of *)
(* pc_sch_glue gives the ball.                                              *)
(* ------------------------------------------------------------------------- *)

let SCHY_FAR_FINISH = prove
 (`!(g:real^3->real^3) g' r ga ga' gb gb' r1 e Ea Ka.
     SCH_BASE0_STATEMENT /\ schy_norm g g' r e /\
     sch_neck ga ga' /\ sch_morse ga /\ sch_neck gb gb' /\ sch_morse gb /\
     (!t. sch_crit ga t ==> ~((ga t)$3 = e)) /\
     CARD(sch_saddles ga) + CARD(sch_saddles gb) = 1 /\
     IMAGE ga (sch_saddles ga) UNION IMAGE gb (sch_saddles gb) = IMAGE g (sch_saddles g) /\
     &0 < r1 /\ r1 <= r /\ &16 * e < r1 pow 2 /\
     IMAGE ga (sphere(vec 0,&1)) INTER schy_box r1 =
     IMAGE g (sphere(vec 0,&1)) INTER schy_box r1 /\
     IMAGE gb (sphere(vec 0,&1)) INTER schy_box r1 = {} /\
     IMAGE ga (sphere(vec 0,&1)) = Ea UNION Ka /\ Ea SUBSET IMAGE g (sphere(vec 0,&1)) /\
     (!x. x IN Ka ==> ~(x$3 = e)) /\
     CARD(components(sch_level ga e)) < CARD(components(sch_level g e)) /\
     (sch_bounds_ball (IMAGE ga (sphere(vec 0,&1))) /\
      sch_bounds_ball (IMAGE gb (sphere(vec 0,&1)))
      ==> sch_bounds_ball (IMAGE g (sphere(vec 0,&1))))
     ==> schy_norm ga ga' r1 e /\
         CARD(components(sch_level ga e)) < CARD(components(sch_level g e)) /\
         (sch_bounds_ball (IMAGE ga (sphere(vec 0,&1)))
          ==> sch_bounds_ball (IMAGE g (sphere(vec 0,&1))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[schy_norm] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(vec 0:real^3 IN IMAGE (gb:real^3->real^3) (sphere(vec 0,&1)))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `vec 0:real^3 IN IMAGE (gb:real^3->real^3) (sphere(vec 0,&1)) INTER schy_box r1`
    MP_TAC THENL
     [REWRITE_TAC[IN_INTER; schy_box; IN_ELIM_THM; VEC_COMPONENT] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_SIMP_TAC[REAL_POW_LT];
      ASM_REWRITE_TAC[NOT_IN_EMPTY]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `ga:real^3->real^3`; `gb:real^3->real^3`; `t0:real^3`]
    SCHY_SADDLE_SPLIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `schy_chart (IMAGE (ga:real^3->real^3) (sphere(vec 0,&1))) r1` ASSUME_TAC THENL
   [MATCH_MP_TAC SCHY_CHART_SHRINK THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (g:real^3->real^3) (sphere(vec 0,&1))`; `r:real`] THEN
    REWRITE_TAC[GSYM schy_box] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sch_level (ga:real^3->real^3) e SUBSET sch_level g e` ASSUME_TAC THENL
   [REWRITE_TAC[sch_level; SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN
    ASM_REWRITE_TAC[IN_UNION] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [UNDISCH_TAC `(Ea:real^3->bool) SUBSET IMAGE (g:real^3->real^3) (sphere(vec 0,&1))` THEN
      UNDISCH_TAC `(x:real^3) IN Ea` THEN SET_TAC[];
      MESON_TAC[ASSUME `!x:real^3. x IN Ka ==> ~(x$3 = e)`; ASSUME `(x:real^3) IN Ka`;
                ASSUME `(x:real^3)$3 = e`]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(schy_rpt e IN connected_component (sch_level (ga:real^3->real^3) e)
                                                    (schy_lpt e))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~(schy_rpt e IN connected_component (sch_level (g:real^3->real^3) e)
                                                     (schy_lpt e))` THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `!s t x:real^3. s SUBSET t /\ x IN s ==> x IN t`) THEN
    EXISTS_TAC `connected_component (sch_level (ga:real^3->real^3) e) (schy_lpt e)` THEN
    ASM_SIMP_TAC[CONNECTED_COMPONENT_MONO];
    ALL_TAC] THEN
  SUBGOAL_THEN `sch_bounds_ball (IMAGE (gb:real^3->real^3) (sphere(vec 0,&1)))` ASSUME_TAC THENL
   [UNDISCH_TAC `SCH_BASE0_STATEMENT` THEN REWRITE_TAC[SCH_BASE0_STATEMENT] THEN
    DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `gb':real^3->real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `sch_bounds_ball (IMAGE (ga:real^3->real^3) (sphere(vec 0,&1))) /\
               sch_bounds_ball (IMAGE (gb:real^3->real^3) (sphere(vec 0,&1)))
               ==> sch_bounds_ball (IMAGE (g:real^3->real^3) (sphere(vec 0,&1)))` THEN
  ASM_REWRITE_TAC[]);;

let SCHY_FAR_STEP = prove
 (`!(g:real^3->real^3) g' r e C.
     SCHY_DEPS /\ schy_norm g g' r e /\
     C IN components(sch_level g e) /\ ~(schy_lpt e IN C) /\ ~(schy_rpt e IN C) /\
     (!x:real^2. x IN inside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C)
                 ==> ~((vector[x$1; x$2; e]:real^3) IN IMAGE g (sphere(vec 0,&1))))
     ==> ?g1 g1' r1. schy_norm g1 g1' r1 e /\
                     CARD(components(sch_level g1 e)) < CARD(components(sch_level g e)) /\
                     (sch_bounds_ball (IMAGE g1 (sphere(vec 0,&1)))
                      ==> sch_bounds_ball (IMAGE g (sphere(vec 0,&1))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SCHY_DEPS] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [schy_norm]) THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
   [UNDISCH_TAC `schy_chart (IMAGE (g:real^3->real^3) (sphere(vec 0,&1))) r` THEN
    SIMP_TAC[schy_chart];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt(&16 * e) /\ sqrt(&16 * e) < r /\ sqrt(&16 * e) pow 2 = &16 * e`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= &16 * e` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2] THEN
    SUBGOAL_THEN `r = sqrt(r pow 2)` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `r1 = (sqrt(&16 * e) + r) / &2` THEN
  SUBGOAL_THEN `&0 < r1 /\ r1 < r /\ &16 * e < r1 pow 2` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "r1" THEN ASM_REAL_ARITH_TAC; EXPAND_TAC "r1" THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `sqrt(&16 * e) pow 2 = &16 * e` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[ARITH] THEN
    EXPAND_TAC "r1" THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `connected(IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) INTER schy_box r1) /\
                ~(IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) INTER schy_box r1 = {})`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`IMAGE (g:real^3->real^3) (sphere(vec 0,&1))`; `r:real`; `r1:real`]
      SCHY_CHART_PART) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM schy_box] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY; BALL_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `r:real`; `r1:real`; `e:real`;
                 `C:real^3->bool`] SCHY_FAR_CUT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g1:real^3->real^3` (X_CHOOSE_THEN `g1':real^3->real^3`
    (X_CHOOSE_THEN `g2:real^3->real^3` (X_CHOOSE_THEN `g2':real^3->real^3`
      (X_CHOOSE_THEN `Theta:real^3->real^3` (X_CHOOSE_THEN `e0:real`
        (X_CHOOSE_THEN `E1:real^3->bool` (X_CHOOSE_THEN `E2:real^3->bool`
          (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)))))))))) THEN
  SUBGOAL_THEN `sch_bounds_ball (IMAGE (g1:real^3->real^3) (sphere(vec 0,&1))) /\
                sch_bounds_ball (IMAGE (g2:real^3->real^3) (sphere(vec 0,&1)))
                ==> sch_bounds_ball (IMAGE (g:real^3->real^3) (sphere(vec 0,&1)))`
  ASSUME_TAC THENL
   [STRIP_TAC THEN MP_TAC SCH6_SLAB_GLUE THEN REWRITE_TAC[SCH_SLAB_GLUE_STATEMENT] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`g':real^3->real^3`; `g1:real^3->real^3`; `g1':real^3->real^3`;
                          `g2:real^3->real^3`; `g2':real^3->real^3`; `Theta:real^3->real^3`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    EXISTS_TAC `e0:real` THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD(sch_saddles (g1:real^3->real^3)) + CARD(sch_saddles (g2:real^3->real^3)) = 1 /\
                CARD(sch_saddles (g2:real^3->real^3)) + CARD(sch_saddles (g1:real^3->real^3)) = 1`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`CARD(sch_saddles (g1:real^3->real^3)) + CARD(sch_saddles (g2:real^3->real^3)) =
       CARD(sch_saddles (g:real^3->real^3))`;
      `CARD(sch_saddles (g:real^3->real^3)) = 1`] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g2:real^3->real^3) (sch_saddles g2) UNION IMAGE (g1:real^3->real^3) (sch_saddles g1) =
                IMAGE (g:real^3->real^3) (sch_saddles g)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[UNION_COMM] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `CARD(components(sch_level (g1:real^3->real^3) e)) <
                CARD(components(sch_level (g:real^3->real^3) e)) /\
                CARD(components(sch_level (g2:real^3->real^3) e)) <
                CARD(components(sch_level (g:real^3->real^3) e))` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `CARD(components(sch_level (g1:real^3->real^3) e)) +
                 CARD(components(sch_level (g2:real^3->real^3) e)) + 1 =
                 CARD(components(sch_level (g:real^3->real^3) e))` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(E1:real^3->bool) SUBSET IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) /\
                (E2:real^3->bool) SUBSET IMAGE (g:real^3->real^3) (sphere(vec 0,&1))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) =
                 E1 UNION IMAGE (Theta:real^3->real^3) sch_lat UNION E2` THEN
    DISCH_THEN SUBST1_TAC THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sch_bounds_ball (IMAGE (g2:real^3->real^3) (sphere(vec 0,&1))) /\
                sch_bounds_ball (IMAGE (g1:real^3->real^3) (sphere(vec 0,&1)))
                ==> sch_bounds_ball (IMAGE (g:real^3->real^3) (sphere(vec 0,&1)))`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[CONJ_SYM] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `r1 <= r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `connected((E1 UNION IMAGE (Theta:real^3->real^3) sch_lat UNION E2) INTER schy_box r1) /\
    ~((E1 UNION IMAGE (Theta:real^3->real^3) sch_lat UNION E2) INTER schy_box r1 = {})`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
      `IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) =
       E1 UNION IMAGE (Theta:real^3->real^3) sch_lat UNION E2`)) THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`E1:real^3->bool`; `E2:real^3->bool`; `IMAGE (Theta:real^3->real^3) sch_lat`;
                 `IMAGE (Theta:real^3->real^3) sch_cap1`; `IMAGE (Theta:real^3->real^3) sch_cap2`;
                 `schy_box r1`] SCHY_PIECE_SIDE) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
   [SUBGOAL_THEN `IMAGE (g1:real^3->real^3) (sphere(vec 0,&1)) INTER schy_box r1 =
                  IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) INTER schy_box r1 /\
                  IMAGE (g2:real^3->real^3) (sphere(vec 0,&1)) INTER schy_box r1 = {}`
    STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`g1:real^3->real^3`; `g1':real^3->real^3`; `r1:real`] THEN
    MATCH_MP_TAC SCHY_FAR_FINISH THEN
    MAP_EVERY EXISTS_TAC [`g':real^3->real^3`; `r:real`; `g2:real^3->real^3`;
                          `g2':real^3->real^3`; `E1:real^3->bool`;
                          `IMAGE (Theta:real^3->real^3) sch_cap1`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    SUBGOAL_THEN `IMAGE (g2:real^3->real^3) (sphere(vec 0,&1)) INTER schy_box r1 =
                  IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) INTER schy_box r1 /\
                  IMAGE (g1:real^3->real^3) (sphere(vec 0,&1)) INTER schy_box r1 = {}`
    STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`g2:real^3->real^3`; `g2':real^3->real^3`; `r1:real`] THEN
    MATCH_MP_TAC SCHY_FAR_FINISH THEN
    MAP_EVERY EXISTS_TAC [`g':real^3->real^3`; `r:real`; `g1:real^3->real^3`;
                          `g1':real^3->real^3`; `E2:real^3->bool`;
                          `IMAGE (Theta:real^3->real^3) sch_cap2`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The reflection x1 -> -x1 and the swap x1 <-> x2 as height-                *)
(* preserving maps, the cancellation with the right branch point, and the   *)
(* induction on the number of level components.                             *)
(* ------------------------------------------------------------------------- *)

let schy_refl = new_definition
 `schy_refl (x:real^2) = vector[--(x$1); x$2]:real^2`;;

let schy_swap = new_definition
 `schy_swap (x:real^2) = vector[x$2; x$1]:real^2`;;

let SCHY_REFL_SWAP = prove
 (`linear schy_refl /\ (!x. schy_refl(schy_refl x) = x) /\
   linear schy_swap /\ (!x. schy_swap(schy_swap x) = x)`,
  REWRITE_TAC[linear; schy_refl; schy_swap; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2;
              VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN REAL_ARITH_TAC);;

let SCHY_INVOL_DIFFEO = prove
 (`!A:real^2->real^2.
     linear A /\ (!x. A(A x) = x) ==> diffeomorphism_on (:real^2) (:real^2) A A`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) (A:real^2->real^2)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:real^2)`; `\x:real^2. x`; `A:real^2->real^2`] SMOOTH_MAP_ON_LINEAR_O) THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; OPEN_UNIV; o_DEF; ETA_AX];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[diffeomorphism_on; OPEN_UNIV; IN_UNIV] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN ASM_MESON_TAC[]);;

let SCHY_HP_RS = prove
 (`(!x:real^3. schy_hp schy_refl (&0) x = vector[--(x$1); x$2; x$3]) /\
   (!x:real^3. schy_hp schy_swap (&0) x = vector[x$2; x$1; x$3])`,
  REWRITE_TAC[schy_hp; sch5v_at; sch5v_pr; schy_refl; schy_swap; VECTOR_2; REAL_ADD_RID]);;

let SCHY_HP_INVOL = prove
 (`!A:real^2->real^2.
     linear A /\ (!x. A(A x) = x)
     ==> diffeomorphism_on (:real^2) (:real^2) A A /\
         (!x. schy_hp A (&0) (schy_hp A (&0) x) = x) /\
         linear (schy_hp A (&0)) /\
         (!x y. schy_hp A (&0) x = schy_hp A (&0) y ==> x = y) /\
         (!y. ?x. schy_hp A (&0) x = y) /\
         (!y s. y IN IMAGE (schy_hp A (&0)) s <=> schy_hp A (&0) y IN s)`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `diffeomorphism_on (:real^2) (:real^2) (A:real^2->real^2) A` ASSUME_TAC THENL
   [MATCH_MP_TAC SCHY_INVOL_DIFFEO THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. schy_hp (A:real^2->real^2) (&0) (schy_hp A (&0) x) = x` ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`A:real^2->real^2`; `A:real^2->real^2`; `&0`; `x:real^3`] SCHY_HP_INV) THEN
    ASM_REWRITE_TAC[REAL_NEG_0];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `linear (sch5v_pr:real^3->real^2)` ASSUME_TAC THENL
     [REWRITE_TAC[SCH5V_PR_AT_SMOOTH]; ALL_TAC] THEN
    REWRITE_TAC[linear; schy_hp; sch5v_at; REAL_ADD_RID] THEN
    ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]]);;

let SCHY_CHART_REFL = prove
 (`!(s:real^3->bool) r.
     schy_chart s r ==> schy_chart (IMAGE (schy_hp schy_refl (&0)) s) r`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPEC `schy_refl` SCHY_HP_INVOL) THEN REWRITE_TAC[SCHY_REFL_SWAP] THEN STRIP_TAC THEN
  REWRITE_TAC[schy_chart] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CH"))) THEN
  REPEAT(CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^3) IN IMAGE (schy_hp schy_refl (&0)) s <=>
                vector[--(x$1); x$2; x$3] IN s` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SCHY_HP_RS]; ALL_TAC] THEN
  USE_THEN "CH" (MP_TAC o SPEC `vector[--((x:real^3)$1); x$2; x$3]:real^3`) THEN
  REWRITE_TAC[VECTOR_3; REAL_POW_NEG; ARITH] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC]);;

let SCHY_CHART_FLIPSWAP = prove
 (`!(s:real^3->bool) r.
     schy_chart s r ==> schy_chart (IMAGE (schy_hp schy_swap (&0)) (IMAGE sch_flip3 s)) r`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPEC `schy_swap` SCHY_HP_INVOL) THEN REWRITE_TAC[SCHY_REFL_SWAP] THEN STRIP_TAC THEN
  REWRITE_TAC[schy_chart] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CH"))) THEN
  REPEAT(CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^3) IN IMAGE (schy_hp schy_swap (&0)) (IMAGE sch_flip3 s) <=>
                vector[x$2; x$1; --(x$3)] IN s` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[SCH5_IN_IMAGE_FLIP3] THEN REWRITE_TAC[SCHY_HP_RS; sch_flip3; VECTOR_3];
    ALL_TAC] THEN
  USE_THEN "CH" (MP_TAC o SPEC `vector[(x:real^3)$2; x$1; --(x$3)]:real^3`) THEN
  REWRITE_TAC[VECTOR_3; REAL_ABS_NEG] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC]);;

let SCHY_BRANCH_IN_LEVEL = prove
 (`!(g:real^3->real^3) r e.
     schy_chart (IMAGE g (sphere(vec 0,&1))) r /\ &0 < e /\ &16 * e < r pow 2
     ==> schy_lpt e IN sch_level g e /\ schy_rpt e IN sch_level g e /\
         vector[&0; sqrt e; --e] IN sch_level g (--e) /\
         vector[&0; --(sqrt e); --e] IN sch_level g (--e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [schy_chart]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CH"))) THEN
  SUBGOAL_THEN `&0 < sqrt e /\ sqrt e pow 2 = e /\ e < r pow 2 /\ e < r` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `r pow 2 < r` MP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `x = r * r /\ r * r < r * &1 ==> x < r`) THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[sch_level; IN_ELIM_THM; schy_lpt; schy_rpt; VECTOR_3] THEN
  REPEAT CONJ_TAC THEN USE_THEN "CH" (fun th -> W(fun (_,w) ->
    MP_TAC(SPEC (lhand w) th))) THEN
  REWRITE_TAC[VECTOR_3; REAL_POW_NEG; ARITH] THEN ASM_REWRITE_TAC[] THEN
  (ANTS_TAC THENL
    [CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
     DISCH_THEN SUBST1_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC]));;

let SCHY_CC_REFL = prove
 (`!s x:real^3. x IN s ==> x IN connected_component s x`,
  REWRITE_TAC[IN] THEN MESON_TAC[CONNECTED_COMPONENT_REFL; IN]);;

let SCHY_COMP_JOIN = prove
 (`!s c (x:real^3) y. c IN components s /\ x IN c /\ y IN c ==> y IN connected_component s x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(c:real^3->bool) SUBSET connected_component s x` MP_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN
    ASM_MESON_TAC[IN_COMPONENTS_CONNECTED; IN_COMPONENTS_SUBSET];
    UNDISCH_TAC `(y:real^3) IN c` THEN SET_TAC[]]);;

(* The cancellation with the right branch point: reflect x1 -> -x1.         *)

let SCHY_CANCEL_R = prove
 (`SCHY_CANCEL_STATEMENT
   ==> !(g:real^3->real^3) g' r e C.
         sch_neck g g' /\ sch_morse g /\ CARD(sch_saddles g) = 1 /\
         (?t0. t0 IN sch_saddles g /\ g t0 = vec 0) /\
         schy_chart (IMAGE g (sphere(vec 0,&1))) r /\ &0 < e /\ &16 * e < r pow 2 /\
         (!t. sch_crit g t ==> ~((g t)$3 = e)) /\
         C IN components(sch_level g e) /\ schy_rpt e IN C /\ ~(schy_lpt e IN C) /\
         (!x:real^2. x IN inside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C)
                     ==> ~((vector[x$1; x$2; e]:real^3) IN IMAGE g (sphere(vec 0,&1))))
         ==> sch_bounds_ball (IMAGE g (sphere(vec 0,&1)))`,
  REWRITE_TAC[SCHY_CANCEL_STATEMENT] THEN DISCH_THEN(LABEL_TAC "CAN") THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `schy_refl` SCHY_HP_INVOL) THEN REWRITE_TAC[SCHY_REFL_SWAP] THEN
  ABBREV_TAC `R = schy_hp schy_refl (&0)` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`schy_refl`; `schy_refl`; `&0`; `g:real^3->real^3`; `g':real^3->real^3`]
    SCHY_HP_MORSE) THEN
  ASM_REWRITE_TAC[REAL_NEG_0; REAL_ADD_RID] THEN STRIP_TAC THEN
  SUBGOAL_THEN `sch_bounds_ball (IMAGE ((R:real^3->real^3) o (g:real^3->real^3))
                                       (sphere(vec 0,&1)))` MP_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  USE_THEN "CAN" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`(g':real^3->real^3) o (R:real^3->real^3)`; `r:real`; `e:real`;
                        `IMAGE (R:real^3->real^3) C`] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    ASM_REWRITE_TAC[];
    EXISTS_TAC `t0:real^3` THEN ASM_REWRITE_TAC[o_THM] THEN
    EXPAND_TAC "R" THEN REWRITE_TAC[SCHY_HP_RS] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VEC_COMPONENT] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "R" THEN MATCH_MP_TAC SCHY_CHART_REFL THEN
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`R:real^3->real^3`; `sch_level (g:real^3->real^3) e`]
      COMPONENTS_LINEAR_IMAGE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "R" THEN
    REWRITE_TAC[SCHY_HP_RS; schy_lpt; schy_rpt; VECTOR_3; REAL_NEG_NEG] THEN
    UNDISCH_TAC `schy_rpt e IN C` THEN REWRITE_TAC[schy_rpt];
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "R" THEN
    REWRITE_TAC[SCHY_HP_RS; schy_lpt; schy_rpt; VECTOR_3; REAL_NEG_NEG] THEN
    UNDISCH_TAC `~(schy_lpt e IN C)` THEN REWRITE_TAC[schy_lpt];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (\y:real^3. vector[y$1; y$2]:real^2) (IMAGE (R:real^3->real^3) C) =
                IMAGE schy_refl (IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM] THEN EXPAND_TAC "R" THEN
    REWRITE_TAC[SCHY_HP_RS; schy_refl; VECTOR_3; VECTOR_2];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`schy_refl`; `IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C`]
    INSIDE_LINEAR_IMAGE) THEN
  ANTS_TAC THENL [REWRITE_TAC[SCHY_REFL_SWAP] THEN MESON_TAC[SCHY_REFL_SWAP]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
  X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN
  SUBGOAL_THEN `vector[(schy_refl w)$1; (schy_refl w)$2; e]:real^3 =
                (R:real^3->real^3)(vector[w$1; w$2; e])` SUBST1_TAC THENL
   [EXPAND_TAC "R" THEN REWRITE_TAC[SCHY_HP_RS; schy_refl; VECTOR_2; VECTOR_3]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "inside")) (concl th))) THEN
  FIRST_ASSUM ACCEPT_TAC);;

(* ------------------------------------------------------------------------- *)
(* The induction on the number of components of the level e, the flip-swap  *)
(* x -> (x2, x1, -x3) for the second case of the orientability lemma        *)
(* SCHY_LEMMA_J, and the reduction                                          *)
(* SCHY_DEPS /\ SCHY_CANCEL_STATEMENT ==> SCH_BASE1_STATEMENT.               *)
(* ------------------------------------------------------------------------- *)

let SCHY_INDUCT = prove
 (`!n (g:real^3->real^3) g' r e.
     SCHY_DEPS /\ SCHY_CANCEL_STATEMENT /\ schy_norm g g' r e /\
     CARD(components(sch_level g e)) = n
     ==> sch_bounds_ball (IMAGE g (sphere(vec 0,&1)))`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_THEN(LABEL_TAC "IH") THEN
  MAP_EVERY X_GEN_TAC [`g:real^3->real^3`; `g':real^3->real^3`; `r:real`; `e:real`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS (GEN_REWRITE_RULE I [schy_norm] th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [SCHY_DEPS]) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `r:real`; `e:real`] SCHY_BRANCH_IN_LEVEL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  UNDISCH_TAC `SCH_LEVEL_INNERMOST_STATEMENT` THEN REWRITE_TAC[SCH_LEVEL_INNERMOST_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`g:real^3->real^3`; `g':real^3->real^3`; `e:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `schy_lpt e` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real^3->bool` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `schy_lpt e IN C` THENL
   [SUBGOAL_THEN `~(schy_rpt e IN C)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `~(schy_rpt e IN connected_component (sch_level (g:real^3->real^3) e)
                                                       (schy_lpt e))` THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC SCHY_COMP_JOIN THEN EXISTS_TAC `C:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `SCHY_CANCEL_STATEMENT` THEN REWRITE_TAC[SCHY_CANCEL_STATEMENT] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`g':real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `schy_rpt e IN C` THENL
   [MP_TAC(MATCH_MP SCHY_CANCEL_R (ASSUME `SCHY_CANCEL_STATEMENT`)) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`g':real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`]
    SCHY_FAR_STEP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g1:real^3->real^3` (X_CHOOSE_THEN `g1':real^3->real^3`
    (X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  USE_THEN "IH" (MP_TAC o SPEC `CARD(components(sch_level (g1:real^3->real^3) e))`) THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
      `CARD(components(sch_level (g:real^3->real^3) e)) = n`)) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`g1:real^3->real^3`; `g1':real^3->real^3`; `r1:real`; `e:real`]) THEN
  ASM_REWRITE_TAC[]);;

let SCHY_FLIP_SWAP = prove
 (`!(g:real^3->real^3) g' r e.
     sch_neck g g' /\ sch_morse g /\ CARD(sch_saddles g) = 1 /\
     (?t0. t0 IN sch_saddles g /\ g t0 = vec 0) /\
     schy_chart (IMAGE g (sphere(vec 0,&1))) r /\ &0 < e /\ &16 * e < r pow 2 /\
     (!t. sch_crit g t ==> ~((g t)$3 = --e)) /\
     ~(vector[&0; --(sqrt e); --e] IN
       connected_component (sch_level g (--e)) (vector[&0; sqrt e; --e]))
     ==> ?g2 g2'. schy_norm g2 g2' r e /\
                  (sch_bounds_ball (IMAGE g2 (sphere(vec 0,&1)))
                   ==> sch_bounds_ball (IMAGE g (sphere(vec 0,&1))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `schy_swap` SCHY_HP_INVOL) THEN REWRITE_TAC[SCHY_REFL_SWAP] THEN
  ABBREV_TAC `W = schy_hp schy_swap (&0)` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `sch_neck (sch_flip3 o (g:real^3->real^3) o sch_flip3)
             (sch_flip3 o (g':real^3->real^3) o sch_flip3) /\
    sch_morse (sch_flip3 o (g:real^3->real^3) o sch_flip3) /\
    sch_saddles (sch_flip3 o (g:real^3->real^3) o sch_flip3) = IMAGE sch_flip3 (sch_saddles g) /\
    (!t. sch_crit (sch_flip3 o (g:real^3->real^3) o sch_flip3) t <=> sch_crit g (sch_flip3 t))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SCH5_NECK_FLIP THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SCH5_MORSE_FLIP THEN EXISTS_TAC `g':real^3->real^3` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SCH5_SADDLES_FLIP THEN EXISTS_TAC `g':real^3->real^3` THEN ASM_REWRITE_TAC[];
      GEN_TAC THEN MATCH_MP_TAC SCH5_CRIT_FLIP THEN EXISTS_TAC `g':real^3->real^3` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`schy_swap`; `schy_swap`; `&0`; `sch_flip3 o (g:real^3->real^3) o sch_flip3`;
                 `sch_flip3 o (g':real^3->real^3) o sch_flip3`] SCHY_HP_MORSE) THEN
  ASM_REWRITE_TAC[REAL_NEG_0; REAL_ADD_RID] THEN STRIP_TAC THEN
  EXISTS_TAC `(W:real^3->real^3) o sch_flip3 o (g:real^3->real^3) o sch_flip3` THEN
  EXISTS_TAC `(sch_flip3 o (g':real^3->real^3) o sch_flip3) o (W:real^3->real^3)` THEN
  REWRITE_TAC[schy_norm] THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`sch_flip3`; `sch_saddles (g:real^3->real^3)`] CARD_IMAGE_INJ) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[SCHY_SADDLES_FINITE] THEN MESON_TAC[SCH5_FLIP3_FACTS]; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    EXISTS_TAC `sch_flip3 t0` THEN ASM_REWRITE_TAC[o_THM; SCH5_FLIP3_FACTS] THEN
    CONJ_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    EXPAND_TAC "W" THEN
    REWRITE_TAC[SCHY_HP_RS; sch_flip3; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
                VEC_COMPONENT] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SCH5_IMAGE_FLIP_NECK] THEN EXPAND_TAC "W" THEN
    MATCH_MP_TAC SCHY_CHART_FLIPSWAP THEN FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    ASM_REWRITE_TAC[o_THM; SCH5_FLIP3_FACTS] THEN X_GEN_TAC `t:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `sch_flip3 t` o check (fun th -> concl th =
      `!t. sch_crit (g:real^3->real^3) t ==> ~((g t)$3 = --e)`)) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[SCH5_LEVEL_FLIP] THEN
    SUBGOAL_THEN `schy_lpt e = (W:real^3->real^3)(sch_flip3(vector[&0; --(sqrt e); --e])) /\
                  schy_rpt e = (W:real^3->real^3)(sch_flip3(vector[&0; sqrt e; --e]))`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [EXPAND_TAC "W" THEN
      REWRITE_TAC[SCHY_HP_RS; sch_flip3; schy_lpt; schy_rpt; VECTOR_3; REAL_NEG_NEG];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`W:real^3->real^3`; `IMAGE sch_flip3 (sch_level (g:real^3->real^3) (--e))`;
                   `sch_flip3(vector[&0; --(sqrt e); --e])`] CONNECTED_COMPONENT_LINEAR_IMAGE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`sch_flip3`; `sch_level (g:real^3->real^3) (--e)`;
                   `vector[&0; --(sqrt e); --e]:real^3`] CONNECTED_COMPONENT_LINEAR_IMAGE) THEN
    ANTS_TAC THENL [MESON_TAC[SCH5_FLIP3_FACTS]; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[SCH5_IN_IMAGE_FLIP3; SCH5_FLIP3_FACTS] THEN
    UNDISCH_TAC `~(vector[&0; --(sqrt e); --e] IN
                   connected_component (sch_level (g:real^3->real^3) (--e))
                                       (vector[&0; sqrt e; --e]))` THEN
    REWRITE_TAC[IN] THEN MESON_TAC[CONNECTED_COMPONENT_SYM];
    DISCH_TAC THEN
    SUBGOAL_THEN `sch_bounds_ball (IMAGE (sch_flip3 o (g:real^3->real^3) o sch_flip3)
                                         (sphere(vec 0,&1)))` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_imp o concl)) THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[SCH5_IMAGE_FLIP_NECK] THEN
    DISCH_THEN(MP_TAC o MATCH_MP SCH6_BOUNDS_BALL_FLIP) THEN
    REWRITE_TAC[SCH5_FLIP3_IMAGE_IMAGE]]);;

let SCHY_REDUCE = prove
 (`SCHY_DEPS /\ SCHY_CANCEL_STATEMENT ==> SCH_BASE1_STATEMENT`,
  REWRITE_TAC[SCH_BASE1_STATEMENT] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`g:real^3->real^3`; `g':real^3->real^3`] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [SCHY_DEPS]) THEN
  SUBGOAL_THEN `?t0:real^3. t0 IN sch_saddles g` (X_CHOOSE_TAC `t0:real^3`) THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN DISCH_TAC THEN
    UNDISCH_TAC `CARD(sch_saddles (g:real^3->real^3)) = 1` THEN
    ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `t0:real^3`] SCHY_NORMALIZE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real^2->real^2` (X_CHOOSE_THEN `A':real^2->real^2`
    (X_CHOOSE_THEN `b:real` (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`A:real^2->real^2`; `A':real^2->real^2`; `b:real`; `g:real^3->real^3`;
                 `g':real^3->real^3`] SCHY_HP_MORSE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `((schy_hp (A:real^2->real^2) b o (g:real^3->real^3)) t0) = vec 0` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `schy_chart (IMAGE (schy_hp (A:real^2->real^2) b o (g:real^3->real^3))
                                  (sphere(vec 0,&1))) r` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `G = schy_hp (A:real^2->real^2) b o (g:real^3->real^3)` THEN
  ABBREV_TAC `G' = (g':real^3->real^3) o schy_hp (A':real^2->real^2) (--b)` THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_imp(concl th) &&
    can (term_match [] `sch_bounds_ball (IMAGE (g:real^3->real^3) (sphere(vec 0,&1)))`)
        (rand(concl th)))) THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
   [UNDISCH_TAC `schy_chart (IMAGE (G:real^3->real^3) (sphere(vec 0,&1))) r` THEN
    SIMP_TAC[schy_chart];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {t | sch_crit (G:real^3->real^3) t}` ASSUME_TAC THENL
   [UNDISCH_TAC `sch_morse (G:real^3->real^3)` THEN SIMP_TAC[sch_morse]; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (\t. ((G:real^3->real^3) t)$3) {t | sch_crit G t} UNION
                  IMAGE (\t. --(((G:real^3->real^3) t)$3)) {t | sch_crit G t}`;
                 `r pow 2 / &16`] SCHY_AVOID_FINITE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[FINITE_UNION] THEN CONJ_TAC THEN MATCH_MP_TAC FINITE_IMAGE THEN
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_POW_LT]; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&16 * e < r pow 2` ASSUME_TAC THENL
   [UNDISCH_TAC `e < r pow 2 / &16` THEN SIMP_TAC[REAL_LT_RDIV_EQ; REAL_ARITH `&0 < &16`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. sch_crit (G:real^3->real^3) t ==> ~((G t)$3 = e) /\ ~((G t)$3 = --e)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real^3` THEN DISCH_TAC THEN
    UNDISCH_TAC `~(e IN IMAGE (\t. ((G:real^3->real^3) t)$3) {t | sch_crit G t} UNION
                         IMAGE (\t. --(((G:real^3->real^3) t)$3)) {t | sch_crit G t})` THEN
    REWRITE_TAC[IN_UNION; IN_IMAGE; IN_ELIM_THM; DE_MORGAN_THM; NOT_EXISTS_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN (MP_TAC o SPEC `t:real^3`)) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(!t. sch_crit (G:real^3->real^3) t ==> ~((G t)$3 = e)) /\
                (!t. sch_crit (G:real^3->real^3) t ==> ~((G t)$3 = --e))` STRIP_ASSUME_TAC THENL
   [MESON_TAC[ASSUME `!t. sch_crit (G:real^3->real^3) t ==> ~((G t)$3 = e) /\ ~((G t)$3 = --e)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `t0 IN sch_saddles (G:real^3->real^3) /\ CARD(sch_saddles G) = 1`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^3->real^3`; `r:real`; `e:real`] SCHY_BRANCH_IN_LEVEL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_CASES_TAC `schy_rpt e IN connected_component (sch_level (G:real^3->real^3) e) (schy_lpt e)`
  THENL
   [SUBGOAL_THEN `~(vector[&0; --(sqrt e); --e] IN
                    connected_component (sch_level (G:real^3->real^3) (--e))
                                        (vector[&0; sqrt e; --e]))` ASSUME_TAC THENL
     [DISCH_TAC THEN MATCH_MP_TAC SCHY_LEMMA_J THEN
      MAP_EVERY EXISTS_TAC
       [`G:real^3->real^3`; `G':real^3->real^3`; `r:real`; `e:real`;
        `connected_component (sch_level (G:real^3->real^3) e) (schy_lpt e)`;
        `connected_component (sch_level (G:real^3->real^3) (--e)) (vector[&0; sqrt e; --e])`] THEN
      ASM_SIMP_TAC[CONNECTED_COMPONENT_IN_COMPONENTS; SCHY_CC_REFL];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`G:real^3->real^3`; `G':real^3->real^3`; `r:real`; `e:real`]
      SCHY_FLIP_SWAP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXISTS_TAC `t0:real^3` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `G2:real^3->real^3` (X_CHOOSE_THEN `G2':real^3->real^3`
      STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC SCHY_INDUCT THEN
    MAP_EVERY EXISTS_TAC [`CARD(components(sch_level (G2:real^3->real^3) e))`;
                          `G2':real^3->real^3`; `r:real`; `e:real`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SCHY_INDUCT THEN
    MAP_EVERY EXISTS_TAC [`CARD(components(sch_level (G:real^3->real^3) e))`;
                          `G':real^3->real^3`; `r:real`; `e:real`] THEN
    ASM_REWRITE_TAC[schy_norm] THEN EXISTS_TAC `t0:real^3` THEN ASM_REWRITE_TAC[]]);;

