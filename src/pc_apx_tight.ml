(* ========================================================================= *)
(* pc_apx_tight: the tight-shell lemma APX_TIGHT_SHELL_STATEMENT of           *)
(* pc_apx_class (two cut spheres close to each other: the region between    *)
(* them is a product, starting at S_k and ending radially at S_j), and with *)
(* APX_REGION_FROM_TIGHT the region theorem APX_REGION_STATEMENT.  Method:  *)
(* in the coordinates of the neck e_k the transition map phi = ej_inv o e_k  *)
(* is aligned with the cylinder levels (APX_TRANSITION_DERIV); the splice of *)
(* the two level functions has no critical points; SMT_PRODUCT2_STATEMENT   *)
(* with power-map windows gives the product, glued to the two collars       *)
(* (MFD_PARAM_UNION).                                                       *)
(* ========================================================================= *)

needs "src/pc_apx_class.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The tight shell, part 1 (model analysis of a transition map              *)
(* psi between two necks, in the coordinates of the first): along rays the  *)
(* level s(psi) has derivative within kappa of +c or -c with one sign for   *)
(* the whole ray, the sign is the same for all rays (sphere variation), and *)
(* with that sign the level is aligned: s(psi y) - sg c s(y) varies by at   *)
(* most kappa |s y' - s y| + sqrt 2 pi kappa.                               *)
(* ------------------------------------------------------------------------- *)

(* The derivative alignment of a transition map psi at y (the form of      *)
(* APX_TRANSITION_DERIV): the differential of s o psi is sg c ds up to      *)
(* kappa in the cylinder norm.                                              *)

let apx_ts_align = new_definition
 `apx_ts_align (psi:real^3->real^3) (c:real) (kappa:real) (sg:real) (y:real^3) <=>
    !k. abs(sqrt(&2) * (psi y dot frechet_derivative psi (at y) k) / (psi y dot psi y) -
            sg * c * sqrt(&2) * (y dot k) / (y dot y))
        <= kappa * sqrt(k dot (cylinder_flow (&0) y ** k))`;;

let APX_TS_RAY_DERIV = prove
 (`!(psi:real^3->real^3) O c kappa om t.
        open O /\ smooth_map_on O psi /\
        (!y. y IN O ==> ~(psi y = vec 0)) /\
        (!y. y IN O ==> ?sg. (sg = &1 \/ sg = -- &1) /\ apx_ts_align psi c kappa sg y) /\
        norm om = &1 /\ exp(t / sqrt(&2)) % om IN O
        ==> ?d. ((\s. apx_sval(psi(exp(s / sqrt(&2)) % om))) has_real_derivative d)
                (atreal t) /\
                (abs(d - c) <= kappa \/ abs(d + c) <= kappa)`,
  REWRITE_TAC[apx_ts_align] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(exp(t / sqrt(&2)) % om:real^3 = vec 0)` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_RAY_NONZERO THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`psi:real^3->real^3`; `om:real^3`; `t:real`] APX_RAY_SVAL_DERIV) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `O:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `v = exp(t / sqrt(&2)) % (om:real^3)` THEN DISCH_TAC THEN
  EXISTS_TAC `sqrt(&2) * ((psi:real^3->real^3) v dot
                          frechet_derivative psi (at v) (inv(sqrt(&2)) % v)) /
              (psi v dot psi v)` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v:real^3` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> t = `cylinder_flow (&0)`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `sg:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPEC `inv(sqrt(&2)) % v:real^3`))) THEN
  MP_TAC(SPEC `v:real^3` APX_RAY_UNIT_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN (fun th -> REWRITE_TAC[th])) THEN
  REWRITE_TAC[SQRT_1; REAL_MUL_RID] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN REAL_ARITH_TAC);;

let APX_TS_RAY_MONO = prove
 (`!(psi:real^3->real^3) O c kappa om a b.
        open O /\ smooth_map_on O psi /\
        (!y. y IN O ==> ~(psi y = vec 0)) /\
        (!y. y IN O ==> ?sg. (sg = &1 \/ sg = -- &1) /\ apx_ts_align psi c kappa sg y) /\
        norm om = &1 /\ a < b /\ kappa < c /\
        (!t. a < t /\ t < b ==> exp(t / sqrt(&2)) % om IN O)
        ==> ?f'. (!t. a < t /\ t < b
                      ==> ((\s. apx_sval(psi(exp(s / sqrt(&2)) % om))) has_real_derivative
                           f' t) (atreal t)) /\
                 ((!t. a < t /\ t < b ==> abs(f' t - c) <= kappa) \/
                  (!t. a < t /\ t < b ==> abs(f' t + c) <= kappa))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. ?d. a < t /\ t < b
            ==> ((\s. apx_sval((psi:real^3->real^3)(exp(s / sqrt(&2)) % om)))
                 has_real_derivative d) (atreal t) /\
                (abs(d - c) <= kappa \/ abs(d + c) <= kappa)`
  MP_TAC THENL
   [X_GEN_TAC `t:real` THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN STRIP_TAC THEN
    MATCH_MP_TAC APX_TS_RAY_DERIV THEN EXISTS_TAC `O:real^3->bool` THEN ASM_SIMP_TAC[];
    REWRITE_TAC[SKOLEM_THM]] THEN
  DISCH_THEN(X_CHOOSE_TAC `f':real->real`) THEN EXISTS_TAC `f':real->real` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. apx_sval((psi:real^3->real^3)(exp(s / sqrt(&2)) % om))`;
                 `f':real->real`; `a:real`; `b:real`; `c:real`; `kappa:real`]
                APX_1D_MONO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN DISCH_THEN DISJ_CASES_TAC THENL
   [DISJ1_TAC THEN MATCH_MP_TAC APX_1D_INCR_DERIV THEN
    EXISTS_TAC `\s. apx_sval((psi:real^3->real^3)(exp(s / sqrt(&2)) % om))` THEN
    ASM_SIMP_TAC[];
    DISJ2_TAC THEN
    MP_TAC(ISPECL [`\s. --(apx_sval((psi:real^3->real^3)(exp(s / sqrt(&2)) % om)))`;
                   `\s. --((f':real->real) s)`; `a:real`; `b:real`; `c:real`; `kappa:real`]
                  APX_1D_INCR_DERIV) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> t = `f':real->real`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
        CONJ_TAC THENL
         [MP_TAC(ISPECL [`\s. apx_sval((psi:real^3->real^3)(exp(s / sqrt(&2)) % om))`;
                         `(f':real->real) t`; `atreal t`] HAS_REAL_DERIVATIVE_NEG) THEN
          ASM_REWRITE_TAC[];
          ASM_REAL_ARITH_TAC];
        REPEAT STRIP_TAC THEN BETA_TAC THEN
        MATCH_MP_TAC(REAL_ARITH `y < x ==> --x < --y`) THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`x:real`; `y:real`] o check (fun th ->
          is_forall(concl th) && not(can (find_term (fun t -> t = `f':real->real`)) (concl th))
          && can (find_term (fun t -> t = `apx_sval`)) (concl th))) THEN
        ASM_REWRITE_TAC[]];
      REWRITE_TAC[] THEN MESON_TAC[REAL_ARITH `abs(--x - c) = abs(x + c)`]]]);;

let APX_TS_RAY_SIGN_AT = prove
 (`!(psi:real^3->real^3) O c kappa om a b f' sg t.
        open O /\ smooth_map_on O psi /\
        (!y. y IN O ==> ~(psi y = vec 0)) /\
        (!y. y IN O ==> ?sg. (sg = &1 \/ sg = -- &1) /\ apx_ts_align psi c kappa sg y) /\
        norm om = &1 /\ kappa < c /\ (sg = &1 \/ sg = -- &1) /\
        (!t. a < t /\ t < b ==> exp(t / sqrt(&2)) % om IN O) /\
        (!t. a < t /\ t < b
             ==> ((\s. apx_sval(psi(exp(s / sqrt(&2)) % om))) has_real_derivative f' t)
                 (atreal t)) /\
        (!t. a < t /\ t < b ==> abs(f' t - sg * c) <= kappa) /\
        a < t /\ t < b
        ==> apx_ts_align psi c kappa sg (exp(t / sqrt(&2)) % om)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `~(exp(t / sqrt(&2)) % om:real^3 = vec 0) /\ exp(t / sqrt(&2)) % om IN O`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[APX_RAY_NONZERO]; ALL_TAC] THEN
  MP_TAC(ISPECL [`psi:real^3->real^3`; `om:real^3`; `t:real`] APX_RAY_SVAL_DERIV) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `O:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `v = exp(t / sqrt(&2)) % (om:real^3)` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(f':real->real) t = sqrt(&2) * ((psi:real^3->real^3) v dot
                         frechet_derivative psi (at v) (inv(sqrt(&2)) % v)) /
                        (psi v dot psi v)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
    EXISTS_TAC `\s. apx_sval((psi:real^3->real^3)(exp(s / sqrt(&2)) % om))` THEN
    EXISTS_TAC `t:real` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(v:real^3) IN O`) o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_ts_align")) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `sg0:real` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `sg0:real = sg` (fun th -> REWRITE_TAC[GSYM th] THEN FIRST_ASSUM ACCEPT_TAC) THEN
  UNDISCH_TAC `apx_ts_align (psi:real^3->real^3) c kappa sg0 v` THEN
  REWRITE_TAC[apx_ts_align] THEN DISCH_THEN(MP_TAC o SPEC `inv(sqrt(&2)) % v:real^3`) THEN
  MP_TAC(SPEC `v:real^3` APX_RAY_UNIT_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN (fun th -> REWRITE_TAC[th])) THEN
  REWRITE_TAC[SQRT_1; REAL_MUL_RID] THEN
  UNDISCH_TAC `(f':real->real) t = sqrt(&2) * ((psi:real^3->real^3) v dot
                         frechet_derivative psi (at v) (inv(sqrt(&2)) % v)) /
                        (psi v dot psi v)` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `abs((f':real->real) t - sg * c) <= kappa` MP_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `sg = &1 \/ sg = -- &1` THEN UNDISCH_TAC `sg0 = &1 \/ sg0 = -- &1` THEN
  UNDISCH_TAC `kappa < c` THEN
  REPEAT(POP_ASSUM(K ALL_TAC)) THEN
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq(concl th) && is_var(lhs(concl th))))) THEN
  ASM_REAL_ARITH_TAC);;

let APX_TS_RAYS_SAME = prove
 (`!(psi:real^3->real^3) O c kappa om1 om2 a b f1 f2 s1 s2.
        open O /\ smooth_map_on O psi /\
        (!y. y IN O ==> ~(psi y = vec 0)) /\
        (!y. y IN O ==> ?sg. (sg = &1 \/ sg = -- &1) /\ apx_ts_align psi c kappa sg y) /\
        apx_slab a b SUBSET O /\ a < &0 /\ &1 < b /\ &0 <= kappa /\
        (&1 + sqrt(&2) * pi) * kappa < c /\
        norm om1 = &1 /\ norm om2 = &1 /\
        (s1 = &1 \/ s1 = -- &1) /\ (s2 = &1 \/ s2 = -- &1) /\
        (!t. a < t /\ t < b
             ==> ((\s. apx_sval(psi(exp(s / sqrt(&2)) % om1))) has_real_derivative f1 t)
                 (atreal t) /\ abs(f1 t - s1 * c) <= kappa) /\
        (!t. a < t /\ t < b
             ==> ((\s. apx_sval(psi(exp(s / sqrt(&2)) % om2))) has_real_derivative f2 t)
                 (atreal t) /\ abs(f2 t - s2 * c) <= kappa)
        ==> s1 = s2`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(ISPECL [`\s. apx_sval((psi:real^3->real^3)(exp(s / sqrt(&2)) % om1))`;
                 `f1:real->real`; `a:real`; `b:real`; `s1 * c:real`; `kappa:real`;
                 `&0`; `&1`] APX_1D_MVT_BOUNDS) THEN
  MP_TAC(ISPECL [`\s. apx_sval((psi:real^3->real^3)(exp(s / sqrt(&2)) % om2))`;
                 `f2:real->real`; `a:real`; `b:real`; `s2 * c:real`; `kappa:real`;
                 `&0`; `&1`] APX_1D_MVT_BOUNDS) THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < &1`] THEN
  SUBGOAL_THEN
   `!r0. &0 < r0 /\ (!v:real^3. norm v = r0 ==> v IN O)
         ==> abs(apx_sval((psi:real^3->real^3)(r0 % om2)) - apx_sval(psi(r0 % om1)))
             <= sqrt(&2) * pi * kappa`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`psi:real^3->real^3`; `O:real^3->bool`; `r0:real`; `kappa:real`;
                   `c:real`] APX_SPHERE_VARIATION) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN CONJ_TAC THENL
         [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `O:real^3->bool` THEN
          ASM_REWRITE_TAC[];
          ASM_SIMP_TAC[]];
        REWRITE_TAC[GSYM apx_ts_align] THEN FIRST_ASSUM ACCEPT_TAC];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. a < t /\ t < b ==> !v:real^3. norm v = exp(t / sqrt(&2)) ==> v IN O`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `apx_slab a b SUBSET (O:real^3->bool)` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[apx_slab; annulus; IN_ELIM_THM] THEN
    REWRITE_TAC[REAL_EXP_MONO_LT] THEN
    SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
     [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV2_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(apx_sval((psi:real^3->real^3)(exp(&0 / sqrt(&2)) % om2)) -
        apx_sval(psi(exp(&0 / sqrt(&2)) % om1))) <= sqrt(&2) * pi * kappa /\
    abs(apx_sval((psi:real^3->real^3)(exp(&1 / sqrt(&2)) % om2)) -
        apx_sval(psi(exp(&1 / sqrt(&2)) % om1))) <= sqrt(&2) * pi * kappa`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `pi`)) (concl th))) THEN
    REWRITE_TAC[REAL_EXP_POS_LT] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= sqrt(&2) * pi * kappa` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[SQRT_POS_LE; REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MP_TAC PI_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `s2 = --s1` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `~(s1 = s2:real)` THEN UNDISCH_TAC `s1 = &1 \/ s1 = -- &1` THEN
    UNDISCH_TAC `s2 = &1 \/ s2 = -- &1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `(&1 + sqrt(&2) * pi) * kappa < c` THEN
  UNDISCH_TAC `s1 = &1 \/ s1 = -- &1` THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term (fun t -> t = `apx_sval`)) (concl th) && not(is_forall(concl th))))) THEN
  REWRITE_TAC[REAL_MUL_LNEG; REAL_SUB_RZERO; REAL_MUL_RID] THEN
  REPEAT(POP_ASSUM(K ALL_TAC)) THEN
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq(concl th) && is_var(lhs(concl th))))) THEN
  ASM_REAL_ARITH_TAC);;

let APX_TS_SIGN = prove
 (`!(psi:real^3->real^3) O c kappa a b.
        open O /\ smooth_map_on O psi /\
        (!y. y IN O ==> ~(psi y = vec 0)) /\
        (!y. y IN O ==> ?sg. (sg = &1 \/ sg = -- &1) /\ apx_ts_align psi c kappa sg y) /\
        apx_slab a b SUBSET O /\ a < &0 /\ &1 < b /\ &0 <= kappa /\
        (&1 + sqrt(&2) * pi) * kappa < c
        ==> ?sg. (sg = &1 \/ sg = -- &1) /\
                 !y. y IN apx_slab a b ==> apx_ts_align psi c kappa sg y`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `kappa < c` ASSUME_TAC THENL
   [SUBGOAL_THEN `kappa <= (&1 + sqrt(&2) * pi) * kappa` MP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x * k ==> k <= (&1 + x) * k`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[SQRT_POS_LE; REAL_POS] THEN
      MP_TAC PI_POS THEN REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!om:real^3. norm om = &1
       ==> !t. a < t /\ t < b ==> exp(t / sqrt(&2)) % om IN O`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `apx_slab a b SUBSET (O:real^3->bool)` THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[APX_RAY_IN_SLAB];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!om:real^3. norm om = &1
       ==> ?s f'. (s = &1 \/ s = -- &1) /\
                  !t. a < t /\ t < b
                      ==> ((\s. apx_sval((psi:real^3->real^3)(exp(s / sqrt(&2)) % om)))
                           has_real_derivative f' t) (atreal t) /\
                          abs(f' t - s * c) <= kappa`
  ASSUME_TAC THENL
   [X_GEN_TAC `om:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`psi:real^3->real^3`; `O:real^3->bool`; `c:real`; `kappa:real`;
                   `om:real^3`; `a:real`; `b:real`] APX_TS_RAY_MONO) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `f':real->real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN DISJ_CASES_TAC THENL
     [MAP_EVERY EXISTS_TAC [`&1`; `f':real->real`] THEN
      ASM_SIMP_TAC[REAL_MUL_LID];
      MAP_EVERY EXISTS_TAC [`-- &1`; `f':real->real`] THEN
      ASM_SIMP_TAC[REAL_MUL_LNEG; REAL_MUL_LID; REAL_SUB_RNEG]];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(basis 1:real^3) = &1` ASSUME_TAC THENL
   [SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `norm(basis 1:real^3) = &1`) o check (fun th ->
    is_forall(concl th) && can (find_term (fun t -> t = `has_real_derivative`)) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:real` (X_CHOOSE_THEN `f0:real->real`
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  EXISTS_TAC `s0:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN apx_slab a b` THEN
    REWRITE_TAC[apx_slab; annulus; IN_ELIM_THM] THEN
    MP_TAC(SPEC `a / sqrt(&2)` REAL_EXP_POS_LT) THEN
    MESON_TAC[NORM_0; REAL_LT_TRANS; REAL_LT_REFL];
    ALL_TAC] THEN
  MP_TAC(SPEC `y:real^3` APX_POLAR) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `om = inv(norm y) % (y:real^3)` THEN ABBREV_TAC `t = apx_sval(y:real^3)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `a < t /\ t < b` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`om:real^3`; `t:real`; `a:real`; `b:real`] APX_RAY_IN_SLAB) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `norm(om:real^3) = &1`) o check (fun th ->
    is_forall(concl th) && can (find_term (fun t -> t = `has_real_derivative`)) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` (X_CHOOSE_THEN `f':real->real`
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  SUBGOAL_THEN `s:real = s0` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC APX_TS_RAYS_SAME THEN
    MAP_EVERY EXISTS_TAC [`psi:real^3->real^3`; `O:real^3->bool`; `c:real`; `kappa:real`;
                          `om:real^3`; `basis 1:real^3`; `a:real`; `b:real`;
                          `f':real->real`; `f0:real->real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `exp(t / sqrt(&2)) % om = (y:real^3)`)) THEN
  MATCH_MP_TAC APX_TS_RAY_SIGN_AT THEN
  MAP_EVERY EXISTS_TAC [`O:real^3->bool`; `a:real`; `b:real`; `f':real->real`] THEN
  ASM_SIMP_TAC[]);;

let APX_TS_RAY_DERIV_SG = prove
 (`!(psi:real^3->real^3) U c kappa sg om a b.
        open U /\ smooth_map_on U psi /\ (!y. y IN U ==> ~(psi y = vec 0)) /\
        (!y. y IN U ==> apx_ts_align psi c kappa sg y) /\ norm om = &1 /\
        (!t. a < t /\ t < b ==> exp(t / sqrt(&2)) % om IN U)
        ==> ?f'. !t. a < t /\ t < b
                     ==> ((\s. apx_sval(psi(exp(s / sqrt(&2)) % om))) has_real_derivative
                          f' t) (atreal t) /\
                         abs(f' t - sg * c) <= kappa`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(exp(t / sqrt(&2)) % om:real^3 = vec 0) /\ exp(t / sqrt(&2)) % om IN U`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[APX_RAY_NONZERO]; ALL_TAC] THEN
  MP_TAC(ISPECL [`psi:real^3->real^3`; `om:real^3`; `t:real`] APX_RAY_SVAL_DERIV) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `v = exp(t / sqrt(&2)) % (om:real^3)` THEN DISCH_TAC THEN
  EXISTS_TAC `sqrt(&2) * ((psi:real^3->real^3) v dot
                          frechet_derivative psi (at v) (inv(sqrt(&2)) % v)) /
              (psi v dot psi v)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `apx_ts_align (psi:real^3->real^3) c kappa sg v` MP_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[apx_ts_align] THEN DISCH_THEN(MP_TAC o SPEC `inv(sqrt(&2)) % v:real^3`) THEN
  MP_TAC(SPEC `v:real^3` APX_RAY_UNIT_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN (fun th -> REWRITE_TAC[th])) THEN
  REWRITE_TAC[SQRT_1; REAL_MUL_RID]);;

let APX_TS_LEVEL = prove
 (`!(psi:real^3->real^3) c kappa a b sg y y'.
        smooth_map_on (apx_slab a b) psi /\
        (!y. y IN apx_slab a b ==> ~(psi y = vec 0)) /\
        &0 <= kappa /\ (sg = &1 \/ sg = -- &1) /\
        (!y. y IN apx_slab a b ==> apx_ts_align psi c kappa sg y) /\
        y IN apx_slab a b /\ y' IN apx_slab a b
        ==> abs((apx_sval(psi y') - sg * c * apx_sval y') -
                (apx_sval(psi y) - sg * c * apx_sval y))
            <= kappa * abs(apx_sval y' - apx_sval y) + sqrt(&2) * pi * kappa`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `open(apx_slab a b:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[apx_slab; OPEN_ANNULUS]; ALL_TAC] THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0) /\ ~(y':real^3 = vec 0)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN apx_slab a b` THEN UNDISCH_TAC `(y':real^3) IN apx_slab a b` THEN
    REWRITE_TAC[apx_slab; annulus; IN_ELIM_THM] THEN
    MP_TAC(SPEC `a / sqrt(&2)` REAL_EXP_POS_LT) THEN
    MESON_TAC[NORM_0; REAL_LT_TRANS; REAL_LT_REFL];
    ALL_TAC] THEN
  MP_TAC(SPEC `y:real^3` APX_POLAR) THEN MP_TAC(SPEC `y':real^3` APX_POLAR) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `om = inv(norm y) % (y:real^3)` THEN ABBREV_TAC `t = apx_sval(y:real^3)` THEN
  ABBREV_TAC `om' = inv(norm y') % (y':real^3)` THEN ABBREV_TAC `t' = apx_sval(y':real^3)` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `a < t /\ t < b /\ a < t' /\ t' < b` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`om:real^3`; `t:real`; `a:real`; `b:real`] APX_RAY_IN_SLAB) THEN
    MP_TAC(ISPECL [`om':real^3`; `t':real`; `a:real`; `b:real`] APX_RAY_IN_SLAB) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  (* the sphere variation at level t' *)
  SUBGOAL_THEN
   `abs(apx_sval((psi:real^3->real^3)(exp(t' / sqrt(&2)) % om')) -
        apx_sval(psi(exp(t' / sqrt(&2)) % om))) <= sqrt(&2) * pi * kappa`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`psi:real^3->real^3`; `apx_slab a b:real^3->bool`;
                   `exp(t' / sqrt(&2))`; `kappa:real`; `c:real`] APX_SPHERE_VARIATION) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_EXP_POS_LT] THEN REPEAT CONJ_TAC THENL
       [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
        SUBGOAL_THEN `~(v:real^3 = vec 0)` ASSUME_TAC THENL
         [DISCH_TAC THEN UNDISCH_TAC `norm(v:real^3) = exp(t' / sqrt(&2))` THEN
          ASM_REWRITE_TAC[NORM_0] THEN MP_TAC(SPEC `t' / sqrt(&2)` REAL_EXP_POS_LT) THEN
          REAL_ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `apx_sval(v:real^3) = t'` ASSUME_TAC THENL
         [ASM_REWRITE_TAC[apx_sval; LOG_EXP] THEN MATCH_MP_TAC REAL_DIV_LMUL THEN
          SIMP_TAC[SQRT_EQ_0; REAL_OF_NUM_EQ; ARITH];
          ALL_TAC] THEN
        MP_TAC(SPEC `v:real^3` APX_POLAR) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
        ASM_SIMP_TAC[APX_RAY_IN_SLAB];
        X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN CONJ_TAC THENL
         [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
          EXISTS_TAC `apx_slab a b:real^3->bool` THEN ASM_REWRITE_TAC[];
          ASM_SIMP_TAC[]];
        X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN EXISTS_TAC `sg:real` THEN
        ASM_REWRITE_TAC[GSYM apx_ts_align] THEN ASM_SIMP_TAC[]];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the ray part along om from t to t' *)
  MP_TAC(ISPECL [`psi:real^3->real^3`; `apx_slab a b:real^3->bool`; `c:real`; `kappa:real`;
                 `sg:real`; `om:real^3`; `a:real`; `b:real`] APX_TS_RAY_DERIV_SG) THEN
  ASM_SIMP_TAC[APX_RAY_IN_SLAB] THEN
  DISCH_THEN(X_CHOOSE_TAC `f':real->real`) THEN
  SUBGOAL_THEN
   `abs((apx_sval((psi:real^3->real^3)(exp(t' / sqrt(&2)) % om)) -
         apx_sval(psi(exp(t / sqrt(&2)) % om))) - sg * c * (t' - t))
    <= kappa * abs(t' - t)`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `t:real = t'` THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `t:real = t'`)) THEN
      REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_ABS_0; REAL_LE_REFL];
      ALL_TAC] THEN
    SUBGOAL_THEN `t < t' \/ t' < t` DISJ_CASES_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`\s. apx_sval((psi:real^3->real^3)(exp(s / sqrt(&2)) % om))`;
                     `f':real->real`; `a:real`; `b:real`; `sg * c:real`; `kappa:real`;
                     `t:real`; `t':real`] APX_1D_MVT_BOUNDS) THEN
      ASM_SIMP_TAC[] THEN
      SUBGOAL_THEN `abs(t' - t) = t' - t` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REAL_ARITH_TAC;
      MP_TAC(ISPECL [`\s. apx_sval((psi:real^3->real^3)(exp(s / sqrt(&2)) % om))`;
                     `f':real->real`; `a:real`; `b:real`; `sg * c:real`; `kappa:real`;
                     `t':real`; `t:real`] APX_1D_MVT_BOUNDS) THEN
      ASM_SIMP_TAC[] THEN
      SUBGOAL_THEN `abs(t' - t) = t - t'` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `exp(t / sqrt(&2)) % om = (y:real^3)` THEN
  UNDISCH_TAC `exp(t' / sqrt(&2)) % om' = (y':real^3)` THEN
  REPEAT(DISCH_THEN(SUBST_ALL_TAC o SYM)) THEN
  SUBGOAL_THEN `apx_sval(exp(t / sqrt(&2)) % om:real^3) = t /\
                apx_sval(exp(t' / sqrt(&2)) % om':real^3) = t'`
  (fun th -> REWRITE_TAC[th]) THENL
   [ASM_SIMP_TAC[APX_RAY_SVAL]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!A1 A2 B x d1 d2. abs(A1 - A2) <= d1 /\ abs((A2 - B) - x) <= d2
                      ==> abs((A1 - B) - x) <= d2 + d1`) THEN
  EXISTS_TAC `apx_sval((psi:real^3->real^3)(exp(t' / sqrt(&2)) % om))` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `(a - sg * c * t') - (b - sg * c * t) =
                          (a - b) - sg * c * (t' - t)`] THEN
  FIRST_ASSUM ACCEPT_TAC);;

(* ------------------------------------------------------------------------- *)
(* The tight shell, part 2 (the splice in the model).  The                  *)
(* splice of the own level s and the transferred level D - s o psi with the  *)
(* smooth step in s: smooth, equal to s below the window and to D - s o psi  *)
(* above it, with positive derivative along rays when psi is aligned with   *)
(* sign -1 and the levels agree in the window up to d0 (C d0 small); the     *)
(* crossing of the unit sphere of the other neck on a ray (IVT).             *)
(* ------------------------------------------------------------------------- *)

let APX_TS_STEP_DERIV0 = prove
 (`!Ds x. (!t. (smooth_step has_real_derivative Ds t) (atreal t)) /\ (x < &0 \/ &1 < x)
          ==> Ds x = &0`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `x:real`) ASSUME_TAC) THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
  MAP_EVERY EXISTS_TAC [`smooth_step`; `x:real`] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM DISJ_CASES_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    MAP_EVERY EXISTS_TAC [`\t:real. &0`; `--x`] THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `y:real` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SMOOTH_STEP_0 THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    MAP_EVERY EXISTS_TAC [`\t:real. &1`; `x - &1`] THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `y:real` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SMOOTH_STEP_1 THEN ASM_REAL_ARITH_TAC]);;

let APX_TS_SPLICE_1D = prove
 (`!g g' t0 w1 w2 D Ds C c kappa d0.
        w1 < w2 /\ (g has_real_derivative g') (atreal t0) /\ abs(g' + c) <= kappa /\
        kappa < c /\
        (!t. (smooth_step has_real_derivative Ds t) (atreal t) /\ abs(Ds t) <= C) /\
        (w1 <= t0 /\ t0 <= w2 ==> abs(D - g t0 - t0) <= d0) /\ &0 <= d0 /\
        C * d0 < (w2 - w1) * min (c - kappa) (&1)
        ==> ?d. ((\t. (&1 - smooth_step((t - w1) / (w2 - w1))) * t +
                      smooth_step((t - w1) / (w2 - w1)) * (D - g t))
                 has_real_derivative d) (atreal t0) /\ &0 < d`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < w2 - w1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `chi = smooth_step((t0 - w1) / (w2 - w1))` THEN
  ABBREV_TAC `dchi = Ds((t0 - w1) / (w2 - w1)) * inv(w2 - w1)` THEN
  SUBGOAL_THEN `((\t. smooth_step((t - w1) / (w2 - w1))) has_real_derivative dchi) (atreal t0)`
  ASSUME_TAC THENL
   [EXPAND_TAC "dchi" THEN
    MP_TAC(ISPECL [`\t. (t - w1) / (w2 - w1)`; `smooth_step`; `inv(w2 - w1)`;
                   `Ds((t0 - w1) / (w2 - w1)):real`; `t0:real`] REAL_DIFF_CHAIN_ATREAL) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_div] THEN
    MP_TAC(ISPECL [`\t:real. t - w1`; `&1`; `\t:real. inv(w2 - w1)`; `&0`; `t0:real`]
                  HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN ANTS_TAC THENL
     [MP_TAC(ISPECL [`\t:real. t`; `&1`; `\t:real. (w1:real)`; `&0`; `atreal t0`]
                    HAS_REAL_DERIVATIVE_SUB) THEN
      REWRITE_TAC[HAS_REAL_DERIVATIVE_ID; HAS_REAL_DERIVATIVE_CONST; REAL_SUB_RZERO; ETA_AX];
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `(&1 - chi) * &1 + chi * --g' + dchi * ((D - (g:real->real) t0) - t0)` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `((\t. &1 - smooth_step((t - w1) / (w2 - w1))) has_real_derivative
                   (&0 - dchi)) (atreal t0)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`\t:real. &1`; `&0`; `\t. smooth_step((t - w1) / (w2 - w1))`;
                     `dchi:real`; `atreal t0`] HAS_REAL_DERIVATIVE_SUB) THEN
      ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST];
      ALL_TAC] THEN
    SUBGOAL_THEN `((\t. D - (g:real->real) t) has_real_derivative (&0 - g')) (atreal t0)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`\t:real. (D:real)`; `&0`; `g:real->real`; `g':real`; `atreal t0`]
                    HAS_REAL_DERIVATIVE_SUB) THEN
      ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST; ETA_AX];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\t. &1 - smooth_step((t - w1) / (w2 - w1))`; `&0 - dchi`;
                   `\t:real. t`; `&1`; `t0:real`] HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
    ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_ID] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\t. smooth_step((t - w1) / (w2 - w1))`; `dchi:real`;
                   `\t. D - (g:real->real) t`; `&0 - g'`; `t0:real`]
                  HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\t. (&1 - smooth_step((t - w1) / (w2 - w1))) * t`;
                   `(&1 - smooth_step((t0 - w1) / (w2 - w1))) * &1 + (&0 - dchi) * t0`;
                   `\t. smooth_step((t - w1) / (w2 - w1)) * (D - (g:real->real) t)`;
                   `smooth_step((t0 - w1) / (w2 - w1)) * (&0 - g') +
                    dchi * (D - (g:real->real) t0)`;
                   `atreal t0`] HAS_REAL_DERIVATIVE_ADD) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= chi /\ chi <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "chi" THEN REWRITE_TAC[SMOOTH_STEP_BOUNDS]; ALL_TAC] THEN
  SUBGOAL_THEN `c - kappa <= --g'` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `m = min (c - kappa) (&1)` THEN
  SUBGOAL_THEN `m <= (&1 - chi) * &1 + chi * --g'` ASSUME_TAC THENL
   [SUBGOAL_THEN `(&1 - chi) * m <= (&1 - chi) * &1 /\ chi * m <= chi * --g'` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN EXPAND_TAC "m" THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < m` ASSUME_TAC THENL [EXPAND_TAC "m" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `w1 <= t0 /\ t0 <= w2` THENL
   [SUBGOAL_THEN `abs(dchi * ((D - (g:real->real) t0) - t0)) <= (C * inv(w2 - w1)) * d0`
    ASSUME_TAC THENL
     [REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      REWRITE_TAC[REAL_ABS_POS] THEN CONJ_TAC THENL
       [EXPAND_TAC "dchi" THEN REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_INV] THEN
        ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
        REWRITE_TAC[REAL_ARITH `(D - g) - t = D - g - t`] THEN ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(C * inv(w2 - w1)) * d0 < m` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_ARITH `(C * i) * d = (C * d) * i`; GSYM real_div] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `dchi = &0` SUBST1_TAC THENL
   [EXPAND_TAC "dchi" THEN
    SUBGOAL_THEN `Ds((t0 - w1) / (w2 - w1)) = &0` (fun th -> REWRITE_TAC[th; REAL_MUL_LZERO]) THEN
    MATCH_MP_TAC APX_TS_STEP_DERIV0 THEN ASM_SIMP_TAC[] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let APX_TS_NZ_FROM_RAY = prove
 (`!(H:real^3->real^1) v d.
        H differentiable (at v) /\ ~(v = vec 0) /\ ~(d = &0) /\
        ((\s. drop(H(exp(s / sqrt(&2)) % (inv(norm v) % v)))) has_real_derivative d)
        (atreal (apx_sval v))
        ==> ~(frechet_derivative H (at v) = (\h. vec 0))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `v:real^3` APX_POLAR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `((H:real^3->real^1) has_derivative (\h. vec 0))
                (at (exp(apx_sval v / sqrt(&2)) % inv(norm v) % v))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && is_abs(rhs(concl th)))) THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP APX_RAY_COMPOSE_DERIV) THEN
  REWRITE_TAC[DROP_VEC] THEN DISCH_TAC THEN
  UNDISCH_TAC `~(d = &0)` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
  MAP_EVERY EXISTS_TAC [`\s. drop((H:real^3->real^1)(exp(s / sqrt(&2)) % (inv(norm v) % v)))`;
                        `apx_sval(v:real^3)`] THEN
  ASM_REWRITE_TAC[]);;

(* The splice of the own level s and the transferred level D - s o psi.      *)

let apx_ts_splice = new_definition
 `apx_ts_splice (psi:real^3->real^3) (w1:real) (w2:real) (D:real) (v:real^3) =
    (&1 - smooth_step((apx_sval v - w1) / (w2 - w1))) * apx_sval v +
    smooth_step((apx_sval v - w1) / (w2 - w1)) * (D - apx_sval(psi v))`;;

let APX_TS_SPLICE_SMOOTH = prove
 (`!O (psi:real^3->real^3) w1 w2 D.
        open O /\ smooth_map_on O psi /\
        (!v. v IN O ==> ~(psi v = vec 0) /\ ~(v = vec 0))
        ==> smooth_map_on O (\v. lift(apx_ts_splice psi w1 w2 D v))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[apx_ts_splice] THEN
  SUBGOAL_THEN `smooth_map_on O (\v:real^3. lift(apx_sval v))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `{y:real^3 | ~(y = vec 0)}` THEN
    REWRITE_TAC[APX_SVAL_SMOOTH] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on O (\v:real^3. lift(apx_sval((psi:real^3->real^3) v)))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\v:real^3. lift(apx_sval((psi:real^3->real^3) v))) =
                  (\y. lift(apx_sval y)) o psi` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `{y:real^3 | ~(y = vec 0)}` THEN
    ASM_REWRITE_TAC[OPEN_NONZERO; APX_SVAL_SMOOTH] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on O (\v:real^3. lift(smooth_step((apx_sval v - w1) / (w2 - w1))))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`O:real^3->bool`;
                   `\v:real^3. lift((apx_sval v - w1) / (w2 - w1))`]
                  SMOOTH_MAP_ON_SMOOTH_STEP_COMPOSE) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    MP_TAC(ISPECL [`O:real^3->bool`; `inv(w2 - w1)`;
                   `\v:real^3. lift(apx_sval v - w1)`] SMOOTH_MAP_ON_LIFT_CMUL) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`O:real^3->bool`; `\v:real^3. lift(apx_sval v)`; `\v:real^3. lift w1`]
                  SMOOTH_MAP_ON_LIFT_SUB) THEN
    ASM_REWRITE_TAC[LIFT_DROP; SMOOTH_MAP_ON_CONST];
    ALL_TAC] THEN
  ABBREV_TAC `X = \v:real^3. lift(smooth_step((apx_sval v - w1) / (w2 - w1)))` THEN
  ABBREV_TAC `Y = \v:real^3. lift(apx_sval v)` THEN
  ABBREV_TAC `Z = \v:real^3. lift(D - apx_sval((psi:real^3->real^3) v))` THEN
  SUBGOAL_THEN `smooth_map_on O (Z:real^3->real^1)` ASSUME_TAC THENL
   [EXPAND_TAC "Z" THEN
    MP_TAC(ISPECL [`O:real^3->bool`; `\v:real^3. lift D`;
                   `\v:real^3. lift(apx_sval((psi:real^3->real^3) v))`]
                  SMOOTH_MAP_ON_LIFT_SUB) THEN
    ASM_REWRITE_TAC[LIFT_DROP; SMOOTH_MAP_ON_CONST];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\v. lift((&1 - smooth_step((apx_sval v - w1) / (w2 - w1))) * apx_sval v +
              smooth_step((apx_sval v - w1) / (w2 - w1)) *
              (D - apx_sval((psi:real^3->real^3) v)))) =
    (\v. lift(drop((\v. lift(drop((\v. lift(&1)) v) - drop((X:real^3->real^1) v))) v) *
              drop((Y:real^3->real^1) v) +
              drop(X v) * drop((Z:real^3->real^1) v)))`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["X"; "Y"; "Z"] THEN REWRITE_TAC[FUN_EQ_THM; LIFT_DROP];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`O:real^3->bool`;
                 `\v:real^3. lift(drop((\v:real^3. lift(drop((\v:real^3. lift(&1)) v) -
                                                   drop((X:real^3->real^1) v))) v) *
                                  drop((Y:real^3->real^1) v))`;
                 `\v:real^3. lift(drop((X:real^3->real^1) v) * drop((Z:real^3->real^1) v))`]
                SMOOTH_MAP_ON_LIFT_ADD) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`O:real^3->bool`; `\v:real^3. lift(&1 - drop((X:real^3->real^1) v))`;
                   `Y:real^3->real^1`] SMOOTH_MAP_ON_LIFT_MUL) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    EXPAND_TAC "Y" THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`O:real^3->bool`; `\v:real^3. lift(&1)`; `X:real^3->real^1`]
                  SMOOTH_MAP_ON_LIFT_SUB) THEN
    ASM_REWRITE_TAC[LIFT_DROP; SMOOTH_MAP_ON_CONST; ETA_AX];
    MP_TAC(ISPECL [`O:real^3->bool`; `X:real^3->real^1`; `Z:real^3->real^1`]
                  SMOOTH_MAP_ON_LIFT_MUL) THEN
    ASM_REWRITE_TAC[]]);;

let APX_TS_SPLICE_ZONES = prove
 (`!(psi:real^3->real^3) w1 w2 D v.
        w1 < w2
        ==> (apx_sval v <= w1 ==> apx_ts_splice psi w1 w2 D v = apx_sval v) /\
            (w2 <= apx_sval v ==> apx_ts_splice psi w1 w2 D v = D - apx_sval(psi v))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[apx_ts_splice] THEN
  SUBGOAL_THEN `&0 < w2 - w1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THEN DISCH_TAC THENL
   [SUBGOAL_THEN `smooth_step((apx_sval(v:real^3) - w1) / (w2 - w1)) = &0` SUBST1_TAC THENL
     [MATCH_MP_TAC SMOOTH_STEP_0 THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    SUBGOAL_THEN `smooth_step((apx_sval(v:real^3) - w1) / (w2 - w1)) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC SMOOTH_STEP_1 THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC]]);;

(* Along a ray the splice is the 1D splice of t and D - s(psi(ray t)).       *)

let APX_TS_SPLICE_RAY = prove
 (`!(psi:real^3->real^3) w1 w2 D om.
        norm om = &1
        ==> (\t. apx_ts_splice psi w1 w2 D (exp(t / sqrt(&2)) % om)) =
            (\t. (&1 - smooth_step((t - w1) / (w2 - w1))) * t +
                 smooth_step((t - w1) / (w2 - w1)) *
                 (D - (\s. apx_sval(psi(exp(s / sqrt(&2)) % om))) t))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM; apx_ts_splice] THEN
  ASM_SIMP_TAC[APX_RAY_SVAL]);;

let APX_TS_SPLICE_REGULAR = prove
 (`!(psi:real^3->real^3) O c kappa w1 w2 D d0 Ds C v.
        open O /\ smooth_map_on O psi /\
        (!y. y IN O ==> ~(psi y = vec 0) /\ ~(y = vec 0)) /\
        (!y. y IN O ==> apx_ts_align psi c kappa (-- &1) y) /\
        w1 < w2 /\ kappa < c /\
        (!t. (smooth_step has_real_derivative Ds t) (atreal t) /\ abs(Ds t) <= C) /\
        &0 <= d0 /\ C * d0 < (w2 - w1) * min (c - kappa) (&1) /\
        v IN O /\
        (w1 <= apx_sval v /\ apx_sval v <= w2
         ==> abs(D - apx_sval(psi v) - apx_sval v) <= d0)
        ==> ~(frechet_derivative (\v. lift(apx_ts_splice psi w1 w2 D v)) (at v) =
              (\h. vec 0))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `~(v:real^3 = vec 0)` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(SPEC `v:real^3` APX_POLAR) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `om = inv(norm v) % (v:real^3)` THEN ABBREV_TAC `t0 = apx_sval(v:real^3)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`O:real^3->bool`; `om:real^3`; `t0:real`] APX_RAY_OPEN_PRE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `dd:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`psi:real^3->real^3`; `O:real^3->bool`; `c:real`; `kappa:real`;
                 `-- &1`; `om:real^3`; `t0 - dd`; `t0 + dd`] APX_TS_RAY_DERIV_SG) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real->real` (MP_TAC o SPEC `t0:real`)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `x - -- &1 * c = x + c`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\s. apx_sval((psi:real^3->real^3)(exp(s / sqrt(&2)) % om))`;
                 `(f':real->real) t0`; `t0:real`; `w1:real`; `w2:real`; `D:real`;
                 `Ds:real->real`; `C:real`; `c:real`; `kappa:real`; `d0:real`]
                APX_TS_SPLICE_1D) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `exp(t0 / sqrt(&2)) % om = (v:real^3)` THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    EXPAND_TAC "t0" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC APX_TS_NZ_FROM_RAY THEN EXISTS_TAC `d:real` THEN
  BETA_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `O:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC APX_TS_SPLICE_SMOOTH THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> concl th = `inv(norm v) % (v:real^3) = om`)) THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> concl th = `apx_sval(v:real^3) = t0`)) THEN
  MP_TAC(ISPECL [`psi:real^3->real^3`; `w1:real`; `w2:real`; `D:real`; `om:real^3`]
                APX_TS_SPLICE_RAY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  FIRST_ASSUM(ACCEPT_TAC o CONV_RULE(DEPTH_CONV BETA_CONV) o check (fun th ->
    can (find_term (fun t -> t = `d:real`)) (concl th) &&
    can (find_term (fun t -> t = `has_real_derivative`)) (concl th))));;

(* The splice context on an open set O of the model.                         *)

let apx_ts_ctx = new_definition
 `apx_ts_ctx (psi:real^3->real^3) (O:real^3->bool) (c:real) (kappa:real) (w1:real)
             (w2:real) (D:real) (d0:real) (C:real) (Ds:real->real) <=>
    open O /\ smooth_map_on O psi /\
    (!y. y IN O ==> ~(psi y = vec 0) /\ ~(y = vec 0)) /\
    (!y. y IN O ==> apx_ts_align psi c kappa (-- &1) y) /\
    w1 < w2 /\ kappa < c /\
    (!t. (smooth_step has_real_derivative Ds t) (atreal t) /\ abs(Ds t) <= C) /\
    &0 <= d0 /\ C * d0 < (w2 - w1) * min (c - kappa) (&1) /\
    (!y. y IN O /\ w1 <= apx_sval y /\ apx_sval y <= w2
         ==> abs(D - apx_sval(psi y) - apx_sval y) <= d0)`;;

let APX_TS_CTX_REGULAR = prove
 (`!(psi:real^3->real^3) O c kappa w1 w2 D d0 C Ds v.
        apx_ts_ctx psi O c kappa w1 w2 D d0 C Ds /\ v IN O
        ==> ~(frechet_derivative (\v. lift(apx_ts_splice psi w1 w2 D v)) (at v) =
              (\h. vec 0))`,
  REWRITE_TAC[apx_ts_ctx] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`psi:real^3->real^3`; `O:real^3->bool`; `c:real`; `kappa:real`;
                 `w1:real`; `w2:real`; `D:real`; `d0:real`; `Ds:real->real`; `C:real`;
                 `v:real^3`] APX_TS_SPLICE_REGULAR) THEN
  ASM_SIMP_TAC[]);;

let APX_TS_POSDER_INCR = prove
 (`!f f' a b.
        (!t. a < t /\ t < b ==> (f has_real_derivative f' t) (atreal t) /\ &0 < f' t)
        ==> !x y. a < x /\ x < y /\ y < b ==> f x < f y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_STRICTLY_INCREASING_IMP THEN
  EXISTS_TAC `f':real->real` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN CONJ_TAC THEN X_GEN_TAC `t:real` THEN STRIP_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]]);;

let APX_TS_CTX_RAY_INCR = prove
 (`!(psi:real^3->real^3) O c kappa w1 w2 D d0 C Ds om a b.
        apx_ts_ctx psi O c kappa w1 w2 D d0 C Ds /\ norm om = &1 /\
        (!t. a < t /\ t < b ==> exp(t / sqrt(&2)) % om IN O)
        ==> !x y. a < x /\ x < y /\ y < b
                  ==> apx_ts_splice psi w1 w2 D (exp(x / sqrt(&2)) % om) <
                      apx_ts_splice psi w1 w2 D (exp(y / sqrt(&2)) % om)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. ?d. a < t /\ t < b
            ==> ((\t. apx_ts_splice (psi:real^3->real^3) w1 w2 D (exp(t / sqrt(&2)) % om))
                 has_real_derivative d) (atreal t) /\ &0 < d`
  MP_TAC THENL
   [X_GEN_TAC `t0:real` THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN STRIP_TAC THEN
    UNDISCH_TAC `apx_ts_ctx (psi:real^3->real^3) O c kappa w1 w2 D d0 C Ds` THEN
    REWRITE_TAC[apx_ts_ctx] THEN STRIP_TAC THEN
    SUBGOAL_THEN `exp(t0 / sqrt(&2)) % om IN (O:real^3->bool)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`O:real^3->bool`; `om:real^3`; `t0:real`] APX_RAY_OPEN_PRE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `dd:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`psi:real^3->real^3`; `O:real^3->bool`; `c:real`; `kappa:real`;
                   `-- &1`; `om:real^3`; `t0 - dd`; `t0 + dd`] APX_TS_RAY_DERIV_SG) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `f':real->real` (MP_TAC o SPEC `t0:real`)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `x - -- &1 * c = x + c`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`psi:real^3->real^3`; `w1:real`; `w2:real`; `D:real`; `om:real^3`]
                  APX_TS_SPLICE_RAY) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC APX_TS_SPLICE_1D THEN
    MAP_EVERY EXISTS_TAC [`(f':real->real) t0`; `Ds:real->real`; `C:real`; `c:real`;
                          `kappa:real`; `d0:real`] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `apx_sval(exp(t0 / sqrt(&2)) % om:real^3) = t0` ASSUME_TAC THENL
     [ASM_SIMP_TAC[APX_RAY_SVAL]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `exp(t0 / sqrt(&2)) % om:real^3` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `d0:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `fd:real->real`)] THEN
  MP_TAC(ISPECL [`\t. apx_ts_splice (psi:real^3->real^3) w1 w2 D (exp(t / sqrt(&2)) % om)`;
                 `fd:real->real`; `a:real`; `b:real`] APX_TS_POSDER_INCR) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[]]);;

let APX_TS_CROSS = prove
 (`!(psi:real^3->real^3) c kappa a b x1.
        smooth_map_on (apx_slab a b) psi /\
        (!y. y IN apx_slab a b ==> ~(psi y = vec 0)) /\
        (!y. y IN apx_slab a b ==> apx_ts_align psi c kappa (-- &1) y) /\
        norm x1 = &1 /\ a < &0 /\ &0 < apx_sval(psi x1) /\
        &2 * apx_sval(psi x1) < b /\ &0 <= kappa /\ kappa + &1 / &2 < c
        ==> ?tau. &0 < tau /\ tau <= &2 * apx_sval(psi x1) /\
                  apx_sval(psi(exp(tau / sqrt(&2)) % x1)) = &0`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ABBREV_TAC `tau1 = apx_sval((psi:real^3->real^3) x1)` THEN
  SUBGOAL_THEN `open(apx_slab a b:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[apx_slab; OPEN_ANNULUS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`psi:real^3->real^3`; `apx_slab a b:real^3->bool`; `c:real`; `kappa:real`;
                 `-- &1`; `x1:real^3`; `a:real`; `b:real`] APX_TS_RAY_DERIV_SG) THEN
  ASM_SIMP_TAC[APX_RAY_IN_SLAB] THEN
  DISCH_THEN(X_CHOOSE_TAC `f':real->real`) THEN
  ABBREV_TAC `g = \t. apx_sval((psi:real^3->real^3)(exp(t / sqrt(&2)) % x1))` THEN
  SUBGOAL_THEN `(g:real->real) (&0) = tau1` ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN EXPAND_TAC "tau1" THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_EXP_0; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real->real) (&2 * tau1) < &0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:real->real`; `f':real->real`; `a:real`; `b:real`; `-- &1 * c:real`;
                   `kappa:real`; `&0`; `&2 * tau1`] APX_1D_MVT_BOUNDS) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(-- &1 * c + kappa) * (&2 * tau1 - &0) < --tau1` MP_TAC THENL
     [REWRITE_TAC[REAL_SUB_RZERO] THEN
      SUBGOAL_THEN `(-- &1 * c + kappa) * (&2 * tau1) = --(&2 * tau1 * (c - kappa))`
      SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_LT_NEG2] THEN
      SUBGOAL_THEN `tau1 * &1 < tau1 * (&2 * (c - kappa))` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real->real`; `&0`; `&2 * tau1`; `&0`] REAL_IVT_DECREASING) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC APX_1D_CONT THEN EXISTS_TAC `f':real->real` THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `f':real->real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `tau:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `tau:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_CASES_TAC `tau = &0` THENL
     [UNDISCH_TAC `(g:real->real) tau = &0` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    UNDISCH_TAC `(g:real->real) tau = &0` THEN EXPAND_TAC "g" THEN REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The tight shell, part 3 (the model).  psi on a slab of the               *)
(* first neck, aligned with sign -1, crossing the unit sphere of the second  *)
(* neck at level tau on the ray of x1, with the disjoint annuli (1/2,2):     *)
(* tau >= 19/10 l2 (l2 = sqrt 2 log 2), the window [tau - 11/10 l2 - 1/20,   *)
(* tau - 11/10 l2], the splice context, the zones, the level sets of the     *)
(* splice F (F = l32 is the sphere of radius 3/2, F = D - l2 is the sphere   *)
(* of radius 2 of the second neck, F = D its unit sphere), compactness,      *)
(* radial convexity and regularity.                                          *)
(* ------------------------------------------------------------------------- *)

(* Numerical facts on l2 = sqrt 2 log 2 (half width of annulus(1/2,2) in    *)
(* s-units) and l32 = sqrt 2 log(3/2).                                      *)

let APX_TS_NUM = prove
 (`&7 / &10 <= sqrt(&2) * log(&2) /\ sqrt(&2) * log(&2) <= &3 / &2 /\
   &0 < sqrt(&2) * log(&3 / &2) /\ sqrt(&2) * log(&3 / &2) < sqrt(&2) * log(&2) /\
   &1 / &20 <= &7 / &10 * (sqrt(&2) * log(&2)) - sqrt(&2) * log(&3 / &2) /\
   &1 <= sqrt(&2)`,
  STRIP_ASSUME_TAC APX_LOG_CONSTS THEN
  SUBGOAL_THEN `&7 / &5 <= sqrt(&2) /\ &1 <= sqrt(&2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. &0 < x ==> &1 - inv x <= log x` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MP_TAC(SPEC `log(inv x)` REAL_EXP_LE_X) THEN
    ASM_SIMP_TAC[EXP_LOG; REAL_LT_INV; LOG_INV] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(SPEC `&2` (ASSUME `!x. &0 < x ==> &1 - inv x <= log x`)) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&7 / &5 * &1 / &2` THEN
    CONJ_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `&7 / &5 * &1 / &2 = (&7 / &5) * (&1 / &2)`] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `&7 * log(&2) - &10 * log(&3 / &2) = log(&131072 / &59049)` ASSUME_TAC THENL
   [SUBGOAL_THEN `&131072 / &59049 = &2 pow 7 / (&3 / &2) pow 10` SUBST1_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    SIMP_TAC[LOG_DIV; REAL_POW_LT; REAL_ARITH `&0 < &2`; REAL_ARITH `&0 < &3 / &2`;
             LOG_POW] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&72023 / &131072 <= log(&131072 / &59049)` ASSUME_TAC THENL
   [MP_TAC(SPEC `&131072 / &59049` (ASSUME `!x. &0 < x ==> &1 - inv x <= log x`)) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&7 / &10 * (sqrt(&2) * log(&2)) - sqrt(&2) * log(&3 / &2) =
                sqrt(&2) * (&7 * log(&2) - &10 * log(&3 / &2)) / &10`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * (&72023 / &131072) / &10` THEN
  CONJ_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  CONJ_TAC THENL [ALL_TAC; CONV_TAC REAL_RAT_REDUCE_CONV] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_REWRITE_TAC[REAL_POS] THEN
  REWRITE_TAC[GSYM real_div] THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let APX_TS_SLAB_LOG = prove
 (`!r1 r2. &0 < r1 /\ &0 < r2
           ==> annulus r1 r2 = apx_slab (sqrt(&2) * log r1) (sqrt(&2) * log r2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[apx_slab] THEN
  SUBGOAL_THEN `~(sqrt(&2) = &0)` ASSUME_TAC THENL
   [SIMP_TAC[SQRT_EQ_0; REAL_OF_NUM_EQ; ARITH]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_FIELD `~(s = &0) ==> (s * x) / s = x`; EXP_LOG]);;

(* The window of the splice, just below the crossing level tau of the other *)
(* unit sphere: zone B (transferred level) from wb, zone A (own level) up to *)
(* wa = wb - 1/20, and the constant D of the transferred level.             *)

let apx_ts_wb = new_definition
 `apx_ts_wb (tau:real) = tau - &11 / &10 * (sqrt(&2) * log(&2))`;;

let apx_ts_wa = new_definition
 `apx_ts_wa (tau:real) = apx_ts_wb tau - &1 / &20`;;

let apx_ts_dd = new_definition
 `apx_ts_dd (c:real) (tau:real) = c * tau + (&1 - c) * apx_ts_wb tau`;;

(* The model hypotheses: psi (the transition map in the coordinates of the  *)
(* first neck) on a slab, aligned with sign -1, crossing the second unit    *)
(* sphere at level tau on the ray of x1, and the disjoint annuli.           *)

let apx_ts_mdl = new_definition
 `apx_ts_mdl (psi:real^3->real^3) (c:real) (kappa:real) (a:real) (b:real) (x1:real^3)
             (tau:real) <=>
    smooth_map_on (apx_slab a b) psi /\ (!y. y IN apx_slab a b ==> ~(psi y = vec 0)) /\
    (!y. y IN apx_slab a b ==> apx_ts_align psi c kappa (-- &1) y) /\
    a <= -- &2 /\ tau + &3 <= b /\ norm x1 = &1 /\ &0 < tau /\
    apx_sval(psi(exp(tau / sqrt(&2)) % x1)) = &0 /\
    (!v. v IN apx_slab a b /\ v IN annulus (&1 / &2) (&2)
         ==> ~(psi v IN annulus (&1 / &2) (&2))) /\
    &0 <= kappa /\ kappa <= &1 / &1000 /\ abs(c - &1) <= &1 / &1000`;;

let APX_TS_MDL_TAU = prove
 (`!(psi:real^3->real^3) c kappa a b x1 tau.
        apx_ts_mdl psi c kappa a b x1 tau
        ==> &19 / &10 * (sqrt(&2) * log(&2)) <= tau`,
  REWRITE_TAC[apx_ts_mdl] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  STRIP_ASSUME_TAC APX_TS_NUM THEN
  ABBREV_TAC `l2 = sqrt(&2) * log(&2)` THEN
  SUBGOAL_THEN `annulus (&1 / &2) (&2):real^3->bool = apx_slab (--l2) l2` ASSUME_TAC THENL
   [MP_TAC(SPECL [`&1 / &2`; `&2`] APX_TS_SLAB_LOG) THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    EXPAND_TAC "l2" THEN
    SIMP_TAC[REAL_ARITH `&1 / &2 = inv(&2)`; LOG_INV; REAL_ARITH `&0 < &2`] THEN
    REWRITE_TAC[REAL_MUL_RNEG];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(apx_slab a b:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[apx_slab; OPEN_ANNULUS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`psi:real^3->real^3`; `apx_slab a b:real^3->bool`; `c:real`; `kappa:real`;
                 `-- &1`; `x1:real^3`; `a:real`; `b:real`] APX_TS_RAY_DERIV_SG) THEN
  ASM_SIMP_TAC[APX_RAY_IN_SLAB] THEN
  DISCH_THEN(X_CHOOSE_TAC `f':real->real`) THEN
  ABBREV_TAC `ts = &19 / &20 * l2` THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `exp(ts / sqrt(&2)) % x1 IN apx_slab a b /\
                exp(ts / sqrt(&2)) % x1 IN apx_slab (--l2) l2` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[APX_RAY_IN_SLAB] THEN EXPAND_TAC "ts" THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `exp(ts / sqrt(&2)) % x1:real^3` o check (fun th ->
    is_forall(concl th) && can (find_term (fun t -> t = `annulus (&1 / &2) (&2):real^3->bool`))
    (concl th))) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[APX_SLAB_SVAL] THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `abs(apx_sval((psi:real^3->real^3)(exp(ts / sqrt(&2)) % x1))) < l2`
  (fun th -> MP_TAC th THEN REAL_ARITH_TAC) THEN
  SUBGOAL_THEN `!t t'. a < t /\ t < t' /\ t' < b
                ==> (-- &1 * c - kappa) * (t' - t) <=
                    apx_sval((psi:real^3->real^3)(exp(t' / sqrt(&2)) % x1)) -
                    apx_sval(psi(exp(t / sqrt(&2)) % x1)) /\
                    apx_sval(psi(exp(t' / sqrt(&2)) % x1)) -
                    apx_sval(psi(exp(t / sqrt(&2)) % x1)) <=
                    (-- &1 * c + kappa) * (t' - t)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\s. apx_sval((psi:real^3->real^3)(exp(s / sqrt(&2)) % x1))`;
                   `f':real->real`; `a:real`; `b:real`; `-- &1 * c:real`; `kappa:real`;
                   `t:real`; `t':real`] APX_1D_MVT_BOUNDS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `ts:real = tau` THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c + kappa <= &1002 / &1000 /\ &0 <= c - kappa` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ts < tau \/ tau < ts` DISJ_CASES_TAC THENL
   [ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPECL [`ts:real`; `tau:real`]) THEN
    ANTS_TAC THENL [EXPAND_TAC "ts" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(c + kappa) * (tau - ts) < l2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(&1002 / &1000) * (tau - ts)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        EXPAND_TAC "ts" THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (c - kappa) * (tau - ts)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPECL [`tau:real`; `ts:real`]) THEN
    ANTS_TAC THENL [EXPAND_TAC "ts" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(c + kappa) * (ts - tau) < l2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `(&1002 / &1000) * (&19 / &20 * l2)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN EXPAND_TAC "ts" THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (c - kappa) * (ts - tau)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC]);;

let APX_TS_MDL_LEVEL = prove
 (`!(psi:real^3->real^3) c kappa a b x1 tau y.
        apx_ts_mdl psi c kappa a b x1 tau /\ y IN apx_slab a b
        ==> abs(apx_sval(psi y) + c * apx_sval y - c * tau)
            <= kappa * abs(apx_sval y - tau) + sqrt(&2) * pi * kappa`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[apx_ts_mdl] THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `exp(tau / sqrt(&2)) % x1 IN apx_slab a b /\
                apx_sval(exp(tau / sqrt(&2)) % x1:real^3) = tau` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[APX_RAY_IN_SLAB; APX_RAY_SVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`psi:real^3->real^3`; `c:real`; `kappa:real`; `a:real`; `b:real`;
                 `-- &1`; `exp(tau / sqrt(&2)) % x1:real^3`; `y:real^3`] APX_TS_LEVEL) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let APX_TS_MDL_FACTS = prove
 (`!(psi:real^3->real^3) c kappa a b x1 tau.
        apx_ts_mdl psi c kappa a b x1 tau
        ==> apx_ts_wa tau = apx_ts_wb tau - &1 / &20 /\
            apx_ts_wb tau = tau - &11 / &10 * (sqrt(&2) * log(&2)) /\
            sqrt(&2) * log(&3 / &2) + &1 / &10 * (sqrt(&2) * log(&2)) <= apx_ts_wa tau /\
            abs(apx_ts_dd c tau - tau) <= &1 / &500 /\
            &1 / &20 <= apx_ts_dd c tau - sqrt(&2) * log(&2) - sqrt(&2) * log(&3 / &2) /\
            sqrt(&2) * pi * kappa <= &1 / &200 /\
            &998 / &1000 <= c - kappa /\ c + kappa <= &1002 / &1000`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP APX_TS_MDL_TAU) THEN
  POP_ASSUM MP_TAC THEN UNDISCH_TAC `apx_ts_mdl (psi:real^3->real^3) c kappa a b x1 tau` THEN
  REWRITE_TAC[apx_ts_mdl] THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  DISCH_TAC THEN STRIP_ASSUME_TAC APX_TS_NUM THEN
  REWRITE_TAC[apx_ts_wa; apx_ts_wb; apx_ts_dd] THEN
  ABBREV_TAC `l2 = sqrt(&2) * log(&2)` THEN
  ABBREV_TAC `l32 = sqrt(&2) * log(&3 / &2)` THEN
  SUBGOAL_THEN `sqrt(&2) * pi * kappa <= &1 / &200` ASSUME_TAC THENL
   [SUBGOAL_THEN `sqrt(&2) <= &3 / &2 /\ pi <= &16 / &5` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV;
        MP_TAC PI_APPROX_32 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&3 / &2 * &16 / &5) * kappa` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_SIMP_TAC[SQRT_POS_LE; REAL_POS; PI_POS_LE];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_ARITH `(c * tau + (&1 - c) * (tau - x)) - tau = --((&1 - c) * x)`] THEN
    REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 / &1000 * &2` THEN
    CONJ_TAC THENL [ALL_TAC; CONV_TAC REAL_RAT_REDUCE_CONV] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `abs((&1 - c) * (&11 / &10 * l2)) <= &1 / &500` MP_TAC THENL
     [REWRITE_TAC[REAL_ABS_MUL] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 / &1000 * &2` THEN
      CONJ_TAC THENL [ALL_TAC; CONV_TAC REAL_RAT_REDUCE_CONV] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* Arithmetic of the level alignment |s + c d| <= k |d| + e (d = s v - tau). *)

let APX_TS_ARITH_LO = prove
 (`!s c k e d L. abs(s + c * d) <= k * abs d + e /\ &998 / &1000 <= c - k /\ &0 <= k /\
                 d <= --L /\ &0 <= L
                 ==> &998 / &1000 * L - e <= s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `d = --(--d) /\ &0 <= --d /\ L <= --d` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `u = --d` THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `d = --u`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_ABS_NEG; REAL_MUL_RNEG]) THEN
  SUBGOAL_THEN `abs u = u` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&998 / &1000 * u <= (c - k) * u` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let APX_TS_ARITH_HI = prove
 (`!s c k e d L. abs(s + c * d) <= k * abs d + e /\ &998 / &1000 <= c - k /\ &0 <= k /\
                 L <= d /\ &0 <= L
                 ==> s <= e - &998 / &1000 * L`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs d = d` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&998 / &1000 * d <= (c - k) * d` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let APX_TS_ARITH_MID = prove
 (`!s c k e d L. abs(s + c * d) <= k * abs d + e /\ c + k <= &1002 / &1000 /\ &0 <= k /\
                 &998 / &1000 <= c - k /\ --L <= d /\ d <= &0 /\ &0 <= L
                 ==> s <= &1002 / &1000 * L + e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `d = --(--d) /\ &0 <= --d /\ --d <= L` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `u = --d` THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `d = --u`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_ABS_NEG; REAL_MUL_RNEG]) THEN
  SUBGOAL_THEN `abs u = u` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(c + k) * u <= &1002 / &1000 * L` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The level alignment in the form used below. *)

let APX_TS_MDL_ALIGN = prove
 (`!(psi:real^3->real^3) c kappa a b x1 tau v.
        apx_ts_mdl psi c kappa a b x1 tau /\ v IN apx_slab a b
        ==> abs(apx_sval(psi v) + c * (apx_sval v - tau))
            <= kappa * abs(apx_sval v - tau) + &1 / &200`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`psi:real^3->real^3`; `c:real`; `kappa:real`; `a:real`; `b:real`;
                 `x1:real^3`; `tau:real`; `v:real^3`] APX_TS_MDL_LEVEL) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_TS_MDL_FACTS) THEN
  REWRITE_TAC[REAL_ARITH `s + c * (x - t) = s + c * x - c * t`] THEN
  ASM_REAL_ARITH_TAC);;

(* Points whose transferred level is in [-1, 21/20 l2 + 1/100] lie in zone B *)
(* and inside the model slab W.                                              *)

let APX_TS_MDL_INV = prove
 (`!(psi:real^3->real^3) c kappa a b x1 tau v.
        apx_ts_mdl psi c kappa a b x1 tau /\ v IN apx_slab a b /\
        -- &1 <= apx_sval(psi v) /\
        apx_sval(psi v) <= &21 / &20 * (sqrt(&2) * log(&2)) + &1 / &100
        ==> apx_ts_wb tau < apx_sval v /\ apx_sval v < tau + &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`psi:real^3->real^3`; `c:real`; `kappa:real`; `a:real`; `b:real`;
                 `x1:real^3`; `tau:real`; `v:real^3`] APX_TS_MDL_ALIGN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_TS_MDL_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_TS_MDL_TAU) THEN
  STRIP_ASSUME_TAC APX_TS_NUM THEN
  SUBGOAL_THEN `&0 <= kappa` ASSUME_TAC THENL
   [ASM_MESON_TAC[apx_ts_mdl]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`apx_sval((psi:real^3->real^3) v)`; `c:real`; `kappa:real`; `&1 / &200`;
                   `apx_sval(v:real^3) - tau`; `&11 / &10 * (sqrt(&2) * log(&2))`]
                  APX_TS_ARITH_LO) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`apx_sval((psi:real^3->real^3) v)`; `c:real`; `kappa:real`; `&1 / &200`;
                   `apx_sval(v:real^3) - tau`; `&2`] APX_TS_ARITH_HI) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let APX_TS_MDL_CTX = prove
 (`!(psi:real^3->real^3) c kappa a b x1 tau Ds C.
        apx_ts_mdl psi c kappa a b x1 tau /\
        (!t. (smooth_step has_real_derivative Ds t) (atreal t) /\ abs(Ds t) <= C) /\
        &0 <= C /\ kappa <= inv(&200 * (C + &1)) /\ abs(c - &1) <= inv(&200 * (C + &1))
        ==> apx_ts_ctx psi (apx_slab (-- &1) (tau + &2)) c kappa (apx_ts_wa tau)
                       (apx_ts_wb tau) (apx_ts_dd c tau)
                       (kappa * &2 + sqrt(&2) * pi * kappa + abs(&1 - c) / &20) C Ds`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_TS_MDL_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_TS_MDL_TAU) THEN
  STRIP_ASSUME_TAC APX_TS_NUM THEN
  UNDISCH_TAC `apx_ts_mdl (psi:real^3->real^3) c kappa a b x1 tau` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[apx_ts_mdl] th)) THEN
  SUBGOAL_THEN `apx_slab (-- &1) (tau + &2) SUBSET apx_slab a b` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_SLAB_SUBSET THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `K = inv(&200 * (C + &1))` THEN
  SUBGOAL_THEN `&0 < K /\ C * K <= &1 / &200` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM real_div] THEN
    SUBGOAL_THEN `&0 < &200 * (C + &1)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&2) * pi <= &24 / &5` ASSUME_TAC THENL
   [SUBGOAL_THEN `sqrt(&2) <= &3 / &2 /\ pi <= &16 / &5` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV;
        MP_TAC PI_APPROX_32 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 / &2 * &16 / &5` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_POS; PI_POS_LE];
      CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN `kappa * &2 + sqrt(&2) * pi * kappa + abs(&1 - c) / &20 <= &137 / &20 * K /\
                &0 <= kappa * &2 + sqrt(&2) * pi * kappa + abs(&1 - c) / &20`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `sqrt(&2) * pi * kappa <= &24 / &5 * K /\ &0 <= sqrt(&2) * pi * kappa`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
        ASM_SIMP_TAC[REAL_LE_MUL; SQRT_POS_LE; REAL_POS; PI_POS_LE];
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_MUL; SQRT_POS_LE; REAL_POS;
                                                    PI_POS_LE]];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `abs(&1 - c) = abs(c - &1)`] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[apx_ts_ctx] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[apx_slab; OPEN_ANNULUS];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `apx_slab a b:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN apx_slab a b` ASSUME_TAC THENL
     [UNDISCH_TAC `apx_slab (-- &1) (tau + &2) SUBSET apx_slab a b` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[];
      UNDISCH_TAC `(y:real^3) IN apx_slab (-- &1) (tau + &2)` THEN
      SIMP_TAC[APX_SLAB_SVAL]];
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN apx_slab a b` ASSUME_TAC THENL
     [UNDISCH_TAC `apx_slab (-- &1) (tau + &2) SUBSET apx_slab a b` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[];
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `C * (&137 / &20 * K)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&998 / &1000 <= min (c - kappa) (&1)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `C * (&137 / &20 * K) = &137 / &20 * (C * K)`] THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN apx_slab a b` ASSUME_TAC THENL
     [UNDISCH_TAC `apx_slab (-- &1) (tau + &2) SUBSET apx_slab a b` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`psi:real^3->real^3`; `c:real`; `kappa:real`; `a:real`; `b:real`;
                   `x1:real^3`; `tau:real`; `y:real^3`] APX_TS_MDL_LEVEL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `abs(apx_sval(y:real^3) - tau) <= &2 /\
                  &0 <= apx_ts_wb tau - apx_sval y /\ apx_ts_wb tau - apx_sval y <= &1 / &20`
    STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `kappa * abs(apx_sval(y:real^3) - tau) <= kappa * &2 /\
                  abs(&1 - c) * (apx_ts_wb tau - apx_sval(y:real^3)) <= abs(&1 - c) / &20`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
        GEN_REWRITE_TAC (RAND_CONV) [real_div] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `apx_ts_dd c tau - apx_sval((psi:real^3->real^3) y) - apx_sval y =
      --(apx_sval(psi y) + c * apx_sval y - c * tau) +
      (&1 - c) * (apx_ts_wb tau - apx_sval y)`
    SUBST1_TAC THENL [REWRITE_TAC[apx_ts_dd] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!x y a b e. abs x <= a + b /\ abs y <= e ==> abs(--x + y) <= a + b + e`) THEN
    CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ABS_MUL] THEN
      SUBGOAL_THEN `abs(apx_ts_wb tau - apx_sval(y:real^3)) = apx_ts_wb tau - apx_sval y`
      SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]]]);;

let APX_TS_MDL_EST = prove
 (`!(psi:real^3->real^3) c kappa a b x1 tau v.
        apx_ts_mdl psi c kappa a b x1 tau /\ v IN apx_slab (-- &1) (tau + &2)
        ==> (apx_sval v <= apx_ts_wb tau
             ==> sqrt(&2) * log(&2) + &1 / &50 <= apx_sval(psi v)) /\
            (apx_ts_wa tau <= apx_sval v /\ apx_sval v <= tau
             ==> apx_sval(psi v) <= &111 / &100 * (sqrt(&2) * log(&2)) + &3 / &50) /\
            (tau <= apx_sval v ==> apx_sval(psi v) <= &1 / &200) /\
            (tau + &1 <= apx_sval v ==> apx_sval(psi v) < &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_TS_MDL_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_TS_MDL_TAU) THEN
  STRIP_ASSUME_TAC APX_TS_NUM THEN
  SUBGOAL_THEN `&0 <= kappa /\ apx_slab (-- &1) (tau + &2) SUBSET apx_slab a b`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `apx_ts_mdl (psi:real^3->real^3) c kappa a b x1 tau` THEN
    REWRITE_TAC[apx_ts_mdl] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC APX_SLAB_SUBSET THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`psi:real^3->real^3`; `c:real`; `kappa:real`; `a:real`; `b:real`;
                 `x1:real^3`; `tau:real`; `v:real^3`] APX_TS_MDL_ALIGN) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_TAC] THEN
  REPEAT CONJ_TAC THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`apx_sval((psi:real^3->real^3) v)`; `c:real`; `kappa:real`; `&1 / &200`;
                   `apx_sval(v:real^3) - tau`; `&11 / &10 * (sqrt(&2) * log(&2))`]
                  APX_TS_ARITH_LO) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`apx_sval((psi:real^3->real^3) v)`; `c:real`; `kappa:real`; `&1 / &200`;
                   `apx_sval(v:real^3) - tau`; `&11 / &10 * (sqrt(&2) * log(&2)) + &1 / &20`]
                  APX_TS_ARITH_MID) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`apx_sval((psi:real^3->real^3) v)`; `c:real`; `kappa:real`; `&1 / &200`;
                   `apx_sval(v:real^3) - tau`; `&0`] APX_TS_ARITH_HI) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`apx_sval((psi:real^3->real^3) v)`; `c:real`; `kappa:real`; `&1 / &200`;
                   `apx_sval(v:real^3) - tau`; `&1`] APX_TS_ARITH_HI) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let APX_TS_SPLICE_BETWEEN = prove
 (`!(psi:real^3->real^3) w1 w2 D v.
        min (apx_sval v) (D - apx_sval(psi v)) <= apx_ts_splice psi w1 w2 D v /\
        apx_ts_splice psi w1 w2 D v <= max (apx_sval v) (D - apx_sval(psi v))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[apx_ts_splice] THEN
  MP_TAC(SPEC `(apx_sval(v:real^3) - w1) / (w2 - w1)` SMOOTH_STEP_BOUNDS) THEN
  ABBREV_TAC `x = smooth_step((apx_sval(v:real^3) - w1) / (w2 - w1))` THEN
  ABBREV_TAC `p = apx_sval(v:real^3)` THEN
  ABBREV_TAC `q = D - apx_sval((psi:real^3->real^3) v)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(&1 - x) * min p q <= (&1 - x) * p /\ x * min p q <= x * q /\
                (&1 - x) * p <= (&1 - x) * max p q /\ x * q <= x * max p q`
  MP_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let APX_TS_MDL_LEVELS = prove
 (`!(psi:real^3->real^3) c kappa a b x1 tau v.
        apx_ts_mdl psi c kappa a b x1 tau /\ v IN apx_slab (-- &1) (tau + &2)
        ==> let fv = apx_ts_splice psi (apx_ts_wa tau) (apx_ts_wb tau) (apx_ts_dd c tau) v in
            (fv = sqrt(&2) * log(&3 / &2) <=> apx_sval v = sqrt(&2) * log(&3 / &2)) /\
            (fv = apx_ts_dd c tau - sqrt(&2) * log(&2) <=>
             apx_sval(psi v) = sqrt(&2) * log(&2)) /\
            (fv = apx_ts_dd c tau <=> apx_sval(psi v) = &0) /\
            (&0 < fv <=> &0 < apx_sval v) /\ (&0 <= fv <=> &0 <= apx_sval v) /\
            (fv < apx_ts_dd c tau <=> &0 < apx_sval(psi v)) /\
            (fv <= apx_ts_dd c tau <=> &0 <= apx_sval(psi v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_TS_MDL_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_TS_MDL_TAU) THEN
  STRIP_ASSUME_TAC APX_TS_NUM THEN
  MP_TAC(ISPECL [`psi:real^3->real^3`; `c:real`; `kappa:real`; `a:real`; `b:real`;
                 `x1:real^3`; `tau:real`; `v:real^3`] APX_TS_MDL_EST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`psi:real^3->real^3`; `apx_ts_wa tau`; `apx_ts_wb tau`;
                 `apx_ts_dd c tau`; `v:real^3`] APX_TS_SPLICE_BETWEEN) THEN
  MP_TAC(ISPECL [`psi:real^3->real^3`; `apx_ts_wa tau`; `apx_ts_wb tau`;
                 `apx_ts_dd c tau`; `v:real^3`] APX_TS_SPLICE_ZONES) THEN
  ANTS_TAC THENL [REWRITE_TAC[apx_ts_wa] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `fv = apx_ts_splice (psi:real^3->real^3) (apx_ts_wa tau) (apx_ts_wb tau)
                    (apx_ts_dd c tau) v` THEN
  ABBREV_TAC `l2 = sqrt(&2) * log(&2)` THEN
  ABBREV_TAC `l32 = sqrt(&2) * log(&3 / &2)` THEN
  ABBREV_TAC `s = apx_sval(v:real^3)` THEN
  ABBREV_TAC `q = apx_sval((psi:real^3->real^3) v)` THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC)) THEN
  ASM_CASES_TAC `s <= apx_ts_wa tau` THENL
   [SUBGOAL_THEN `fv = s:real` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `l2 + &1 / &50 <= q` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      MAP_EVERY UNDISCH_TAC [`s <= apx_ts_wa tau`;
                             `apx_ts_wa tau = apx_ts_wb tau - &1 / &20`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`s <= apx_ts_wa tau`; `apx_ts_wa tau = apx_ts_wb tau - &1 / &20`;
      `apx_ts_wb tau = tau - &11 / &10 * l2`; `abs(apx_ts_dd c tau - tau) <= &1 / &500`;
      `&7 / &10 <= l2`; `l2 + &1 / &50 <= q`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `s < apx_ts_wb tau` THENL
   [SUBGOAL_THEN `l2 + &1 / &50 <= q /\ q <= &111 / &100 * l2 + &3 / &50`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      MAP_EVERY UNDISCH_TAC
       [`~(s <= apx_ts_wa tau)`; `s < apx_ts_wb tau`;
        `apx_ts_wb tau = tau - &11 / &10 * l2`; `&7 / &10 <= l2`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`~(s <= apx_ts_wa tau)`; `s < apx_ts_wb tau`;
      `apx_ts_wa tau = apx_ts_wb tau - &1 / &20`; `apx_ts_wb tau = tau - &11 / &10 * l2`;
      `l32 + &1 / &10 * l2 <= apx_ts_wa tau`; `abs(apx_ts_dd c tau - tau) <= &1 / &500`;
      `&7 / &10 <= l2`; `&0 < l32`; `l2 + &1 / &50 <= q`;
      `q <= &111 / &100 * l2 + &3 / &50`; `min s (apx_ts_dd c tau - q) <= fv`;
      `fv <= max s (apx_ts_dd c tau - q)`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `fv = apx_ts_dd c tau - q` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC `~(s < apx_ts_wb tau)` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `s <= tau` THENL
   [SUBGOAL_THEN `q <= &111 / &100 * l2 + &3 / &50` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      MAP_EVERY UNDISCH_TAC
       [`~(s < apx_ts_wb tau)`; `apx_ts_wa tau = apx_ts_wb tau - &1 / &20`; `s <= tau`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`~(s < apx_ts_wb tau)`; `apx_ts_wa tau = apx_ts_wb tau - &1 / &20`;
      `apx_ts_wb tau = tau - &11 / &10 * l2`; `l32 + &1 / &10 * l2 <= apx_ts_wa tau`;
      `abs(apx_ts_dd c tau - tau) <= &1 / &500`; `&7 / &10 <= l2`; `&0 < l32`;
      `q <= &111 / &100 * l2 + &3 / &50`] THEN
    REAL_ARITH_TAC;
    SUBGOAL_THEN `q <= &1 / &200` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC `~(s <= tau)` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`~(s <= tau)`; `abs(apx_ts_dd c tau - tau) <= &1 / &500`;
      `&19 / &10 * l2 <= tau`; `&7 / &10 <= l2`; `&0 < l32`; `l32 < l2`;
      `q <= &1 / &200`] THEN
    REAL_ARITH_TAC]);;

let APX_TS_MDL_SMOOTH = prove
 (`!(psi:real^3->real^3) c kappa a b x1 tau.
        apx_ts_mdl psi c kappa a b x1 tau
        ==> smooth_map_on (apx_slab (-- &1) (tau + &2))
              (\v. lift(apx_ts_splice psi (apx_ts_wa tau) (apx_ts_wb tau)
                                      (apx_ts_dd c tau) v))`,
  REWRITE_TAC[apx_ts_mdl] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `apx_slab (-- &1) (tau + &2) SUBSET apx_slab a b` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_SLAB_SUBSET THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC APX_TS_SPLICE_SMOOTH THEN
  REWRITE_TAC[apx_slab; OPEN_ANNULUS] THEN REWRITE_TAC[GSYM apx_slab] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `apx_slab a b:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `vec 0:real^3`)) (concl th) &&
        not(can (find_term (fun t -> t = `annulus (&1 / &2) (&2):real^3->bool`)) (concl th)))) THEN
      ASM SET_TAC[];
      UNDISCH_TAC `(v:real^3) IN apx_slab (-- &1) (tau + &2)` THEN SIMP_TAC[APX_SLAB_SVAL]]]);;

let APX_TS_MDL_COMPACT = prove
 (`!(psi:real^3->real^3) c kappa a b x1 tau alpha beta.
        apx_ts_mdl psi c kappa a b x1 tau /\ &0 <= alpha /\ beta <= apx_ts_dd c tau
        ==> compact {v | v IN apx_slab (-- &1) (tau + &2) /\
                         alpha <= apx_ts_splice psi (apx_ts_wa tau) (apx_ts_wb tau)
                                                (apx_ts_dd c tau) v /\
                         apx_ts_splice psi (apx_ts_wa tau) (apx_ts_wb tau)
                                       (apx_ts_dd c tau) v <= beta}`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `F0 = \v:real^3. apx_ts_splice psi (apx_ts_wa tau) (apx_ts_wb tau)
                                             (apx_ts_dd c tau) v` THEN
  SUBGOAL_THEN `!v:real^3. apx_ts_splice psi (apx_ts_wa tau) (apx_ts_wb tau)
                                         (apx_ts_dd c tau) v = F0 v`
  (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "F0" THEN REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `K0 = cball(vec 0:real^3,exp((tau + &1) / sqrt(&2))) DIFF
                   ball(vec 0,exp(&0 / sqrt(&2)))` THEN
  MP_TAC(SPECL [`&0`; `tau + &1`] APX_CSLAB) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `{v | v IN apx_slab (-- &1) (tau + &2) /\ alpha <= (F0:real^3->real) v /\ F0 v <= beta} =
    {v | v IN K0 /\ (\v. lift(F0 v)) v IN interval[lift alpha,lift beta]}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTERVAL_1; LIFT_DROP] THEN
    X_GEN_TAC `v:real^3` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[APX_SLAB_SVAL] THEN EQ_TAC THEN STRIP_TAC THENL
     [ALL_TAC; ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC] THEN
    SUBGOAL_THEN `(v:real^3) IN apx_slab (-- &1) (tau + &2)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[APX_SLAB_SVAL]; ALL_TAC] THEN
    MP_TAC(ISPECL [`psi:real^3->real^3`; `c:real`; `kappa:real`; `a:real`; `b:real`;
                   `x1:real^3`; `tau:real`; `v:real^3`] APX_TS_MDL_LEVELS) THEN
    MP_TAC(ISPECL [`psi:real^3->real^3`; `c:real`; `kappa:real`; `a:real`; `b:real`;
                   `x1:real^3`; `tau:real`; `v:real^3`] APX_TS_MDL_EST) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    EXPAND_TAC "F0" THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `alpha <= (F0:real^3->real) v` THEN UNDISCH_TAC `(F0:real^3->real) v <= beta` THEN
    EXPAND_TAC "F0" THEN REWRITE_TAC[] THEN
    ABBREV_TAC `fv = apx_ts_splice (psi:real^3->real^3) (apx_ts_wa tau) (apx_ts_wb tau)
                                   (apx_ts_dd c tau) v` THEN
    DISCH_TAC THEN DISCH_TAC THEN
    DISCH_THEN(fun est -> DISCH_THEN(fun lev ->
      let est4 = CONJUNCT2(CONJUNCT2(CONJUNCT2 est)) in
      let lev5 = CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2 lev)))) in
      let lev7 = CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2 lev))))) in
      ASSUME_TAC est4 THEN ASSUME_TAC lev5 THEN ASSUME_TAC lev7)) THEN
    SUBGOAL_THEN `&0 <= apx_sval(v:real^3)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(fun th -> if concl th = `&0 <= fv <=> &0 <= apx_sval(v:real^3)`
                              then REWRITE_TAC[GSYM th] else failwith "no") THEN
      MAP_EVERY UNDISCH_TAC [`alpha <= fv`; `&0 <= alpha`] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `apx_sval(v:real^3) <= tau + &1` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      SUBGOAL_THEN `apx_sval((psi:real^3->real^3) v) < &0` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          concl th = `tau + &1 <= apx_sval(v:real^3) ==> apx_sval((psi:real^3->real^3) v) < &0`)) THEN
        UNDISCH_TAC `tau + &1 < apx_sval(v:real^3)` THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th ->
        concl th = `fv <= apx_ts_dd c tau <=> &0 <= apx_sval((psi:real^3->real^3) v)`)) THEN
      MAP_EVERY UNDISCH_TAC [`apx_sval((psi:real^3->real^3) v) < &0`; `fv <= beta`;
                             `beta <= apx_ts_dd c tau`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CLOSED_IN_COMPACT THEN EXISTS_TAC `K0:real^3->bool` THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE THEN
  REWRITE_TAC[CLOSED_INTERVAL] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `apx_slab (-- &1) (tau + &2):real^3->bool` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN EXPAND_TAC "F0" THEN
    MATCH_MP_TAC APX_TS_MDL_SMOOTH THEN ASM_MESON_TAC[];
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `v:real^3` THEN ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let APX_TS_MDL_RADIAL = prove
 (`!(psi:real^3->real^3) c kappa a b x1 tau v t.
        apx_ts_mdl psi c kappa a b x1 tau /\ v IN apx_slab (-- &1) (tau + &2) /\
        &0 < apx_sval v /\ &0 < apx_sval(psi v) /\ &1 < t * norm v /\ t <= &1
        ==> t % v IN apx_slab (-- &1) (tau + &2) /\ &0 < apx_sval(t % v) /\
            &0 < apx_sval(psi(t % v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_TS_MDL_FACTS) THEN
  UNDISCH_TAC `apx_ts_mdl (psi:real^3->real^3) c kappa a b x1 tau` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[apx_ts_mdl] th)) THEN
  SUBGOAL_THEN `~(v:real^3 = vec 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[APX_SLAB_SVAL]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < norm(v:real^3)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `t * norm(v:real^3) <= &0` MP_TAC THENL
     [REWRITE_TAC[REAL_ARITH `x * y <= &0 <=> &0 <= --x * y`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < apx_sval(t % v:real^3) /\ apx_sval(t % v:real^3) <= apx_sval v`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[APX_SVAL_SCALE] THEN CONJ_TAC THENL
     [REWRITE_TAC[apx_sval] THEN
      SUBGOAL_THEN `sqrt(&2) * log t + sqrt(&2) * log(norm(v:real^3)) =
                    sqrt(&2) * log(t * norm v)` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN AP_TERM_TAC THEN
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC LOG_MUL THEN ASM_REWRITE_TAC[NORM_POS_LT];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH] THEN
      MATCH_MP_TAC LOG_POS_LT THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_ARITH `s * l + x <= x <=> &0 <= s * --l`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[SQRT_POS_LE; REAL_POS] THEN
      REWRITE_TAC[REAL_NEG_GE0] THEN
      SUBGOAL_THEN `log t <= log(&1)` MP_TAC THENL
       [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[]; REWRITE_TAC[LOG_1]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `t % v IN apx_slab (-- &1) (tau + &2)` ASSUME_TAC THENL
   [REWRITE_TAC[APX_SLAB_SVAL] THEN
    ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ] THEN
    UNDISCH_TAC `(v:real^3) IN apx_slab (-- &1) (tau + &2)` THEN
    REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `v:real^3` APX_POLAR) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `om = inv(norm v) % (v:real^3)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `t % v = exp(apx_sval(t % v:real^3) / sqrt(&2)) % om` SUBST1_TAC THENL
   [MP_TAC(SPEC `t % v:real^3` APX_POLAR) THEN
    ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ] THEN
    SUBGOAL_THEN `inv(norm(t % v)) % (t % v:real^3) = om` (fun th -> SIMP_TAC[th]) THEN
    EXPAND_TAC "om" THEN REWRITE_TAC[NORM_MUL; VECTOR_MUL_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`; REAL_INV_MUL] THEN
    SUBGOAL_THEN `~(t = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(apx_slab a b:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[apx_slab; OPEN_ANNULUS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`psi:real^3->real^3`; `apx_slab a b:real^3->bool`; `c:real`; `kappa:real`;
                 `-- &1`; `om:real^3`; `a:real`; `b:real`] APX_TS_RAY_DERIV_SG) THEN
  ASM_SIMP_TAC[APX_RAY_IN_SLAB] THEN DISCH_THEN(X_CHOOSE_TAC `f':real->real`) THEN
  ASM_CASES_TAC `apx_sval(t % v:real^3) = apx_sval(v:real^3)` THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `exp(apx_sval(v:real^3) / sqrt(&2)) % om = v` THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. apx_sval((psi:real^3->real^3)(exp(s / sqrt(&2)) % om))`;
                 `f':real->real`; `a:real`; `b:real`; `-- &1 * c:real`; `kappa:real`;
                 `apx_sval(t % v:real^3)`; `apx_sval(v:real^3)`] APX_1D_MVT_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `(v:real^3) IN apx_slab (-- &1) (tau + &2)` THEN
    REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(-- &1 * c + kappa) * (apx_sval(v:real^3) - apx_sval(t % v:real^3)) <= &0`
  MP_TAC THENL
   [REWRITE_TAC[REAL_ARITH `x * y <= &0 <=> &0 <= --x * y`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let APX_TS_MDL_ONTO = prove
 (`!(psi:real^3->real^3) c kappa a b x1 tau w.
        apx_ts_mdl psi c kappa a b x1 tau /\
        (!w. w IN annulus (&1 / &4) (&4) ==> ?v. v IN apx_slab a b /\ psi v = w) /\
        ~(w = vec 0) /\ -- &1 <= apx_sval w /\
        apx_sval w <= &21 / &20 * (sqrt(&2) * log(&2)) + &1 / &100
        ==> ?v. v IN apx_slab (-- &1) (tau + &2) /\ apx_ts_wb tau < apx_sval v /\
                psi v = w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_TS_MDL_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_TS_MDL_TAU) THEN
  STRIP_ASSUME_TAC APX_TS_NUM THEN
  SUBGOAL_THEN `(w:real^3) IN annulus (&1 / &4) (&4)` MP_TAC THENL
   [MP_TAC(SPECL [`&1 / &4`; `&4`] APX_TS_SLAB_LOG) THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `sqrt(&2) * log(&1 / &4) = --(&2 * (sqrt(&2) * log(&2))) /\
                  sqrt(&2) * log(&4) = &2 * (sqrt(&2) * log(&2))`
    (fun th -> REWRITE_TAC[th]) THENL
     [SUBGOAL_THEN `&4 = &2 pow 2 /\ &1 / &4 = inv(&2 pow 2)` (fun th -> REWRITE_TAC[th]) THENL
       [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
      SIMP_TAC[LOG_INV; LOG_POW; REAL_POW_LT; REAL_ARITH `&0 < &2`] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th o check (fun t ->
    is_forall(concl t) && can (find_term (fun x -> x = `annulus (&1 / &4) (&4):real^3->bool`))
    (concl t)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `v:real^3` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`psi:real^3->real^3`; `c:real`; `kappa:real`; `a:real`; `b:real`;
                 `x1:real^3`; `tau:real`; `v:real^3`] APX_TS_MDL_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[APX_SLAB_SVAL]; ASM_REAL_ARITH_TAC]);;

let APX_TS_MDL_REGULAR = prove
 (`!(psi:real^3->real^3) c kappa a b x1 tau Ds C v.
        apx_ts_mdl psi c kappa a b x1 tau /\
        (!t. (smooth_step has_real_derivative Ds t) (atreal t) /\ abs(Ds t) <= C) /\
        &0 <= C /\ kappa <= inv(&200 * (C + &1)) /\ abs(c - &1) <= inv(&200 * (C + &1)) /\
        v IN apx_slab (-- &1) (tau + &2)
        ==> ~(frechet_derivative
               (\v. lift(apx_ts_splice psi (apx_ts_wa tau) (apx_ts_wb tau)
                                       (apx_ts_dd c tau) v))
               (at v) = (\h. vec 0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC APX_TS_CTX_REGULAR THEN
  MAP_EVERY EXISTS_TAC
   [`apx_slab (-- &1) (tau + &2):real^3->bool`; `c:real`; `kappa:real`;
    `kappa * &2 + sqrt(&2) * pi * kappa + abs(&1 - c) / &20`; `C:real`; `Ds:real->real`] THEN
  CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
  MATCH_MP_TAC APX_TS_MDL_CTX THEN
  MAP_EVERY EXISTS_TAC [`a:real`; `b:real`; `x1:real^3`] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The tight shell at the manifold level, part 1.  Alignment of              *)
(* transition maps for small eps in the apx_ts_align form, deep levels of a *)
(* neck through a point of another neck, the hypotheses apx_tsh of the      *)
(* tight-shell statement, the sign of the level of the hypothesis point and *)
(* the exclusion of the increasing sign (the other cut sphere would meet    *)
(* the inner side of e_k).                                                  *)
(* ------------------------------------------------------------------------- *)

let APX_TS_SQRT_DEV = prove
 (`!q. &0 <= q ==> abs(sqrt q - &1) <= abs(q - &1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `q - &1 = (sqrt q - &1) * (sqrt q + &1)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ARITH `(a - &1) * (a + &1) = a * a - &1`] THEN
    ASM_SIMP_TAC[GSYM REAL_POW_2; SQRT_POW_2];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
  ASM_SIMP_TAC[SQRT_POS_LE; REAL_ARITH `&0 <= x ==> &1 <= abs(x + &1)`]);;

(* The transition alignment of two eps-necks for small eps, in the form of   *)
(* apx_ts_align, with |c - 1| and kappa below any K0 in (0,1].               *)

let APX_TS_ALIGN_HOLDS = prove
 (`!K0. &0 < K0 /\ K0 <= &1
        ==> ?eps1. &0 < eps1 /\
              !top atlas (g:A->real^3^3) eps x (e:real^3->A) x' e' (ei:A->real^3) v.
                 &0 < eps /\ eps <= eps1 /\ riemannian_metric atlas g /\
                 rfs_neck (top,atlas) g eps x e /\ rfs_neck (top,atlas) g eps x' e' /\
                 (!z. z IN rfs_neck_dom eps ==> ei(e z) = z) /\
                 v IN rfs_neck_dom eps /\ e' v IN IMAGE e (rfs_neck_dom eps)
                 ==> abs(sqrt(mfd_scalar atlas g x / mfd_scalar atlas g x') - &1) <= K0 /\
                     ?sg. (sg = &1 \/ sg = -- &1) /\
                          apx_ts_align (ei o e')
                            (sqrt(mfd_scalar atlas g x / mfd_scalar atlas g x')) K0 sg v`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `alpha1 = (K0 / &7) pow 2` THEN
  SUBGOAL_THEN `&0 < alpha1 /\ alpha1 <= &1 / &32 /\ &7 * sqrt alpha1 = K0 /\
                &4 * alpha1 <= K0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "alpha1" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_POW_DIV] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < &7 pow 2`] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV];
      SUBGOAL_THEN `sqrt((K0 / &7) pow 2) = K0 / &7` SUBST1_TAC THENL
       [MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      REWRITE_TAC[REAL_POW_DIV] THEN
      SUBGOAL_THEN `K0 pow 2 <= K0` MP_TAC THENL
       [REWRITE_TAC[REAL_POW_2] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `UNIV:A->bool` APX_NECK_CURV) THEN REWRITE_TAC[APX_NECK_CURV_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `alpha1:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n1"))) THEN
  ABBREV_TAC `eps1 = min eps2 alpha1` THEN
  SUBGOAL_THEN `&0 < eps1 /\ eps1 <= alpha1 /\ eps1 <= eps2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eps1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`alpha1:real`; `eps1:real`] (INST_TYPE [`:A`,`:A`] APX_TRANSITION_DERIV)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "n1" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
      `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    DISCH_THEN(LABEL_TAC "tr")] THEN
  EXISTS_TAC `eps1:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  USE_THEN "tr" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `g:A->real^3^3`; `eps:real`; `x:A`; `e:real^3->A`; `x':A`; `e':real^3->A`;
    `ei:A->real^3`; `v:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `sg:real`
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs(mfd_scalar atlas (g:A->real^3^3) x / mfd_scalar atlas g x' - &1)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC APX_TS_SQRT_DEV THEN
      SUBGOAL_THEN `&0 < mfd_scalar atlas (g:A->real^3^3) x /\ &0 < mfd_scalar atlas g x'`
      MP_TAC THENL
       [UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x (e:real^3->A)` THEN
        UNDISCH_TAC `rfs_neck (top,atlas) (g:A->real^3^3) eps x' (e':real^3->A)` THEN
        REWRITE_TAC[rfs_neck] THEN SIMP_TAC[];
        ALL_TAC] THEN
      SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE];
      ASM_REAL_ARITH_TAC];
    EXISTS_TAC `sg:real` THEN ASM_REWRITE_TAC[apx_ts_align; o_THM] THEN
    X_GEN_TAC `k:real^3` THEN FIRST_X_ASSUM(MP_TAC o SPEC `k:real^3`) THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[]]);;

let APX_TS_DEEP = prove
 (`!top atlas (g:A->real^3^3) eps x (e:real^3->A) x' e' z0 x0 K Tm.
        apx_ch_ctx top atlas g eps /\
        rfs_neck (top,atlas) g eps x e /\ rfs_neck (top,atlas) g eps x' e' /\
        z0 IN rfs_neck_dom eps /\ abs(apx_sval z0) <= K /\ x0 IN sphere(vec 0,&1) /\
        e' x0 = e z0 /\ &0 <= Tm /\ Tm < inv eps /\
        &101 / &100 * &3 / &2 * (Tm + &24 / &5) < &99 / &100 * (inv eps - K)
        ==> !v. v IN apx_slab (--Tm) Tm ==> e' v IN IMAGE e (rfs_neck_dom eps)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
  UNDISCH_TAC `apx_ch_ctx top atlas (g:A->real^3^3) eps` THEN
  REWRITE_TAC[apx_ch_ctx] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x0:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC APX_DEEP_LEVELS THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                        `g:A->real^3^3`; `x:A`; `x':A`; `z0:real^3`; `x0:real^3`; `K:real`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `v IN rfs_neck_dom eps /\ abs(apx_sval(v:real^3)) < Tm` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(v:real^3) IN apx_slab (--Tm) Tm` THEN
    REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `&3 / &2`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (concl th))) THEN
    MAP_EVERY EXISTS_TAC [`e:real^3->A`; `e':real^3->A`; `x0:real^3`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    FIRST_X_ASSUM(fun th -> if is_eq(concl th) && rand(concl th) = `(e:real^3->A) z0`
      then REWRITE_TAC[th] else failwith "no") THEN
    UNDISCH_TAC `(z0:real^3) IN rfs_neck_dom eps` THEN REWRITE_TAC[IN_IMAGE] THEN
    MESON_TAC[];
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `&101 / &100 * &3 / &2 * (Tm + &24 / &5)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC]);;

(* The hypotheses of the tight-shell statement, with the region data as     *)
(* apx_rg0.                                                                  *)

let apx_tsh = new_definition
 `apx_tsh (top:A topology,atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) (dl:real)
          (J:num->bool) (e:num->real^3->A) (P:A->bool) (j:num) (k:num) <=>
    apx_rg0 (top,atlas) g dl J e P /\ j IN J /\ k IN J /\ ~(j = k) /\
    ~DISJOINT (IMAGE (e k) (sphere(vec 0,&1)))
              (IMAGE (e j) (apx_slab (--inv(&64 * dl)) (inv(&64 * dl))))`;;

(* A cut sphere point is never on the inner side of a cut neck. *)

let APX_TS_NOT_INNER = prove
 (`!top atlas (g:A->real^3^3) dl J (e:num->real^3->A) P i m p.
        apx_rg0 (top,atlas) g dl J e P /\ i IN J /\ m IN J /\
        p IN IMAGE (e i) (sphere(vec 0,&1)) /\ p IN IMAGE (e m) (apx_slab (--inv dl) (&0))
        ==> F`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `dl:real`; `J:num->bool`; `e:num->real^3->A`; `P:A->bool`; `m:num`]
                APX_RG0_INNER) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(p:A) IN top closure_of P` (fun th -> MP_TAC th THEN ASM SET_TAC[]) THEN
  UNDISCH_TAC `apx_rg0 (top,atlas) (g:A->real^3^3) dl J (e:num->real^3->A) P` THEN
  REWRITE_TAC[apx_rg0] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN DISJ2_TAC THEN
  EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]);;

(* Two different cut spheres are disjoint. *)

let APX_TS_SPHERES_DISJOINT = prove
 (`!top atlas (g:A->real^3^3) dl J (e:num->real^3->A) P i m.
        apx_rg0 (top,atlas) g dl J e P /\ i IN J /\ m IN J /\ ~(i = m)
        ==> DISJOINT (IMAGE (e i) (sphere(vec 0,&1))) (IMAGE (e m) (sphere(vec 0,&1)))`,
  REWRITE_TAC[apx_rg0] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `m:num`] o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> t = `annulus (&1 / &2) (&2):real^3->bool`)) (concl th) &&
    not(can (find_term (fun t -> t = `annulus (&1) (&2):real^3->bool`)) (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `sphere(vec 0:real^3,&1) SUBSET annulus (&1 / &2) (&2)` MP_TAC THENL
   [REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    SET_TAC[]]);;

(* The level of the hypothesis point is positive. *)

let APX_TS_TAU1_POS = prove
 (`!top atlas (g:A->real^3^3) dl J (e:num->real^3->A) P j k x1 z1.
        apx_tsh (top,atlas) g dl J e P j k /\ norm x1 = &1 /\
        z1 IN rfs_neck_dom dl /\ e k x1 = e j z1
        ==> &0 < apx_sval z1`,
  REWRITE_TAC[apx_tsh] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN REWRITE_TAC[REAL_LE_LT] THEN STRIP_TAC THENL
   [MATCH_MP_TAC APX_TS_NOT_INNER THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `dl:real`; `J:num->bool`; `e:num->real^3->A`;
                          `P:A->bool`; `k:num`; `j:num`; `(e:num->real^3->A) j z1`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(e:num->real^3->A) k x1 = e j z1`)) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_SPHERE_0];
      MATCH_MP_TAC FUN_IN_IMAGE THEN
      UNDISCH_TAC `(z1:real^3) IN rfs_neck_dom dl` THEN
      REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[]];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `dl:real`; `J:num->bool`; `e:num->real^3->A`; `P:A->bool`; `k:num`; `j:num`]
                  APX_TS_SPHERES_DISJOINT) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `norm(z1:real^3) = &1` ASSUME_TAC THENL
     [UNDISCH_TAC `apx_sval(z1:real^3) = &0` THEN
      UNDISCH_TAC `(z1:real^3) IN rfs_neck_dom dl` THEN
      REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL; apx_sval] THEN STRIP_TAC THEN
      SUBGOAL_THEN `~(sqrt(&2) = &0)` ASSUME_TAC THENL
       [SIMP_TAC[SQRT_EQ_0; REAL_OF_NUM_EQ; ARITH]; ALL_TAC] THEN
      ASM_REWRITE_TAC[REAL_ENTIRE] THEN DISCH_TAC THEN
      MP_TAC(SPEC `norm(z1:real^3)` EXP_LOG) THEN ASM_REWRITE_TAC[NORM_POS_LT; REAL_EXP_0] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; NOT_FORALL_THM] THEN
    EXISTS_TAC `(e:num->real^3->A) k x1` THEN CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_SPHERE_0];
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_SPHERE_0]]]);;

let APX_TS_SVAL0 = prove
 (`!w:real^3. ~(w = vec 0) ==> (apx_sval w = &0 <=> norm w = &1)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL [ALL_TAC; SIMP_TAC[APX_SVAL_UNIT]] THEN
  REWRITE_TAC[apx_sval; REAL_ENTIRE] THEN
  SIMP_TAC[SQRT_EQ_0; REAL_OF_NUM_EQ; ARITH] THEN DISCH_TAC THEN
  MP_TAC(SPEC `norm(w:real^3)` EXP_LOG) THEN ASM_REWRITE_TAC[NORM_POS_LT; REAL_EXP_0] THEN
  MESON_TAC[]);;

(* The transferred level cannot increase outwards: otherwise the other cut   *)
(* sphere would meet the inner side of e_k.                                  *)

let APX_TS_SIGN_TOPO = prove
 (`!top atlas (g:A->real^3^3) dl J (e:num->real^3->A) P j k (ej:A->real^3) x1 c kappa Tm.
        apx_tsh (top,atlas) g dl J e P j k /\
        (!z. z IN rfs_neck_dom dl ==> ej(e j z) = z) /\
        (!v. v IN apx_slab (--Tm) Tm ==> e k v IN IMAGE (e j) (rfs_neck_dom dl)) /\
        smooth_map_on (apx_slab (--Tm) Tm) (ej o e k) /\
        (!v. v IN apx_slab (--Tm) Tm ==> ~((ej o e k) v = vec 0)) /\
        (!v. v IN apx_slab (--Tm) Tm ==> apx_ts_align (ej o e k) c kappa (&1) v) /\
        norm x1 = &1 /\ &0 < apx_sval((ej o e k) x1) /\
        &2 * apx_sval((ej o e k) x1) < Tm /\ Tm <= inv dl /\
        &0 <= kappa /\ kappa + &1 / &2 < c
        ==> F`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ABBREV_TAC `phi = (ej:A->real^3) o (e:num->real^3->A) k` THEN
  ABBREV_TAC `tau1 = apx_sval((phi:real^3->real^3) x1)` THEN
  SUBGOAL_THEN `open(apx_slab (--Tm) Tm:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[apx_slab; OPEN_ANNULUS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`phi:real^3->real^3`; `apx_slab (--Tm) Tm:real^3->bool`; `c:real`;
                 `kappa:real`; `&1`; `x1:real^3`; `--Tm`; `Tm:real`] APX_TS_RAY_DERIV_SG) THEN
  ASM_SIMP_TAC[APX_RAY_IN_SLAB] THEN DISCH_THEN(X_CHOOSE_TAC `f':real->real`) THEN
  ABBREV_TAC `gg = \t. apx_sval((phi:real^3->real^3)(exp(t / sqrt(&2)) % x1))` THEN
  SUBGOAL_THEN `(gg:real->real) (&0) = tau1` ASSUME_TAC THENL
   [EXPAND_TAC "gg" THEN EXPAND_TAC "tau1" THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_EXP_0; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gg:real->real) (--(&2 * tau1)) < &0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`gg:real->real`; `f':real->real`; `--Tm`; `Tm:real`; `&1 * c:real`;
                   `kappa:real`; `--(&2 * tau1)`; `&0`] APX_1D_MVT_BOUNDS) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `tau1 < (&1 * c - kappa) * (&0 - --(&2 * tau1))` MP_TAC THENL
     [REWRITE_TAC[REAL_ARITH `&0 - --(&2 * t) = &2 * t`; REAL_MUL_LID] THEN
      SUBGOAL_THEN `tau1 * &1 < tau1 * (&2 * (c - kappa))` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`gg:real->real`; `--(&2 * tau1)`; `&0`; `&0`] REAL_IVT_INCREASING) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC APX_1D_CONT THEN EXISTS_TAC `f':real->real` THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `f':real->real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `ts:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `ts < &0` ASSUME_TAC THENL
   [ASM_CASES_TAC `ts = &0` THENL
     [UNDISCH_TAC `(gg:real->real) ts = &0` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `vs = exp(ts / sqrt(&2)) % (x1:real^3)` THEN
  SUBGOAL_THEN `(vs:real^3) IN apx_slab (--Tm) Tm /\ vs IN apx_slab (--inv dl) (&0)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "vs" THEN ASM_SIMP_TAC[APX_RAY_IN_SLAB] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `norm((phi:real^3->real^3) vs) = &1` ASSUME_TAC THENL
   [MP_TAC(SPEC `(phi:real^3->real^3) vs` APX_TS_SVAL0) THEN ASM_SIMP_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `(gg:real->real) ts = &0` THEN EXPAND_TAC "gg" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:num->real^3->A) j ((phi:real^3->real^3) vs) = e k vs` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `vs:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (concl th) &&
      can (find_term (fun t -> t = `rfs_neck_dom dl`)) (concl th))) THEN
    ASM_REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    EXPAND_TAC "phi" THEN ASM_SIMP_TAC[o_THM];
    ALL_TAC] THEN
  MATCH_MP_TAC APX_TS_NOT_INNER THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                        `g:A->real^3^3`; `dl:real`; `J:num->bool`; `e:num->real^3->A`;
                        `P:A->bool`; `j:num`; `k:num`; `(e:num->real^3->A) k vs`] THEN
  UNDISCH_TAC `apx_tsh (top,atlas) (g:A->real^3^3) dl J (e:num->real^3->A) P j k` THEN
  REWRITE_TAC[apx_tsh] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `(e:num->real^3->A) j ((phi:real^3->real^3) vs) = e k vs`)) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_SPHERE_0];
    MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The tight shell at the manifold level, part 2: the scale                 *)
(* regime apx_tsr and the data APX_TS_DATA (inverses, the transition map    *)
(* phi = ej o e k in the coordinates of e_k with the model hypotheses, and   *)
(* phi onto the annulus(1/4,4) of e_j).                                      *)
(* ------------------------------------------------------------------------- *)

(* The scale regime of the tight shell: the chain context at dl and 2 dl,    *)
(* the section property of neck spheres at dl, and the transition alignment *)
(* of dl-necks with constant K0.                                            *)

let apx_tsr = new_definition
 `apx_tsr (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)
          (dl:real) (K0:real) <=>
    apx_ch_ctx top atlas g dl /\ apx_ch_ctx top atlas g (&2 * dl) /\
    apx_ch_more top atlas g dl /\ dl <= &1 / &1000 /\ &0 < K0 /\ K0 <= &1 / &1000 /\
    (!x (e:real^3->A) x' e' (ei:A->real^3) v.
        rfs_neck (top,atlas) g dl x e /\ rfs_neck (top,atlas) g dl x' e' /\
        (!z. z IN rfs_neck_dom dl ==> ei(e z) = z) /\
        v IN rfs_neck_dom dl /\ e' v IN IMAGE e (rfs_neck_dom dl)
        ==> abs(sqrt(mfd_scalar atlas g x / mfd_scalar atlas g x') - &1) <= K0 /\
            ?sg. (sg = &1 \/ sg = -- &1) /\
                 apx_ts_align (ei o e') (sqrt(mfd_scalar atlas g x / mfd_scalar atlas g x'))
                              K0 sg v)`;;

(* The data of the tight shell: the inverses of the two necks, the        *)
(* transition map phi = ej o e k on the slab of levels |s| < 1/(2 dl) with   *)
(* the model hypotheses (sign -1 by APX_TS_SIGN_TOPO, crossing level tau of  *)
(* S_j), and phi onto the annulus(1/4,4) of e_j (deep levels at scale 2 dl). *)

let APX_TS_DATA = prove
 (`!top atlas (g:A->real^3^3) dl J (e:num->real^3->A) P j k K0.
     apx_tsh (top,atlas) g dl J e P j k /\ apx_tsr top atlas g dl K0
     ==> ?ek ej xk xj x1 tau.
           rfs_neck (top,atlas) g dl xk (e k) /\ rfs_neck (top,atlas) g dl xj (e j) /\
           (!z. z IN rfs_neck_dom dl ==> ek(e k z) = z) /\
           (!z. z IN rfs_neck_dom dl ==> ej(e j z) = z) /\
           (!v. v IN apx_slab (--inv(&2 * dl)) (inv(&2 * dl))
                ==> e k v IN IMAGE (e j) (rfs_neck_dom dl)) /\
           apx_ts_mdl ((ej:A->real^3) o e k)
                      (sqrt(mfd_scalar atlas g xj / mfd_scalar atlas g xk)) K0
                      (--inv(&2 * dl)) (inv(&2 * dl)) x1 tau /\
           (!w. w IN annulus (&1 / &4) (&4)
                ==> ?v. v IN apx_slab (--inv(&2 * dl)) (inv(&2 * dl)) /\ (ej o e k) v = w)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "tsh") MP_TAC) THEN
  REWRITE_TAC[apx_tsr] THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  USE_THEN "tsh" (fun th -> MP_TAC th THEN REWRITE_TAC[apx_tsh] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "rg0") STRIP_ASSUME_TAC)) THEN
  USE_THEN "rg0" (fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[apx_rg0] th)) THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(j:num) IN J`) o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck")) (concl th) &&
    not(can (find_term (fun t -> t = `ei:A->real^3`)) (concl th)))) THEN
  DISCH_THEN(X_CHOOSE_TAC `xj:A`) THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(k:num) IN J`) o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_neck")) (concl th) &&
    not(can (find_term (fun t -> t = `ei:A->real^3`)) (concl th)))) THEN
  DISCH_THEN(X_CHOOSE_TAC `xk:A`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom dl`;
                 `(e:num->real^3->A) j`] MFD_PARAM_MAPS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ej:A->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom dl`;
                 `(e:num->real^3->A) k`] MFD_PARAM_MAPS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ek:A->real^3` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`ek:A->real^3`; `ej:A->real^3`; `xk:A`; `xj:A`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "DISJOINT")) (concl th))) THEN
  REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:A` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `x1:real^3` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `z1:real^3` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `x1:real^3` THEN
  SUBGOAL_THEN `inv(&64 * dl) <= inv dl` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(z1:real^3) IN rfs_neck_dom dl /\ abs(apx_sval z1) <= inv(&64 * dl) /\
                norm(x1:real^3) = &1 /\ (e:num->real^3->A) k x1 = e j z1`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[APX_SLAB_NECK_DOM] THEN
      MP_TAC(SPECL [`--inv(&64 * dl)`; `inv(&64 * dl)`; `--inv dl`; `inv dl`]
                   APX_SLAB_SUBSET) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
      UNDISCH_TAC `(z1:real^3) IN apx_slab (--inv(&64 * dl)) (inv(&64 * dl))` THEN
      REWRITE_TAC[APX_SLAB_SVAL] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `(x1:real^3) IN sphere(vec 0,&1)` THEN REWRITE_TAC[IN_SPHERE_0];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&500 <= inv(&2 * dl) /\ inv(&2 * dl) < inv dl /\ &0 < dl`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPECL [`&2 * dl`; `&1 / &500`] REAL_LE_INV2) THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC];
      CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v. v IN apx_slab (--inv(&2 * dl)) (inv(&2 * dl))
                    ==> (e:num->real^3->A) k v IN IMAGE (e j) (rfs_neck_dom dl)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APX_TS_DEEP THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `xj:A`; `xk:A`; `z1:real^3`; `x1:real^3`;
                          `inv(&64 * dl)`] THEN
    ASM_REWRITE_TAC[IN_SPHERE_0; ETA_AX] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_INV_MUL] THEN
    SUBGOAL_THEN `&500 <= inv(&2) * inv dl` MP_TAC THENL
     [ASM_REWRITE_TAC[GSYM REAL_INV_MUL]; ALL_TAC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM IN_IMAGE] THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Tm = inv(&2 * dl)` THEN
  ABBREV_TAC `phi = (ej:A->real^3) o (e:num->real^3->A) k` THEN
  ABBREV_TAC `c = sqrt(mfd_scalar atlas (g:A->real^3^3) xj / mfd_scalar atlas g xk)` THEN
  SUBGOAL_THEN `!v. v IN apx_slab (--Tm) Tm
                    ==> v IN rfs_neck_dom dl /\ (phi:real^3->real^3) v IN rfs_neck_dom dl /\
                        (e:num->real^3->A) j (phi v) = e k v /\ ~(phi v = vec 0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(v:real^3) IN rfs_neck_dom dl` ASSUME_TAC THENL
     [UNDISCH_TAC `(v:real^3) IN apx_slab (--Tm) Tm` THEN REWRITE_TAC[APX_SLAB_NECK_DOM] THEN
      MP_TAC(SPECL [`--Tm`; `Tm:real`; `--inv dl`; `inv dl`] APX_SLAB_SUBSET) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SET_TAC[]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `v:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `apx_slab (--Tm) Tm:real^3->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    EXPAND_TAC "phi" THEN ASM_SIMP_TAC[o_THM] THEN
    MP_TAC(SPEC `dl:real` APX_NECK_DOM_NONZERO) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (apx_slab (--Tm) Tm) (phi:real^3->real^3)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `rfs_neck_dom dl`; `rfs_neck_dom dl`; `(e:num->real^3->A) j`;
                   `(e:num->real^3->A) k`; `ej:A->real^3`] APX_PARAM_TRANSITION) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `{v | v IN rfs_neck_dom dl /\ (e:num->real^3->A) k v IN IMAGE (e j) (rfs_neck_dom dl)}` THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (concl th) &&
      can (find_term (fun t -> t = `apx_slab (--Tm) Tm:real^3->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(c - &1) <= K0 /\
                !v. v IN apx_slab (--Tm) Tm
                    ==> ?sg. (sg = &1 \/ sg = -- &1) /\ apx_ts_align phi c K0 sg v`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `!v. v IN apx_slab (--Tm) Tm
                      ==> abs(c - &1) <= K0 /\
                          ?sg. (sg = &1 \/ sg = -- &1) /\ apx_ts_align phi c K0 sg v`
    ASSUME_TAC THENL
     [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN MAP_EVERY EXPAND_TAC ["c"; "phi"] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `ei:A->real^3`)) (concl th))) THEN
      EXISTS_TAC `(e:num->real^3->A) j` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (concl th) &&
        can (find_term (fun t -> t = `apx_slab (--Tm) Tm:real^3->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `x1:real^3`) THEN
      SUBGOAL_THEN `(x1:real^3) IN apx_slab (--Tm) Tm` (fun th -> SIMP_TAC[th]) THEN
      REWRITE_TAC[APX_SLAB_SVAL] THEN
      SUBGOAL_THEN `~(x1:real^3 = vec 0)` ASSUME_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `norm(x1:real^3) = &1` THEN ASM_REWRITE_TAC[NORM_0] THEN
        REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[APX_SVAL_UNIT] THEN ASM_REAL_ARITH_TAC;
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:real^3->real^3) x1 = z1` ASSUME_TAC THENL
   [EXPAND_TAC "phi" THEN ASM_SIMP_TAC[o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < apx_sval(z1:real^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_TS_TAU1_POS THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `dl:real`; `J:num->bool`; `e:num->real^3->A`;
                          `P:A->bool`; `j:num`; `k:num`; `x1:real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + sqrt(&2) * pi) * K0 < c /\ K0 + &1 / &2 < c` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `sqrt(&2) * pi <= &24 / &5` MP_TAC THENL
     [SUBGOAL_THEN `sqrt(&2) <= &3 / &2 /\ pi <= &16 / &5` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV;
          MP_TAC PI_APPROX_32 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 / &2 * &16 / &5` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_POS; PI_POS_LE];
        CONV_TAC REAL_RAT_REDUCE_CONV];
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(&1 + sqrt(&2) * pi) * K0 <= (&1 + &24 / &5) * K0` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`phi:real^3->real^3`; `apx_slab (--Tm) Tm:real^3->bool`; `c:real`; `K0:real`;
                 `--Tm`; `Tm:real`] APX_TS_SIGN) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SUBSET_REFL] THEN REWRITE_TAC[apx_slab; OPEN_ANNULUS] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sg:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "al"))) THEN
  SUBGOAL_THEN `!v. v IN apx_slab (--Tm) Tm ==> ~((phi:real^3->real^3) v = vec 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * apx_sval(z1:real^3) < Tm` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&2 * inv(&64 * dl)` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "Tm" THEN REWRITE_TAC[REAL_INV_MUL] THEN
    SUBGOAL_THEN `&0 < inv dl` MP_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sg = -- &1` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN2 SUBST_ALL_TAC ACCEPT_TAC o check (fun th ->
      concl th = `sg = &1 \/ sg = -- &1`)) THEN
    MATCH_MP_TAC(TAUT `F ==> p`) THEN
    MATCH_MP_TAC APX_TS_SIGN_TOPO THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `dl:real`; `J:num->bool`; `e:num->real^3->A`;
                          `P:A->bool`; `j:num`; `k:num`; `ej:A->real^3`; `x1:real^3`;
                          `c:real`; `K0:real`; `Tm:real`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY(ASM_REAL_ARITH_TAC) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`phi:real^3->real^3`; `c:real`; `K0:real`; `--Tm`; `Tm:real`; `x1:real^3`]
                APX_TS_CROSS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tau:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `tau:real` THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `tau <= &2 * apx_sval(z1:real^3)` ASSUME_TAC THENL
   [UNDISCH_TAC `tau <= &2 * apx_sval((phi:real^3->real^3) x1)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[apx_ts_mdl] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `tau <= &2 * inv(&64 * dl)` MP_TAC THENL
       [UNDISCH_TAC `tau <= &2 * apx_sval((phi:real^3->real^3) x1)` THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      EXPAND_TAC "Tm" THEN REWRITE_TAC[REAL_INV_MUL] THEN
      SUBGOAL_THEN `&1000 <= inv dl` MP_TAC THENL
       [MP_TAC(SPECL [`dl:real`; `&1 / &1000`] REAL_LE_INV2) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC];
        CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC];
      X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `j:num`] o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `annulus (&1 / &2) (&2):real^3->bool`)) (concl th) &&
        not(can (find_term (fun t -> t = `annulus (&1) (&2):real^3->bool`)) (concl th)) &&
        not(can (find_term (fun t -> t = `phi:real^3->real^3`)) (concl th)))) THEN
      ASM_REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; NOT_FORALL_THM] THEN
      EXISTS_TAC `(e:num->real^3->A) k v` THEN CONJ_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        SUBGOAL_THEN `(e:num->real^3->A) k v = e j ((phi:real^3->real^3) v)` SUBST1_TAC THENL
         [ASM_MESON_TAC[]; MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]];
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `z0 = exp(tau / sqrt(&2)) % (x1:real^3)` THEN
  SUBGOAL_THEN `(z0:real^3) IN apx_slab (--Tm) Tm /\ apx_sval z0 = tau` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "z0" THEN ASM_SIMP_TAC[APX_RAY_IN_SLAB; APX_RAY_SVAL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm((phi:real^3->real^3) z0) = &1 /\ (e:num->real^3->A) j (phi z0) = e k z0`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPEC `(phi:real^3->real^3) z0` APX_TS_SVAL0) THEN ASM_SIMP_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_neck (top,atlas) (g:A->real^3^3) (&2 * dl) xk ((e:num->real^3->A) k) /\
                rfs_neck (top,atlas) (g:A->real^3^3) (&2 * dl) xj ((e:num->real^3->A) j)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC APX_NECK_MONO_GEN THEN EXISTS_TAC `dl:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_neck_dom (&2 * dl) = apx_slab (--Tm) Tm` ASSUME_TAC THENL
   [EXPAND_TAC "Tm" THEN REWRITE_TAC[APX_SLAB_NECK_DOM]; ALL_TAC] THEN
  SUBGOAL_THEN `!w. w IN apx_slab (-- &3) (&3)
                    ==> (e:num->real^3->A) j w IN IMAGE (e k) (rfs_neck_dom (&2 * dl))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APX_TS_DEEP THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `g:A->real^3^3`; `xk:A`; `xj:A`; `z0:real^3`;
                          `(phi:real^3->real^3) z0`; `tau:real`] THEN
    ASM_REWRITE_TAC[IN_SPHERE_0; ETA_AX] THEN
    SUBGOAL_THEN `tau <= &2 * inv(&64 * dl)` MP_TAC THENL
     [UNDISCH_TAC `tau <= &2 * apx_sval((phi:real^3->real^3) x1)` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&1000 <= inv dl` MP_TAC THENL
     [MP_TAC(SPECL [`dl:real`; `&1 / &1000`] REAL_LE_INV2) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `Tm = inv(&2) * inv dl` MP_TAC THENL
     [EXPAND_TAC "Tm" THEN REWRITE_TAC[REAL_INV_MUL]; ALL_TAC] THEN
    REWRITE_TAC[REAL_INV_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(w:real^3) IN apx_slab (-- &3) (&3) /\ w IN rfs_neck_dom dl` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `annulus (&1 / &4) (&4):real^3->bool =
                  apx_slab (sqrt(&2) * log(&1 / &4)) (sqrt(&2) * log(&4))` MP_TAC THENL
     [MATCH_MP_TAC APX_TS_SLAB_LOG THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `sqrt(&2) * log(&1 / &4) = --(&2 * (sqrt(&2) * log(&2))) /\
                  sqrt(&2) * log(&4) = &2 * (sqrt(&2) * log(&2))`
    (fun th -> REWRITE_TAC[th]) THENL
     [SUBGOAL_THEN `&4 = &2 pow 2 /\ &1 / &4 = inv(&2 pow 2)` (fun th -> REWRITE_TAC[th]) THENL
       [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
      SIMP_TAC[LOG_INV; LOG_POW; REAL_POW_LT; REAL_ARITH `&0 < &2`] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(fun th -> UNDISCH_TAC `(w:real^3) IN annulus (&1 / &4) (&4)` THEN
      REWRITE_TAC[th]) THEN
    STRIP_ASSUME_TAC APX_TS_NUM THEN REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&1000 <= inv dl` MP_TAC THENL
     [MP_TAC(SPECL [`dl:real`; `&1 / &1000`] REAL_LE_INV2) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> t = `apx_slab (-- &3) (&3):real^3->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `v:real^3` THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  EXPAND_TAC "phi" THEN REWRITE_TAC[o_THM] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(e:num->real^3->A) j w = e k v`)) THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The tight shell at the manifold level, part 3: the window                 *)
(* radial maps h0 = r |x|^(p-1) x and h1 = r |x|^(-p-1) x (levels and       *)
(* diffeomorphisms of annuli), nonvanishing derivatives of affine images,   *)
(* the model function apx_ts_F, the level function apx_ts_fm in M and the   *)
(* top level apx_ts_b, and the product APX_TS_PRODUCT (SMT_PRODUCT2 between *)
(* the sphere of radius 3/2 of e_k and the sphere of radius 2 of e_j).       *)
(* ------------------------------------------------------------------------- *)

(* Radial power maps: h0 r p x = r |x|^(p-1) x and h1 r p x = r |x|^(-p-1) x  *)
(* (the window charts of the product), their levels and diffeomorphisms.     *)

let apx_ts_h0 = new_definition
 `apx_ts_h0 (r:real) (p:real) (x:real^3) = r % (norm x rpow (p - &1) % x)`;;

let apx_ts_h1 = new_definition
 `apx_ts_h1 (r:real) (p:real) (x:real^3) =
    r % (inv(norm(norm x rpow (p - &1) % x) pow 2) % (norm x rpow (p - &1) % x))`;;

let APX_TS_SVAL_POW = prove
 (`!p x:real^3. ~(x = vec 0)
                ==> ~(norm x rpow (p - &1) % x = vec 0) /\
                    apx_sval(norm x rpow (p - &1) % x) = p * apx_sval x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[VECTOR_MUL_EQ_0; RPOW_POS_LT; NORM_POS_LT; REAL_LT_IMP_NZ];
    REWRITE_TAC[apx_sval] THEN ASM_SIMP_TAC[SMT_POWER_MAP_NORM] THEN
    ASM_SIMP_TAC[LOG_RPOW; NORM_POS_LT] THEN REAL_ARITH_TAC]);;

let APX_TS_H_LEVELS = prove
 (`!r p x:real^3.
        &0 < r /\ ~(x = vec 0)
        ==> ~(apx_ts_h0 r p x = vec 0) /\ ~(apx_ts_h1 r p x = vec 0) /\
            apx_sval(apx_ts_h0 r p x) = sqrt(&2) * log r + p * apx_sval x /\
            apx_sval(apx_ts_h1 r p x) = sqrt(&2) * log r - p * apx_sval x /\
            inv(norm(apx_ts_h0 r p x)) % apx_ts_h0 r p x = inv(norm x) % x /\
            inv(norm(apx_ts_h1 r p x)) % apx_ts_h1 r p x = inv(norm x) % x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:real`; `x:real^3`] APX_TS_SVAL_POW) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `y = norm(x:real^3) rpow (p - &1) % x` THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(inv(norm(y:real^3) pow 2) % y = vec 0) /\
                apx_sval(inv(norm(y:real^3) pow 2) % y) = --(p * apx_sval x)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[APX_SVAL_INVERSION] THEN
    ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0; REAL_POW_EQ_0; NORM_EQ_0] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[apx_ts_h0; apx_ts_h1] THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ; APX_SVAL_SCALE] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3 c. &0 < c ==> inv(norm(c % z)) % (c % z) = inv(norm z) % z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `z:real^3 = vec 0` THENL
     [ASM_REWRITE_TAC[VECTOR_MUL_RZERO]; ALL_TAC] THEN
    REWRITE_TAC[NORM_MUL; VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < c ==> abs c = c`; REAL_INV_MUL] THEN
    UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(x:real^3) rpow (p - &1) /\ &0 < inv(norm(y:real^3) pow 2)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RPOW_POS_LT; NORM_POS_LT; REAL_LT_INV_EQ; REAL_POW_LT]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[] THEN EXPAND_TAC "y" THEN ASM_SIMP_TAC[];
    ASM_SIMP_TAC[] THEN EXPAND_TAC "y" THEN ASM_SIMP_TAC[]]);;

let APX_TS_H0_DIFFEO = prove
 (`!r p r1 r2. &0 < r /\ &0 < p /\ &0 < r1 /\ r1 <= r2
               ==> ?h'. diffeomorphism_on (annulus r1 r2)
                          (annulus (r * r1 rpow p) (r * r2 rpow p)) (apx_ts_h0 r p) h'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:real`; `r1:real`; `r2:real`] (INST_TYPE [`:3`,`:N`] SMT_DIFFEO_POWER_ANNULUS)) THEN
  MP_TAC(ISPECL [`r:real`; `r1 rpow p`; `r2 rpow p`] (INST_TYPE [`:3`,`:N`] SMT_DIFFEO_SCALING_ANNULUS)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `(\x:real^3. norm x rpow (inv p - &1) % x) o (\x:real^3. inv r % x)` THEN
  SUBGOAL_THEN `apx_ts_h0 r p = (\x:real^3. r % x) o (\x. norm x rpow (p - &1) % x)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; apx_ts_h0]; ALL_TAC] THEN
  MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN
  EXISTS_TAC `annulus (r1 rpow p) (r2 rpow p):real^3->bool` THEN ASM_REWRITE_TAC[]);;

let APX_TS_H1_DIFFEO = prove
 (`!r p r1 r2. &0 < r /\ &0 < p /\ &0 < r1 /\ r1 <= r2
               ==> ?h'. diffeomorphism_on (annulus r1 r2)
                          (annulus (r * inv(r2 rpow p)) (r * inv(r1 rpow p)))
                          (apx_ts_h1 r p) h'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < r1 rpow p /\ r1 rpow p <= r2 rpow p` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RPOW_POS_LT] THEN MATCH_MP_TAC RPOW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:real`; `r1:real`; `r2:real`] (INST_TYPE [`:3`,`:N`] SMT_DIFFEO_POWER_ANNULUS)) THEN
  MP_TAC(ISPECL [`r1 rpow p`; `r2 rpow p`] (INST_TYPE [`:3`,`:N`] SMT_DIFFEO_INVERSION_ANNULUS)) THEN
  MP_TAC(ISPECL [`r:real`; `inv(r2 rpow p)`; `inv(r1 rpow p)`]
                (INST_TYPE [`:3`,`:N`] SMT_DIFFEO_SCALING_ANNULUS)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `((\x:real^3. norm x rpow (inv p - &1) % x) o
               (\x:real^3. inv(norm x pow 2) % x)) o (\x:real^3. inv r % x)` THEN
  SUBGOAL_THEN `apx_ts_h1 r p = (\x:real^3. r % x) o (\x:real^3. inv(norm x pow 2) % x) o
                                (\x. norm x rpow (p - &1) % x)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; apx_ts_h1]; ALL_TAC] THEN
  MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN
  EXISTS_TAC `annulus (inv(r2 rpow p)) (inv(r1 rpow p)):real^3->bool` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN
  EXISTS_TAC `annulus (r1 rpow p) (r2 rpow p):real^3->bool` THEN ASM_REWRITE_TAC[]);;

let APX_TS_NZ_AFFINE = prove
 (`!(H:real^3->real^1) (G:real^3->real^1) O a b v.
        open O /\ v IN O /\ (!z. z IN O ==> H z = a % G z + b) /\
        G differentiable (at v) /\ ~(a = &0) /\
        ~(frechet_derivative G (at v) = (\h. vec 0))
        ==> ~(frechet_derivative H (at v) = (\h. vec 0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `G' = frechet_derivative (G:real^3->real^1) (at v)` THEN
  SUBGOAL_THEN `((G:real^3->real^1) has_derivative G') (at v)` ASSUME_TAC THENL
   [EXPAND_TAC "G'" THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]; ALL_TAC] THEN
  SUBGOAL_THEN `((H:real^3->real^1) has_derivative (\h. a % (G':real^3->real^1) h)) (at v)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    EXISTS_TAC `\z. a % (G:real^3->real^1) z + b` THEN EXISTS_TAC `O:real^3->bool` THEN
    ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `(\h. a % (G':real^3->real^1) h) = (\h. a % G' h + vec 0)` SUBST1_TAC THENL
     [REWRITE_TAC[VECTOR_ADD_RID]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  UNDISCH_TAC `~((G':real^3->real^1) = (\h. vec 0))` THEN
  REWRITE_TAC[FUN_EQ_THM; VECTOR_MUL_EQ_0] THEN ASM_MESON_TAC[]);;

(* The model function, the product level function in M and the top level. *)

let apx_ts_F = new_definition
 `apx_ts_F (phi:real^3->real^3) (c:real) (tau:real) =
    apx_ts_splice phi (apx_ts_wa tau) (apx_ts_wb tau) (apx_ts_dd c tau)`;;

let apx_ts_fm = new_definition
 `apx_ts_fm (phi:real^3->real^3) (c:real) (tau:real) (ek:A->real^3) (p:A) =
    &20 * (apx_ts_F phi c tau (ek p) - sqrt(&2) * log(&3 / &2)) / sqrt(&2)`;;

let apx_ts_b = new_definition
 `apx_ts_b (c:real) (tau:real) =
    &20 * (apx_ts_dd c tau - sqrt(&2) * log(&2) - sqrt(&2) * log(&3 / &2)) / sqrt(&2)`;;

(* The product between the window spheres: SMT_PRODUCT2_STATEMENT for the  *)
(* level function fM = 20 (F o ek - l32) / sqrt 2 on e_k(W), with the window *)
(* charts e_k o h0 (radius 3/2, power 1/20) and e_j o h1 (radius 2).        *)

let APX_TS_PRODUCT = prove
 (`!top atlas (g:A->real^3^3) dl J (e:num->real^3->A) P j k K0 (ek:A->real^3) (ej:A->real^3)
    xk xj x1 tau Ds C.
     apx_tsh (top,atlas) g dl J e P j k /\ apx_tsr top atlas g dl K0 /\
     rfs_neck (top,atlas) g dl xk (e k) /\ rfs_neck (top,atlas) g dl xj (e j) /\
     (!z. z IN rfs_neck_dom dl ==> ek(e k z) = z) /\
     (!z. z IN rfs_neck_dom dl ==> ej(e j z) = z) /\
     (!v. v IN apx_slab (--inv(&2 * dl)) (inv(&2 * dl))
          ==> e k v IN IMAGE (e j) (rfs_neck_dom dl)) /\
     apx_ts_mdl (ej o e k) (sqrt(mfd_scalar atlas g xj / mfd_scalar atlas g xk)) K0
                (--inv(&2 * dl)) (inv(&2 * dl)) x1 tau /\
     (!w. w IN annulus (&1 / &4) (&4)
          ==> ?v. v IN apx_slab (--inv(&2 * dl)) (inv(&2 * dl)) /\ (ej o e k) v = w) /\
     (!t. (smooth_step has_real_derivative Ds t) (atreal t) /\ abs(Ds t) <= C) /\
     &0 <= C /\ K0 <= inv(&200 * (C + &1))
     ==> ?E0 gg gg'.
           mfd_param top atlas
             (annulus (&2 / &3)
               (&3 / &2 * exp(apx_ts_b (sqrt(mfd_scalar atlas g xj / mfd_scalar atlas g xk)) tau)))
             E0 /\
           sphere_diffeo gg gg' /\
           (!x. x IN annulus (&2 / &3) (&3 / &2)
                ==> E0 x = e k (apx_ts_h0 (&3 / &2) (&1 / &20) x)) /\
           (!x. x IN annulus
                  (&2 / &3 * exp(apx_ts_b (sqrt(mfd_scalar atlas g xj / mfd_scalar atlas g xk)) tau))
                  (&3 / &2 * exp(apx_ts_b (sqrt(mfd_scalar atlas g xj / mfd_scalar atlas g xk)) tau))
                ==> E0 x = e j (apx_ts_h1 (&2) (&1 / &20)
                     (radial_ext gg
                      (exp(--apx_ts_b (sqrt(mfd_scalar atlas g xj / mfd_scalar atlas g xk)) tau) % x)))) /\
           (!x. x IN annulus (&2 / &3)
                  (&3 / &2 * exp(apx_ts_b (sqrt(mfd_scalar atlas g xj / mfd_scalar atlas g xk)) tau))
                ==> apx_ts_fm (ej o e k) (sqrt(mfd_scalar atlas g xj / mfd_scalar atlas g xk)) tau ek
                      (E0 x) = log(norm x)) /\
           {p | p IN IMAGE (e k) (apx_slab (-- &1) (tau + &2)) /\
                &0 <= apx_ts_fm (ej o e k) (sqrt(mfd_scalar atlas g xj / mfd_scalar atlas g xk)) tau ek p /\
                apx_ts_fm (ej o e k) (sqrt(mfd_scalar atlas g xj / mfd_scalar atlas g xk)) tau ek p
                <= apx_ts_b (sqrt(mfd_scalar atlas g xj / mfd_scalar atlas g xk)) tau} =
           IMAGE E0 {x | &1 <= norm x /\
                         norm x <= exp(apx_ts_b (sqrt(mfd_scalar atlas g xj / mfd_scalar atlas g xk)) tau)}`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ABBREV_TAC `c = sqrt(mfd_scalar atlas (g:A->real^3^3) xj / mfd_scalar atlas g xk)` THEN
  ABBREV_TAC `Tm = inv(&2 * dl)` THEN
  ABBREV_TAC `phi = (ej:A->real^3) o (e:num->real^3->A) k` THEN
  ABBREV_TAC `W = apx_slab (-- &1) (tau + &2)` THEN
  ABBREV_TAC `bb = apx_ts_b c tau` THEN
  ABBREV_TAC `fM = apx_ts_fm (phi:real^3->real^3) c tau (ek:A->real^3)` THEN
  ABBREV_TAC `Fm = apx_ts_F (phi:real^3->real^3) c tau` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_TS_MDL_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_TS_MDL_TAU) THEN
  STRIP_ASSUME_TAC APX_TS_NUM THEN
  UNDISCH_TAC `apx_ts_mdl (phi:real^3->real^3) c K0 (--Tm) Tm x1 tau` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[apx_ts_mdl] th)) THEN
  UNDISCH_TAC `apx_tsr top atlas (g:A->real^3^3) dl K0` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[apx_tsr] th)) THEN
  SUBGOAL_THEN `&0 < dl /\ &1000 <= inv dl /\ Tm = inv(&2) * inv dl` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `apx_tsh (top,atlas) (g:A->real^3^3) dl J (e:num->real^3->A) P j k` THEN
    REWRITE_TAC[apx_tsh; apx_rg0] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`dl:real`; `&1 / &1000`] REAL_LE_INV2) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC];
      EXPAND_TAC "Tm" THEN REWRITE_TAC[REAL_INV_MUL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `W SUBSET apx_slab (--Tm) Tm /\ apx_slab (--Tm) Tm SUBSET rfs_neck_dom dl`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[APX_SLAB_NECK_DOM] THEN CONJ_TAC THEN
    MATCH_MP_TAC APX_SLAB_SUBSET THEN
    (SUBGOAL_THEN `Tm <= inv dl` MP_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!v. v IN W ==> (ek:A->real^3)((e:num->real^3->A) k v) = v /\
                               e k v = e j ((phi:real^3->real^3) v) /\
                               (fM:A->real) (e k v) =
                               &20 * ((Fm:real^3->real) v - sqrt(&2) * log(&3 / &2)) / sqrt(&2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(v:real^3) IN apx_slab (--Tm) Tm /\ v IN rfs_neck_dom dl` STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`(v:real^3) IN W`; `W SUBSET apx_slab (--Tm) Tm`;
                             `apx_slab (--Tm) Tm SUBSET rfs_neck_dom dl`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(ek:A->real^3)((e:num->real^3->A) k v) = v` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `v:real^3` o check (let tq1 = `apx_slab (--Tm) Tm:real^3->bool` in
         fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (concl th) &&
        can (find_term (fun t -> t = tq1)) (concl th))) THEN
      ASM_REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
      EXPAND_TAC "phi" THEN ASM_SIMP_TAC[o_THM];
      MAP_EVERY EXPAND_TAC ["fM"; "Fm"] THEN REWRITE_TAC[apx_ts_fm] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `annulus (&1 / &2) (&2):real^3->bool =
                apx_slab (--(sqrt(&2) * log(&2))) (sqrt(&2) * log(&2))` ASSUME_TAC THENL
   [MP_TAC(SPECL [`&1 / &2`; `&2`] APX_TS_SLAB_LOG) THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    SIMP_TAC[REAL_ARITH `&1 / &2 = inv(&2)`; LOG_INV; REAL_ARITH `&0 < &2`] THEN
    REWRITE_TAC[REAL_MUL_RNEG];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &3 / &2 /\ sqrt(&2) * log(&3 / &2) = sqrt(&2) * log(&3 / &2)`
  STRIP_ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN annulus (&1 / &2) (&2)
        ==> apx_ts_h0 (&3 / &2) (&1 / &20) x IN W /\
            apx_sval(apx_ts_h0 (&3 / &2) (&1 / &20) x) =
            sqrt(&2) * log(&3 / &2) + &1 / &20 * apx_sval x /\
            apx_sval(apx_ts_h0 (&3 / &2) (&1 / &20) x) <= apx_ts_wa tau /\
            (fM:A->real) ((e:num->real^3->A) k (apx_ts_h0 (&3 / &2) (&1 / &20) x)) =
            log(norm x)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN
    DISCH_THEN(MP_TAC o REWRITE_RULE[ASSUME `annulus (&1 / &2) (&2):real^3->bool =
                apx_slab (--(sqrt(&2) * log(&2))) (sqrt(&2) * log(&2))`; APX_SLAB_SVAL]) THEN
    STRIP_TAC THEN
    MP_TAC(SPECL [`&3 / &2`; `&1 / &20`; `x:real^3`] APX_TS_H_LEVELS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `apx_ts_h0 (&3 / &2) (&1 / &20) x IN W` ASSUME_TAC THENL
     [EXPAND_TAC "W" THEN ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `apx_sval(apx_ts_h0 (&3 / &2) (&1 / &20) x) <= apx_ts_wa tau` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `apx_ts_h0 (&3 / &2) (&1 / &20) x IN W`) o
      check (let tq1 = `fM:A->real` and tq2 = `ek:A->real^3` in fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = tq1)) (concl th) &&
      can (find_term (fun t -> t = tq2)) (concl th))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(Fm:real^3->real) (apx_ts_h0 (&3 / &2) (&1 / &20) x) =
                  sqrt(&2) * log(&3 / &2) + &1 / &20 * apx_sval x` SUBST1_TAC THENL
     [EXPAND_TAC "Fm" THEN REWRITE_TAC[apx_ts_F] THEN
      MP_TAC(ISPECL [`phi:real^3->real^3`; `apx_ts_wa tau`; `apx_ts_wb tau`;
                     `apx_ts_dd c tau`; `apx_ts_h0 (&3 / &2) (&1 / &20) x`]
                    APX_TS_SPLICE_ZONES) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[apx_sval] THEN
    SUBGOAL_THEN `~(sqrt(&2) = &0)` MP_TAC THENL
     [SIMP_TAC[SQRT_EQ_0; REAL_OF_NUM_EQ; ARITH]; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN annulus (&1 / &2) (&2)
        ==> ?v. v IN W /\ apx_ts_wb tau < apx_sval v /\
                (phi:real^3->real^3) v = apx_ts_h1 (&2) (&1 / &20) x /\
                (e:num->real^3->A) j (apx_ts_h1 (&2) (&1 / &20) x) = e k v /\
                (fM:A->real) (e k v) = bb + log(norm x)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN
    DISCH_THEN(MP_TAC o REWRITE_RULE[ASSUME `annulus (&1 / &2) (&2):real^3->bool =
                apx_slab (--(sqrt(&2) * log(&2))) (sqrt(&2) * log(&2))`; APX_SLAB_SVAL]) THEN
    STRIP_TAC THEN
    MP_TAC(SPECL [`&2`; `&1 / &20`; `x:real^3`] APX_TS_H_LEVELS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; STRIP_TAC] THEN
    MP_TAC(ISPECL [`phi:real^3->real^3`; `c:real`; `K0:real`; `--Tm`; `Tm:real`;
                   `x1:real^3`; `tau:real`; `apx_ts_h1 (&2) (&1 / &20) x`] APX_TS_MDL_ONTO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `v:real^3` THEN
    SUBGOAL_THEN `(v:real^3) IN W` ASSUME_TAC THENL
     [EXPAND_TAC "W" THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(v:real^3) IN W`) o check
      (let tq1 = `fM:A->real` and tq2 = `ek:A->real^3` in fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = tq1)) (concl th) &&
      can (find_term (fun t -> t = tq2)) (concl th))) THEN
    STRIP_TAC THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MESON_TAC[ASSUME `(e:num->real^3->A) k v = e j ((phi:real^3->real^3) v)`;
                ASSUME `(phi:real^3->real^3) v = apx_ts_h1 (&2) (&1 / &20) x`];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(Fm:real^3->real) v = apx_ts_dd c tau - apx_sval((phi:real^3->real^3) v)`
    SUBST1_TAC THENL
     [EXPAND_TAC "Fm" THEN REWRITE_TAC[apx_ts_F] THEN
      MP_TAC(ISPECL [`phi:real^3->real^3`; `apx_ts_wa tau`; `apx_ts_wb tau`;
                     `apx_ts_dd c tau`; `v:real^3`] APX_TS_SPLICE_ZONES) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "bb" THEN REWRITE_TAC[apx_ts_b; apx_sval] THEN
    SUBGOAL_THEN `~(sqrt(&2) = &0)` MP_TAC THENL
     [SIMP_TAC[SQRT_EQ_0; REAL_OF_NUM_EQ; ARITH]; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(W:real^3->bool) /\ W SUBSET rfs_neck_dom dl` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[apx_slab; OPEN_ANNULUS] THEN
    REWRITE_TAC[GSYM apx_slab] THEN
    MAP_EVERY UNDISCH_TAC [`apx_slab (-- &1) (tau + &2) = W`; `W SUBSET apx_slab (--Tm) Tm`;
                           `apx_slab (--Tm) Tm SUBSET rfs_neck_dom dl`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param top atlas (rfs_neck_dom dl) ((e:num->real^3->A) k) /\
                mfd_param top atlas (rfs_neck_dom dl) ((e:num->real^3->A) j) /\
                smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
                hausdorff_space (top:A topology)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `apx_tsh (top,atlas) (g:A->real^3^3) dl J (e:num->real^3->A) P j k` THEN
    REWRITE_TAC[apx_tsh; apx_rg0] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[rfs_neck;
              ASSUME `rfs_neck (top,atlas) (g:A->real^3^3) dl xk ((e:num->real^3->A) k)`;
              ASSUME `rfs_neck (top,atlas) (g:A->real^3^3) dl xj ((e:num->real^3->A) j)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on W (\v:real^3. lift((Fm:real^3->real) v))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`phi:real^3->real^3`; `c:real`; `K0:real`; `--Tm`; `Tm:real`;
                   `x1:real^3`; `tau:real`] APX_TS_MDL_SMOOTH) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["Fm"; "W"] THEN REWRITE_TAC[apx_ts_F];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (IMAGE ((e:num->real^3->A) k) W) /\
                mfd_param top atlas W ((e:num->real^3->A) k)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `mfd_param top atlas W ((e:num->real^3->A) k)` ASSUME_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `rfs_neck_dom dl` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN FIRST_ASSUM(MP_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_smooth_on (atlas:((A->bool)#(A->real^3))->bool) (IMAGE ((e:num->real^3->A) k) W) (\x. lift((fM:A->real) x))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC APX_MFD_SMOOTH_ON_PARAM THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `rfs_neck_dom dl`] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `\v:real^3. lift(&20 / sqrt(&2) * (Fm:real^3->real) v -
                               &20 * sqrt(&2) * log(&3 / &2) / sqrt(&2))` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM; LIFT_DROP] THEN
      AP_TERM_TAC THEN ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`W:real^3->bool`;
                   `\v:real^3. lift(&20 / sqrt(&2) * drop(lift((Fm:real^3->real) v)))`;
                   `\v:real^3. lift(&20 * sqrt(&2) * log(&3 / &2) / sqrt(&2))`]
                  SMOOTH_MAP_ON_LIFT_SUB) THEN
    REWRITE_TAC[LIFT_DROP; SMOOTH_MAP_ON_CONST] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`W:real^3->bool`; `&20 / sqrt(&2)`; `\v:real^3. lift((Fm:real^3->real) v)`]
                  SMOOTH_MAP_ON_LIFT_CMUL) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; REWRITE_TAC[LIFT_DROP]];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(c - &1) <= K0` ASSUME_TAC THENL
   [SUBGOAL_THEN `(x1:real^3) IN apx_slab (--Tm) Tm /\ x1 IN rfs_neck_dom dl`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(x1:real^3) IN apx_slab (--Tm) Tm` ASSUME_TAC THENL
       [REWRITE_TAC[APX_SLAB_SVAL] THEN
        SUBGOAL_THEN `~(x1:real^3 = vec 0)` ASSUME_TAC THENL
         [DISCH_TAC THEN UNDISCH_TAC `norm(x1:real^3) = &1` THEN
          ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
          ALL_TAC] THEN
        ASM_SIMP_TAC[APX_SVAL_UNIT] THEN ASM_REAL_ARITH_TAC;
        MAP_EVERY UNDISCH_TAC [`(x1:real^3) IN apx_slab (--Tm) Tm`;
                               `apx_slab (--Tm) Tm SUBSET rfs_neck_dom dl`] THEN
        SET_TAC[]];
      ALL_TAC] THEN
    EXPAND_TAC "c" THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`xj:A`; `(e:num->real^3->A) j`; `xk:A`;
      `(e:num->real^3->A) k`; `ej:A->real^3`; `x1:real^3`] o check (let tq1 = `ei:A->real^3` in
          fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = tq1)) (concl th))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (let tq1 = `apx_slab (--Tm) Tm:real^3->bool` in
          fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (concl th) &&
        can (find_term (fun t -> t = tq1)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(c - &1) <= inv(&200 * (C + &1))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K0:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_regular_on (atlas:((A->bool)#(A->real^3))->bool)
                  (IMAGE ((e:num->real^3->A) k) W) (fM:A->real)` ASSUME_TAC THENL
   [REWRITE_TAC[mfd_regular_on] THEN
    MAP_EVERY X_GEN_TAC [`ch:(A->bool)#(A->real^3)`; `q:A`] THEN
    REWRITE_TAC[IN_INTER] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MATCH_MP_TAC APX_MFD_REGULAR_AT_PARAM THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                          `W:real^3->bool`; `IMAGE ((e:num->real^3->A) k) W`] THEN
    ASM_REWRITE_TAC[IN_INTER] THEN
    CONJ_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC APX_TS_NZ_AFFINE THEN
    MAP_EVERY EXISTS_TAC [`\z:real^3. lift((Fm:real^3->real) z)`; `W:real^3->bool`;
                          `&20 / sqrt(&2)`;
                          `lift(--(&20 * sqrt(&2) * log(&3 / &2) / sqrt(&2)))`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(z:real^3) IN W`) o check
        (let tq1 = `fM:A->real` and tq2 = `ek:A->real^3` in fun th ->
        is_forall(concl th) && can (find_term (fun t -> t = tq1)) (concl th) &&
        can (find_term (fun t -> t = tq2)) (concl th))) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM LIFT_CMUL; GSYM LIFT_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `W:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN `~(sqrt(&2) = &0)` MP_TAC THENL
       [SIMP_TAC[SQRT_EQ_0; REAL_OF_NUM_EQ; ARITH]; CONV_TAC REAL_FIELD];
      MP_TAC(ISPECL [`phi:real^3->real^3`; `c:real`; `K0:real`; `--Tm`; `Tm:real`;
                     `x1:real^3`; `tau:real`; `Ds:real->real`; `C:real`; `v:real^3`]
                    APX_TS_MDL_REGULAR) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(v:real^3) IN W` THEN EXPAND_TAC "W" THEN
        SIMP_TAC[];
        ALL_TAC] THEN
      EXPAND_TAC "Fm" THEN REWRITE_TAC[apx_ts_F]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < bb` ASSUME_TAC THENL
   [EXPAND_TAC "bb" THEN REWRITE_TAC[apx_ts_b] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!v. v IN W
                    ==> (&0 <= (fM:A->real) ((e:num->real^3->A) k v) <=>
                         sqrt(&2) * log(&3 / &2) <= (Fm:real^3->real) v) /\
                        (fM ((e:num->real^3->A) k v) <= bb <=>
                         Fm v <= apx_ts_dd c tau - sqrt(&2) * log(&2)) /\
                        (fM ((e:num->real^3->A) k v) = &0 <=>
                         Fm v = sqrt(&2) * log(&3 / &2)) /\
                        (fM ((e:num->real^3->A) k v) = bb <=>
                         Fm v = apx_ts_dd c tau - sqrt(&2) * log(&2))`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(v:real^3) IN W`) o check
      (let tq1 = `fM:A->real` and tq2 = `ek:A->real^3` in fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = tq1)) (concl th) &&
      can (find_term (fun t -> t = tq2)) (concl th))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "bb" THEN REWRITE_TAC[apx_ts_b] THEN
    SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
     [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
    REWRITE_TAC[real_div] THEN
    ABBREV_TAC `q = inv(sqrt(&2))` THEN
    SUBGOAL_THEN `&0 < q` ASSUME_TAC THENL
     [EXPAND_TAC "q" THEN ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `&20 * x * q = (&20 * q) * x`] THEN
    SUBGOAL_THEN `&0 < &20 * q` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `m = &20 * q` THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_ARITH `&0 <= m * x <=> &0 <= x * m`] THEN
    ASM_SIMP_TAC[REAL_LE_MUL_EQ; REAL_LE_LMUL_EQ; REAL_EQ_MUL_LCANCEL;
                 REAL_LT_IMP_NZ; REAL_ENTIRE] THEN
    REWRITE_TAC[GSYM REAL_SUB_LDISTRIB] THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_EQ_MUL_LCANCEL; REAL_LT_IMP_NZ] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `compact_in top {p | p IN IMAGE ((e:num->real^3->A) k) W /\
                                    &0 <= (fM:A->real) p /\ fM p <= bb}`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `{p | p IN IMAGE ((e:num->real^3->A) k) W /\ &0 <= (fM:A->real) p /\ fM p <= bb} =
                  IMAGE (e k) {v | v IN W /\ sqrt(&2) * log(&3 / &2) <= (Fm:real^3->real) v /\
                                   Fm v <= apx_ts_dd c tau - sqrt(&2) * log(&2)}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN X_GEN_TAC `p:A` THEN EQ_TAC THENL
       [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) MP_TAC) THEN
        FIRST_X_ASSUM SUBST_ALL_TAC THEN
        FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(v:real^3) IN W`) o check
          (let tq1 = `bb:real` and tq2 = `Fm:real^3->real` in fun th ->
          is_forall(concl th) && can (find_term (fun t -> t = tq1)) (concl th) &&
          can (find_term (fun t -> t = tq2)) (concl th))) THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC `v:real^3` THEN
        ASM_REWRITE_TAC[];
        DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
        FIRST_X_ASSUM SUBST_ALL_TAC THEN
        FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(v:real^3) IN W`) o check
          (let tq1 = `bb:real` and tq2 = `Fm:real^3->real` in fun th ->
          is_forall(concl th) && can (find_term (fun t -> t = tq1)) (concl th) &&
          can (find_term (fun t -> t = tq2)) (concl th))) THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `v:real^3` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `W:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    MP_TAC(ISPECL [`phi:real^3->real^3`; `c:real`; `K0:real`; `--Tm`; `Tm:real`;
                   `x1:real^3`; `tau:real`; `sqrt(&2) * log(&3 / &2)`;
                   `apx_ts_dd c tau - sqrt(&2) * log(&2)`] APX_TS_MDL_COMPACT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["Fm"; "W"] THEN REWRITE_TAC[apx_ts_F];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_neck_chart top atlas ((e:num->real^3->A) k o apx_ts_h0 (&3 / &2) (&1 / &20)) /\
                mfd_neck_chart top atlas ((e:num->real^3->A) j o apx_ts_h1 (&2) (&1 / &20))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[mfd_neck_chart] THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`&3 / &2`; `&1 / &20`; `&1 / &2`; `&2`] APX_TS_H0_DIFFEO) THEN
      ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_TAC `h':real^3->real^3`) THEN
      MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
      MAP_EVERY EXISTS_TAC [`W:real^3->bool`;
        `annulus (&3 / &2 * (&1 / &2) rpow (&1 / &20)) (&3 / &2 * &2 rpow (&1 / &20)):real^3->bool`;
        `h':real^3->real^3`] THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
        REWRITE_RULE[diffeomorphism_on]) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
      MP_TAC(SPECL [`&2`; `&1 / &20`; `&1 / &2`; `&2`] APX_TS_H1_DIFFEO) THEN
      ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_TAC `h':real^3->real^3`) THEN
      MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
      MAP_EVERY EXISTS_TAC [`rfs_neck_dom dl`;
        `annulus (&2 * inv(&2 rpow (&1 / &20))) (&2 * inv((&1 / &2) rpow (&1 / &20))):real^3->bool`;
        `h':real^3->real^3`] THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
        REWRITE_RULE[diffeomorphism_on]) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN
      DISCH_THEN(MP_TAC o REWRITE_RULE[ASSUME `annulus (&1 / &2) (&2):real^3->bool =
                apx_slab (--(sqrt(&2) * log(&2))) (sqrt(&2) * log(&2))`; APX_SLAB_SVAL]) THEN
      STRIP_TAC THEN
      MP_TAC(SPECL [`&2`; `&1 / &20`; `x:real^3`] APX_TS_H_LEVELS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; STRIP_TAC] THEN
      ASM_REWRITE_TAC[APX_SLAB_NECK_DOM; APX_SLAB_SVAL] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE ((e:num->real^3->A) k o apx_ts_h0 (&3 / &2) (&1 / &20)) (annulus (&1 / &2) (&2))
    SUBSET IMAGE (e k) W /\
    IMAGE ((e:num->real^3->A) j o apx_ts_h1 (&2) (&1 / &20)) (annulus (&1 / &2) (&2))
    SUBSET IMAGE (e k) W /\
    DISJOINT (IMAGE ((e:num->real^3->A) k o apx_ts_h0 (&3 / &2) (&1 / &20))
                    (annulus (&1 / &2) (&2)))
             (IMAGE ((e:num->real^3->A) j o apx_ts_h1 (&2) (&1 / &20))
                    (annulus (&1 / &2) (&2))) /\
    (!x. x IN annulus (&1 / &2) (&2)
         ==> (fM:A->real) (((e:num->real^3->A) k o apx_ts_h0 (&3 / &2) (&1 / &20)) x) =
             &0 + log(norm x)) /\
    (!x. x IN annulus (&1 / &2) (&2)
         ==> (fM:A->real) (((e:num->real^3->A) j o apx_ts_h1 (&2) (&1 / &20)) x) =
             bb + log(norm x))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM; REAL_ADD_LID] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_SIMP_TAC[];
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN annulus (&1 / &2) (&2)`) o
        check (let tq1 = `apx_ts_h1 (&2) (&1 / &20)` and tq2 = `bb:real` in
            fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = tq1)) (concl th) &&
        can (find_term (fun t -> t = tq2)) (concl th))) THEN
      DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE; o_THM] THEN
      X_GEN_TAC `p:A` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC)
        (X_CHOOSE_THEN `x':real^3` STRIP_ASSUME_TAC)) THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(x':real^3) IN annulus (&1 / &2) (&2)`) o
        check (let tq1 = `apx_ts_h1 (&2) (&1 / &20)` and tq2 = `bb:real` in
            fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = tq1)) (concl th) &&
        can (find_term (fun t -> t = tq2)) (concl th))) THEN
      DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
      FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN annulus (&1 / &2) (&2)`) o
        check (let tq1 = `apx_ts_h0 (&3 / &2) (&1 / &20)` in fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = tq1)) (concl th))) THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `apx_ts_h0 (&3 / &2) (&1 / &20) x = v` MP_TAC THENL
       [MATCH_MP_TAC MFD_PARAM_INJ THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                              `W:real^3->bool`; `(e:num->real^3->A) k`] THEN
        ASM_REWRITE_TAC[] THEN
        MESON_TAC[ASSUME `p:A = (e:num->real^3->A) k (apx_ts_h0 (&3 / &2) (&1 / &20) x)`;
                  ASSUME `p:A = (e:num->real^3->A) j (apx_ts_h1 (&2) (&1 / &20) x')`;
                  ASSUME `(e:num->real^3->A) j (apx_ts_h1 (&2) (&1 / &20) x') = e k v`];
        DISCH_TAC THEN
        UNDISCH_TAC `apx_sval(apx_ts_h0 (&3 / &2) (&1 / &20) x) <= apx_ts_wa tau` THEN
        FIRST_X_ASSUM(let tq1 = `apx_ts_h0 (&3 / &2) (&1 / &20) x = v` in
            fun th -> if concl th = tq1
                                then REWRITE_TAC[th] else failwith "no") THEN
        UNDISCH_TAC `apx_ts_wb tau < apx_sval(v:real^3)` THEN
        UNDISCH_TAC `apx_ts_wa tau = apx_ts_wb tau - &1 / &20` THEN
        REAL_ARITH_TAC];
      ASM_SIMP_TAC[];
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN annulus (&1 / &2) (&2)`) o
        check (let tq1 = `apx_ts_h1 (&2) (&1 / &20)` and tq2 = `bb:real` in
            fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = tq1)) (concl th) &&
        can (find_term (fun t -> t = tq2)) (concl th))) THEN
      DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sphere(vec 0:real^3,&1) SUBSET annulus (&1 / &2) (&2) /\
                (!u:real^3. norm u = &1
                   ==> apx_ts_h0 (&3 / &2) (&1 / &20) u = &3 / &2 % u /\
                       apx_ts_h1 (&2) (&1 / &20) u = &2 % u)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[apx_ts_h0; apx_ts_h1; RPOW_ONE] THEN
      REWRITE_TAC[VECTOR_MUL_LID] THEN
      ASM_REWRITE_TAC[REAL_POW_ONE; REAL_INV_1; VECTOR_MUL_LID]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{p | p IN IMAGE ((e:num->real^3->A) k) W /\ (fM:A->real) p = &0} =
    IMAGE (e k o apx_ts_h0 (&3 / &2) (&1 / &20)) (sphere(vec 0,&1))`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; o_THM; IN_SPHERE_0] THEN
    X_GEN_TAC `p:A` THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) MP_TAC) THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(v:real^3) IN W`) o check
        (let tq1 = `bb:real` and tq2 = `Fm:real^3->real` in fun th ->
        is_forall(concl th) && can (find_term (fun t -> t = tq1)) (concl th) &&
        can (find_term (fun t -> t = tq2)) (concl th))) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`phi:real^3->real^3`; `c:real`; `K0:real`; `--Tm`; `Tm:real`;
                     `x1:real^3`; `tau:real`; `v:real^3`] APX_TS_MDL_LEVELS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN EXPAND_TAC "W" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      SUBGOAL_THEN `apx_ts_splice (phi:real^3->real^3) (apx_ts_wa tau) (apx_ts_wb tau)
                      (apx_ts_dd c tau) v = (Fm:real^3->real) v` SUBST1_TAC THENL
       [EXPAND_TAC "Fm" THEN REWRITE_TAC[apx_ts_F]; ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(v:real^3 = vec 0)` ASSUME_TAC THENL
       [UNDISCH_TAC `(v:real^3) IN W` THEN EXPAND_TAC "W" THEN SIMP_TAC[APX_SLAB_SVAL];
        ALL_TAC] THEN
      EXISTS_TAC `inv(norm v) % (v:real^3)` THEN
      MP_TAC(SPEC `v:real^3` APX_POLAR) THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `exp((sqrt(&2) * log(&3 / &2)) / sqrt(&2)) = &3 / &2`
      (fun th -> REWRITE_TAC[th]) THENL
       [SUBGOAL_THEN `~(sqrt(&2) = &0)` ASSUME_TAC THENL
         [SIMP_TAC[SQRT_EQ_0; REAL_OF_NUM_EQ; ARITH]; ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_FIELD `~(s = &0) ==> (s * x) / s = x`] THEN
        MATCH_MP_TAC EXP_LOG THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      STRIP_TAC THEN ASM_SIMP_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `w9:real^3` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
      SUBGOAL_THEN `(w9:real^3) IN annulus (&1 / &2) (&2)` ASSUME_TAC THENL
       [UNDISCH_TAC `sphere(vec 0:real^3,&1) SUBSET annulus (&1 / &2) (&2)` THEN
        REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(w9:real^3) IN annulus (&1 / &2) (&2)`) o
        check (let tq1 = `apx_ts_h0 (&3 / &2) (&1 / &20)` and tq2 = `W:real^3->bool` in
            fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = tq1)) (concl th) &&
        can (find_term (fun t -> t = tq2)) (concl th))) THEN
      STRIP_TAC THEN CONJ_TAC THENL
       [EXISTS_TAC `apx_ts_h0 (&3 / &2) (&1 / &20) w9` THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[LOG_1]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{p | p IN IMAGE ((e:num->real^3->A) k) W /\ (fM:A->real) p = bb} =
    IMAGE (e j o apx_ts_h1 (&2) (&1 / &20)) (sphere(vec 0,&1))`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; o_THM; IN_SPHERE_0] THEN
    X_GEN_TAC `p:A` THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) MP_TAC) THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(v:real^3) IN W`) o check
        (let tq1 = `bb:real` and tq2 = `Fm:real^3->real` in fun th ->
        is_forall(concl th) && can (find_term (fun t -> t = tq1)) (concl th) &&
        can (find_term (fun t -> t = tq2)) (concl th))) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`phi:real^3->real^3`; `c:real`; `K0:real`; `--Tm`; `Tm:real`;
                     `x1:real^3`; `tau:real`; `v:real^3`] APX_TS_MDL_LEVELS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN EXPAND_TAC "W" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      SUBGOAL_THEN `apx_ts_splice (phi:real^3->real^3) (apx_ts_wa tau) (apx_ts_wb tau)
                      (apx_ts_dd c tau) v = (Fm:real^3->real) v` SUBST1_TAC THENL
       [EXPAND_TAC "Fm" THEN REWRITE_TAC[apx_ts_F]; ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `~((phi:real^3->real^3) v = vec 0)` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check
         (let tq1 = `vec 0:real^3` and tq2 = `phi:real^3->real^3` and tq3 = `annulus (&1 / &2) (&2):real^3->bool` in
           fun th -> is_forall(concl th) &&
          can (find_term (fun t -> t = tq1)) (concl th) &&
          can (find_term (fun t -> t = tq2)) (concl th) &&
          not(can (find_term (fun t -> t = tq3)) (concl th)))) THEN
        UNDISCH_TAC `(v:real^3) IN W` THEN UNDISCH_TAC `W SUBSET apx_slab (--Tm) Tm` THEN
        SET_TAC[];
        ALL_TAC] THEN
      EXISTS_TAC `inv(norm((phi:real^3->real^3) v)) % phi v` THEN
      MP_TAC(SPEC `(phi:real^3->real^3) v` APX_POLAR) THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `exp((sqrt(&2) * log(&2)) / sqrt(&2)) = &2`
      (fun th -> REWRITE_TAC[th]) THENL
       [SUBGOAL_THEN `~(sqrt(&2) = &0)` ASSUME_TAC THENL
         [SIMP_TAC[SQRT_EQ_0; REAL_OF_NUM_EQ; ARITH]; ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_FIELD `~(s = &0) ==> (s * x) / s = x`] THEN
        MATCH_MP_TAC EXP_LOG THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      STRIP_TAC THEN ASM_SIMP_TAC[] THEN
      FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(v:real^3) IN W`) o check
        (let tq1 = `fM:A->real` and tq2 = `ek:A->real^3` in fun th ->
        is_forall(concl th) && can (find_term (fun t -> t = tq1)) (concl th) &&
        can (find_term (fun t -> t = tq2)) (concl th))) THEN
      SIMP_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `w9:real^3` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
      SUBGOAL_THEN `(w9:real^3) IN annulus (&1 / &2) (&2)` ASSUME_TAC THENL
       [UNDISCH_TAC `sphere(vec 0:real^3,&1) SUBSET annulus (&1 / &2) (&2)` THEN
        REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(w9:real^3) IN annulus (&1 / &2) (&2)`) o
        check (let tq1 = `apx_ts_h1 (&2) (&1 / &20)` and tq2 = `W:real^3->bool` in
            fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = tq1)) (concl th) &&
        can (find_term (fun t -> t = tq2)) (concl th))) THEN
      DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[LOG_1; REAL_ADD_RID] THEN EXISTS_TAC `v:real^3` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                `IMAGE ((e:num->real^3->A) k) W`; `fM:A->real`;
                `(e:num->real^3->A) k o apx_ts_h0 (&3 / &2) (&1 / &20)`;
                `(e:num->real^3->A) j o apx_ts_h1 (&2) (&1 / &20)`; `&0`; `bb:real`]
               (REWRITE_RULE[SMT_PRODUCT2_STATEMENT] (ISPEC `UNIV:A->bool` SMT_PRODUCT2))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_RZERO; REAL_SUB_LZERO; REAL_ADD_LID; o_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `E0:real^3->A` (X_CHOOSE_THEN `gg:real^3->real^3`
    (X_CHOOSE_THEN `gg':real^3->real^3` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`E0:real^3->A`; `gg:real^3->real^3`; `gg':real^3->real^3`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The tight shell at the manifold level, part 4: the gluing.               *)
(* Zones of the splice by value, vector equality by level and direction,   *)
(* the far piece x -> e((L / |x|) gg(x / |x|)), gluing two parametrized     *)
(* slabs with a common level function, the window map on slabs, and the    *)
(* far end of the product in radial form.                                  *)
(* ------------------------------------------------------------------------- *)

(* Low values of the splice are in zone A, high values in zone B. *)

let APX_TS_MDL_ZONEF = prove
 (`!(psi:real^3->real^3) c kappa a b x1 tau v.
        apx_ts_mdl psi c kappa a b x1 tau /\ v IN apx_slab (-- &1) (tau + &2)
        ==> (apx_ts_splice psi (apx_ts_wa tau) (apx_ts_wb tau) (apx_ts_dd c tau) v
             <= sqrt(&2) * log(&3 / &2)
             ==> apx_sval v <= apx_ts_wa tau) /\
            (apx_ts_dd c tau - sqrt(&2) * log(&2) <=
             apx_ts_splice psi (apx_ts_wa tau) (apx_ts_wb tau) (apx_ts_dd c tau) v
             ==> apx_ts_wb tau <= apx_sval v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_TS_MDL_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_TS_MDL_TAU) THEN
  STRIP_ASSUME_TAC APX_TS_NUM THEN
  MP_TAC(ISPECL [`psi:real^3->real^3`; `c:real`; `kappa:real`; `a:real`; `b:real`;
                 `x1:real^3`; `tau:real`; `v:real^3`] APX_TS_MDL_EST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`psi:real^3->real^3`; `apx_ts_wa tau`; `apx_ts_wb tau`;
                 `apx_ts_dd c tau`; `v:real^3`] APX_TS_SPLICE_BETWEEN) THEN
  MP_TAC(ISPECL [`psi:real^3->real^3`; `apx_ts_wa tau`; `apx_ts_wb tau`;
                 `apx_ts_dd c tau`; `v:real^3`] APX_TS_SPLICE_ZONES) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `fv = apx_ts_splice (psi:real^3->real^3) (apx_ts_wa tau) (apx_ts_wb tau)
                     (apx_ts_dd c tau) v` THEN
  ABBREV_TAC `l2 = sqrt(&2) * log(&2)` THEN
  ABBREV_TAC `l32 = sqrt(&2) * log(&3 / &2)` THEN
  ABBREV_TAC `s = apx_sval(v:real^3)` THEN
  ABBREV_TAC `q = apx_sval((psi:real^3->real^3) v)` THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC)) THEN
  ASM_CASES_TAC `s <= apx_ts_wa tau` THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `fv = s:real` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `s < apx_ts_wb tau` THENL
   [SUBGOAL_THEN `l2 + &1 / &50 <= q /\ q <= &111 / &100 * l2 + &3 / &50`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `fv = apx_ts_dd c tau - q` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `s <= tau` THENL
   [SUBGOAL_THEN `q <= &111 / &100 * l2 + &3 / &50` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `q <= &1 / &200` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC]);;

let APX_TS_VEC_EQ = prove
 (`!u w:real^3. ~(u = vec 0) /\ ~(w = vec 0) /\ apx_sval u = apx_sval w /\
                inv(norm u) % u = inv(norm w) % w ==> u = w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `u:real^3` APX_POLAR) THEN MP_TAC(SPEC `w:real^3` APX_POLAR) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
  ASM_REWRITE_TAC[]);;

let APX_TS_EC_FACTS = prove
 (`!(gg:real^3->real^3) L x.
        (!y. y IN sphere(vec 0,&1) ==> gg y IN sphere(vec 0,&1)) /\ &0 < L /\ ~(x = vec 0)
        ==> ~((L / norm x) % gg(inv(norm x) % x) = vec 0) /\
            apx_sval((L / norm x) % gg(inv(norm x) % x)) = sqrt(&2) * log L - apx_sval x /\
            inv(norm((L / norm x) % gg(inv(norm x) % x))) % ((L / norm x) % gg(inv(norm x) % x)) =
            gg(inv(norm x) % x) /\
            (L / norm x) % gg(inv(norm x) % x) =
            L % (inv(norm(radial_ext gg x) pow 2) % radial_ext gg x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm((gg:real^3->real^3)(inv(norm x) % x)) = &1` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IN_SPHERE_0] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[SMT_NORMALIZE_SPHERE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(x:real^3) /\ &0 < L / norm x` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[NORM_POS_LT; REAL_LT_DIV]; ALL_TAC] THEN
  SUBGOAL_THEN `~((gg:real^3->real^3)(inv(norm x) % x) = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `norm((gg:real^3->real^3)(inv(norm x) % x)) = &1` THEN
    ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ];
    ASM_SIMP_TAC[APX_SVAL_SCALE; APX_SVAL_UNIT] THEN
    ASM_SIMP_TAC[LOG_DIV; NORM_POS_LT; apx_sval] THEN REAL_ARITH_TAC;
    REWRITE_TAC[NORM_MUL] THEN ASM_REWRITE_TAC[REAL_MUL_RID] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; VECTOR_MUL_ASSOC; REAL_MUL_LINV;
                 REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    MP_TAC(ISPECL [`gg:real^3->real^3`; `x:real^3`] SMT_RADIAL_EXT_NORM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[radial_ext; VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < norm(x:real^3)` THEN CONV_TAC REAL_FIELD]);;

(* Gluing two parametrizations of slabs with a common level function. *)

let APX_TS_GLUE2 = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (lam:A->real) a1 b1 a2 b2
    (e1:real^3->A) e2.
        smooth_manifold_atlas top atlas /\
        mfd_param top atlas (apx_slab a1 b1) e1 /\ mfd_param top atlas (apx_slab a2 b2) e2 /\
        (!x. x IN apx_slab a1 b1 ==> lam(e1 x) = apx_sval x) /\
        (!x. x IN apx_slab a2 b2 ==> lam(e2 x) = apx_sval x) /\
        (!x. x IN apx_slab a1 b1 /\ x IN apx_slab a2 b2 ==> e1 x = e2 x) /\
        a1 <= a2 /\ a2 < b1 /\ b1 <= b2
        ==> ?e. mfd_param top atlas (apx_slab a1 b2) e /\
                (!x. x IN apx_slab a1 b1 ==> e x = e1 x) /\
                (!x. x IN apx_slab a2 b2 ==> e x = e2 x) /\
                (!x. x IN apx_slab a1 b2 ==> lam(e x) = apx_sval x)`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `s1 = apx_slab a1 b1` THEN ABBREV_TAC `s2 = apx_slab a2 b2` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `apx_slab a1 b2 = s1 UNION s2` SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["s1"; "s2"] THEN
    REWRITE_TAC[EXTENSION; IN_UNION; APX_SLAB_SVAL] THEN X_GEN_TAC `x:real^3` THEN
    ASM_CASES_TAC `x:real^3 = vec 0` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3 y. x IN s1 /\ y IN s2 /\ apx_sval x = apx_sval y ==> y IN s1`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["s1"; "s2"] THEN REWRITE_TAC[APX_SLAB_SVAL] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `e = \x:real^3. if x IN s1 then (e1:real^3->A) x else e2 x` THEN
  SUBGOAL_THEN `(!x. x IN s1 ==> (e:real^3->A) x = e1 x) /\ (!x. x IN s2 ==> e x = e2 x)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN CONJ_TAC THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    COND_CASES_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `e:real^3->A` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_UNION THEN
    MAP_EVERY EXISTS_TAC [`e1:real^3->A`; `e2:real^3->A`] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE] THEN X_GEN_TAC `p:A` THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC)
                                 (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `y:real^3` THEN
      SUBGOAL_THEN `(y:real^3) IN s1` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[];
        ASM_MESON_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
      CONJ_TAC THEN EXISTS_TAC `x:real^3` THEN ASM_MESON_TAC[]];
    X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_UNION] THEN STRIP_TAC THEN ASM_SIMP_TAC[]]);;

(* The far piece: x |-> e((L / |x|) gg(x / |x|)) parametrizes the annulus  *)
(* (L / 2, L) when e parametrizes a set containing the annulus (1, 2).    *)

let APX_TS_PIECE_C = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) s (e:real^3->A) gg gg' L.
        smooth_manifold_atlas top atlas /\ mfd_param top atlas s e /\
        annulus (&1) (&2) SUBSET s /\ sphere_diffeo gg gg' /\ &0 < L
        ==> mfd_param top atlas (annulus (L / &2) L)
              (\x. e((L / norm x) % gg(inv(norm x) % x)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?h'. diffeomorphism_on (annulus (L / &2) L) (annulus (&1) (&2))
           ((\x:real^3. L % x) o (\x:real^3. inv(norm x pow 2) % x) o radial_ext gg) h'`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`gg:real^3->real^3`; `gg':real^3->real^3`; `L / &2`; `L:real`]
      SMT_DIFFEO_RADIAL_EXT_ANNULUS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(ISPECL [`L / &2`; `L:real`] (INST_TYPE [`:3`,`:N`] SMT_DIFFEO_INVERSION_ANNULUS)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(ISPECL [`L:real`; `inv L`; `inv(L / &2)`]
      (INST_TYPE [`:3`,`:N`] SMT_DIFFEO_SCALING_ANNULUS)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `L * inv L = &1 /\ L * inv(L / &2) = &2` (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `&0 < L` THEN CONV_TAC REAL_FIELD; DISCH_TAC] THEN
    EXISTS_TAC `(radial_ext gg' o (\x:real^3. inv(norm x pow 2) % x)) o (\x:real^3. inv L % x)` THEN
    MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN
    EXISTS_TAC `annulus (inv L) (inv(L / &2)):real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN
    EXISTS_TAC `annulus (L / &2) L:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MFD_PARAM_EQ THEN
  EXISTS_TAC `(e:real^3->A) o (\x:real^3. L % x) o (\x:real^3. inv(norm x pow 2) % x) o
              radial_ext gg` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
    MAP_EVERY EXISTS_TAC [`s:real^3->bool`; `annulus (&1) (&2):real^3->bool`;
                          `h':real^3->real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^3` THEN REWRITE_TAC[annulus; IN_ELIM_THM; o_THM] THEN STRIP_TAC THEN
  AP_TERM_TAC THEN
  MP_TAC(ISPECL [`gg:real^3->real^3`; `L:real`; `x:real^3`] APX_TS_EC_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[sphere_diffeo];
      REWRITE_TAC[GSYM NORM_EQ_0] THEN ASM_REAL_ARITH_TAC];
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2(CONJUNCT2(CONJUNCT2 th))])]);;

(* The window map h0 on slabs: levels shift by sqrt 2 log r and scale by p. *)

let APX_TS_H0_SLAB = prove
 (`!r p a b. &0 < r /\ &0 < p /\ a <= b
             ==> ?h'. diffeomorphism_on (apx_slab a b)
                        (apx_slab (sqrt(&2) * log r + p * a) (sqrt(&2) * log r + p * b))
                        (apx_ts_h0 r p) h'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[apx_slab] THEN
  MP_TAC(SPECL [`r:real`; `p:real`; `exp(a / sqrt(&2))`; `exp(b / sqrt(&2))`]
    APX_TS_H0_DIFFEO) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_EXP_POS_LT; REAL_EXP_MONO_LE; REAL_LE_DIV2_EQ; SQRT_POS_LT;
                 REAL_OF_NUM_LT; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u. r * exp(u / sqrt(&2)) rpow p = exp((sqrt(&2) * log r + p * u) / sqrt(&2))`
  (fun th -> REWRITE_TAC[th]) THEN
  GEN_TAC THEN REWRITE_TAC[rpow; REAL_EXP_POS_LT; LOG_EXP] THEN
  SUBGOAL_THEN `r = exp(log r)` (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [th]) THENL
   [ASM_SIMP_TAC[EXP_LOG]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `~(sqrt(&2) = &0)` MP_TAC THENL
   [SIMP_TAC[SQRT_EQ_0; REAL_OF_NUM_EQ; ARITH]; CONV_TAC REAL_FIELD]);;

(* The product annuli as slabs. *)

let APX_TS_ANN_SLAB = prove
 (`!b. annulus (&2 / &3) (&3 / &2) =
       apx_slab (--(sqrt(&2) * log(&3 / &2))) (sqrt(&2) * log(&3 / &2)) /\
       annulus (&2 / &3) (&3 / &2 * exp b) =
       apx_slab (--(sqrt(&2) * log(&3 / &2))) (sqrt(&2) * b + sqrt(&2) * log(&3 / &2)) /\
       annulus (&2 / &3 * exp b) (&3 / &2 * exp b) =
       apx_slab (sqrt(&2) * b - sqrt(&2) * log(&3 / &2)) (sqrt(&2) * b + sqrt(&2) * log(&3 / &2))`,
  GEN_TAC THEN
  SUBGOAL_THEN `log(&2 / &3) = --log(&3 / &2)` ASSUME_TAC THENL
   [SIMP_TAC[LOG_DIV; REAL_ARITH `&0 < &2 /\ &0 < &3`] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  W(fun (_,w) -> MP_TAC(SPECL [rand(rator(lhs w)); rand(lhs w)] APX_TS_SLAB_LOG)) THEN
  ASM_SIMP_TAC[REAL_LT_MUL; REAL_EXP_POS_LT; REAL_ARITH `&0 < &2 / &3 /\ &0 < &3 / &2`] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[LOG_MUL; REAL_EXP_POS_LT; REAL_ARITH `&0 < &2 / &3 /\ &0 < &3 / &2`; LOG_EXP] THEN
  BINOP_TAC THEN REAL_ARITH_TAC);;

(* Radial extensions of sphere maps: norm, level and direction. *)

let APX_TS_RADIAL_DIR = prove
 (`!(gg:real^3->real^3) u.
        (!y. y IN sphere(vec 0,&1) ==> gg y IN sphere(vec 0,&1)) /\ ~(u = vec 0)
        ==> ~(radial_ext gg u = vec 0) /\ apx_sval(radial_ext gg u) = apx_sval u /\
            inv(norm(radial_ext gg u)) % radial_ext gg u = gg(inv(norm u) % u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`gg:real^3->real^3`; `u:real^3`] SMT_RADIAL_EXT_NORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < norm(u:real^3)` ASSUME_TAC THENL [ASM_SIMP_TAC[NORM_POS_LT]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM NORM_EQ_0] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[apx_sval];
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[radial_ext; VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID]]);;

let APX_TS_DIR_SCALE = prove
 (`!c u:real^3. &0 < c ==> inv(norm(c % u)) % (c % u) = inv(norm u) % u`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `u:real^3 = vec 0` THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_RZERO]; ALL_TAC] THEN
  REWRITE_TAC[NORM_MUL; VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < c ==> abs c = c`; REAL_INV_MUL] THEN
  UNDISCH_TAC `&0 < c` THEN UNDISCH_TAC `~(u:real^3 = vec 0)` THEN
  REWRITE_TAC[GSYM NORM_EQ_0] THEN CONV_TAC REAL_FIELD);;

let APX_TS_FAR_EQ = prove
 (`!(gg:real^3->real^3) b y.
        (!u. u IN sphere(vec 0,&1) ==> gg u IN sphere(vec 0,&1)) /\ ~(y = vec 0)
        ==> apx_ts_h1 (&2) (&1 / &20) (radial_ext gg (exp(--b) % y)) =
            (exp((sqrt(&2) * log(&2) + sqrt(&2) * log(&3 / &2) + sqrt(&2) * b / &20) /
                 sqrt(&2)) / norm(apx_ts_h0 (&3 / &2) (&1 / &20) y)) %
            gg(inv(norm(apx_ts_h0 (&3 / &2) (&1 / &20) y)) % apx_ts_h0 (&3 / &2) (&1 / &20) y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `L = exp((sqrt(&2) * log(&2) + sqrt(&2) * log(&3 / &2) + sqrt(&2) * b / &20) /
                      sqrt(&2))` THEN
  ABBREV_TAC `x = apx_ts_h0 (&3 / &2) (&1 / &20) y` THEN
  ABBREV_TAC `u = exp(--b) % (y:real^3)` THEN
  ABBREV_TAC `w = radial_ext (gg:real^3->real^3) u` THEN
  SUBGOAL_THEN `&0 < L /\ sqrt(&2) * log L =
                sqrt(&2) * log(&2) + sqrt(&2) * log(&3 / &2) + sqrt(&2) * b / &20`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[REAL_EXP_POS_LT; LOG_EXP] THEN
    SUBGOAL_THEN `~(sqrt(&2) = &0)` MP_TAC THENL
     [SIMP_TAC[SQRT_EQ_0; REAL_OF_NUM_EQ; ARITH]; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MP_TAC(SPECL [`&3 / &2`; `&1 / &20`; `y:real^3`] APX_TS_H_LEVELS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[ASSUME `apx_ts_h0 (&3 / &2) (&1 / &20) y = x`]) THEN
  SUBGOAL_THEN `~(u:real^3 = vec 0) /\ apx_sval u = --(sqrt(&2) * b) + apx_sval(y:real^3) /\
                inv(norm u) % u = inv(norm y) % y`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN
    ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_EXP_NZ; APX_SVAL_SCALE; REAL_EXP_POS_LT;
                 APX_TS_DIR_SCALE; LOG_EXP] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`gg:real^3->real^3`; `u:real^3`] APX_TS_RADIAL_DIR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[ASSUME `radial_ext (gg:real^3->real^3) u = w`]) THEN
  MP_TAC(SPECL [`&2`; `&1 / &20`; `w:real^3`] APX_TS_H_LEVELS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`gg:real^3->real^3`; `L:real`; `x:real^3`] APX_TS_EC_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MATCH_MP_TAC APX_TS_VEC_EQ THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

(* The gluing context: the data of the two necks (APX_TS_DATA) and the     *)
(* product E0 (APX_TS_PRODUCT), for plain neck maps Ek, Ej with inverses   *)
(* ek, ej, a model constant c and the crossing level tau.                  *)

let apx_tsg = new_definition
 `apx_tsg (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) (dl:real)
          (Ek:real^3->A) (Ej:real^3->A) (ek:A->real^3) (ej:A->real^3)
          (c:real) (K0:real) (x1:real^3) (tau:real)
          (E0:real^3->A) (gg:real^3->real^3) (gg':real^3->real^3) <=>
    smooth_manifold_atlas top atlas /\ hausdorff_space top /\ &0 < dl /\
    mfd_param top atlas (rfs_neck_dom dl) Ek /\ mfd_param top atlas (rfs_neck_dom dl) Ej /\
    (!z. z IN rfs_neck_dom dl ==> ek(Ek z) = z) /\
    (!z. z IN rfs_neck_dom dl ==> ej(Ej z) = z) /\
    (!v. v IN apx_slab (--inv(&2 * dl)) (inv(&2 * dl))
         ==> Ek v IN IMAGE Ej (rfs_neck_dom dl)) /\
    apx_ts_mdl (ej o Ek) c K0 (--inv(&2 * dl)) (inv(&2 * dl)) x1 tau /\
    (!w. w IN annulus (&1 / &4) (&4)
         ==> ?v. v IN apx_slab (--inv(&2 * dl)) (inv(&2 * dl)) /\ (ej o Ek) v = w) /\
    mfd_param top atlas (annulus (&2 / &3) (&3 / &2 * exp(apx_ts_b c tau))) E0 /\
    sphere_diffeo gg gg' /\
    (!x. x IN annulus (&2 / &3) (&3 / &2)
         ==> E0 x = Ek (apx_ts_h0 (&3 / &2) (&1 / &20) x)) /\
    (!x. x IN annulus (&2 / &3 * exp(apx_ts_b c tau)) (&3 / &2 * exp(apx_ts_b c tau))
         ==> E0 x = Ej (apx_ts_h1 (&2) (&1 / &20)
                         (radial_ext gg (exp(--apx_ts_b c tau) % x)))) /\
    (!x. x IN annulus (&2 / &3) (&3 / &2 * exp(apx_ts_b c tau))
         ==> apx_ts_fm (ej o Ek) c tau ek (E0 x) = log(norm x)) /\
    {p | p IN IMAGE Ek (apx_slab (-- &1) (tau + &2)) /\
         &0 <= apx_ts_fm (ej o Ek) c tau ek p /\
         apx_ts_fm (ej o Ek) c tau ek p <= apx_ts_b c tau} =
    IMAGE E0 {x | &1 <= norm x /\ norm x <= exp(apx_ts_b c tau)}`;;

(* The level function F o ek on the three pieces: e_k near its sphere, the *)
(* product, and the far points e_j z with 0 < s z < l2.                    *)

let APX_TS_G_LEVELS = prove
 (`!top atlas dl (Ek:real^3->A) Ej ek ej c K0 x1 tau E0 gg gg'.
     apx_tsg top atlas dl Ek Ej ek ej c K0 x1 tau E0 gg gg'
     ==> (!v. v IN apx_slab (-- &1) (tau + &2)
              ==> v IN rfs_neck_dom dl /\ ek(Ek v) = v /\ Ek v = Ej((ej o Ek) v)) /\
         (!x. x IN apx_slab (&0) (sqrt(&2) * log(&3 / &2))
              ==> x IN apx_slab (-- &1) (tau + &2) /\ &0 < apx_sval((ej o Ek) x) /\
                  apx_ts_F (ej o Ek) c tau (ek(Ek x)) = apx_sval x) /\
         (!y. y IN apx_slab (--(sqrt(&2) * log(&3 / &2)))
                            (sqrt(&2) * apx_ts_b c tau + sqrt(&2) * log(&3 / &2))
              ==> apx_ts_F (ej o Ek) c tau (ek(E0 y)) =
                  apx_sval(apx_ts_h0 (&3 / &2) (&1 / &20) y)) /\
         (!z. ~(z = vec 0) /\ &0 < apx_sval z /\ apx_sval z < sqrt(&2) * log(&2)
              ==> ?v. v IN apx_slab (-- &1) (tau + &2) /\ apx_ts_wb tau < apx_sval v /\
                      (ej o Ek) v = z /\ Ek v = Ej z /\
                      apx_ts_F (ej o Ek) c tau (ek(Ej z)) = apx_ts_dd c tau - apx_sval z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[apx_tsg] THEN STRIP_TAC THEN
  ABBREV_TAC `Tm = inv(&2 * dl)` THEN
  ABBREV_TAC `phi = (ej:A->real^3) o (Ek:real^3->A)` THEN
  ABBREV_TAC `W = apx_slab (-- &1) (tau + &2)` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_TS_MDL_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_TS_MDL_TAU) THEN
  STRIP_ASSUME_TAC APX_TS_NUM THEN
  UNDISCH_TAC `apx_ts_mdl (phi:real^3->real^3) c K0 (--Tm) Tm x1 tau` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[apx_ts_mdl] th)) THEN
  SUBGOAL_THEN `W SUBSET apx_slab (--Tm) Tm /\ apx_slab (--Tm) Tm SUBSET rfs_neck_dom dl`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[APX_SLAB_NECK_DOM] THEN CONJ_TAC THEN
    MATCH_MP_TAC APX_SLAB_SUBSET THENL
     [ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `Tm <= inv dl` MP_TAC THENL
       [EXPAND_TAC "Tm" THEN REWRITE_TAC[REAL_INV_MUL] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 < x ==> inv(&2) * x <= x`) THEN
        ASM_REWRITE_TAC[REAL_LT_INV_EQ];
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v. v IN W ==> v IN rfs_neck_dom dl /\ (ek:A->real^3)((Ek:real^3->A) v) = v /\
                               Ek v = (Ej:real^3->A)((phi:real^3->real^3) v)`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(v:real^3) IN apx_slab (--Tm) Tm /\ v IN rfs_neck_dom dl` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(v:real^3) IN apx_slab (--Tm) Tm`) o
      check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (concl th) &&
        can (find_term (fun t -> t = `Ej:real^3->A`)) (concl th) &&
        not (can (find_term (fun t -> t = `E0:real^3->A`)) (concl th)))) THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    EXPAND_TAC "phi" THEN ASM_SIMP_TAC[o_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. ~(y = vec 0) /\ apx_sval y <= apx_ts_wa tau
                ==> apx_ts_F (phi:real^3->real^3) c tau y = apx_sval y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[apx_ts_F] THEN
    MP_TAC(ISPECL [`phi:real^3->real^3`; `apx_ts_wa tau`; `apx_ts_wb tau`;
                   `apx_ts_dd c tau`; `y:real^3`] APX_TS_SPLICE_ZONES) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    (* piece A *)
    X_GEN_TAC `x:real^3` THEN REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN W` ASSUME_TAC THENL
     [EXPAND_TAC "W" THEN ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN W`)) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`phi:real^3->real^3`; `c:real`; `K0:real`; `--Tm`; `Tm:real`;
                     `x1:real^3`; `tau:real`; `x:real^3`] APX_TS_MDL_EST) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN EXPAND_TAC "W" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    (* piece B *)
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MP_TAC(SPEC `apx_ts_b c tau` APX_TS_ANN_SLAB) THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME
      `(y:real^3) IN apx_slab (--(sqrt(&2) * log(&3 / &2)))
                              (sqrt(&2) * apx_ts_b c tau + sqrt(&2) * log(&3 / &2))`) o
      check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `apx_ts_fm:(real^3->real^3)->real->real->(A->real^3)->A->real`))
          (concl th))) THEN
    REWRITE_TAC[apx_ts_fm] THEN DISCH_TAC THEN
    UNDISCH_TAC `(y:real^3) IN apx_slab (--(sqrt(&2) * log(&3 / &2)))
                                (sqrt(&2) * apx_ts_b c tau + sqrt(&2) * log(&3 / &2))` THEN
    REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`&3 / &2`; `&1 / &20`; `y:real^3`] APX_TS_H_LEVELS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&20 * (apx_ts_F (phi:real^3->real^3) c tau ((ek:A->real^3)((E0:real^3->A) y)) -
                        sqrt(&2) * log(&3 / &2)) / sqrt(&2) = log(norm(y:real^3))` THEN
    REWRITE_TAC[apx_sval] THEN
    SUBGOAL_THEN `~(sqrt(&2) = &0)` MP_TAC THENL
     [SIMP_TAC[SQRT_EQ_0; REAL_OF_NUM_EQ; ARITH]; CONV_TAC REAL_FIELD];
    (* piece C *)
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`phi:real^3->real^3`; `c:real`; `K0:real`; `--Tm`; `Tm:real`;
                   `x1:real^3`; `tau:real`; `z:real^3`] APX_TS_MDL_ONTO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `v:real^3` THEN
    SUBGOAL_THEN `(v:real^3) IN W` ASSUME_TAC THENL
     [EXPAND_TAC "W" THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(v:real^3) IN W`)) THEN STRIP_TAC THEN
    SUBGOAL_THEN `(Ek:real^3->A) v = (Ej:real^3->A) z` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(ek:A->real^3)((Ej:real^3->A) z) = v` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    REWRITE_TAC[apx_ts_F] THEN
    MP_TAC(ISPECL [`phi:real^3->real^3`; `apx_ts_wa tau`; `apx_ts_wb tau`;
                   `apx_ts_dd c tau`; `v:real^3`] APX_TS_SPLICE_ZONES) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

(* The glued parametrization of the slab (0, D) (that is, of the annulus  *)
(* (1, exp(D / sqrt 2))): e_k near the sphere of e_k, E0 o h0^-1 in the     *)
(* middle, and x -> e_j((L / |x|) gg(x / |x|)) at the far end.             *)

let APX_TS_G_PARAM = prove
 (`!top atlas dl (Ek:real^3->A) Ej ek ej c K0 x1 tau E0 gg gg'.
     apx_tsg top atlas dl Ek Ej ek ej c K0 x1 tau E0 gg gg'
     ==> ?E. mfd_param top atlas (apx_slab (&0) (apx_ts_dd c tau)) E /\
             (!x. x IN apx_slab (&0) (sqrt(&2) * log(&3 / &2)) ==> E x = Ek x) /\
             (!x. x IN apx_slab (apx_ts_dd c tau - sqrt(&2) * log(&2)) (apx_ts_dd c tau)
                  ==> E x = Ej((exp(apx_ts_dd c tau / sqrt(&2)) / norm x) %
                               gg(inv(norm x) % x))) /\
             (!y. y IN apx_slab (--(sqrt(&2) * log(&3 / &2)))
                                (sqrt(&2) * apx_ts_b c tau + sqrt(&2) * log(&3 / &2))
                  ==> E(apx_ts_h0 (&3 / &2) (&1 / &20) y) = E0 y) /\
             (!x. x IN apx_slab (sqrt(&2) * log(&3 / &2) + &1 / &20 * --(sqrt(&2) * log(&3 / &2)))
                                (sqrt(&2) * log(&3 / &2) + &1 / &20 *
                                 (sqrt(&2) * apx_ts_b c tau + sqrt(&2) * log(&3 / &2)))
                  ==> ?y. y IN apx_slab (--(sqrt(&2) * log(&3 / &2)))
                                        (sqrt(&2) * apx_ts_b c tau + sqrt(&2) * log(&3 / &2)) /\
                          apx_ts_h0 (&3 / &2) (&1 / &20) y = x /\ E x = E0 y) /\
             (!x. x IN apx_slab (&0) (apx_ts_dd c tau)
                  ==> apx_ts_F (ej o Ek) c tau (ek(E x)) = apx_sval x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_TS_G_LEVELS) THEN
  UNDISCH_TAC `apx_tsg top atlas dl (Ek:real^3->A) Ej ek ej c K0 x1 tau E0 gg gg'` THEN
  REWRITE_TAC[apx_tsg] THEN STRIP_TAC THEN
  MP_TAC(SPEC `apx_ts_b c tau` APX_TS_ANN_SLAB) THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_TS_MDL_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_TS_MDL_TAU) THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[apx_ts_mdl] (ASSUME
    `apx_ts_mdl ((ej:A->real^3) o (Ek:real^3->A)) c K0 (--inv(&2 * dl)) (inv(&2 * dl))
                (x1:real^3) tau`)) THEN
  STRIP_ASSUME_TAC APX_TS_NUM THEN
  ABBREV_TAC `l2 = sqrt(&2) * log(&2)` THEN
  ABBREV_TAC `l32 = sqrt(&2) * log(&3 / &2)` THEN
  ABBREV_TAC `dd = apx_ts_dd c tau` THEN
  ABBREV_TAC `sb = sqrt(&2) * apx_ts_b c tau` THEN
  ABBREV_TAC `L = exp(dd / sqrt(&2))` THEN
  ABBREV_TAC `F0 = \p:A. apx_ts_F ((ej:A->real^3) o (Ek:real^3->A)) c tau (ek p)` THEN
  SUBGOAL_THEN `!p:A. apx_ts_F ((ej:A->real^3) o (Ek:real^3->A)) c tau (ek p) = F0 p`
  (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [EXPAND_TAC "F0" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(sqrt(&2) = &0)` ASSUME_TAC THENL
   [SIMP_TAC[SQRT_EQ_0; REAL_OF_NUM_EQ; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `&20 * (dd - l2 - l32) = sb` ASSUME_TAC THENL
   [EXPAND_TAC "sb" THEN REWRITE_TAC[apx_ts_b] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(sqrt(&2) = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < L /\ sqrt(&2) * log L = dd /\ L / &2 = exp((dd - l2) / sqrt(&2))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[REAL_EXP_POS_LT; LOG_EXP] THEN CONJ_TAC THENL
     [UNDISCH_TAC `~(sqrt(&2) = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `(dd - l2) / sqrt(&2) = dd / sqrt(&2) - log(&2)` SUBST1_TAC THENL
     [EXPAND_TAC "l2" THEN UNDISCH_TAC `~(sqrt(&2) = &0)` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_EXP_SUB] THEN SIMP_TAC[EXP_LOG; REAL_ARITH `&0 < &2`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Ys = apx_slab (--l32) (sb + l32)` THEN
  ABBREV_TAC `Bs = apx_slab (l32 + &1 / &20 * --l32) (l32 + &1 / &20 * (sb + l32))` THEN
  MP_TAC(SPECL [`&3 / &2`; `&1 / &20`; `--l32`; `sb + l32`] APX_TS_H0_SLAB) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `h':real^3->real^3` o
    REWRITE_RULE[ASSUME `sqrt(&2) * log(&3 / &2) = l32`;
                 ASSUME `apx_slab (--l32) (sb + l32) = Ys`;
                 ASSUME `apx_slab (l32 + &1 / &20 * --l32) (l32 + &1 / &20 * (sb + l32)) = Bs`]) THEN
  SUBGOAL_THEN
   `(!y. y IN Ys ==> apx_ts_h0 (&3 / &2) (&1 / &20) y IN Bs /\
                     (h':real^3->real^3)(apx_ts_h0 (&3 / &2) (&1 / &20) y) = y) /\
    (!x. x IN Bs ==> (h':real^3->real^3) x IN Ys /\
                     apx_ts_h0 (&3 / &2) (&1 / &20) (h' x) = x)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on Ys Bs (apx_ts_h0 (&3 / &2) (&1 / &20)) h'` THEN
    REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN Bs ==> ~((h':real^3->real^3) x = vec 0) /\
                               apx_sval x = l32 + &1 / &20 * apx_sval(h' x)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(h':real^3->real^3) x IN Ys /\ apx_ts_h0 (&3 / &2) (&1 / &20) (h' x) = x`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~((h':real^3->real^3) x = vec 0)` ASSUME_TAC THENL
     [UNDISCH_TAC `(h':real^3->real^3) x IN Ys` THEN EXPAND_TAC "Ys" THEN
      SIMP_TAC[APX_SLAB_SVAL];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`&3 / &2`; `&1 / &20`; `(h':real^3->real^3) x`] APX_TS_H_LEVELS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the two first pieces *)
  SUBGOAL_THEN `mfd_param top atlas (apx_slab (&0) l32) (Ek:real^3->A)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `rfs_neck_dom dl` THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      REWRITE_TAC[apx_slab; OPEN_ANNULUS];
      REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param top atlas Bs ((E0:real^3->A) o (h':real^3->real^3))` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
    MAP_EVERY EXISTS_TAC [`Ys:real^3->bool`; `Ys:real^3->bool`;
                          `apx_ts_h0 (&3 / &2) (&1 / &20)`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN MATCH_MP_TAC DIFFEOMORPHISM_ON_SYM THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN apx_slab (&0) l32 ==> (F0:A->real)((Ek:real^3->A) x) = apx_sval x`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN Bs ==> (F0:A->real)(((E0:real^3->A) o (h':real^3->real^3)) x) = apx_sval x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(h':real^3->real^3) x IN Ys /\ apx_ts_h0 (&3 / &2) (&1 / &20) (h' x) = x`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN apx_slab (&0) l32 /\ x IN Bs
                    ==> (Ek:real^3->A) x = ((E0:real^3->A) o (h':real^3->real^3)) x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(h':real^3->real^3) x IN Ys /\ apx_ts_h0 (&3 / &2) (&1 / &20) (h' x) = x`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~((h':real^3->real^3) x = vec 0) /\
                  apx_sval x = l32 + &1 / &20 * apx_sval(h' x)` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(h':real^3->real^3) x IN apx_slab (--l32) l32` ASSUME_TAC THENL
     [UNDISCH_TAC `(h':real^3->real^3) x IN Ys` THEN
      UNDISCH_TAC `(x:real^3) IN apx_slab (&0) l32` THEN
      EXPAND_TAC "Ys" THEN REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= l32 + &1 / &20 * --l32 /\ l32 + &1 / &20 * --l32 < l32 /\
                l32 <= l32 + &1 / &20 * (sb + l32)` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `F0:A->real`;
                 `&0`; `l32:real`; `l32 + &1 / &20 * --l32`; `l32 + &1 / &20 * (sb + l32)`;
                 `Ek:real^3->A`; `(E0:real^3->A) o (h':real^3->real^3)`] APX_TS_GLUE2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `eAB:real^3->A` STRIP_ASSUME_TAC) THEN
  (* the far piece *)
  ABBREV_TAC `eC = \x:real^3. (Ej:real^3->A)((L / norm x) % gg(inv(norm x) % x))` THEN
  SUBGOAL_THEN `mfd_param top atlas (apx_slab (dd - l2) dd) (eC:real^3->A)` ASSUME_TAC THENL
   [EXPAND_TAC "eC" THEN REWRITE_TAC[apx_slab] THEN
    REWRITE_TAC[GSYM(ASSUME `L / &2 = exp((dd - l2) / sqrt(&2))`);
                ASSUME `exp(dd / sqrt(&2)) = L`] THEN
    MATCH_MP_TAC APX_TS_PIECE_C THEN
    MAP_EVERY EXISTS_TAC [`rfs_neck_dom dl`; `gg':real^3->real^3`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`&1`; `&2`] APX_TS_SLAB_LOG) THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[LOG_1; REAL_MUL_RZERO; APX_SLAB_NECK_DOM] THEN
    MATCH_MP_TAC APX_SLAB_SUBSET THEN
    SUBGOAL_THEN `&0 < inv dl /\ inv(&2 * dl) = inv(&2) * inv dl` MP_TAC THENL
     [ASM_REWRITE_TAC[REAL_LT_INV_EQ; REAL_INV_MUL]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN apx_slab (dd - l2) dd ==> (F0:A->real)((eC:real^3->A) x) = apx_sval x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN
    EXPAND_TAC "eC" THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`gg:real^3->real^3`; `L:real`; `x:real^3`] APX_TS_EC_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[sphere_diffeo]; ALL_TAC] THEN
    ABBREV_TAC `z = (L / norm x) % (gg:real^3->real^3)(inv(norm x) % x)` THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `apx_ts_wb tau`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN apx_slab (&0) (l32 + &1 / &20 * (sb + l32)) /\ x IN apx_slab (dd - l2) dd
                    ==> (eAB:real^3->A) x = (eC:real^3->A) x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN Bs` ASSUME_TAC THENL
     [EXPAND_TAC "Bs" THEN
      UNDISCH_TAC `(x:real^3) IN apx_slab (&0) (l32 + &1 / &20 * (sb + l32))` THEN
      UNDISCH_TAC `(x:real^3) IN apx_slab (dd - l2) dd` THEN
      REWRITE_TAC[APX_SLAB_SVAL] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(h':real^3->real^3) x IN Ys /\ apx_ts_h0 (&3 / &2) (&1 / &20) (h' x) = x`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~((h':real^3->real^3) x = vec 0) /\
                  apx_sval x = l32 + &1 / &20 * apx_sval(h' x)` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(h':real^3->real^3) x IN apx_slab (sb - l32) (sb + l32)` ASSUME_TAC THENL
     [UNDISCH_TAC `(h':real^3->real^3) x IN Ys` THEN
      UNDISCH_TAC `(x:real^3) IN apx_slab (dd - l2) dd` THEN
      EXPAND_TAC "Ys" THEN REWRITE_TAC[APX_SLAB_SVAL] THEN
      REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(eAB:real^3->A) x = (E0:real^3->A)((h':real^3->real^3) x)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[o_THM]; ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
        can (find_term (fun t -> t = `apx_slab (sb - l32) (sb + l32)`)) (concl th)
      then SUBST1_TAC(MATCH_MP th (ASSUME `(h':real^3->real^3) x IN apx_slab (sb - l32) (sb + l32)`))
      else failwith "no") THEN
    EXPAND_TAC "eC" THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`gg:real^3->real^3`; `apx_ts_b c tau`; `(h':real^3->real^3) x`]
      APX_TS_FAR_EQ) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[sphere_diffeo]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    EXPAND_TAC "L" THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= dd - l2 /\ dd - l2 < l32 + &1 / &20 * (sb + l32) /\
                l32 + &1 / &20 * (sb + l32) <= dd` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `F0:A->real`;
                 `&0`; `l32 + &1 / &20 * (sb + l32)`; `dd - l2`; `dd:real`;
                 `eAB:real^3->A`; `eC:real^3->A`] APX_TS_GLUE2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `E:real^3->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `E:real^3->A` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `apx_slab (&0) l32 SUBSET apx_slab (&0) (l32 + &1 / &20 * (sb + l32)) /\
                Bs SUBSET apx_slab (&0) (l32 + &1 / &20 * (sb + l32))` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Bs" THEN CONJ_TAC THEN MATCH_MP_TAC APX_SLAB_SUBSET THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN apx_slab (&0) (l32 + &1 / &20 * (sb + l32))` ASSUME_TAC THENL
     [ASM SET_TAC[]; ASM_SIMP_TAC[]];
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN apx_slab (dd - l2) dd` ASSUME_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN EXPAND_TAC "eC" THEN REWRITE_TAC[];
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `apx_ts_h0 (&3 / &2) (&1 / &20) y IN Bs /\
                  (h':real^3->real^3)(apx_ts_h0 (&3 / &2) (&1 / &20) y) = y`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `apx_ts_h0 (&3 / &2) (&1 / &20) y IN apx_slab (&0) (l32 + &1 / &20 * (sb + l32))`
    ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[o_THM];
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN EXISTS_TAC `(h':real^3->real^3) x` THEN
    SUBGOAL_THEN `(x:real^3) IN apx_slab (&0) (l32 + &1 / &20 * (sb + l32))` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[o_THM]]);;

(* Norm bounds as level bounds. *)

let APX_TS_NORM_SVAL = prove
 (`!y:real^3 b. ~(y = vec 0)
                ==> (&1 <= norm y <=> &0 <= apx_sval y) /\
                    (norm y <= exp b <=> apx_sval y <= sqrt(&2) * b)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^3) /\ &0 < sqrt(&2)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[NORM_POS_LT; SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  REWRITE_TAC[apx_sval] THEN
  MP_TAC(SPECL [`&1`; `norm(y:real^3)`] LOG_MONO_LE) THEN
  MP_TAC(SPECL [`norm(y:real^3)`; `exp b`] LOG_MONO_LE) THEN
  ASM_REWRITE_TAC[REAL_EXP_POS_LT; REAL_LT_01; LOG_1; LOG_EXP] THEN
  REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_LE_MUL_EQ]);;

(* The tight-shell parametrization: E = e_k on annulus(1, 3/2), the radial  *)
(* far formula on annulus(L/2, L), and image the model region e_k(R) with  *)
(* R = (v in W: 0 < s v, 0 < s(phi v)).                                    *)

let APX_TS_GLUE = prove
 (`!top atlas dl (Ek:real^3->A) Ej ek ej c K0 x1 tau E0 gg gg'.
     apx_tsg top atlas dl Ek Ej ek ej c K0 x1 tau E0 gg gg'
     ==> ?E. &1 < exp(apx_ts_dd c tau / sqrt(&2)) /\
             mfd_param top atlas (annulus (&1) (exp(apx_ts_dd c tau / sqrt(&2)))) E /\
             (!x. x IN annulus (&1) (&3 / &2) ==> E x = Ek x) /\
             (!x. x IN annulus (exp(apx_ts_dd c tau / sqrt(&2)) / &2)
                               (exp(apx_ts_dd c tau / sqrt(&2)))
                  ==> E x = Ej((exp(apx_ts_dd c tau / sqrt(&2)) / norm x) %
                               gg(inv(norm x) % x))) /\
             IMAGE E (annulus (&1) (exp(apx_ts_dd c tau / sqrt(&2)))) =
             IMAGE Ek {v | v IN apx_slab (-- &1) (tau + &2) /\ &0 < apx_sval v /\
                           &0 < apx_sval((ej o Ek) v)}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `E:real^3->A` STRIP_ASSUME_TAC o MATCH_MP APX_TS_G_PARAM) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_TS_G_LEVELS) THEN
  UNDISCH_TAC `apx_tsg top atlas dl (Ek:real^3->A) Ej ek ej c K0 x1 tau E0 gg gg'` THEN
  REWRITE_TAC[apx_tsg] THEN STRIP_TAC THEN
  MP_TAC(SPEC `apx_ts_b c tau` APX_TS_ANN_SLAB) THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_TS_MDL_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_TS_MDL_TAU) THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[apx_ts_mdl] (ASSUME
    `apx_ts_mdl ((ej:A->real^3) o (Ek:real^3->A)) c K0 (--inv(&2 * dl)) (inv(&2 * dl))
                (x1:real^3) tau`)) THEN
  STRIP_ASSUME_TAC APX_TS_NUM THEN
  ABBREV_TAC `l2 = sqrt(&2) * log(&2)` THEN
  ABBREV_TAC `l32 = sqrt(&2) * log(&3 / &2)` THEN
  ABBREV_TAC `dd = apx_ts_dd c tau` THEN
  ABBREV_TAC `sb = sqrt(&2) * apx_ts_b c tau` THEN
  ABBREV_TAC `L = exp(dd / sqrt(&2))` THEN
  ABBREV_TAC `W = apx_slab (-- &1) (tau + &2)` THEN
  ABBREV_TAC `phi = (ej:A->real^3) o (Ek:real^3->A)` THEN
  ABBREV_TAC `F1 = apx_ts_F (phi:real^3->real^3) c tau` THEN
  SUBGOAL_THEN `~(sqrt(&2) = &0) /\ &0 < sqrt(&2)` STRIP_ASSUME_TAC THENL
   [SIMP_TAC[SQRT_EQ_0; SQRT_POS_LT; REAL_OF_NUM_EQ; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `&20 * (dd - l2 - l32) = sb` ASSUME_TAC THENL
   [EXPAND_TAC "sb" THEN REWRITE_TAC[apx_ts_b] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(sqrt(&2) = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < L /\ sqrt(&2) * log L = dd /\ exp((dd - l2) / sqrt(&2)) = L / &2 /\
                exp(l32 / sqrt(&2)) = &3 / &2 /\ exp(&0 / sqrt(&2)) = &1`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[REAL_EXP_POS_LT; LOG_EXP] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `~(sqrt(&2) = &0)` THEN CONV_TAC REAL_FIELD;
      SUBGOAL_THEN `(dd - l2) / sqrt(&2) = dd / sqrt(&2) - log(&2)` SUBST1_TAC THENL
       [EXPAND_TAC "l2" THEN UNDISCH_TAC `~(sqrt(&2) = &0)` THEN CONV_TAC REAL_FIELD;
        ALL_TAC] THEN
      REWRITE_TAC[REAL_EXP_SUB] THEN SIMP_TAC[EXP_LOG; REAL_ARITH `&0 < &2`] THEN
      REAL_ARITH_TAC;
      EXPAND_TAC "l32" THEN
      SUBGOAL_THEN `(sqrt(&2) * log(&3 / &2)) / sqrt(&2) = log(&3 / &2)` SUBST1_TAC THENL
       [UNDISCH_TAC `~(sqrt(&2) = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      SIMP_TAC[EXP_LOG; REAL_ARITH `&0 < &3 / &2`];
      REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_EXP_0]];
    ALL_TAC] THEN
  SUBGOAL_THEN `annulus (&1) L = apx_slab (&0) dd:real^3->bool /\
                annulus (&1) (&3 / &2) = apx_slab (&0) l32:real^3->bool /\
                annulus (L / &2) L = apx_slab (dd - l2) dd:real^3->bool`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[apx_slab] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `E:real^3->A` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < dd` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [EXPAND_TAC "L" THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EXP_0] THEN
    REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_SIMP_TAC[REAL_LT_DIV];
    ALL_TAC] THEN
  (* facts on the model at points of W *)
  SUBGOAL_THEN `W SUBSET apx_slab (--inv(&2 * dl)) (inv(&2 * dl))` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN MATCH_MP_TAC APX_SLAB_SUBSET THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `apx_ts_wa tau < apx_ts_wb tau` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!v. v IN W
        ==> (&0 < (F1:real^3->real) v <=> &0 < apx_sval v) /\
            (F1 v < dd <=> &0 < apx_sval((phi:real^3->real^3) v)) /\
            (F1 v <= l32 ==> F1 v = apx_sval v) /\
            (dd - l2 <= F1 v ==> F1 v = dd - apx_sval(phi v))`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`phi:real^3->real^3`; `c:real`; `K0:real`; `--inv(&2 * dl)`;
                   `inv(&2 * dl)`; `x1:real^3`; `tau:real`; `v:real^3`] APX_TS_MDL_LEVELS) THEN
    MP_TAC(ISPECL [`phi:real^3->real^3`; `c:real`; `K0:real`; `--inv(&2 * dl)`;
                   `inv(&2 * dl)`; `x1:real^3`; `tau:real`; `v:real^3`] APX_TS_MDL_ZONEF) THEN
    MP_TAC(ISPECL [`phi:real^3->real^3`; `apx_ts_wa tau`; `apx_ts_wb tau`;
                   `apx_ts_dd c tau`; `v:real^3`] APX_TS_SPLICE_ZONES) THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
    EXPAND_TAC "F1" THEN REWRITE_TAC[apx_ts_F] THEN ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `fv = apx_ts_splice (phi:real^3->real^3) (tau - &11 / &10 * l2 - &1 / &20)
                       (tau - &11 / &10 * l2) dd v` THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC)) THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN DISCH_TAC THENL
     [SUBGOAL_THEN `apx_sval(v:real^3) <= tau - &11 / &10 * l2 - &1 / &20` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      SUBGOAL_THEN `tau - &11 / &10 * l2 <= apx_sval(v:real^3)` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v. v IN W ==> apx_ts_fm (phi:real^3->real^3) c tau (ek:A->real^3) ((Ek:real^3->A) v) =
                               &20 * ((F1:real^3->real) v - l32) / sqrt(&2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN REWRITE_TAC[apx_ts_fm] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u:real^3. u IN sphere(vec 0,&1)
                ==> gg u IN sphere(vec 0,&1) /\ gg' u IN sphere(vec 0,&1) /\
                    gg'(gg u) = u /\ gg(gg' u) = u`
  ASSUME_TAC THENL [ASM_MESON_TAC[sphere_diffeo]; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN apx_slab (--l32) (sb + l32)
                ==> ~(apx_ts_h0 (&3 / &2) (&1 / &20) y = vec 0) /\
                    apx_sval(apx_ts_h0 (&3 / &2) (&1 / &20) y) = l32 + &1 / &20 * apx_sval y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN REWRITE_TAC[APX_SLAB_SVAL] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`&3 / &2`; `&1 / &20`; `y:real^3`] APX_TS_H_LEVELS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `p:A` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^3` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
    SUBGOAL_THEN `?v:real^3. v IN W /\ (E:real^3->A) x = (Ek:real^3->A) v`
    (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THENL
     [UNDISCH_TAC `(x:real^3) IN apx_slab (&0) dd` THEN REWRITE_TAC[APX_SLAB_SVAL] THEN
      STRIP_TAC THEN
      ASM_CASES_TAC `apx_sval(x:real^3) < l32` THENL
       [EXISTS_TAC `x:real^3` THEN
        SUBGOAL_THEN `(x:real^3) IN apx_slab (&0) l32` ASSUME_TAC THENL
         [ASM_REWRITE_TAC[APX_SLAB_SVAL]; ALL_TAC] THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      ASM_CASES_TAC `dd - l2 < apx_sval(x:real^3)` THENL
       [SUBGOAL_THEN `(x:real^3) IN apx_slab (dd - l2) dd` ASSUME_TAC THENL
         [ASM_REWRITE_TAC[APX_SLAB_SVAL]; ALL_TAC] THEN
        MP_TAC(ISPECL [`gg:real^3->real^3`; `L:real`; `x:real^3`] APX_TS_EC_FACTS) THEN
        ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
        ABBREV_TAC `z = (L / norm x) % (gg:real^3->real^3)(inv(norm x) % x)` THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (fun th ->
          is_forall(concl th) && can (find_term (fun t -> t = `apx_ts_wb tau`)) (concl th))) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `v:real^3` THEN ASM_SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(x:real^3) IN apx_slab (l32 + &1 / &20 * --l32) (l32 + &1 / &20 * (sb + l32))`
      ASSUME_TAC THENL
       [ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME
        `(x:real^3) IN apx_slab (l32 + &1 / &20 * --l32) (l32 + &1 / &20 * (sb + l32))`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `~(y:real^3 = vec 0) /\ apx_sval(x:real^3) = l32 + &1 / &20 * apx_sval y`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [UNDISCH_TAC `(y:real^3) IN apx_slab (--l32) (sb + l32)` THEN SIMP_TAC[APX_SLAB_SVAL];
          FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
            concl th = `apx_ts_h0 (&3 / &2) (&1 / &20) y = (x:real^3)`)) THEN
          ASM_SIMP_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `(E0:real^3->A) y IN IMAGE E0 {x | &1 <= norm x /\ norm x <= exp(apx_ts_b c tau)}`
      MP_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_ELIM_THM] THEN
        MP_TAC(SPECL [`y:real^3`; `apx_ts_b c tau`] APX_TS_NORM_SVAL) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      FIRST_ASSUM(fun th -> if is_eq(concl th) &&
          can (find_term ((=) `E0:real^3->A`)) (rand(concl th)) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_ts_fm")) (lhand(concl th))
        then REWRITE_TAC[GSYM th] else failwith "no") THEN
      REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN STRIP_TAC THEN
      EXISTS_TAC `x':real^3` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `v:real^3` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(F1:real^3->real) v = apx_sval(x:real^3)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN apx_slab (&0) dd`) o check (fun th ->
        is_forall(concl th) && can (find_term (fun t -> t = `F1:real^3->real`)) (concl th) &&
        can (find_term (fun t -> t = `E:real^3->A`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(x:real^3) IN apx_slab (&0) dd` THEN REWRITE_TAC[APX_SLAB_SVAL] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(v:real^3) IN W`) o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `dd - l2`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^3` (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(v:real^3) IN W`) o check (fun th ->
    is_forall(concl th) && can (find_term (fun t -> t = `dd - l2`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(v:real^3 = vec 0) /\ ~((phi:real^3->real^3) v = vec 0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `(v:real^3) IN W` THEN EXPAND_TAC "W" THEN SIMP_TAC[APX_SLAB_SVAL];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `(F1:real^3->real) v < l32` THENL
   [EXISTS_TAC `v:real^3` THEN
    SUBGOAL_THEN `(F1:real^3->real) v = apx_sval(v:real^3)` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(v:real^3) IN apx_slab (&0) l32` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `dd - l2 < (F1:real^3->real) v` THENL
   [SUBGOAL_THEN `(F1:real^3->real) v = dd - apx_sval((phi:real^3->real^3) v)` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `z = (phi:real^3->real^3) v` THEN
    ABBREV_TAC `x = (L / norm z) % (gg':real^3->real^3)(inv(norm z) % z)` THEN
    EXISTS_TAC `x:real^3` THEN
    MP_TAC(ISPECL [`gg':real^3->real^3`; `L:real`; `z:real^3`] APX_TS_EC_FACTS) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MAP_EVERY ASSUME_TAC o butlast o CONJUNCTS o
      REWRITE_RULE[ASSUME `(L / norm z) % (gg':real^3->real^3)(inv(norm z) % z) = x`]) THEN
    SUBGOAL_THEN `inv(norm z) % z IN sphere(vec 0:real^3,&1)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[SMT_NORMALIZE_SPHERE]; ALL_TAC] THEN
    MP_TAC(ISPECL [`gg:real^3->real^3`; `L:real`; `x:real^3`] APX_TS_EC_FACTS) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MAP_EVERY ASSUME_TAC o butlast o CONJUNCTS) THEN
    SUBGOAL_THEN `(L / norm x) % (gg:real^3->real^3)(inv(norm x) % x) = z` ASSUME_TAC THENL
     [MATCH_MP_TAC APX_TS_VEC_EQ THEN REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC;
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^3) IN apx_slab (dd - l2) dd` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
          can (find_term (fun t -> t = `apx_slab (dd - l2) dd`)) (concl th) &&
          can (find_term (fun t -> t = `E:real^3->A`)) (concl th)
        then REWRITE_TAC[MATCH_MP th (ASSUME `(x:real^3) IN apx_slab (dd - l2) dd`)]
        else failwith "no") THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Ek:real^3->A) v IN IMAGE (E0:real^3->A)
                  {x:real^3 | &1 <= norm x /\ norm x <= exp(apx_ts_b c tau)}`
  MP_TAC THENL
   [FIRST_ASSUM(fun th -> if is_eq(concl th) &&
        can (find_term ((=) `E0:real^3->A`)) (rand(concl th)) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_ts_fm")) (lhand(concl th))
      then REWRITE_TAC[GSYM th] else failwith "no") THEN
    REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `&20 * ((F1:real^3->real) v - l32) / sqrt(&2) =
                  (&20 * (F1 v - l32)) / sqrt(&2)` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `&1 <= norm(y:real^3)` THEN ASM_REWRITE_TAC[NORM_0] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`y:real^3`; `apx_ts_b c tau`] APX_TS_NORM_SVAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN apx_slab (--l32) (sb + l32)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `apx_ts_h0 (&3 / &2) (&1 / &20) y` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[APX_SLAB_SVAL] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The tight shell, part 5: topology.  Continuity of a radial               *)
(* section along the normalization, the inner side of a section (open, with *)
(* compact closure), and the exclusion of a third sphere inside the shell   *)
(* (APX_TS_N4).                                                             *)
(* ------------------------------------------------------------------------- *)

(* The level of a radial section along the normalization is continuous. *)

let APX_TS_UDIR_CONT = prove
 (`!u:real^3->real.
        (\x. lift(u x)) continuous_on sphere(vec 0,&1)
        ==> (\z. lift(norm z - u(inv(norm z) % z))) continuous_on {z:real^3 | ~(z = vec 0)}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_SUB] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
  REWRITE_TAC[REWRITE_RULE[o_DEF] CONTINUOUS_ON_LIFT_NORM] THEN
  SUBGOAL_THEN `(\z. lift(u(inv(norm z) % z))) =
                (\x. lift((u:real^3->real) x)) o (\z:real^3. inv(norm z) % z)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN REWRITE_TAC[SMOOTH_MAP_ON_NORMALIZE];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `sphere(vec 0:real^3,&1)` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_SPHERE_0] THEN
    SIMP_TAC[APX_NORMALIZE_UNIT]]);;

(* The inner side of a radial section u of a parametrization Ek, between    *)
(* the unit sphere and the section, is open, and its closure (the closed     *)
(* inner side) is compact.                                                   *)

let APX_TS_INNER_SIDE = prove
 (`!(u:real^3->real) B.
        (\x. lift(u x)) continuous_on sphere(vec 0,&1) /\
        (!x. x IN sphere(vec 0,&1) ==> u x <= B)
        ==> open {v:real^3 | &1 < norm v /\ norm v < u(inv(norm v) % v)} /\
            compact {v:real^3 | &1 <= norm v /\ norm v <= u(inv(norm v) % v)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP APX_TS_UDIR_CONT) THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`\z:real^3. lift(norm z - u(inv(norm z) % z))`;
                   `{z:real^3 | &1 < norm z}`; `{y:real^1 | y$1 < &0}`]
      CONTINUOUS_OPEN_PREIMAGE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN
        DISCH_TAC THEN DISCH_TAC THEN UNDISCH_TAC `&1 < norm(z:real^3)` THEN
        ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
        SUBGOAL_THEN `{z:real^3 | &1 < norm z} = (:real^3) DIFF cball(vec 0,&1)`
        SUBST1_TAC THENL
         [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_CBALL_0] THEN
          REAL_ARITH_TAC;
          SIMP_TAC[OPEN_DIFF; OPEN_UNIV; CLOSED_CBALL]]];
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; GSYM drop; LIFT_DROP] THEN REAL_ARITH_TAC];
    REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `cball(vec 0:real^3,B)` THEN
      REWRITE_TAC[BOUNDED_CBALL; SUBSET; IN_ELIM_THM; IN_CBALL_0] THEN
      X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN
      SUBGOAL_THEN `~(v:real^3 = vec 0)` ASSUME_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `&1 <= norm(v:real^3)` THEN
        ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `(u:real^3->real)(inv(norm v) % v) <= B` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[SMT_NORMALIZE_SPHERE];
        ASM_REAL_ARITH_TAC];
      MP_TAC(ISPECL [`\z:real^3. lift(norm z - u(inv(norm z) % z))`;
                     `{z:real^3 | &1 <= norm z}`; `{y:real^1 | y$1 <= &0}`]
        CONTINUOUS_CLOSED_PREIMAGE) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_LE] THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
          EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN
          DISCH_TAC THEN DISCH_TAC THEN UNDISCH_TAC `&1 <= norm(z:real^3)` THEN
          ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
          SUBGOAL_THEN `{z:real^3 | &1 <= norm z} = (:real^3) DIFF ball(vec 0,&1)`
          SUBST1_TAC THENL
           [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_BALL_0] THEN
            REAL_ARITH_TAC;
            SIMP_TAC[CLOSED_DIFF; CLOSED_UNIV; OPEN_BALL]]];
        MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
        REWRITE_TAC[EXTENSION; IN_ELIM_THM; GSYM drop; LIFT_DROP] THEN REAL_ARITH_TAC]]]);;

(* A connected open set P meeting the inner side of a radial section of a   *)
(* parametrization Ek, and avoiding the unit sphere and the section, lies in *)
(* the inner side; so a set in the closure of P cannot avoid the inner side, *)
(* the unit sphere and the section.  The inner side lies in R when R is      *)
(* radially convex inwards and contains the section.                        *)

let APX_TS_N4 = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) N (Ek:real^3->A) R (u:real^3->real) B P Sj.
     hausdorff_space top /\ mfd_param top atlas N Ek /\
     sphere(vec 0,&1) SUBSET N /\ R SUBSET N /\
     (!v t. v IN R /\ &1 < t * norm v /\ t <= &1 ==> t % v IN R) /\
     (\x. lift(u x)) continuous_on sphere(vec 0,&1) /\
     (!x. x IN sphere(vec 0,&1) ==> &0 < u x /\ u x <= B /\ u x % x IN R) /\
     open_in top P /\ connected_in top P /\
     DISJOINT P (IMAGE Ek (sphere(vec 0,&1))) /\
     DISJOINT P (IMAGE (\x. Ek(u x % x)) (sphere(vec 0,&1))) /\
     ~(DISJOINT P (IMAGE Ek {v | &1 < norm v /\ norm v < u(inv(norm v) % v)})) /\
     Sj SUBSET top closure_of P /\ ~(Sj = {}) /\
     DISJOINT Sj (IMAGE Ek (sphere(vec 0,&1))) /\
     DISJOINT Sj (IMAGE (\x. Ek(u x % x)) (sphere(vec 0,&1))) /\
     DISJOINT Sj (IMAGE Ek R)
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`u:real^3->real`; `B:real`] APX_TS_INNER_SIDE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `I0 = {v:real^3 | &1 < norm v /\ norm v < u(inv(norm v) % v)}` THEN
  ABBREV_TAC `K0 = {v:real^3 | &1 <= norm v /\ norm v <= u(inv(norm v) % v)}` THEN
  ABBREV_TAC `Sm = IMAGE (\x. (Ek:real^3->A)(u x % x)) (sphere(vec 0,&1))` THEN
  SUBGOAL_THEN `!v:real^3. &1 <= norm v
                ==> ~(v = vec 0) /\ inv(norm v) % v IN sphere(vec 0,&1) /\
                    norm v % (inv(norm v) % v) = v`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(v:real^3 = vec 0)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `&1 <= norm(v:real^3)` THEN
      ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[SMT_NORMALIZE_SPHERE; APX_NORMALIZE_UNIT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN sphere(vec 0,&1) ==> norm((u:real^3->real) x % x) = u x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < (u:real^3->real) x` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `x IN sphere(vec 0:real^3,&1)` THEN
    REWRITE_TAC[IN_SPHERE_0; NORM_MUL] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_MUL_RID] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(I0:real^3->bool) SUBSET R` ASSUME_TAC THENL
   [EXPAND_TAC "I0" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(v:real^3 = vec 0) /\ inv(norm v) % v IN sphere(vec 0,&1) /\
                  norm v % (inv(norm v) % v) = v` STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
         can (find_term (fun t -> t = `&1 <= norm(v:real^3)`)) (snd(strip_forall(concl th)))
         then MATCH_MP_TAC th else failwith "no") THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `x:real^3 = inv(norm v) % v` THEN
    SUBGOAL_THEN `&0 < (u:real^3->real) x /\ u x % x IN R /\ norm(u x % x) = u x`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `v:real^3 = (norm v / (u:real^3->real) x) % (u x % x)` SUBST1_TAC THENL
     [REWRITE_TAC[VECTOR_MUL_ASSOC] THEN ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ];
      ALL_TAC] THEN
    FIRST_ASSUM(MATCH_MP_TAC o
      check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 2)) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(K0:real^3->bool) SUBSET N /\ I0 SUBSET K0 /\
                IMAGE (Ek:real^3->A) K0 SUBSET
                IMAGE Ek I0 UNION IMAGE Ek (sphere(vec 0,&1)) UNION Sm`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `!v:real^3. v IN K0
                  ==> v IN I0 \/ v IN sphere(vec 0,&1) \/
                      v = u(inv(norm v) % v) % (inv(norm v) % v)`
    ASSUME_TAC THENL
     [X_GEN_TAC `v:real^3` THEN EXPAND_TAC "K0" THEN EXPAND_TAC "I0" THEN
      REWRITE_TAC[IN_ELIM_THM; IN_SPHERE_0] THEN STRIP_TAC THEN
      ASM_CASES_TAC `norm(v:real^3) = &1` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `norm(v:real^3) = u(inv(norm v) % v)` THENL
       [DISJ2_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
        CONV_TAC SYM_CONV THEN
        FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
         can (find_term (fun t -> t = `&1 <= norm(v:real^3)`)) (snd(strip_forall(concl th)))
         then MP_TAC(SPEC `v:real^3` th) else failwith "no") THEN
        ASM_SIMP_TAC[];
        DISJ1_TAC THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(v:real^3) IN K0`)) THEN
      STRIP_TAC THENL
       [ASM SET_TAC[];
        ASM SET_TAC[];
        FIRST_X_ASSUM SUBST1_TAC THEN
        SUBGOAL_THEN `inv(norm v) % v IN sphere(vec 0:real^3,&1)` ASSUME_TAC THENL
         [UNDISCH_TAC `(v:real^3) IN K0` THEN EXPAND_TAC "K0" THEN
          REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
          ALL_TAC] THEN
        SUBGOAL_THEN `(u:real^3->real)(inv(norm v) % v) % (inv(norm v) % v) IN R`
        MP_TAC THENL [ASM_SIMP_TAC[]; ASM SET_TAC[]]];
      MAP_EVERY EXPAND_TAC ["I0"; "K0"] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(v:real^3) IN K0`)) THEN
      STRIP_TAC THENL
       [ASM SET_TAC[];
        ASM SET_TAC[];
        REWRITE_TAC[IN_UNION] THEN DISJ2_TAC THEN DISJ2_TAC THEN EXPAND_TAC "Sm" THEN
        REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `inv(norm v) % v:real^3` THEN
        CONJ_TAC THENL
         [REWRITE_TAC[] THEN AP_TERM_TAC THEN FIRST_ASSUM ACCEPT_TAC;
          UNDISCH_TAC `(v:real^3) IN K0` THEN EXPAND_TAC "K0" THEN
          REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_SIMP_TAC[]]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (IMAGE (Ek:real^3->A) I0) /\ closed_in top (IMAGE Ek K0)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `N:real^3->bool`] THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`(I0:real^3->bool) SUBSET R`; `(R:real^3->bool) SUBSET N`] THEN
      SET_TAC[];
      MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `N:real^3->bool`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (Ek:real^3->A) I0 SUBSET IMAGE Ek K0` ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P INTER IMAGE (Ek:real^3->A) I0 = P` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_CONNECTED_CLOPEN_EQ THEN EXISTS_TAC `top:A topology` THEN
    ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET] THEN CONJ_TAC THENL
     [UNDISCH_TAC `~DISJOINT P (IMAGE (Ek:real^3->A) I0)` THEN SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `!P c k q. (c:A->bool) SUBSET k /\ P INTER k SUBSET q
                                     ==> P INTER c SUBSET q`) THEN
    EXISTS_TAC `IMAGE (Ek:real^3->A) K0` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (Ek:real^3->A) I0 SUBSET IMAGE Ek K0` THEN SET_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`IMAGE (Ek:real^3->A) K0 SUBSET IMAGE Ek I0 UNION IMAGE Ek (sphere(vec 0,&1)) UNION Sm`;
        `DISJOINT P (IMAGE (Ek:real^3->A) (sphere(vec 0,&1)))`; `DISJOINT (P:A->bool) Sm`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `top closure_of P SUBSET IMAGE (Ek:real^3->A) K0` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`P INTER IMAGE (Ek:real^3->A) I0 = P`;
                           `IMAGE (Ek:real^3->A) I0 SUBSET IMAGE Ek K0`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (Ek:real^3->A) I0 SUBSET IMAGE Ek R` ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(Sj:A->bool) = {}` MP_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `!S C K I0 Sph Sm R.
        S SUBSET C /\ C SUBSET K /\ K SUBSET I0 UNION Sph UNION Sm /\ I0 SUBSET R /\
        DISJOINT S Sph /\ DISJOINT S Sm /\ DISJOINT S R ==> (S:A->bool) = {}`) THEN
    MAP_EVERY EXISTS_TAC
     [`top closure_of P:A->bool`; `IMAGE (Ek:real^3->A) K0`; `IMAGE (Ek:real^3->A) I0`;
      `IMAGE (Ek:real^3->A) (sphere(vec 0,&1))`; `Sm:A->bool`; `IMAGE (Ek:real^3->A) R`] THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

(* The model region Q = e_k(R) of the tight shell: open, connected, closure  *)
(* in Q with the two unit spheres, disjoint from them, and meeting P.        *)

let APX_TS_Q_FACTS = prove
 (`!top atlas (g:A->real^3^3) dl J (e:num->real^3->A) P j k ek ej c K0 x1 tau E0 gg gg'
    E L Q.
     apx_tsh (top,atlas) g dl J e P j k /\
     apx_tsg top atlas dl (e k) (e j) ek ej c K0 x1 tau E0 gg gg' /\
     mfd_param top atlas (annulus (&1) L) E /\
     Q = IMAGE (e k) {v | v IN apx_slab (-- &1) (tau + &2) /\ &0 < apx_sval v /\
                          &0 < apx_sval((ej o e k) v)} /\
     IMAGE E (annulus (&1) L) = Q
     ==> open_in top Q /\ connected_in top Q /\
         top closure_of Q SUBSET
         Q UNION IMAGE (e k) (sphere(vec 0,&1)) UNION IMAGE (e j) (sphere(vec 0,&1)) /\
         DISJOINT Q (IMAGE (e k) (sphere(vec 0,&1))) /\
         DISJOINT Q (IMAGE (e j) (sphere(vec 0,&1))) /\
         e k (&4 / &3 % basis 1) IN Q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_TS_G_LEVELS) THEN
  UNDISCH_TAC `apx_tsg top atlas dl ((e:num->real^3->A) k) (e j) ek ej c K0 x1 tau E0 gg gg'` THEN
  REWRITE_TAC[apx_tsg] THEN STRIP_TAC THEN
  ABBREV_TAC `phi = (ej:A->real^3) o (e:num->real^3->A) k` THEN
  ABBREV_TAC `W = apx_slab (-- &1) (tau + &2)` THEN
  ABBREV_TAC `Rm = {v | v IN W /\ &0 < apx_sval v /\ &0 < apx_sval((phi:real^3->real^3) v)}` THEN
  SUBGOAL_THEN `sphere(vec 0:real^3,&1) SUBSET rfs_neck_dom dl` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `apx_tsh (top,atlas) (g:A->real^3^3) dl J (e:num->real^3->A) P j k` THEN
      REWRITE_TAC[apx_tsh] THEN STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP APX_RG0_BASICS) THEN
      DISCH_THEN(MP_TAC o SPEC `k:num` o CONJUNCT1) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^3. v IN Rm ==> v IN W /\ ~(v = vec 0) /\ &0 < apx_sval v /\
                                       &0 < apx_sval((phi:real^3->real^3) v)`
  ASSUME_TAC THENL
   [EXPAND_TAC "Rm" THEN EXPAND_TAC "W" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    SIMP_TAC[APX_SLAB_SVAL];
    ALL_TAC] THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[apx_ts_mdl] (ASSUME
    `apx_ts_mdl (phi:real^3->real^3) c K0 (--inv(&2 * dl)) (inv(&2 * dl)) x1 tau`)) THEN
  SUBGOAL_THEN `W SUBSET apx_slab (--inv(&2 * dl)) (inv(&2 * dl))` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN MATCH_MP_TAC APX_SLAB_SUBSET THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!v. v IN W
        ==> (&0 < apx_ts_splice (phi:real^3->real^3) (apx_ts_wa tau) (apx_ts_wb tau)
                                (apx_ts_dd c tau) v <=> &0 < apx_sval v) /\
            (&0 <= apx_ts_splice phi (apx_ts_wa tau) (apx_ts_wb tau) (apx_ts_dd c tau) v <=>
             &0 <= apx_sval v) /\
            (apx_ts_splice phi (apx_ts_wa tau) (apx_ts_wb tau) (apx_ts_dd c tau) v =
             apx_ts_dd c tau <=> apx_sval(phi v) = &0) /\
            (apx_ts_splice phi (apx_ts_wa tau) (apx_ts_wb tau) (apx_ts_dd c tau) v <
             apx_ts_dd c tau <=> &0 < apx_sval(phi v)) /\
            (apx_ts_splice phi (apx_ts_wa tau) (apx_ts_wb tau) (apx_ts_dd c tau) v <=
             apx_ts_dd c tau <=> &0 <= apx_sval(phi v))`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`phi:real^3->real^3`; `c:real`; `K0:real`; `--inv(&2 * dl)`;
                   `inv(&2 * dl)`; `x1:real^3`; `tau:real`; `v:real^3`] APX_TS_MDL_LEVELS) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`phi:real^3->real^3`; `c:real`; `K0:real`; `--inv(&2 * dl)`;
                 `inv(&2 * dl)`; `x1:real^3`; `tau:real`; `&0`; `apx_ts_dd c tau`]
    APX_TS_MDL_COMPACT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[ASSUME `apx_slab (-- &1) (tau + &2) = W`]) THEN
  ABBREV_TAC `Fs = apx_ts_splice (phi:real^3->real^3) (apx_ts_wa tau) (apx_ts_wb tau)
                     (apx_ts_dd c tau)` THEN
  ABBREV_TAC `Km = {v | v IN W /\ &0 <= (Fs:real^3->real) v /\ Fs v <= apx_ts_dd c tau}` THEN
  SUBGOAL_THEN `!w:real^3. w IN sphere(vec 0,&1) ==> ~(w = vec 0) /\ apx_sval w = &0`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^3` THEN REWRITE_TAC[IN_SPHERE_0] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[APX_SVAL_UNIT] THEN DISCH_TAC THEN
    UNDISCH_TAC `norm(w:real^3) = &1` THEN ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^3. v IN W ==> (ej:A->real^3)((e:num->real^3->A) k v) = phi v`
  ASSUME_TAC THENL
   [EXPAND_TAC "phi" THEN REWRITE_TAC[o_THM]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* open *)
    FIRST_ASSUM(MP_TAC o MATCH_MP MFD_PARAM_MAPS o check (let tE = `E:real^3->A` in fun th ->
      can (find_term (fun t -> t = tE)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_param")) (concl th))) THEN
    STRIP_TAC THEN
    MESON_TAC[ASSUME `open_in top (IMAGE (E:real^3->A) (annulus (&1) L))`;
              ASSUME `IMAGE (E:real^3->A) (annulus (&1) L) = Q`];
    (* connected *)
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `Q:A->bool` && is_comb(lhs(concl th)))) THEN
    MATCH_MP_TAC APX_PARAM_CONNECTED_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`;
                          `annulus (&1) L:real^3->bool`] THEN
    ASM_REWRITE_TAC[APX_CONNECTED_ANNULUS3; SUBSET_REFL];
    (* closure *)
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE ((e:num->real^3->A) k) Km` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
        EXPAND_TAC "Km" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
        X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(v:real^3) IN W /\ ~(v = vec 0) /\ &0 < apx_sval v /\
                      &0 < apx_sval((phi:real^3->real^3) v)` STRIP_ASSUME_TAC THENL
         [ASM_SIMP_TAC[]; ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE];
        MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC MFD_PARAM_COMPACT_IMAGE THEN
        MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom dl`] THEN
        ASM_REWRITE_TAC[] THEN EXPAND_TAC "Km" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
        ASM_SIMP_TAC[]];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `v:real^3` THEN
      EXPAND_TAC "Km" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      SUBGOAL_THEN `~(v:real^3 = vec 0) /\ ~((phi:real^3->real^3) v = vec 0)` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [UNDISCH_TAC `(v:real^3) IN W` THEN EXPAND_TAC "W" THEN SIMP_TAC[APX_SLAB_SVAL];
          FIRST_X_ASSUM(let tv = `vec 0:real^3`
                        and ts = `apx_slab (--inv(&2 * dl)) (inv(&2 * dl))`
                        and ti = `IMAGE:(real^3->A)->(real^3->bool)->A->bool` in
            fun th -> if is_forall(concl th) &&
              can (find_term (fun t -> t = tv)) (concl th) &&
              can (find_term (fun t -> t = ts)) (concl th)
              && not(can (find_term (fun t -> t = ti)) (concl th))
            then MATCH_MP_TAC th else failwith "no") THEN
          UNDISCH_TAC `(v:real^3) IN W` THEN
          UNDISCH_TAC `W SUBSET apx_slab (--inv(&2 * dl)) (inv(&2 * dl))` THEN SET_TAC[]];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(v:real^3) IN W`) o check
       (let tF = `Fs:real^3->real` and tK = `Km:real^3->bool` in fun th ->
        is_forall(concl th) && can (find_term (fun t -> t = tF)) (concl th) &&
        not (can (find_term (fun t -> t = tK)) (concl th)))) THEN
      STRIP_TAC THEN
      ASM_CASES_TAC `(Fs:real^3->real) v = &0` THENL
       [SUBGOAL_THEN `apx_sval(v:real^3) = &0` ASSUME_TAC THENL
         [MAP_EVERY UNDISCH_TAC
           [`(Fs:real^3->real) v = &0`; `&0 < (Fs:real^3->real) v <=> &0 < apx_sval(v:real^3)`;
            `&0 <= (Fs:real^3->real) v <=> &0 <= apx_sval(v:real^3)`] THEN
          REAL_ARITH_TAC;
          ALL_TAC] THEN
        REWRITE_TAC[IN_UNION] THEN DISJ2_TAC THEN DISJ1_TAC THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_SPHERE_0] THEN
        MESON_TAC[APX_TS_SVAL0; ASSUME `~(v:real^3 = vec 0)`; ASSUME `apx_sval(v:real^3) = &0`];
        ALL_TAC] THEN
      ASM_CASES_TAC `(Fs:real^3->real) v = apx_ts_dd c tau` THENL
       [SUBGOAL_THEN `apx_sval((phi:real^3->real^3) v) = &0` ASSUME_TAC THENL
         [MESON_TAC[ASSUME `(Fs:real^3->real) v = apx_ts_dd c tau`;
                    ASSUME `(Fs:real^3->real) v = apx_ts_dd c tau <=>
                            apx_sval((phi:real^3->real^3) v) = &0`];
          ALL_TAC] THEN
        REWRITE_TAC[IN_UNION] THEN DISJ2_TAC THEN DISJ2_TAC THEN
        SUBGOAL_THEN `(e:num->real^3->A) k v = e j ((phi:real^3->real^3) v)` SUBST1_TAC THENL
         [FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(v:real^3) IN W`) o check
           (let tn = `rfs_neck_dom dl` in fun th ->
              is_forall(concl th) && can (find_term (fun t -> t = tn)) (concl th))) THEN
          SIMP_TAC[];
          ALL_TAC] THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_SPHERE_0] THEN
        MESON_TAC[APX_TS_SVAL0; ASSUME `~((phi:real^3->real^3) v = vec 0)`;
                  ASSUME `apx_sval((phi:real^3->real^3) v) = &0`];
        ALL_TAC] THEN
      REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN EXPAND_TAC "Rm" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < (Fs:real^3->real) v /\ Fs v < apx_ts_dd c tau` MP_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`&0 <= (Fs:real^3->real) v`; `(Fs:real^3->real) v <= apx_ts_dd c tau`;
          `~((Fs:real^3->real) v = &0)`; `~((Fs:real^3->real) v = apx_ts_dd c tau)`] THEN
        REAL_ARITH_TAC;
        ASM_REWRITE_TAC[]]];
    (* disjoint from the sphere of e_k *)
    ASM_REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    X_GEN_TAC `p:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(v:real^3) IN W /\ ~(v = vec 0) /\ &0 < apx_sval v` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(w:real^3) IN rfs_neck_dom dl` ASSUME_TAC THENL
     [UNDISCH_TAC `(w:real^3) IN sphere(vec 0,&1)` THEN
      UNDISCH_TAC `sphere(vec 0:real^3,&1) SUBSET rfs_neck_dom dl` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(ek:A->real^3) p = v` ASSUME_TAC THENL
     [UNDISCH_TAC `p:A = (e:num->real^3->A) k v` THEN DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(ek:A->real^3) p = w` ASSUME_TAC THENL
     [UNDISCH_TAC `p:A = (e:num->real^3->A) k w` THEN DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `v:real^3 = w` SUBST_ALL_TAC THENL
     [MESON_TAC[ASSUME `(ek:A->real^3) p = v`; ASSUME `(ek:A->real^3) p = w`]; ALL_TAC] THEN
    SUBGOAL_THEN `apx_sval(w:real^3) = &0` MP_TAC THENL [ASM_SIMP_TAC[]; ASM_REAL_ARITH_TAC];
    (* disjoint from the sphere of e_j *)
    ASM_REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    X_GEN_TAC `p:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(v:real^3) IN W /\ ~(v = vec 0) /\ &0 < apx_sval((phi:real^3->real^3) v)`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(w:real^3) IN rfs_neck_dom dl` ASSUME_TAC THENL
     [UNDISCH_TAC `(w:real^3) IN sphere(vec 0,&1)` THEN
      UNDISCH_TAC `sphere(vec 0:real^3,&1) SUBSET rfs_neck_dom dl` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(ej:A->real^3) p = (phi:real^3->real^3) v` ASSUME_TAC THENL
     [UNDISCH_TAC `p:A = (e:num->real^3->A) k v` THEN DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(ej:A->real^3) p = w` ASSUME_TAC THENL
     [UNDISCH_TAC `p:A = (e:num->real^3->A) j w` THEN DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(phi:real^3->real^3) v = w` ASSUME_TAC THENL
     [MESON_TAC[ASSUME `(ej:A->real^3) p = (phi:real^3->real^3) v`; ASSUME `(ej:A->real^3) p = w`];
      ALL_TAC] THEN
    SUBGOAL_THEN `apx_sval(w:real^3) = &0` MP_TAC THENL
     [ASM_SIMP_TAC[];
      MESON_TAC[REAL_LT_REFL; ASSUME `&0 < apx_sval((phi:real^3->real^3) v)`;
                ASSUME `(phi:real^3->real^3) v = w`]];
    (* a point of P in Q *)
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    SUBGOAL_THEN `&4 / &3 % basis 1:real^3 IN apx_slab (&0) (sqrt(&2) * log(&3 / &2))`
    ASSUME_TAC THENL
     [REWRITE_TAC[APX_SLAB_SVAL; apx_sval; NORM_MUL] THEN
      SIMP_TAC[NORM_BASIS; BASIS_NONZERO; DIMINDEX_3; ARITH; VECTOR_MUL_EQ_0] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      SUBGOAL_THEN `&0 < sqrt(&2) /\ &0 < log(&4 / &3) /\ log(&4 / &3) < log(&3 / &2)`
      STRIP_ASSUME_TAC THENL
       [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH] THEN CONJ_TAC THENL
         [MATCH_MP_TAC LOG_POS_LT THEN REAL_ARITH_TAC;
          MATCH_MP_TAC LOG_MONO_LT_IMP THEN REAL_ARITH_TAC];
        ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_LMUL]];
      ALL_TAC] THEN
    EXPAND_TAC "Rm" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME
      `&4 / &3 % basis 1:real^3 IN apx_slab (&0) (sqrt(&2) * log(&3 / &2))`) o
      check (let tS = `apx_slab (&0) (sqrt(&2) * log(&3 / &2))` in fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = tS)) (concl th))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&4 / &3 % basis 1:real^3 IN apx_slab (&0) (sqrt(&2) * log(&3 / &2))` THEN
    SIMP_TAC[APX_SLAB_SVAL]]);;

(* No third cut sphere lies in the model region: it would be a section of  *)
(* the neck e_k (apx_ch_more, clause 3), and APX_TS_N4 applies.             *)

let APX_TS_THIRD = prove
 (`!top atlas (g:A->real^3^3) dl J (e:num->real^3->A) P j k m ek ej c K0 x1 tau E0 gg gg'
    Q.
     apx_tsh (top,atlas) g dl J e P j k /\ apx_ch_more top atlas g dl /\
     apx_tsg top atlas dl (e k) (e j) ek ej c K0 x1 tau E0 gg gg' /\
     Q = IMAGE (e k) {v | v IN apx_slab (-- &1) (tau + &2) /\ &0 < apx_sval v /\
                          &0 < apx_sval((ej o e k) v)} /\
     DISJOINT Q (IMAGE (e j) (sphere(vec 0,&1))) /\
     m IN J /\ ~(m = j) /\ ~(m = k) /\
     IMAGE (e m) (sphere(vec 0,&1)) SUBSET Q
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_TS_G_LEVELS) THEN
  UNDISCH_TAC `apx_tsg top atlas dl ((e:num->real^3->A) k) (e j) ek ej c K0 x1 tau E0 gg gg'` THEN
  REWRITE_TAC[apx_tsg] THEN STRIP_TAC THEN
  UNDISCH_TAC `apx_tsh (top,atlas) (g:A->real^3^3) dl J (e:num->real^3->A) P j k` THEN
  REWRITE_TAC[apx_tsh] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_RG0_BASICS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_RG0_PARTS) THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[apx_rg0] (ASSUME
    `apx_rg0 (top,atlas) (g:A->real^3^3) dl J (e:num->real^3->A) P`)) THEN
  ABBREV_TAC `phi = (ej:A->real^3) o (e:num->real^3->A) k` THEN
  ABBREV_TAC `W = apx_slab (-- &1) (tau + &2)` THEN
  ABBREV_TAC `Rm = {v | v IN W /\ &0 < apx_sval v /\ &0 < apx_sval((phi:real^3->real^3) v)}` THEN
  SUBGOAL_THEN `annulus (&1 / &2) (&2) SUBSET rfs_neck_dom dl /\
                sphere(vec 0:real^3,&1) SUBSET rfs_neck_dom dl` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `annulus (&1 / &2) (&2) SUBSET rfs_neck_dom dl` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(Rm:real^3->bool) SUBSET rfs_neck_dom dl` ASSUME_TAC THENL
   [EXPAND_TAC "Rm" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^3 t. v IN Rm /\ &1 < t * norm v /\ t <= &1 ==> t % v IN Rm` ASSUME_TAC THENL
   [EXPAND_TAC "Rm" THEN EXPAND_TAC "W" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`phi:real^3->real^3`; `c:real`; `K0:real`; `--inv(&2 * dl)`;
                   `inv(&2 * dl)`; `x1:real^3`; `tau:real`; `v:real^3`; `t:real`]
      APX_TS_MDL_RADIAL) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the third sphere is a section of e_k *)
  SUBGOAL_THEN `?yk ym. rfs_neck (top,atlas) (g:A->real^3^3) dl yk ((e:num->real^3->A) k) /\
                        rfs_neck (top,atlas) g dl ym (e m)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE ((e:num->real^3->A) m) (sphere(vec 0,&1)) SUBSET
                IMAGE (e k) (rfs_neck_dom dl)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `Q:A->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `apx_ch_more top atlas (g:A->real^3^3) dl` THEN REWRITE_TAC[apx_ch_more] THEN
  DISCH_THEN(MP_TAC o SPECL [`yk:A`; `(e:num->real^3->A) k`; `ym:A`; `(e:num->real^3->A) m`] o
    CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP APX_SECTION_DATA) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x:real^3. x IN sphere(vec 0,&1)
                ==> &0 < u x /\ norm(u x % x) = u x /\ u x % x IN rfs_neck_dom dl`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `exp(--inv dl / sqrt(&2)) < (u:real^3->real) x /\
                  u x < exp(inv dl / sqrt(&2))` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (u:real^3->real) x` ASSUME_TAC THENL
     [MP_TAC(SPEC `--inv dl / sqrt(&2)` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `norm((u:real^3->real) x % x) = u x` ASSUME_TAC THENL
     [UNDISCH_TAC `x IN sphere(vec 0:real^3,&1)` THEN
      REWRITE_TAC[IN_SPHERE_0; NORM_MUL] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[APX_SLAB_NECK_DOM; apx_slab; annulus; IN_ELIM_THM] THEN
    REWRITE_TAC[real_div; REAL_MUL_LNEG] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN sphere(vec 0,&1) ==> u x % x IN Rm` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(e:num->real^3->A) k (u x % x) IN Q` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        is_comb(concl th) && rand(concl th) = `Q:A->bool`)) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:real^3` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(u:real^3->real) x % x = v` (fun th -> ASM_REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `(u:real^3->real) x % x IN rfs_neck_dom dl /\ (v:real^3) IN rfs_neck_dom dl`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN sphere(vec 0,&1) ==> &2 <= u x` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < (u:real^3->real) x /\ norm(u x % x) = u x /\ u x % x IN rfs_neck_dom dl /\
                  u x % x IN Rm` STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&1 < (u:real^3->real) x` ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 < apx_sval((u:real^3->real) x % x)` MP_TAC THENL
       [UNDISCH_TAC `(u:real^3->real) x % x IN Rm` THEN EXPAND_TAC "Rm" THEN
        SIMP_TAC[IN_ELIM_THM];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[apx_sval] THEN
      SUBGOAL_THEN `&0 < sqrt(&2)` (fun th -> SIMP_TAC[th; REAL_LT_MUL_EQ]) THENL
       [SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
      MP_TAC(SPECL [`&1`; `(u:real^3->real) x`] LOG_MONO_LT) THEN
      ASM_REWRITE_TAC[REAL_LT_01; LOG_1] THEN SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(e:num->real^3->A) k (u x % x) IN IMAGE (e k) (annulus (&1 / &2) (&2)) /\
                  e k (u x % x) IN IMAGE (e m) (annulus (&1 / &2) (&2))` MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN
        ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `(e:num->real^3->A) k (u x % x) IN IMAGE (e m) (sphere(vec 0,&1))`
        MP_TAC THENL
         [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:real^3` THEN
          ASM_REWRITE_TAC[];
          MATCH_MP_TAC(SET_RULE `!f s t x. s SUBSET t ==> (x:A) IN IMAGE (f:real^3->A) s ==> x IN IMAGE f t`) THEN
          REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC]];
      ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `!a b x. DISJOINT a b ==> (x:A) IN a /\ x IN b ==> F`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN sphere(vec 0,&1)
                ==> &0 < u x /\ u x <= exp(inv dl / sqrt(&2)) /\ u x % x IN Rm`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&2 <= (u:real^3->real) x /\ u x < exp(inv dl / sqrt(&2)) /\ u x % x IN Rm`
    MP_TAC THENL
     [ASM_SIMP_TAC[]; STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(j:num = m) /\ ~(k:num = m)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(m:num = j)` THEN UNDISCH_TAC `~(m:num = k)` THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i IN J ==> DISJOINT P (IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_neck_chart")) (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT P (IMAGE ((e:num->real^3->A) k) (sphere(vec 0,&1))) /\
                DISJOINT P (IMAGE (\x. (e:num->real^3->A) k (u x % x)) (sphere(vec 0,&1)))`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      can (find_term (fun t -> t = `u:real^3->real`)) (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~DISJOINT P (IMAGE ((e:num->real^3->A) k)
                   {v | &1 < norm v /\ norm v < u(inv(norm v) % v)})` ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; NOT_FORALL_THM] THEN
    EXISTS_TAC `(e:num->real^3->A) k (&4 / &3 % basis 1)` THEN
    CONJ_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `&4 / &3 % basis 1:real^3`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_ELIM_THM] THEN
    SUBGOAL_THEN `basis 1 IN sphere(vec 0:real^3,&1) /\ norm(&4 / &3 % basis 1:real^3) = &4 / &3 /\
                  inv(norm(&4 / &3 % basis 1:real^3)) % (&4 / &3 % basis 1:real^3) =
                  basis 1:real^3`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[IN_SPHERE_0; NORM_MUL] THEN
      SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH; VECTOR_MUL_ASSOC] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[VECTOR_MUL_LID];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&2 <= (u:real^3->real)(basis 1)` MP_TAC THENL
     [ASM_SIMP_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE ((e:num->real^3->A) j) (sphere(vec 0,&1)) SUBSET top closure_of P /\
                ~(IMAGE ((e:num->real^3->A) j) (sphere(vec 0,&1)) = {})` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `p:A` THEN DISCH_TAC THEN DISJ2_TAC THEN
      EXISTS_TAC `IMAGE ((e:num->real^3->A) j) (sphere(vec 0,&1))` THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IMAGE_EQ_EMPTY] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `basis 1:real^3` THEN
      SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH]];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (IMAGE ((e:num->real^3->A) j) (sphere(vec 0,&1)))
                         (IMAGE (e k) (sphere(vec 0,&1))) /\
                DISJOINT (IMAGE ((e:num->real^3->A) j) (sphere(vec 0,&1)))
                         (IMAGE (\x. e k (u x % x)) (sphere(vec 0,&1))) /\
                DISJOINT (IMAGE ((e:num->real^3->A) j) (sphere(vec 0,&1))) (IMAGE (e k) Rm)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC APX_TS_SPHERES_DISJOINT THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `g:A->real^3^3`; `dl:real`; `J:num->bool`; `P:A->bool`] THEN
      ASM_REWRITE_TAC[];
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        can (find_term (fun t -> t = `u:real^3->real`)) (concl th))) THEN
      MATCH_MP_TAC APX_TS_SPHERES_DISJOINT THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                            `g:A->real^3^3`; `dl:real`; `J:num->bool`; `P:A->bool`] THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `DISJOINT Q (IMAGE ((e:num->real^3->A) j) (sphere(vec 0,&1)))` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `rfs_neck_dom dl`;
                 `(e:num->real^3->A) k`; `Rm:real^3->bool`; `u:real^3->real`;
                 `exp(inv dl / sqrt(&2))`; `P:A->bool`;
                 `IMAGE ((e:num->real^3->A) j) (sphere(vec 0,&1))`] APX_TS_N4) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]]);;

(* The topology of the tight shell: the region P is the model region Q and *)
(* J consists of the two cut spheres j, k only.                            *)

let APX_TS_TOPO = prove
 (`!top atlas (g:A->real^3^3) dl J (e:num->real^3->A) P j k ek ej c K0 x1 tau E0 gg gg'
    E L Q.
     apx_tsh (top,atlas) g dl J e P j k /\ apx_ch_more top atlas g dl /\
     apx_tsg top atlas dl (e k) (e j) ek ej c K0 x1 tau E0 gg gg' /\
     mfd_param top atlas (annulus (&1) L) E /\
     Q = IMAGE (e k) {v | v IN apx_slab (-- &1) (tau + &2) /\ &0 < apx_sval v /\
                          &0 < apx_sval((ej o e k) v)} /\
     IMAGE E (annulus (&1) L) = Q
     ==> J = {j,k} /\ P = Q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `Q:A->bool`)) THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                `dl:real`; `J:num->bool`; `e:num->real^3->A`; `P:A->bool`; `j:num`; `k:num`;
                `ek:A->real^3`; `ej:A->real^3`; `c:real`; `K0:real`; `x1:real^3`; `tau:real`;
                `E0:real^3->A`; `gg:real^3->real^3`; `gg':real^3->real^3`; `E:real^3->A`;
                `L:real`; `Q:A->bool`] APX_TS_Q_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[apx_tsh] (ASSUME
    `apx_tsh (top,atlas) (g:A->real^3^3) dl J (e:num->real^3->A) P j k`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_RG0_BASICS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP APX_RG0_PARTS) THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[apx_rg0] (ASSUME
    `apx_rg0 (top,atlas) (g:A->real^3^3) dl J (e:num->real^3->A) P`)) THEN
  ABBREV_TAC `Sk = IMAGE ((e:num->real^3->A) k) (sphere(vec 0,&1))` THEN
  ABBREV_TAC `Sj = IMAGE ((e:num->real^3->A) j) (sphere(vec 0,&1))` THEN
  SUBGOAL_THEN `!i. i IN J ==> DISJOINT P (IMAGE ((e:num->real^3->A) i) (sphere(vec 0,&1)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_neck_chart")) (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT P (Sk:A->bool) /\ DISJOINT P (Sj:A->bool) /\
                (e:num->real^3->A) k (&4 / &3 % basis 1) IN P`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Sk"; "Sj"] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  (* P is contained in Q *)
  SUBGOAL_THEN `P INTER Q = P:A->bool` ASSUME_TAC THENL
   [MATCH_MP_TAC APX_CONNECTED_CLOPEN_EQ THEN EXISTS_TAC `top:A topology` THEN
    ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `(e:num->real^3->A) k (&4 / &3 % basis 1)` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `top closure_of (P INTER Q) SUBSET Q UNION Sk UNION (Sj:A->bool)` MP_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `top closure_of (Q:A->bool)` THEN
      ASM_SIMP_TAC[CLOSURE_OF_MONO; INTER_SUBSET];
      MAP_EVERY UNDISCH_TAC [`DISJOINT P (Sk:A->bool)`; `DISJOINT P (Sj:A->bool)`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `P SUBSET (Q:A->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `P INTER Q = P:A->bool` THEN SET_TAC[]; ALL_TAC] THEN
  (* no third sphere *)
  SUBGOAL_THEN `!m:num. m IN J ==> m = j \/ m = k` ASSUME_TAC THENL
   [X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `m:num = j` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `m:num = k` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                  `dl:real`; `J:num->bool`; `e:num->real^3->A`; `P:A->bool`; `j:num`; `k:num`;
                  `m:num`; `ek:A->real^3`; `ej:A->real^3`; `c:real`; `K0:real`; `x1:real^3`;
                  `tau:real`; `E0:real^3->A`; `gg:real^3->real^3`; `gg':real^3->real^3`;
                  `Q:A->bool`] APX_TS_THIRD) THEN
    REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `IMAGE ((e:num->real^3->A) m) (sphere(vec 0,&1)) SUBSET top closure_of P /\
                  DISJOINT (IMAGE ((e:num->real^3->A) m) (sphere(vec 0,&1))) Sk /\
                  DISJOINT (IMAGE ((e:num->real^3->A) m) (sphere(vec 0,&1))) Sj`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN
        X_GEN_TAC `p:A` THEN DISCH_TAC THEN DISJ2_TAC THEN
        EXISTS_TAC `IMAGE ((e:num->real^3->A) m) (sphere(vec 0,&1))` THEN
        ASM_REWRITE_TAC[] THEN EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[];
        EXPAND_TAC "Sk" THEN MATCH_MP_TAC APX_TS_SPHERES_DISJOINT THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                              `g:A->real^3^3`; `dl:real`; `J:num->bool`; `P:A->bool`] THEN
        ASM_REWRITE_TAC[];
        EXPAND_TAC "Sj" THEN MATCH_MP_TAC APX_TS_SPHERES_DISJOINT THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                              `g:A->real^3^3`; `dl:real`; `J:num->bool`; `P:A->bool`] THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `top closure_of P SUBSET Q UNION Sk UNION (Sj:A->bool)` MP_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `top closure_of (Q:A->bool)` THEN
      ASM_SIMP_TAC[CLOSURE_OF_MONO];
      MAP_EVERY UNDISCH_TAC
       [`IMAGE ((e:num->real^3->A) m) (sphere(vec 0,&1)) SUBSET top closure_of P`;
        `DISJOINT (IMAGE ((e:num->real^3->A) m) (sphere(vec 0,&1))) Sk`;
        `DISJOINT (IMAGE ((e:num->real^3->A) m) (sphere(vec 0,&1))) Sj`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `J = {j:num,k}` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN X_GEN_TAC `m:num` THEN
    EQ_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "connected_in")) (concl th))) THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONJ_TAC THENL
   [REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `(e:num->real^3->A) k (&4 / &3 % basis 1)` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The tight-shell lemma APX_TIGHT_SHELL (thresholds from the                 *)
(* smooth-step derivative bound, the alignment, chain-context and          *)
(* apx_ch_more thresholds; data, product, gluing and topology), and the     *)
(* region theorem APX_REGION by APX_REGION_FROM_TIGHT.                      *)
(* ------------------------------------------------------------------------- *)

(* The tight-shell lemma. *)

let APX_TIGHT_SHELL = prove
 (`!u:A->bool. APX_TIGHT_SHELL_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[APX_TIGHT_SHELL_STATEMENT] THEN
  X_CHOOSE_THEN `Ds:real->real` (X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC)
    APX_SMOOTH_STEP_DERIV THEN
  ABBREV_TAC `K0 = min (&1 / &1000) (inv(&200 * (C + &1)))` THEN
  SUBGOAL_THEN `&0 < K0 /\ K0 <= &1 / &1000 /\ K0 <= inv(&200 * (C + &1)) /\ K0 <= &1`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K0" THEN
    SUBGOAL_THEN `&0 < inv(&200 * (C + &1))` MP_TAC THENL
     [REWRITE_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPEC `K0:real` (INST_TYPE [`:A`,`:A`] APX_TS_ALIGN_HOLDS)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "align"))) THEN
  X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ctx"))
    (INST_TYPE [`:A`,`:A`] APX_CH_CTX_HOLDS) THEN
  X_CHOOSE_THEN `e3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "more"))
    (INST_TYPE [`:A`,`:A`] APX_CH_MORE_HOLDS) THEN
  EXISTS_TAC `min (&1 / &1000) (min e1 (min (e2 / &2) e3))` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `g:A->real^3^3`; `dl:real`; `J:num->bool`; `e:num->real^3->A`;
                       `P:A->bool`; `j:num`; `k:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `dl <= &1 / &1000 /\ dl <= e1 /\ &2 * dl <= e2 /\ dl <= e3`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `apx_tsh (top,atlas) (g:A->real^3^3) dl J (e:num->real^3->A) P j k`
  ASSUME_TAC THENL
   [REWRITE_TAC[apx_tsh; apx_rg0] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `apx_tsr top atlas (g:A->real^3^3) dl K0` ASSUME_TAC THENL
   [REWRITE_TAC[apx_tsr] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "ctx" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                      `g:A->real^3^3`; `dl:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "ctx" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                      `g:A->real^3^3`; `&2 * dl`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "more" (MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                                       `g:A->real^3^3`; `dl:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      MAP_EVERY X_GEN_TAC [`x:A`; `ea:real^3->A`; `x':A`; `eb:real^3->A`; `ei:A->real^3`;
                           `v:real^3`] THEN
      STRIP_TAC THEN USE_THEN "align" MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `dl:real`; `ea:real^3->A`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                `dl:real`; `J:num->bool`; `e:num->real^3->A`; `P:A->bool`; `j:num`; `k:num`;
                `K0:real`] APX_TS_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ek:A->real^3` (X_CHOOSE_THEN `ej:A->real^3`
    (X_CHOOSE_THEN `xk:A` (X_CHOOSE_THEN `xj:A` (X_CHOOSE_THEN `x1:real^3`
    (X_CHOOSE_THEN `tau:real` STRIP_ASSUME_TAC)))))) THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                `dl:real`; `J:num->bool`; `e:num->real^3->A`; `P:A->bool`; `j:num`; `k:num`;
                `K0:real`; `ek:A->real^3`; `ej:A->real^3`; `xk:A`; `xj:A`; `x1:real^3`;
                `tau:real`; `Ds:real->real`; `C:real`] APX_TS_PRODUCT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `E0:real^3->A` (X_CHOOSE_THEN `gg:real^3->real^3`
    (X_CHOOSE_THEN `gg':real^3->real^3` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `c = sqrt(mfd_scalar atlas (g:A->real^3^3) xj / mfd_scalar atlas g xk)` THEN
  SUBGOAL_THEN `apx_tsg top atlas dl ((e:num->real^3->A) k) (e j) ek ej c K0 x1 tau E0 gg gg'`
  ASSUME_TAC THENL
   [REWRITE_TAC[apx_tsg] THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP APX_RG0_BASICS o CONJUNCT1 o REWRITE_RULE[apx_tsh]) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `E:real^3->A` STRIP_ASSUME_TAC o MATCH_MP APX_TS_GLUE) THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                `dl:real`; `J:num->bool`; `e:num->real^3->A`; `P:A->bool`; `j:num`; `k:num`;
                `ek:A->real^3`; `ej:A->real^3`; `c:real`; `K0:real`; `x1:real^3`; `tau:real`;
                `E0:real^3->A`; `gg:real^3->real^3`; `gg':real^3->real^3`; `E:real^3->A`;
                `exp(apx_ts_dd c tau / sqrt(&2))`;
                `IMAGE ((e:num->real^3->A) k)
                   {v | v IN apx_slab (-- &1) (tau + &2) /\ &0 < apx_sval v /\
                        &0 < apx_sval(((ej:A->real^3) o e k) v)}`] APX_TS_TOPO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    USE_THEN "more" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  MAP_EVERY EXISTS_TAC [`E:real^3->A`; `exp(apx_ts_dd c tau / sqrt(&2))`;
                        `gg:real^3->real^3`; `gg':real^3->real^3`] THEN
  ASM_REWRITE_TAC[]);;

(* The REGION theorem. *)

let APX_REGION = prove
 (`!u:A->bool. APX_REGION_STATEMENT u`,
  GEN_TAC THEN MATCH_MP_TAC APX_REGION_FROM_TIGHT THEN REWRITE_TAC[APX_TIGHT_SHELL]);;

