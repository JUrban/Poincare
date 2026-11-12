(* ========================================================================= *)
(* pc_sch_level2: two facts about the regular levels of a Morse neck,        *)
(* SCH4L_LEVEL_NECK |- SCH_LEVEL_NECK_STATEMENT and SCH4L_LEVEL_INNERMOST |- *)
(* SCH_LEVEL_INNERMOST_STATEMENT. SCH_LEVEL_NECK: a component of a regular   *)
(* level of a Morse neck is a planar neck circle at height a (the planar     *)
(* lemma SCH4N_PLANAR_NECK for phi(z) = |g'(z,a)|^2 - 1).                    *)
(* SCH_LEVEL_INNERMOST: a component minimal for "inside" has no point of the *)
(* sphere over its inside (nesting of Jordan curves, finitely many           *)
(* components).                                                              *)
(* ========================================================================= *)

needs "src/pc_sch_lcirc.ml";;
needs "src/pc_sch_level.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* SCH_LEVEL_NECK.                                                           *)
(* ------------------------------------------------------------------------- *)

let SCH4L_AT_DERIV = prove
 (`!a z. (sch5v_at a has_derivative sch5v_at (&0)) (at z) /\ linear (sch5v_at (&0))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `linear (sch5v_at (&0))` ASSUME_TAC THENL
   [REWRITE_TAC[linear; sch5v_at] THEN
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
             VECTOR_MUL_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `sch5v_at a = \z. sch5v_at (&0) z + vector[&0; &0; a]` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; sch5v_at] THEN
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(sch5v_at (&0) has_derivative sch5v_at (&0)) (at z) /\
                ((\z:real^2. vector[&0; &0; a]:real^3) has_derivative (\h. vec 0)) (at z)`
  MP_TAC THENL [ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR; HAS_DERIVATIVE_CONST]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_DERIVATIVE_ADD) THEN REWRITE_TAC[VECTOR_ADD_RID; ETA_AX]);;

let SCH4L_PLANAR_SETUP = prove
 (`!(g:real^3->real^3) g' a C d0.
     sch_neck g g' /\ (!t. sch_crit g t ==> ~((g t)$3 = a)) /\
     C IN components(sch_level g a) /\ compact C /\ ~(C = {}) /\
     C SUBSET sch5v_oh g g' /\
     (!x. x IN C ==> x$3 = a /\ x IN IMAGE g (sphere(vec 0,&1))) /\
     &0 < d0 /\
     (!x y. x IN sch_level g a /\ ~(x IN C) /\ y IN C ==> d0 <= dist(x,y))
     ==> sch4n_setup (\z:real^2. norm(g'(sch5v_at a z)) pow 2 - &1)
                     (\z:real^2. sch5v_pr(sch5v_grad g' (sch5v_at a z)))
                     {z:real^2 | sch5v_at a z IN IMAGE g (annulus (&1 / &2) (&2))}
                     (IMAGE sch5v_pr C) d0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`] SCH5V_NECK_OPEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`] SCH5V_GRAD_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC SCH5V_PR_AT_SMOOTH THEN STRIP_TAC THEN
  MP_TAC SCH5V_PR_AT THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x:real^3. x IN C ==> x IN IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2)) /\
                                     sch5v_at a (sch5v_pr x) = x`
  (LABEL_TAC "CX") THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o check (fun th ->
      can (term_match [] `!x:real^3. x IN C ==> x$3 = a /\ P x`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN IMAGE (g:real^3->real^3) (sphere(vec 0,&1))` THEN
      MATCH_MP_TAC(SET_RULE `s SUBSET t ==> x IN IMAGE (f:real^3->real^3) s ==> x IN IMAGE f t`) THEN
      REWRITE_TAC[SUBSET; SCH5_SPHERE_IN_ANNULUS];
      UNDISCH_TAC `(x:real^3)$3 = a` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[SCH5V_PR_AT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open {z:real^2 | sch5v_at a z IN IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2))}`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `{z:real^2 | sch5v_at a z IN IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2))} =
                  {z | z IN (:real^2) /\ sch5v_at a z IN IMAGE g (annulus (&1 / &2) (&2))}`
    SUBST1_TAC THENL [REWRITE_TAC[IN_UNIV]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[OPEN_UNIV; ETA_AX];
    ALL_TAC] THEN
  REWRITE_TAC[sch4n_setup] THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    SUBGOAL_THEN `(\z:real^2. sch5v_pr(sch5v_grad (g':real^3->real^3) (sch5v_at a z))) =
                  sch5v_pr o (sch5v_grad g' o sch5v_at a)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2))` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV]];
    X_GEN_TAC `z:real^2` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `sch5v_at a z`]
      SCH5V_RHO_HAS_DERIVATIVE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`a:real`; `z:real^2`] SCH4L_AT_DERIV) THEN STRIP_TAC THEN
    SUBGOAL_THEN `((\z:real^2. lift(norm((g':real^3->real^3)(sch5v_at a z)) pow 2)) has_derivative
                   (\h. lift(sch5v_grad g' (sch5v_at a z) dot sch5v_at (&0) h))) (at z)`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `(\z:real^2. lift(norm((g':real^3->real^3)(sch5v_at a z)) pow 2)) =
                    (\y. lift(norm(g' y) pow 2)) o sch5v_at a` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      SUBGOAL_THEN `(\h. lift(sch5v_grad (g':real^3->real^3) (sch5v_at a z) dot sch5v_at (&0) h)) =
                    (\v. lift(sch5v_grad g' (sch5v_at a z) dot v)) o sch5v_at (&0)`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `!h. sch5v_grad (g':real^3->real^3) (sch5v_at a z) dot sch5v_at (&0) h =
                      sch5v_pr(sch5v_grad g' (sch5v_at a z)) dot h` ASSUME_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[sch5v_at; sch5v_pr; DOT_3; DOT_2; VECTOR_3; VECTOR_2] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\z:real^2. lift(norm((g':real^3->real^3)(sch5v_at a z)) pow 2)`;
                   `\h. lift(sch5v_grad (g':real^3->real^3) (sch5v_at a z) dot sch5v_at (&0) h)`;
                   `\z:real^2. lift(&1)`; `\h:real^2. vec 0:real^1`; `at (z:real^2)`]
      HAS_DERIVATIVE_SUB) THEN
    ASM_REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
    REWRITE_TAC[VECTOR_SUB_RZERO; GSYM LIFT_SUB];
    MATCH_MP_TAC COMPACT_LINEAR_IMAGE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONNECTED_LINEAR_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IN_COMPONENTS_CONNECTED THEN
    EXISTS_TAC `sch_level (g:real^3->real^3) a` THEN FIRST_ASSUM ACCEPT_TAC;
    ASM_REWRITE_TAC[IMAGE_EQ_EMPTY];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN
    DISCH_TAC THEN USE_THEN "CX" (fun th -> ASM_SIMP_TAC[th]);
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    USE_THEN "CX" (fun th -> ASM_SIMP_TAC[th]) THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `x:real^3`] SCH5V_IN_SURFACE) THEN
      USE_THEN "CX" (fun th -> ASM_SIMP_TAC[th]) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o check (fun th ->
        can (term_match [] `!x:real^3. x IN C ==> x$3 = a /\ P x`) (concl th))) THEN
      ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `(x:real^3) IN sch5v_oh g g'` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[sch5v_oh; IN_ELIM_THM; sch5v_pr] THEN
      SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VEC_COMPONENT] THEN
      STRIP_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
      UNDISCH_TAC `~((sch5v_grad (g':real^3->real^3) x)$1 pow 2 +
                     (sch5v_grad g' x)$2 pow 2 = &0)` THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV];
    FIRST_ASSUM ACCEPT_TAC;
    MAP_EVERY X_GEN_TAC [`z:real^2`; `y:real^2`] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `y':real^3` STRIP_ASSUME_TAC o REWRITE_RULE[IN_IMAGE])
        ASSUME_TAC))) THEN
    REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `sch5v_at a (z:real^2)` THEN REWRITE_TAC[SCH5V_PR_AT] THEN
    SUBGOAL_THEN `sch5v_at a (z:real^2) IN sch_level (g:real^3->real^3) a` ASSUME_TAC THENL
     [REWRITE_TAC[SCH4_LEVEL_EQ; IN_INTER; IN_ELIM_THM; SCH5V_PR_AT] THEN
      MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `sch5v_at a (z:real^2)`]
        SCH5V_IN_SURFACE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `norm((g':real^3->real^3)(sch5v_at a z)) pow 2 - &1 = &0` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `sch5v_at a (z:real^2) IN C` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> if can (term_match []
        `!x y:real^3. x IN sch_level (g:real^3->real^3) a /\ ~(x IN C) /\ y IN C
                      ==> d0 <= dist(x,y)`) (concl th)
      then MP_TAC(MATCH_MP (SPECL [`sch5v_at a (z:real^2)`; `y':real^3`] th)
             (CONJ (ASSUME `sch5v_at a (z:real^2) IN sch_level (g:real^3->real^3) a`)
               (CONJ (ASSUME `~(sch5v_at a (z:real^2) IN C)`) (ASSUME `(y':real^3) IN C`))))
      else failwith "D0") THEN
    SUBGOAL_THEN `dist(sch5v_at a (z:real^2), y':real^3) = dist(z,y)` SUBST1_TAC THENL
     [USE_THEN "CX" (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
        [GSYM(CONJUNCT2(MATCH_MP th (ASSUME `(y':real^3) IN C`)))]) THEN
      ASM_REWRITE_TAC[SCH5V_PR_AT];
      ALL_TAC] THEN
    UNDISCH_TAC `dist(z:real^2,y) < d0` THEN REAL_ARITH_TAC]);;

(* The statement SCH_LEVEL_NECK: the planar lemma applied to                *)
(* phi(z) = |g'(z,a)|^2 - 1 and K = pr C, then C is the lift of pr C.       *)

let SCH4L_LEVEL_NECK = prove
 (`SCH_LEVEL_NECK_STATEMENT`,
  REWRITE_TAC[SCH_LEVEL_NECK_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `C:real^3->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(components(sch_level (g:real^3->real^3) a))` ASSUME_TAC THENL
   [MP_TAC SCH_LEVEL_FINITE THEN REWRITE_TAC[SCH_LEVEL_FINITE_STATEMENT] THEN
    DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `g':real^3->real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `C:real^3->bool`]
    SCH5V_LEVEL_COMPONENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC)))))) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `C:real^3->bool`; `d0:real`]
    SCH4L_PLANAR_SETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SCH4N_PLANAR_NECK) THEN
  DISCH_THEN(X_CHOOSE_THEN `Fn:real^2->real^2` (X_CHOOSE_THEN `Fn':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`Fn:real^2->real^2`; `Fn':real^2->real^2`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\x:real^2. vector[(Fn x)$1; (Fn x)$2; a]:real^3) = sch5v_at a o Fn`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; sch5v_at]; ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM IMAGE_o] THEN
  MATCH_MP_TAC(SET_RULE `(!x:real^3. x IN C ==> (f:real^3->real^3) x = x) ==> C = IMAGE f C`) THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN `(x:real^3)$3 = a` (SUBST1_TAC o SYM) THENL
   [ASM_MESON_TAC[]; REWRITE_TAC[SCH5V_PR_AT]]);;

(* ------------------------------------------------------------------------- *)
(* SCH_LEVEL_INNERMOST.  The relation "pr C' lies inside pr C"               *)
(* on the finitely many components is irreflexive and transitive           *)
(* (INSIDE_INSIDE_COMPACT_CONNECTED), so it has a minimal element; a point  *)
(* of the sphere at height a over the inside of a minimal pr C would lie on *)
(* a component C' with pr C' inside pr C.                                   *)
(* ------------------------------------------------------------------------- *)

let SCH4L_PR_INJ = prove
 (`!u v:real^3. u$3 = v$3 /\ sch5v_pr u = sch5v_pr v ==> u = v`,
  REWRITE_TAC[sch5v_pr; CART_EQ; DIMINDEX_2; DIMINDEX_3; FORALL_2; FORALL_3; VECTOR_2] THEN
  MESON_TAC[]);;

let SCH4L_LEVEL_INNERMOST = prove
 (`SCH_LEVEL_INNERMOST_STATEMENT`,
  REWRITE_TAC[SCH_LEVEL_INNERMOST_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\y:real^3. vector[y$1; y$2]:real^2) = sch5v_pr` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; sch5v_pr]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2. vector[x$1; x$2; a]:real^3 = sch5v_at a x`
  (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[sch5v_at]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(components(sch_level (g:real^3->real^3) a))` ASSUME_TAC THENL
   [MP_TAC SCH_LEVEL_FINITE THEN REWRITE_TAC[SCH_LEVEL_FINITE_STATEMENT] THEN
    DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `g':real^3->real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!C. C IN components(sch_level (g:real^3->real^3) a)
                    ==> compact(IMAGE sch5v_pr C) /\ connected(IMAGE sch5v_pr C) /\
                        ~(IMAGE sch5v_pr C = {}) /\ (!x:real^3. x IN C ==> x$3 = a)`
  (LABEL_TAC "CF") THENL
   [X_GEN_TAC `C:real^3->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `C:real^3->bool`]
      SCH5V_LEVEL_COMPONENT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_LINEAR_IMAGE THEN ASM_REWRITE_TAC[SCH5V_PR_AT_SMOOTH];
      MATCH_MP_TAC CONNECTED_LINEAR_IMAGE THEN REWRITE_TAC[SCH5V_PR_AT_SMOOTH] THEN
      MATCH_MP_TAC IN_COMPONENTS_CONNECTED THEN
      EXISTS_TAC `sch_level (g:real^3->real^3) a` THEN FIRST_ASSUM ACCEPT_TAC;
      ASM_REWRITE_TAC[IMAGE_EQ_EMPTY];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!C C'. C IN components(sch_level (g:real^3->real^3) a) /\
                       C' IN components(sch_level g a) /\ ~(C = C')
                       ==> IMAGE sch5v_pr C INTER IMAGE sch5v_pr C' = {}` (LABEL_TAC "DJ") THENL
   [MAP_EVERY X_GEN_TAC [`C:real^3->bool`; `C':real^3->bool`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `C INTER C' = {}:real^3->bool` MP_TAC THENL
     [ASM_MESON_TAC[COMPONENTS_NONOVERLAP]; ALL_TAC] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    DISCH_TAC THEN X_GEN_TAC `z:real^2` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(u:real^3)$3 = a /\ (v:real^3)$3 = a` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(u:real^3) = v` ASSUME_TAC THENL
     [MATCH_MP_TAC SCH4L_PR_INJ THEN ASM_MESON_TAC[]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `WF (\C' C:real^3->bool. C' IN components(sch_level (g:real^3->real^3) a) /\
                                         C IN components(sch_level g a) /\
                                         IMAGE sch5v_pr C' SUBSET inside(IMAGE sch5v_pr C))`
  MP_TAC THENL
   [MATCH_MP_TAC WF_FINITE THEN REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `C:real^3->bool` THEN STRIP_TAC THEN
      USE_THEN "CF" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
        (ASSUME `(C:real^3->bool) IN components(sch_level (g:real^3->real^3) a)`))) THEN
      MP_TAC(ISPEC `IMAGE sch5v_pr (C:real^3->bool)` INSIDE_NO_OVERLAP) THEN
      UNDISCH_TAC `IMAGE sch5v_pr (C:real^3->bool) SUBSET inside(IMAGE sch5v_pr C)` THEN
      UNDISCH_TAC `~(IMAGE sch5v_pr (C:real^3->bool) = {})` THEN SET_TAC[];
      MAP_EVERY X_GEN_TAC [`C1:real^3->bool`; `C2:real^3->bool`; `C3:real^3->bool`] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `inside(IMAGE sch5v_pr (C2:real^3->bool))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INSIDE_INSIDE_COMPACT_CONNECTED THEN
      USE_THEN "CF" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
        (ASSUME `(C2:real^3->bool) IN components(sch_level (g:real^3->real^3) a)`))) THEN
      USE_THEN "CF" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
        (ASSUME `(C3:real^3->bool) IN components(sch_level (g:real^3->real^3) a)`))) THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
      X_GEN_TAC `C:real^3->bool` THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `components(sch_level (g:real^3->real^3) a)` THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[SUBSET; IN_ELIM_THM]];
    ALL_TAC] THEN
  REWRITE_TAC[WF] THEN
  DISCH_THEN(MP_TAC o SPEC `\C:real^3->bool. C IN components(sch_level (g:real^3->real^3) a)`) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[MEMBER_NOT_EMPTY; COMPONENTS_EQ_EMPTY]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "MIN"))) THEN
  EXISTS_TAC `C:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `?C'. C' IN components(sch_level (g:real^3->real^3) a) /\ sch5v_at a (x:real^2) IN C'`
  (X_CHOOSE_THEN `C':real^3->bool` STRIP_ASSUME_TAC) THENL
   [REWRITE_TAC[GSYM IN_UNIONS; GSYM UNIONS_COMPONENTS] THEN
    REWRITE_TAC[SCH4_LEVEL_EQ; IN_INTER; IN_ELIM_THM; SCH5V_PR_AT] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^2) IN IMAGE sch5v_pr (C':real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `sch5v_at a (x:real^2)` THEN
    ASM_REWRITE_TAC[SCH5V_PR_AT];
    ALL_TAC] THEN
  ASM_CASES_TAC `C':real^3->bool = C` THENL
   [UNDISCH_TAC `(x:real^2) IN IMAGE sch5v_pr (C':real^3->bool)` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^2) IN inside(IMAGE sch5v_pr (C:real^3->bool))` THEN
    MP_TAC(ISPEC `IMAGE sch5v_pr (C:real^3->bool)` INSIDE_NO_OVERLAP) THEN SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "MIN" (MP_TAC o SPEC `C':real^3->bool`) THEN
  REWRITE_TAC[ASSUME `(C':real^3->bool) IN components(sch_level (g:real^3->real^3) a)`;
              ASSUME `(C:real^3->bool) IN components(sch_level (g:real^3->real^3) a)`] THEN
  MP_TAC(ISPECL [`IMAGE sch5v_pr (C:real^3->bool)`; `IMAGE sch5v_pr (C':real^3->bool)`]
    SCH5V_CONNECTED_SIDE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "CF" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
        (ASSUME `(C':real^3->bool) IN components(sch_level (g:real^3->real^3) a)`))) THEN
      FIRST_ASSUM ACCEPT_TAC;
      USE_THEN "DJ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `IMAGE sch5v_pr (C:real^3->bool)` INSIDE_INTER_OUTSIDE) THEN
  UNDISCH_TAC `IMAGE sch5v_pr (C':real^3->bool) SUBSET outside(IMAGE sch5v_pr C)` THEN
  UNDISCH_TAC `(x:real^2) IN IMAGE sch5v_pr (C':real^3->bool)` THEN
  UNDISCH_TAC `(x:real^2) IN inside(IMAGE sch5v_pr (C:real^3->bool))` THEN
  SET_TAC[]);;

