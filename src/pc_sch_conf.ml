(* ========================================================================= *)
(* pc_sch_conf: complex-analytic part of the smooth planar Schoenflies       *)
(* theorem by the conformal route.                                           *)
(*                                                                           *)
(* Contents: Cauchy splitting of a function holomorphic on an annulus        *)
(* r0 < |z| < 1 into a part holomorphic on the unit disc and a part          *)
(* holomorphic outside radius r0 and vanishing at infinity; the reflection  *)
(* lemma (a holomorphic function on the annulus whose real part tends to 0   *)
(* at the unit circle extends holomorphically to r0 < |z| < 1/r0 with        *)
(* H(1/cnj z) = --cnj(H z)); nonvanishing holomorphic functions on an        *)
(* annulus are z^m exp(H); and the analytic-collar Schoenflies theorem       *)
(* SCH2_ANALYTIC_COLLAR: if F is holomorphic and injective near the unit     *)
(* circle, the closed inside of F(circle) is the image of the closed unit    *)
(* disc under a conformal map defined near the closed disc, which agrees     *)
(* with F up to a conformal self-map of a neighbourhood of the circle        *)
(* preserving the circle.                                                    *)
(* ========================================================================= *)

needs "src/pc_sch_stmt.ml";;
needs "src/pc_an_beltrami.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Concentric circles and the Cauchy formula on an annulus.                  *)
(* ------------------------------------------------------------------------- *)

let SCH2_CIRCLEPATH_0 = prove
 (`!s t. circlepath(Cx(&0),s) t = Cx s * cexp(ii * Cx(&2 * pi * drop t)) /\
         norm(cexp(ii * Cx(&2 * pi * drop t))) = &1`,
  REWRITE_TAC[CIRCLEPATH; COMPLEX_ADD_LID; NORM_CEXP_II] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[CX_MUL] THEN CONV_TAC COMPLEX_RING);;

let SCH2_CONVEX_COMB_BOUNDS = prove
 (`!u a b. &0 <= u /\ u <= &1
           ==> min a b <= (&1 - u) * a + u * b /\ (&1 - u) * a + u * b <= max a b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (&1 - u) * (a - min a b) /\ &0 <= u * (b - min a b) /\
                &0 <= (&1 - u) * (max a b - a) /\ &0 <= u * (max a b - b)`
  MP_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[real_min; real_max] THEN
    REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let SCH2_CIRCLE_SEGMENT = prove
 (`!s1 s2 t. &0 < s1 /\ &0 < s2
             ==> segment[circlepath(Cx(&0),s1) t,circlepath(Cx(&0),s2) t] SUBSET
                 {w | min s1 s2 <= norm w /\ norm w <= max s1 s2}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SCH2_CIRCLEPATH_0] THEN
  ABBREV_TAC `e = cexp(ii * Cx(&2 * pi * drop t))` THEN
  SUBGOAL_THEN `norm(e:complex) = &1` ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN REWRITE_TAC[NORM_CEXP_II]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; segment; IN_ELIM_THM] THEN X_GEN_TAC `w:complex` THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC SUBST1_TAC)) THEN
  REWRITE_TAC[COMPLEX_CMUL] THEN
  SUBGOAL_THEN `Cx(&1 - u) * Cx s1 * e + Cx u * Cx s2 * e =
                Cx((&1 - u) * s1 + u * s2) * e` SUBST1_TAC THENL
   [REWRITE_TAC[CX_ADD; CX_MUL; CX_SUB] THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_MUL_RID] THEN
  MP_TAC(SPECL [`u:real`; `s1:real`; `s2:real`] SCH2_CONVEX_COMB_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= min s1 s2` MP_TAC THENL
   [REWRITE_TAC[real_min] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let SCH2_CIRCLES_HOMOTOPIC = prove
 (`!u s1 s2. &0 < s1 /\ &0 < s2 /\
             {w | min s1 s2 <= norm w /\ norm w <= max s1 s2} SUBSET u
             ==> homotopic_loops u (circlepath(Cx(&0),s1)) (circlepath(Cx(&0),s2))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMOTOPIC_LOOPS_LINEAR THEN
  REWRITE_TAC[PATH_CIRCLEPATH; PATHSTART_CIRCLEPATH; PATHFINISH_CIRCLEPATH] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `{w:complex | min s1 s2 <= norm w /\ norm w <= max s1 s2}` THEN
  ASM_SIMP_TAC[SCH2_CIRCLE_SEGMENT]);;

let SCH2_CIRCLE_INTEGRALS_EQ = prove
 (`!f u s1 s2. open u /\ f holomorphic_on u /\ &0 < s1 /\ &0 < s2 /\
               {w | min s1 s2 <= norm w /\ norm w <= max s1 s2} SUBSET u
               ==> path_integral (circlepath(Cx(&0),s1)) f =
                   path_integral (circlepath(Cx(&0),s2)) f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CAUCHY_THEOREM_HOMOTOPIC_LOOPS THEN
  EXISTS_TAC `u:complex->bool` THEN ASM_REWRITE_TAC[VALID_PATH_CIRCLEPATH] THEN
  MATCH_MP_TAC SCH2_CIRCLES_HOMOTOPIC THEN ASM_REWRITE_TAC[]);;

(* Membership in spheres and balls centred at Cx(&0). *)

let SCH2_IN_C0 = prove
 (`!w:complex s. (w IN sphere(Cx(&0),s) <=> norm w = s) /\
                 (w IN ball(Cx(&0),s) <=> norm w < s) /\
                 (w IN cball(Cx(&0),s) <=> norm w <= s)`,
  REWRITE_TAC[GSYM COMPLEX_VEC_0; IN_SPHERE_0; IN_BALL_0; IN_CBALL_0]);;

(* Integrability of f(w)/(w - z) on a circle not through z. *)

let SCH2_CIRCLE_PI = prove
 (`!f:complex->complex z s.
        &0 < s /\ ~(norm z = s) /\ f continuous_on sphere(Cx(&0),s)
        ==> (\w. f w / (w - z)) path_integrable_on circlepath(Cx(&0),s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PATH_INTEGRABLE_CONTINUOUS_CIRCLEPATH THEN
  ASM_SIMP_TAC[PATH_IMAGE_CIRCLEPATH; REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_DIV THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST] THEN
  REWRITE_TAC[SCH2_IN_C0; COMPLEX_SUB_0] THEN ASM_MESON_TAC[]);;

(* The integral of 1/(w - z) over a centred circle: 2 pi i inside, 0 outside. *)

let SCH2_CIRCLE_CAUCHY_KERNEL = prove
 (`!z s. &0 < s /\ ~(norm z = s)
         ==> path_integral (circlepath(Cx(&0),s)) (\w. Cx(&1) / (w - z)) =
             if norm z < s then Cx(&2) * Cx pi * ii else Cx(&0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`circlepath(Cx(&0),s)`; `z:complex`] WINDING_NUMBER_VALID_PATH) THEN
  ASM_SIMP_TAC[VALID_PATH_CIRCLEPATH; PATH_IMAGE_CIRCLEPATH; REAL_LT_IMP_LE;
               SCH2_IN_C0] THEN
  COND_CASES_TAC THENL
   [MP_TAC(ISPECL [`Cx(&0)`; `s:real`; `z:complex`] WINDING_NUMBER_CIRCLEPATH) THEN
    ASM_REWRITE_TAC[COMPLEX_SUB_RZERO] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC CX_2PII_NZ THEN CONV_TAC COMPLEX_FIELD;
    MP_TAC(ISPECL [`circlepath(Cx(&0),s)`; `cball(Cx(&0),s)`; `z:complex`]
      WINDING_NUMBER_ZERO_OUTSIDE) THEN
    ASM_SIMP_TAC[PATH_CIRCLEPATH; CONVEX_CBALL; PATHSTART_CIRCLEPATH;
                 PATHFINISH_CIRCLEPATH; PATH_IMAGE_CIRCLEPATH; REAL_LT_IMP_LE;
                 SPHERE_SUBSET_CBALL; SCH2_IN_C0] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC CX_2PII_NZ THEN CONV_TAC COMPLEX_FIELD]);;

let SCH2_ANNULUS_CAUCHY = prove
 (`!H r0 s1 s2 z.
        &0 <= r0 /\ r0 < s1 /\ s1 < norm z /\ norm z < s2 /\ s2 < &1 /\
        H holomorphic_on annulus r0 (&1)
        ==> Cx(&2) * Cx pi * ii * H z =
            path_integral (circlepath(Cx(&0),s2)) (\w. H w / (w - z)) -
            path_integral (circlepath(Cx(&0),s1)) (\w. H w / (w - z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(z:complex) IN annulus r0 (&1)` ASSUME_TAC THENL
   [REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `g = \w. if w = z then complex_derivative H z
                      else ((H:complex->complex) w - H z) / (w - z)` THEN
  SUBGOAL_THEN `(g:complex->complex) holomorphic_on annulus r0 (&1)` ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN MATCH_MP_TAC POLE_LEMMA_OPEN THEN
    ASM_REWRITE_TAC[OPEN_ANNULUS];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. r0 < s /\ s < &1 ==> sphere(Cx(&0),s) SUBSET annulus r0 (&1)`
  (LABEL_TAC "SPH") THENL
   [REWRITE_TAC[SUBSET; SCH2_IN_C0; annulus; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. r0 < s /\ s < &1 /\ ~(norm(z:complex) = s)
                    ==> path_integral (circlepath(Cx(&0),s)) g =
                        path_integral (circlepath(Cx(&0),s)) (\w. H w / (w - z)) -
                        H z * path_integral (circlepath(Cx(&0),s))
                                (\w. Cx(&1) / (w - z))`
  (LABEL_TAC "LIN") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(H:complex->complex) continuous_on sphere(Cx(&0),s)` ASSUME_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `annulus r0 (&1):complex->bool` THEN
      ASM_SIMP_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\w:complex. Cx(&1) / (w - z)`; `circlepath(Cx(&0),s)`;
                   `(H:complex->complex) z`] PATH_INTEGRAL_COMPLEX_LMUL) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC SCH2_CIRCLE_PI THEN ASM_REWRITE_TAC[CONTINUOUS_ON_CONST]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`\w:complex. (H:complex->complex) w / (w - z)`;
                   `\w:complex. (H:complex->complex) z * Cx(&1) / (w - z)`;
                   `circlepath(Cx(&0),s)`] PATH_INTEGRAL_SUB) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC SCH2_CIRCLE_PI THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC PATH_INTEGRABLE_COMPLEX_LMUL THEN
        MATCH_MP_TAC SCH2_CIRCLE_PI THEN ASM_REWRITE_TAC[CONTINUOUS_ON_CONST]];
      ALL_TAC] THEN
    REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC PATH_INTEGRAL_EQ THEN
    ASM_SIMP_TAC[PATH_IMAGE_CIRCLEPATH; REAL_LT_IMP_LE; SCH2_IN_C0] THEN
    X_GEN_TAC `w:complex` THEN DISCH_TAC THEN EXPAND_TAC "g" THEN
    COND_CASES_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(w - z:complex = Cx(&0))` MP_TAC THENL
     [ASM_REWRITE_TAC[COMPLEX_SUB_0]; CONV_TAC COMPLEX_FIELD];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:complex->complex`; `annulus r0 (&1):complex->bool`;
                 `s1:real`; `s2:real`] SCH2_CIRCLE_INTEGRALS_EQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_ANNULUS] THEN
    REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; annulus; real_min; real_max] THEN
    COND_CASES_TAC THEN REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "LIN" (fun th -> MP_TAC(SPEC `s1:real` th) THEN MP_TAC(SPEC `s2:real` th)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`z:complex`; `s1:real`] SCH2_CIRCLE_CAUCHY_KERNEL) THEN
  MP_TAC(SPECL [`z:complex`; `s2:real`] SCH2_CIRCLE_CAUCHY_KERNEL) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `~(norm(z:complex) < s1)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  CONV_TAC COMPLEX_RING);;

(* ------------------------------------------------------------------------- *)
(* The Cauchy splitting H = Hp + Hm on the annulus r0 < |z| < 1.             *)
(* Hp is the Cauchy integral over a circle just inside |z| = 1 (holomorphic  *)
(* on the unit disc), Hm minus the Cauchy integral over a circle just        *)
(* outside |z| = r0 (holomorphic for |z| > r0, zero at infinity).            *)
(* ------------------------------------------------------------------------- *)

let sch2_hp = new_definition
 `sch2_hp (H:complex->complex) (r0:real) (z:complex) =
    path_integral (circlepath(Cx(&0),(&1 + max r0 (norm z)) / &2))
                  (\w. H w / (w - z)) / (Cx(&2) * Cx pi * ii)`;;

let sch2_hm = new_definition
 `sch2_hm (H:complex->complex) (r0:real) (z:complex) =
    --(path_integral (circlepath(Cx(&0),(r0 + min (norm z) ((&1 + r0) / &2)) / &2))
                     (\w. H w / (w - z))) / (Cx(&2) * Cx pi * ii)`;;

let SCH2_CIRCLE_VDERIV_NORM = prove
 (`!s t. norm(vector_derivative (circlepath(Cx(&0),s)) (at t)) = &2 * pi * abs s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VECTOR_DERIVATIVE_CIRCLEPATH] THEN
  SUBGOAL_THEN `Cx(&2) * Cx pi * ii * Cx(drop t) = ii * Cx(&2 * pi * drop t)` SUBST1_TAC THENL
   [REWRITE_TAC[CX_MUL] THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; COMPLEX_NORM_II; NORM_CEXP_II] THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_MUL_LID] THEN
  SIMP_TAC[PI_POS; REAL_ARITH `&0 < x ==> abs x = x`] THEN REAL_ARITH_TAC);;

(* The Cauchy integral over a circle has a complex derivative off the circle. *)

let SCH2_CAUCHY_INT_DIFF = prove
 (`!f:complex->complex s w.
        &0 < s /\ f continuous_on sphere(Cx(&0),s) /\ ~(norm w = s)
        ==> (\v. path_integral (circlepath(Cx(&0),s)) (\u. f u / (u - v)))
            complex_differentiable (at w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:complex->complex`;
                 `\v. path_integral (circlepath(Cx(&0),s)) (\u. f u / (u - v))`;
                 `circlepath(Cx(&0),s)`; `(:complex) DIFF sphere(Cx(&0),s)`;
                 `1`; `&2 * pi * s`] CAUCHY_NEXT_DERIVATIVE) THEN
  ASM_SIMP_TAC[ARITH_EQ; GSYM closed; CLOSED_SPHERE; VALID_PATH_CIRCLEPATH;
               PATH_IMAGE_CIRCLEPATH; REAL_LT_IMP_LE; COMPLEX_POW_1] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[SCH2_CIRCLE_VDERIV_NORM] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < s ==> abs s = s`; REAL_LE_REFL];
      X_GEN_TAC `v:complex` THEN REWRITE_TAC[IN_DIFF; IN_UNIV; SCH2_IN_C0] THEN
      REWRITE_TAC[COMPLEX_POW_1] THEN
      DISCH_TAC THEN MATCH_MP_TAC HAS_PATH_INTEGRAL_INTEGRAL THEN
      MATCH_MP_TAC SCH2_CIRCLE_PI THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `w:complex`) THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; SCH2_IN_C0] THEN
  MESON_TAC[complex_differentiable]);;

let SCH2_SHELL_SUB = prove
 (`!s1 s2 a b. a < s1 /\ a < s2 /\ s1 < b /\ s2 < b
               ==> {w:complex | min s1 s2 <= norm w /\ norm w <= max s1 s2} SUBSET
                   annulus a b`,
  REWRITE_TAC[SUBSET; IN_ELIM_THM; annulus; real_min; real_max] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `w:complex` THEN
  COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

let SCH2_DIV_HOLO = prove
 (`!H:complex->complex z u.
        H holomorphic_on u /\ ~(z IN u)
        ==> (\w. H w / (w - z)) holomorphic_on u`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOLOMORPHIC_ON_DIV THEN
  ASM_SIMP_TAC[HOLOMORPHIC_ON_SUB; HOLOMORPHIC_ON_ID; HOLOMORPHIC_ON_CONST] THEN
  REWRITE_TAC[COMPLEX_SUB_0] THEN ASM_MESON_TAC[]);;

let SCH2_HP_RADIUS = prove
 (`!H r0 s z.
        &0 <= r0 /\ r0 < s /\ norm z < s /\ s < &1 /\
        H holomorphic_on annulus r0 (&1)
        ==> sch2_hp H r0 z =
            path_integral (circlepath(Cx(&0),s)) (\w. H w / (w - z)) /
            (Cx(&2) * Cx pi * ii)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sch2_hp] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SCH2_CIRCLE_INTEGRALS_EQ THEN
  EXISTS_TAC `annulus (max r0 (norm(z:complex))) (&1):complex->bool` THEN
  REWRITE_TAC[OPEN_ANNULUS] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SCH2_DIV_HOLO THEN CONJ_TAC THENL
     [MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN
      EXISTS_TAC `annulus r0 (&1):complex->bool` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC];
    REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SCH2_SHELL_SUB THEN REWRITE_TAC[real_max] THEN
    COND_CASES_TAC THEN ASM_REAL_ARITH_TAC]);;

let SCH2_HM_RADIUS = prove
 (`!H r0 s z.
        &0 <= r0 /\ r0 < s /\ s < norm z /\ s < &1 /\
        H holomorphic_on annulus r0 (&1)
        ==> sch2_hm H r0 z =
            --(path_integral (circlepath(Cx(&0),s)) (\w. H w / (w - z))) /
            (Cx(&2) * Cx pi * ii)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sch2_hm] THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SCH2_CIRCLE_INTEGRALS_EQ THEN
  EXISTS_TAC `annulus r0 (min (norm(z:complex)) (&1)):complex->bool` THEN
  REWRITE_TAC[OPEN_ANNULUS] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SCH2_DIV_HOLO THEN CONJ_TAC THENL
     [MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN
      EXISTS_TAC `annulus r0 (&1):complex->bool` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC];
    REWRITE_TAC[real_min] THEN REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SCH2_SHELL_SUB THEN REWRITE_TAC[real_min] THEN
    REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC]);;

let SCH2_HP_HOLO = prove
 (`!H r0. &0 <= r0 /\ r0 < &1 /\ H holomorphic_on annulus r0 (&1)
          ==> sch2_hp H r0 holomorphic_on ball(Cx(&0),&1)`,
  REPEAT STRIP_TAC THEN SIMP_TAC[HOLOMORPHIC_ON_OPEN; OPEN_BALL] THEN
  REWRITE_TAC[GSYM complex_differentiable; SCH2_IN_C0] THEN
  X_GEN_TAC `z0:complex` THEN DISCH_TAC THEN
  ABBREV_TAC `s = (&1 + max r0 (norm(z0:complex))) / &2` THEN
  SUBGOAL_THEN `r0 < s /\ norm(z0:complex) < s /\ s < &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_TRANSFORM_AT THEN
  EXISTS_TAC `\v. path_integral (circlepath(Cx(&0),s)) (\w. H w / (w - v)) /
                  (Cx(&2) * Cx pi * ii)` THEN
  EXISTS_TAC `s - norm(z0:complex)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `v:complex` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SCH2_HP_RADIUS THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `dist(v:complex,z0) < s - norm(z0:complex)` THEN
    REWRITE_TAC[dist] THEN NORM_ARITH_TAC;
    MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_DIV_AT THEN
    REWRITE_TAC[COMPLEX_DIFFERENTIABLE_CONST; CX_2PII_NZ] THEN
    MATCH_MP_TAC SCH2_CAUCHY_INT_DIFF THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `annulus r0 (&1):complex->bool` THEN
      ASM_SIMP_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON] THEN
      REWRITE_TAC[SUBSET; SCH2_IN_C0; annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC]]);;

let SCH2_HM_HOLO = prove
 (`!H r0. &0 <= r0 /\ r0 < &1 /\ H holomorphic_on annulus r0 (&1)
          ==> sch2_hm H r0 holomorphic_on {z | r0 < norm z}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open {z:complex | r0 < norm z}` ASSUME_TAC THENL
   [SUBGOAL_THEN `{z:complex | r0 < norm z} = (:complex) DIFF cball(Cx(&0),r0)`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_UNIV; SCH2_IN_C0] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[GSYM closed; CLOSED_CBALL]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[HOLOMORPHIC_ON_OPEN] THEN
  REWRITE_TAC[GSYM complex_differentiable; IN_ELIM_THM] THEN
  X_GEN_TAC `z0:complex` THEN DISCH_TAC THEN
  ABBREV_TAC `s = (r0 + min (norm(z0:complex)) ((&1 + r0) / &2)) / &2` THEN
  SUBGOAL_THEN `r0 < s /\ s < norm(z0:complex) /\ s < &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[real_min] THEN COND_CASES_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_TRANSFORM_AT THEN
  EXISTS_TAC `\v. --(path_integral (circlepath(Cx(&0),s)) (\w. H w / (w - v))) /
                  (Cx(&2) * Cx pi * ii)` THEN
  EXISTS_TAC `norm(z0:complex) - s` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `v:complex` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SCH2_HM_RADIUS THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `dist(v:complex,z0) < norm(z0:complex) - s` THEN
    REWRITE_TAC[dist] THEN NORM_ARITH_TAC;
    MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_DIV_AT THEN
    REWRITE_TAC[COMPLEX_DIFFERENTIABLE_CONST; CX_2PII_NZ] THEN
    MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_NEG THEN
    MATCH_MP_TAC SCH2_CAUCHY_INT_DIFF THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `annulus r0 (&1):complex->bool` THEN
      ASM_SIMP_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON] THEN
      REWRITE_TAC[SUBSET; SCH2_IN_C0; annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC]]);;

let SCH2_SPLIT = prove
 (`!H r0 z. &0 <= r0 /\ r0 < &1 /\ H holomorphic_on annulus r0 (&1) /\
            z IN annulus r0 (&1)
            ==> H z = sch2_hp H r0 z + sch2_hm H r0 z`,
  REWRITE_TAC[annulus; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`H:complex->complex`; `r0:real`; `(r0 + norm(z:complex)) / &2`;
                `(norm(z:complex) + &1) / &2`; `z:complex`] SCH2_ANNULUS_CAUCHY) THEN
  ASM_REWRITE_TAC[annulus] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`H:complex->complex`; `r0:real`; `(norm(z:complex) + &1) / &2`;
                `z:complex`] SCH2_HP_RADIUS) THEN
  MP_TAC(SPECL [`H:complex->complex`; `r0:real`; `(r0 + norm(z:complex)) / &2`;
                `z:complex`] SCH2_HM_RADIUS) THEN
  ASM_REWRITE_TAC[annulus] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC CX_2PII_NZ THEN CONV_TAC COMPLEX_FIELD);;

let SCH2_NORM_2PII = prove
 (`norm(Cx(&2) * Cx pi * ii) = &2 * pi`,
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; COMPLEX_NORM_II] THEN
  MP_TAC PI_POS THEN REAL_ARITH_TAC);;

let SCH2_HM_LIM = prove
 (`!H r0. &0 <= r0 /\ r0 < &1 /\ H holomorphic_on annulus r0 (&1)
          ==> !e. &0 < e
                  ==> ?R. &1 <= R /\ !z. R <= norm z ==> norm(sch2_hm H r0 z) < e`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `s = (r0 + (&1 + r0) / &2) / &2` THEN
  SUBGOAL_THEN `r0 < s /\ s < (&1 + r0) / &2 /\ &0 < s` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(H:complex->complex) continuous_on sphere(Cx(&0),s)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `annulus r0 (&1):complex->bool` THEN
    ASM_SIMP_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON] THEN
    REWRITE_TAC[SUBSET; SCH2_IN_C0; annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?M. &0 < M /\ !w. norm w = s ==> norm((H:complex->complex) w) <= M`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`H:complex->complex`; `sphere(Cx(&0),s)`]
      COMPACT_CONTINUOUS_IMAGE) THEN
    ASM_REWRITE_TAC[COMPACT_SPHERE] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; SCH2_IN_C0];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= M * s / e` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_DIV; REAL_LT_IMP_LE]; ALL_TAC] THEN
  EXISTS_TAC `&1 + s + M * s / e` THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(&1 + r0) / &2 < norm(z:complex)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `min (norm(z:complex)) ((&1 + r0) / &2) = (&1 + r0) / &2`
  ASSUME_TAC THENL [REWRITE_TAC[real_min] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(z:complex) - s` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[sch2_hm; COMPLEX_NORM_DIV; NORM_NEG; SCH2_NORM_2PII] THEN
  MP_TAC(ISPECL [`\w. (H:complex->complex) w / (w - z)`;
                 `path_integral (circlepath(Cx(&0),s)) (\w. (H:complex->complex) w / (w - z))`;
                 `Cx(&0)`; `s:real`; `M / (norm(z:complex) - s)`]
    HAS_PATH_INTEGRAL_BOUND_CIRCLEPATH) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HAS_PATH_INTEGRAL_INTEGRAL THEN MATCH_MP_TAC SCH2_CIRCLE_PI THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[];
      X_GEN_TAC `w:complex` THEN REWRITE_TAC[COMPLEX_SUB_RZERO] THEN DISCH_TAC THEN
      SUBGOAL_THEN `norm(z:complex) - s <= norm(w - z:complex)` ASSUME_TAC THENL
       [UNDISCH_TAC `norm(w:complex) = s` THEN NORM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[COMPLEX_NORM_DIV] THEN
      SUBGOAL_THEN `&0 < norm(w - z:complex)` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `M:real` THEN
      ASM_SIMP_TAC[] THEN
      REWRITE_TAC[REAL_ARITH `M / a * b = (M * b) / a`] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `M * s / e < norm(z:complex) - s` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * pi` ASSUME_TAC THENL
   [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `M / (norm(z:complex) - s) * &2 * pi * s` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `M / a * &2 * pi * s = (&2 * pi) * ((M * s) / a)`] THEN
  SUBGOAL_THEN `(M * s) / (norm(z:complex) - s) < e` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
    UNDISCH_TAC `M * s / e < norm(z:complex) - s` THEN
    REWRITE_TAC[REAL_ARITH `M * s / e = (M * s) / e`] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `p * x < p * e ==> p * x < e * p`) THEN
  MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The reflection lemma.  Qm(z) = cnj(Hm(1/cnj z)) (0 at z = 0)              *)
(* is holomorphic on |z| < 1/r0; Q = Hp + Qm is holomorphic on the unit disc *)
(* with real part tending to 0 at the circle when Re H does, hence Q is an   *)
(* imaginary constant c, and c - Qm + Hm extends H across the circle.        *)
(* ------------------------------------------------------------------------- *)

let sch2_qm = new_definition
 `sch2_qm (H:complex->complex) (r0:real) (z:complex) =
    if z = Cx(&0) then Cx(&0) else cnj(sch2_hm H r0 (inv(cnj z)))`;;

let SCH2_INV_CNJ_NORM = prove
 (`!z:complex. norm(inv(cnj z)) = inv(norm z) /\ inv(cnj(inv(cnj z))) = z`,
  REWRITE_TAC[COMPLEX_NORM_INV; COMPLEX_NORM_CNJ; CNJ_INV; CNJ_CNJ; COMPLEX_INV_INV]);;

(* Away from 0, Qm is differentiable where |z| < 1/r0. *)

let SCH2_QM_DIFF = prove
 (`!H r0 z. &0 < r0 /\ r0 < &1 /\ H holomorphic_on annulus r0 (&1) /\
            ~(z = Cx(&0)) /\ norm z < inv r0
            ==> (\z. cnj(sch2_hm H r0 (inv(cnj z)))) complex_differentiable at z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z. cnj(sch2_hm H r0 (inv(cnj z)))) =
                (\w. cnj(sch2_hm H r0 (cnj w))) o inv` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; CNJ_INV]; ALL_TAC] THEN
  MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_COMPOSE_AT THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`\z:complex. z`; `z:complex`] COMPLEX_DIFFERENTIABLE_INV_AT) THEN
    ASM_REWRITE_TAC[COMPLEX_DIFFERENTIABLE_ID; ETA_AX];
    MATCH_MP_TAC BEL_CNJ_CONJ_DIFF THEN REWRITE_TAC[ETA_AX] THEN
    MP_TAC(SPECL [`H:complex->complex`; `r0:real`] SCH2_HM_HOLO) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    SUBGOAL_THEN `open {z:complex | r0 < norm z}` ASSUME_TAC THENL
     [SUBGOAL_THEN `{z:complex | r0 < norm z} = (:complex) DIFF cball(Cx(&0),r0)`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_UNIV; SCH2_IN_C0] THEN
        REAL_ARITH_TAC;
        REWRITE_TAC[GSYM closed; CLOSED_CBALL]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[HOLOMORPHIC_ON_OPEN; GSYM complex_differentiable] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[IN_ELIM_THM; COMPLEX_NORM_CNJ; COMPLEX_NORM_INV] THEN
    SUBGOAL_THEN `&0 < norm(z:complex)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[COMPLEX_NORM_NZ]; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN
    MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REWRITE_TAC[]]);;

let SCH2_QM_HOLO = prove
 (`!H r0. &0 < r0 /\ r0 < &1 /\ H holomorphic_on annulus r0 (&1)
          ==> sch2_qm H r0 holomorphic_on ball(Cx(&0),inv r0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!z. ~(z = Cx(&0)) /\ norm z < inv r0
                    ==> sch2_qm H r0 complex_differentiable at z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_TRANSFORM_AT THEN
    EXISTS_TAC `\z. cnj(sch2_hm H r0 (inv(cnj z)))` THEN
    EXISTS_TAC `norm(z:complex)` THEN ASM_SIMP_TAC[COMPLEX_NORM_NZ; SCH2_QM_DIFF] THEN
    X_GEN_TAC `w:complex` THEN DISCH_TAC THEN REWRITE_TAC[sch2_qm] THEN
    COND_CASES_TAC THENL
     [UNDISCH_TAC `dist(w:complex,z) < norm(z:complex)` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[dist; COMPLEX_SUB_LZERO; NORM_NEG; REAL_LT_REFL];
      REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC NO_ISOLATED_SINGULARITY THEN EXISTS_TAC `{Cx(&0)}` THEN
  REWRITE_TAC[OPEN_BALL; FINITE_SING] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    X_GEN_TAC `z:complex` THEN REWRITE_TAC[SCH2_IN_C0] THEN DISCH_TAC THEN
    ASM_CASES_TAC `z = Cx(&0)` THENL
     [ALL_TAC;
      MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN ASM_SIMP_TAC[]] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[CONTINUOUS_AT; LIM_AT] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`H:complex->complex`; `r0:real`] SCH2_HM_LIM) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `R:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `inv R` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `w:complex` THEN REWRITE_TAC[dist; COMPLEX_SUB_RZERO] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(w = Cx(&0))` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[GSYM COMPLEX_NORM_NZ]; ALL_TAC] THEN
    ASM_REWRITE_TAC[sch2_qm; COMPLEX_SUB_RZERO; COMPLEX_NORM_CNJ] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[SCH2_INV_CNJ_NORM] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    SIMP_TAC[HOLOMORPHIC_ON_OPEN; OPEN_DIFF; OPEN_BALL; CLOSED_SING] THEN
    REWRITE_TAC[GSYM complex_differentiable; IN_DIFF; IN_SING; SCH2_IN_C0] THEN
    ASM_MESON_TAC[]]);;

let SCH2_Q_HOLO = prove
 (`!H r0. &0 < r0 /\ r0 < &1 /\ H holomorphic_on annulus r0 (&1)
          ==> (\z. sch2_hp H r0 z + sch2_qm H r0 z) holomorphic_on ball(Cx(&0),&1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOLOMORPHIC_ON_ADD THEN CONJ_TAC THENL
   [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC SCH2_HP_HOLO THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN
    EXISTS_TAC `ball(Cx(&0),inv r0)` THEN ASM_SIMP_TAC[SCH2_QM_HOLO] THEN
    MATCH_MP_TAC SUBSET_BALL THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_1] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC]);;

let SCH2_INV_CNJ_EQ = prove
 (`!z:complex. inv(cnj z) = Cx(inv(norm z pow 2)) * z`,
  GEN_TAC THEN ASM_CASES_TAC `z = Cx(&0)` THEN
  ASM_REWRITE_TAC[CNJ_CX; COMPLEX_INV_0; COMPLEX_MUL_RZERO] THEN
  REWRITE_TAC[CX_INV; CX_POW; COMPLEX_NORM_POW_2] THEN
  SUBGOAL_THEN `~(cnj z = Cx(&0))` MP_TAC THENL
   [ASM_REWRITE_TAC[CNJ_EQ_0]; ALL_TAC] THEN
  UNDISCH_TAC `~(z = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD);;

let SCH2_INV_CNJ_CLOSE = prove
 (`!z:complex rho. &0 < rho /\ rho <= norm z /\ norm z < &1
                   ==> norm(inv(cnj z) - z) <= &2 / rho * (&1 - norm z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SCH2_INV_CNJ_EQ] THEN
  REWRITE_TAC[COMPLEX_RING `Cx a * z - z = (Cx a - Cx(&1)) * z`; GSYM CX_SUB] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
  SUBGOAL_THEN `&0 < norm(z:complex)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `inv(norm(z:complex) pow 2) - &1 = (&1 - norm z) * (&1 + norm z) /
                                                    norm z pow 2`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < norm(z:complex)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&1 - norm(z:complex)) * (&1 + norm z) / norm z pow 2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  SUBGOAL_THEN `((&1 - norm(z:complex)) * (&1 + norm z) / norm z pow 2) * norm z =
                (&1 - norm z) * ((&1 + norm z) / norm z)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < norm(z:complex)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `&2 / rho * (&1 - n) = (&1 - n) * (&2 / rho)`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 / norm(z:complex)` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]]]);;

let SCH2_Q_RE_LIM = prove
 (`!H r0. &0 < r0 /\ r0 < &1 /\ H holomorphic_on annulus r0 (&1) /\
          (!e. &0 < e ==> ?d. &0 < d /\
                              !z. &1 - d < norm z /\ norm z < &1 ==> abs(Re(H z)) < e)
          ==> !e. &0 < e
                  ==> ?d. &0 < d /\
                          !z. &1 - d < norm z /\ norm z < &1
                              ==> abs(Re(sch2_hp H r0 z + sch2_qm H r0 z)) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  ABBREV_TAC `rho = (&1 + r0) / &2` THEN
  SUBGOAL_THEN `r0 < rho /\ rho < &1 /\ &1 / &2 <= rho` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `k = cball(Cx(&0),&2) DIFF ball(Cx(&0),rho)` THEN
  SUBGOAL_THEN `compact(k:complex->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN MATCH_MP_TAC COMPACT_DIFF THEN
    REWRITE_TAC[COMPACT_CBALL; OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:complex. w IN k <=> rho <= norm w /\ norm w <= &2` ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN REWRITE_TAC[IN_DIFF; SCH2_IN_C0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sch2_hm H r0 continuous_on k` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `{z:complex | r0 < norm z}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HOLOMORPHIC_ON_IMP_CONTINUOUS_ON THEN
      MATCH_MP_TAC SCH2_HM_HOLO THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sch2_hm H r0`; `k:complex->bool`] COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ASM_REWRITE_TAC[uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "RH1"))) THEN
  EXISTS_TAC `min d1 (min (&1 - rho) (rho * d2 / &2))` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `z:complex` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
  SUBGOAL_THEN `rho < norm(z:complex)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(z = Cx(&0))` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM COMPLEX_NORM_NZ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`H:complex->complex`; `r0:real`; `z:complex`] SCH2_SPLIT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN
    ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  ASM_REWRITE_TAC[sch2_qm; RE_ADD; RE_CNJ] THEN
  SUBGOAL_THEN `Re(sch2_hp H r0 z) = Re(H z) - Re(sch2_hm H r0 z)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[RE_ADD] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `norm(sch2_hm H r0 (inv(cnj z)) - sch2_hm H r0 z) < e / &2`
  MP_TAC THENL
   [ONCE_REWRITE_TAC[GSYM dist] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[SCH2_INV_CNJ_NORM] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1` THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_INV_1_LE THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv rho` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[dist] THEN
      MP_TAC(SPECL [`z:complex`; `rho:real`] SCH2_INV_CNJ_CLOSE) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `b < c ==> a <= b ==> a < c`) THEN
      SUBGOAL_THEN `&2 / rho * (&1 - norm(z:complex)) < &2 / rho * (rho * d2 / &2)`
      MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
        SUBGOAL_THEN `&2 / rho * (rho * d2 / &2) = d2` SUBST1_TAC THENL
         [UNDISCH_TAC `&1 / &2 <= rho` THEN CONV_TAC REAL_FIELD; REWRITE_TAC[]]]];
    ALL_TAC] THEN
  MP_TAC(SPEC `sch2_hm H r0 (inv(cnj z)) - sch2_hm H r0 z` COMPLEX_NORM_GE_RE_IM) THEN
  REWRITE_TAC[RE_SUB] THEN
  USE_THEN "RH1" (MP_TAC o SPEC `z:complex`) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `&1 - min d1 (min (&1 - rho) (rho * d2 / &2)) < norm(z:complex)` THEN
    UNDISCH_TAC `norm(z:complex) < &1` THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let SCH2_ABS_LE_ALL = prove
 (`!x. (!e. &0 < e ==> abs x <= e) ==> x = &0`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o SPEC `abs x / &2`) THEN REAL_ARITH_TAC);;

let SCH2_Q_CONST = prove
 (`!H r0. &0 < r0 /\ r0 < &1 /\ H holomorphic_on annulus r0 (&1) /\
          (!e. &0 < e ==> ?d. &0 < d /\
                              !z. &1 - d < norm z /\ norm z < &1 ==> abs(Re(H z)) < e)
          ==> ?c. Re c = &0 /\
                  !z. z IN ball(Cx(&0),&1) ==> sch2_hp H r0 z + sch2_qm H r0 z = c`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> LABEL_TAC "QL" (MATCH_MP SCH2_Q_RE_LIM th) THEN
                       STRIP_ASSUME_TAC th) THEN
  ABBREV_TAC `Q = \z. sch2_hp H r0 z + sch2_qm H r0 z` THEN
  SUBGOAL_THEN `(Q:complex->complex) holomorphic_on ball(Cx(&0),&1)` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN MATCH_MP_TAC SCH2_Q_HOLO THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN ball(Cx(&0),&1) ==> Re((Q:complex->complex) z) = &0`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:complex` THEN REWRITE_TAC[SCH2_IN_C0] THEN DISCH_TAC THEN
    MATCH_MP_TAC SCH2_ABS_LE_ALL THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "QL" (fun th -> MP_TAC(MP (SPEC `e:real` th) (ASSUME `&0 < e`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "QD"))) THEN
    ABBREV_TAC `s = (max (norm(z:complex)) (&1 - d) + &1) / &2` THEN
    SUBGOAL_THEN `norm(z:complex) < s /\ &1 - d < s /\ s < &1 /\ &0 < s`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "s" THEN REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN
      MP_TAC(ISPEC `z:complex` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(Q:complex->complex) continuous_on cball(Cx(&0),s) /\
                  Q holomorphic_on ball(Cx(&0),s)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(Cx(&0),&1)` THEN
        ASM_SIMP_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON] THEN
        REWRITE_TAC[SUBSET; SCH2_IN_C0] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN EXISTS_TAC `ball(Cx(&0),&1)` THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; SCH2_IN_C0] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`Q:complex->complex`; `ball(Cx(&0),s)`; `e:real`]
      MAXIMUM_REAL_FRONTIER) THEN
    MP_TAC(ISPECL [`\z. --((Q:complex->complex) z)`; `ball(Cx(&0),s)`; `e:real`]
      MAXIMUM_REAL_FRONTIER) THEN
    ASM_SIMP_TAC[BOUNDED_BALL; INTERIOR_OPEN; OPEN_BALL; CLOSURE_BALL; FRONTIER_BALL;
                 HOLOMORPHIC_ON_NEG; CONTINUOUS_ON_NEG; SCH2_IN_C0; RE_NEG] THEN
    SUBGOAL_THEN `!w. norm w = s ==> abs(Re((Q:complex->complex) w)) < e`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN EXPAND_TAC "Q" THEN USE_THEN "QD" MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `z':complex`) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
    ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `z':complex`) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN ASM_REWRITE_TAC[]] THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `(Q:complex->complex)(Cx(&0))` THEN
  SUBGOAL_THEN `?c. !z. z IN ball(Cx(&0),&1) ==> (Q:complex->complex) z = c`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`ball(Cx(&0),&1)`; `Q:complex->complex`] OPEN_MAPPING_THM) THEN
    ASM_REWRITE_TAC[OPEN_BALL; CONNECTED_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `ball(Cx(&0),&1)`) THEN
    REWRITE_TAC[OPEN_BALL; SUBSET_REFL] THEN
    DISCH_THEN(MP_TAC o REWRITE_RULE[open_def]) THEN
    DISCH_THEN(MP_TAC o SPEC `(Q:complex->complex)(Cx(&0))`) THEN
    SUBGOAL_THEN `Cx(&0) IN ball(Cx(&0),&1)` ASSUME_TAC THENL
     [REWRITE_TAC[SCH2_IN_C0; COMPLEX_NORM_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `ee:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(Q:complex->complex)(Cx(&0)) + Cx(ee / &2)`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[dist; COMPLEX_RING `(a + b) - a:complex = b`; COMPLEX_NORM_CX] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:complex` STRIP_ASSUME_TAC o REWRITE_RULE[IN_IMAGE]) THEN
    SUBGOAL_THEN `Re((Q:complex->complex) w) = &0 /\ Re(Q(Cx(&0))) = &0` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[RE_ADD; RE_CX] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `Cx(&0) IN ball(Cx(&0),&1)` ASSUME_TAC THENL
   [REWRITE_TAC[SCH2_IN_C0; COMPLEX_NORM_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  EXPAND_TAC "Q" THEN REWRITE_TAC[] THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:complex`) THEN EXPAND_TAC "Q" THEN
  ASM_REWRITE_TAC[]);;

(* The reflection lemma. *)

let SCH2_REFLECT = prove
 (`!H r0. &0 < r0 /\ r0 < &1 /\ H holomorphic_on annulus r0 (&1) /\
          (!e. &0 < e ==> ?d. &0 < d /\
                              !z. &1 - d < norm z /\ norm z < &1 ==> abs(Re(H z)) < e)
          ==> ?H'. H' holomorphic_on annulus r0 (inv r0) /\
                   (!z. z IN annulus r0 (&1) ==> H' z = H z) /\
                   (!z. z IN annulus r0 (inv r0)
                        ==> inv(cnj z) IN annulus r0 (inv r0) /\
                            H'(inv(cnj z)) = --cnj(H' z))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
    X_CHOOSE_THEN `c:complex` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "QC"))
      (MATCH_MP SCH2_Q_CONST th)) THEN
  SUBGOAL_THEN `r0 < inv r0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_INV_1_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:complex. z IN annulus r0 (inv r0) ==> inv(cnj z) IN annulus r0 (inv r0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[annulus; IN_ELIM_THM; SCH2_INV_CNJ_NORM] THEN REPEAT STRIP_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN
      MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `\z. c - cnj(sch2_hm H r0 (inv(cnj z))) + sch2_hm H r0 z` THEN
  REPEAT CONJ_TAC THENL
   [SIMP_TAC[HOLOMORPHIC_ON_OPEN; OPEN_ANNULUS; GSYM complex_differentiable] THEN
    X_GEN_TAC `z:complex` THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(z = Cx(&0))` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM COMPLEX_NORM_NZ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_SUB THEN
      REWRITE_TAC[COMPLEX_DIFFERENTIABLE_CONST] THEN
      MATCH_MP_TAC SCH2_QM_DIFF THEN ASM_REWRITE_TAC[];
      MP_TAC(SPECL [`H:complex->complex`; `r0:real`] SCH2_HM_HOLO) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      SUBGOAL_THEN `open {z:complex | r0 < norm z}` ASSUME_TAC THENL
       [SUBGOAL_THEN `{z:complex | r0 < norm z} = (:complex) DIFF cball(Cx(&0),r0)`
        SUBST1_TAC THENL
         [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_UNIV; SCH2_IN_C0] THEN
          REAL_ARITH_TAC;
          REWRITE_TAC[GSYM closed; CLOSED_CBALL]];
        ALL_TAC] THEN
      ASM_SIMP_TAC[HOLOMORPHIC_ON_OPEN; GSYM complex_differentiable; ETA_AX] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM]];
    X_GEN_TAC `z:complex` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(z = Cx(&0)) /\ z IN ball(Cx(&0),&1)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(z:complex) IN annulus r0 (&1)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM; SCH2_IN_C0; GSYM COMPLEX_NORM_NZ] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "QC" (fun th -> MP_TAC(MP (SPEC `z:complex` th)
                                         (ASSUME `(z:complex) IN ball(Cx(&0),&1)`))) THEN
    REWRITE_TAC[sch2_qm; ASSUME `~(z:complex = Cx(&0))`] THEN
    MP_TAC(SPECL [`H:complex->complex`; `r0:real`; `z:complex`] SCH2_SPLIT) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    CONV_TAC COMPLEX_RING;
    X_GEN_TAC `z:complex` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[SCH2_INV_CNJ_NORM; CNJ_ADD; CNJ_SUB; CNJ_CNJ; COMPLEX_NEG_ADD] THEN
    SUBGOAL_THEN `cnj c = --c` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[COMPLEX_EQ; RE_CNJ; IM_CNJ; RE_NEG; IM_NEG] THEN REAL_ARITH_TAC;
      CONV_TAC COMPLEX_RING]]);;

(* ------------------------------------------------------------------------- *)
(* Logarithms of nonvanishing holomorphic functions on the                   *)
(* annulus r0 < |z| < 1, via the strip log r0 < Re w < 0 (cexp maps it onto *)
(* the annulus): K o cexp = cexp o L with L(w + 2 pi i) = L(w) + 2 pi i m,   *)
(* m an integer, and then K z = cexp(m clog z + H z) with H holomorphic on   *)
(* the annulus (H = L o clog - m clog, holomorphic across the cut of clog).  *)
(* ------------------------------------------------------------------------- *)

let sch2_strip = new_definition
 `sch2_strip (r0:real) = {w:complex | log r0 < Re w /\ Re w < &0}`;;

let SCH2_STRIP_OPEN_CONVEX = prove
 (`!r0. open(sch2_strip r0) /\ convex(sch2_strip r0)`,
  GEN_TAC THEN
  SUBGOAL_THEN `sch2_strip r0 = {w:complex | Re w > log r0} INTER {w | Re w < &0}`
  SUBST1_TAC THENL
   [REWRITE_TAC[sch2_strip; EXTENSION; IN_INTER; IN_ELIM_THM; real_gt]; ALL_TAC] THEN
  SIMP_TAC[OPEN_INTER; CONVEX_INTER; OPEN_HALFSPACE_RE_GT; OPEN_HALFSPACE_RE_LT;
           CONVEX_HALFSPACE_RE_GT; CONVEX_HALFSPACE_RE_LT]);;

let SCH2_STRIP_EXP = prove
 (`!r0 w. &0 < r0 /\ w IN sch2_strip r0 ==> cexp w IN annulus r0 (&1)`,
  REWRITE_TAC[sch2_strip; annulus; IN_ELIM_THM; NORM_CEXP] THEN
  REPEAT STRIP_TAC THENL
   [SUBGOAL_THEN `r0 = exp(log r0)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[EXP_LOG]; ASM_REWRITE_TAC[REAL_EXP_MONO_LT]];
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_EXP_0] THEN
    ASM_REWRITE_TAC[REAL_EXP_MONO_LT]]);;

let SCH2_STRIP_CLOG = prove
 (`!r0 z. &0 < r0 /\ z IN annulus r0 (&1) ==> clog z IN sch2_strip r0`,
  REWRITE_TAC[sch2_strip; annulus; IN_ELIM_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(z = Cx(&0))` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM COMPLEX_NORM_NZ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[RE_CLOG] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REWRITE_TAC[];
    GEN_REWRITE_TAC RAND_CONV [GSYM LOG_1] THEN
    MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let SCH2_STRIP_SHIFT = prove
 (`!r0 w t. w IN sch2_strip r0 ==> w + ii * Cx t IN sch2_strip r0`,
  REWRITE_TAC[sch2_strip; IN_ELIM_THM; RE_ADD; RE_MUL_II; IM_CX] THEN
  REAL_ARITH_TAC);;

let SCH2_CEXP_PERIOD = prove
 (`!w. cexp(w + ii * Cx(&2 * pi)) = cexp w`,
  REWRITE_TAC[CEXP_ADD; CEXP_2PII; COMPLEX_MUL_RID]);;

(* A holomorphic logarithm of K o cexp on the strip. *)

let SCH2_STRIP_LOG_EXISTS = prove
 (`!K r0. &0 < r0 /\ r0 < &1 /\ K holomorphic_on annulus r0 (&1) /\
          (!z. z IN annulus r0 (&1) ==> ~(K z = Cx(&0)))
          ==> ?L. L holomorphic_on sch2_strip r0 /\
                  !w. w IN sch2_strip r0 ==> K(cexp w) = cexp(L w)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Ft = (K:complex->complex) o cexp` THEN
  SUBGOAL_THEN `(Ft:complex->complex) holomorphic_on sch2_strip r0` ASSUME_TAC THENL
   [EXPAND_TAC "Ft" THEN MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE_GEN THEN
    EXISTS_TAC `annulus r0 (&1):complex->bool` THEN
    ASM_SIMP_TAC[HOLOMORPHIC_ON_CEXP; SCH2_STRIP_EXP];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. w IN sch2_strip r0 ==> ~((Ft:complex->complex) w = Cx(&0))`
  ASSUME_TAC THENL
   [EXPAND_TAC "Ft" THEN REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[SCH2_STRIP_EXP];
    ALL_TAC] THEN
  MP_TAC(SPEC `r0:real` SCH2_STRIP_OPEN_CONVEX) THEN STRIP_TAC THEN
  SUBGOAL_THEN `!w. w IN sch2_strip r0
                    ==> ((Ft:complex->complex) has_complex_derivative
                         complex_derivative Ft w) (at w)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE] THEN
    ASM_MESON_TAC[HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\w. complex_derivative Ft w / (Ft:complex->complex) w)
                holomorphic_on sch2_strip r0` ASSUME_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_ON_DIV THEN ASM_REWRITE_TAC[ETA_AX] THEN
    ASM_SIMP_TAC[HOLOMORPHIC_COMPLEX_DERIVATIVE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\w. complex_derivative Ft w / (Ft:complex->complex) w`;
                 `sch2_strip r0`; `{}:complex->bool`] HOLOMORPHIC_CONVEX_PRIMITIVE) THEN
  ASM_SIMP_TAC[FINITE_EMPTY; HOLOMORPHIC_ON_IMP_CONTINUOUS_ON; DIFF_EMPTY;
               INTERIOR_OPEN] THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT]; ALL_TAC] THEN
  ASM_SIMP_TAC[HAS_COMPLEX_DERIVATIVE_WITHIN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_TAC `P:complex->complex`) THEN
  SUBGOAL_THEN `?c. !w. w IN sch2_strip r0
                        ==> (Ft:complex->complex) w * cexp(--(P w)) = c`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_ZERO_CONNECTED_CONSTANT THEN
    ASM_SIMP_TAC[CONVEX_CONNECTED] THEN X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `Cx(&0) = (Ft:complex->complex) w *
               (cexp(--(P w)) * --(complex_derivative Ft w / Ft w)) +
               complex_derivative Ft w * cexp(--(P w))`
    SUBST1_TAC THENL
     [SUBGOAL_THEN `~((Ft:complex->complex) w = Cx(&0))` MP_TAC THENL
       [ASM_SIMP_TAC[]; CONV_TAC COMPLEX_FIELD];
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_MUL_AT THEN ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`\w:complex. --((P:complex->complex) w)`; `cexp`;
                   `--(complex_derivative Ft w / (Ft:complex->complex) w)`;
                   `cexp(--((P:complex->complex) w))`; `w:complex`]
      COMPLEX_DIFF_CHAIN_AT) THEN
    REWRITE_TAC[o_DEF; HAS_COMPLEX_DERIVATIVE_CEXP] THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_NEG THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_MUL_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(c = Cx(&0))` ASSUME_TAC THENL
   [MP_TAC(ISPEC `r0:real` sch2_strip) THEN DISCH_THEN(K ALL_TAC) THEN
    SUBGOAL_THEN `Cx(log r0 / &2) IN sch2_strip r0` ASSUME_TAC THENL
     [REWRITE_TAC[sch2_strip; IN_ELIM_THM; RE_CX] THEN
      SUBGOAL_THEN `log r0 < &0` MP_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [GSYM LOG_1] THEN
        MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REWRITE_TAC[];
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `Cx(log r0 / &2)`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[COMPLEX_ENTIRE; CEXP_NZ] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `\w. (P:complex->complex) w + clog c` THEN CONJ_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_ON_ADD THEN REWRITE_TAC[HOLOMORPHIC_ON_CONST] THEN
    ASM_SIMP_TAC[HOLOMORPHIC_ON_OPEN] THEN ASM_MESON_TAC[];
    X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
    REWRITE_TAC[CEXP_ADD] THEN ASM_SIMP_TAC[CEXP_CLOG] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:complex`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN EXPAND_TAC "Ft" THEN
    REWRITE_TAC[o_THM; CEXP_NEG] THEN
    MP_TAC(SPEC `(P:complex->complex) w` CEXP_NZ) THEN CONV_TAC COMPLEX_FIELD]);;

let SCH2_CEXP_EQ_1 = prove
 (`!z. cexp z = Cx(&1) ==> ?n. integer n /\ z = ii * Cx(&2 * n * pi)`,
  GEN_TAC THEN REWRITE_TAC[CEXP_EQ_1] THEN STRIP_TAC THEN
  EXISTS_TAC `n:real` THEN ASM_REWRITE_TAC[COMPLEX_EQ; RE_MUL_II; IM_MUL_II; RE_CX;
                                            IM_CX] THEN
  REAL_ARITH_TAC);;

(* Iterating an additive period. *)

let SCH2_PERIOD_ITER = prove
 (`!L:complex->complex s c d.
        (!w t. w IN s ==> w + ii * Cx t IN s) /\
        (!w. w IN s ==> L(w + ii * Cx c) = L w + d)
        ==> !n w. w IN s
                  ==> L(w + ii * Cx(&n * c)) = L w + Cx(&n) * d /\
                      L(w - ii * Cx(&n * c)) = L w - Cx(&n) * d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[REAL_MUL_LZERO; COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO;
                COMPLEX_ADD_RID; COMPLEX_SUB_RZERO];
    ALL_TAC] THEN
  X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `w:complex`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_SUC; CX_ADD] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `w + ii * Cx((&n + &1) * c) = (w + ii * Cx(&n * c)) + ii * Cx c`
    SUBST1_TAC THENL [REWRITE_TAC[CX_ADD; CX_MUL] THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w + ii * Cx(&n * c)`) THEN ASM_SIMP_TAC[] THEN
    DISCH_THEN(K ALL_TAC) THEN CONV_TAC COMPLEX_RING;
    ABBREV_TAC `v = w - ii * Cx((&n + &1) * c)` THEN
    SUBGOAL_THEN `w - ii * Cx(&n * c) = v + ii * Cx c` ASSUME_TAC THENL
     [EXPAND_TAC "v" THEN REWRITE_TAC[CX_ADD; CX_MUL] THEN CONV_TAC COMPLEX_RING;
      ALL_TAC] THEN
    SUBGOAL_THEN `(v:complex) IN s` ASSUME_TAC THENL
     [EXPAND_TAC "v" THEN
      REWRITE_TAC[COMPLEX_RING `w - ii * Cx t = w + ii * --Cx t`; GSYM CX_NEG] THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `v:complex`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(L:complex->complex)(w - ii * Cx(&n * c)) = L w - Cx(&n) * d` THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC COMPLEX_RING]);;

(* The period of a logarithm of a 2 pi i periodic function. *)

let SCH2_STRIP_LOG_PERIOD = prove
 (`!K r0 L. &0 < r0 /\ r0 < &1 /\ L holomorphic_on sch2_strip r0 /\
            (!w. w IN sch2_strip r0 ==> K(cexp w) = cexp(L w))
            ==> ?m. integer m /\
                    !w. w IN sch2_strip r0
                        ==> L(w + ii * Cx(&2 * pi)) = L w + ii * Cx(&2 * m * pi)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM(LABEL_TAC "KL") THEN
  ABBREV_TAC `D = \w. (L:complex->complex)(w + ii * Cx(&2 * pi)) - L w` THEN
  SUBGOAL_THEN `!w. w IN sch2_strip r0
                    ==> ?n. integer n /\ (D:complex->complex) w = ii * Cx(&2 * n * pi)`
  (LABEL_TAC "DV") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SCH2_CEXP_EQ_1 THEN EXPAND_TAC "D" THEN
    REWRITE_TAC[CEXP_SUB] THEN
    SUBGOAL_THEN `(w + ii * Cx(&2 * pi)) IN sch2_strip r0` ASSUME_TAC THENL
     [ASM_SIMP_TAC[SCH2_STRIP_SHIFT]; ALL_TAC] THEN
    SUBGOAL_THEN `cexp(L(w + ii * Cx(&2 * pi))) = cexp((L:complex->complex) w)`
    SUBST1_TAC THENL
     [USE_THEN "KL" (fun th -> REWRITE_TAC[GSYM(MP (SPEC `w + ii * Cx(&2 * pi)` th)
                     (ASSUME `(w + ii * Cx(&2 * pi)) IN sch2_strip r0`));
                    GSYM(MP (SPEC `w:complex` th) (ASSUME `w IN sch2_strip r0`))]) THEN
      REWRITE_TAC[SCH2_CEXP_PERIOD];
      MATCH_MP_TAC COMPLEX_DIV_REFL THEN REWRITE_TAC[CEXP_NZ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?a. !w. w IN sch2_strip r0 ==> (D:complex->complex) w = a`
  (X_CHOOSE_THEN `a:complex` (LABEL_TAC "DA")) THENL
   [MATCH_MP_TAC CONTINUOUS_DISCRETE_RANGE_CONSTANT THEN
    SIMP_TAC[CONVEX_CONNECTED; SCH2_STRIP_OPEN_CONVEX] THEN CONJ_TAC THENL
     [EXPAND_TAC "D" THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
       [ALL_TAC; ASM_SIMP_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON]] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `sch2_strip r0` THEN
      ASM_SIMP_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN SIMP_TAC[SCH2_STRIP_SHIFT];
      X_GEN_TAC `x:complex` THEN DISCH_TAC THEN EXISTS_TAC `&2 * pi` THEN
      CONJ_TAC THENL [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `y:complex` THEN STRIP_TAC THEN
      USE_THEN "DV" (fun th ->
        MP_TAC(MP (SPEC `x:complex` th) (ASSUME `(x:complex) IN sch2_strip r0`)) THEN
        MP_TAC(MP (SPEC `y:complex` th) (ASSUME `(y:complex) IN sch2_strip r0`))) THEN
      DISCH_THEN(X_CHOOSE_THEN `ny:real` STRIP_ASSUME_TAC) THEN
      DISCH_THEN(X_CHOOSE_THEN `nx:real` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `~((D:complex->complex) y = D x)` THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN
      REWRITE_TAC[GSYM COMPLEX_SUB_LDISTRIB; GSYM CX_SUB] THEN
      REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_II; COMPLEX_NORM_CX; REAL_MUL_LID] THEN
      SUBGOAL_THEN `&2 * ny * pi - &2 * nx * pi = (&2 * pi) * (ny - nx)` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM; REAL_ABS_PI] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_ABS_INTEGER_LEMMA THEN ASM_SIMP_TAC[INTEGER_SUB] THEN
      DISCH_TAC THEN UNDISCH_TAC `~(ii * Cx(&2 * ny * pi) = ii * Cx(&2 * nx * pi))` THEN
      SUBGOAL_THEN `ny = nx:real` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `Cx(log r0 / &2) IN sch2_strip r0` ASSUME_TAC THENL
   [REWRITE_TAC[sch2_strip; IN_ELIM_THM; RE_CX] THEN
    SUBGOAL_THEN `log r0 < &0` MP_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM LOG_1] THEN
      MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REWRITE_TAC[];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "DV" (fun th -> MP_TAC(MP (SPEC `Cx(log r0 / &2)` th)
                     (ASSUME `Cx(log r0 / &2) IN sch2_strip r0`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DM"))) THEN
  EXISTS_TAC `m:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
  USE_THEN "DA" (fun th ->
    MP_TAC(MP (SPEC `w:complex` th) (ASSUME `(w:complex) IN sch2_strip r0`)) THEN
    MP_TAC(MP (SPEC `Cx(log r0 / &2)` th) (ASSUME `Cx(log r0 / &2) IN sch2_strip r0`))) THEN
  USE_THEN "DM" SUBST1_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  EXPAND_TAC "D" THEN REWRITE_TAC[] THEN CONV_TAC COMPLEX_RING);;

let SCH2_PERIOD_INT = prove
 (`!L:complex->complex s c d.
        (!w t. w IN s ==> w + ii * Cx t IN s) /\
        (!w. w IN s ==> L(w + ii * Cx c) = L w + d)
        ==> !k w. integer k /\ w IN s ==> L(w + ii * Cx(k * c)) = L w + Cx k * d`,
  REPEAT GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP SCH2_PERIOD_ITER) THEN
  REWRITE_TAC[INTEGER_CASES] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[REAL_MUL_LNEG; CX_NEG; COMPLEX_MUL_RNEG; COMPLEX_MUL_LNEG] THEN
  REWRITE_TAC[GSYM complex_sub] THEN ASM_SIMP_TAC[]);;

(* The logarithm on the annulus. *)

let SCH2_ANNULUS_LOG = prove
 (`!K r0. &0 < r0 /\ r0 < &1 /\ K holomorphic_on annulus r0 (&1) /\
          (!z. z IN annulus r0 (&1) ==> ~(K z = Cx(&0)))
          ==> ?L m H.
                L holomorphic_on sch2_strip r0 /\ integer m /\
                (!w. w IN sch2_strip r0 ==> K(cexp w) = cexp(L w)) /\
                (!w. w IN sch2_strip r0
                     ==> L(w + ii * Cx(&2 * pi)) = L w + ii * Cx(&2 * m * pi)) /\
                H holomorphic_on annulus r0 (&1) /\
                (!z. z IN annulus r0 (&1)
                     ==> H z = L(clog z) - Cx m * clog z /\
                         K z = cexp(Cx m * clog z + H z))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
    X_CHOOSE_THEN `L:complex->complex` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "KL"))
      (MATCH_MP SCH2_STRIP_LOG_EXISTS th)) THEN
  MP_TAC(SPECL [`K:complex->complex`; `r0:real`; `L:complex->complex`]
    SCH2_STRIP_LOG_PERIOD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN USE_THEN "KL" ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "PER"))) THEN
  MAP_EVERY EXISTS_TAC [`L:complex->complex`; `m:real`;
                        `\z. (L:complex->complex)(clog z) - Cx m * clog z`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!k w. integer k /\ w IN sch2_strip r0
                      ==> (L:complex->complex)(w + ii * Cx(k * &2 * pi)) =
                          L w + Cx k * ii * Cx(&2 * m * pi)`
  (LABEL_TAC "PERK") THENL
   [MATCH_MP_TAC SCH2_PERIOD_INT THEN REWRITE_TAC[SCH2_STRIP_SHIFT] THEN
    USE_THEN "PER" ACCEPT_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `z:complex` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(z = Cx(&0))` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:complex) IN annulus r0 (&1)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM; GSYM COMPLEX_NORM_NZ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_RING `m * c + (l - m * c):complex = l`] THEN
    USE_THEN "KL" (fun th -> MP_TAC(MP (SPEC `clog z` th)
      (MATCH_MP SCH2_STRIP_CLOG (CONJ (ASSUME `&0 < r0`)
        (ASSUME `(z:complex) IN annulus r0 (&1)`))))) THEN
    ASM_SIMP_TAC[CEXP_CLOG]] THEN
  SIMP_TAC[HOLOMORPHIC_ON_OPEN; OPEN_ANNULUS; GSYM complex_differentiable] THEN
  X_GEN_TAC `z0:complex` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(z0 = Cx(&0))` ASSUME_TAC THENL
   [UNDISCH_TAC `(z0:complex) IN annulus r0 (&1)` THEN
    REWRITE_TAC[annulus; IN_ELIM_THM; GSYM COMPLEX_NORM_NZ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `annulus r0 (&1):complex->bool` OPEN_CONTAINS_BALL) THEN
  REWRITE_TAC[OPEN_ANNULUS] THEN DISCH_THEN(MP_TAC o SPEC `z0:complex`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `Lb = \z:complex. clog(z / z0) + clog z0` THEN
  SUBGOAL_THEN
   `!z. dist(z,z0) < min d0 (norm z0)
        ==> (\z. (L:complex->complex)(clog z) - Cx m * clog z) z =
            (\z. L(Lb z) - Cx m * Lb z) z`
  (LABEL_TAC "EQ") THENL
   [X_GEN_TAC `z:complex` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:complex) IN annulus r0 (&1)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
      REWRITE_TAC[IN_BALL] THEN ASM_MESON_TAC[DIST_SYM];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(z = Cx(&0))` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:complex) IN annulus r0 (&1)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM; GSYM COMPLEX_NORM_NZ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `cexp((Lb:complex->complex) z - clog z) = Cx(&1)` MP_TAC THENL
     [EXPAND_TAC "Lb" THEN
      REWRITE_TAC[CEXP_SUB; CEXP_ADD] THEN
      SUBGOAL_THEN `~(z / z0 = Cx(&0))` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[COMPLEX_DIV_EQ_0]; ALL_TAC] THEN
      ASM_SIMP_TAC[CEXP_CLOG] THEN
      UNDISCH_TAC `~(z0 = Cx(&0))` THEN UNDISCH_TAC `~(z = Cx(&0))` THEN
      CONV_TAC COMPLEX_FIELD;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC o MATCH_MP SCH2_CEXP_EQ_1) THEN
    SUBGOAL_THEN `clog z = (Lb:complex->complex) z + ii * Cx(--k * &2 * pi)` ASSUME_TAC THENL
     [UNDISCH_TAC `(Lb:complex->complex) z - clog z = ii * Cx(&2 * k * pi)` THEN
      REWRITE_TAC[CX_MUL; CX_NEG] THEN CONV_TAC COMPLEX_RING;
      ALL_TAC] THEN
    SUBGOAL_THEN `(Lb:complex->complex) z IN sch2_strip r0` ASSUME_TAC THENL
     [SUBGOAL_THEN `clog z IN sch2_strip r0` MP_TAC THENL
       [MATCH_MP_TAC SCH2_STRIP_CLOG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[sch2_strip; IN_ELIM_THM] THEN
      REWRITE_TAC[RE_ADD; RE_MUL_II; IM_CX] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "PERK" (fun th -> REWRITE_TAC[MP (SPECL [`--k:real`; `(Lb:complex->complex) z`] th)
      (CONJ (ONCE_REWRITE_RULE[GSYM INTEGER_NEG] (ASSUME `integer k`))
            (ASSUME `(Lb:complex->complex) z IN sch2_strip r0`))]) THEN
    REWRITE_TAC[CX_MUL; CX_NEG] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_TRANSFORM_AT THEN
  EXISTS_TAC `\z:complex. (L:complex->complex)((Lb:complex->complex) z) - Cx m * Lb z` THEN
  EXISTS_TAC `min d0 (norm(z0:complex))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[COMPLEX_NORM_NZ]; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x':complex` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    USE_THEN "EQ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Lb:complex->complex) complex_differentiable at z0` ASSUME_TAC THENL
   [EXPAND_TAC "Lb" THEN MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_ADD THEN
    REWRITE_TAC[COMPLEX_DIFFERENTIABLE_CONST] THEN
    SUBGOAL_THEN `(\z. clog(z / z0)) = clog o (\z. z / z0)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_COMPOSE_AT THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_DIV_AT THEN
      ASM_REWRITE_TAC[COMPLEX_DIFFERENTIABLE_ID; COMPLEX_DIFFERENTIABLE_CONST];
      MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_AT_CLOG THEN
      ASM_SIMP_TAC[COMPLEX_DIV_REFL; RE_CX] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Lb:complex->complex) z0 = clog z0` ASSUME_TAC THENL
   [EXPAND_TAC "Lb" THEN ASM_SIMP_TAC[COMPLEX_DIV_REFL; CLOG_1; COMPLEX_ADD_LID];
    ALL_TAC] THEN
  MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_SUB THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM o_DEF] THEN
    MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_COMPOSE_AT THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT THEN
    EXISTS_TAC `sch2_strip r0` THEN ASM_REWRITE_TAC[SCH2_STRIP_OPEN_CONVEX] THEN
    MATCH_MP_TAC SCH2_STRIP_CLOG THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_MUL_AT THEN
    ASM_REWRITE_TAC[ETA_AX; COMPLEX_DIFFERENTIABLE_CONST]]);;

(* ------------------------------------------------------------------------- *)
(* The degree.  If K is holomorphic, injective and nonzero on                *)
(* the annulus r0 < |z| < 1, maps it into the unit disc and |K(z)| -> 1 at   *)
(* the unit circle, then K(z) = z * cexp(H z) with H holomorphic: the        *)
(* integer m of SCH2_ANNULUS_LOG is the winding number of K on circles (so   *)
(* |m| <= 1 since these images are simple closed curves), and m > 0 by the   *)
(* mean value of Re H = log|K| - m log|z| over circles, which is constant.  *)
(* ------------------------------------------------------------------------- *)

let SCH2_CIRCLE_PARAM = prove
 (`!f s. &0 < s /\ f continuous_on sphere(Cx(&0),s)
         ==> path_integral (circlepath(Cx(&0),s)) (\z. f z / z) =
             Cx(&2) * Cx pi * ii *
             integral (interval[vec 0,vec 1]) (\t. f(circlepath(Cx(&0),s) t))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PATH_INTEGRAL_UNIQUE THEN
  REWRITE_TAC[has_path_integral] THEN
  SUBGOAL_THEN `(\t. (f:complex->complex)(circlepath(Cx(&0),s) t)) continuous_on
                interval[vec 0,vec 1]`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [REWRITE_TAC[ETA_AX; GSYM path; PATH_CIRCLEPATH];
      REWRITE_TAC[ETA_AX; GSYM path_image] THEN
      ASM_SIMP_TAC[PATH_IMAGE_CIRCLEPATH; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_INTEGRAL_EQ THEN
  EXISTS_TAC `\t. Cx(&2) * Cx pi * ii * (f:complex->complex)(circlepath(Cx(&0),s) t)` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `vector_derivative (circlepath(Cx(&0),s)) (at t within interval[vec 0,vec 1]) =
                  Cx(&2) * Cx(pi) * ii * Cx(s) * cexp(Cx(&2) * Cx pi * ii * Cx(drop t))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN
      ASM_REWRITE_TAC[DROP_VEC; REAL_LT_01] THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
      REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CIRCLEPATH];
      ALL_TAC] THEN
    REWRITE_TAC[CIRCLEPATH; COMPLEX_ADD_LID] THEN
    SUBGOAL_THEN `~(Cx s * cexp(Cx(&2) * Cx pi * ii * Cx(drop t)) = Cx(&0))` MP_TAC THENL
     [REWRITE_TAC[COMPLEX_ENTIRE; CEXP_NZ; CX_INJ] THEN ASM_REAL_ARITH_TAC;
      CONV_TAC COMPLEX_FIELD];
    MATCH_MP_TAC HAS_INTEGRAL_COMPLEX_LMUL THEN
    MATCH_MP_TAC HAS_INTEGRAL_COMPLEX_LMUL THEN
    MATCH_MP_TAC HAS_INTEGRAL_COMPLEX_LMUL THEN
    REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL] THEN
    MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN ASM_REWRITE_TAC[]]);;

(* Real parts of averages over [0,1]. *)

let SCH2_RE_INTEGRAL_BOUNDS = prove
 (`!g:real^1->complex A B.
        g continuous_on interval[vec 0,vec 1] /\
        (!t. t IN interval[vec 0,vec 1] ==> A <= Re(g t) /\ Re(g t) <= B)
        ==> A <= Re(integral (interval[vec 0,vec 1]) g) /\
            Re(integral (interval[vec 0,vec 1]) g) <= B`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RE_DEF] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP INTEGRABLE_CONTINUOUS) THENL
   [MP_TAC(INST [`A:real`,`B:real`]
      (ISPECL [`g:real^1->complex`; `vec 0:real^1`; `vec 1:real^1`; `1`]
        INTEGRAL_COMPONENT_LBOUND));
    MP_TAC(ISPECL [`g:real^1->complex`; `vec 0:real^1`; `vec 1:real^1`; `1`]
      INTEGRAL_COMPONENT_UBOUND)] THEN
  ASM_SIMP_TAC[GSYM RE_DEF; DIMINDEX_2; ARITH; CONTENT_UNIT_1; REAL_MUL_RID]);;

(* Points of a centred circle as exponentials of strip points. *)

let SCH2_CIRCLE_CEXP = prove
 (`!s t. &0 < s
         ==> circlepath(Cx(&0),s) t = cexp(Cx(log s) + ii * Cx(&2 * pi * drop t))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SCH2_CIRCLEPATH_0; CEXP_ADD; GSYM CX_EXP] THEN
  ASM_SIMP_TAC[EXP_LOG]);;

(* The winding number of K on circles is the period m of its logarithm. *)

let SCH2_WINDING_M = prove
 (`!K L m r0 s.
        &0 < r0 /\ r0 < s /\ s < &1 /\ L holomorphic_on sch2_strip r0 /\
        (!w. w IN sch2_strip r0 ==> K(cexp w) = cexp(L w)) /\
        (!w. w IN sch2_strip r0
             ==> L(w + ii * Cx(&2 * pi)) = L w + ii * Cx(&2 * m * pi))
        ==> winding_number(K o circlepath(Cx(&0),s),Cx(&0)) = Cx m`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!t. Cx(log s) + ii * Cx(&2 * pi * drop t) IN sch2_strip r0`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[sch2_strip; IN_ELIM_THM; RE_ADD; RE_CX; RE_MUL_II; IM_CX] THEN
    REWRITE_TAC[REAL_ADD_RID; REAL_NEG_0] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC RAND_CONV [GSYM LOG_1] THEN
      MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `q = \t. (L:complex->complex)(Cx(log s) + ii * Cx(&2 * pi * drop t))` THEN
  SUBGOAL_THEN `(K:complex->complex) o circlepath(Cx(&0),s) = cexp o q` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `t:real^1` THEN
    EXPAND_TAC "q" THEN
    SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SCH2_CIRCLE_CEXP];
    ALL_TAC] THEN
  SUBGOAL_THEN `path(q:real^1->complex)` ASSUME_TAC THENL
   [REWRITE_TAC[path] THEN EXPAND_TAC "q" THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      REWRITE_TAC[CX_MUL] THEN REPEAT(MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL) THEN
      MP_TAC(ISPECL [`\t:real^1. t`; `interval[vec 0:real^1,vec 1]`]
        CONTINUOUS_ON_CX_DROP) THEN
      REWRITE_TAC[CONTINUOUS_ON_ID];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `sch2_strip r0` THEN
      ASM_SIMP_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[WINDING_NUMBER_COMPOSE_CEXP] THEN
  REWRITE_TAC[pathstart; pathfinish] THEN EXPAND_TAC "q" THEN
  REWRITE_TAC[DROP_VEC; REAL_MUL_RZERO; REAL_MUL_RID; COMPLEX_MUL_RZERO;
              COMPLEX_ADD_RID] THEN
  FIRST_ASSUM(MP_TAC o SPEC `Cx(log s)`) THEN
  SUBGOAL_THEN `Cx(log s) IN sch2_strip r0` (fun th -> REWRITE_TAC[th]) THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `vec 0:real^1`) THEN
    REWRITE_TAC[DROP_VEC; REAL_MUL_RZERO; COMPLEX_MUL_RZERO; COMPLEX_ADD_RID];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[CX_MUL] THEN MP_TAC CX_2PII_NZ THEN CONV_TAC COMPLEX_FIELD);;

(* An injective K on the annulus has m in {-1, 0, 1}. *)

let SCH2_M_BOUND = prove
 (`!K L m r0 s.
        &0 < r0 /\ r0 < s /\ s < &1 /\ L holomorphic_on sch2_strip r0 /\
        (!w. w IN sch2_strip r0 ==> K(cexp w) = cexp(L w)) /\
        (!w. w IN sch2_strip r0
             ==> L(w + ii * Cx(&2 * pi)) = L w + ii * Cx(&2 * m * pi)) /\
        K holomorphic_on annulus r0 (&1) /\
        (!z. z IN annulus r0 (&1) ==> ~(K z = Cx(&0))) /\
        (!w z. w IN annulus r0 (&1) /\ z IN annulus r0 (&1) /\ K w = K z ==> w = z)
        ==> m = &1 \/ m = &0 \/ m = -- &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`K:complex->complex`; `L:complex->complex`; `m:real`; `r0:real`;
                `s:real`] SCH2_WINDING_M) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `sphere(Cx(&0),s) SUBSET annulus r0 (&1)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; SCH2_IN_C0; annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `path_image(circlepath(Cx(&0),s)) = sphere(Cx(&0),s)` ASSUME_TAC THENL
   [MATCH_MP_TAC PATH_IMAGE_CIRCLEPATH THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `simple_path((K:complex->complex) o circlepath(Cx(&0),s))` ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLE_PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[SIMPLE_PATH_CIRCLEPATH] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `annulus r0 (&1):complex->bool` THEN
      ASM_SIMP_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(Cx(&0) IN path_image((K:complex->complex) o circlepath(Cx(&0),s)))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PATH_IMAGE_COMPOSE; IN_IMAGE] THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `path_image((K:complex->complex) o circlepath(Cx(&0),s))`
    INSIDE_UNION_OUTSIDE) THEN
  REWRITE_TAC[EXTENSION; IN_UNION; IN_DIFF; IN_UNIV] THEN
  DISCH_THEN(MP_TAC o SPEC `Cx(&0)`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP SIMPLE_CLOSED_PATH_WINDING_NUMBER_INSIDE) THEN
    DISCH_THEN(DISJ_CASES_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `Cx(&0)`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM CX_NEG; CX_INJ] THEN REAL_ARITH_TAC;
    MP_TAC(ISPECL [`(K:complex->complex) o circlepath(Cx(&0),s)`; `Cx(&0)`]
      WINDING_NUMBER_ZERO_IN_OUTSIDE) THEN
    ASM_SIMP_TAC[SIMPLE_PATH_IMP_PATH; PATHSTART_COMPOSE; PATHFINISH_COMPOSE;
                 PATHSTART_CIRCLEPATH; PATHFINISH_CIRCLEPATH] THEN
    REWRITE_TAC[CX_INJ] THEN REAL_ARITH_TAC]);;

let SCH2_LOG_NORM = prove
 (`!m H K z. ~(z = Cx(&0)) /\ K = cexp(Cx m * clog z + H)
             ==> Re H = log(norm K) - m * log(norm z)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[NORM_CEXP; LOG_EXP; RE_ADD; RE_MUL_CX] THEN
  ASM_SIMP_TAC[RE_CLOG] THEN REAL_ARITH_TAC);;

let SCH2_MAX_LT1 = prove
 (`!K:complex->complex u s.
        &0 < s /\ sphere(Cx(&0),s) SUBSET u /\ K continuous_on u /\
        (!z. z IN u ==> norm(K z) < &1)
        ==> ?B. B < &1 /\ !z. norm z = s ==> norm(K z) <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `IMAGE (\z. norm((K:complex->complex) z)) (sphere(Cx(&0),s))`
    COMPACT_ATTAINS_SUP) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o; IMAGE_EQ_EMPTY; SPHERE_EQ_EMPTY] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN REWRITE_TAC[COMPACT_SPHERE; o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `u:complex->bool` THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; FORALL_IN_IMAGE; SCH2_IN_C0] THEN
  DISCH_THEN(X_CHOOSE_THEN `z0:complex` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `norm((K:complex->complex) z0)` THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[SCH2_IN_C0]);;

let SCH2_NORM_CIRCLEPATH_0 = prove
 (`!s t. &0 <= s ==> norm(circlepath(Cx(&0),s) t) = s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SCH2_CIRCLEPATH_0; COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
  ASM_REAL_ARITH_TAC);;

let SCH2_MEAN_CONST = prove
 (`!H r0 s. &0 < r0 /\ r0 < s /\ s < &1 /\ H holomorphic_on annulus r0 (&1)
            ==> integral (interval[vec 0,vec 1]) (\t. H(circlepath(Cx(&0),s) t)) =
                integral (interval[vec 0,vec 1])
                         (\t. H(circlepath(Cx(&0),(&1 + r0) / &2) t))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!s'. r0 < s' /\ s' < &1
                     ==> path_integral (circlepath(Cx(&0),s')) (\z. H z / z) =
                         Cx(&2) * Cx pi * ii *
                         integral (interval[vec 0,vec 1]) (\t. H(circlepath(Cx(&0),s') t))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SCH2_CIRCLE_PARAM THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `annulus r0 (&1):complex->bool` THEN
    ASM_SIMP_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON] THEN
    REWRITE_TAC[SUBSET; SCH2_IN_C0; annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z. (H:complex->complex) z / z`; `annulus r0 (&1):complex->bool`;
                 `s:real`; `(&1 + r0) / &2`] SCH2_CIRCLE_INTEGRALS_EQ) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[OPEN_ANNULUS] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HOLOMORPHIC_ON_DIV THEN
      ASM_REWRITE_TAC[HOLOMORPHIC_ON_ID; ETA_AX] THEN
      REWRITE_TAC[annulus; IN_ELIM_THM; GSYM COMPLEX_NORM_NZ] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SCH2_SHELL_SUB THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `s:real` th) THEN
                          MP_TAC(SPEC `(&1 + r0) / &2` th)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC CX_2PII_NZ THEN CONV_TAC COMPLEX_FIELD);;

let SCH2_MEAN_RE_BOUNDS = prove
 (`!H K m r0 s A B.
        &0 < r0 /\ r0 < s /\ s < &1 /\ H holomorphic_on annulus r0 (&1) /\
        (!z. z IN annulus r0 (&1) ==> K z = cexp(Cx m * clog z + H z)) /\
        (!z. norm z = s ==> A <= log(norm(K z)) /\ log(norm(K z)) <= B)
        ==> A - m * log s <=
            Re(integral (interval[vec 0,vec 1]) (\t. H(circlepath(Cx(&0),s) t))) /\
            Re(integral (interval[vec 0,vec 1]) (\t. H(circlepath(Cx(&0),s) t))) <=
            B - m * log s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM(LABEL_TAC "BD") THEN
  MATCH_MP_TAC SCH2_RE_INTEGRAL_BOUNDS THEN
  CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [REWRITE_TAC[ETA_AX; GSYM path; PATH_CIRCLEPATH]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `annulus r0 (&1):complex->bool` THEN
    ASM_SIMP_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; annulus; IN_ELIM_THM] THEN
    SUBGOAL_THEN `&0 <= s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SCH2_NORM_CIRCLEPATH_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN BETA_TAC THEN
  ABBREV_TAC `z = circlepath(Cx(&0),s) t` THEN
  SUBGOAL_THEN `norm(z:complex) = s` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN MATCH_MP_TAC SCH2_NORM_CIRCLEPATH_0 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:complex) IN annulus r0 (&1)` ASSUME_TAC THENL
   [REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(z = Cx(&0))` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM COMPLEX_NORM_NZ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`m:real`; `(H:complex->complex) z`; `(K:complex->complex) z`;
                 `z:complex`] SCH2_LOG_NORM) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  USE_THEN "BD" (fun th -> MP_TAC(MP (SPEC `z:complex` th)
                                     (ASSUME `norm(z:complex) = s`))) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* m > 0 from the mean value of Re H on circles. *)

let SCH2_M_POS = prove
 (`!K m H r0.
        &0 < r0 /\ r0 < &1 /\ (m = &1 \/ m = &0 \/ m = -- &1) /\
        H holomorphic_on annulus r0 (&1) /\
        (!z. z IN annulus r0 (&1) ==> K z = cexp(Cx m * clog z + H z)) /\
        K continuous_on annulus r0 (&1) /\
        (!z. z IN annulus r0 (&1) ==> norm(K z) < &1) /\
        (!e. &0 < e ==> ?d. &0 < d /\
                            !z. &1 - d < norm z /\ norm z < &1 ==> &1 - e < norm(K z))
        ==> m = &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(LABEL_TAC "LIM") THEN
  ABBREV_TAC `s0 = (&1 + r0) / &2` THEN
  SUBGOAL_THEN `r0 < s0 /\ s0 < &1 /\ &0 < s0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s A B. r0 < s /\ s < &1 /\
            (!z. norm z = s ==> A <= log(norm((K:complex->complex) z)) /\
                                log(norm(K z)) <= B)
            ==> A - m * log s <=
                Re(integral (interval[vec 0,vec 1])
                            (\t. (H:complex->complex)(circlepath(Cx(&0),s0) t))) /\
                Re(integral (interval[vec 0,vec 1])
                            (\t. (H:complex->complex)(circlepath(Cx(&0),s0) t))) <=
                B - m * log s`
  (LABEL_TAC "MB") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL [`H:complex->complex`; `r0:real`; `s:real`] SCH2_MEAN_CONST) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `(&1 + r0) / &2 = s0`] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC SCH2_MEAN_RE_BOUNDS THEN
    MAP_EVERY EXISTS_TAC [`K:complex->complex`; `r0:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `X = Re(integral (interval[vec 0,vec 1])
                              (\t. (H:complex->complex)(circlepath(Cx(&0),s0) t)))` THEN
  SUBGOAL_THEN `!s. r0 < s /\ s < &1 ==> log s < &0` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM LOG_1] THEN
    MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN annulus r0 (&1) ==> &0 < norm((K:complex->complex) z)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[COMPLEX_NORM_NZ; CEXP_NZ]; ALL_TAC] THEN
  (* A circle s1 near 1 where 1/2 < |K| <= B1 < 1. *)
  USE_THEN "LIM" (MP_TAC o SPEC `&1 / &2`) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D1"))) THEN
  ABBREV_TAC `s1 = (&1 + max r0 (&1 - d1)) / &2` THEN
  SUBGOAL_THEN `r0 < s1 /\ s1 < &1 /\ &1 - d1 < s1 /\ &0 < s1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s1" THEN REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:complex->complex`; `annulus r0 (&1):complex->bool`; `s1:real`]
    SCH2_MAX_LT1) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; SCH2_IN_C0; annulus; IN_ELIM_THM] THEN
    ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `B1:real` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `!z. norm z = s1 ==> (z:complex) IN annulus r0 (&1)` ASSUME_TAC THENL
   [REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 / &2 < B1` ASSUME_TAC THENL
   [SUBGOAL_THEN `norm(Cx s1) = s1` ASSUME_TAC THENL
     [REWRITE_TAC[COMPLEX_NORM_CX] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `norm((K:complex->complex)(Cx s1))` THEN
    ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `Cx s1`) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "MB" (MP_TAC o SPECL [`s1:real`; `log(&1 / &2)`; `log B1`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
    CONJ_TAC THEN MATCH_MP_TAC LOG_MONO_LE_IMP THENL
     [CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN
      USE_THEN "D1" (MP_TAC o SPEC `w:complex`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ASM_SIMP_TAC[]];
    STRIP_TAC] THEN
  SUBGOAL_THEN `log B1 < &0` ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM LOG_1] THEN
    MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* If m <= 0 then X < 0. *)
  FIRST_X_ASSUM(DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `X < &0` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= m * log s1` MP_TAC THENL
     [FIRST_X_ASSUM DISJ_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_LE_REFL] THEN
      REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_LID; REAL_NEG_GE0] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* A circle s2 very near 1 where |K| > exp(X/2). *)
  USE_THEN "LIM" (MP_TAC o SPEC `&1 - exp(X / &2)`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_SUB_LT] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_EXP_0] THEN
    REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `&1 - (&1 - x) = x`] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D2"))) THEN
  ABBREV_TAC `s2 = (&1 + max (max r0 (&1 - d2)) (exp(X / &2))) / &2` THEN
  SUBGOAL_THEN `exp(X / &2) < &1` ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_EXP_0] THEN
    REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `r0 < s2 /\ s2 < &1 /\ &1 - d2 < s2 /\ exp(X / &2) < s2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s2" THEN REWRITE_TAC[real_max] THEN
    REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "MB" (MP_TAC o SPECL [`s2:real`; `X / &2`; `&0`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(w:complex) IN annulus r0 (&1)` ASSUME_TAC THENL
     [REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN
      USE_THEN "D2" (MP_TAC o SPEC `w:complex`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[]];
      GEN_REWRITE_TAC RAND_CONV [GSYM LOG_1] THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    STRIP_TAC] THEN
  SUBGOAL_THEN `X / &2 < log s2` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN
    MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT];
    ALL_TAC] THEN
  FIRST_X_ASSUM DISJ_CASES_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_REAL_ARITH_TAC);;

(* The degree-one logarithm. *)

let SCH2_DEGREE_ONE = prove
 (`!K r0. &0 < r0 /\ r0 < &1 /\ K holomorphic_on annulus r0 (&1) /\
          (!z. z IN annulus r0 (&1) ==> ~(K z = Cx(&0)) /\ norm(K z) < &1) /\
          (!w z. w IN annulus r0 (&1) /\ z IN annulus r0 (&1) /\ K w = K z ==> w = z) /\
          (!e. &0 < e ==> ?d. &0 < d /\
                              !z. &1 - d < norm z /\ norm z < &1 ==> &1 - e < norm(K z))
          ==> ?H. H holomorphic_on annulus r0 (&1) /\
                  !z. z IN annulus r0 (&1) ==> K z = z * cexp(H z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`K:complex->complex`; `r0:real`] SCH2_ANNULUS_LOG) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:complex->complex` (X_CHOOSE_THEN `m:real`
    (X_CHOOSE_THEN `H:complex->complex` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(LABEL_TAC "HK") THEN
  SUBGOAL_THEN `!z. z IN annulus r0 (&1) ==> K z = cexp(Cx m * clog z + H z)`
  (LABEL_TAC "KH") THENL
   [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    USE_THEN "HK" (fun th -> ACCEPT_TAC(CONJUNCT2(MP (SPEC `z:complex` th)
                     (ASSUME `(z:complex) IN annulus r0 (&1)`))));
    ALL_TAC] THEN
  MP_TAC(SPECL [`K:complex->complex`; `L:complex->complex`; `m:real`; `r0:real`;
                `(&1 + r0) / &2`] SCH2_M_BOUND) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_REAL_ARITH_TAC);
    DISCH_TAC] THEN
  MP_TAC(SPECL [`K:complex->complex`; `m:real`; `H:complex->complex`; `r0:real`]
    SCH2_M_POS) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY(MATCH_MP_TAC HOLOMORPHIC_ON_IMP_CONTINUOUS_ON THEN FIRST_ASSUM ACCEPT_TAC) THEN
    X_GEN_TAC `z:complex` THEN DISCH_TAC THEN ASM_SIMP_TAC[];
    DISCH_THEN SUBST_ALL_TAC] THEN
  EXISTS_TAC `H:complex->complex` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  USE_THEN "KH" (fun th -> REWRITE_TAC[MP (SPEC `z:complex` th)
                   (ASSUME `(z:complex) IN annulus r0 (&1)`)]) THEN
  SUBGOAL_THEN `~(z = Cx(&0))` ASSUME_TAC THENL
   [UNDISCH_TAC `(z:complex) IN annulus r0 (&1)` THEN
    REWRITE_TAC[annulus; IN_ELIM_THM; GSYM COMPLEX_NORM_NZ] THEN ASM_REAL_ARITH_TAC;
    SIMP_TAC[COMPLEX_MUL_LID; CEXP_ADD; CEXP_CLOG; ASSUME `~(z = Cx(&0))`]]);;

(* ------------------------------------------------------------------------- *)
(* Images of the unit circle under holomorphic injections of an              *)
(* annulus: they are Jordan curves, and the two sides of the circle go to    *)
(* the two sides of the curve.                                               *)
(* ------------------------------------------------------------------------- *)

let SCH2_UNIT_CIRCLE_PATH = prove
 (`!Fa:complex->complex.
        Fa continuous_on sphere(Cx(&0),&1) /\
        (!w z. w IN sphere(Cx(&0),&1) /\ z IN sphere(Cx(&0),&1) /\ Fa w = Fa z ==> w = z)
        ==> simple_path(Fa o circlepath(Cx(&0),&1)) /\
            pathfinish(Fa o circlepath(Cx(&0),&1)) = pathstart(Fa o circlepath(Cx(&0),&1)) /\
            path_image(Fa o circlepath(Cx(&0),&1)) = IMAGE Fa (sphere(Cx(&0),&1))`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `path_image(circlepath(Cx(&0),&1)) = sphere(Cx(&0),&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC PATH_IMAGE_CIRCLEPATH THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATHSTART_CIRCLEPATH;
              PATHFINISH_CIRCLEPATH; PATH_IMAGE_COMPOSE] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SIMPLE_PATH_CONTINUOUS_IMAGE THEN
  ASM_REWRITE_TAC[SIMPLE_PATH_CIRCLEPATH] THEN REAL_ARITH_TAC);;

(* A connected set missing a Jordan curve lies on one side of it. *)

let SCH2_CONNECTED_SIDE = prove
 (`!(c:real^1->complex) (u:complex->bool).
         simple_path c /\ pathfinish c = pathstart c /\ connected u /\
         u INTER path_image c = {}
         ==> u SUBSET inside(path_image c) \/ u SUBSET outside(path_image c)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `c:real^1->complex` JORDAN_INSIDE_OUTSIDE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `connected(u:complex->bool)` THEN
  GEN_REWRITE_TAC LAND_CONV [CONNECTED_OPEN_IN] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`u INTER inside(path_image(c:real^1->complex))`;
                             `u INTER outside(path_image(c:real^1->complex))`]) THEN
  ASM_SIMP_TAC[OPEN_IN_OPEN_INTER] THEN
  UNDISCH_TAC `inside(path_image(c:real^1->complex)) INTER
               outside(path_image c) = {}` THEN
  UNDISCH_TAC `inside(path_image(c:real^1->complex)) UNION
               outside(path_image c) = (:complex) DIFF path_image c` THEN
  UNDISCH_TAC `u INTER path_image(c:real^1->complex) = {}` THEN
  SET_TAC[]);;

let SCH2_CONNECTED_ANN = prove
 (`!r1 r2. connected(annulus r1 r2:complex->bool)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`vec 0:complex`; `r1:real`; `r2:real`] (CONJUNCT1 CONNECTED_ANNULUS)) THEN
  REWRITE_TAC[DIMINDEX_2; LE_REFL; VECTOR_SUB_RZERO; annulus]);;

let SCH2_IMAGE_SIDE_LEMMA = prove
 (`!f:complex->complex a b c s t.
        (!x. x IN a ==> f x IN s) /\ (!x. x IN b ==> f x IN s) /\
        s INTER t = {} /\ IMAGE f c INTER t = {}
        ==> (IMAGE f a UNION IMAGE f c UNION IMAGE f b) INTER t = {}`,
  SET_TAC[]);;

(* The two sides of the unit circle go to the two sides of its image. *)

let SCH2_SIDES = prove
 (`!Fa r1 r2.
        &0 < r1 /\ r1 < &1 /\ &1 < r2 /\ Fa holomorphic_on annulus r1 r2 /\
        (!w z. w IN annulus r1 r2 /\ z IN annulus r1 r2 /\ Fa w = Fa z ==> w = z)
        ==> ((!z. z IN annulus r1 (&1) ==> Fa z IN inside(IMAGE Fa (sphere(Cx(&0),&1)))) /\
             (!z. z IN annulus (&1) r2 ==> Fa z IN outside(IMAGE Fa (sphere(Cx(&0),&1))))) \/
            ((!z. z IN annulus r1 (&1) ==> Fa z IN outside(IMAGE Fa (sphere(Cx(&0),&1)))) /\
             (!z. z IN annulus (&1) r2 ==> Fa z IN inside(IMAGE Fa (sphere(Cx(&0),&1)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM(LABEL_TAC "INJ") THEN
  SUBGOAL_THEN `sphere(Cx(&0),&1) SUBSET annulus r1 r2 /\
                (annulus r1 (&1):complex->bool) SUBSET annulus r1 r2 /\
                (annulus (&1) r2:complex->bool) SUBSET annulus r1 r2 /\
                annulus r1 (&1) INTER sphere(Cx(&0),&1) = {} /\
                annulus (&1) r2 INTER sphere(Cx(&0),&1) = {}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; EXTENSION; IN_UNION; IN_INTER; NOT_IN_EMPTY; SCH2_IN_C0;
                annulus; IN_ELIM_THM] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `Fa:complex->complex` SCH2_UNIT_CIRCLE_PATH) THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `annulus r1 r2:complex->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOLOMORPHIC_ON_IMP_CONTINUOUS_ON THEN
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN USE_THEN "INJ" MATCH_MP_TAC THEN
      UNDISCH_TAC `sphere(Cx(&0),&1) SUBSET annulus r1 r2` THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `c = (Fa:complex->complex) o circlepath(Cx(&0),&1)` THEN STRIP_TAC THEN
  MP_TAC(ISPEC `c:real^1->complex` JORDAN_INSIDE_OUTSIDE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!u. u SUBSET annulus r1 r2 /\ connected u /\ u INTER sphere(Cx(&0),&1) = {}
        ==> IMAGE (Fa:complex->complex) u SUBSET inside(IMAGE Fa (sphere(Cx(&0),&1))) \/
            IMAGE Fa u SUBSET outside(IMAGE Fa (sphere(Cx(&0),&1)))`
  (LABEL_TAC "SIDE") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`c:real^1->complex`; `IMAGE (Fa:complex->complex) u`]
      SCH2_CONNECTED_SIDE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `annulus r1 r2:complex->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOLOMORPHIC_ON_IMP_CONTINUOUS_ON THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
      X_GEN_TAC `y:complex` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:complex` STRIP_ASSUME_TAC)
                                 (X_CHOOSE_THEN `x':complex` STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `x:complex = x'` SUBST_ALL_TAC THENL
       [USE_THEN "INJ" MATCH_MP_TAC THEN
        UNDISCH_TAC `sphere(Cx(&0),&1) SUBSET annulus r1 r2` THEN
        UNDISCH_TAC `(u:complex->bool) SUBSET annulus r1 r2` THEN
        UNDISCH_TAC `(x:complex) IN u` THEN UNDISCH_TAC `(x':complex) IN sphere(Cx(&0),&1)` THEN
        UNDISCH_TAC `(y:complex) = (Fa:complex->complex) x` THEN
        UNDISCH_TAC `(y:complex) = (Fa:complex->complex) x'` THEN
        SET_TAC[];
        UNDISCH_TAC `u INTER sphere(Cx(&0),&1) = {}` THEN
        UNDISCH_TAC `(x':complex) IN u` THEN UNDISCH_TAC `(x':complex) IN sphere(Cx(&0),&1)` THEN
        SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (Fa:complex->complex) (annulus r1 r2))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`Fa:complex->complex`; `annulus r1 r2:complex->bool`]
      HOLOMORPHIC_ON_INVERSE) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL [REWRITE_TAC[OPEN_ANNULUS]; USE_THEN "INJ" ACCEPT_TAC];
      DISCH_THEN(ACCEPT_TAC o CONJUNCT1)];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Fa:complex->complex)(Cx(&1)) IN IMAGE Fa (sphere(Cx(&0),&1)) /\
                (Fa:complex->complex)(Cx(&1)) IN IMAGE Fa (annulus r1 r2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[SCH2_IN_C0; annulus; IN_ELIM_THM; COMPLEX_NORM_CX] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. frontier s = IMAGE (Fa:complex->complex) (sphere(Cx(&0),&1)) /\
                    IMAGE Fa (annulus r1 r2) INTER s = {}
                    ==> F` (LABEL_TAC "FR") THENL
   [X_GEN_TAC `s:complex->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(Fa:complex->complex)(Cx(&1)) IN closure s` MP_TAC THENL
     [UNDISCH_TAC `frontier s = IMAGE (Fa:complex->complex) (sphere(Cx(&0),&1))` THEN
      UNDISCH_TAC `(Fa:complex->complex)(Cx(&1)) IN IMAGE Fa (sphere(Cx(&0),&1))` THEN
      REWRITE_TAC[frontier] THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`IMAGE (Fa:complex->complex) (annulus r1 r2)`; `s:complex->bool`]
      OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(Fa:complex->complex)(Cx(&1)) IN IMAGE Fa (annulus r1 r2)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "SIDE" (fun th ->
    MP_TAC(MP (SPEC `annulus r1 (&1):complex->bool` th)
      (CONJ (ASSUME `(annulus r1 (&1):complex->bool) SUBSET annulus r1 r2`)
        (CONJ (SPECL [`r1:real`; `&1`] SCH2_CONNECTED_ANN)
              (ASSUME `annulus r1 (&1) INTER sphere(Cx(&0),&1) = {}`)))) THEN
    MP_TAC(MP (SPEC `annulus (&1) r2:complex->bool` th)
      (CONJ (ASSUME `(annulus (&1) r2:complex->bool) SUBSET annulus r1 r2`)
        (CONJ (SPECL [`&1`; `r2:real`] SCH2_CONNECTED_ANN)
              (ASSUME `annulus (&1) r2 INTER sphere(Cx(&0),&1) = {}`))))) THEN
  SUBGOAL_THEN
   `IMAGE (Fa:complex->complex) (annulus r1 r2) =
    IMAGE Fa (annulus r1 (&1)) UNION IMAGE Fa (sphere(Cx(&0),&1)) UNION
    IMAGE Fa (annulus (&1) r2)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_UNION] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_UNION; SCH2_IN_C0; annulus; IN_ELIM_THM] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (Fa:complex->complex) (sphere(Cx(&0),&1))` INSIDE_NO_OVERLAP) THEN
  MP_TAC(ISPEC `IMAGE (Fa:complex->complex) (sphere(Cx(&0),&1))` OUTSIDE_NO_OVERLAP) THEN
  UNDISCH_TAC `inside(IMAGE (Fa:complex->complex) (sphere(Cx(&0),&1))) INTER
               outside(IMAGE Fa (sphere(Cx(&0),&1))) = {}` THEN
  DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  STRIP_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN USE_THEN "FR" MATCH_MP_TAC THENL
   [EXISTS_TAC `outside(IMAGE (Fa:complex->complex) (sphere(Cx(&0),&1)))`;
    EXISTS_TAC `inside(IMAGE (Fa:complex->complex) (sphere(Cx(&0),&1)))`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SCH2_IMAGE_SIDE_LEMMA THENL
   [EXISTS_TAC `inside(IMAGE (Fa:complex->complex) (sphere(Cx(&0),&1)))`;
    EXISTS_TAC `outside(IMAGE (Fa:complex->complex) (sphere(Cx(&0),&1)))`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[INTER_COMM]);;

let SCH2_RADIAL_PROJ = prove
 (`!z:complex. ~(z = Cx(&0)) /\ norm z <= &1
               ==> norm(inv(Cx(norm z)) * z) = &1 /\
                   norm(inv(Cx(norm z)) * z - z) = &1 - norm z`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(z:complex)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_NORM_NZ]; ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_RING `i * z - z = (i - Cx(&1)) * z`; GSYM CX_INV; GSYM CX_SUB] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
  SUBGOAL_THEN `&1 <= inv(norm(z:complex))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INV_1_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&1 <= x ==> abs(x - &1) = x - &1`;
               REAL_ARITH `&1 <= x ==> abs x = x`] THEN
  ASM_SIMP_TAC[REAL_SUB_RDISTRIB; REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN REAL_ARITH_TAC);;

(* The Riemann map of the inside and the boundary behaviour of f o Fa.      *)

let SCH2_RIEMANN_K = prove
 (`!Fa r1 r2.
        &0 < r1 /\ r1 < &1 /\ &1 < r2 /\ Fa holomorphic_on annulus r1 r2 /\
        (!w z. w IN annulus r1 r2 /\ z IN annulus r1 r2 /\ Fa w = Fa z ==> w = z) /\
        (!z. z IN annulus r1 (&1) ==> Fa z IN inside(IMAGE Fa (sphere(Cx(&0),&1))))
        ==> ?f g. f holomorphic_on inside(IMAGE Fa (sphere(Cx(&0),&1))) /\
                  g holomorphic_on ball(Cx(&0),&1) /\
                  (!z. z IN inside(IMAGE Fa (sphere(Cx(&0),&1)))
                       ==> f z IN ball(Cx(&0),&1) /\ g(f z) = z) /\
                  (!z. z IN ball(Cx(&0),&1)
                       ==> g z IN inside(IMAGE Fa (sphere(Cx(&0),&1))) /\ f(g z) = z) /\
                  (!e. &0 < e
                       ==> ?d. &0 < d /\
                               !z. &1 - d < norm z /\ norm z < &1
                                   ==> &1 - e < norm(f(Fa z)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `!z. z IN annulus r1 (&1)
                   ==> (Fa:complex->complex) z IN inside(IMAGE Fa (sphere(Cx(&0),&1)))` THEN
  DISCH_THEN(LABEL_TAC "IN") THEN
  UNDISCH_TAC `!w z. w IN annulus r1 r2 /\ z IN annulus r1 r2 /\
                     (Fa:complex->complex) w = Fa z ==> w = z` THEN
  DISCH_THEN(LABEL_TAC "INJ") THEN
  SUBGOAL_THEN `sphere(Cx(&0),&1) SUBSET annulus r1 r2` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; SCH2_IN_C0; annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(Fa:complex->complex) continuous_on annulus r1 r2` ASSUME_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_ON_IMP_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `Fa:complex->complex` SCH2_UNIT_CIRCLE_PATH) THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `annulus r1 r2:complex->bool` THEN
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN USE_THEN "INJ" MATCH_MP_TAC THEN
      UNDISCH_TAC `sphere(Cx(&0),&1) SUBSET annulus r1 r2` THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `c = (Fa:complex->complex) o circlepath(Cx(&0),&1)` THEN STRIP_TAC THEN
  MP_TAC(ISPEC `c:real^1->complex` JORDAN_INSIDE_OUTSIDE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `c:real^1->complex` SIMPLY_CONNECTED_INSIDE_SIMPLE_PATH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `inside(IMAGE (Fa:complex->complex) (sphere(Cx(&0),&1)))`
    RIEMANN_MAPPING_THEOREM) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(inside(IMAGE (Fa:complex->complex) (sphere(Cx(&0),&1))) = (:complex))`
  (fun th -> REWRITE_TAC[th]) THENL
   [DISCH_TAC THEN UNDISCH_TAC `bounded(inside(IMAGE (Fa:complex->complex)
                                       (sphere(Cx(&0),&1))))` THEN
    ASM_REWRITE_TAC[NOT_BOUNDED_UNIV];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:complex->complex` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:complex->complex` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  (* Points of the inside far from the curve have images in a smaller disc. *)
  ASM_CASES_TAC `&1 < e` THENL
   [EXISTS_TAC `&1 - r1` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&0` THEN
    REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `C = IMAGE (g:complex->complex) (cball(Cx(&0),&1 - e))` THEN
  SUBGOAL_THEN `cball(Cx(&0),&1 - e) SUBSET ball(Cx(&0),&1)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; SCH2_IN_C0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `compact(C:complex->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    REWRITE_TAC[COMPACT_CBALL] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `ball(Cx(&0),&1)` THEN ASM_SIMP_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN `C INTER IMAGE (Fa:complex->complex) (sphere(Cx(&0),&1)) = {}`
  ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN
    MP_TAC(ISPEC `IMAGE (Fa:complex->complex) (sphere(Cx(&0),&1))` INSIDE_NO_OVERLAP) THEN
    UNDISCH_TAC `cball(Cx(&0),&1 - e) SUBSET ball(Cx(&0),&1)` THEN
    UNDISCH_TAC `!z. z IN ball(Cx(&0),&1)
                     ==> (g:complex->complex) z IN inside(IMAGE Fa (sphere(Cx(&0),&1))) /\
                         f(g z) = z` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < setdist(C,IMAGE (Fa:complex->complex) (sphere(Cx(&0),&1)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `&0 < x <=> &0 <= x /\ ~(x = &0)`; SETDIST_POS_LE] THEN
    MP_TAC(ISPECL [`C:complex->bool`; `IMAGE (Fa:complex->complex) (sphere(Cx(&0),&1))`]
      SETDIST_EQ_0_COMPACT_CLOSED) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `path_image(c:real^1->complex) = IMAGE Fa (sphere(Cx(&0),&1))` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC CLOSED_PATH_IMAGE THEN
      ASM_SIMP_TAC[SIMPLE_PATH_IMP_PATH];
      DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY; SPHERE_EQ_EMPTY] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    EXPAND_TAC "C" THEN REWRITE_TAC[IMAGE_EQ_EMPTY; CBALL_EQ_EMPTY] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `dl = setdist(C,IMAGE (Fa:complex->complex) (sphere(Cx(&0),&1)))` THEN
  (* Uniform continuity of Fa on the closed annulus (1 + r1)/2 <= |z| <= 1. *)
  ABBREV_TAC `k = cball(Cx(&0),&1) DIFF ball(Cx(&0),(&1 + r1) / &2)` THEN
  SUBGOAL_THEN `compact(k:complex->bool) /\ k SUBSET annulus r1 r2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN
    SIMP_TAC[COMPACT_DIFF; COMPACT_CBALL; OPEN_BALL] THEN
    REWRITE_TAC[SUBSET; IN_DIFF; SCH2_IN_C0; annulus; IN_ELIM_THM] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Fa:complex->complex`; `k:complex->bool`]
    COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `annulus r1 r2:complex->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[uniformly_continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `dl:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min eta ((&1 - r1) / &2)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `z:complex` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(z = Cx(&0))` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM COMPLEX_NORM_NZ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `z1 = inv(Cx(norm(z:complex))) * z` THEN
  SUBGOAL_THEN `norm(z1:complex) = &1 /\ dist(z1,z) < eta` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `z:complex` SCH2_RADIAL_PROJ) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[dist] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:complex) IN k /\ (z1:complex) IN k` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN REWRITE_TAC[IN_DIFF; SCH2_IN_C0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(Fa:complex->complex) z IN inside(IMAGE Fa (sphere(Cx(&0),&1)))`
  ASSUME_TAC THENL
   [USE_THEN "IN" MATCH_MP_TAC THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(Fa:complex->complex) z IN C` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `(f:complex->complex)((Fa:complex->complex) z)` THEN
    ASM_SIMP_TAC[SCH2_IN_C0];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Fa:complex->complex) z1 IN IMAGE Fa (sphere(Cx(&0),&1))` ASSUME_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[SCH2_IN_C0]; ALL_TAC] THEN
  MP_TAC(ISPECL [`C:complex->bool`; `IMAGE (Fa:complex->complex) (sphere(Cx(&0),&1))`;
                 `(Fa:complex->complex) z`; `(Fa:complex->complex) z1`] SETDIST_LE_DIST) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`z:complex`; `z1:complex`]) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`(Fa:complex->complex) z`; `(Fa:complex->complex) z1`] DIST_SYM) THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The reflected map J z = z cexp(H z) on r0 < |z| < 1/r0 for                *)
(* a symmetric H (H(1/cnj z) = --cnj(H z)) that is injective with |J| < 1    *)
(* inside the circle: J(1/cnj z) = 1/cnj(J z), |J| = 1 exactly on the       *)
(* circle, J is injective on the whole annulus and maps the circle onto     *)
(* itself.                                                                   *)
(* ------------------------------------------------------------------------- *)

let SCH2_J_SYM = prove
 (`!H:complex->complex z.
        ~(z = Cx(&0)) /\ H(inv(cnj z)) = --cnj(H z)
        ==> inv(cnj z) * cexp(H(inv(cnj z))) = inv(cnj(z * cexp(H z)))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[CEXP_NEG; CNJ_MUL; CNJ_CEXP; COMPLEX_INV_MUL]);;

let SCH2_J_NORMS = prove
 (`!H r0. &0 < r0 /\ r0 < &1 /\
          (!z. z IN annulus r0 (inv r0) ==> H(inv(cnj z)) = --cnj(H z)) /\
          (!z. z IN annulus r0 (&1) ==> norm(z * cexp(H z)) < &1)
          ==> !z. z IN annulus r0 (inv r0)
                  ==> (norm(z * cexp(H z)) < &1 <=> norm z < &1) /\
                      (norm(z * cexp(H z)) = &1 <=> norm z = &1)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "SYM") (LABEL_TAC "IN1")))) THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < norm(z:complex) /\ ~(z = Cx(&0))` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(z:complex) IN annulus r0 (inv r0)` THEN
    REWRITE_TAC[annulus; IN_ELIM_THM; GSYM COMPLEX_NORM_NZ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm z = &1 ==> norm((z:complex) * cexp(H z)) = &1` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `inv(cnj z) = (z:complex)` ASSUME_TAC THENL
     [SUBGOAL_THEN `z * cnj z = Cx(&1)` MP_TAC THENL
       [REWRITE_TAC[GSYM COMPLEX_NORM_POW_2] THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC COMPLEX_RING;
        SUBGOAL_THEN `~(cnj z = Cx(&0))` MP_TAC THENL
         [ASM_REWRITE_TAC[CNJ_EQ_0]; CONV_TAC COMPLEX_FIELD]];
      ALL_TAC] THEN
    USE_THEN "SYM" (fun th -> MP_TAC(MP (SPEC `z:complex` th)
                     (ASSUME `(z:complex) IN annulus r0 (inv r0)`))) THEN
    REWRITE_TAC[ASSUME `inv(cnj z) = (z:complex)`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `Re((H:complex->complex) z) = &0` ASSUME_TAC THENL
     [UNDISCH_TAC `(H:complex->complex) z = --cnj(H z)` THEN
      REWRITE_TAC[COMPLEX_EQ; RE_NEG; RE_CNJ; IM_NEG; IM_CNJ] THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[COMPLEX_NORM_MUL; NORM_CEXP; REAL_EXP_0; REAL_MUL_RID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 < norm z ==> &1 < norm((z:complex) * cexp(H z))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `inv(cnj z) IN annulus r0 (&1)` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:complex) IN annulus r0 (inv r0)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM; SCH2_INV_CNJ_NORM] THEN STRIP_TAC THEN
      CONJ_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN
        MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC;
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_1] THEN
        MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    USE_THEN "IN1" (fun th -> MP_TAC(MP (SPEC `inv(cnj(z:complex))` th)
                       (ASSUME `inv(cnj(z:complex)) IN annulus r0 (&1)`))) THEN
    MP_TAC(ISPECL [`H:complex->complex`; `z:complex`] SCH2_J_SYM) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "SYM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[COMPLEX_NORM_INV; COMPLEX_NORM_CNJ] THEN
    SUBGOAL_THEN `&0 < norm((z:complex) * cexp(H z))` MP_TAC THENL
     [ASM_REWRITE_TAC[COMPLEX_NORM_NZ; COMPLEX_ENTIRE; CEXP_NZ]; ALL_TAC] THEN
    SPEC_TAC(`norm((z:complex) * cexp(H z))`,`a:real`) THEN REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `a <= &1` THENL
     [MP_TAC(SPEC `a:real` REAL_INV_1_LE) THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm z < &1 ==> norm((z:complex) * cexp(H z)) < &1` ASSUME_TAC THENL
   [DISCH_TAC THEN USE_THEN "IN1" MATCH_MP_TAC THEN
    UNDISCH_TAC `(z:complex) IN annulus r0 (inv r0)` THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `norm(z:complex) < &1` THENL
   [MP_TAC(MP (ASSUME `norm z < &1 ==> norm((z:complex) * cexp(H z)) < &1`)
              (ASSUME `norm(z:complex) < &1`)) THEN
    UNDISCH_TAC `norm(z:complex) < &1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `norm(z:complex) = &1` THENL
   [MP_TAC(MP (ASSUME `norm z = &1 ==> norm((z:complex) * cexp(H z)) = &1`)
              (ASSUME `norm(z:complex) = &1`)) THEN
    UNDISCH_TAC `norm(z:complex) = &1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 < norm(z:complex)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(MP (ASSUME `&1 < norm z ==> &1 < norm((z:complex) * cexp(H z))`)
            (ASSUME `&1 < norm(z:complex)`)) THEN
  UNDISCH_TAC `&1 < norm(z:complex)` THEN REAL_ARITH_TAC);;

let SCH2_J_INJ = prove
 (`!H r0. &0 < r0 /\ r0 < &1 /\ H holomorphic_on annulus r0 (inv r0) /\
          (!z. z IN annulus r0 (inv r0) ==> H(inv(cnj z)) = --cnj(H z)) /\
          (!z. z IN annulus r0 (&1) ==> norm(z * cexp(H z)) < &1) /\
          (!w z. w IN annulus r0 (&1) /\ z IN annulus r0 (&1) /\
                 w * cexp(H w) = z * cexp(H z) ==> w = z)
          ==> !w z. w IN annulus r0 (inv r0) /\ z IN annulus r0 (inv r0) /\
                    w * cexp(H w) = z * cexp(H z) ==> w = z`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
    ASSUME_TAC(MATCH_MP SCH2_J_NORMS
      (CONJ (CONJUNCT1 th) (CONJ (CONJUNCT1(CONJUNCT2 th))
        (CONJ (CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2 th))))
              (CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2 th)))))))))) THEN
  UNDISCH_TAC `!w z. w IN annulus r0 (&1) /\ z IN annulus r0 (&1) /\
                     w * cexp(H w) = z * cexp((H:complex->complex) z) ==> w = z` THEN
  DISCH_THEN(LABEL_TAC "INJ1") THEN
  UNDISCH_TAC `!z. z IN annulus r0 (inv r0) ==> (H:complex->complex)(inv(cnj z)) = --cnj(H z)` THEN
  DISCH_THEN(LABEL_TAC "SYM") THEN
  UNDISCH_TAC `!z. z IN annulus r0 (inv r0)
                   ==> (norm(z * cexp((H:complex->complex) z)) < &1 <=> norm z < &1) /\
                       (norm(z * cexp(H z)) = &1 <=> norm z = &1)` THEN
  DISCH_THEN(LABEL_TAC "NRM") THEN
  SUBGOAL_THEN `r0 < &1 /\ &1 < inv r0` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_INV_1_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`z1:complex`; `z2:complex`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(norm(z1:complex) < &1 <=> norm(z2:complex) < &1) /\
                (norm(z1:complex) = &1 <=> norm(z2:complex) = &1)` STRIP_ASSUME_TAC THENL
   [USE_THEN "NRM" (fun th -> REWRITE_TAC[GSYM(MP (SPEC `z1:complex` th)
                     (ASSUME `(z1:complex) IN annulus r0 (inv r0)`));
                    GSYM(MP (SPEC `z2:complex` th)
                     (ASSUME `(z2:complex) IN annulus r0 (inv r0)`))]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `norm(z1:complex) < &1` THENL
   [SUBGOAL_THEN `norm(z2:complex) < &1` ASSUME_TAC THENL
     [UNDISCH_TAC `norm(z1:complex) < &1 <=> norm(z2:complex) < &1` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "INJ1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z1:complex) IN annulus r0 (inv r0)` THEN
    UNDISCH_TAC `(z2:complex) IN annulus r0 (inv r0)` THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(norm(z2:complex) < &1)` ASSUME_TAC THENL
   [UNDISCH_TAC `norm(z1:complex) < &1 <=> norm(z2:complex) < &1` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `norm(z1:complex) = &1` THENL
   [ALL_TAC;
    (* both outside the circle: reflect *)
    SUBGOAL_THEN `~(norm(z2:complex) = &1)` ASSUME_TAC THENL
     [UNDISCH_TAC `norm(z1:complex) = &1 <=> norm(z2:complex) = &1` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&1 < norm(z1:complex) /\ &1 < norm(z2:complex)` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `!z. z IN annulus r0 (inv r0) /\ &1 < norm z
                      ==> inv(cnj z) IN annulus r0 (&1) /\ ~(z = Cx(&0))`
    ASSUME_TAC THENL
     [REWRITE_TAC[annulus; IN_ELIM_THM; SCH2_INV_CNJ_NORM; GSYM COMPLEX_NORM_NZ] THEN
      REPEAT STRIP_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN
        MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC;
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_1] THEN
        MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> LABEL_TAC "OUT" th) THEN
    SUBGOAL_THEN `!z. z IN annulus r0 (inv r0) /\ &1 < norm z
                      ==> inv(cnj z) * cexp(H(inv(cnj z))) = inv(cnj(z * cexp(H z)))`
    (LABEL_TAC "JS") THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC SCH2_J_SYM THEN CONJ_TAC THENL
       [USE_THEN "OUT" (fun th -> MP_TAC(SPEC `z:complex` th)) THEN
        ASM_SIMP_TAC[];
        USE_THEN "SYM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `inv(cnj z1) IN annulus r0 (&1) /\ inv(cnj z2) IN annulus r0 (&1)`
    STRIP_ASSUME_TAC THENL
     [USE_THEN "OUT" (fun th -> MP_TAC(SPEC `z1:complex` th) THEN
                                MP_TAC(SPEC `z2:complex` th)) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `inv(cnj z1) = inv(cnj(z2:complex))` MP_TAC THENL
     [USE_THEN "INJ1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "JS" (fun th ->
        REWRITE_TAC[MP (SPEC `z1:complex` th)
                       (CONJ (ASSUME `(z1:complex) IN annulus r0 (inv r0)`)
                             (ASSUME `&1 < norm(z1:complex)`));
                    MP (SPEC `z2:complex` th)
                       (CONJ (ASSUME `(z2:complex) IN annulus r0 (inv r0)`)
                             (ASSUME `&1 < norm(z2:complex)`))]) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[COMPLEX_EQ_INV2; CNJ_INJ]]] THEN
  (* both on the circle: open mapping *)
  ASM_CASES_TAC `z1:complex = z2` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `norm(z2:complex) = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `norm(z1:complex) = &1 <=> norm(z2:complex) = &1` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `ep = min (norm(z1 - z2:complex) / &2) (min (&1 - r0) (inv r0 - &1))` THEN
  SUBGOAL_THEN `&0 < ep` ASSUME_TAC THENL
   [EXPAND_TAC "ep" THEN REWRITE_TAC[REAL_LT_MIN] THEN
    ASM_SIMP_TAC[REAL_HALF; NORM_POS_LT; VECTOR_SUB_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(z1:complex,ep) SUBSET annulus r0 (inv r0) /\
                ball(z2:complex,ep) SUBSET annulus r0 (inv r0) /\
                DISJOINT (ball(z1:complex,ep)) (ball(z2,ep))` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL; annulus; IN_ELIM_THM; DISJOINT; EXTENSION; IN_INTER;
                NOT_IN_EMPTY] THEN
    EXPAND_TAC "ep" THEN REWRITE_TAC[REAL_LT_MIN] THEN
    REPEAT CONJ_TAC THEN GEN_TAC THEN
    UNDISCH_TAC `norm(z1:complex) = &1` THEN UNDISCH_TAC `norm(z2:complex) = &1` THEN
    CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z:complex. z * cexp(H z)) holomorphic_on annulus r0 (inv r0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN REWRITE_TAC[HOLOMORPHIC_ON_ID] THEN
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM o_DEF] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE THEN ASM_REWRITE_TAC[HOLOMORPHIC_ON_CEXP];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`annulus r0 (inv r0):complex->bool`; `\z:complex. z * cexp(H z)`]
    OPEN_MAPPING_THM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_ANNULUS; SCH2_CONNECTED_ANN] THEN
    DISCH_THEN(X_CHOOSE_THEN `cc:complex` (LABEL_TAC "CC")) THEN
    SUBGOAL_THEN `Cx((r0 + &1) / &2) IN annulus r0 (&1) /\
                  Cx((r0 + &3) / &4) IN annulus r0 (&1) /\
                  Cx((r0 + &1) / &2) IN annulus r0 (inv r0) /\
                  Cx((r0 + &3) / &4) IN annulus r0 (inv r0)` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[annulus; IN_ELIM_THM; COMPLEX_NORM_CX] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `Cx((r0 + &1) / &2) = Cx((r0 + &3) / &4)` MP_TAC THENL
     [USE_THEN "INJ1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "CC" (fun th ->
        MP_TAC(MP (SPEC `Cx((r0 + &1) / &2)` th)
                  (ASSUME `Cx((r0 + &1) / &2) IN annulus r0 (inv r0)`)) THEN
        MP_TAC(MP (SPEC `Cx((r0 + &3) / &4)` th)
                  (ASSUME `Cx((r0 + &3) / &4) IN annulus r0 (inv r0)`))) THEN
      REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN REFL_TAC;
      REWRITE_TAC[CX_INJ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `ball(z1:complex,ep)` th) THEN
                       MP_TAC(SPEC `ball(z2:complex,ep)` th)) THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN REPEAT DISCH_TAC THEN
  ABBREV_TAC `w0 = (z1:complex) * cexp(H z1)` THEN
  SUBGOAL_THEN `(w0:complex) IN IMAGE (\z. z * cexp(H z)) (ball(z1,ep)) INTER
                IMAGE (\z. z * cexp(H z)) (ball(z2,ep))` ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTER; IN_IMAGE] THEN CONJ_TAC THENL
     [EXISTS_TAC `z1:complex` THEN ASM_REWRITE_TAC[CENTRE_IN_BALL];
      EXISTS_TAC `z2:complex` THEN ASM_REWRITE_TAC[CENTRE_IN_BALL]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (\z. z * cexp((H:complex->complex) z)) (ball(z1,ep)) INTER
                IMAGE (\z. z * cexp(H z)) (ball(z2,ep))` OPEN_CONTAINS_BALL) THEN
  ASM_SIMP_TAC[OPEN_INTER] THEN DISCH_THEN(MP_TAC o SPEC `w0:complex`) THEN
  REWRITE_TAC[ASSUME `(w0:complex) IN IMAGE (\z. z * cexp((H:complex->complex) z))
                        (ball(z1,ep)) INTER IMAGE (\z. z * cexp(H z)) (ball(z2,ep))`] THEN
  DISCH_THEN(X_CHOOSE_THEN `et:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "BALL"))) THEN
  SUBGOAL_THEN `norm(w0:complex) = &1` ASSUME_TAC THENL
   [EXPAND_TAC "w0" THEN
    USE_THEN "NRM" (fun th -> REWRITE_TAC[MP (SPEC `z1:complex` th)
                     (ASSUME `(z1:complex) IN annulus r0 (inv r0)`)]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `w = Cx(&1 - min (et / &2) (&1 / &2)) * w0` THEN
  SUBGOAL_THEN `(w:complex) IN ball(w0,et) /\ norm w < &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN REWRITE_TAC[IN_BALL; dist] THEN
    REWRITE_TAC[COMPLEX_RING `w0 - Cx a * w0 = (Cx(&1) - Cx a) * w0`; GSYM CX_SUB] THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_MUL_RID] THEN
    REWRITE_TAC[real_min] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:complex) IN IMAGE (\z. z * cexp(H z)) (ball(z1,ep)) /\
                w IN IMAGE (\z. z * cexp(H z)) (ball(z2,ep))` MP_TAC THENL
   [USE_THEN "BALL" (fun th -> MATCH_MP_TAC(REWRITE_RULE[SUBSET; IN_INTER] th)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x1:complex` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `x2:complex` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(x1:complex) IN annulus r0 (inv r0) /\ (x2:complex) IN annulus r0 (inv r0)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ball(z1:complex,ep) SUBSET annulus r0 (inv r0)` THEN
    UNDISCH_TAC `ball(z2:complex,ep) SUBSET annulus r0 (inv r0)` THEN
    UNDISCH_TAC `(x1:complex) IN ball(z1,ep)` THEN
    UNDISCH_TAC `(x2:complex) IN ball(z2,ep)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(x1:complex) < &1 /\ norm(x2:complex) < &1` STRIP_ASSUME_TAC THENL
   [USE_THEN "NRM" (fun th -> REWRITE_TAC[GSYM(CONJUNCT1(MP (SPEC `x1:complex` th)
                     (ASSUME `(x1:complex) IN annulus r0 (inv r0)`)));
                    GSYM(CONJUNCT1(MP (SPEC `x2:complex` th)
                     (ASSUME `(x2:complex) IN annulus r0 (inv r0)`)))]) THEN
    UNDISCH_TAC `(w:complex) = x1 * cexp(H x1)` THEN
    UNDISCH_TAC `(w:complex) = x2 * cexp(H x2)` THEN
    REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `x1:complex = x2` ASSUME_TAC THENL
   [USE_THEN "INJ1" MATCH_MP_TAC THEN
    UNDISCH_TAC `(x1:complex) IN annulus r0 (inv r0)` THEN
    UNDISCH_TAC `(x2:complex) IN annulus r0 (inv r0)` THEN
    UNDISCH_TAC `norm(x1:complex) < &1` THEN UNDISCH_TAC `norm(x2:complex) < &1` THEN
    UNDISCH_TAC `(w:complex) = x1 * cexp(H x1)` THEN
    UNDISCH_TAC `(w:complex) = x2 * cexp(H x2)` THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `DISJOINT (ball(z1:complex,ep)) (ball(z2,ep))` THEN
  UNDISCH_TAC `(x1:complex) IN ball(z1,ep)` THEN UNDISCH_TAC `(x2:complex) IN ball(z2,ep)` THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let SCH2_J_ONTO = prove
 (`!H r0. &0 < r0 /\ r0 < &1 /\ H holomorphic_on annulus r0 (inv r0) /\
          (!z. z IN annulus r0 (inv r0) ==> H(inv(cnj z)) = --cnj(H z)) /\
          (!z. z IN annulus r0 (&1) ==> norm(z * cexp(H z)) < &1) /\
          (!w z. w IN annulus r0 (&1) /\ z IN annulus r0 (&1) /\
                 w * cexp(H w) = z * cexp(H z) ==> w = z)
          ==> IMAGE (\z. z * cexp(H z)) (sphere(Cx(&0),&1)) = sphere(Cx(&0),&1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SCH2_J_INJ) THEN
  FIRST_ASSUM(fun th -> ASSUME_TAC(MATCH_MP SCH2_J_NORMS
      (CONJ (CONJUNCT1 th) (CONJ (CONJUNCT1(CONJUNCT2 th))
        (CONJ (CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2 th))))
              (CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2 th)))))))))) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  SUBGOAL_THEN `&1 < inv r0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INV_1_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sphere(Cx(&0),&1) SUBSET annulus r0 (inv r0)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; SCH2_IN_C0; annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z:complex. z * cexp(H z)) holomorphic_on annulus r0 (inv r0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN REWRITE_TAC[HOLOMORPHIC_ON_ID] THEN
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM o_DEF] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE THEN ASM_REWRITE_TAC[HOLOMORPHIC_ON_CEXP];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (\z:complex. z * cexp(H z)) (sphere(Cx(&0),&1)) SUBSET
                sphere(Cx(&0),&1)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; SCH2_IN_C0] THEN X_GEN_TAC `z:complex` THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:complex` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `norm(z * cexp((H:complex->complex) z)) = &1`))
        (concl(SPEC `z:complex` th)))) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `sphere(Cx(&0),&1) SUBSET annulus r0 (inv r0)` THEN
      REWRITE_TAC[SUBSET; SCH2_IN_C0] THEN ASM_MESON_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z:complex. z * cexp(H z)`; `annulus r0 (inv r0):complex->bool`]
    HOLOMORPHIC_ON_INVERSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_ANNULUS] THEN REWRITE_TAC[] THEN ASM_MESON_TAC[];
    DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  MP_TAC(ISPECL [`Cx(&0)`; `&1`] CONNECTED_SPHERE) THEN
  REWRITE_TAC[DIMINDEX_2; LE_REFL; CONNECTED_CLOPEN] THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (\z:complex. z * cexp(H z)) (sphere(Cx(&0),&1))`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `IMAGE (\z:complex. z * cexp(H z)) (sphere(Cx(&0),&1)) =
                    sphere(Cx(&0),&1) INTER
                    IMAGE (\z:complex. z * cexp(H z)) (annulus r0 (inv r0))`
      SUBST1_TAC THENL
       [ALL_TAC; MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_REWRITE_TAC[]] THEN
      MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [UNDISCH_TAC `sphere(Cx(&0),&1) SUBSET annulus r0 (inv r0)` THEN
        UNDISCH_TAC `IMAGE (\z:complex. z * cexp(H z)) (sphere(Cx(&0),&1)) SUBSET
                     sphere(Cx(&0),&1)` THEN SET_TAC[];
        REWRITE_TAC[SUBSET; IN_INTER; IN_IMAGE; SCH2_IN_C0] THEN
        X_GEN_TAC `w:complex` THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `z:complex` STRIP_ASSUME_TAC)) THEN
        EXISTS_TAC `z:complex` THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `z:complex` o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `norm(z * cexp((H:complex->complex) z)) = &1`))
            (concl(SPEC `z:complex` th)))) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
        UNDISCH_TAC `norm(w:complex) = &1` THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC CLOSED_SUBSET THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      REWRITE_TAC[COMPACT_SPHERE] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `annulus r0 (inv r0):complex->bool` THEN
      ASM_SIMP_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON]];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_EQ_EMPTY; SPHERE_EQ_EMPTY] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Auxiliary lemmas for the analytic-collar theorem.                         *)
(* ------------------------------------------------------------------------- *)

(* An injective function has at most one zero; avoid it by shrinking. *)

let SCH2_AVOID_ZERO = prove
 (`!K:complex->complex rA.
        rA < &1 /\
        (!w z. w IN annulus rA (&1) /\ z IN annulus rA (&1) /\ K w = K z ==> w = z)
        ==> ?r0. rA <= r0 /\ r0 < &1 /\
                 !z. z IN annulus r0 (&1) ==> ~(K z = Cx(&0))`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `?z0:complex. z0 IN annulus rA (&1) /\ K z0 = Cx(&0)` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `z0:complex` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `norm(z0:complex)` THEN
    UNDISCH_TAC `(z0:complex) IN annulus rA (&1)` THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN X_GEN_TAC `z:complex` THEN STRIP_TAC THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `z:complex = z0` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    EXISTS_TAC `rA:real` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_MESON_TAC[]]);;

(* Re H -> 0 at the circle when K z = z cexp(H z), |K| < 1 and |K| -> 1. *)

let SCH2_RE_H_LIM = prove
 (`!K:complex->complex H r0.
        &0 < r0 /\ r0 < &1 /\
        (!z. z IN annulus r0 (&1) ==> K z = z * cexp(H z) /\ norm(K z) < &1) /\
        (!e. &0 < e ==> ?d. &0 < d /\
                            !z. &1 - d < norm z /\ norm z < &1 ==> &1 - e < norm(K z))
        ==> !e. &0 < e ==> ?d. &0 < d /\
                               !z. &1 - d < norm z /\ norm z < &1 ==> abs(Re(H z)) < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  ABBREV_TAC `a = exp(--(e / &2))` THEN
  SUBGOAL_THEN `&0 < a /\ a < &1 /\ log a = --(e / &2)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN REWRITE_TAC[REAL_EXP_POS_LT; LOG_EXP] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_EXP_0] THEN
    REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&1 - a`) THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_ARITH `&1 - (&1 - a) = a`]] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d (min (&1 - a) (&1 - r0))` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `z:complex` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:complex) IN annulus r0 (&1)` ASSUME_TAC THENL
   [REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:complex` o check (is_forall o concl)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:complex`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(z:complex)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `Re((H:complex->complex) z) =
                log(norm((K:complex->complex) z)) - log(norm z)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_NORM_MUL; NORM_CEXP] THEN
    ASM_SIMP_TAC[LOG_MUL; REAL_EXP_POS_LT; LOG_EXP] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `log a < log(norm((K:complex->complex) z)) /\
                log(norm((K:complex->complex) z)) < &0 /\
                log a < log(norm(z:complex)) /\ log(norm(z:complex)) < &0`
  MP_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC RAND_CONV [GSYM LOG_1] THEN MATCH_MP_TAC LOG_MONO_LT_IMP THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC RAND_CONV [GSYM LOG_1] THEN MATCH_MP_TAC LOG_MONO_LT_IMP THEN
      ASM_REAL_ARITH_TAC];
    REWRITE_TAC[ASSUME `log a = --(e / &2)`] THEN REAL_ARITH_TAC]);;

let SCH2_RADIAL_PROJ_GEN = prove
 (`!w:complex. ~(w = Cx(&0))
               ==> norm(inv(Cx(norm w)) * w) = &1 /\
                   norm(inv(Cx(norm w)) * w - w) = abs(&1 - norm w)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < norm(w:complex)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_NORM_NZ]; ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_RING `i * z - z = (i - Cx(&1)) * z`; GSYM CX_INV; GSYM CX_SUB] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
  SUBGOAL_THEN `abs(inv(norm(w:complex))) * norm w = &1 /\
                abs(inv(norm(w:complex)) - &1) * norm w = abs(&1 - norm w)`
  (fun th -> REWRITE_TAC[th]) THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; REAL_LT_INV_EQ] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM(MATCH_MP
    (REAL_ARITH `&0 < x ==> abs x = x`) (ASSUME `&0 < norm(w:complex)`))] THEN
  REWRITE_TAC[GSYM REAL_ABS_MUL; REAL_SUB_RDISTRIB] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_LID]);;

(* A margin around the unit circle inside an open set containing it. *)

let SCH2_CIRCLE_MARGIN = prove
 (`!v:complex->bool. open v /\ sphere(Cx(&0),&1) SUBSET v
                     ==> ?d. &0 < d /\ d < &1 /\
                             !w. abs(norm w - &1) < d ==> w IN v`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `(:complex) DIFF v = {}` THENL
   [EXISTS_TAC `&1 / &2` THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `d0 = setdist(sphere(Cx(&0),&1),(:complex) DIFF v)` THEN
  SUBGOAL_THEN `&0 < d0` ASSUME_TAC THENL
   [EXPAND_TAC "d0" THEN
    REWRITE_TAC[REAL_ARITH `&0 < x <=> &0 <= x /\ ~(x = &0)`; SETDIST_POS_LE] THEN
    MP_TAC(ISPECL [`sphere(Cx(&0),&1)`; `(:complex) DIFF v`] SETDIST_EQ_0_COMPACT_CLOSED) THEN
    ASM_REWRITE_TAC[COMPACT_SPHERE; GSYM OPEN_CLOSED] THEN
    REWRITE_TAC[closed; SET_RULE `(:complex) DIFF ((:complex) DIFF v) = v`] THEN
    ASM_REWRITE_TAC[SPHERE_EQ_EMPTY] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `min d0 (&1 / &2)` THEN
  REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `w:complex` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(w = Cx(&0))` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM COMPLEX_NORM_NZ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `w1 = inv(Cx(norm(w:complex))) * w` THEN
  SUBGOAL_THEN `(w1:complex) IN sphere(Cx(&0),&1) /\ dist(w1,w) = abs(norm w - &1)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "w1" THEN REWRITE_TAC[SCH2_IN_C0; dist] THEN
    MP_TAC(SPEC `w:complex` SCH2_RADIAL_PROJ_GEN) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `~((w:complex) IN (:complex) DIFF v) ==> w IN v`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`sphere(Cx(&0),&1)`; `(:complex) DIFF v`; `w1:complex`; `w:complex`]
    SETDIST_LE_DIST) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The analytic-collar Schoenflies theorem.  Fa holomorphic                  *)
(* and injective on r1 < |z| < r2, inner side inside and outer side outside  *)
(* the Jordan curve Fa(circle).  Then a holomorphic injection Phi on a disc  *)
(* of radius R > 1 maps the closed unit disc onto the closed inside, and     *)
(* Phi o J = Fa near the circle for J z = z cexp(L z), L symmetric (so J is  *)
(* a holomorphic self-map of a neighbourhood of the circle preserving it).   *)
(* ------------------------------------------------------------------------- *)

let SCH2_K_FACTS = prove
 (`!Fa f g r1 r2 rA.
        &0 < r1 /\ r1 <= rA /\ rA < &1 /\ &1 < r2 /\
        Fa holomorphic_on annulus r1 r2 /\
        (!w z. w IN annulus r1 r2 /\ z IN annulus r1 r2 /\ Fa w = Fa z ==> w = z) /\
        (!z. z IN annulus r1 (&1) ==> Fa z IN inside(IMAGE Fa (sphere(Cx(&0),&1)))) /\
        f holomorphic_on inside(IMAGE Fa (sphere(Cx(&0),&1))) /\
        (!z. z IN inside(IMAGE Fa (sphere(Cx(&0),&1)))
             ==> f z IN ball(Cx(&0),&1) /\ g(f z) = z)
        ==> (\z. f(Fa z)) holomorphic_on annulus rA (&1) /\
            (!z. z IN annulus rA (&1) ==> norm(f(Fa z)) < &1) /\
            (!w z. w IN annulus rA (&1) /\ z IN annulus rA (&1) /\ f(Fa w) = f(Fa z)
                   ==> w = z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z:complex. z IN annulus rA (&1) ==> z IN annulus r1 (&1) /\
                                                    z IN annulus r1 r2`
  ASSUME_TAC THENL
   [REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM o_DEF] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE_GEN THEN
    EXISTS_TAC `inside(IMAGE (Fa:complex->complex) (sphere(Cx(&0),&1)))` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN
      EXISTS_TAC `annulus r1 r2:complex->bool` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[]];
    X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(f:complex->complex)((Fa:complex->complex) z) IN ball(Cx(&0),&1)` MP_TAC THENL
     [ASM_MESON_TAC[]; REWRITE_TAC[SCH2_IN_C0]];
    MAP_EVERY X_GEN_TAC [`w:complex`; `z:complex`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(Fa:complex->complex) w = Fa z` ASSUME_TAC THENL
     [SUBGOAL_THEN `(Fa:complex->complex) w IN inside(IMAGE Fa (sphere(Cx(&0),&1))) /\
                    (Fa:complex->complex) z IN inside(IMAGE Fa (sphere(Cx(&0),&1)))`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(g:complex->complex)(f((Fa:complex->complex) w)) = Fa w /\
                    (g:complex->complex)(f((Fa:complex->complex) z)) = Fa z`
      MP_TAC THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]] THEN
      MESON_TAC[];
      ASM_MESON_TAC[]]]);;

let SCH2_J_EXISTS = prove
 (`!K r0. &0 < r0 /\ r0 < &1 /\ K holomorphic_on annulus r0 (&1) /\
          (!z. z IN annulus r0 (&1) ==> ~(K z = Cx(&0)) /\ norm(K z) < &1) /\
          (!w z. w IN annulus r0 (&1) /\ z IN annulus r0 (&1) /\ K w = K z ==> w = z) /\
          (!e. &0 < e ==> ?d. &0 < d /\
                              !z. &1 - d < norm z /\ norm z < &1 ==> &1 - e < norm(K z))
          ==> ?L. L holomorphic_on annulus r0 (inv r0) /\
                  (!z. z IN annulus r0 (inv r0) ==> L(inv(cnj z)) = --cnj(L z)) /\
                  (!z. z IN annulus r0 (&1) ==> z * cexp(L z) = K z)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `H:complex->complex` STRIP_ASSUME_TAC o
    MATCH_MP SCH2_DEGREE_ONE) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  MP_TAC(SPECL [`K:complex->complex`; `H:complex->complex`; `r0:real`] SCH2_RE_H_LIM) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`H:complex->complex`; `r0:real`] SCH2_REFLECT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:complex->complex` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `L:complex->complex` THEN ASM_SIMP_TAC[]);;

let SCH2_PHI_CONSTRUCT = prove
 (`!Fa f g L r0 r1 r2.
     &0 < r1 /\ r1 <= r0 /\ inv r2 <= r0 /\ r0 < &1 /\ &1 < r2 /\
     Fa holomorphic_on annulus r1 r2 /\
     (!w z. w IN annulus r1 r2 /\ z IN annulus r1 r2 /\ Fa w = Fa z ==> w = z) /\
     (!z. z IN annulus r1 (&1) ==> Fa z IN inside(IMAGE Fa (sphere(Cx(&0),&1)))) /\
     (!z. z IN annulus (&1) r2 ==> Fa z IN outside(IMAGE Fa (sphere(Cx(&0),&1)))) /\
     g holomorphic_on ball(Cx(&0),&1) /\
     (!z. z IN inside(IMAGE Fa (sphere(Cx(&0),&1)))
          ==> f z IN ball(Cx(&0),&1) /\ g(f z) = z) /\
     (!z. z IN ball(Cx(&0),&1)
          ==> g z IN inside(IMAGE Fa (sphere(Cx(&0),&1))) /\ f(g z) = z) /\
     (!e. &0 < e ==> ?d. &0 < d /\
                         !z. &1 - d < norm z /\ norm z < &1 ==> &1 - e < norm(f(Fa z))) /\
     L holomorphic_on annulus r0 (inv r0) /\
     (!z. z IN annulus r0 (inv r0) ==> L(inv(cnj z)) = --cnj(L z)) /\
     (!z. z IN annulus r0 (&1) ==> z * cexp(L z) = f(Fa z)) /\
     (!z. z IN annulus r0 (&1) ==> norm(f(Fa z)) < &1) /\
     (!w z. w IN annulus r0 (&1) /\ z IN annulus r0 (&1) /\ f(Fa w) = f(Fa z) ==> w = z)
     ==> ?Phi R rho.
           &1 < R /\ Phi holomorphic_on ball(Cx(&0),R) /\
           (!w z. w IN ball(Cx(&0),R) /\ z IN ball(Cx(&0),R) /\ Phi w = Phi z ==> w = z) /\
           IMAGE Phi (cball(Cx(&0),&1)) =
             IMAGE Fa (sphere(Cx(&0),&1)) UNION inside(IMAGE Fa (sphere(Cx(&0),&1))) /\
           r0 <= rho /\ rho < &1 /\
           (!z. z IN annulus rho (inv rho)
                ==> z * cexp(L z) IN ball(Cx(&0),R) /\ Phi(z * cexp(L z)) = Fa z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun (t,l) -> UNDISCH_TAC t THEN DISCH_THEN(LABEL_TAC l))
   [`!w z. w IN annulus r0 (&1) /\ z IN annulus r0 (&1) /\
           (f:complex->complex)((Fa:complex->complex) w) = f(Fa z) ==> w = z`, "KINJ";
    `!z. z IN annulus r0 (&1) ==> norm((f:complex->complex)((Fa:complex->complex) z)) < &1`,
      "KB";
    `!z. z IN annulus r0 (&1) ==> z * cexp((L:complex->complex) z) =
                                  (f:complex->complex)((Fa:complex->complex) z)`, "JK";
    `!z. z IN annulus r0 (inv r0) ==> (L:complex->complex)(inv(cnj z)) = --cnj(L z)`,
      "SYM";
    `!e. &0 < e ==> ?d. &0 < d /\
                        !z. &1 - d < norm z /\ norm z < &1
                            ==> &1 - e < norm((f:complex->complex)((Fa:complex->complex) z))`,
      "LIM";
    `!z. z IN ball(Cx(&0),&1)
         ==> (g:complex->complex) z IN inside(IMAGE (Fa:complex->complex) (sphere(Cx(&0),&1))) /\
             (f:complex->complex)(g z) = z`, "GF";
    `!z. z IN inside(IMAGE (Fa:complex->complex) (sphere(Cx(&0),&1)))
         ==> (f:complex->complex) z IN ball(Cx(&0),&1) /\ (g:complex->complex)(f z) = z`, "FG";
    `!z. z IN annulus (&1) r2
         ==> (Fa:complex->complex) z IN outside(IMAGE Fa (sphere(Cx(&0),&1)))`, "OUT";
    `!z. z IN annulus r1 (&1)
         ==> (Fa:complex->complex) z IN inside(IMAGE Fa (sphere(Cx(&0),&1)))`, "IN";
    `!w z. w IN annulus r1 r2 /\ z IN annulus r1 r2 /\
           (Fa:complex->complex) w = Fa z ==> w = z`, "FINJ"] THEN
  SUBGOAL_THEN `&0 < r0 /\ &1 < inv r0 /\ inv r0 <= r2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INV_1_LT THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(annulus r0 (inv r0):complex->bool) SUBSET annulus r1 r2 /\
                (annulus r0 (&1):complex->bool) SUBSET annulus r1 (&1) /\
                (annulus r0 (&1):complex->bool) SUBSET annulus r0 (inv r0) /\
                sphere(Cx(&0),&1) SUBSET annulus r0 (inv r0)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM; SCH2_IN_C0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* The facts about J. *)
  SUBGOAL_THEN `!z. z IN annulus r0 (&1) ==> norm(z * cexp((L:complex->complex) z)) < &1`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    USE_THEN "JK" (fun th -> REWRITE_TAC[MP (SPEC `z:complex` th)
      (ASSUME `(z:complex) IN annulus r0 (&1)`)]) THEN
    USE_THEN "KB" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w z. w IN annulus r0 (&1) /\ z IN annulus r0 (&1) /\
                      w * cexp((L:complex->complex) w) = z * cexp(L z) ==> w = z`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`w:complex`; `z:complex`] THEN STRIP_TAC THEN
    USE_THEN "KINJ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "JK" (fun th -> REWRITE_TAC[GSYM(MP (SPEC `z:complex` th)
      (ASSUME `(z:complex) IN annulus r0 (&1)`)); GSYM(MP (SPEC `w:complex` th)
      (ASSUME `(w:complex) IN annulus r0 (&1)`))]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`L:complex->complex`; `r0:real`] SCH2_J_INJ) THEN
  MP_TAC(SPECL [`L:complex->complex`; `r0:real`] SCH2_J_ONTO) THEN
  MP_TAC(SPECL [`L:complex->complex`; `r0:real`] SCH2_J_NORMS) THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "SYM" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(LABEL_TAC "JN") THEN DISCH_THEN(LABEL_TAC "JO") THEN
  DISCH_THEN(LABEL_TAC "JI") THEN
  SUBGOAL_THEN `(\z:complex. z * cexp(L z)) holomorphic_on annulus r0 (inv r0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN REWRITE_TAC[HOLOMORPHIC_ON_ID] THEN
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM o_DEF] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE THEN ASM_REWRITE_TAC[HOLOMORPHIC_ON_CEXP];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z:complex. z * cexp(L z)`; `annulus r0 (inv r0):complex->bool`]
    HOLOMORPHIC_ON_INVERSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_ANNULUS] THEN USE_THEN "JI" ACCEPT_TAC; ALL_TAC] THEN
  ABBREV_TAC `V = IMAGE (\z:complex. z * cexp(L z)) (annulus r0 (inv r0))` THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `Ji:complex->complex`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
      (CONJUNCTS_THEN2 (LABEL_TAC "JIJ") (LABEL_TAC "JJI")))))) THEN
  SUBGOAL_THEN `!z. z IN annulus r0 (inv r0) ==> z * cexp((L:complex->complex) z) IN V`
  (LABEL_TAC "JV") THENL
   [EXPAND_TAC "V" THEN REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!w. w IN V ==> (Ji:complex->complex) w IN annulus r0 (inv r0) /\
                               Ji w * cexp((L:complex->complex)(Ji w)) = w`
  (LABEL_TAC "JIV") THENL
   [X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
    USE_THEN "JJI" (fun th -> REWRITE_TAC[MP (SPEC `w:complex` th)
      (ASSUME `(w:complex) IN V`)]) THEN
    UNDISCH_TAC `(w:complex) IN V` THEN EXPAND_TAC "V" THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:complex` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "JIJ" (fun th -> REWRITE_TAC[MP (SPEC `z:complex` th)
      (ASSUME `(z:complex) IN annulus r0 (inv r0)`)]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `V:complex->bool` SCH2_CIRCLE_MARGIN) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "JO" (SUBST1_TAC o SYM) THEN
    EXPAND_TAC "V" THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `dl:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "MARGIN"))))] THEN
  USE_THEN "LIM" (MP_TAC o SPEC `dl / (&2 + dl)`) THEN ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D"))) THEN
  ABBREV_TAC `Phi = \w:complex. if norm w < &1 then (g:complex->complex) w
                                else (Fa:complex->complex)(Ji w)` THEN
  (* Consistency on V. *)
  SUBGOAL_THEN `!w. w IN V ==> (Phi:complex->complex) w = Fa((Ji:complex->complex) w)`
  (LABEL_TAC "CONS") THENL
   [X_GEN_TAC `w:complex` THEN DISCH_TAC THEN EXPAND_TAC "Phi" THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "JIV" (fun th -> STRIP_ASSUME_TAC(MP (SPEC `w:complex` th)
      (ASSUME `(w:complex) IN V`))) THEN
    ABBREV_TAC `z = (Ji:complex->complex) w` THEN
    SUBGOAL_THEN `norm(z:complex) < &1` ASSUME_TAC THENL
     [USE_THEN "JN" (fun th -> REWRITE_TAC[GSYM(CONJUNCT1(MP (SPEC `z:complex` th)
        (ASSUME `(z:complex) IN annulus r0 (inv r0)`)))]) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:complex) IN annulus r0 (&1)` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:complex) IN annulus r0 (inv r0)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(w:complex) = (f:complex->complex)((Fa:complex->complex) z)` SUBST1_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) && rand(concl th) = `w:complex`)) THEN
      USE_THEN "JK" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(Fa:complex->complex) z IN inside(IMAGE Fa (sphere(Cx(&0),&1)))`
    ASSUME_TAC THENL
     [USE_THEN "IN" MATCH_MP_TAC THEN
      UNDISCH_TAC `(annulus r0 (&1):complex->bool) SUBSET annulus r1 (&1)` THEN
      UNDISCH_TAC `(z:complex) IN annulus r0 (&1)` THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "FG" (fun th -> ACCEPT_TAC(CONJUNCT2(MP (SPEC `(Fa:complex->complex) z` th)
      (ASSUME `(Fa:complex->complex) z IN inside(IMAGE Fa (sphere(Cx(&0),&1)))`))));
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. w IN V ==> (Ji:complex->complex) w IN annulus r1 r2` (LABEL_TAC "JIA")
  THENL
   [X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
    USE_THEN "JIV" (MP_TAC o CONJUNCT1 o C MP (ASSUME `(w:complex) IN V`) o SPEC `w:complex`) THEN
    UNDISCH_TAC `(annulus r0 (inv r0):complex->bool) SUBSET annulus r1 r2` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. w IN V ==> (norm((Ji:complex->complex) w) < &1 <=> norm w < &1) /\
                               (norm(Ji w) = &1 <=> norm w = &1)` (LABEL_TAC "JIN") THENL
   [X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
    USE_THEN "JIV" (STRIP_ASSUME_TAC o C MP (ASSUME `(w:complex) IN V`) o SPEC `w:complex`) THEN
    USE_THEN "JN" (MP_TAC o C MP (ASSUME `(Ji:complex->complex) w IN annulus r0 (inv r0)`) o
      SPEC `(Ji:complex->complex) w`) THEN
    REWRITE_TAC[ASSUME `(Ji:complex->complex) w * cexp((L:complex->complex)(Ji w)) = w`] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. w IN V /\ ~(norm w < &1)
                    ==> ~((Fa:complex->complex)((Ji:complex->complex) w) IN
                          inside(IMAGE Fa (sphere(Cx(&0),&1))))` (LABEL_TAC "OUTV") THENL
   [X_GEN_TAC `w:complex` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(norm((Ji:complex->complex) w) < &1)` ASSUME_TAC THENL
     [USE_THEN "JIN" (fun th -> REWRITE_TAC[CONJUNCT1(MP (SPEC `w:complex` th)
        (ASSUME `(w:complex) IN V`))]) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(Ji:complex->complex) w IN annulus r0 (inv r0)` ASSUME_TAC THENL
     [USE_THEN "JIV" (fun th -> REWRITE_TAC[CONJUNCT1(MP (SPEC `w:complex` th)
        (ASSUME `(w:complex) IN V`))]);
      ALL_TAC] THEN
    ABBREV_TAC `z = (Ji:complex->complex) w` THEN
    ASM_CASES_TAC `norm(z:complex) = &1` THENL
     [SUBGOAL_THEN `(Fa:complex->complex) z IN IMAGE Fa (sphere(Cx(&0),&1))` MP_TAC THENL
       [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `z:complex` THEN ASM_REWRITE_TAC[SCH2_IN_C0];
        ALL_TAC] THEN
      MP_TAC(ISPEC `IMAGE (Fa:complex->complex) (sphere(Cx(&0),&1))` INSIDE_NO_OVERLAP) THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:complex) IN annulus (&1) r2` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:complex) IN annulus r0 (inv r0)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN
      UNDISCH_TAC `~(norm(z:complex) = &1)` THEN UNDISCH_TAC `~(norm(z:complex) < &1)` THEN
      UNDISCH_TAC `inv r0 <= r2` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "OUT" (MP_TAC o C MP (ASSUME `(z:complex) IN annulus (&1) r2`) o SPEC `z:complex`) THEN
    MP_TAC(ISPEC `IMAGE (Fa:complex->complex) (sphere(Cx(&0),&1))` INSIDE_INTER_OUTSIDE) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. norm w < &1 ==> (Phi:complex->complex) w = g w` (LABEL_TAC "PIN") THENL
   [X_GEN_TAC `w:complex` THEN DISCH_TAC THEN EXPAND_TAC "Phi" THEN
    REWRITE_TAC[ASSUME `norm(w:complex) < &1`];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. w IN ball(Cx(&0),&1 + dl / &2) /\ ~(norm w < &1) ==> w IN V`
  (LABEL_TAC "BIGV") THENL
   [X_GEN_TAC `w:complex` THEN REWRITE_TAC[SCH2_IN_C0] THEN STRIP_TAC THEN
    USE_THEN "MARGIN" MATCH_MP_TAC THEN
    UNDISCH_TAC `norm(w:complex) < &1 + dl / &2` THEN UNDISCH_TAC `~(norm(w:complex) < &1)` THEN
    UNDISCH_TAC `&0 < dl` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN annulus r0 (inv r0)
                    ==> (Phi:complex->complex)(z * cexp((L:complex->complex) z)) = Fa z`
  (LABEL_TAC "PJ") THENL
   [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `z * cexp((L:complex->complex) z) IN V` ASSUME_TAC THENL
     [USE_THEN "JV" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "CONS" (fun th -> REWRITE_TAC[MP (SPEC `z * cexp((L:complex->complex) z)` th)
      (ASSUME `z * cexp((L:complex->complex) z) IN V`)]) THEN
    USE_THEN "JIJ" (fun th -> REWRITE_TAC[MP (SPEC `z:complex` th)
      (ASSUME `(z:complex) IN annulus r0 (inv r0)`)]);
    ALL_TAC] THEN
  (* Holomorphy. *)
  SUBGOAL_THEN `(Phi:complex->complex) holomorphic_on ball(Cx(&0),&1 + dl / &2)` ASSUME_TAC
  THENL
   [SIMP_TAC[HOLOMORPHIC_ON_OPEN; OPEN_BALL] THEN REWRITE_TAC[GSYM complex_differentiable] THEN
    X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
    ASM_CASES_TAC `norm(w:complex) < &1` THENL
     [MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_TRANSFORM_AT THEN
      MAP_EVERY EXISTS_TAC [`g:complex->complex`; `&1 - norm(w:complex)`] THEN
      ASM_REWRITE_TAC[REAL_SUB_LT] THEN CONJ_TAC THENL
       [X_GEN_TAC `y:complex` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
        USE_THEN "PIN" MATCH_MP_TAC THEN
        UNDISCH_TAC `dist(y:complex,w) < &1 - norm(w:complex)` THEN CONV_TAC NORM_ARITH;
        MATCH_MP_TAC HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT THEN
        EXISTS_TAC `ball(Cx(&0),&1)` THEN ASM_REWRITE_TAC[OPEN_BALL; SCH2_IN_C0]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(w:complex) IN V` ASSUME_TAC THENL
     [USE_THEN "BIGV" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPEC `V:complex->bool` OPEN_CONTAINS_BALL) THEN
    REWRITE_TAC[ASSUME `open(V:complex->bool)`] THEN
    DISCH_THEN(MP_TAC o SPEC `w:complex`) THEN REWRITE_TAC[ASSUME `(w:complex) IN V`] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [`(Fa:complex->complex) o (Ji:complex->complex)`; `e:real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `y:complex` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
      SUBGOAL_THEN `(y:complex) IN V` ASSUME_TAC THENL
       [UNDISCH_TAC `ball(w:complex,e) SUBSET V` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
        DISCH_THEN MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      USE_THEN "CONS" (fun th -> REWRITE_TAC[MP (SPEC `y:complex` th)
        (ASSUME `(y:complex) IN V`)]);
      MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_COMPOSE_AT THEN CONJ_TAC THENL
       [MATCH_MP_TAC HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT THEN
        EXISTS_TAC `V:complex->bool` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT THEN
        EXISTS_TAC `annulus r1 r2:complex->bool` THEN ASM_REWRITE_TAC[OPEN_ANNULUS] THEN
        USE_THEN "JIA" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  (* Injectivity. *)
  SUBGOAL_THEN `!w z. w IN ball(Cx(&0),&1 + dl / &2) /\ z IN ball(Cx(&0),&1 + dl / &2) /\
                      norm w < &1 /\ (Phi:complex->complex) w = Phi z ==> w = z`
  (LABEL_TAC "INJ1") THENL
   [MAP_EVERY X_GEN_TAC [`w:complex`; `z:complex`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(w:complex) IN ball(Cx(&0),&1)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[SCH2_IN_C0]; ALL_TAC] THEN
    ASM_CASES_TAC `norm(z:complex) < &1` THENL
     [SUBGOAL_THEN `(z:complex) IN ball(Cx(&0),&1)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[SCH2_IN_C0]; ALL_TAC] THEN
      SUBGOAL_THEN `(g:complex->complex) w = g z` ASSUME_TAC THENL
       [USE_THEN "PIN" (fun th -> REWRITE_TAC[GSYM(MP (SPEC `w:complex` th)
          (ASSUME `norm(w:complex) < &1`)); GSYM(MP (SPEC `z:complex` th)
          (ASSUME `norm(z:complex) < &1`))]) THEN
        FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      USE_THEN "GF" (fun th -> MP_TAC(CONJUNCT2(MP (SPEC `w:complex` th)
        (ASSUME `(w:complex) IN ball(Cx(&0),&1)`))) THEN
        MP_TAC(CONJUNCT2(MP (SPEC `z:complex` th) (ASSUME `(z:complex) IN ball(Cx(&0),&1)`)))) THEN
      REWRITE_TAC[ASSUME `(g:complex->complex) w = g z`] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:complex) IN V` ASSUME_TAC THENL
     [USE_THEN "BIGV" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "OUTV" (fun th -> MP_TAC(MP (SPEC `z:complex` th)
      (CONJ (ASSUME `(z:complex) IN V`) (ASSUME `~(norm(z:complex) < &1)`)))) THEN
    USE_THEN "CONS" (fun th -> REWRITE_TAC[GSYM(MP (SPEC `z:complex` th)
      (ASSUME `(z:complex) IN V`))]) THEN
    REWRITE_TAC[GSYM(ASSUME `(Phi:complex->complex) w = Phi z`)] THEN
    USE_THEN "PIN" (fun th -> REWRITE_TAC[MP (SPEC `w:complex` th)
      (ASSUME `norm(w:complex) < &1`)]) THEN
    USE_THEN "GF" (fun th -> REWRITE_TAC[CONJUNCT1(MP (SPEC `w:complex` th)
      (ASSUME `(w:complex) IN ball(Cx(&0),&1)`))]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!w z. w IN ball(Cx(&0),&1 + dl / &2) /\ z IN ball(Cx(&0),&1 + dl / &2) /\
                      (Phi:complex->complex) w = Phi z ==> w = z` ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`w:complex`; `z:complex`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `norm(w:complex) < &1` THENL
     [USE_THEN "INJ1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `norm(z:complex) < &1` THENL
     [CONV_TAC SYM_CONV THEN USE_THEN "INJ1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(w:complex) IN V /\ (z:complex) IN V` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN USE_THEN "BIGV" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(Ji:complex->complex) w = Ji z` ASSUME_TAC THENL
     [USE_THEN "FINJ" MATCH_MP_TAC THEN
      USE_THEN "JIA" (fun th -> REWRITE_TAC[MP (SPEC `w:complex` th)
        (ASSUME `(w:complex) IN V`); MP (SPEC `z:complex` th) (ASSUME `(z:complex) IN V`)]) THEN
      USE_THEN "CONS" (fun th -> REWRITE_TAC[GSYM(MP (SPEC `w:complex` th)
        (ASSUME `(w:complex) IN V`)); GSYM(MP (SPEC `z:complex` th)
        (ASSUME `(z:complex) IN V`))]) THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    USE_THEN "JIV" (fun th -> MP_TAC(CONJUNCT2(MP (SPEC `w:complex` th)
      (ASSUME `(w:complex) IN V`))) THEN
      MP_TAC(CONJUNCT2(MP (SPEC `z:complex` th) (ASSUME `(z:complex) IN V`)))) THEN
    REWRITE_TAC[ASSUME `(Ji:complex->complex) w = Ji z`] THEN MESON_TAC[];
    ALL_TAC] THEN
  (* The image of the closed disc. *)
  SUBGOAL_THEN `IMAGE (Phi:complex->complex) (cball(Cx(&0),&1)) =
                IMAGE Fa (sphere(Cx(&0),&1)) UNION inside(IMAGE Fa (sphere(Cx(&0),&1)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `w:complex` THEN
      REWRITE_TAC[SCH2_IN_C0; IN_UNION] THEN DISCH_TAC THEN
      ASM_CASES_TAC `norm(w:complex) < &1` THENL
       [DISJ2_TAC THEN USE_THEN "PIN" (fun th -> REWRITE_TAC[MP (SPEC `w:complex` th)
          (ASSUME `norm(w:complex) < &1`)]) THEN
        SUBGOAL_THEN `(w:complex) IN ball(Cx(&0),&1)` ASSUME_TAC THENL
         [ASM_REWRITE_TAC[SCH2_IN_C0]; ALL_TAC] THEN
        USE_THEN "GF" (fun th -> REWRITE_TAC[CONJUNCT1(MP (SPEC `w:complex` th)
          (ASSUME `(w:complex) IN ball(Cx(&0),&1)`))]);
        ALL_TAC] THEN
      DISJ1_TAC THEN
      SUBGOAL_THEN `(w:complex) IN V` ASSUME_TAC THENL
       [USE_THEN "BIGV" MATCH_MP_TAC THEN ASM_REWRITE_TAC[SCH2_IN_C0] THEN
        UNDISCH_TAC `norm(w:complex) <= &1` THEN UNDISCH_TAC `&0 < dl` THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      USE_THEN "CONS" (fun th -> REWRITE_TAC[MP (SPEC `w:complex` th)
        (ASSUME `(w:complex) IN V`)]) THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(Ji:complex->complex) w` THEN
      REWRITE_TAC[SCH2_IN_C0] THEN
      USE_THEN "JIN" (fun th -> REWRITE_TAC[CONJUNCT2(MP (SPEC `w:complex` th)
        (ASSUME `(w:complex) IN V`))]) THEN
      UNDISCH_TAC `norm(w:complex) <= &1` THEN UNDISCH_TAC `~(norm(w:complex) < &1)` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_UNION] THEN X_GEN_TAC `y:complex` THEN STRIP_TAC THENL
     [UNDISCH_TAC `(y:complex) IN IMAGE Fa (sphere(Cx(&0),&1))` THEN
      REWRITE_TAC[IN_IMAGE; SCH2_IN_C0] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:complex` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(z:complex) IN annulus r0 (inv r0)` ASSUME_TAC THENL
       [UNDISCH_TAC `sphere(Cx(&0),&1) SUBSET annulus r0 (inv r0)` THEN
        REWRITE_TAC[SUBSET; SCH2_IN_C0] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      EXISTS_TAC `z * cexp((L:complex->complex) z)` THEN
      USE_THEN "PJ" (fun th -> REWRITE_TAC[MP (SPEC `z:complex` th)
        (ASSUME `(z:complex) IN annulus r0 (inv r0)`)]) THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      USE_THEN "JN" (MP_TAC o C MP (ASSUME `(z:complex) IN annulus r0 (inv r0)`) o
        SPEC `z:complex`) THEN
      UNDISCH_TAC `norm(z:complex) = &1` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; SCH2_IN_C0] THEN EXISTS_TAC `(f:complex->complex) y` THEN
    USE_THEN "FG" (STRIP_ASSUME_TAC o C MP (ASSUME `(y:complex) IN
      inside(IMAGE (Fa:complex->complex) (sphere(Cx(&0),&1)))`) o SPEC `y:complex`) THEN
    UNDISCH_TAC `(f:complex->complex) y IN ball(Cx(&0),&1)` THEN REWRITE_TAC[SCH2_IN_C0] THEN
    DISCH_TAC THEN
    USE_THEN "PIN" (fun th -> REWRITE_TAC[MP (SPEC `(f:complex->complex) y` th)
      (ASSUME `norm((f:complex->complex) y) < &1`)]) THEN
    REWRITE_TAC[ASSUME `(g:complex->complex)((f:complex->complex) y) = y`] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  (* The witnesses. *)
  MAP_EVERY EXISTS_TAC [`Phi:complex->complex`; `&1 + dl / &2`; `max r0 (&1 - d)`] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `&0 < dl` THEN REAL_ARITH_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    REAL_ARITH_TAC;
    UNDISCH_TAC `r0 < &1` THEN UNDISCH_TAC `&0 < d` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:complex) IN annulus r0 (inv r0)` ASSUME_TAC THENL
   [UNDISCH_TAC `(z:complex) IN annulus (max r0 (&1 - d)) (inv(max r0 (&1 - d)))` THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN
    SUBGOAL_THEN `inv(max r0 (&1 - d)) <= inv r0` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN UNDISCH_TAC `&0 < r0` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "PJ" (fun th -> REWRITE_TAC[MP (SPEC `z:complex` th)
    (ASSUME `(z:complex) IN annulus r0 (inv r0)`)]) THEN
  REWRITE_TAC[SCH2_IN_C0] THEN
  ASM_CASES_TAC `norm(z:complex) <= &1` THENL
   [SUBGOAL_THEN `norm(z * cexp((L:complex->complex) z)) <= &1` MP_TAC THENL
     [USE_THEN "JN" (MP_TAC o C MP (ASSUME `(z:complex) IN annulus r0 (inv r0)`) o
        SPEC `z:complex`) THEN
      UNDISCH_TAC `norm(z:complex) <= &1` THEN REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < dl` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= norm(z * cexp((L:complex->complex) z))` ASSUME_TAC THENL
   [USE_THEN "JN" (MP_TAC o C MP (ASSUME `(z:complex) IN annulus r0 (inv r0)`) o
      SPEC `z:complex`) THEN
    UNDISCH_TAC `~(norm(z:complex) <= &1)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(z = Cx(&0))` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(norm(z:complex) <= &1)` THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:complex->complex`; `z:complex`] SCH2_J_SYM) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "SYM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `u = inv(cnj(z:complex))` THEN DISCH_TAC THEN
  SUBGOAL_THEN `norm(u:complex) = inv(norm(z:complex))` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[COMPLEX_NORM_INV; COMPLEX_NORM_CNJ]; ALL_TAC] THEN
  SUBGOAL_THEN `max r0 (&1 - d) < norm(u:complex) /\ norm(u:complex) < &1`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ASSUME `norm(u:complex) = inv(norm(z:complex))`] THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
      UNDISCH_TAC `(z:complex) IN annulus (max r0 (&1 - d)) (inv(max r0 (&1 - d)))` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN UNDISCH_TAC `&0 < r0` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INV_LT_1 THEN UNDISCH_TAC `~(norm(z:complex) <= &1)` THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:complex) IN annulus r0 (&1)` ASSUME_TAC THENL
   [REWRITE_TAC[annulus; IN_ELIM_THM] THEN
    UNDISCH_TAC `max r0 (&1 - d) < norm(u:complex)` THEN
    UNDISCH_TAC `norm(u:complex) < &1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 - dl / (&2 + dl) < norm(u * cexp((L:complex->complex) u))` MP_TAC THENL
   [USE_THEN "JK" (fun th -> REWRITE_TAC[MP (SPEC `u:complex` th)
      (ASSUME `(u:complex) IN annulus r0 (&1)`)]) THEN
    USE_THEN "D" MATCH_MP_TAC THEN
    UNDISCH_TAC `max r0 (&1 - d) < norm(u:complex)` THEN
    UNDISCH_TAC `norm(u:complex) < &1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ASSUME `u * cexp((L:complex->complex) u) = inv(cnj(z * cexp(L z)))`;
              COMPLEX_NORM_INV; COMPLEX_NORM_CNJ] THEN
  SUBGOAL_THEN `&1 - dl / (&2 + dl) = inv(&1 + dl / &2)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < dl` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  UNDISCH_TAC `&1 <= norm(z * cexp((L:complex->complex) z))` THEN
  SPEC_TAC(`norm(z * cexp((L:complex->complex) z))`,`a:real`) THEN
  X_GEN_TAC `a:real` THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`inv(&1 + dl / &2)`; `inv a`] REAL_LT_INV2) THEN
  REWRITE_TAC[REAL_INV_INV; ASSUME `inv(&1 + dl / &2) < inv a`] THEN
  DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN
  UNDISCH_TAC `&0 < dl` THEN REAL_ARITH_TAC);;

let SCH2_ANALYTIC_COLLAR = prove
 (`!Fa r1 r2.
     &0 < r1 /\ r1 < &1 /\ &1 < r2 /\ Fa holomorphic_on annulus r1 r2 /\
     (!w z. w IN annulus r1 r2 /\ z IN annulus r1 r2 /\ Fa w = Fa z ==> w = z) /\
     (!z. z IN annulus r1 (&1) ==> Fa z IN inside(IMAGE Fa (sphere(Cx(&0),&1)))) /\
     (!z. z IN annulus (&1) r2 ==> Fa z IN outside(IMAGE Fa (sphere(Cx(&0),&1))))
     ==> ?Phi R rho L.
           &1 < R /\ Phi holomorphic_on ball(Cx(&0),R) /\
           (!w z. w IN ball(Cx(&0),R) /\ z IN ball(Cx(&0),R) /\ Phi w = Phi z ==> w = z) /\
           IMAGE Phi (cball(Cx(&0),&1)) =
             IMAGE Fa (sphere(Cx(&0),&1)) UNION inside(IMAGE Fa (sphere(Cx(&0),&1))) /\
           r1 <= rho /\ inv r2 <= rho /\ rho < &1 /\
           L holomorphic_on annulus rho (inv rho) /\
           (!z. z IN annulus rho (inv rho) ==> L(inv(cnj z)) = --cnj(L z)) /\
           (!z. z IN annulus rho (inv rho)
                ==> z * cexp(L z) IN ball(Cx(&0),R) /\ Phi(z * cexp(L z)) = Fa z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `!z. z IN annulus (&1) r2
                   ==> (Fa:complex->complex) z IN outside(IMAGE Fa (sphere(Cx(&0),&1)))` THEN
  DISCH_THEN(LABEL_TAC "OUT") THEN
  UNDISCH_TAC `!z. z IN annulus r1 (&1)
                   ==> (Fa:complex->complex) z IN inside(IMAGE Fa (sphere(Cx(&0),&1)))` THEN
  DISCH_THEN(LABEL_TAC "IN") THEN
  UNDISCH_TAC `!w z. w IN annulus r1 r2 /\ z IN annulus r1 r2 /\
                     (Fa:complex->complex) w = Fa z ==> w = z` THEN
  DISCH_THEN(LABEL_TAC "FINJ") THEN
  MP_TAC(SPECL [`Fa:complex->complex`; `r1:real`; `r2:real`] SCH2_RIEMANN_K) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "FINJ" ACCEPT_TAC; USE_THEN "IN" ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:complex->complex` (X_CHOOSE_THEN `g:complex->complex`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "FG") (CONJUNCTS_THEN2 (LABEL_TAC "GF")
        (LABEL_TAC "LIM"))))))) THEN
  ABBREV_TAC `rA = max r1 (inv r2)` THEN
  SUBGOAL_THEN `r1 <= rA /\ inv r2 <= rA /\ &0 < rA /\ rA < &1 /\ &0 < inv r2 /\
                inv r2 < &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rA" THEN
    SUBGOAL_THEN `&0 < inv r2 /\ inv r2 < &1` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`Fa:complex->complex`; `f:complex->complex`; `g:complex->complex`;
                `r1:real`; `r2:real`; `rA:real`] SCH2_K_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    (USE_THEN "FINJ" ACCEPT_TAC ORELSE USE_THEN "IN" ACCEPT_TAC ORELSE
     USE_THEN "FG" ACCEPT_TAC);
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "KB")
      (LABEL_TAC "KINJ")))] THEN
  MP_TAC(SPECL [`\z:complex. (f:complex->complex)((Fa:complex->complex) z)`; `rA:real`]
    SCH2_AVOID_ZERO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NZ" o BETA_RULE)))) THEN
  SUBGOAL_THEN `(annulus r0 (&1):complex->bool) SUBSET annulus rA (&1)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN annulus r0 (&1)
                    ==> norm((f:complex->complex)((Fa:complex->complex) z)) < &1`
  (LABEL_TAC "KB0") THENL
   [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN USE_THEN "KB" MATCH_MP_TAC THEN
    UNDISCH_TAC `(annulus r0 (&1):complex->bool) SUBSET annulus rA (&1)` THEN
    UNDISCH_TAC `(z:complex) IN annulus r0 (&1)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w z. w IN annulus r0 (&1) /\ z IN annulus r0 (&1) /\
                      (f:complex->complex)((Fa:complex->complex) w) = f(Fa z) ==> w = z`
  (LABEL_TAC "KINJ0") THENL
   [MAP_EVERY X_GEN_TAC [`w:complex`; `z:complex`] THEN STRIP_TAC THEN
    USE_THEN "KINJ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(annulus r0 (&1):complex->bool) SUBSET annulus rA (&1)` THEN
    UNDISCH_TAC `(z:complex) IN annulus r0 (&1)` THEN
    UNDISCH_TAC `(w:complex) IN annulus r0 (&1)` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`\z:complex. (f:complex->complex)((Fa:complex->complex) z)`; `r0:real`]
    SCH2_J_EXISTS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN
      EXISTS_TAC `annulus rA (&1):complex->bool` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `z:complex` THEN DISCH_TAC THEN CONJ_TAC THENL
       [USE_THEN "NZ" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        USE_THEN "KB0" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC];
      USE_THEN "KINJ0" ACCEPT_TAC;
      USE_THEN "LIM" ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:complex->complex` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "SYM") ASSUME_TAC) o BETA_RULE)) THEN
  SUBGOAL_THEN `r1 <= r0 /\ inv r2 <= r0` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`Fa:complex->complex`; `f:complex->complex`; `g:complex->complex`;
                `L:complex->complex`; `r0:real`; `r1:real`; `r2:real`]
    SCH2_PHI_CONSTRUCT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Phi:complex->complex` (X_CHOOSE_THEN `R:real`
    (X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(annulus rho (inv rho):complex->bool) SUBSET annulus r0 (inv r0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN X_GEN_TAC `z:complex` THEN
    SUBGOAL_THEN `inv rho <= inv r0` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`Phi:complex->complex`; `R:real`; `rho:real`; `L:complex->complex`] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN
    EXISTS_TAC `annulus r0 (inv r0):complex->bool` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `z:complex` THEN DISCH_TAC THEN USE_THEN "SYM" MATCH_MP_TAC THEN
    UNDISCH_TAC `(annulus rho (inv rho):complex->bool) SUBSET annulus r0 (inv r0)` THEN
    UNDISCH_TAC `(z:complex) IN annulus rho (inv rho)` THEN SET_TAC[];
    FIRST_ASSUM ACCEPT_TAC]);;

