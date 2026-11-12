(* ========================================================================= *)
(* pc_wan_sob2c: planar slicing for W^(1,2) maps.                            *)
(* Polar Fubini for the Dirichlet density (WAN_POLAR_DIR), absolute          *)
(* continuity on almost every circle (WAN_CIRCLE_ACL) and the                *)
(* Courant-Lebesgue lemma, interior and at a boundary point.                 *)
(* The polar map is the library FUBINI_POLAR (Multivariate/transcendentals)  *)
(* composed with a translation and a rotation.                               *)
(* ========================================================================= *)

needs "src/pc_wan_sob2pb.ml";;
prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Polar coordinates around a centre, with an angular offset.               *)
(* ------------------------------------------------------------------------- *)

let WAN_CIRC_CEXP = prove
 (`!(a:real^2) r t. wan_circ a r t = a + Cx r * cexp(ii * Cx t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_circ] THEN AP_TERM_TAC THEN
  REWRITE_TAC[COMPLEX_EQ; RE_MUL_CX; IM_MUL_CX; RE_CEXP; IM_CEXP; RE_MUL_II; IM_MUL_II;
              RE_CX; IM_CX; REAL_NEG_0; REAL_EXP_0; REAL_MUL_LID] THEN
  REWRITE_TAC[RE_DEF; IM_DEF; VECTOR_MUL_COMPONENT; VECTOR_2]);;

let WAN_CIRC_NORM = prove
 (`!(a:real^2) r t. norm(wan_circ a r t - a) = abs r`,
  REWRITE_TAC[WAN_CIRC_CEXP; VECTOR_ARITH `(a + x) - a:real^N = x`] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; NORM_CEXP_II; REAL_MUL_RID]);;

let WAN_ROT_INTEGRAL = prove
 (`!(f:complex->real^M) c b.
     norm c = &1
     ==> ((\z. f(c * z)) absolutely_integrable_on (:complex) /\
          integral (:complex) (\z. f(c * z)) = b <=>
          f absolutely_integrable_on (:complex) /\ integral (:complex) f = b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:complex->real^M`; `\z:complex. c * z`; `(:complex)`; `b:real^M`]
                HAS_ABSOLUTE_INTEGRAL_CHANGE_OF_VARIABLES_LINEAR) THEN
  REWRITE_TAC[LINEAR_COMPLEX_MUL] THEN
  SUBGOAL_THEN `abs(det(matrix(\z:complex. c * z))) = &1` SUBST1_TAC THENL
   [MP_TAC(ISPEC `matrix(\z:complex. c * z)` DET_ORTHOGONAL_MATRIX) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC ORTHOGONAL_MATRIX_MATRIX THEN
      ASM_REWRITE_TAC[ORTHOGONAL_TRANSFORMATION_COMPLEX_MUL];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (\z:complex. c * z) (:complex) = (:complex)` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN X_GEN_TAC `w:complex` THEN
    EXISTS_TAC `inv c * w:complex` THEN
    SUBGOAL_THEN `~(c = Cx(&0))` MP_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `norm(c:complex) = &1` THEN
      ASM_REWRITE_TAC[COMPLEX_NORM_0] THEN REAL_ARITH_TAC;
      CONV_TAC COMPLEX_FIELD];
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_MUL_LID; ETA_AX]);;

let WAN_FUBINI_POLAR_CIRC = prove
 (`!(f:real^2->real^M) a al.
     f absolutely_integrable_on (:real^2)
     ==> negligible
          {r | &0 <= drop r /\
               ~((\t. drop r % f(wan_circ a (drop r) (al + drop t)))
                 absolutely_integrable_on interval[vec 0,lift(&2 * pi)])} /\
         (\r. integral (interval[vec 0,lift(&2 * pi)])
                (\t. drop r % f(wan_circ a (drop r) (al + drop t))))
         absolutely_integrable_on {r | &0 <= drop r} /\
         integral {r | &0 <= drop r}
           (\r. integral (interval[vec 0,lift(&2 * pi)])
                  (\t. drop r % f(wan_circ a (drop r) (al + drop t)))) =
         integral (:real^2) f`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `\z:complex. (f:real^2->real^M)(a + cexp(ii * Cx al) * z)` FUBINI_POLAR) THEN
  SUBGOAL_THEN
   `!r t. a + cexp(ii * Cx al) * (Cx r * cexp(ii * Cx t)) = wan_circ a r (al + t)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[WAN_CIRC_CEXP; CX_ADD; COMPLEX_ADD_LDISTRIB; CEXP_ADD] THEN
    REPEAT GEN_TAC THEN AP_TERM_TAC THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z:complex. (f:real^2->real^M)(a + z)`; `cexp(ii * Cx al)`;
                 `integral (:real^2) (f:real^2->real^M)`] WAN_ROT_INTEGRAL) THEN
  REWRITE_TAC[NORM_CEXP_II] THEN
  SUBGOAL_THEN
   `(\z:complex. (f:real^2->real^M)(a + z)) absolutely_integrable_on (:complex) /\
    integral (:complex) (\z. f(a + z)) = integral (:real^2) f`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[ABSOLUTELY_INTEGRABLE_TRANSLATION; INTEGRAL_TRANSLATION] THEN
    SUBGOAL_THEN `IMAGE (\x:real^2. a + x) (:real^2) = (:real^2)` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN
      MESON_TAC[VECTOR_ARITH `a + (x - a):real^N = x`];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN SIMP_TAC[]);;

let WAN_ANNULUS_EQ = prove
 (`!(a:real^2) r1 r2.
     {x | r1 < norm(x - a) /\ norm(x - a) < r2} = ball(a,r2) DIFF cball(a,r1) /\
     lebesgue_measurable {x | r1 < norm(x - a) /\ norm(x - a) < r2} /\
     measurable {x | r1 < norm(x - a) /\ norm(x - a) < r2}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{x | r1 < norm(x - a) /\ norm(x - a) < r2} = ball(a:real^2,r2) DIFF cball(a,r1)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_BALL; IN_CBALL; dist] THEN
    GEN_TAC THEN REWRITE_TAC[NORM_SUB] THEN REAL_ARITH_TAC;
    SIMP_TAC[LEBESGUE_MEASURABLE_DIFF; LEBESGUE_MEASURABLE_BALL; LEBESGUE_MEASURABLE_CBALL;
             MEASURABLE_DIFF; MEASURABLE_BALL; MEASURABLE_CBALL]]);;

(* ------------------------------------------------------------------------- *)
(* Polar Fubini on an annulus, and WAN_POLAR_DIR.                            *)
(* ------------------------------------------------------------------------- *)

let WAN_POLAR_ANNULUS = prove
 (`!(g:real^2->real^M) a al r1 r2.
     &0 <= r1 /\ r1 <= r2 /\
     g absolutely_integrable_on {x | r1 < norm(x - a) /\ norm(x - a) < r2}
     ==> (?N. negligible N /\
              !r. r1 < r /\ r < r2 /\ ~(lift r IN N)
                  ==> (\t. g(wan_circ a r (al + drop t))) absolutely_integrable_on
                      interval[vec 0,lift(&2 * pi)]) /\
         (\r. drop r % integral (interval[vec 0,lift(&2 * pi)])
                         (\t. g(wan_circ a (drop r) (al + drop t))))
         absolutely_integrable_on interval[lift r1,lift r2] /\
         integral (interval[lift r1,lift r2])
           (\r. drop r % integral (interval[vec 0,lift(&2 * pi)])
                           (\t. g(wan_circ a (drop r) (al + drop t)))) =
         integral {x | r1 < norm(x - a) /\ norm(x - a) < r2} g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `A = {x:real^2 | r1 < norm(x - a) /\ norm(x - a) < r2}` THEN
  ABBREV_TAC `f = \x:real^2. if x IN A then (g:real^2->real^M) x else vec 0` THEN
  SUBGOAL_THEN `(f:real^2->real^M) absolutely_integrable_on (:real^2) /\
                integral (:real^2) f = integral (A:real^2->bool) g`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN
    ASM_REWRITE_TAC[ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV; INTEGRAL_RESTRICT_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r t. (f:real^2->real^M)(wan_circ a r t) =
          if r1 < abs r /\ abs r < r2 then g(wan_circ a r t) else vec 0`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "f" THEN EXPAND_TAC "A" THEN
    REWRITE_TAC[IN_ELIM_THM; WAN_CIRC_NORM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^2->real^M`; `a:real^2`; `al:real`] WAN_FUBINI_POLAR_CIRC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC
   `N0 = {r | &0 <= drop r /\
              ~((\t. drop r % (f:real^2->real^M)(wan_circ a (drop r) (al + drop t)))
                absolutely_integrable_on interval[vec 0,lift(&2 * pi)])}` THEN
  ABBREV_TAC
   `H = \r. integral (interval[vec 0,lift(&2 * pi)])
              (\t. drop r % (f:real^2->real^M)(wan_circ a (drop r) (al + drop t)))` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!r. &0 <= drop r /\ ~(r1 < drop r /\ drop r < r2) ==> (H:real^1->real^M) r = vec 0`
  (LABEL_TAC "k2") THENL
   [X_GEN_TAC `r:real^1` THEN STRIP_TAC THEN EXPAND_TAC "H" THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`; VECTOR_MUL_RZERO; INTEGRAL_0];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. r1 < drop r /\ drop r < r2 /\ ~(r IN N0)
        ==> (\t. (g:real^2->real^M)(wan_circ a (drop r) (al + drop t)))
            absolutely_integrable_on interval[vec 0,lift(&2 * pi)] /\
            (H:real^1->real^M) r =
            drop r % integral (interval[vec 0,lift(&2 * pi)])
                       (\t. g(wan_circ a (drop r) (al + drop t)))`
  (LABEL_TAC "k3") THENL
   [X_GEN_TAC `r:real^1` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < drop r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\t. drop r % (g:real^2->real^M)(wan_circ a (drop r) (al + drop t)))
      absolutely_integrable_on interval[vec 0,lift(&2 * pi)]`
    ASSUME_TAC THENL
     [UNDISCH_TAC `~((r:real^1) IN N0)` THEN EXPAND_TAC "N0" THEN
      ASM_SIMP_TAC[IN_ELIM_THM; REAL_LT_IMP_LE; REAL_ARITH `&0 < x ==> abs x = x`];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\t. (g:real^2->real^M)(wan_circ a (drop r) (al + drop t)))
      absolutely_integrable_on interval[vec 0,lift(&2 * pi)]`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `inv(drop r)` o MATCH_MP ABSOLUTELY_INTEGRABLE_CMUL) THEN
      ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID; ETA_AX];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "H" THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_ARITH `&0 < x ==> abs x = x`] THEN
    MATCH_MP_TAC INTEGRAL_CMUL THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. r IN interval[lift r1,lift r2] DIFF (lift r1 INSERT lift r2 INSERT N0)
        ==> drop r % integral (interval[vec 0,lift(&2 * pi)])
                       (\t. (g:real^2->real^M)(wan_circ a (drop r) (al + drop t))) =
            (H:real^1->real^M) r`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real^1` THEN
    REWRITE_TAC[IN_DIFF; IN_INSERT; IN_INTERVAL_1; GSYM DROP_EQ; LIFT_DROP; DE_MORGAN_THM] THEN
    STRIP_TAC THEN CONV_TAC SYM_CONV THEN USE_THEN "k3" (MP_TAC o SPEC `r:real^1`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `negligible(lift r1 INSERT lift r2 INSERT (N0:real^1->bool))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NEGLIGIBLE_INSERT]; ALL_TAC] THEN
  SUBGOAL_THEN `interval[lift r1,lift r2] SUBSET {r:real^1 | &0 <= drop r}` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTERVAL_1; IN_ELIM_THM; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(H:real^1->real^M) absolutely_integrable_on interval[lift r1,lift r2]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `{r:real^1 | &0 <= drop r}` THEN
    ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_INTERVAL];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [EXISTS_TAC `N0:real^1->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    USE_THEN "k3" (MP_TAC o SPEC `lift r`) THEN
    REWRITE_TAC[LIFT_DROP] THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] ABSOLUTELY_INTEGRABLE_SPIKE) THEN
    MAP_EVERY EXISTS_TAC [`H:real^1->real^M`; `lift r1 INSERT lift r2 INSERT (N0:real^1->bool)`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `integral (interval[lift r1,lift r2]) (H:real^1->real^M)` THEN CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_SPIKE THEN
      EXISTS_TAC `lift r1 INSERT lift r2 INSERT (N0:real^1->bool)` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `integral {r:real^1 | &0 <= drop r} (H:real^1->real^M)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    ONCE_REWRITE_TAC[GSYM INTEGRAL_RESTRICT_UNIV] THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `r:real^1` THEN
    ASM_CASES_TAC `(r:real^1) IN interval[lift r1,lift r2]` THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `(r:real^1) IN {r | &0 <= drop r}` (fun th -> REWRITE_TAC[th]) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    USE_THEN "k2" MATCH_MP_TAC THEN
    UNDISCH_TAC `(r:real^1) IN {r | &0 <= drop r}` THEN
    UNDISCH_TAC `~((r:real^1) IN interval[lift r1,lift r2])` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INTERVAL_1; LIFT_DROP] THEN REAL_ARITH_TAC]);;

let WAN_DIR_DENSITY_ABS_INT = prove
 (`!(s:real^2->bool) (u:real^2->real^K) t.
     wan_w12 s u /\ lebesgue_measurable t /\ t SUBSET s
     ==> (\x. lift(norm(wan_wd s 1 u x) pow 2 + norm(wan_wd s 2 u x) pow 2))
         absolutely_integrable_on t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= 2 ==> wan_wd s i (u:real^2->real^K) IN lspace t (&2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_SIMP_TAC[WAN_WD_WORKS; DIMINDEX_2];
    ALL_TAC] THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_INTEGRABLE_BOUND THEN
  EXISTS_TAC `\x. lift(norm(wan_wd s 1 (u:real^2->real^K) x) pow 2 +
                       norm(wan_wd s 2 u x) pow 2)` THEN
  REWRITE_TAC[NORM_LIFT; LIFT_DROP] THEN
  SIMP_TAC[REAL_ARITH `&0 <= x /\ &0 <= y ==> abs(x + y) = x + y`; REAL_LE_POW_2;
           REAL_LE_REFL] THEN
  REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC INTEGRABLE_ADD THEN
  CONJ_TAC THEN MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN
  REWRITE_TAC[ETA_AX] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC);;

let WAN_POLAR_DIR = prove
 (`!(kk:K->bool). WAN_POLAR_DIR_STATEMENT kk`,
  GEN_TAC THEN REWRITE_TAC[WAN_POLAR_DIR_STATEMENT] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\x. lift(norm(wan_wd (ball(a,R)) 1 (u:real^2->real^K) x) pow 2 +
              norm(wan_wd (ball(a,R)) 2 u x) pow 2)`;
    `a:real^2`; `&0`; `r1:real`; `r2:real`] WAN_POLAR_ANNULUS) THEN
  REWRITE_TAC[REAL_ADD_LID] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC WAN_DIR_DENSITY_ABS_INT THEN
    ASM_REWRITE_TAC[WAN_ANNULUS_EQ] THEN
    SIMP_TAC[LEBESGUE_MEASURABLE_DIFF; LEBESGUE_MEASURABLE_BALL; LEBESGUE_MEASURABLE_CBALL] THEN
    REWRITE_TAC[SUBSET; IN_DIFF; IN_BALL] THEN ASM_MESON_TAC[REAL_LTE_TRANS];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!r:real^1 X:real^1. lift(drop r * drop X) = drop r % X`
  (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[LIFT_CMUL; LIFT_DROP]; ALL_TAC] THEN
  ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE]);;

(* ------------------------------------------------------------------------- *)
(* Smooth maps along circles: the derivative and the fundamental theorem.   *)
(* ------------------------------------------------------------------------- *)

let WAN_CIRC_VDERIV = prove
 (`!(a:real^2) r al t.
     ((\s. wan_circ a r (al + drop s)) has_vector_derivative
      (r % vector[--sin(al + drop t); cos(al + drop t)])) (at t)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `r % vector[--sin(al + drop t); cos(al + drop t)] =
    Cx r * ii * cexp(ii * (Cx al + Cx(drop t)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM CX_ADD] THEN
    REWRITE_TAC[COMPLEX_EQ; RE_MUL_CX; IM_MUL_CX; RE_MUL_II; IM_MUL_II; RE_CEXP; IM_CEXP;
                RE_CX; IM_CX; REAL_NEG_0; REAL_EXP_0; REAL_MUL_LID] THEN
    REWRITE_TAC[RE_DEF; IM_DEF; VECTOR_MUL_COMPONENT; VECTOR_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[WAN_CIRC_CEXP; CX_ADD] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_REAL_COMPLEX THEN
  COMPLEX_DIFF_TAC THEN CONV_TAC COMPLEX_RING);;

let WAN_VECTOR2_BASIS = prove
 (`!x y. vector[x; y]:real^2 = x % basis 1 + y % basis 2`,
  SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_ADD_COMPONENT;
           VECTOR_MUL_COMPONENT; BASIS_COMPONENT; ARITH] THEN
  REAL_ARITH_TAC);;

let WAN_CIRC_COMPOSE_VDERIV = prove
 (`!(w:real^2->real^K) a r al t.
     smooth_map_on (:real^2) w
     ==> ((\s. w(wan_circ a r (al + drop s))) has_vector_derivative
          (r % (--(sin(al + drop t)) % partial_derivative 1 w (wan_circ a r (al + drop t)) +
                cos(al + drop t) % partial_derivative 2 w (wan_circ a r (al + drop t)))))
         (at t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^2)`; `w:real^2->real^K`] WAN_C1_OPEN_FACTS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[OPEN_UNIV; smooth_map_on]; ALL_TAC] THEN
  REWRITE_TAC[IN_UNIV] THEN STRIP_TAC THEN
  ABBREV_TAC `p = wan_circ a r (al + drop t)` THEN
  ABBREV_TAC `c = r % vector[--sin(al + drop t); cos(al + drop t)]:real^2` THEN
  SUBGOAL_THEN
   `r % (--(sin(al + drop t)) % partial_derivative 1 (w:real^2->real^K) p +
         cos(al + drop t) % partial_derivative 2 w p) =
    frechet_derivative w (at p) c`
  SUBST1_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[partial_derivative; WAN_VECTOR2_BASIS] THEN
    SUBGOAL_THEN `linear(frechet_derivative (w:real^2->real^K) (at p))` ASSUME_TAC THENL
     [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_MESON_TAC[differentiable];
      ASM_SIMP_TAC[LINEAR_CMUL; LINEAR_ADD]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^2`; `r:real`; `al:real`; `t:real^1`] WAN_CIRC_VDERIV) THEN
  ASM_REWRITE_TAC[has_vector_derivative] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\s:real^1. wan_circ a r (al + drop s)`; `w:real^2->real^K`;
                 `\h:real^1. drop h % (c:real^2)`;
                 `frechet_derivative (w:real^2->real^K) (at p)`;
                 `t:real^1`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[o_DEF] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `h:real^1` THEN
  MATCH_MP_TAC LINEAR_CMUL THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
  ASM_MESON_TAC[differentiable]);;

let WAN_CIRC_FTC_SMOOTH = prove
 (`!(w:real^2->real^K) a r al t1 t2.
     smooth_map_on (:real^2) w /\ t1 <= t2
     ==> ((\s. r % (--(sin(al + drop s)) %
                    partial_derivative 1 w (wan_circ a r (al + drop s)) +
                    cos(al + drop s) %
                    partial_derivative 2 w (wan_circ a r (al + drop s))))
          has_integral (w(wan_circ a r (al + t2)) - w(wan_circ a r (al + t1))))
         (interval[lift t1,lift t2])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\s. (w:real^2->real^K)(wan_circ a r (al + drop s))`;
                 `\s. r % (--(sin(al + drop s)) %
                           partial_derivative 1 (w:real^2->real^K) (wan_circ a r (al + drop s)) +
                           cos(al + drop s) %
                           partial_derivative 2 w (wan_circ a r (al + drop s)))`;
                 `lift t1`; `lift t2`] FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
  ASM_SIMP_TAC[WAN_CIRC_COMPOSE_VDERIV]);;

(* ------------------------------------------------------------------------- *)
(* Smooth approximation on a compact set that also converges uniformly when *)
(* u is continuous (the construction of WAN_W12_LOCAL_APPROX, pc_wan_sob2). *)
(* ------------------------------------------------------------------------- *)

let WAN_W12_LOCAL_APPROX_UNIF = prove
 (`!(s:real^N->bool) (u:real^N->real^K) (g:num->real^N->real^K) k.
     open s /\ wan_l2loc s u /\ u continuous_on s /\
     (!i. 1 <= i /\ i <= dimindex(:N) ==> wan_l2loc s (g i) /\ wan_wpd s i u (g i)) /\
     compact k /\ k SUBSET s
     ==> ?w:num->real^N->real^K.
           (!n. wan_vtest s (w n)) /\
           (!i. 1 <= i /\ i <= dimindex(:N)
                ==> ((\n. drop(integral k
                                (\x. lift(norm(partial_derivative i (w n) x - g i x) pow 2))))
                     ---> &0) sequentially) /\
           (!e. &0 < e ==> ?M. !n x. M <= n /\ x IN k ==> norm(w n x - u x) <= e)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `k:real^N->bool`] WAN_COMPACT_NBHD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d1:real` MP_TAC) THEN
  ABBREV_TAC `k1 = {x + y:real^N | x IN k /\ y IN cball(vec 0,d1)}` THEN
  ABBREV_TAC `uu = {x + y:real^N | x IN k /\ y IN ball(vec 0,d1)}` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `k1:real^N->bool`] WAN_SMOOTH_URYSOHN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `psi:real^N->real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!i x. x IN uu ==> wan_dpart i (psi:real^N->real) x = &0` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[wan_dpart] THEN
    MP_TAC(ISPECL [`\y. lift((psi:real^N->real) y)`; `\y:real^N. lift(&1)`;
                   `uu:real^N->bool`; `x:real^N`] LRG_FRECHET_DERIVATIVE_EQ_OPEN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FRECHET_DERIVATIVE_CONST_AT; DROP_VEC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `u:real^N->real^K`; `g:num->real^N->real^K`;
                 `psi:real^N->real`] WAN_CUTOFF_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `kp:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?w0 (G:num->real^N->real^K).
      w0 IN lspace (:real^N) (&2) /\ w0 continuous_on (:real^N) /\
      (!x. ~(x IN kp) ==> w0 x = vec 0) /\
      (!x. x IN k ==> w0 x = (u:real^N->real^K) x) /\
      !i. 1 <= i /\ i <= dimindex(:N)
          ==> G i IN lspace (:real^N) (&2) /\ (!x. ~(x IN kp) ==> G i x = vec 0) /\
              wan_wpd (:real^N) i w0 (G i) /\
              (!x. x IN k ==> G i x = (g:num->real^N->real^K) i x)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\x. if x IN s then (psi:real^N->real) x % (u:real^N->real^K) x else vec 0)
      continuous_on (:real^N)`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `(:real^N) = s UNION ((:real^N) DIFF kp)` SUBST1_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_UNION_OPEN THEN ASM_REWRITE_TAC[GSYM closed] THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
        EXISTS_TAC `\x. (psi:real^N->real) x % (u:real^N->real^K) x` THEN
        SIMP_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN ASM_REWRITE_TAC[o_DEF] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
        REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
        ASM_MESON_TAC[wan_test];
        MATCH_MP_TAC CONTINUOUS_ON_EQ THEN EXISTS_TAC `\x:real^N. vec 0:real^K` THEN
        REWRITE_TAC[CONTINUOUS_ON_CONST; IN_DIFF; IN_UNIV] THEN ASM_MESON_TAC[]];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC
     [`\x. if x IN s then (psi:real^N->real) x % (u:real^N->real^K) x else vec 0`;
      `\i x. if x IN s then wan_dpart i (psi:real^N->real) x % (u:real^N->real^K) x +
                            psi x % (g:num->real^N->real^K) i x else vec 0`] THEN
    ASM_SIMP_TAC[ETA_AX] THEN
    SUBGOAL_THEN `!x. x IN k ==> (x:real^N) IN s /\ x IN uu /\ psi x = &1` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[VECTOR_MUL_LID; VECTOR_MUL_LZERO; VECTOR_ADD_LID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `kp:real^N->bool`] WAN_COMPACT_NBHD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\n. wan_moll (d2 / (&n + &2)) (w0:real^N->real^K)` THEN
  SUBGOAL_THEN `!n. &0 < d2 / (&n + &2) /\ d2 / (&n + &2) < d2` ASSUME_TAC THENL
   [GEN_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 < &n + &2`] THEN
      SUBGOAL_THEN `&0 <= d2 * &n` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POS]; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_lloc (:real^N) (w0:real^N->real^K)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_L2_LLOC]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN REWRITE_TAC[wan_vtest] THEN CONJ_TAC THENL
     [MATCH_MP_TAC WAN_MOLL_SMOOTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `{x + y:real^N | x IN kp /\ y IN cball(vec 0,d2)}` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`d2 / (&n + &2)`; `w0:real^N->real^K`; `kp:real^N->bool`]
                  WAN_MOLL_SUPPORT) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `~((x:real^N) IN {x + y | x IN kp /\ y IN cball(vec 0,d2)})` THEN
    REWRITE_TAC[IN_ELIM_THM; CONTRAPOS_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`p:real^N`; `q:real^N`] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(q:real^N) IN ball(vec 0,d2 / (&n + &2))` THEN
    REWRITE_TAC[IN_BALL_0; IN_CBALL_0] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (is_forall o concl)) THEN REAL_ARITH_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `!n x. partial_derivative i (wan_moll (d2 / (&n + &2)) (w0:real^N->real^K)) x =
            wan_moll (d2 / (&n + &2)) ((G:num->real^N->real^K) i) x`
    (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN MATCH_MP_TAC WAN_MOLL_WPD THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC WAN_MOLL_SEQ_L2_ON THEN EXISTS_TAC `kp:real^N->bool` THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`w0:real^N->real^K`; `k:real^N->bool`] WAN_MOLL_UNIFORM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPEC `d / d2` REAL_ARCH_INV) THEN ASM_SIMP_TAC[REAL_LT_DIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `M:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `M:num` THEN MAP_EVERY X_GEN_TAC [`n:num`; `x:real^N`] THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `(u:real^N->real^K) x = w0 x` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `d:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `d2 / (&n + &2) <= d2 * inv(&M)` MP_TAC THENL
     [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      UNDISCH_TAC `(M:num) <= n` THEN UNDISCH_TAC `~((M:num) = 0)` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_EQ] THEN
      MP_TAC(SPEC `M:num` REAL_POS) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `d2 * inv(&M) < d` MP_TAC THENL
     [UNDISCH_TAC `inv(&M) < d / d2` THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `d2 / (&n + &2)`)) (concl th))) THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Nonnegative functions with summable integrals tend to 0 almost           *)
(* everywhere (Beppo Levi on the partial sums).                             *)
(* ------------------------------------------------------------------------- *)

let WAN_GEOM_HALF_SUM = prove
 (`!k. sum(0..k) (\n. inv(&2) pow n) <= &2`,
  GEN_TAC THEN REWRITE_TAC[SUM_GP; LT] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[real_pow] THEN
  MP_TAC(SPECL [`inv(&2)`; `k:num`] REAL_POW_LE) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

let WAN_SUMMABLE_AE_NULL = prove
 (`!(f:num->real^M->real^1) s.
     (!n. (f n) integrable_on s) /\ (!n x. x IN s ==> &0 <= drop(f n x)) /\
     (!n. drop(integral s (f n)) <= inv(&2) pow n)
     ==> ?N. negligible N /\
             !x. x IN s DIFF N ==> ((\n. drop(f n x)) ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\k x. vsum(0..k) (\n. (f:num->real^M->real^1) n x)`; `s:real^M->bool`]
                BEPPO_LEVI_INCREASING) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_VSUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG];
      REPEAT STRIP_TAC THEN REWRITE_TAC[VSUM_CLAUSES_NUMSEG; LE_0; DROP_ADD] THEN
      ASM_SIMP_TAC[REAL_LE_ADDR];
      REWRITE_TAC[BOUNDED_POS] THEN EXISTS_TAC `&2` THEN
      REWRITE_TAC[REAL_ARITH `&0 < &2`; FORALL_IN_GSPEC; IN_UNIV] THEN
      X_GEN_TAC `k:num` THEN
      ASM_SIMP_TAC[INTEGRAL_VSUM; FINITE_NUMSEG; NORM_1; DROP_VSUM; o_DEF] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
        MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_SIMP_TAC[];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(0..k) (\n. inv(&2) pow n)` THEN
        REWRITE_TAC[WAN_GEOM_HALF_SUM] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
        ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^M->real^1` (X_CHOOSE_THEN `N:real^M->bool`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `N:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  REWRITE_TAC[TENDSTO_REAL; o_DEF; LIFT_DROP; LIFT_NUM] THEN
  MATCH_MP_TAC SEQ_OFFSET_REV THEN EXISTS_TAC `1` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `1` o MATCH_MP SEQ_OFFSET) THEN
  DISCH_THEN(MP_TAC o C CONJ (ASSUME
   `((\k. vsum(0..k) (\n. (f:num->real^M->real^1) n x)) --> g x) sequentially`)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP LIM_SUB) THEN
  REWRITE_TAC[VECTOR_SUB_REFL; GSYM ADD1; VSUM_CLAUSES_NUMSEG; LE_0] THEN
  REWRITE_TAC[VECTOR_ARITH `(a + b) - a:real^N = b`]);;

(* ------------------------------------------------------------------------- *)
(* Passing to the limit in fundamental-theorem identities along a curve.    *)
(* ------------------------------------------------------------------------- *)

let WAN_TRIG_COMB_SQ = prove
 (`!(A:real^K) B s. norm(--(sin s) % A + cos s % B) pow 2 <= norm A pow 2 + norm B pow 2`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(abs(sin s) * norm(A:real^K) + abs(cos s) * norm(B:real^K)) pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC(NORM_ARITH
     `norm(x:real^K) = p /\ norm(y:real^K) = q ==> norm(x + y) <= p + q`) THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_NEG];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(sin s) pow 2 + abs(cos s) pow 2 = &1` MP_TAC THENL
   [REWRITE_TAC[REAL_POW2_ABS; SIN_CIRCLE]; ALL_TAC] THEN
  MP_TAC(SPEC `abs(sin s) * norm(B:real^K) - abs(cos s) * norm(A:real^K)` REAL_LE_POW_2) THEN
  SPEC_TAC(`abs(sin s)`,`p:real`) THEN SPEC_TAC(`abs(cos s)`,`q:real`) THEN
  SPEC_TAC(`norm(A:real^K)`,`a:real`) THEN SPEC_TAC(`norm(B:real^K)`,`b:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  MP_TAC(REAL_RING `(p * a + q * b) pow 2 + (p * b - q * a) pow 2 =
                    (p pow 2 + q pow 2) * (a pow 2 + b pow 2)`) THEN
  ASM_REWRITE_TAC[REAL_MUL_LID] THEN ASM_REAL_ARITH_TAC);;

let WAN_AMGM_NORM_BOUND = prove
 (`!(d:real^K) h lam.
     &0 < lam /\ norm d pow 2 <= h ==> norm d <= lam / &2 + inv(&2 * lam) * h`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&2 * lam * norm(d:real^K) <= lam pow 2 + h` MP_TAC THENL
   [MP_TAC(SPEC `lam - norm(d:real^K)` REAL_LE_POW_2) THEN
    MP_TAC(REAL_RING `(lam - norm(d:real^K)) pow 2 =
                      lam pow 2 - &2 * lam * norm d + norm d pow 2`) THEN
    UNDISCH_TAC `norm(d:real^K) pow 2 <= h` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_FIELD `&0 < lam ==> lam / &2 + inv(&2 * lam) * h =
                                        (lam pow 2 + h) / (&2 * lam)`] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&0 < lam ==> &0 < &2 * lam`] THEN
  REAL_ARITH_TAC);;

let WAN_HAS_INTEGRAL_L2_LIMIT = prove
 (`!(v:num->real^1->real^K) w (h:num->real^1->real) (yy:num->real^K) y a b.
     drop a <= drop b /\
     w integrable_on interval[a,b] /\
     (!n. (v n has_integral yy n) (interval[a,b])) /\
     (yy --> y) sequentially /\
     (!n. (\s. lift(h n s)) integrable_on interval[a,b]) /\
     (!n s. s IN interval[a,b] ==> norm(v n s - w s) pow 2 <= h n s) /\
     ((\n. drop(integral (interval[a,b]) (\s. lift(h n s)))) ---> &0) sequentially
     ==> (w has_integral y) (interval[a,b])`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!n. ((v:num->real^1->real^K) n) integrable_on interval[a,b]` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[integrable_on] THEN EXISTS_TAC `(yy:num->real^K) n` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\n. integral (interval[a,b]) ((v:num->real^1->real^K) n)) -->
     integral (interval[a,b]) w) sequentially`
  ASSUME_TAC THENL
   [REWRITE_TAC[LIM_SEQUENTIALLY; dist] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < e / (drop b - drop a + &1) /\
                  e / (drop b - drop a + &1) * (drop b - drop a) < e`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 < drop b - drop a + &1` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_DIV] THEN
      ASM_SIMP_TAC[REAL_FIELD `&0 < c ==> e / c * x = (e * x) / c`; REAL_LT_LDIV_EQ] THEN
      MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `lam = e / (drop b - drop a + &1)` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e * lam` o GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY]) THEN
    ASM_SIMP_TAC[REAL_LT_MUL; REAL_SUB_RZERO] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `integral (interval[a,b]) ((v:num->real^1->real^K) n) - integral (interval[a,b]) w =
      integral (interval[a,b]) (\s. v n s - w s)`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_SUB THEN
      ASM_SIMP_TAC[ETA_AX];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\s. lift(lam / &2 + inv(&2 * lam) * (h:num->real^1->real) n s)) integrable_on
      interval[a,b] /\
      drop(integral (interval[a,b]) (\s. lift(lam / &2 + inv(&2 * lam) * h n s))) =
      (drop b - drop a) * lam / &2 +
      inv(&2 * lam) * drop(integral (interval[a,b]) (\s. lift(h n s)))`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN
      SUBGOAL_THEN
       `(\s:real^1. lift(lam / &2)) integrable_on interval[a,b] /\
        (\s. inv(&2 * lam) % lift((h:num->real^1->real) n s)) integrable_on interval[a,b]`
      STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[INTEGRABLE_CONST] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[INTEGRABLE_ADD; INTEGRAL_ADD; INTEGRAL_CONST; INTEGRAL_CMUL; CONTENT_1;
                   DROP_ADD; DROP_CMUL; LIFT_DROP] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `drop(integral (interval[a,b])
                   (\s. lift(lam / &2 + inv(&2 * lam) * (h:num->real^1->real) n s)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_SIMP_TAC[ETA_AX];
        X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
        MATCH_MP_TAC WAN_AMGM_NORM_BOUND THEN ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `inv(&2 * lam) * drop(integral (interval[a,b]) (\s. lift((h:num->real^1->real) n s)))
      < e / &2`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv(&2 * lam) * (e * lam)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_LMUL THEN
        ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < lam ==> &0 < &2 * lam`] THEN
        ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_FIELD `&0 < lam ==> inv(&2 * lam) * (e * lam) = e / &2`;
                     REAL_LE_REFL]];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `integral (interval[a,b]) (w:real^1->real^K) = y` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
    EXISTS_TAC `\n. integral (interval[a,b]) ((v:num->real^1->real^K) n)` THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    SUBGOAL_THEN `(\n. integral (interval[a,b]) ((v:num->real^1->real^K) n)) = yy`
    (fun th -> ASM_REWRITE_TAC[th]) THEN
    REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL]);;

(* ------------------------------------------------------------------------- *)
(* Sections of integrable maps along circles, and products with sin, cos.   *)
(* ------------------------------------------------------------------------- *)

let WAN_POLAR_SECTION_FACTS = prove
 (`!(f:real^2->real^M) x0 al.
     f absolutely_integrable_on (:real^2)
     ==> ?E. negligible E /\
             (!r. &0 < r /\ ~(lift r IN E)
                  ==> (\t. f(wan_circ x0 r (al + drop t))) absolutely_integrable_on
                      interval[vec 0,lift(&2 * pi)]) /\
             (\r. if r IN E then vec 0
                  else drop r % integral (interval[vec 0,lift(&2 * pi)])
                                  (\t. f(wan_circ x0 (drop r) (al + drop t))))
             absolutely_integrable_on {r | &0 <= drop r} /\
             integral {r | &0 <= drop r}
               (\r. if r IN E then vec 0
                    else drop r % integral (interval[vec 0,lift(&2 * pi)])
                                    (\t. f(wan_circ x0 (drop r) (al + drop t)))) =
             integral (:real^2) f`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:real^2->real^M`; `x0:real^2`; `al:real`] WAN_FUBINI_POLAR_CIRC) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `E = {r | &0 <= drop r /\
             ~((\t. drop r % (f:real^2->real^M)(wan_circ x0 (drop r) (al + drop t)))
               absolutely_integrable_on interval[vec 0,lift(&2 * pi)])}` THEN
  STRIP_TAC THEN EXISTS_TAC `E:real^1->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!r. &0 <= drop r /\ ~(r IN E)
        ==> (\t. drop r % (f:real^2->real^M)(wan_circ x0 (drop r) (al + drop t)))
            absolutely_integrable_on interval[vec 0,lift(&2 * pi)]`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real^1` THEN STRIP_TAC THEN
    UNDISCH_TAC `~((r:real^1) IN E)` THEN EXPAND_TAC "E" THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. &0 < drop r /\ ~(r IN E)
        ==> (\t. (f:real^2->real^M)(wan_circ x0 (drop r) (al + drop t)))
            absolutely_integrable_on interval[vec 0,lift(&2 * pi)]`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real^1` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:real^1`) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    DISCH_THEN(MP_TAC o SPEC `inv(drop r)` o MATCH_MP ABSOLUTELY_INTEGRABLE_CMUL) THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. r IN {r | &0 <= drop r} DIFF E
        ==> (if r IN E then vec 0
             else drop r % integral (interval[vec 0,lift(&2 * pi)])
                             (\t. (f:real^2->real^M)(wan_circ x0 (drop r) (al + drop t)))) =
            integral (interval[vec 0,lift(&2 * pi)])
              (\t. drop r % f(wan_circ x0 (drop r) (al + drop t)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real^1` THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `drop r = &0` THENL
     [ASM_REWRITE_TAC[VECTOR_MUL_LZERO; INTEGRAL_0]; ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_CMUL THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `lift r` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `&0 < drop r`)) (concl th))) THEN
    ASM_REWRITE_TAC[LIFT_DROP];
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] ABSOLUTELY_INTEGRABLE_SPIKE) THEN
    EXISTS_TAC `\r. integral (interval[vec 0,lift(&2 * pi)])
                      (\t. drop r % (f:real^2->real^M)(wan_circ x0 (drop r) (al + drop t)))` THEN
    EXISTS_TAC `E:real^1->bool` THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `integral {r | &0 <= drop r}
                  (\r. integral (interval[vec 0,lift(&2 * pi)])
                         (\t. drop r % (f:real^2->real^M)(wan_circ x0 (drop r) (al + drop t))))` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC INTEGRAL_SPIKE THEN
    EXISTS_TAC `E:real^1->bool` THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[]]);;

let WAN_CONT_SIN_COS = prove
 (`!c. (\s:real^1. lift(sin(c + drop s))) continuous_on (:real^1) /\
       (\s:real^1. lift(cos(c + drop s))) continuous_on (:real^1)`,
  GEN_TAC THEN
  SUBGOAL_THEN `(\x. c + x) real_continuous_on (:real)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_ADD THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_CONST; REAL_CONTINUOUS_ON_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. sin(c + x)) real_continuous_on (:real) /\
                (\x. cos(c + x)) real_continuous_on (:real)` MP_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`\x:real. c + x`; `sin`; `(:real)`] REAL_CONTINUOUS_ON_COMPOSE);
      MP_TAC(ISPECL [`\x:real. c + x`; `cos`; `(:real)`] REAL_CONTINUOUS_ON_COMPOSE)] THEN
    ASM_REWRITE_TAC[o_DEF; REAL_CONTINUOUS_ON_SIN; REAL_CONTINUOUS_ON_COS];
    REWRITE_TAC[REAL_CONTINUOUS_ON; IMAGE_LIFT_UNIV; o_DEF]]);;

let WAN_TRIG_PRODUCT_ABS_INT = prove
 (`!(g:real^1->real^K) a b c.
     g absolutely_integrable_on interval[a,b]
     ==> (\s. --(sin(c + drop s)) % g s) absolutely_integrable_on interval[a,b] /\
         (\s. cos(c + drop s) % g s) absolutely_integrable_on interval[a,b]`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`\x:real^1 y:real^K. drop x % y`; `\s. lift(--(sin(c + drop s)))`;
                   `g:real^1->real^K`; `interval[a:real^1,b]`]
                  ABSOLUTELY_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT);
    MP_TAC(ISPECL [`\x:real^1 y:real^K. drop x % y`; `\s. lift(cos(c + drop s))`;
                   `g:real^1->real^K`; `interval[a:real^1,b]`]
                  ABSOLUTELY_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT)] THEN
  REWRITE_TAC[BILINEAR_DROP_MUL; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  (CONJ_TAC THENL
    [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_CLOSED_SUBSET THEN
     REWRITE_TAC[CLOSED_INTERVAL] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
     EXISTS_TAC `(:real^1)` THEN REWRITE_TAC[SUBSET_UNIV] THEN
     REWRITE_TAC[LIFT_NEG] THEN TRY(MATCH_MP_TAC CONTINUOUS_ON_NEG) THEN
     REWRITE_TAC[WAN_CONT_SIN_COS];
     REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN EXISTS_TAC `&1` THEN
     REWRITE_TAC[NORM_LIFT; REAL_ABS_NEG; SIN_BOUND; COS_BOUND; REAL_LT_01]]));;

(* ------------------------------------------------------------------------- *)
(* Sections along arcs inside a measurable set: integrability, and the      *)
(* almost-everywhere decay of sections of a summable sequence.               *)
(* ------------------------------------------------------------------------- *)

let WAN_ARC_SECTION_K = prove
 (`!(g:real^2->real^M) k x0 al.
     g absolutely_integrable_on k
     ==> ?E. negligible E /\
             !r t1 t2.
               &0 < r /\ ~(lift r IN E) /\ &0 <= t1 /\ t1 <= t2 /\ t2 <= &2 * pi /\
               (!t. t1 <= t /\ t <= t2 ==> wan_circ x0 r (al + t) IN k)
               ==> (\s. g(wan_circ x0 r (al + drop s))) absolutely_integrable_on
                   interval[lift t1,lift t2]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. if x IN k then (g:real^2->real^M) x else vec 0`; `x0:real^2`;
                 `al:real`] WAN_POLAR_SECTION_FACTS) THEN
  ASM_REWRITE_TAC[ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `E:real^1->bool` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `&0 < r`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_EQ THEN
  EXISTS_TAC `\s. if wan_circ x0 r (al + drop s) IN k
                  then (g:real^2->real^M)(wan_circ x0 r (al + drop s)) else vec 0` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
    STRIP_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `wan_circ x0 r (al + drop s) IN (k:real^2->bool)`
    (fun th -> REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_SUBINTERVAL THEN
    EXISTS_TAC `interval[vec 0:real^1,lift(&2 * pi)]` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN ASM_REAL_ARITH_TAC]);;

let WAN_ARC_NULL_SEQ = prove
 (`!(h:num->real^2->real) k x0 al.
     (!n x. &0 <= h n x) /\
     (!n. (\x. lift(h n x)) integrable_on k) /\
     (!n. drop(integral k (\x. lift(h n x))) <= inv(&2) pow n)
     ==> ?E. negligible E /\
             !r t1 t2.
               &0 < r /\ ~(lift r IN E) /\ &0 <= t1 /\ t1 <= t2 /\ t2 <= &2 * pi /\
               (!t. t1 <= t /\ t <= t2 ==> wan_circ x0 r (al + t) IN k)
               ==> (!n. (\s. lift(h n (wan_circ x0 r (al + drop s)))) integrable_on
                        interval[lift t1,lift t2]) /\
                   ((\n. drop(integral (interval[lift t1,lift t2])
                                (\s. lift(h n (wan_circ x0 r (al + drop s)))))) ---> &0)
                   sequentially`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `hh = \n x. if x IN k then lift((h:num->real^2->real) n x) else vec 0` THEN
  SUBGOAL_THEN
   `!n. ((hh:num->real^2->real^1) n) absolutely_integrable_on (:real^2) /\
        integral (:real^2) (hh n) = integral (k:real^2->bool) (\x. lift((h:num->real^2->real) n x)) /\
        (!x. &0 <= drop(hh n x))`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "hh" THEN
    REWRITE_TAC[ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV; INTEGRAL_RESTRICT_UNIV] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_INTEGRABLE_BOUND THEN
      EXISTS_TAC `\x. lift((h:num->real^2->real) n x)` THEN
      ASM_REWRITE_TAC[NORM_LIFT; LIFT_DROP] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x <= x`];
      GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[LIFT_DROP; DROP_VEC; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?E:num->real^1->bool.
      !n. negligible(E n) /\
          (!r. &0 < r /\ ~(lift r IN E n)
               ==> (\t. (hh:num->real^2->real^1) n (wan_circ x0 r (al + drop t)))
                   absolutely_integrable_on interval[vec 0,lift(&2 * pi)]) /\
          (\r. if r IN E n then vec 0
               else drop r % integral (interval[vec 0,lift(&2 * pi)])
                               (\t. hh n (wan_circ x0 (drop r) (al + drop t))))
          absolutely_integrable_on {r | &0 <= drop r} /\
          integral {r | &0 <= drop r}
            (\r. if r IN E n then vec 0
                 else drop r % integral (interval[vec 0,lift(&2 * pi)])
                                 (\t. hh n (wan_circ x0 (drop r) (al + drop t)))) =
          integral (:real^2) (hh n)`
  MP_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN GEN_TAC THEN
    MATCH_MP_TAC WAN_POLAR_SECTION_FACTS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `E:num->real^1->bool` (LABEL_TAC "E")) THEN
  ABBREV_TAC
   `Psi = \n r. if r IN (E:num->real^1->bool) n then vec 0
                else drop r % integral (interval[vec 0,lift(&2 * pi)])
                                (\t. (hh:num->real^2->real^1) n
                                       (wan_circ x0 (drop r) (al + drop t)))` THEN
  MP_TAC(ISPECL [`Psi:num->real^1->real^1`; `{r:real^1 | &0 <= drop r}`]
                WAN_SUMMABLE_AE_NULL) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [GEN_TAC THEN EXPAND_TAC "Psi" THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      USE_THEN "E" (fun th -> REWRITE_TAC[th]);
      MAP_EVERY X_GEN_TAC [`n:num`; `r:real^1`] THEN REWRITE_TAC[IN_ELIM_THM] THEN
      DISCH_TAC THEN EXPAND_TAC "Psi" THEN COND_CASES_TAC THEN
      REWRITE_TAC[DROP_VEC; REAL_LE_REFL; DROP_CMUL] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `drop r = &0` THENL
       [ASM_REWRITE_TAC[wan_circ; VECTOR_MUL_LZERO; VECTOR_ADD_RID; INTEGRABLE_CONST];
        ALL_TAC] THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      USE_THEN "E" (MP_TAC o SPEC `drop r` o CONJUNCT1 o CONJUNCT2 o SPEC `n:num`) THEN
      REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      GEN_TAC THEN EXPAND_TAC "Psi" THEN USE_THEN "E" (fun th -> REWRITE_TAC[th]) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N0:real^1->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `N0 UNION UNIONS {(E:num->real^1->bool) n | n IN (:num)}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_UNION THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC NEGLIGIBLE_COUNTABLE_UNIONS THEN USE_THEN "E" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`r:real`; `t1:real`; `t2:real`] THEN
  REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV; DE_MORGAN_THM; NOT_EXISTS_THM] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!n s. s IN interval[lift t1,lift t2]
          ==> (hh:num->real^2->real^1) n (wan_circ x0 r (al + drop s)) =
              lift((h:num->real^2->real) n (wan_circ x0 r (al + drop s)))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN STRIP_TAC THEN
    EXPAND_TAC "hh" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `wan_circ x0 r (al + drop s) IN (k:real^2->bool)`
    (fun th -> REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `interval[lift t1,lift t2] SUBSET interval[vec 0,lift(&2 * pi)]`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (\t. (hh:num->real^2->real^1) n (wan_circ x0 r (al + drop t)))
        absolutely_integrable_on interval[vec 0,lift(&2 * pi)]`
  ASSUME_TAC THENL
   [GEN_TAC THEN USE_THEN "E" (MP_TAC o SPEC `r:real` o CONJUNCT1 o CONJUNCT2 o SPEC `n:num`) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (\s. lift((h:num->real^2->real) n (wan_circ x0 r (al + drop s)))) integrable_on
        interval[lift t1,lift t2]`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_EQ THEN
    EXISTS_TAC `\t. (hh:num->real^2->real^1) n (wan_circ x0 r (al + drop t))` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
    EXISTS_TAC `interval[vec 0:real^1,lift(&2 * pi)]` THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. inv r * drop((Psi:num->real^1->real^1) n (lift r))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
    EXPAND_TAC "Psi" THEN ASM_REWRITE_TAC[LIFT_DROP; DROP_CMUL] THEN
    ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_LID] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `drop(integral (interval[lift t1,lift t2])
                  (\t. (hh:num->real^2->real^1) n (wan_circ x0 r (al + drop t))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC INTEGRAL_EQ THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
    MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
    EXISTS_TAC `interval[vec 0:real^1,lift(&2 * pi)]` THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
    SUBST1_TAC(REAL_ARITH `&0 = inv r * &0`) THEN MATCH_MP_TAC REALLIM_LMUL THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM; LIFT_DROP] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

(* ------------------------------------------------------------------------- *)
(* Absolute continuity along almost every arc inside a compact subset.      *)
(* ------------------------------------------------------------------------- *)

let WAN_SMOOTH_PARTIAL_CONT = prove
 (`!(w:real^N->real^K) i.
     smooth_map_on (:real^N) w ==> (\x. partial_derivative i w x) continuous_on (:real^N)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^N)`; `w:real^N->real^K`] WAN_C1_OPEN_FACTS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[OPEN_UNIV; smooth_map_on]; ALL_TAC] THEN
  SIMP_TAC[partial_derivative]);;

let WAN_LSPACE2_ABS_INT_MEAS = prove
 (`!(S:real^N->bool) (f:real^N->real^K).
     measurable S /\ f IN lspace S (&2) ==> f absolutely_integrable_on S`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^N->real^K`; `S:real^N->bool`; `&2`] HOELDER_BOUND) THEN
  ASM_SIMP_TAC[REAL_ARITH `&1 <= &2`]);;

let WAN_HARMONIC_BOUND_LIM = prove
 (`!(f:num->real^K) l. (!n. norm(f n - l) <= inv(&n + &1)) ==> (f --> l) sequentially`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[LIM_NULL] THEN
  MATCH_MP_TAC LIM_NULL_COMPARISON THEN EXISTS_TAC `\n. inv(&n + &1)` THEN
  ASM_REWRITE_TAC[SEQ_HARMONIC_OFFSET] THEN MATCH_MP_TAC ALWAYS_EVENTUALLY THEN
  ASM_REWRITE_TAC[]);;

let WAN_ARC_APPROX_SEQ = prove
 (`!(D:real^2->bool) (u:real^2->real^K) k.
     open D /\ u continuous_on D /\ wan_w12 D u /\ compact k /\ k SUBSET D
     ==> ?W. (!n. smooth_map_on (:real^2) (W n)) /\
             (!n x. x IN k ==> norm(W n x - u x) <= inv(&n + &1)) /\
             (!n. (\x. lift(norm(partial_derivative 1 (W n) x - wan_wd D 1 u x) pow 2 +
                            norm(partial_derivative 2 (W n) x - wan_wd D 2 u x) pow 2))
                  integrable_on k) /\
             (!n. drop(integral k
                        (\x. lift(norm(partial_derivative 1 (W n) x - wan_wd D 1 u x) pow 2 +
                                  norm(partial_derivative 2 (W n) x - wan_wd D 2 u x) pow 2)))
                  <= inv(&2) pow n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> wan_wd D i (u:real^2->real^K) IN lspace D (&2) /\ wan_wpd D i u (wan_wd D i u)`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC WAN_WD_WORKS THEN ASM_REWRITE_TAC[DIMINDEX_2];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`D:real^2->bool`; `u:real^2->real^K`; `\i. wan_wd D i (u:real^2->real^K)`;
                 `k:real^2->bool`] WAN_W12_LOCAL_APPROX_UNIF) THEN
  REWRITE_TAC[DIMINDEX_2] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[WAN_LSPACE2_IMP_L2LOC; WAN_W12_IMP_LSPACE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:num->real^2->real^K` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!n. smooth_map_on (:real^2) ((w:num->real^2->real^K) n)` ASSUME_TAC THENL
   [ASM_MESON_TAC[wan_vtest]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n i. 1 <= i /\ i <= 2
          ==> (\x. partial_derivative i ((w:num->real^2->real^K) n) x - wan_wd D i u x)
              IN lspace k (&2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LSPACE_SUB THEN REWRITE_TAC[REAL_POS] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC WAN_CONT_COMPACT_LSPACE2 THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_SIMP_TAC[SUBSET_UNIV; WAN_SMOOTH_PARTIAL_CONT];
      REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC LSPACE_SUBSET THEN
      EXISTS_TAC `D:real^2->bool` THEN ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n i. 1 <= i /\ i <= 2
          ==> (\x. lift(norm(partial_derivative i ((w:num->real^2->real^K) n) x -
                             wan_wd D i u x) pow 2)) integrable_on k`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `i:num`]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP WAN_LSPACE2_SQNORM_INTEGRABLE) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `H = \n x. norm(partial_derivative 1 ((w:num->real^2->real^K) n) x - wan_wd D 1 u x) pow 2 +
              norm(partial_derivative 2 (w n) x - wan_wd D 2 u x) pow 2` THEN
  SUBGOAL_THEN
   `!n. (\x. lift((H:num->real^2->real) n x)) integrable_on k /\
        drop(integral k (\x. lift(H n x))) =
        drop(integral k (\x. lift(norm(partial_derivative 1 ((w:num->real^2->real^K) n) x -
                                       wan_wd D 1 u x) pow 2))) +
        drop(integral k (\x. lift(norm(partial_derivative 2 (w n) x -
                                       wan_wd D 2 u x) pow 2)))`
  (LABEL_TAC "Hint") THENL
   [GEN_TAC THEN EXPAND_TAC "H" THEN REWRITE_TAC[LIFT_ADD] THEN
    SUBGOAL_THEN
     `(\x. lift(norm(partial_derivative 1 ((w:num->real^2->real^K) n) x -
                     wan_wd D 1 u x) pow 2)) integrable_on k /\
      (\x. lift(norm(partial_derivative 2 ((w:num->real^2->real^K) n) x -
                     wan_wd D 2 u x) pow 2)) integrable_on k`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[INTEGRABLE_ADD; INTEGRAL_ADD; DROP_ADD];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\n. drop(integral k (\x. lift((H:num->real^2->real) n x)))) ---> &0)
                sequentially`
  ASSUME_TAC THENL
   [USE_THEN "Hint" (fun th -> REWRITE_TAC[th]) THEN SUBST1_TAC(REAL_ARITH `&0 = &0 + &0`) THEN
    MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?mm:num->num.
      !n. drop(integral k (\x. lift((H:num->real^2->real) (mm n) x))) <= inv(&2) pow n /\
          !x. x IN k ==> norm((w:num->real^2->real^K) (mm n) x - u x) <= inv(&n + &1)`
  (X_CHOOSE_THEN `mm:num->num` (LABEL_TAC "mm")) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `inv(&2) pow n` o GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY]) THEN
    SIMP_TAC[REAL_POW_LT; REAL_LT_INV_EQ; REAL_ARITH `&0 < &2`; REAL_SUB_RZERO] THEN
    DISCH_THEN(X_CHOOSE_TAC `M1:num`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `inv(&n + &1)` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `u:real^2->real^K`)) (concl th) &&
      can (find_term (fun t -> is_var t && fst(dest_var t) = "e")) (concl th))) THEN
    REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
    DISCH_THEN(X_CHOOSE_TAC `M2:num`) THEN EXISTS_TAC `M1 + M2:num` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `abs x < e ==> x <= e`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `\n. (w:num->real^2->real^K) ((mm:num->num) n)` THEN REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN USE_THEN "mm" (MP_TAC o SPEC `n:num`) THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN USE_THEN "Hint" (MP_TAC o CONJUNCT1 o SPEC `(mm:num->num) n`) THEN
    EXPAND_TAC "H" THEN REWRITE_TAC[];
    GEN_TAC THEN USE_THEN "mm" (MP_TAC o CONJUNCT1 o SPEC `n:num`) THEN
    EXPAND_TAC "H" THEN REWRITE_TAC[]]);;

let WAN_ARC_ACL_K = prove
 (`!(D:real^2->bool) (u:real^2->real^K) k x0 al.
     open D /\ u continuous_on D /\ wan_w12 D u /\ compact k /\ k SUBSET D
     ==> ?S. negligible S /\
             !r t1 t2.
               &0 < r /\ ~(lift r IN S) /\ &0 <= t1 /\ t1 <= t2 /\ t2 <= &2 * pi /\
               (!t. t1 <= t /\ t <= t2 ==> wan_circ x0 r (al + t) IN k)
               ==> ((\s. r % (--(sin(al + drop s)) %
                              wan_wd D 1 u (wan_circ x0 r (al + drop s)) +
                              cos(al + drop s) %
                              wan_wd D 2 u (wan_circ x0 r (al + drop s))))
                    has_integral (u(wan_circ x0 r (al + t2)) - u(wan_circ x0 r (al + t1))))
                   (interval[lift t1,lift t2]) /\
                   (\s. lift(norm(wan_wd D 1 u (wan_circ x0 r (al + drop s))) pow 2 +
                             norm(wan_wd D 2 u (wan_circ x0 r (al + drop s))) pow 2))
                   integrable_on interval[lift t1,lift t2]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`D:real^2->bool`; `u:real^2->real^K`; `k:real^2->bool`]
                WAN_ARC_APPROX_SEQ) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:num->real^2->real^K` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2 ==> wan_wd D i (u:real^2->real^K) absolutely_integrable_on k`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_LSPACE2_ABS_INT_MEAS THEN
    ASM_SIMP_TAC[MEASURABLE_COMPACT] THEN MATCH_MP_TAC LSPACE_SUBSET THEN
    EXISTS_TAC `D:real^2->bool` THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT; WAN_WD_WORKS; DIMINDEX_2];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`wan_wd D 1 (u:real^2->real^K)`; `k:real^2->bool`; `x0:real^2`; `al:real`]
                WAN_ARC_SECTION_K) THEN
  ANTS_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `E1:real^1->bool` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "E1"))) THEN
  MP_TAC(ISPECL [`wan_wd D 2 (u:real^2->real^K)`; `k:real^2->bool`; `x0:real^2`; `al:real`]
                WAN_ARC_SECTION_K) THEN
  ANTS_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `E2:real^1->bool` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "E2"))) THEN
  MP_TAC(ISPECL [`\x. lift(norm(wan_wd D 1 (u:real^2->real^K) x) pow 2 +
                           norm(wan_wd D 2 u x) pow 2)`;
                 `k:real^2->bool`; `x0:real^2`; `al:real`] WAN_ARC_SECTION_K) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC WAN_DIR_DENSITY_ABS_INT THEN ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `E3:real^1->bool` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "E3"))) THEN
  MP_TAC(ISPECL
   [`\n x. norm(partial_derivative 1 ((W:num->real^2->real^K) n) x - wan_wd D 1 u x) pow 2 +
           norm(partial_derivative 2 (W n) x - wan_wd D 2 u x) pow 2`;
    `k:real^2->bool`; `x0:real^2`; `al:real`] WAN_ARC_NULL_SEQ) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_ADD THEN
    REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `E0:real^1->bool` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "E0"))) THEN
  EXISTS_TAC `E0 UNION E1 UNION E2 UNION (E3:real^1->bool)` THEN
  ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ; IN_UNION; DE_MORGAN_THM] THEN
  MAP_EVERY X_GEN_TAC [`r:real`; `t1:real`; `t2:real`] THEN STRIP_TAC THEN
  USE_THEN "E1" (MP_TAC o SPECL [`r:real`; `t1:real`; `t2:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "E2" (MP_TAC o SPECL [`r:real`; `t1:real`; `t2:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "E3" (MP_TAC o SPECL [`r:real`; `t1:real`; `t2:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "E0" (MP_TAC o SPECL [`r:real`; `t1:real`; `t2:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE]] THEN
  MATCH_MP_TAC WAN_HAS_INTEGRAL_L2_LIMIT THEN
  MAP_EVERY EXISTS_TAC
   [`\n s. r % (--(sin(al + drop s)) %
                partial_derivative 1 ((W:num->real^2->real^K) n) (wan_circ x0 r (al + drop s)) +
                cos(al + drop s) %
                partial_derivative 2 (W n) (wan_circ x0 r (al + drop s)))`;
    `\n s. r pow 2 *
           (norm(partial_derivative 1 ((W:num->real^2->real^K) n) (wan_circ x0 r (al + drop s)) -
                 wan_wd D 1 u (wan_circ x0 r (al + drop s))) pow 2 +
            norm(partial_derivative 2 (W n) (wan_circ x0 r (al + drop s)) -
                 wan_wd D 2 u (wan_circ x0 r (al + drop s))) pow 2)`;
    `\n. (W:num->real^2->real^K) n (wan_circ x0 r (al + t2)) - W n (wan_circ x0 r (al + t1))`] THEN
  REWRITE_TAC[LIFT_DROP] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_CMUL THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ADD THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`\s. wan_wd D 1 (u:real^2->real^K) (wan_circ x0 r (al + drop s))`;
                     `lift t1`; `lift t2`; `al:real`] WAN_TRIG_PRODUCT_ABS_INT);
      MP_TAC(ISPECL [`\s. wan_wd D 2 (u:real^2->real^K) (wan_circ x0 r (al + drop s))`;
                     `lift t1`; `lift t2`; `al:real`] WAN_TRIG_PRODUCT_ABS_INT)] THEN
    ASM_SIMP_TAC[];
    GEN_TAC THEN MATCH_MP_TAC WAN_CIRC_FTC_SMOOTH THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC LIM_SUB THEN CONJ_TAC THEN MATCH_MP_TAC WAN_HARMONIC_BOUND_LIM THEN
    GEN_TAC THEN REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `inv(&n + &1)`)) (concl th))) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    GEN_TAC THEN REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`n:num`; `s:real^1`] THEN DISCH_TAC THEN
    REWRITE_TAC[VECTOR_ARITH
     `r % (a % x1 + b % x2) - r % (a % y1 + b % y2):real^N =
      r % (a % (x1 - y1) + b % (x2 - y2))`] THEN
    REWRITE_TAC[NORM_MUL; REAL_POW_MUL; REAL_POW2_ABS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2; WAN_TRIG_COMB_SQ];
    REWRITE_TAC[LIFT_CMUL] THEN
    SUBGOAL_THEN `&0 = r pow 2 * &0` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
    EXISTS_TAC `\n. r pow 2 *
       drop(integral (interval[lift t1,lift t2])
         (\s. lift(norm(partial_derivative 1 ((W:num->real^2->real^K) n)
                          (wan_circ x0 r (al + drop s)) -
                        wan_wd D 1 u (wan_circ x0 r (al + drop s))) pow 2 +
                   norm(partial_derivative 2 (W n) (wan_circ x0 r (al + drop s)) -
                        wan_wd D 2 u (wan_circ x0 r (al + drop s))) pow 2)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
      ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL];
      MATCH_MP_TAC REALLIM_LMUL THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Absolute continuity on almost every arc in an open set; WAN_CIRCLE_ACL.  *)
(* ------------------------------------------------------------------------- *)

let WAN_CIRC_CONT = prove
 (`!(x0:real^2) r al. (\s. wan_circ x0 r (al + drop s)) continuous_on (:real^1)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
  REWRITE_TAC[differentiable] THEN
  MP_TAC(SPECL [`x0:real^2`; `r:real`; `al:real`; `t:real^1`] WAN_CIRC_VDERIV) THEN
  REWRITE_TAC[has_vector_derivative] THEN MESON_TAC[]);;

let WAN_ARC_ACL = prove
 (`!(D:real^2->bool) (u:real^2->real^K) x0 al.
     open D /\ u continuous_on D /\ wan_w12 D u
     ==> ?S. negligible S /\
             !r t1 t2.
               &0 < r /\ ~(lift r IN S) /\ &0 <= t1 /\ t1 <= t2 /\ t2 <= &2 * pi /\
               (!t. t1 <= t /\ t <= t2 ==> wan_circ x0 r (al + t) IN D)
               ==> ((\s. r % (--(sin(al + drop s)) %
                              wan_wd D 1 u (wan_circ x0 r (al + drop s)) +
                              cos(al + drop s) %
                              wan_wd D 2 u (wan_circ x0 r (al + drop s))))
                    has_integral (u(wan_circ x0 r (al + t2)) - u(wan_circ x0 r (al + t1))))
                   (interval[lift t1,lift t2]) /\
                   (\s. lift(norm(wan_wd D 1 u (wan_circ x0 r (al + drop s))) pow 2 +
                             norm(wan_wd D 2 u (wan_circ x0 r (al + drop s))) pow 2))
                   integrable_on interval[lift t1,lift t2]`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_UNION_COMPACT_SUBSETS) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->real^2->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?S:num->real^1->bool.
      !n. negligible(S n) /\
          !r t1 t2.
            &0 < r /\ ~(lift r IN S n) /\ &0 <= t1 /\ t1 <= t2 /\ t2 <= &2 * pi /\
            (!t. t1 <= t /\ t <= t2 ==> wan_circ x0 r (al + t) IN f n)
            ==> ((\s. r % (--(sin(al + drop s)) %
                           wan_wd D 1 (u:real^2->real^K) (wan_circ x0 r (al + drop s)) +
                           cos(al + drop s) %
                           wan_wd D 2 u (wan_circ x0 r (al + drop s))))
                 has_integral (u(wan_circ x0 r (al + t2)) - u(wan_circ x0 r (al + t1))))
                (interval[lift t1,lift t2]) /\
                (\s. lift(norm(wan_wd D 1 u (wan_circ x0 r (al + drop s))) pow 2 +
                          norm(wan_wd D 2 u (wan_circ x0 r (al + drop s))) pow 2))
                integrable_on interval[lift t1,lift t2]`
  (X_CHOOSE_THEN `S:num->real^1->bool` (LABEL_TAC "S")) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN GEN_TAC THEN MATCH_MP_TAC WAN_ARC_ACL_K THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `UNIONS {(S:num->real^1->bool) n | n IN (:num)}` THEN CONJ_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_COUNTABLE_UNIONS THEN USE_THEN "S" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`r:real`; `t1:real`; `t2:real`] THEN
  REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV; NOT_EXISTS_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `compact(IMAGE (\s. wan_circ x0 r (al + drop s)) (interval[lift t1,lift t2])) /\
    IMAGE (\s. wan_circ x0 r (al + drop s)) (interval[lift t1,lift t2]) SUBSET D`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN REWRITE_TAC[COMPACT_INTERVAL] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
      REWRITE_TAC[SUBSET_UNIV; WAN_CIRC_CONT];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1; LIFT_DROP] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `IMAGE (\s. wan_circ x0 r (al + drop s)) (interval[lift t1,lift t2])` o
   check (fun th -> is_forall(concl th) && can (find_term ((=) `compact:(real^2->bool)->bool`))
                    (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  USE_THEN "S" (MP_TAC o SPECL [`r:real`; `t1:real`; `t2:real`] o CONJUNCT2 o SPEC `N:num`) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN REWRITE_TAC[GE; LE_REFL] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN(MP_TAC o SPEC `lift t`) THEN
  REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

let WAN_CIRC_IN_BALL = prove
 (`!(a:real^2) R r t. &0 <= r /\ r < R ==> wan_circ a r t IN ball(a,R)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_BALL; dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
  ASM_REWRITE_TAC[WAN_CIRC_NORM] THEN ASM_REAL_ARITH_TAC);;

let WAN_CIRCLE_ACL = prove
 (`!(kk:K->bool). WAN_CIRCLE_ACL_STATEMENT kk`,
  GEN_TAC THEN REWRITE_TAC[WAN_CIRCLE_ACL_STATEMENT] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ball(a:real^2,R)`; `u:real^2->real^K`; `a:real^2`; `&0`] WAN_ARC_ACL) THEN
  ASM_REWRITE_TAC[OPEN_BALL; REAL_ADD_LID] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `S:real^1->bool` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`r:real`; `&0`; `t:real`]) THEN
    ASM_SIMP_TAC[REAL_LE_REFL; LIFT_NUM; WAN_CIRC_IN_BALL; REAL_LT_IMP_LE];
    FIRST_X_ASSUM(MP_TAC o SPECL [`r:real`; `&0`; `&2 * pi`]) THEN
    ASM_SIMP_TAC[REAL_LE_REFL; LIFT_NUM; WAN_CIRC_IN_BALL; REAL_LT_IMP_LE] THEN
    ANTS_TAC THENL [MP_TAC PI_POS THEN REAL_ARITH_TAC; SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Tools for the Courant-Lebesgue lemma.                                     *)
(* ------------------------------------------------------------------------- *)

let WAN_L2_BOUND_LSPACE = prove
 (`!(v:real^M->real^K) g s.
     v measurable_on s /\ (\x. lift(g x)) integrable_on s /\
     (!x. x IN s ==> norm(v x) pow 2 <= g x)
     ==> v IN lspace s (&2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lspace; IN_ELIM_THM; RPOW_POW] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `\x. lift((g:real^M->real) x)` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_ON_LIFT_POW THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MEASURABLE_ON_NORM];
    REWRITE_TAC[NORM_LIFT; LIFT_DROP; REAL_ABS_POW; REAL_ABS_NORM] THEN ASM_SIMP_TAC[]]);;

let WAN_CIRC_PERIODIC_REP = prove
 (`!(a:real^2) r t. ?s. &0 <= s /\ s <= &2 * pi /\ wan_circ a r t = wan_circ a r s`,
  REPEAT GEN_TAC THEN MP_TAC(SPEC `t:real` SINCOS_PRINCIPAL_VALUE) THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `&0 <= y` THENL
   [EXISTS_TAC `y:real` THEN ASM_REWRITE_TAC[wan_circ] THEN
    MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC;
    EXISTS_TAC `y + &2 * pi` THEN ASM_REWRITE_TAC[wan_circ; SIN_PERIODIC; COS_PERIODIC] THEN
    ASM_REAL_ARITH_TAC]);;

let WAN_INTEGRAL_INV = prove
 (`!c A B. &0 < A /\ A <= B
           ==> ((\r. lift(c * inv(drop r))) has_integral lift(c * (log B - log A)))
               (interval[lift A,lift B])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\r:real^1. lift(c * log(drop r))`; `\r:real^1. lift(c * inv(drop r))`;
                 `lift A`; `lift B`] FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  ASM_REWRITE_TAC[LIFT_DROP; REAL_SUB_LDISTRIB; LIFT_SUB] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `x:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN STRIP_TAC THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
  REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_CMUL THEN
  MP_TAC(SPEC `drop x` HAS_REAL_DERIVATIVE_LOG) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; LIFT_DROP; o_DEF]);;

let WAN_LOG_SQRT_RATIO = prove
 (`!d R. &0 < d /\ &0 < R ==> log(sqrt d * R) - log(d * R) = log(inv d) / &2`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LOG_MUL; SQRT_POS_LT; LOG_SQRT; LOG_INV] THEN
  REAL_ARITH_TAC);;

let WAN_DIR_2D_EQ = prove
 (`!(s:real^2->bool) (u:real^2->real^K).
     wan_w12 s u
     ==> wan_dir s u =
         drop(integral s (\x. lift(norm(wan_wd s 1 u x) pow 2 + norm(wan_wd s 2 u x) pow 2)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_dir; DIMINDEX_2; SUM_2; LIFT_ADD] THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= 2
                    ==> (\x. lift(norm(wan_wd s i (u:real^2->real^K) x) pow 2)) integrable_on s`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN
    REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[WAN_WD_WORKS; DIMINDEX_2];
    ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGRAL_ADD; DROP_ADD; ARITH]);;

let WAN_INTEGRAL_STRICT_AE = prove
 (`!(f:real^1->real^1) g a b N.
     drop a < drop b /\ f integrable_on interval[a,b] /\ g integrable_on interval[a,b] /\
     negligible N /\ (!x. x IN interval[a,b] DIFF N ==> drop(g x) < drop(f x))
     ==> drop(integral (interval[a,b]) g) < drop(integral (interval[a,b]) f)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `h = \x. if x IN N then vec 0 else (f:real^1->real^1) x - g x` THEN
  SUBGOAL_THEN
   `(h:real^1->real^1) integrable_on interval[a,b] /\
    integral (interval[a,b]) h = integral (interval[a,b]) f - integral (interval[a,b]) g`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(\x. (f:real^1->real^1) x - g x) integrable_on interval[a,b]` ASSUME_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
    SUBGOAL_THEN `!x. x IN interval[a,b] DIFF N
                      ==> (h:real^1->real^1) x = (\x. (f:real^1->real^1) x - g x) x`
    ASSUME_TAC THENL
     [EXPAND_TAC "h" THEN SIMP_TAC[IN_DIFF]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] INTEGRABLE_SPIKE) THEN
      EXISTS_TAC `\x. (f:real^1->real^1) x - g x` THEN EXISTS_TAC `N:real^1->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `integral (interval[a,b]) (\x. (f:real^1->real^1) x - g x)` THEN
      CONJ_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_SPIKE THEN
        EXISTS_TAC `N:real^1->bool` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC INTEGRAL_SUB THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN interval[a,b] ==> &0 <= drop((h:real^1->real^1) x)` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN EXPAND_TAC "h" THEN
    COND_CASES_TAC THEN REWRITE_TAC[DROP_VEC; REAL_LE_REFL; DROP_SUB] THEN
    MATCH_MP_TAC(REAL_ARITH `a < b ==> &0 <= b - a`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DIFF];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN REWRITE_TAC[GSYM DROP_SUB] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
  REWRITE_TAC[REAL_LT_LE] THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  MP_TAC(ISPECL [`h:real^1->real^1`; `interval[a:real^1,b]`] HAS_INTEGRAL_NEGLIGIBLE_EQ) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_1] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `i = 1` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM drop] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((h:real^1->real^1) has_integral vec 0) (interval[a,b])`
  (fun th -> REWRITE_TAC[th]) THENL
   [SUBGOAL_THEN `vec 0:real^1 = integral (interval[a:real^1,b]) (h:real^1->real^1)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[GSYM DROP_EQ; DROP_VEC]; ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `negligible(interval[a:real^1,b])` MP_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `{x | x IN interval[a,b] /\ ~((h:real^1->real^1) x = vec 0)} UNION N` THEN
    ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(x:real^1) IN N` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "h" THEN ASM_REWRITE_TAC[GSYM DROP_EQ; DROP_SUB; DROP_VEC] THEN
    MATCH_MP_TAC(REAL_ARITH `a < b ==> ~(b - a = &0)`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DIFF];
    REWRITE_TAC[NEGLIGIBLE_INTERVAL; INTERVAL_EQ_EMPTY_1] THEN ASM_REAL_ARITH_TAC]);;

let WAN_LOOP_L1_BOUND = prove
 (`!(v:real^1->real^K) (U:real->real^K) t1 t2.
     (!t. &0 <= t /\ t <= &2 * pi ==> (v has_integral (U t - U(&0))) (interval[vec 0,lift t])) /\
     U(&2 * pi) = U(&0) /\
     v absolutely_integrable_on interval[vec 0,lift(&2 * pi)] /\
     &0 <= t1 /\ t1 <= t2 /\ t2 <= &2 * pi
     ==> &2 * norm(U t1 - U t2) <=
         drop(integral (interval[vec 0,lift(&2 * pi)]) (\s. lift(norm(v s))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!c d. &0 <= c /\ c <= d /\ d <= &2 * pi
          ==> (v:real^1->real^K) absolutely_integrable_on interval[lift c,lift d]`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_SUBINTERVAL THEN
    EXISTS_TAC `interval[vec 0:real^1,lift(&2 * pi)]` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c d. &0 <= c /\ c <= d /\ d <= &2 * pi
          ==> norm(integral (interval[lift c,lift d]) (v:real^1->real^K)) <=
              drop(integral (interval[lift c,lift d]) (\s. lift(norm(v s))))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
    REWRITE_TAC[LIFT_DROP; REAL_LE_REFL] THEN
    SUBGOAL_THEN `(v:real^1->real^K) absolutely_integrable_on interval[lift c,lift d]`
    MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SIMP_TAC[absolutely_integrable_on];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &2 * pi` ASSUME_TAC THENL
   [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!c. &0 <= c /\ c <= &2 * pi
        ==> integral (interval[vec 0,lift c]) (v:real^1->real^K) = U c - U(&0)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral (interval[lift t1,lift t2]) (v:real^1->real^K) = U t2 - U t1 /\
    integral (interval[lift t2,lift(&2 * pi)]) (v:real^1->real^K) = U(&0) - U t2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`v:real^1->real^K`; `vec 0:real^1`; `lift t2`; `lift t1`]
                    INTEGRAL_COMBINE);
      MP_TAC(ISPECL [`v:real^1->real^K`; `vec 0:real^1`; `lift(&2 * pi)`; `lift t2`]
                    INTEGRAL_COMBINE)] THEN
    REWRITE_TAC[LIFT_DROP; DROP_VEC] THEN
    (ANTS_TAC THENL
      [REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
       MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
       REWRITE_TAC[GSYM LIFT_NUM] THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
       ALL_TAC]) THEN
    REWRITE_TAC[GSYM LIFT_NUM] THEN
    (SUBGOAL_THEN `integral (interval[lift(&0),lift t1]) (v:real^1->real^K) = U t1 - U(&0) /\
                   integral (interval[lift(&0),lift t2]) v = U t2 - U(&0) /\
                   integral (interval[lift(&0),lift(&2 * pi)]) v = U(&2 * pi) - U(&0)`
     (fun th -> REWRITE_TAC[th]) THENL
      [REWRITE_TAC[LIFT_NUM] THEN REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
       ASM_REAL_ARITH_TAC;
       ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `drop(integral (interval[lift(&0),lift t1]) (\s. lift(norm((v:real^1->real^K) s)))) +
    drop(integral (interval[lift t1,lift t2]) (\s. lift(norm(v s)))) +
    drop(integral (interval[lift t2,lift(&2 * pi)]) (\s. lift(norm(v s)))) =
    drop(integral (interval[vec 0,lift(&2 * pi)]) (\s. lift(norm(v s))))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM DROP_ADD; GSYM LIFT_NUM] THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `(\s. lift(norm((v:real^1->real^K) s))) integrable_on
                  interval[lift(&0),lift(&2 * pi)]` ASSUME_TAC THENL
     [REWRITE_TAC[LIFT_NUM] THEN
      SUBGOAL_THEN `(v:real^1->real^K) absolutely_integrable_on interval[vec 0,lift(&2 * pi)]`
      MP_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[absolutely_integrable_on]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(\s. lift(norm((v:real^1->real^K) s))) integrable_on interval[lift(&0),lift t2]`
    ASSUME_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
      EXISTS_TAC `interval[lift(&0),lift(&2 * pi)]` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `integral (interval[lift(&0),lift t1]) (\s. lift(norm((v:real^1->real^K) s))) +
      integral (interval[lift t1,lift t2]) (\s. lift(norm(v s))) =
      integral (interval[lift(&0),lift t2]) (\s. lift(norm(v s)))`
    (LABEL_TAC "c1") THENL
     [MATCH_MP_TAC INTEGRAL_COMBINE THEN ASM_REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
    SUBGOAL_THEN
     `integral (interval[lift(&0),lift t2]) (\s. lift(norm((v:real^1->real^K) s))) +
      integral (interval[lift t2,lift(&2 * pi)]) (\s. lift(norm(v s))) =
      integral (interval[lift(&0),lift(&2 * pi)]) (\s. lift(norm(v s)))`
    (LABEL_TAC "c2") THENL
     [MATCH_MP_TAC INTEGRAL_COMBINE THEN ASM_REWRITE_TAC[LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REMOVE_THEN "c1" MP_TAC THEN REMOVE_THEN "c2" MP_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC(REAL_ARITH `x <= b /\ x <= a + c ==> &2 * x <= a + b + c`) THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `norm((U:real->real^K) t1 - U t2) =
                  norm(integral (interval[lift t1,lift t2]) (v:real^1->real^K))`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC NORM_ARITH; ALL_TAC] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(integral (interval[lift(&0),lift t1]) (v:real^1->real^K)) +
              norm(integral (interval[lift t2,lift(&2 * pi)]) v)` THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[LIFT_NUM] THEN
    SUBGOAL_THEN `integral (interval[vec 0,lift t1]) (v:real^1->real^K) = U t1 - U(&0)`
    SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC NORM_ARITH;
    MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC]);;

let WAN_LOOP_OSC_BOUND = prove
 (`!(v:real^1->real^K) (U:real->real^K) g.
     (!t. &0 <= t /\ t <= &2 * pi ==> (v has_integral (U t - U(&0))) (interval[vec 0,lift t])) /\
     U(&2 * pi) = U(&0) /\
     (\s. lift(g s)) integrable_on interval[vec 0,lift(&2 * pi)] /\
     (!s. s IN interval[vec 0,lift(&2 * pi)] ==> norm(v s) pow 2 <= g s)
     ==> !t1 t2. &0 <= t1 /\ t1 <= &2 * pi /\ &0 <= t2 /\ t2 <= &2 * pi
                 ==> norm(U t1 - U t2) pow 2 <=
                     pi / &2 * drop(integral (interval[vec 0,lift(&2 * pi)]) (\s. lift(g s)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &2 * pi` ASSUME_TAC THENL [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^1->real^K) integrable_on interval[vec 0,lift(&2 * pi)]` ASSUME_TAC THENL
   [REWRITE_TAC[integrable_on] THEN EXISTS_TAC `(U:real->real^K)(&2 * pi) - U(&0)` THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(v:real^1->real^K) IN lspace (interval[vec 0,lift(&2 * pi)]) (&2) /\
    (\s. lift(norm((v:real^1->real^K) s))) IN lspace (interval[vec 0,lift(&2 * pi)]) (&2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC WAN_L2_BOUND_LSPACE THEN EXISTS_TAC `g:real^1->real` THEN
    ASM_SIMP_TAC[INTEGRABLE_IMP_MEASURABLE; MEASURABLE_ON_NORM; NORM_LIFT; REAL_ABS_NORM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^1->real^K) absolutely_integrable_on interval[vec 0,lift(&2 * pi)]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_LSPACE2_ABS_INT_MEAS THEN ASM_REWRITE_TAC[MEASURABLE_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `drop(integral (interval[vec 0,lift(&2 * pi)]) (\s. lift(norm((v:real^1->real^K) s)))) pow 2
    <= &2 * pi * drop(integral (interval[vec 0,lift(&2 * pi)]) (\s. lift(g s)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`interval[vec 0:real^1,lift(&2 * pi)]`;
                   `\s. lift(norm((v:real^1->real^K) s))`] WAN_INTEGRAL_SQ_CS) THEN
    ASM_REWRITE_TAC[MEASURABLE_INTERVAL; MEASURE_INTERVAL_1; LIFT_DROP; DROP_VEC;
                    NORM_LIFT; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_SUB_RZERO; NORM_1; REAL_POW2_ABS] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_SIMP_TAC[LIFT_DROP] THEN
    MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t1 t2. &0 <= t1 /\ t1 <= t2 /\ t2 <= &2 * pi
            ==> norm((U:real->real^K) t1 - U t2) pow 2 <=
                pi / &2 * drop(integral (interval[vec 0,lift(&2 * pi)]) (\s. lift(g s)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`v:real^1->real^K`; `U:real->real^K`; `t1:real`; `t2:real`]
                  WAN_LOOP_L1_BOUND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(&2 * norm((U:real->real^K) t1 - U t2)) pow 2 <=
      drop(integral (interval[vec 0,lift(&2 * pi)]) (\s. lift(norm((v:real^1->real^K) s)))) pow 2`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; NORM_POS_LE];
      ALL_TAC] THEN
    UNDISCH_TAC
     `drop(integral (interval[vec 0,lift(&2 * pi)]) (\s. lift(norm((v:real^1->real^K) s)))) pow 2
      <= &2 * pi * drop(integral (interval[vec 0,lift(&2 * pi)]) (\s. lift(g s)))` THEN
    REWRITE_TAC[REAL_POW_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `t1 <= t2` THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[NORM_SUB] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The Courant-Lebesgue lemma (interior circles).                            *)
(* ------------------------------------------------------------------------- *)

let WAN_CIRC_2PI = prove
 (`!(a:real^2) r. wan_circ a r (&2 * pi) = wan_circ a r (&0)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPEC `&0` SIN_PERIODIC) THEN MP_TAC(SPEC `&0` COS_PERIODIC) THEN
  REWRITE_TAC[REAL_ADD_LID] THEN SIMP_TAC[wan_circ]);;

let WAN_CIRCLE_OSC_AE = prove
 (`!(a:real^2) R (u:real^2->real^K).
     &0 < R /\ u continuous_on ball(a,R) /\ wan_w12 (ball(a,R)) u
     ==> ?S. negligible S /\
             !r. &0 < r /\ r < R /\ ~(lift r IN S)
                 ==> (\s. lift(norm(wan_wd (ball(a,R)) 1 u (wan_circ a r (drop s))) pow 2 +
                               norm(wan_wd (ball(a,R)) 2 u (wan_circ a r (drop s))) pow 2))
                     integrable_on interval[vec 0,lift(&2 * pi)] /\
                     !t1 t2. norm(u(wan_circ a r t1) - u(wan_circ a r t2)) pow 2 <=
                             pi / &2 * r pow 2 *
                             drop(integral (interval[vec 0,lift(&2 * pi)])
                                    (\s. lift(norm(wan_wd (ball(a,R)) 1 u
                                                     (wan_circ a r (drop s))) pow 2 +
                                              norm(wan_wd (ball(a,R)) 2 u
                                                     (wan_circ a r (drop s))) pow 2)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `kk:K->bool` WAN_CIRCLE_ACL) THEN REWRITE_TAC[WAN_CIRCLE_ACL_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`a:real^2`; `R:real`; `u:real^2->real^K`]) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `S:real^1->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL
   [`\s. r % (--(sin(drop s)) % wan_wd (ball(a,R)) 1 (u:real^2->real^K) (wan_circ a r (drop s)) +
             cos(drop s) % wan_wd (ball(a,R)) 2 u (wan_circ a r (drop s)))`;
    `\t. (u:real^2->real^K)(wan_circ a r t)`;
    `\s. r pow 2 * (norm(wan_wd (ball(a,R)) 1 (u:real^2->real^K) (wan_circ a r (drop s))) pow 2 +
                    norm(wan_wd (ball(a,R)) 2 u (wan_circ a r (drop s))) pow 2)`]
   WAN_LOOP_OSC_BOUND) THEN
  SUBGOAL_THEN `!x. lift(r pow 2 * x) = r pow 2 % lift x` ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_CMUL]; ALL_TAC] THEN
  REWRITE_TAC[WAN_CIRC_2PI] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_MUL; REAL_POW_MUL; REAL_POW2_ABS] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2; WAN_TRIG_COMB_SQ]];
    ALL_TAC] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`t1:real`; `t2:real`] THEN
  MP_TAC(SPECL [`a:real^2`; `r:real`; `t1:real`] WAN_CIRC_PERIODIC_REP) THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`a:real^2`; `r:real`; `t2:real`] WAN_CIRC_PERIODIC_REP) THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:real` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s1:real`; `s2:real`] o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `pi / &2`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL] THEN REWRITE_TAC[REAL_MUL_AC]);;

let WAN_SQRT_FACTS = prove
 (`!d. &0 < d /\ d < &1
       ==> &0 < sqrt d /\ d < sqrt d /\ sqrt d < &1 /\ &0 < log(inv d)`,
  GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT];
    MATCH_MP_TAC REAL_LT_RSQRT THEN REWRITE_TAC[REAL_POW_2] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[];
    GEN_REWRITE_TAC RAND_CONV [GSYM SQRT_1] THEN MATCH_MP_TAC SQRT_MONO_LT THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC LOG_POS_LT THEN MATCH_MP_TAC REAL_INV_1_LT THEN ASM_REWRITE_TAC[]]);;

let WAN_COURANT_LEBESGUE = prove
 (`!(kk:K->bool). WAN_COURANT_LEBESGUE_STATEMENT kk`,
  GEN_TAC THEN REWRITE_TAC[WAN_COURANT_LEBESGUE_STATEMENT] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^2`; `R:real`; `u:real^2->real^K`] WAN_CIRCLE_OSC_AE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^1->bool` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "S"))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WAN_SQRT_FACTS o CONJ
    (ASSUME `&0 < d`)) THEN
  SUBGOAL_THEN `&0 <= E` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ball(a:real^2,R)`; `u:real^2->real^K`] WAN_DIR_POS) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < d * R /\ d * R < sqrt d * R /\ sqrt d * R < R` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_RMUL_EQ] THEN
    GEN_REWRITE_TAC (RAND_CONV) [GSYM REAL_MUL_LID] THEN
    ASM_SIMP_TAC[REAL_LT_RMUL_EQ];
    ALL_TAC] THEN
  ABBREV_TAC
   `G = \x. lift(norm(wan_wd (ball(a,R)) 1 (u:real^2->real^K) x) pow 2 +
                 norm(wan_wd (ball(a,R)) 2 u x) pow 2)` THEN
  SUBGOAL_THEN
   `{x:real^2 | d * R < norm(x - a) /\ norm(x - a) < sqrt d * R} SUBSET ball(a,R) /\
    lebesgue_measurable {x:real^2 | d * R < norm(x - a) /\ norm(x - a) < sqrt d * R}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[WAN_ANNULUS_EQ] THEN REWRITE_TAC[SUBSET; IN_DIFF; IN_BALL] THEN
    ASM_MESON_TAC[REAL_LT_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(G:real^2->real^1) absolutely_integrable_on ball(a,R) /\
    G absolutely_integrable_on {x:real^2 | d * R < norm(x - a) /\ norm(x - a) < sqrt d * R}`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN CONJ_TAC THEN MATCH_MP_TAC WAN_DIR_DENSITY_ABS_INT THEN
    ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL; SUBSET_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^2->real^1`; `a:real^2`; `&0`; `d * R`; `sqrt d * R`]
                WAN_POLAR_ANNULUS) THEN
  ASM_SIMP_TAC[REAL_ADD_LID; REAL_LT_IMP_LE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `drop(integral (interval[lift(d * R),lift(sqrt d * R)])
           (\r. drop r % integral (interval[vec 0,lift(&2 * pi)])
                           (\t. (G:real^2->real^1)(wan_circ a (drop r) (drop t))))) <= &2 * E`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `drop(integral (ball(a:real^2,R)) G)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
      ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
      EXPAND_TAC "G" THEN REWRITE_TAC[LIFT_DROP] THEN
      SIMP_TAC[REAL_LE_ADD; REAL_LE_POW_2];
      EXPAND_TAC "G" THEN ASM_SIMP_TAC[GSYM WAN_DIR_2D_EQ]];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(LABEL_TAC "neg" o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  ABBREV_TAC `c = &8 * E / log(inv d)` THEN
  MP_TAC(ISPECL [`c:real`; `d * R`; `sqrt d * R`] WAN_INTEGRAL_INV) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; WAN_LOG_SQRT_RATIO] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`\r. drop r % integral (interval[vec 0,lift(&2 * pi)])
                    (\t. (G:real^2->real^1)(wan_circ a (drop r) (drop t)))`;
    `\r:real^1. lift(c * inv(drop r))`; `lift(d * R)`; `lift(sqrt d * R)`;
    `lift(d * R) INSERT lift(sqrt d * R) INSERT (S:real^1->bool)`]
   WAN_INTEGRAL_STRICT_AE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LIFT_DROP; NEGLIGIBLE_INSERT] THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
      ASM_MESON_TAC[integrable_on];
      ALL_TAC] THEN
    X_GEN_TAC `x:real^1` THEN
    REWRITE_TAC[IN_DIFF; IN_INSERT; IN_INTERVAL_1; LIFT_DROP; DE_MORGAN_THM;
                GSYM DROP_EQ] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `d * R < drop x /\ drop x < sqrt d * R` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "S" (MP_TAC o SPEC `drop x`) THEN REWRITE_TAC[LIFT_DROP] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "osc")) THEN
    REMOVE_THEN "neg" (MP_TAC o SPEC `drop x`) THEN ASM_REWRITE_TAC[NOT_FORALL_THM; REAL_NOT_LE] THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:real` (X_CHOOSE_TAC `t2:real`)) THEN
    USE_THEN "osc" (MP_TAC o SPECL [`t1:real`; `t2:real`]) THEN
    ABBREV_TAC
     `J = drop(integral (interval[vec 0,lift(&2 * pi)])
                (\s. lift(norm(wan_wd (ball(a,R)) 1 (u:real^2->real^K)
                                 (wan_circ a (drop x) (drop s))) pow 2 +
                          norm(wan_wd (ball(a,R)) 2 u (wan_circ a (drop x) (drop s))) pow 2)))` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `drop(drop x % integral (interval[vec 0,lift(&2 * pi)])
                         (\t. (G:real^2->real^1)(wan_circ a (drop x) (drop t)))) = drop x * J`
    SUBST1_TAC THENL
     [REWRITE_TAC[DROP_CMUL] THEN EXPAND_TAC "G" THEN EXPAND_TAC "J" THEN REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[LIFT_DROP] THEN
    SUBGOAL_THEN `&4 * pi * E / log(inv d) = pi / &2 * c` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [EXPAND_TAC "c" THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= pi / &2 * c` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MP_TAC PI_POS THEN REAL_ARITH_TAC;
        EXPAND_TAC "c" THEN MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      ALL_TAC] THEN
    SUBGOAL_THEN `pi / &2 * c < pi / &2 * drop x pow 2 * J` MP_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC `norm((u:real^2->real^K)(wan_circ a (drop x) t1) - u(wan_circ a (drop x) t2)) pow 2` THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM(MATCH_MP SQRT_POW_2 th)]) THEN
      MATCH_MP_TAC REAL_POW_LT2 THEN ASM_SIMP_TAC[SQRT_POS_LE; ARITH];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    SIMP_TAC[REAL_LT_LMUL_EQ; REAL_ARITH `&0 < pi ==> &0 < pi / &2`; PI_POS] THEN
    SUBGOAL_THEN `&0 < drop x` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ] THEN
    SUBGOAL_THEN `(drop x * J) * drop x = drop x pow 2 * J` SUBST1_TAC THENL
     [CONV_TAC REAL_RING; REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral (interval[lift(d * R),lift(sqrt d * R)]) (\r:real^1. lift(c * inv(drop r))) =
    lift(c * log(inv d) / &2)`
  SUBST1_TAC THENL [MATCH_MP_TAC INTEGRAL_UNIQUE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LIFT_DROP] THEN
  SUBGOAL_THEN `c * log(inv d) / &2 = &4 * E` SUBST1_TAC THENL
   [EXPAND_TAC "c" THEN UNDISCH_TAC `&0 < log(inv d)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Arcs of circles centred at a boundary point of a disc.                    *)
(* ------------------------------------------------------------------------- *)

let WAN_CIRC_TRIG_EQ = prove
 (`!(x0:real^2) r al x y.
     sin x = sin y /\ cos x = cos y ==> wan_circ x0 r (al + x) = wan_circ x0 r (al + y)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[wan_circ; SIN_ADD; COS_ADD]);;

let WAN_CIRC_OFFSET_REP = prove
 (`!(x0:real^2) r al t. ?s. &0 <= s /\ s <= &2 * pi /\ wan_circ x0 r t = wan_circ x0 r (al + s)`,
  REPEAT GEN_TAC THEN MP_TAC(SPEC `t - al` SINCOS_PRINCIPAL_VALUE) THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `wan_circ x0 r t = wan_circ x0 r (al + (t - al))` SUBST1_TAC THENL
   [AP_TERM_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= y` THENL
   [EXISTS_TAC `y:real` THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC WAN_CIRC_TRIG_EQ THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `y + &2 * pi` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC WAN_CIRC_TRIG_EQ THEN ASM_REWRITE_TAC[SIN_PERIODIC; COS_PERIODIC]]);;

let WAN_SPHERE_CIRC = prove
 (`!(x0:real^2) r y. y IN sphere(x0,r) ==> ?t. wan_circ x0 r t = y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SPHERE; dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
  DISCH_TAC THEN EXISTS_TAC `Arg(y - x0:complex)` THEN
  REWRITE_TAC[WAN_CIRC_CEXP] THEN
  MP_TAC(SPEC `y - x0:complex` ARG) THEN
  DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV) [VECTOR_ARITH `y:real^2 = x0 + (y - x0)`] THEN
                       GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th]) THEN
  REWRITE_TAC[]);;

let WAN_COS_NEG_RANGE = prove
 (`!x. &0 <= x /\ x <= &2 * pi /\ cos x < &0 ==> pi / &2 < x /\ x < &3 * pi / &2`,
  GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN
  ONCE_REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  UNDISCH_TAC `cos x < &0` THEN REWRITE_TAC[REAL_NOT_LT] THENL
   [MATCH_MP_TAC COS_POS_PI_LE THEN MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `cos x = cos((x - &2 * pi) + &2 * pi)` SUBST1_TAC THENL
     [AP_TERM_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[COS_PERIODIC] THEN MATCH_MP_TAC COS_POS_PI_LE THEN
    MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC]);;

let WAN_COS_ARC = prove
 (`!k ty tz t.
     &0 <= ty /\ ty <= t /\ t <= tz /\ tz <= &2 * pi /\ cos ty < --k /\ cos tz < --k
     ==> cos t < --k`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `t <= pi` THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `cos ty` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC COS_MONO_LE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `cos tz` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `cos t = cos(&2 * pi - t) /\ cos tz = cos(&2 * pi - tz)`
    (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[COS_SUB; COS_NPI; SIN_NPI] THEN CONV_TAC REAL_RING;
      MATCH_MP_TAC COS_MONO_LE THEN ASM_REAL_ARITH_TAC]]);;

let WAN_CIRC_BDRY_BALL = prove
 (`!(x0:real^2) R r th0 t.
     &0 < r /\ &0 < R
     ==> (wan_circ x0 r ((th0 - pi) + t) IN ball(wan_circ x0 R th0,R) <=>
          cos t < --(r / (&2 * R)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_BALL; dist] THEN
  SUBGOAL_THEN
   `norm(wan_circ x0 R th0 - wan_circ x0 r ((th0 - pi) + t)) pow 2 =
    R pow 2 + r pow 2 + &2 * R * r * cos t`
  ASSUME_TAC THENL
   [REWRITE_TAC[wan_circ; VECTOR_ARITH `(x + a) - (x + b):real^N = a - b`] THEN
    REWRITE_TAC[NORM_POW_2; DOT_2; VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_2] THEN
    REWRITE_TAC[REAL_ARITH `(th0 - pi) + t = (th0 + t) - pi`; COS_SUB; SIN_SUB; COS_PI;
                SIN_PI; COS_ADD; SIN_ADD] THEN
    MP_TAC(SPEC `th0:real` SIN_CIRCLE) THEN MP_TAC(SPEC `t:real` SIN_CIRCLE) THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  EQ_TAC THEN DISCH_TAC THENL
   [SUBGOAL_THEN `norm(wan_circ x0 R th0 - wan_circ x0 r ((th0 - pi) + t)) pow 2 < R pow 2`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN ARITH_TAC;
      ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
    SUBGOAL_THEN `r * (r + &2 * R * cos t) < &0` MP_TAC THENL
     [MP_TAC(REAL_RING `r * (r + &2 * R * cos t) =
                        (R pow 2 + r pow 2 + &2 * R * r * cos t) - R pow 2`) THEN
      UNDISCH_TAC `R pow 2 + r pow 2 + &2 * R * r * cos t < R pow 2` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> (r * x < &0 <=> r * x < r * &0)`; REAL_LT_LMUL_EQ] THEN
    ASM_SIMP_TAC[REAL_FIELD `&0 < R ==> --(r / (&2 * R)) = (--r) / (&2 * R)`;
                 REAL_LT_RDIV_EQ; REAL_ARITH `&0 < R ==> &0 < &2 * R`] THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `2` THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    SUBGOAL_THEN `r + &2 * R * cos t < &0` MP_TAC THENL
     [UNDISCH_TAC `cos t < --(r / (&2 * R))` THEN
      ASM_SIMP_TAC[REAL_FIELD `&0 < R ==> --(r / (&2 * R)) = (--r) / (&2 * R)`;
                   REAL_LT_RDIV_EQ; REAL_ARITH `&0 < R ==> &0 < &2 * R`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN SUBGOAL_THEN `r * (r + &2 * R * cos t) < &0` MP_TAC THENL
     [ONCE_REWRITE_TAC[REAL_ARITH `x < &0 <=> &0 < --x`] THEN
      REWRITE_TAC[REAL_ARITH `--(r * x) = r * --x`] THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN
      MP_TAC(REAL_RING `r * (r + &2 * R * cos t) =
                        (R pow 2 + r pow 2 + &2 * R * r * cos t) - R pow 2`) THEN
      REAL_ARITH_TAC]]);;

let WAN_ARC_OSC_BOUND = prove
 (`!(v:real^1->real^K) y g t1 t2.
     t1 <= t2 /\ (v has_integral y) (interval[lift t1,lift t2]) /\
     (\s. lift(g s)) integrable_on interval[lift t1,lift t2] /\
     (!s. s IN interval[lift t1,lift t2] ==> norm(v s) pow 2 <= g s)
     ==> norm y pow 2 <= (t2 - t1) * drop(integral (interval[lift t1,lift t2]) (\s. lift(g s)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(v:real^1->real^K) integrable_on interval[lift t1,lift t2]` ASSUME_TAC THENL
   [REWRITE_TAC[integrable_on] THEN EXISTS_TAC `y:real^K` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(v:real^1->real^K) IN lspace (interval[lift t1,lift t2]) (&2) /\
    (\s. lift(norm((v:real^1->real^K) s))) IN lspace (interval[lift t1,lift t2]) (&2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC WAN_L2_BOUND_LSPACE THEN EXISTS_TAC `g:real^1->real` THEN
    ASM_SIMP_TAC[INTEGRABLE_IMP_MEASURABLE; MEASURABLE_ON_NORM; NORM_LIFT; REAL_ABS_NORM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^1->real^K) absolutely_integrable_on interval[lift t1,lift t2]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_LSPACE2_ABS_INT_MEAS THEN ASM_REWRITE_TAC[MEASURABLE_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `y = integral (interval[lift t1,lift t2]) (v:real^1->real^K)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (interval[lift t1,lift t2])
                 (\s. lift(norm((v:real^1->real^K) s)))) pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN REWRITE_TAC[LIFT_DROP; REAL_LE_REFL] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(v:real^1->real^K) absolutely_integrable_on interval[lift t1,lift t2]` THEN
    SIMP_TAC[absolutely_integrable_on];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`interval[lift t1,lift t2]`; `\s. lift(norm((v:real^1->real^K) s))`]
                WAN_INTEGRAL_SQ_CS) THEN
  ASM_REWRITE_TAC[MEASURABLE_INTERVAL; MEASURE_INTERVAL_1; LIFT_DROP; NORM_LIFT;
                  REAL_ABS_NORM; NORM_1; REAL_POW2_ABS] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_SUB_LE] THEN
  MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_SIMP_TAC[LIFT_DROP] THEN
  MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_REWRITE_TAC[]);;

let WAN_SPHERE_ANGLE = prove
 (`!(a:real^2) R x0. x0 IN sphere(a,R) ==> ?th0. a = wan_circ x0 R th0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a:real^2) IN sphere(x0,R)` MP_TAC THENL
   [UNDISCH_TAC `(x0:real^2) IN sphere(a,R)` THEN REWRITE_TAC[IN_SPHERE] THEN
    MESON_TAC[DIST_SYM];
    DISCH_THEN(MP_TAC o MATCH_MP WAN_SPHERE_CIRC) THEN MESON_TAC[]]);;

let WAN_BDRY_ARC_INSIDE = prove
 (`!(x0:real^2) R R0 th0 r t1 t2.
     &0 < R /\ &0 < r /\ r < R0 /\ &0 <= t1 /\ t1 <= t2 /\ t2 <= &2 * pi /\
     cos t1 < --(r / (&2 * R)) /\ cos t2 < --(r / (&2 * R))
     ==> !t. t1 <= t /\ t <= t2
             ==> wan_circ x0 r ((th0 - pi) + t) IN
                 ball(wan_circ x0 R th0,R) INTER ball(x0,R0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[WAN_CIRC_BDRY_BALL] THEN MATCH_MP_TAC WAN_COS_ARC THEN
    MAP_EVERY EXISTS_TAC [`t1:real`; `t2:real`] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_BALL; dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
    REWRITE_TAC[WAN_CIRC_NORM] THEN ASM_REAL_ARITH_TAC]);;

let WAN_BDRY_ARC_PARAM = prove
 (`!(x0:real^2) R R0 th0 r y z.
     &0 < R /\ &0 < r /\ r < R0 /\
     y IN ball(wan_circ x0 R th0,R) INTER sphere(x0,r) /\
     z IN ball(wan_circ x0 R th0,R) INTER sphere(x0,r)
     ==> ?t1 t2. &0 <= t1 /\ t1 <= t2 /\ t2 <= &2 * pi /\ t2 - t1 < pi /\
                 (!t. t1 <= t /\ t <= t2
                      ==> wan_circ x0 r ((th0 - pi) + t) IN
                          ball(wan_circ x0 R th0,R) INTER ball(x0,R0)) /\
                 ((y = wan_circ x0 r ((th0 - pi) + t1) /\ z = wan_circ x0 r ((th0 - pi) + t2)) \/
                  (z = wan_circ x0 r ((th0 - pi) + t1) /\ y = wan_circ x0 r ((th0 - pi) + t2)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[IN_INTER]) THEN
  SUBGOAL_THEN
   `!w. w IN ball(wan_circ x0 R th0,R) /\ w IN sphere(x0:real^2,r)
        ==> ?t. &0 <= t /\ t <= &2 * pi /\ w = wan_circ x0 r ((th0 - pi) + t) /\
                cos t < --(r / (&2 * R))`
  (LABEL_TAC "w") THENL
   [X_GEN_TAC `w:real^2` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP WAN_SPHERE_CIRC) THEN
    DISCH_THEN(X_CHOOSE_THEN `t0:real` (SUBST_ALL_TAC o SYM)) THEN
    MP_TAC(SPECL [`x0:real^2`; `r:real`; `th0 - pi`; `t0:real`] WAN_CIRC_OFFSET_REP) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`x0:real^2`; `R:real`; `r:real`; `th0:real`; `s:real`] WAN_CIRC_BDRY_BALL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      can (find_term ((=) `s:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "w" (MP_TAC o SPEC `y:real^2`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ty:real` STRIP_ASSUME_TAC) THEN
  USE_THEN "w" (MP_TAC o SPEC `z:real^2`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tz:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < r / (&2 * R)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `ty:real` WAN_COS_NEG_RANGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPEC `tz:real` WAN_COS_NEG_RANGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ASM_CASES_TAC `ty <= tz` THENL
   [MAP_EVERY EXISTS_TAC [`ty:real`; `tz:real`] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC WAN_BDRY_ARC_INSIDE THEN ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`tz:real`; `ty:real`] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC WAN_BDRY_ARC_INSIDE THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The Courant-Lebesgue lemma at a boundary point of a disc.                 *)
(* ------------------------------------------------------------------------- *)

let WAN_COURANT_LEBESGUE_BDRY = prove
 (`!(kk:K->bool). WAN_COURANT_LEBESGUE_BDRY_STATEMENT kk`,
  GEN_TAC THEN REWRITE_TAC[WAN_COURANT_LEBESGUE_BDRY_STATEMENT] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `th0:real` o MATCH_MP WAN_SPHERE_ANGLE) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    is_var(lhs(concl th)) && fst(dest_var(lhs(concl th))) = "a")) THEN
  ABBREV_TAC `D = ball(wan_circ x0 R th0,R) INTER ball(x0:real^2,R0)` THEN
  SUBGOAL_THEN `open(D:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN SIMP_TAC[OPEN_INTER; OPEN_BALL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`D:real^2->bool`; `u:real^2->real^K`; `x0:real^2`; `th0 - pi`] WAN_ARC_ACL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^1->bool` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "S"))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WAN_SQRT_FACTS o CONJ (ASSUME `&0 < d`)) THEN
  SUBGOAL_THEN `&0 <= E` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`D:real^2->bool`; `u:real^2->real^K`] WAN_DIR_POS) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < d * R0 /\ d * R0 < sqrt d * R0 /\ sqrt d * R0 < R0` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_RMUL_EQ] THEN
    GEN_REWRITE_TAC (RAND_CONV) [GSYM REAL_MUL_LID] THEN
    ASM_SIMP_TAC[REAL_LT_RMUL_EQ];
    ALL_TAC] THEN
  ABBREV_TAC
   `G = \x. lift(norm(wan_wd D 1 (u:real^2->real^K) x) pow 2 + norm(wan_wd D 2 u x) pow 2)` THEN
  ABBREV_TAC `G' = \x. if x IN D then (G:real^2->real^1) x else vec 0` THEN
  SUBGOAL_THEN `(G:real^2->real^1) absolutely_integrable_on D` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN MATCH_MP_TAC WAN_DIR_DENSITY_ABS_INT THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(G':real^2->real^1) absolutely_integrable_on (:real^2) /\
                integral (:real^2) G' = integral (D:real^2->bool) (G:real^2->real^1) /\
                (!x. &0 <= drop(G' x))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "G'" THEN
    ASM_REWRITE_TAC[ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV; INTEGRAL_RESTRICT_UNIV] THEN
    GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[DROP_VEC; REAL_LE_REFL] THEN
    EXPAND_TAC "G" THEN REWRITE_TAC[LIFT_DROP] THEN
    SIMP_TAC[REAL_LE_ADD; REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(G':real^2->real^1) absolutely_integrable_on
    {x | d * R0 < norm(x - x0) /\ norm(x - x0) < sqrt d * R0}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[SUBSET_UNIV; WAN_ANNULUS_EQ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G':real^2->real^1`; `x0:real^2`; `th0 - pi`; `d * R0`; `sqrt d * R0`]
                WAN_POLAR_ANNULUS) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `N:real^1->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "N"))) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `drop(integral (interval[lift(d * R0),lift(sqrt d * R0)])
           (\r. drop r % integral (interval[vec 0,lift(&2 * pi)])
                           (\t. (G':real^2->real^1)
                                  (wan_circ x0 (drop r) ((th0 - pi) + drop t))))) <= &2 * E`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `drop(integral (:real^2) (G':real^2->real^1))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
      ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; SUBSET_UNIV];
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "G" THEN ASM_SIMP_TAC[GSYM WAN_DIR_2D_EQ]];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(LABEL_TAC "neg" o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  ABBREV_TAC `c = &4 * E / log(inv d)` THEN
  MP_TAC(ISPECL [`c:real`; `d * R0`; `sqrt d * R0`] WAN_INTEGRAL_INV) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; WAN_LOG_SQRT_RATIO] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`\r. drop r % integral (interval[vec 0,lift(&2 * pi)])
                    (\t. (G':real^2->real^1)(wan_circ x0 (drop r) ((th0 - pi) + drop t)))`;
    `\r:real^1. lift(c * inv(drop r))`; `lift(d * R0)`; `lift(sqrt d * R0)`;
    `lift(d * R0) INSERT lift(sqrt d * R0) INSERT ((S:real^1->bool) UNION N)`]
   WAN_INTEGRAL_STRICT_AE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LIFT_DROP; NEGLIGIBLE_INSERT; NEGLIGIBLE_UNION_EQ] THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
      ASM_MESON_TAC[integrable_on];
      ALL_TAC] THEN
    X_GEN_TAC `x:real^1` THEN
    REWRITE_TAC[IN_DIFF; IN_INSERT; IN_UNION; IN_INTERVAL_1; LIFT_DROP; DE_MORGAN_THM;
                GSYM DROP_EQ] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `d * R0 < drop x /\ drop x < sqrt d * R0 /\ &0 < drop x`
    STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REMOVE_THEN "neg" (MP_TAC o SPEC `drop x`) THEN
    ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; REAL_NOT_LE] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^2` (X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`x0:real^2`; `R:real`; `R0:real`; `th0:real`; `drop x`;
                   `y:real^2`; `z:real^2`] WAN_BDRY_ARC_PARAM) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:real` (X_CHOOSE_THEN `t2:real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))))) THEN
    SUBGOAL_THEN
     `norm((u:real^2->real^K) y - u z) =
      norm(u(wan_circ x0 (drop x) ((th0 - pi) + t2)) - u(wan_circ x0 (drop x) ((th0 - pi) + t1)))`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC NORM_ARITH;
      ALL_TAC] THEN
    USE_THEN "S" (MP_TAC o SPECL [`drop x`; `t1:real`; `t2:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN STRIP_TAC THEN
    USE_THEN "N" (MP_TAC o SPEC `drop x`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[LIFT_DROP]; DISCH_TAC] THEN
    ABBREV_TAC
     `J = drop(integral (interval[vec 0,lift(&2 * pi)])
                (\t. (G':real^2->real^1)(wan_circ x0 (drop x) ((th0 - pi) + drop t))))` THEN
    REWRITE_TAC[DROP_CMUL; LIFT_DROP] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL
     [`\s. drop x % (--(sin((th0 - pi) + drop s)) %
                     wan_wd D 1 (u:real^2->real^K) (wan_circ x0 (drop x) ((th0 - pi) + drop s)) +
                     cos((th0 - pi) + drop s) %
                     wan_wd D 2 u (wan_circ x0 (drop x) ((th0 - pi) + drop s)))`;
      `(u:real^2->real^K)(wan_circ x0 (drop x) ((th0 - pi) + t2)) -
       u(wan_circ x0 (drop x) ((th0 - pi) + t1))`;
      `\s. drop x pow 2 *
           (norm(wan_wd D 1 (u:real^2->real^K) (wan_circ x0 (drop x) ((th0 - pi) + drop s))) pow 2 +
            norm(wan_wd D 2 u (wan_circ x0 (drop x) ((th0 - pi) + drop s))) pow 2)`;
      `t1:real`; `t2:real`] WAN_ARC_OSC_BOUND) THEN
    SUBGOAL_THEN `!y. lift(drop x pow 2 * y) = drop x pow 2 % lift y` ASSUME_TAC THENL
     [REWRITE_TAC[LIFT_CMUL]; ALL_TAC] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
        REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_MUL; REAL_POW_MUL; REAL_POW2_ABS] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2; WAN_TRIG_COMB_SQ]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL] THEN
    ABBREV_TAC
     `I12 = drop(integral (interval[lift t1,lift t2])
                 (\s. lift(norm(wan_wd D 1 (u:real^2->real^K)
                                  (wan_circ x0 (drop x) ((th0 - pi) + drop s))) pow 2 +
                           norm(wan_wd D 2 u (wan_circ x0 (drop x) ((th0 - pi) + drop s))) pow 2)))` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= I12 /\ I12 <= J` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [EXPAND_TAC "I12" THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
        SIMP_TAC[REAL_LE_ADD; REAL_LE_POW_2];
        ALL_TAC] THEN
      EXPAND_TAC "I12" THEN EXPAND_TAC "J" THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `drop(integral (interval[lift t1,lift t2])
                    (\t. (G':real^2->real^1)(wan_circ x0 (drop x) ((th0 - pi) + drop t))))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN
        X_GEN_TAC `s:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN STRIP_TAC THEN
        EXPAND_TAC "G'" THEN
        SUBGOAL_THEN `wan_circ x0 (drop x) ((th0 - pi) + drop s) IN (D:real^2->bool)`
        (fun th -> REWRITE_TAC[th]) THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          EXPAND_TAC "G" THEN REWRITE_TAC[]];
        MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
        REPEAT CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
          EXISTS_TAC `interval[vec 0:real^1,lift(&2 * pi)]` THEN
          ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
          REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN ASM_REAL_ARITH_TAC;
          ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE]]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&4 * pi * E / log(inv d) = pi * c` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [EXPAND_TAC "c" THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= pi * c` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MP_TAC PI_POS THEN REAL_ARITH_TAC;
        EXPAND_TAC "c" THEN MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      ALL_TAC] THEN
    SUBGOAL_THEN `pi * c < (t2 - t1) * drop x pow 2 * J` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC `norm((u:real^2->real^K) y - u z) pow 2` THEN CONJ_TAC THENL
       [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM(MATCH_MP SQRT_POW_2 th)]) THEN
        MATCH_MP_TAC REAL_POW_LT2 THEN ASM_SIMP_TAC[SQRT_POS_LE; ARITH];
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `(t2 - t1) * drop x pow 2 * I12` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < drop x pow 2 * J` ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      SUBGOAL_THEN `(t2 - t1) * drop x pow 2 * J <= &0` MP_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= a * --b ==> a * b <= &0`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `c < drop x pow 2 * J` MP_TAC THENL
     [SUBGOAL_THEN `pi * c < pi * (drop x pow 2 * J)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `(t2 - t1) * drop x pow 2 * J` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        SIMP_TAC[REAL_LT_LMUL_EQ; PI_POS]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ] THEN
    SUBGOAL_THEN `(drop x * J) * drop x = drop x pow 2 * J` SUBST1_TAC THENL
     [CONV_TAC REAL_RING; REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral (interval[lift(d * R0),lift(sqrt d * R0)]) (\r:real^1. lift(c * inv(drop r))) =
    lift(c * log(inv d) / &2)`
  SUBST1_TAC THENL [MATCH_MP_TAC INTEGRAL_UNIQUE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LIFT_DROP] THEN
  SUBGOAL_THEN `c * log(inv d) / &2 = &2 * E` SUBST1_TAC THENL
   [EXPAND_TAC "c" THEN UNDISCH_TAC `&0 < log(inv d)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

