(* ========================================================================= *)
(* The variable-radius mollification of Schoen-Uhlenbeck (J. Differential    *)
(* Geom. 17 (1982), Lemma 3.3), part of pc_hm_reg_min:                       *)
(*   hmrm_vr h u x = int phi(y) u(x - h(x) y) dy                             *)
(* with phi = wan_mk, equal to u where h = 0 and to wan_moll (h x) u where   *)
(* h > 0.  Proved: smoothness for smooth u (parameter integrals), a          *)
(* variable-radius Young inequality (Tonelli in kernel form, no nonlinear    *)
(* change of variables), and the W^{1,2} membership with energy bounds on    *)
(* annuli for W^{1,2} maps (smooth approximation and WAN_DIR_LSC).           *)
(* ========================================================================= *)

needs "src/pc_wan_sob2b.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Definitions and the basic identities.                                     *)
(* ========================================================================= *)

let hmrm_vr = new_definition
 `hmrm_vr (h:real^2->real) (u:real^2->real^K) (x:real^2) =
    integral (:real^2) (\y. wan_mk y % u(x - h x % y))`;;

let HMRM_IMAGE_AFFINE_UNIV = prove
 (`!m (c:real^N). ~(m = &0) ==> IMAGE (\y. m % y + c) (:real^N) = (:real^N)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN
  X_GEN_TAC `z:real^N` THEN EXISTS_TAC `inv m % (z - c:real^N)` THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; VECTOR_MUL_LID] THEN
  VECTOR_ARITH_TAC);;

let HMRM_VR_ZERO = prove
 (`!(h:real^2->real) (u:real^2->real^K) x. h x = &0 ==> hmrm_vr h u x = u x`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[hmrm_vr; VECTOR_MUL_LZERO; VECTOR_SUB_RZERO] THEN
  MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MP_TAC(ISPECL [`\y:real^2. lift(wan_mk y)`; `lift(&1)`; `(:real^2)`;
                 `\z:real^1. drop z % (u:real^2->real^K) x`] HAS_INTEGRAL_LINEAR) THEN
  REWRITE_TAC[o_DEF; LIFT_DROP; VECTOR_MUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[WAN_MK_PROPS; linear; DROP_ADD; DROP_CMUL] THEN
  REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC);;

let HMRM_VR_MOLL = prove
 (`!(h:real^2->real) (u:real^2->real^K) x.
     &0 < h x /\ wan_lloc (:real^2) u ==> hmrm_vr h u x = wan_moll (h x) u x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hmrm_vr; WAN_MOLL_EQ] THEN
  ABBREV_TAC `e = (h:real^2->real) x` THEN
  MP_TAC(ISPECL [`wan_mke e:real^2->real`; `u:real^2->real^K`; `x:real^2`]
                WAN_KCONV_INTEGRABLE) THEN
  ASM_SIMP_TAC[WAN_MKE_TEST] THEN
  DISCH_THEN(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE) THEN
  REWRITE_TAC[HAS_INTEGRAL_INTEGRAL] THEN
  DISCH_THEN(MP_TAC o SPECL [`--e:real`; `x:real^2`] o
    MATCH_MP (REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_AFFINITY)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(inv(--e) = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_INV_EQ_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[HMRM_IMAGE_AFFINE_UNIV; DIMINDEX_2] THEN
  SUBGOAL_THEN
   `!y:real^2. wan_mke e (x - (--e % y + x)) % (u:real^2->real^K)(--e % y + x) =
               inv(e) pow 2 % (wan_mk y % u(x - e % y))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[wan_mke; DIMINDEX_2; VECTOR_MUL_ASSOC] THEN
    REWRITE_TAC[VECTOR_ARITH `x - (--e % y + x):real^2 = e % y`;
                VECTOR_ARITH `--e % y + x:real^2 = x - e % y`] THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `e pow 2` o MATCH_MP HAS_INTEGRAL_CMUL) THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC; REAL_MUL_ASSOC] THEN
  SUBGOAL_THEN `e pow 2 * inv(e) pow 2 = &1 /\ e pow 2 * inv(abs(--e) pow 2) = &1`
  (fun th -> REWRITE_TAC[th; VECTOR_MUL_LID; REAL_MUL_LID]) THENL
   [REWRITE_TAC[REAL_ABS_NEG; GSYM REAL_POW_INV; GSYM REAL_POW_MUL] THEN
    ASM_SIMP_TAC[real_abs; REAL_LT_IMP_LE; REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_POW_ONE];
    ALL_TAC] THEN
  DISCH_THEN(ACCEPT_TAC o MATCH_MP INTEGRAL_UNIQUE));;

(* ========================================================================= *)
(* The mollification of a smooth map is smooth (parameter integral over the  *)
(* box containing the support of the bump), with the pointwise derivative    *)
(* bound                                                                     *)
(*   |d_i hmrm_vr h w (x)|^2 <= 9/2 int phi(y) |Dw|^2(x - h(x) y) dy       *)
(* when |d_j h| <= 1/2.                                                      *)
(* ========================================================================= *)

let hmrm_ka = new_definition
 `hmrm_ka (h:real^2->real) (g:real^2->real) (x:real^2) =
    drop(integral (:real^2) (\y. lift(wan_mk y * g(x - h x % y))))`;;

let HMRM_MK_BOX = prove
 (`!y:real^2. ~(y IN interval[--vec 1,vec 1]) ==> wan_mk y = &0`,
  GEN_TAC THEN REWRITE_TAC[IN_INTERVAL; NOT_FORALL_THM; NOT_IMP] THEN
  REWRITE_TAC[VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2 WAN_MK_PROPS))) THEN
  MP_TAC(ISPECL [`y:real^2`; `i:num`] COMPONENT_LE_NORM) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let HMRM_INTEGRAL_BOX = prove
 (`!(f:real^2->real^N).
     (!y. ~(y IN interval[--vec 1,vec 1]) ==> f y = vec 0)
     ==> integral (:real^2) f = integral (interval[--vec 1,vec 1]) f`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM INTEGRAL_RESTRICT_UNIV] THEN
  MATCH_MP_TAC INTEGRAL_EQ THEN REWRITE_TAC[IN_UNIV] THEN GEN_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[]);;

let HMRM_VR_BOX = prove
 (`!(h:real^2->real) (u:real^2->real^K) x.
     hmrm_vr h u x =
     integral (interval[--vec 1,vec 1]) (\y. wan_mk y % u(x - h x % y))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hmrm_vr] THEN MATCH_MP_TAC HMRM_INTEGRAL_BOX THEN
  SIMP_TAC[HMRM_MK_BOX; VECTOR_MUL_LZERO]);;

let HMRM_SM_COMPOSE_UNIV = prove
 (`!(f:real^M->real^N) (g:real^N->real^P).
     smooth_map_on (:real^M) f /\ smooth_map_on (:real^N) g
     ==> smooth_map_on (:real^M) (\x. g(f x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^M)`; `(:real^N)`; `f:real^M->real^N`; `g:real^N->real^P`]
                SMOOTH_MAP_ON_COMPOSE_OPEN) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; o_DEF]);;

let HMRM_SM_CART = prove
 (`smooth_map_on (:real^(M,N)finite_sum) (fstcart:real^(M,N)finite_sum->real^M) /\
   smooth_map_on (:real^(M,N)finite_sum) (sndcart:real^(M,N)finite_sum->real^N)`,
  MP_TAC(ISPECL [`(:real^(M,N)finite_sum)`; `\x:real^(M,N)finite_sum. x`]
                SMOOTH_MAP_ON_FSTCART_OPEN) THEN
  MP_TAC(ISPECL [`(:real^(M,N)finite_sum)`; `\x:real^(M,N)finite_sum. x`]
                SMOOTH_MAP_ON_SNDCART_OPEN) THEN
  REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; o_DEF; ETA_AX] THEN SIMP_TAC[]);;

let HMRM_VR_INTEGRAND_SMOOTH = prove
 (`!(h:real^2->real) (w:real^2->real^K).
     smooth_map_on (:real^2) (\x. lift(h x)) /\ smooth_map_on (:real^2) w
     ==> smooth_map_on (:real^(2,2)finite_sum)
           (\p. wan_mk(sndcart p) % w(fstcart p - h(fstcart p) % sndcart p))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^(2,2)finite_sum)`;
                 `\p:real^(2,2)finite_sum. lift(wan_mk(sndcart p))`;
                 `\p:real^(2,2)finite_sum.
                    (w:real^2->real^K)(fstcart p - h(fstcart p) % sndcart p)`]
                SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
  REWRITE_TAC[LIFT_DROP; OPEN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`sndcart:real^(2,2)finite_sum->real^2`; `\y:real^2. lift(wan_mk y)`]
                  HMRM_SM_COMPOSE_UNIV) THEN
    REWRITE_TAC[HMRM_SM_CART; WAN_MK_PROPS];
    MP_TAC(ISPECL [`\p:real^(2,2)finite_sum. fstcart p - h(fstcart p:real^2) % sndcart p`;
                   `w:real^2->real^K`] HMRM_SM_COMPOSE_UNIV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN REWRITE_TAC[OPEN_UNIV; HMRM_SM_CART; ETA_AX] THEN
    MP_TAC(ISPECL [`(:real^(2,2)finite_sum)`;
                   `\p:real^(2,2)finite_sum. lift(h(fstcart p:real^2))`;
                   `sndcart:real^(2,2)finite_sum->real^2`]
                  SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
    REWRITE_TAC[LIFT_DROP; OPEN_UNIV; HMRM_SM_CART] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`fstcart:real^(2,2)finite_sum->real^2`; `\x:real^2. lift(h x)`]
                  HMRM_SM_COMPOSE_UNIV) THEN
    ASM_REWRITE_TAC[HMRM_SM_CART]]);;

let HMRM_VR_SMOOTH = prove
 (`!(h:real^2->real) (w:real^2->real^K).
     smooth_map_on (:real^2) (\x. lift(h x)) /\ smooth_map_on (:real^2) w
     ==> smooth_map_on (:real^2) (hmrm_vr h w) /\
         !x i. partial_derivative i (hmrm_vr h w) x =
               integral (interval[--vec 1,vec 1])
                 (\y. partial_derivative i (\x. wan_mk y % w(x - h x % y)) x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `hmrm_vr (h:real^2->real) (w:real^2->real^K) =
    (\x. integral (interval[--vec 1,vec 1])
           (\y. (\p:real^(2,2)finite_sum.
                   wan_mk(sndcart p) % w(fstcart p - h(fstcart p) % sndcart p))
                (pastecart x y)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; HMRM_VR_BOX; FSTCART_PASTECART; SNDCART_PASTECART];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^2)`; `(:real^(2,2)finite_sum)`; `--vec 1:real^2`; `vec 1:real^2`;
                 `\p:real^(2,2)finite_sum.
                    wan_mk(sndcart p) % (w:real^2->real^K)(fstcart p - h(fstcart p) % sndcart p)`]
                NS_PARAM_INTEGRAL_SMOOTH) THEN
  ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; HMRM_VR_INTEGRAND_SMOOTH] THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART]);;

(* ========================================================================= *)
(* The derivative of the mollification of a smooth map and its pointwise     *)
(* bound by the variable-radius average of the energy density.               *)
(* ========================================================================= *)

let HMRM_SHIFT_SMOOTH = prove
 (`!(h:real^2->real) (y:real^2).
     smooth_map_on (:real^2) (\x. lift(h x)) ==> smooth_map_on (:real^2) (\x. x - h x % y)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
  REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID] THEN
  MP_TAC(ISPECL [`(:real^2)`; `\x:real^2. lift(h x)`; `\x:real^2. y:real^2`]
                SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
  ASM_REWRITE_TAC[LIFT_DROP; OPEN_UNIV; SMOOTH_MAP_ON_CONST]);;

let HMRM_FD2_EXPAND = prove
 (`!(w:real^2->real^K) p v.
     w differentiable (at p)
     ==> frechet_derivative w (at p) v =
         v$1 % partial_derivative 1 w p + v$2 % partial_derivative 2 w p`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
  REWRITE_TAC[DIMINDEX_2; VSUM_2; partial_derivative] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
  ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL]);;

let HMRM_FD2_BOUND = prove
 (`!(w:real^2->real^K) p v.
     w differentiable (at p)
     ==> norm(frechet_derivative w (at p) v) <=
         norm v * (norm(partial_derivative 1 w p) + norm(partial_derivative 2 w p))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[HMRM_FD2_EXPAND] THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(a:real^K) <= x /\ norm(b:real^K) <= y ==> norm(a + b) <= x + y`) THEN
  REWRITE_TAC[NORM_MUL] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  REWRITE_TAC[NORM_POS_LE; COMPONENT_LE_NORM]);;

let HMRM_PARTIAL_INTEGRAND = prove
 (`!(h:real^2->real) (w:real^2->real^K) y x i.
     smooth_map_on (:real^2) (\x. lift(h x)) /\ smooth_map_on (:real^2) w
     ==> partial_derivative i (\x. wan_mk y % w(x - h x % y)) x =
         wan_mk y % frechet_derivative w (at (x - h x % y))
                      (basis i - drop(partial_derivative i (\x. lift(h x)) x) % y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!z. (w:real^2->real^K) differentiable (at z)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x:real^2. lift(h x)) differentiable (at x)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x:real^2. x - h x % y) differentiable (at x)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(:real^2)` THEN ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; HMRM_SHIFT_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x:real^2. (w:real^2->real^K)(x - h x % y)) = w o (\x. x - h x % y)`
  ASSUME_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) PARTIAL_DERIVATIVE_CMUL o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN ASM_REWRITE_TAC[] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) PARTIAL_DERIVATIVE_CHAIN o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  W(MP_TAC o PART_MATCH (lhs o rand) PARTIAL_DERIVATIVE_SUB o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIFFERENTIABLE_ID] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    MP_TAC(ISPECL [`(:real^2)`; `\x:real^2. lift(h x)`; `\x:real^2. y:real^2`]
                  SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
    ASM_REWRITE_TAC[LIFT_DROP; OPEN_UNIV; SMOOTH_MAP_ON_CONST];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[PARTIAL_DERIVATIVE_ID] THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`i:num`; `\x:real^2. lift(h x)`; `\x:real^2. y:real^2`; `x:real^2`]
                PARTIAL_DERIVATIVE_MUL) THEN
  ASM_REWRITE_TAC[LIFT_DROP; DIFFERENTIABLE_CONST; PARTIAL_DERIVATIVE_CONST] THEN
  DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC);;

(* Continuity in y of the integrands (for integrability over the box).      *)

let HMRM_CONT_SHIFT = prove
 (`!(f:real^2->real^N) (x:real^2) t.
     f continuous_on (:real^2) ==> (\y. f(x - t % y)) continuous_on (:real^2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\y:real^2. (f:real^2->real^N)(x - t % y)) = f o (\y. x - t % y)`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; CONTINUOUS_ON_CMUL;
               CONTINUOUS_ON_ID] THEN
  ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]);;

let HMRM_SMOOTH_CONT = prove
 (`!(f:real^M->real^N). smooth_map_on (:real^M) f ==> f continuous_on (:real^M)`,
  MESON_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]);;

let HMRM_PARTIAL_INTEGRAND_CONT = prove
 (`!(h:real^2->real) (w:real^2->real^K) x i.
     smooth_map_on (:real^2) (\x. lift(h x)) /\ smooth_map_on (:real^2) w
     ==> (\y. partial_derivative i (\x. wan_mk y % w(x - h x % y)) x)
         continuous_on (:real^2)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[HMRM_PARTIAL_INTEGRAND] THEN
  SUBGOAL_THEN `!z. (w:real^2->real^K) differentiable (at z)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  ASM_SIMP_TAC[HMRM_FD2_EXPAND] THEN
  ABBREV_TAC `c = drop(partial_derivative i (\x. lift((h:real^2->real) x)) x)` THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
   [REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC HMRM_SMOOTH_CONT THEN REWRITE_TAC[WAN_MK_PROPS];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
   [REWRITE_TAC[o_DEF; VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; LIFT_SUB; LIFT_CMUL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT THEN REWRITE_TAC[DIMINDEX_2] THEN ARITH_TAC;
    MATCH_MP_TAC HMRM_CONT_SHIFT THEN MATCH_MP_TAC HMRM_SMOOTH_CONT THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN ASM_REWRITE_TAC[OPEN_UNIV];
    REWRITE_TAC[o_DEF; VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; LIFT_SUB; LIFT_CMUL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT THEN REWRITE_TAC[DIMINDEX_2] THEN ARITH_TAC;
    MATCH_MP_TAC HMRM_CONT_SHIFT THEN MATCH_MP_TAC HMRM_SMOOTH_CONT THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN ASM_REWRITE_TAC[OPEN_UNIV]]);;

(* Integrals over the box of continuous functions vanishing off the box.    *)

let HMRM_INTEGRABLE_BOX = prove
 (`!(f:real^2->real^N).
     f continuous_on (:real^2) /\
     (!y. ~(y IN interval[--vec 1,vec 1]) ==> f y = vec 0)
     ==> f integrable_on (:real^2) /\ f integrable_on interval[--vec 1,vec 1] /\
         integral (:real^2) f = integral (interval[--vec 1,vec 1]) f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(f:real^2->real^N) integrable_on interval[--vec 1,vec 1]` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    ALL_TAC] THEN
  ASM_SIMP_TAC[HMRM_INTEGRAL_BOX] THEN
  ONCE_REWRITE_TAC[GSYM INTEGRABLE_RESTRICT_UNIV] THEN
  FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[GSYM INTEGRABLE_RESTRICT_UNIV]) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; IN_UNIV] THEN GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[]);;

let HMRM_CONT_POW2 = prove
 (`!(g:real^N->real) s.
     (\z. lift(g z)) continuous_on s ==> (\z. lift(g z pow 2)) continuous_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_POW_2; LIFT_CMUL] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN ASM_REWRITE_TAC[o_DEF]);;

let HMRM_SQ_SUM_LE = prove
 (`!a b. (a + b) pow 2 <= &2 * (a pow 2 + b pow 2)`,
  REPEAT GEN_TAC THEN MP_TAC(SPEC `a - b:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC);;

let HMRM_VR_PARTIAL_BOUND = prove
 (`!(h:real^2->real) (w:real^2->real^K).
     smooth_map_on (:real^2) (\x. lift(h x)) /\ smooth_map_on (:real^2) w /\
     (!x i. 1 <= i /\ i <= 2
            ==> abs(drop(partial_derivative i (\x. lift(h x)) x)) <= &1 / &2)
     ==> !x i. 1 <= i /\ i <= 2
               ==> norm(partial_derivative i (hmrm_vr h w) x) pow 2 <=
                   &9 / &2 *
                   hmrm_ka h (\z. norm(partial_derivative 1 w z) pow 2 +
                                  norm(partial_derivative 2 w z) pow 2) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real^2` THEN X_GEN_TAC `i:num` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!z. (w:real^2->real^K) differentiable (at z)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. (\z. partial_derivative j (w:real^2->real^K) z) continuous_on (:real^2)`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC HMRM_SMOOTH_CONT THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN ASM_REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  ABBREV_TAC
   `g1 = \z. norm(partial_derivative 1 (w:real^2->real^K) z) +
             norm(partial_derivative 2 w z)` THEN
  SUBGOAL_THEN `!z. &0 <= (g1:real^2->real) z` ASSUME_TAC THENL
   [EXPAND_TAC "g1" THEN SIMP_TAC[REAL_LE_ADD; NORM_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `(\z. lift((g1:real^2->real) z)) continuous_on (:real^2)` ASSUME_TAC THENL
   [EXPAND_TAC "g1" THEN REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
    CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `t = (h:real^2->real) x` THEN
  ABBREV_TAC `c = drop(partial_derivative i (\x. lift((h:real^2->real) x)) x)` THEN
  SUBGOAL_THEN `abs c <= &1 / &2` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  (* the pointwise bound of the integrand *)
  SUBGOAL_THEN
   `!y. norm(partial_derivative i (\x. wan_mk y % (w:real^2->real^K)(x - h x % y)) x) <=
        wan_mk y * (&3 / &2 * (g1:real^2->real)(x - t % y))`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^2` THEN ASM_SIMP_TAC[HMRM_PARTIAL_INTEGRAND] THEN
    REWRITE_TAC[NORM_MUL] THEN
    SUBGOAL_THEN `abs(wan_mk(y:real^2)) = wan_mk y` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_ABS_REFL; WAN_MK_PROPS]; ALL_TAC] THEN
    ASM_CASES_TAC `&1 <= norm(y:real^2)` THENL
     [ASM_SIMP_TAC[WAN_MK_PROPS; REAL_MUL_LZERO; REAL_LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[WAN_MK_PROPS] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(basis i - c % y:real^2) * (g1:real^2->real)(x - t % y)` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "g1" THEN ASM_SIMP_TAC[HMRM_FD2_BOUND]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(NORM_ARITH
     `norm(a:real^2) = &1 /\ norm(b:real^2) <= &1 / &2 ==> norm(a - b) <= &3 / &2`) THEN
    ASM_SIMP_TAC[NORM_BASIS; DIMINDEX_2; NORM_MUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs c * &1` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* continuity and integrability of the scalar functions of y *)
  SUBGOAL_THEN
   `!G:real^2->real. (\z. lift(G z)) continuous_on (:real^2)
        ==> (\y. lift(wan_mk y * G(x - t % y))) integrable_on (:real^2) /\
            (\y. lift(wan_mk y * G(x - t % y))) integrable_on interval[--vec 1,vec 1] /\
            integral (:real^2) (\y. lift(wan_mk y * G(x - t % y))) =
            integral (interval[--vec 1,vec 1]) (\y. lift(wan_mk y * G(x - t % y)))`
  (LABEL_TAC "SC") THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC HMRM_INTEGRABLE_BOX THEN
    SIMP_TAC[HMRM_MK_BOX; REAL_MUL_LZERO; LIFT_NUM] THEN
    REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    REWRITE_TAC[o_DEF] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HMRM_SMOOTH_CONT THEN REWRITE_TAC[WAN_MK_PROPS];
      MP_TAC(ISPECL [`\z:real^2. lift((G:real^2->real) z)`; `x:real^2`; `t:real`]
                    HMRM_CONT_SHIFT) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `norm(partial_derivative i (hmrm_vr h (w:real^2->real^K)) x) <=
    drop(integral (:real^2) (\y. lift(wan_mk y * (&3 / &2 * (g1:real^2->real)(x - t % y)))))`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[HMRM_VR_SMOOTH] THEN
    USE_THEN "SC" (MP_TAC o SPEC `\z:real^2. &3 / &2 * (g1:real^2->real) z`) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN ASM_REWRITE_TAC[];
      STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN
    MP_TAC(ISPECL [`\y. partial_derivative i (\x. wan_mk y % (w:real^2->real^K)(x - h x % y)) x`]
                  HMRM_INTEGRABLE_BOX) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[HMRM_PARTIAL_INTEGRAND_CONT] THEN
      ASM_SIMP_TAC[HMRM_PARTIAL_INTEGRAND; HMRM_MK_BOX; VECTOR_MUL_LZERO];
      SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC
   `e2 = \z. norm(partial_derivative 1 (w:real^2->real^K) z) pow 2 +
             norm(partial_derivative 2 w z) pow 2` THEN
  SUBGOAL_THEN `(\z. lift((e2:real^2->real) z)) continuous_on (:real^2)` ASSUME_TAC THENL
   [EXPAND_TAC "e2" THEN REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
    CONJ_TAC THEN MATCH_MP_TAC HMRM_CONT_POW2 THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. lift((&3 / &2 * (g1:real^2->real) z) pow 2)) continuous_on (:real^2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HMRM_CONT_POW2 THEN REWRITE_TAC[LIFT_CMUL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "SC" (MP_TAC o SPEC `\z:real^2. &3 / &2 * (g1:real^2->real) z`) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  USE_THEN "SC" (MP_TAC o SPEC `\z:real^2. (&3 / &2 * (g1:real^2->real) z) pow 2`) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "SC" (MP_TAC o SPEC `e2:real^2->real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`wan_mk:real^2->real`; `\y:real^2. &3 / &2 * (g1:real^2->real)(x - t % y)`]
                WAN_WEIGHTED_CS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[WAN_MK_PROPS] THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[WAN_MK_PROPS; integrable_on];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `drop(integral (:real^2) (\y. lift(wan_mk y))) = &1` SUBST1_TAC THENL
   [MESON_TAC[WAN_MK_PROPS; INTEGRAL_UNIQUE; LIFT_DROP]; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_LID] THEN DISCH_TAC THEN
  REWRITE_TAC[hmrm_ka; ASSUME `(h:real^2->real) x = t`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `drop(integral (:real^2)
           (\y. lift(wan_mk y * (&3 / &2 * (g1:real^2->real)(x - t % y))))) pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `drop(integral (:real^2)
           (\y. lift(wan_mk y * (&3 / &2 * (g1:real^2->real)(x - t % y)) pow 2)))` THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `drop(integral (:real^2)
           (\y. lift(&9 / &2 * (wan_mk y * (e2:real^2->real)(x - t % y)))))` THEN
  SUBGOAL_THEN
   `integral (:real^2) (\y. lift(&9 / &2 * (wan_mk y * (e2:real^2->real)(x - t % y)))) =
    &9 / &2 % integral (:real^2) (\y. lift(wan_mk y * e2(x - t % y)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\y:real^2. lift(wan_mk y * (e2:real^2->real)(x - t % y))`; `&9 / &2`;
                   `(:real^2)`] INTEGRAL_CMUL) THEN
    ASM_REWRITE_TAC[GSYM LIFT_CMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\y. lift(&9 / &2 * (wan_mk y * (e2:real^2->real)(x - t % y)))) integrable_on (:real^2)`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[DROP_CMUL; REAL_LE_REFL]] THEN
  MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
  REWRITE_TAC[LIFT_DROP] THEN
  EXPAND_TAC "g1" THEN EXPAND_TAC "e2" THEN REWRITE_TAC[] THEN
  MP_TAC(ISPEC `y:real^2` (CONJUNCT1(CONJUNCT2 WAN_MK_PROPS))) THEN
  MP_TAC(ISPECL [`norm(partial_derivative 1 (w:real^2->real^K) (x - t % y))`;
                 `norm(partial_derivative 2 (w:real^2->real^K) (x - t % y))`]
                HMRM_SQ_SUM_LE) THEN
  ABBREV_TAC `a = norm(partial_derivative 1 (w:real^2->real^K) (x - t % y))` THEN
  ABBREV_TAC `b = norm(partial_derivative 2 (w:real^2->real^K) (x - t % y))` THEN
  ABBREV_TAC `m = wan_mk(y:real^2)` THEN
  REPEAT DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `m * (&9 / &2 * (a pow 2 + b pow 2))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(a + b) pow 2 <= &2 * (a pow 2 + b pow 2)` THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The scalar average hmrm_ka and the pointwise bound of the variable-radius *)
(* kernel                                                                    *)
(*   K(x,z) = wan_mke (h x) (x - z) <= 9/4 B h(z)^-2 1(|x - z| < 2 h(z))    *)
(* for h >= 0 with Lipschitz constant 1/2 (B the bound of the bump).        *)
(* ========================================================================= *)

let HMRM_KA_VR = prove
 (`!(h:real^2->real) g x. hmrm_ka h g x = drop(hmrm_vr h (\z. lift(g z)) x)`,
  REWRITE_TAC[hmrm_ka; hmrm_vr; LIFT_CMUL]);;

let HMRM_KA_ZERO = prove
 (`!(h:real^2->real) g x. h x = &0 ==> hmrm_ka h g x = g x`,
  SIMP_TAC[HMRM_KA_VR; HMRM_VR_ZERO; LIFT_DROP]);;

let HMRM_KA_MOLL = prove
 (`!(h:real^2->real) g x.
     &0 < h x /\ wan_lloc (:real^2) (\z. lift(g z))
     ==> hmrm_ka h g x =
         drop(integral (:real^2) (\z. lift(wan_mke (h x) (x - z) * g z)))`,
  SIMP_TAC[HMRM_KA_VR; HMRM_VR_MOLL; WAN_MOLL_EQ; LIFT_CMUL]);;

let HMRM_KER_BOUND = prove
 (`!(h:real^2->real) Bm x z.
     (!x y. abs(h x - h y) <= norm(x - y) / &2) /\ &0 <= Bm /\
     (!w:real^2. wan_mk w <= Bm) /\ &0 < h x
     ==> wan_mke (h x) (x - z) <=
         (if &0 < h z /\ dist(x,z) < &2 * h z then &9 / &4 * Bm * inv(h z) pow 2
          else &0)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `h(x:real^2) <= norm(x - z:real^2)` THENL
   [ASM_SIMP_TAC[WAN_MKE_ZERO] THEN COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
  REWRITE_TAC[REAL_NOT_LE] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`x:real^2`; `z:real^2`]) THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < h(z:real^2) /\ dist(x:real^2,z) < &2 * h z /\
                &2 * h z < &3 * h x`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[dist] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[wan_mke; DIMINDEX_2] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(h(x:real^2)) pow 2 * Bm` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a * b * c:real = (a * c) * b`] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `inv(h(x:real^2)) <= &3 / &2 * inv(h z)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `h(x:real^2) * h(z:real^2)` THEN
    ASM_SIMP_TAC[REAL_LT_MUL] THEN
    ASM_SIMP_TAC[REAL_FIELD `&0 < a /\ &0 < b ==> (a * b) * inv a = b`;
                 REAL_FIELD `&0 < a /\ &0 < b ==> (a * b) * (c / d * inv b) = c / d * a`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&9 / &4 * inv(h(z:real^2)) pow 2 = (&3 / &2 * inv(h z)) pow 2`
  SUBST1_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN
  ASM_REAL_ARITH_TAC);;

(* Measurability on the product space of the kernel and of its majorant.    *)

let HMRM_LMEAS_POS = prove
 (`!(f:real^N->real).
     (\x. lift(f x)) continuous_on (:real^N) ==> lebesgue_measurable {x | &0 < f x}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LEBESGUE_MEASURABLE_OPEN THEN
  SUBGOAL_THEN `{x:real^N | &0 < f x} = {x | (\x. lift(f x)) x IN {y:real^1 | y$1 > &0}}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; GSYM drop; LIFT_DROP] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
  REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT] THEN
  ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV]);;

let HMRM_MEAS_CASES0 = prove
 (`!P (Fn:real^N->real).
     lebesgue_measurable {x | P x} /\ (\x. lift(Fn x)) measurable_on (:real^N)
     ==> (\x. lift(if P x then Fn x else &0)) measurable_on (:real^N)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^N. lift(if P x then (Fn:real^N->real) x else &0)) =
                (\x. if P x then lift(Fn x) else vec 0)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[LIFT_NUM];
    MATCH_MP_TAC MEASURABLE_ON_CASES THEN ASM_REWRITE_TAC[MEASURABLE_ON_CONST]]);;

let HMRM_MEAS_SAFEINV = prove
 (`!(f:real^N->real).
     (\x. lift(f x)) continuous_on (:real^N)
     ==> (\x. lift(inv(if &0 < f x then f x else &1))) measurable_on (:real^N)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_ON_LIFT_INV THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(\x:real^N. lift(if &0 < f x then f x else &1)) =
                  (\x. if &0 < f x then lift(f x) else lift(&1))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[];
      MATCH_MP_TAC MEASURABLE_ON_CASES THEN
      ASM_SIMP_TAC[HMRM_LMEAS_POS; MEASURABLE_ON_CONST; CONTINUOUS_IMP_MEASURABLE_ON]];
    MATCH_MP_TAC(MESON[NEGLIGIBLE_EMPTY] `(s:real^N->bool) = {} ==> negligible s`) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNIV; NOT_IN_EMPTY] THEN GEN_TAC THEN
    COND_CASES_TAC THEN ASM_REAL_ARITH_TAC]);;

let HMRM_CONT_FST = prove
 (`!(f:real^M->real^P). f continuous_on (:real^M)
     ==> (\p:real^(M,N)finite_sum. f(fstcart p)) continuous_on (:real^(M,N)finite_sum)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\p:real^(M,N)finite_sum. (f:real^M->real^P)(fstcart p)) = f o fstcart`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
  ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]);;

let HMRM_CONT_SND = prove
 (`!(f:real^N->real^P). f continuous_on (:real^N)
     ==> (\p:real^(M,N)finite_sum. f(sndcart p)) continuous_on (:real^(M,N)finite_sum)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\p:real^(M,N)finite_sum. (f:real^N->real^P)(sndcart p)) = f o sndcart`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
  ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]);;

let HMRM_YK_MEAS = prove
 (`!(h:real^2->real) (g:real^2->real).
     (\x. lift(h x)) continuous_on (:real^2) /\ (\x. lift(g x)) measurable_on (:real^2)
     ==> (\p:real^(2,2)finite_sum.
            lift(if &0 < h(fstcart p)
                 then wan_mke (h(fstcart p)) (fstcart p - sndcart p) * g(sndcart p)
                 else &0)) measurable_on (:real^(2,2)finite_sum)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Hm = \x:real^2. if &0 < h x then h x else &1` THEN
  SUBGOAL_THEN
   `(\p:real^(2,2)finite_sum.
       lift(if &0 < h(fstcart p)
            then wan_mke (h(fstcart p)) (fstcart p - sndcart p) * g(sndcart p)
            else &0)) =
    (\p. lift(if &0 < h(fstcart p)
              then inv((Hm:real^2->real)(fstcart p)) pow 2 *
                   wan_mk(inv(Hm(fstcart p)) % (fstcart p - sndcart p)) * g(sndcart p)
              else &0))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `p:real^(2,2)finite_sum` THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN EXPAND_TAC "Hm" THEN
    ASM_REWRITE_TAC[wan_mke; DIMINDEX_2; REAL_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\p:real^(2,2)finite_sum. lift(h(fstcart p))) continuous_on (:real^(2,2)finite_sum)`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `\x:real^2. lift(h x)` (INST_TYPE [`:2`,`:N`] HMRM_CONT_FST)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\p:real^(2,2)finite_sum. lift(inv((Hm:real^2->real)(fstcart p))))
    measurable_on (:real^(2,2)finite_sum)`
  ASSUME_TAC THENL
   [EXPAND_TAC "Hm" THEN REWRITE_TAC[] THEN
    MP_TAC(ISPEC `\p:real^(2,2)finite_sum. h(fstcart p:real^2):real` HMRM_MEAS_SAFEINV) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HMRM_MEAS_CASES0 THEN CONJ_TAC THENL
   [MP_TAC(ISPEC `\p:real^(2,2)finite_sum. h(fstcart p:real^2):real` HMRM_LMEAS_POS) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_CMUL; REAL_POW_2] THEN
  REWRITE_TAC[GSYM LIFT_CMUL; REAL_MUL_ASSOC] THEN
  REPEAT(MATCH_MP_TAC MEASURABLE_ON_LIFT_MUL THEN CONJ_TAC) THEN
  TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [ALL_TAC;
    MATCH_MP_TAC(INST_TYPE [`:2`,`:M`; `:2`,`:N`] MEASURABLE_ON_COMPOSE_SNDCART) THEN
    ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`\p:real^(2,2)finite_sum.
                    inv((Hm:real^2->real)(fstcart p)) % (fstcart p - sndcart p)`;
                 `\w:real^2. lift(wan_mk w)`] MEASURABLE_ON_COMPOSE_CONTINUOUS) THEN
  REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_ON_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN
    MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN MATCH_MP_TAC LINEAR_COMPOSE_SUB THEN
    REWRITE_TAC[LINEAR_FSTCART; LINEAR_SNDCART];
    MATCH_MP_TAC HMRM_SMOOTH_CONT THEN REWRITE_TAC[WAN_MK_PROPS]]);;

let HMRM_YF2_MEAS = prove
 (`!(h:real^2->real) (g:real^2->real) c.
     (\x. lift(h x)) continuous_on (:real^2) /\ (\x. lift(g x)) measurable_on (:real^2)
     ==> (\p:real^(2,2)finite_sum.
            lift(if &0 < h(sndcart p) /\ dist(fstcart p,sndcart p) < &2 * h(sndcart p)
                 then c * inv(h(sndcart p)) pow 2 * g(sndcart p) else &0))
         measurable_on (:real^(2,2)finite_sum)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Hm = \x:real^2. if &0 < h x then h x else &1` THEN
  SUBGOAL_THEN
   `(\p:real^(2,2)finite_sum.
       lift(if &0 < h(sndcart p) /\ dist(fstcart p,sndcart p) < &2 * h(sndcart p)
            then c * inv(h(sndcart p)) pow 2 * g(sndcart p) else &0)) =
    (\p. lift(if &0 < h(sndcart p) /\ dist(fstcart p,sndcart p) < &2 * h(sndcart p)
              then c * inv((Hm:real^2->real)(sndcart p)) pow 2 * g(sndcart p) else &0))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `p:real^(2,2)finite_sum` THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN EXPAND_TAC "Hm" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\p:real^(2,2)finite_sum. lift(h(sndcart p))) continuous_on (:real^(2,2)finite_sum)`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `\x:real^2. lift(h x)` (INST_TYPE [`:2`,`:M`] HMRM_CONT_SND)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\p:real^(2,2)finite_sum. lift(inv((Hm:real^2->real)(sndcart p))))
    measurable_on (:real^(2,2)finite_sum)`
  ASSUME_TAC THENL
   [EXPAND_TAC "Hm" THEN REWRITE_TAC[] THEN
    MP_TAC(ISPEC `\p:real^(2,2)finite_sum. h(sndcart p:real^2):real` HMRM_MEAS_SAFEINV) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HMRM_MEAS_CASES0 THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `{p:real^(2,2)finite_sum |
         &0 < h(sndcart p) /\ dist(fstcart p,sndcart p) < &2 * h(sndcart p)} =
      {p | &0 < h(sndcart p)} INTER
      {p | &0 < &2 * h(sndcart p) - dist(fstcart p,sndcart p)}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_INTER THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `\p:real^(2,2)finite_sum. h(sndcart p:real^2):real` HMRM_LMEAS_POS) THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPEC `\p:real^(2,2)finite_sum.
                      &2 * h(sndcart p:real^2) - dist(fstcart p:real^2,sndcart p)`
                   HMRM_LMEAS_POS) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[LIFT_SUB; LIFT_CMUL; dist] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
        MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN MATCH_MP_TAC LINEAR_COMPOSE_SUB THEN
        REWRITE_TAC[LINEAR_FSTCART; LINEAR_SNDCART]]];
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC MEASURABLE_ON_CMUL THEN
  REWRITE_TAC[GSYM LIFT_CMUL; REAL_POW_2; REAL_MUL_ASSOC] THEN
  REPEAT(MATCH_MP_TAC MEASURABLE_ON_LIFT_MUL THEN CONJ_TAC) THEN
  TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  MATCH_MP_TAC(INST_TYPE [`:2`,`:M`; `:2`,`:N`] MEASURABLE_ON_COMPOSE_SNDCART) THEN
  ASM_REWRITE_TAC[]);;

let HMRM_MEASURE_BALL2 = prove
 (`!(z:real^2) r. &0 <= r ==> measure(ball(z,r)) = r pow 2 * measure(ball(vec 0:real^2,&1))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`z:real^2`; `r:real`; `&1`] MEASURE_BALL_SCALING) THEN
  ASM_REWRITE_TAC[REAL_MUL_RID; DIMINDEX_2] THEN DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN
  MP_TAC(ISPECL [`z:real^2`; `vec 0:real^2`; `&1`] BALL_TRANSLATION) THEN
  REWRITE_TAC[VECTOR_ADD_RID] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MEASURE_TRANSLATION]);;

let HMRM_YF2_SLICE = prove
 (`!(h:real^2->real) (g:real^2->real) c z.
     ((\x. lift(if &0 < h z /\ dist(x,z) < &2 * h z then c * inv(h z) pow 2 * g z
                else &0))
      has_integral
      lift(if &0 < h z then &4 * measure(ball(vec 0:real^2,&1)) * c * g z else &0))
     (:real^2)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `&0 < h(z:real^2)` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC; REWRITE_TAC[LIFT_NUM; HAS_INTEGRAL_0]] THEN
  SUBGOAL_THEN
   `(\x. lift(if dist(x,z) < &2 * h z then c * inv(h z) pow 2 * g z else &0)) =
    (\x. if x IN ball(z:real^2,&2 * h z) then lift(c * inv(h z) pow 2 * g z) else vec 0)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; IN_BALL] THEN X_GEN_TAC `x:real^2` THEN
    SUBST1_TAC(ISPECL [`x:real^2`; `z:real^2`] DIST_SYM) THEN
    COND_CASES_TAC THEN REWRITE_TAC[LIFT_NUM];
    ALL_TAC] THEN
  REWRITE_TAC[HAS_INTEGRAL_RESTRICT_UNIV] THEN
  SUBGOAL_THEN
   `lift(&4 * measure(ball(vec 0:real^2,&1)) * c * g z) =
    measure(ball(z:real^2,&2 * h z)) % lift(c * inv(h z) pow 2 * g z)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[HMRM_MEASURE_BALL2; REAL_ARITH `&0 < x ==> &0 <= &2 * x`] THEN
    REWRITE_TAC[GSYM LIFT_CMUL] THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < h(z:real^2)` THEN CONV_TAC REAL_FIELD;
    MATCH_MP_TAC HAS_INTEGRAL_CONST_GEN THEN REWRITE_TAC[MEASURABLE_BALL]]);;

let HMRM_LIP_CONT = prove
 (`!(h:real^2->real).
     (!x y. abs(h x - h y) <= norm(x - y) / &2)
     ==> (\x. lift(h x)) continuous_on (:real^2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[continuous_on; IN_UNIV; DIST_LIFT] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[dist] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x':real^2`; `x:real^2`]) THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The core of the variable-radius Young inequality, by Fubini-Tonelli on    *)
(* real^(2,2)finite_sum in the kernel form, with the explicitly integrable   *)
(* majorant                                                                  *)
(*   F2(x,z) = 9/4 B h(z)^-2 g(z) 1(|x - z| < 2 h(z)).                      *)
(* ========================================================================= *)

let HMRM_KA_YOUNG_CORE = prove
 (`!(h:real^2->real) (g:real^2->real) Bm.
     &0 <= Bm /\ (!w:real^2. wan_mk w <= Bm) /\
     (!x. &0 <= h x) /\ (!x y. abs(h x - h y) <= norm(x - y) / &2) /\
     (!x. &0 <= g x) /\ (\x. lift(g x)) integrable_on (:real^2)
     ==> (\x. lift(hmrm_ka h g x)) integrable_on (:real^2) /\
         drop(integral (:real^2) (\x. lift(hmrm_ka h g x))) <=
         (&1 + &9 * measure(ball(vec 0:real^2,&1)) * Bm) *
         drop(integral (:real^2) (\x. lift(g x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x:real^2. &0 <= h x` (LABEL_TAC "hpos") THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `M1 = measure(ball(vec 0:real^2,&1))` THEN
  SUBGOAL_THEN `&0 < M1` ASSUME_TAC THENL
   [EXPAND_TAC "M1" THEN REWRITE_TAC[MEASURE_BALL_POS; REAL_LT_01]; ALL_TAC] THEN
  ABBREV_TAC `c0 = &9 / &4 * Bm` THEN
  SUBGOAL_THEN `&0 <= c0` ASSUME_TAC THENL
   [EXPAND_TAC "c0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HMRM_LIP_CONT) THEN
  SUBGOAL_THEN `(\x. lift((g:real^2->real) x)) absolutely_integrable_on (:real^2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
    ASM_REWRITE_TAC[DIMINDEX_1; FORALL_1; GSYM drop; LIFT_DROP] THEN
    REPEAT STRIP_TAC THEN SUBGOAL_THEN `i = 1` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ASM_REWRITE_TAC[GSYM drop; LIFT_DROP]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. lift((g:real^2->real) x)) measurable_on (:real^2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[INTEGRABLE_IMP_MEASURABLE]; ALL_TAC] THEN
  SUBGOAL_THEN `wan_lloc (:real^2) (\x. lift((g:real^2->real) x))` ASSUME_TAC THENL
   [REWRITE_TAC[wan_lloc] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(:real^2)` THEN
    ASM_SIMP_TAC[SUBSET_UNIV; LEBESGUE_MEASURABLE_COMPACT];
    ALL_TAC] THEN
  ABBREV_TAC
   `f = \p:real^(2,2)finite_sum.
          lift(if &0 < h(fstcart p)
               then wan_mke (h(fstcart p)) (fstcart p - sndcart p) * g(sndcart p)
               else &0)` THEN
  ABBREV_TAC
   `F2 = \p:real^(2,2)finite_sum.
           lift(if &0 < h(sndcart p) /\ dist(fstcart p,sndcart p) < &2 * h(sndcart p)
                then c0 * inv(h(sndcart p)) pow 2 * g(sndcart p) else &0)` THEN
  SUBGOAL_THEN `(f:real^(2,2)finite_sum->real^1) measurable_on (:real^(2,2)finite_sum) /\
                (F2:real^(2,2)finite_sum->real^1) measurable_on (:real^(2,2)finite_sum)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["f"; "F2"] THEN
    ASM_SIMP_TAC[HMRM_YK_MEAS; HMRM_YF2_MEAS];
    ALL_TAC] THEN
  (* the majorant: slices, nonnegativity, absolute integrability *)
  SUBGOAL_THEN
   `!z:real^2. ((\x. (F2:real^(2,2)finite_sum->real^1)(pastecart x z)) has_integral
                lift(if &0 < h z then &4 * M1 * c0 * g z else &0)) (:real^2)`
  (LABEL_TAC "SL") THENL
   [GEN_TAC THEN EXPAND_TAC "F2" THEN EXPAND_TAC "M1" THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; HMRM_YF2_SLICE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p. &0 <= drop((F2:real^(2,2)finite_sum->real^1) p)` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "F2" THEN REWRITE_TAC[LIFT_DROP] THEN COND_CASES_TAC THEN
    REWRITE_TAC[REAL_LE_REFL] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p. norm((F2:real^(2,2)finite_sum->real^1) p) = drop(F2 p)` ASSUME_TAC THENL
   [GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM LIFT_DROP] THEN
    ASM_REWRITE_TAC[NORM_LIFT; REAL_ABS_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(F2:real^(2,2)finite_sum->real^1) absolutely_integrable_on (:real^(2,2)finite_sum)`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `F2:real^(2,2)finite_sum->real^1` FUBINI_TONELLI_ALT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC(MESON[NEGLIGIBLE_EMPTY] `(s:real^2->bool) = {} ==> negligible s`) THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN X_GEN_TAC `z:real^2` THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
      CONJ_TAC THENL
       [REWRITE_TAC[DIMINDEX_1] THEN MAP_EVERY X_GEN_TAC [`x:real^2`; `j:num`] THEN
        STRIP_TAC THEN SUBGOAL_THEN `j = 1` SUBST1_TAC THENL
         [ASM_ARITH_TAC; ASM_REWRITE_TAC[GSYM drop]];
        USE_THEN "SL" (MP_TAC o SPEC `z:real^2`) THEN MESON_TAC[integrable_on]];
      ASM_REWRITE_TAC[LIFT_DROP; ETA_AX] THEN
      SUBGOAL_THEN
       `(\z:real^2. integral (:real^2) (\x. (F2:real^(2,2)finite_sum->real^1)(pastecart x z))) =
        (\z. if z IN {z | &0 < h z} then (&4 * M1 * c0) % lift((g:real^2->real) z) else vec 0)`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; IN_ELIM_THM] THEN X_GEN_TAC `z:real^2` THEN
        USE_THEN "SL" (MP_TAC o SPEC `z:real^2`) THEN
        DISCH_THEN(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN
        COND_CASES_TAC THEN REWRITE_TAC[LIFT_NUM; LIFT_CMUL; VECTOR_MUL_ASSOC];
        ALL_TAC] THEN
      REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      EXISTS_TAC `(:real^2)` THEN ASM_SIMP_TAC[SUBSET_UNIV; HMRM_LMEAS_POS]];
    ALL_TAC] THEN
  (* the kernel is dominated by the majorant *)
  SUBGOAL_THEN
   `!p. norm((f:real^(2,2)finite_sum->real^1) p) <=
        drop((F2:real^(2,2)finite_sum->real^1) p)`
  ASSUME_TAC THENL
   [X_GEN_TAC `p:real^(2,2)finite_sum` THEN
    ASM_CASES_TAC `&0 < h(fstcart(p:real^(2,2)finite_sum):real^2)` THENL
     [ALL_TAC; EXPAND_TAC "f" THEN ASM_REWRITE_TAC[LIFT_NUM; NORM_0]] THEN
    EXPAND_TAC "f" THEN EXPAND_TAC "F2" THEN ASM_REWRITE_TAC[NORM_LIFT; LIFT_DROP] THEN
    MP_TAC(ISPECL [`h:real^2->real`; `Bm:real`; `fstcart(p:real^(2,2)finite_sum):real^2`;
                   `sndcart(p:real^(2,2)finite_sum):real^2`] HMRM_KER_BOUND) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC
     `K = wan_mke (h(fstcart(p:real^(2,2)finite_sum):real^2)) (fstcart p - sndcart p)` THEN
    SUBGOAL_THEN `&0 <= K` ASSUME_TAC THENL
     [EXPAND_TAC "K" THEN ASM_SIMP_TAC[WAN_MKE_POS]; ALL_TAC] THEN
    SUBGOAL_THEN `abs(K * g(sndcart(p:real^(2,2)finite_sum))) = K * g(sndcart p)`
    SUBST1_TAC THENL
     [REWRITE_TAC[REAL_ABS_REFL] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    COND_CASES_TAC THEN DISCH_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(&9 / &4 * Bm * inv(h(sndcart(p:real^(2,2)finite_sum))) pow 2) *
                  g(sndcart p)` THEN
      CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "c0" THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `K = &0` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_MUL_LZERO; REAL_LE_REFL]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(f:real^(2,2)finite_sum->real^1) absolutely_integrable_on (:real^(2,2)finite_sum)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
    EXISTS_TAC `F2:real^(2,2)finite_sum->real^1` THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
    ALL_TAC] THEN
  (* the x-function of the Fubini decomposition of f *)
  SUBGOAL_THEN
   `!x:real^2. integral (:real^2) (\z. (f:real^(2,2)finite_sum->real^1)(pastecart x z)) =
               lift(if &0 < h x then hmrm_ka h g x else &0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN EXPAND_TAC "f" THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    ASM_CASES_TAC `&0 < h(x:real^2)` THEN ASM_REWRITE_TAC[LIFT_NUM; INTEGRAL_0] THEN
    ASM_SIMP_TAC[HMRM_KA_MOLL; LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z:real^2. integral (:real^2) (\x. (F2:real^(2,2)finite_sum->real^1)(pastecart x z))) =
    (\z. if z IN {z | &0 < h z} then (&4 * M1 * c0) % lift((g:real^2->real) z) else vec 0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; IN_ELIM_THM] THEN X_GEN_TAC `z:real^2` THEN
    USE_THEN "SL" (MP_TAC o SPEC `z:real^2`) THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN
    COND_CASES_TAC THEN REWRITE_TAC[LIFT_NUM; LIFT_CMUL; VECTOR_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral (:real^(2,2)finite_sum) (F2:real^(2,2)finite_sum->real^1) =
    integral (:real^2)
      (\z. if z IN {z | &0 < h z} then (&4 * M1 * c0) % lift((g:real^2->real) z)
           else vec 0)`
  ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
    MP_TAC(ISPEC `F2:real^(2,2)finite_sum->real^1` FUBINI_ABSOLUTELY_INTEGRABLE_ALT) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. if z IN {z | &0 < h z} then (&4 * M1 * c0) % lift((g:real^2->real) z)
         else vec 0) integrable_on (:real^2)`
  ASSUME_TAC THENL
   [REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(:real^2)` THEN ASM_SIMP_TAC[SUBSET_UNIV; HMRM_LMEAS_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `drop(integral (:real^(2,2)finite_sum) (F2:real^(2,2)finite_sum->real^1)) <=
    (&4 * M1 * c0) * drop(integral (:real^2) (\x. lift((g:real^2->real) x)))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(&4 * M1 * c0) * drop(integral (:real^2) (\x. lift((g:real^2->real) x))) =
      drop(integral (:real^2) (\x. (&4 * M1 * c0) % lift(g x)))`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[INTEGRAL_CMUL; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; DROP_CMUL];
      ALL_TAC] THEN
    MATCH_MP_TAC INTEGRAL_DROP_LE THEN
    ASM_SIMP_TAC[INTEGRABLE_CMUL; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
    X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[REAL_LE_REFL; DROP_VEC; DROP_CMUL; LIFT_DROP] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    MAP_EVERY UNDISCH_TAC [`&0 < M1`; `&0 <= c0`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the part where h > 0 *)
  SUBGOAL_THEN
   `((\x. lift(if &0 < h x then hmrm_ka h g x else &0)) has_integral
     integral (:real^(2,2)finite_sum) (f:real^(2,2)finite_sum->real^1)) (:real^2)`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `f:real^(2,2)finite_sum->real^1` FUBINI_ABSOLUTELY_INTEGRABLE) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `drop(integral (:real^(2,2)finite_sum) (f:real^(2,2)finite_sum->real^1)) <=
    drop(integral (:real^(2,2)finite_sum) (F2:real^(2,2)finite_sum->real^1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; IN_UNIV] THEN
    X_GEN_TAC `p:real^(2,2)finite_sum` THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm((f:real^(2,2)finite_sum->real^1) p)` THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM LIFT_DROP] THEN
    REWRITE_TAC[NORM_LIFT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the part where h = 0 *)
  SUBGOAL_THEN
   `(\x. lift(if &0 < h x then &0 else (g:real^2->real) x)) integrable_on (:real^2) /\
    drop(integral (:real^2) (\x. lift(if &0 < h x then &0 else g x))) <=
    drop(integral (:real^2) (\x. lift(g x)))`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\x. lift(if &0 < h x then &0 else (g:real^2->real) x)) =
      (\x. if x IN {x | ~(&0 < h x)} then lift(g x) else vec 0)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; IN_ELIM_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[LIFT_NUM];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV] THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[SUBSET_UNIV] THEN
      REWRITE_TAC[SET_RULE `{x | ~P x} = (:real^2) DIFF {x | P x}`] THEN
      MATCH_MP_TAC LEBESGUE_MEASURABLE_DIFF THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_UNIV; HMRM_LMEAS_POS];
      DISCH_TAC THEN MATCH_MP_TAC INTEGRAL_DROP_LE THEN
      ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
      GEN_TAC THEN DISCH_TAC THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[DROP_VEC; LIFT_DROP; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(hmrm_ka h g x)) =
    (\x. lift(if &0 < h x then hmrm_ka h g x else &0) +
         lift(if &0 < h x then &0 else (g:real^2->real) x))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^2` THEN COND_CASES_TAC THEN
    REWRITE_TAC[LIFT_NUM; VECTOR_ADD_RID; VECTOR_ADD_LID] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC HMRM_KA_ZERO THEN
    USE_THEN "hpos" (MP_TAC o SPEC `x:real^2`) THEN
    UNDISCH_TAC `~(&0 < (h:real^2->real) x)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC
   `((\x. lift(if &0 < h x then hmrm_ka h g x else &0)) has_integral
     integral (:real^(2,2)finite_sum) (f:real^(2,2)finite_sum->real^1)) (:real^2)` THEN
  DISCH_THEN(fun th -> ASSUME_TAC(MATCH_MP HAS_INTEGRAL_INTEGRABLE th) THEN
                       ASSUME_TAC(MATCH_MP INTEGRAL_UNIQUE th)) THEN
  ASM_SIMP_TAC[INTEGRABLE_ADD; INTEGRAL_ADD; DROP_ADD] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&4 * M1 * c0) * drop(integral (:real^2) (\x. lift((g:real^2->real) x))) +
              drop(integral (:real^2) (\x. lift(g x)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[REAL_LE_TRANS];
    EXPAND_TAC "c0" THEN REAL_ARITH_TAC]);;

(* The variable-radius Young inequality: for h >= 0 with Lipschitz constant *)
(* 1/2 and nonnegative integrable g, the average hmrm_ka h g is integrable  *)
(* with integral at most Cy times that of g (Cy universal).                 *)

let HMRM_KA_YOUNG = prove
 (`?Cy. &0 < Cy /\
        !(h:real^2->real) (g:real^2->real).
          (!x. &0 <= h x) /\ (!x y. abs(h x - h y) <= norm(x - y) / &2) /\
          (!x. &0 <= g x) /\ (\x. lift(g x)) integrable_on (:real^2)
          ==> (\x. lift(hmrm_ka h g x)) integrable_on (:real^2) /\
              drop(integral (:real^2) (\x. lift(hmrm_ka h g x))) <=
              Cy * drop(integral (:real^2) (\x. lift(g x)))`,
  MP_TAC(INST_TYPE [`:2`,`:M`] WAN_MK_BOUND) THEN
  DISCH_THEN(X_CHOOSE_THEN `Bm:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `&1 + &9 * measure(ball(vec 0:real^2,&1)) * Bm` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &1 + x`) THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    SIMP_TAC[MEASURE_POS_LE; MEASURABLE_BALL] THEN ASM_REAL_ARITH_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC HMRM_KA_YOUNG_CORE THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Jensen's inequality for the mollification of a vector map:                *)
(*   |hmrm_vr h u x|^2 <= hmrm_ka h |u|^2 x.                                *)
(* ========================================================================= *)

let HMRM_VR_JENSEN = prove
 (`!(h:real^2->real) (u:real^2->real^K) x.
     &0 <= h x /\ wan_lloc (:real^2) u /\ wan_lloc (:real^2) (\z. lift(norm(u z) pow 2))
     ==> norm(hmrm_vr h u x) pow 2 <= hmrm_ka h (\z. norm(u z) pow 2) x`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `h(x:real^2) = &0` THENL
   [ASM_SIMP_TAC[HMRM_VR_ZERO; HMRM_KA_ZERO; REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < h(x:real^2)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[HMRM_VR_MOLL; HMRM_KA_MOLL; WAN_MOLL_EQ] THEN
  ABBREV_TAC `t = (h:real^2->real) x` THEN
  SUBGOAL_THEN `wan_lloc (:real^2) (\z. lift(norm((u:real^2->real^K) z)))` ASSUME_TAC THENL
   [UNDISCH_TAC `wan_lloc (:real^2) (u:real^2->real^K)` THEN
    REWRITE_TAC[wan_lloc] THEN MESON_TAC[ABSOLUTELY_INTEGRABLE_NORM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`wan_mke t:real^2->real`; `u:real^2->real^K`; `x:real^2`]
                WAN_KCONV_INTEGRABLE) THEN
  MP_TAC(ISPECL [`wan_mke t:real^2->real`; `\z. lift(norm((u:real^2->real^K) z))`;
                 `x:real^2`] WAN_KCONV_INTEGRABLE) THEN
  MP_TAC(ISPECL [`wan_mke t:real^2->real`; `\z. lift(norm((u:real^2->real^K) z) pow 2)`;
                 `x:real^2`] WAN_KCONV_INTEGRABLE) THEN
  ASM_SIMP_TAC[WAN_MKE_TEST; GSYM LIFT_CMUL] THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (:real^2)
                 (\z. lift(wan_mke t (x - z) * norm((u:real^2->real^K) z)))) pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; IN_UNIV; LIFT_DROP] THEN
    GEN_TAC THEN REWRITE_TAC[NORM_MUL] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[REAL_ABS_REFL; WAN_MKE_POS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z:real^2. wan_mke t (x - z)`; `\z. norm((u:real^2->real^K) z)`]
                WAN_WEIGHTED_CS) THEN
  ASM_SIMP_TAC[WAN_MKE_POS; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`t:real`; `x:real^2`] WAN_MKE_INTEGRAL_AT) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[integrable_on];
    ALL_TAC] THEN
  SUBGOAL_THEN `drop(integral (:real^2) (\z. lift(wan_mke t (x - z:real^2)))) = &1`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`t:real`; `x:real^2`] WAN_MKE_INTEGRAL_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN
    REWRITE_TAC[LIFT_DROP];
    REWRITE_TAC[REAL_MUL_LID]]);;

(* Localization: the value at x only depends on the map on ball(x,h x).    *)

let HMRM_VR_LOCAL = prove
 (`!(h:real^2->real) (Fu:real^2->real^K) Gu x t.
     &0 <= h x /\ x IN t /\ (&0 < h x ==> ball(x,h x) SUBSET t) /\
     (!z. z IN t ==> Fu z = Gu z)
     ==> hmrm_vr h Fu x = hmrm_vr h Gu x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hmrm_vr] THEN MATCH_MP_TAC INTEGRAL_EQ THEN
  X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  ASM_CASES_TAC `&1 <= norm(y:real^2)` THENL
   [ASM_SIMP_TAC[WAN_MK_PROPS; VECTOR_MUL_LZERO]; ALL_TAC] THEN
  AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_CASES_TAC `h(x:real^2) = &0` THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_SUB_RZERO]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < h(x:real^2)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o C MP (ASSUME `&0 < h(x:real^2)`)) THEN
  REWRITE_TAC[IN_BALL; NORM_ARITH `dist(x:real^2,x - y) = norm y`; NORM_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC);;

let HMRM_KA_LOCAL = prove
 (`!(h:real^2->real) f g x t.
     &0 <= h x /\ x IN t /\ (&0 < h x ==> ball(x,h x) SUBSET t) /\
     (!z. z IN t ==> f z = g z)
     ==> hmrm_ka h f x = hmrm_ka h g x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HMRM_KA_VR] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC HMRM_VR_LOCAL THEN EXISTS_TAC `t:real^2->bool` THEN ASM_SIMP_TAC[]);;

let HMRM_VR_SUB = prove
 (`!(h:real^2->real) (u:real^2->real^K) v x.
     &0 <= h x /\ wan_lloc (:real^2) u /\ wan_lloc (:real^2) v
     ==> hmrm_vr h (\z. u z - v z) x = hmrm_vr h u x - hmrm_vr h v x`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `h(x:real^2) = &0` THENL
   [ASM_SIMP_TAC[HMRM_VR_ZERO]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < h(x:real^2)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `wan_lloc (:real^2) (\z. (u:real^2->real^K) z - v z)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_LLOC_SUB]; ALL_TAC] THEN
  ASM_SIMP_TAC[HMRM_VR_MOLL; WAN_MOLL_EQ; VECTOR_SUB_LDISTRIB] THEN
  MATCH_MP_TAC INTEGRAL_SUB THEN CONJ_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  MATCH_MP_TAC WAN_KCONV_INTEGRABLE THEN ASM_SIMP_TAC[WAN_MKE_TEST]);;

(* The bound of the derivative of h gives the Lipschitz constant 1/2 and    *)
(* the partial bounds used above.                                            *)

let HMRM_DH_FACTS = prove
 (`!(h:real^2->real).
     smooth_map_on (:real^2) (\x. lift(h x)) /\
     (!x v. abs(drop(frechet_derivative (\x. lift(h x)) (at x) v)) <= norm v / &2)
     ==> (!x y. abs(h x - h y) <= norm(x - y) / &2) /\
         (!x i. 1 <= i /\ i <= 2
                ==> abs(drop(partial_derivative i (\x. lift(h x)) x)) <= &1 / &2)`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`\x:real^2. lift(h x)`; `frechet_derivative (\x:real^2. lift(h x)) o at`;
                   `(:real^2)`; `&1 / &2`] DIFFERENTIABLE_BOUND) THEN
    REWRITE_TAC[CONVEX_UNIV; IN_UNIV; o_THM; GSYM DIST_LIFT; dist] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [X_GEN_TAC `z:real^2` THEN
        MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
        MP_TAC(ISPECL [`(:real^2)`; `\x:real^2. lift(h x)`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
        ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN SIMP_TAC[];
        X_GEN_TAC `z:real^2` THEN
        SUBGOAL_THEN `linear(frechet_derivative (\x:real^2. lift(h x)) (at z))` ASSUME_TAC THENL
         [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
          MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^2)` THEN
          ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
          ALL_TAC] THEN
        MP_TAC(ISPEC `frechet_derivative (\x:real^2. lift(h x)) (at z)` ONORM) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
        GEN_TAC THEN
        GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM LIFT_DROP] THEN
        REWRITE_TAC[NORM_LIFT] THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`z:real^2`; `x:real^2`]) THEN REAL_ARITH_TAC];
      REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT] THEN
      DISCH_THEN(MP_TAC o SPECL [`x:real^2`; `y:real^2`]) THEN REAL_ARITH_TAC];
    REWRITE_TAC[partial_derivative] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^2`; `basis i:real^2`]) THEN
    ASM_SIMP_TAC[NORM_BASIS; DIMINDEX_2]]);;

(* L^2 convergence on k gives convergence of the squared L^2 norms on       *)
(* measurable subsets of k.                                                   *)

let HMRM_LNORM_DIFF = prove
 (`!(a:real^N->bool) (f:real^N->real^K) g.
     f IN lspace a (&2) /\ g IN lspace a (&2)
     ==> abs(lnorm a (&2) f - lnorm a (&2) g) <= lnorm a (&2) (\x. f x - g x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. (f:real^N->real^K) x - g x) IN lspace a (&2) /\
                (\x. (g:real^N->real^K) x - f x) IN lspace a (&2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^N->bool`; `&2`; `g:real^N->real^K`; `\x. (f:real^N->real^K) x - g x`]
                LNORM_TRIANGLE) THEN
  MP_TAC(ISPECL [`a:real^N->bool`; `&2`; `f:real^N->real^K`; `\x. (g:real^N->real^K) x - f x`]
                LNORM_TRIANGLE) THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `f + (g - f):real^K = g`; ETA_AX] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SUBGOAL_THEN `lnorm a (&2) (\x. (g:real^N->real^K) x - f x) =
                lnorm a (&2) (\x. f x - g x)`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM LNORM_NEG] THEN REWRITE_TAC[VECTOR_NEG_SUB];
    REAL_ARITH_TAC]);;

let HMRM_L2SQ_CONV = prove
 (`!(f:num->real^N->real^K) g k a.
     lebesgue_measurable a /\ a SUBSET k /\ g IN lspace k (&2) /\
     (!n. f n IN lspace k (&2)) /\
     ((\n. drop(integral k (\x. lift(norm(f n x - g x) pow 2)))) ---> &0) sequentially
     ==> ((\n. drop(integral a (\x. lift(norm(f n x) pow 2)))) --->
          drop(integral a (\x. lift(norm(g x) pow 2)))) sequentially`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(g:real^N->real^K) IN lspace a (&2) /\ !n. (f:num->real^N->real^K) n IN lspace a (&2)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[LSPACE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (\x. (f:num->real^N->real^K) n x - g x) IN lspace k (&2) /\
        (\x. f n x - g x) IN lspace a (&2)`
  ASSUME_TAC THENL
   [GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. lnorm a (&2) (\x. (f:num->real^N->real^K) n x - g x) pow 2 <=
        drop(integral k (\x. lift(norm(f n x - g x) pow 2)))`
  (LABEL_TAC "DY") THENL
   [GEN_TAC THEN ASM_SIMP_TAC[WAN_SOB_LNORM2_SQ] THEN
    MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
    ASM_SIMP_TAC[WAN_LSPACE2_SQNORM_INTEGRABLE; LIFT_DROP; REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\n. lnorm a (&2) ((f:num->real^N->real^K) n)) ---> lnorm a (&2) (g:real^N->real^K))
    sequentially`
  MP_TAC THENL
   [REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY] o check (fun th ->
      is_comb(concl th) && fst(dest_const(fst(strip_comb(concl th)))) = "--->")) THEN
    DISCH_THEN(MP_TAC o SPEC `e pow 2`) THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `lnorm a (&2) (\x. (f:num->real^N->real^K) n x - g x)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC HMRM_LNORM_DIFF THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= lnorm a (&2) (\x. (f:num->real^N->real^K) n x - g x)` ASSUME_TAC
    THENL [MATCH_MP_TAC LNORM_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`2`; `e:real`;
                   `lnorm a (&2) (\x. (f:num->real^N->real^K) n x - g x)`] REAL_POW_LE2) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    USE_THEN "DY" (MP_TAC o SPEC `n:num`) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `2` o MATCH_MP REALLIM_POW) THEN
  ASM_SIMP_TAC[WAN_SOB_LNORM2_SQ]);;

let HMRM_INTEGRAL_ZERO_OUTSIDE = prove
 (`!(f:real^N->real^K) t.
     (!y. ~(y IN t) ==> f y = vec 0) ==> integral (:real^N) f = integral t f`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM INTEGRAL_RESTRICT_UNIV] THEN
  MATCH_MP_TAC INTEGRAL_EQ THEN REWRITE_TAC[IN_UNIV] THEN GEN_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[]);;

let HMRM_KA_KERNEL_BOUND = prove
 (`!(h:real^2->real) g x t Bm.
     &0 < h x /\ (!w:real^2. wan_mk w <= Bm) /\ (!z. &0 <= g z) /\
     wan_lloc (:real^2) (\z. lift(g z)) /\
     ball(x,h x) SUBSET t /\ (\z. lift(g z)) integrable_on t
     ==> hmrm_ka h g x <= Bm * inv(h x) pow 2 * drop(integral t (\z. lift(g z)))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[HMRM_KA_MOLL] THEN
  ABBREV_TAC `e = (h:real^2->real) x` THEN
  SUBGOAL_THEN
   `!z. ~(z IN t) ==> lift(wan_mke e (x - z) * (g:real^2->real) z) = vec 0`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `e <= norm(x - z:real^2)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      UNDISCH_TAC `~((z:real^2) IN t)` THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
      ASM_REWRITE_TAC[IN_BALL; dist];
      ASM_SIMP_TAC[WAN_MKE_ZERO; REAL_MUL_LZERO; LIFT_NUM]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral (:real^2) (\z. lift(wan_mke e (x - z) * g z)) =
    integral t (\z. lift(wan_mke e (x - z) * g z))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC HMRM_INTEGRAL_ZERO_OUTSIDE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(\z. lift(wan_mke e (x - z) * (g:real^2->real) z)) integrable_on (:real^2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN REWRITE_TAC[LIFT_CMUL] THEN
    MP_TAC(ISPECL [`wan_mke e:real^2->real`; `\z. lift((g:real^2->real) z)`; `x:real^2`]
                  WAN_KCONV_INTEGRABLE) THEN
    ASM_SIMP_TAC[WAN_MKE_TEST];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  SUBGOAL_THEN
   `(Bm * inv e pow 2) * drop(integral t (\z. lift((g:real^2->real) z))) =
    drop(integral t (\z. lift((Bm * inv e pow 2) * g z)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[LIFT_CMUL] THEN ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL]; ALL_TAC] THEN
  MATCH_MP_TAC INTEGRAL_DROP_LE THEN REPEAT CONJ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM INTEGRABLE_RESTRICT_UNIV] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> fst(dest_const(rator(rator(concl th)))) =
                                            "integrable_on")) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^2` THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[wan_mke; DIMINDEX_2] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[REAL_LE_POW_2]]);;

(* ========================================================================= *)
(* The W^{1,2} membership of the variable-radius mollification of a W^{1,2}  *)
(* map on an open set A whose h-neighbourhood lies in A' SUBSET k (compact   *)
(* in s), with the energy bound  dir(A) <= Cv * int_A' |Du|^2.  Proof:       *)
(* smooth approximation (WAN_W12_LOCAL_APPROX), the smooth-case derivative   *)
(* bound, the variable-radius Young inequality, and lower semicontinuity     *)
(* (WAN_DIR_LSC).                                                            *)
(* ========================================================================= *)

let HMRM_LIM_FROM_SQ = prove
 (`!(f:num->real^K) l c y.
     &0 <= c /\ (!n. norm(f n - l) pow 2 <= c * y n) /\ (y ---> &0) sequentially
     ==> (f --> l) sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIM_SEQUENTIALLY; dist] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY]) THEN
  DISCH_THEN(MP_TAC o SPEC `e pow 2 / (c + &1)`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_POW_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `norm((f:num->real^K) n - l) pow 2 < e pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `c * (y:num->real) n` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `(c + &1) * abs((y:num->real) n)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c * abs((y:num->real) n)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN REAL_ARITH_TAC];
      ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_ARITH `&0 <= c ==> &0 < c + &1`] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_ARITH `&0 <= c ==> &0 < c + &1`]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN
  ONCE_REWRITE_TAC[TAUT `(~p ==> ~q) <=> (q ==> p)`] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC);;

let HMRM_REALLIM_FROM_SQ = prove
 (`!(a:num->real) c y.
     &0 <= c /\ (!n. &0 <= a n /\ a n pow 2 <= c * y n) /\ (y ---> &0) sequentially
     ==> (a ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\n. lift((a:num->real) n)`; `vec 0:real^1`; `c:real`; `y:num->real`]
                HMRM_LIM_FROM_SQ) THEN
  ASM_REWRITE_TAC[VECTOR_SUB_RZERO; NORM_LIFT; REAL_POW2_ABS] THEN
  REWRITE_TAC[TENDSTO_REAL; o_DEF; LIFT_NUM]);;

let HMRM_KA_POS = prove
 (`!(h:real^2->real) g x.
     &0 <= h x /\ (!z. &0 <= g z) /\ wan_lloc (:real^2) (\z. lift(g z))
     ==> &0 <= hmrm_ka h g x`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `h(x:real^2) = &0` THEN
  ASM_SIMP_TAC[HMRM_KA_ZERO] THEN
  SUBGOAL_THEN `&0 < h(x:real^2)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[HMRM_KA_MOLL] THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN CONJ_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN REWRITE_TAC[LIFT_CMUL] THEN
    MP_TAC(ISPECL [`wan_mke (h(x:real^2)):real^2->real`; `\z. lift((g:real^2->real) z)`;
                   `x:real^2`] WAN_KCONV_INTEGRABLE) THEN
    ASM_SIMP_TAC[WAN_MKE_TEST];
    GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[WAN_MKE_POS]]);;

let HMRM_CONT_LSPACE2 = prove
 (`!(f:real^2->real^N) k t.
     compact k /\ f continuous_on k /\ lebesgue_measurable t /\ t SUBSET k
     ==> f IN lspace t (&2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `bounded(IMAGE (f:real^2->real^N) k)` MP_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `measurable(t:real^2->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MEASURABLE_LEBESGUE_MEASURABLE_SUBSET THEN EXISTS_TAC `k:real^2->bool` THEN
    ASM_SIMP_TAC[MEASURABLE_COMPACT];
    ALL_TAC] THEN
  MATCH_MP_TAC WAN_L2_BOUND_LSPACE THEN EXISTS_TAC `\x:real^2. B pow 2` THEN
  ASM_REWRITE_TAC[INTEGRABLE_ON_CONST] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    REWRITE_TAC[NORM_POS_LE] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]);;

let HMRM_EPS_LE = prove
 (`!x y. (!d. &0 < d ==> x <= y + d) ==> x <= y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(x - y) / &2`) THEN ASM_REAL_ARITH_TAC);;

let HMRM_SQNORM_ADD_INTEGRAL = prove
 (`!(f1:real^N->real^K) (f2:real^N->real^K) a.
     f1 IN lspace a (&2) /\ f2 IN lspace a (&2)
     ==> drop(integral a (\x. lift(norm(f1 x) pow 2 + norm(f2 x) pow 2))) =
         drop(integral a (\x. lift(norm(f1 x) pow 2))) +
         drop(integral a (\x. lift(norm(f2 x) pow 2)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^N->bool`; `f1:real^N->real^K`] WAN_LSPACE2_SQNORM_INTEGRABLE) THEN
  MP_TAC(ISPECL [`a:real^N->bool`; `f2:real^N->real^K`] WAN_LSPACE2_SQNORM_INTEGRABLE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  ASM_SIMP_TAC[LIFT_ADD; INTEGRAL_ADD; DROP_ADD]);;

let HMRM_L2SQ_CONV2 = prove
 (`!(f1:num->real^N->real^K) (f2:num->real^N->real^K) (g1:real^N->real^K)
    (g2:real^N->real^K) k a.
     lebesgue_measurable a /\ a SUBSET k /\ g1 IN lspace k (&2) /\ g2 IN lspace k (&2) /\
     (!n. f1 n IN lspace k (&2)) /\ (!n. f2 n IN lspace k (&2)) /\
     ((\n. drop(integral k (\x. lift(norm(f1 n x - g1 x) pow 2)))) ---> &0) sequentially /\
     ((\n. drop(integral k (\x. lift(norm(f2 n x - g2 x) pow 2)))) ---> &0) sequentially
     ==> ((\n. drop(integral a (\x. lift(norm(f1 n x) pow 2 + norm(f2 n x) pow 2)))) --->
          drop(integral a (\x. lift(norm(g1 x) pow 2 + norm(g2 x) pow 2)))) sequentially`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(g1:real^N->real^K) IN lspace a (&2) /\ (g2:real^N->real^K) IN lspace a (&2) /\
    (!n. (f1:num->real^N->real^K) n IN lspace a (&2)) /\
    (!n. (f2:num->real^N->real^K) n IN lspace a (&2))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY GEN_TAC THEN MATCH_MP_TAC LSPACE_SUBSET THEN
    EXISTS_TAC `k:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[HMRM_SQNORM_ADD_INTEGRAL; ETA_AX] THEN
  MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THEN MATCH_MP_TAC HMRM_L2SQ_CONV THEN
  EXISTS_TAC `k:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let HMRM_VR_W12_LOC = prove
 (`?Cv. &0 < Cv /\
     !(s:real^2->bool) (u:real^2->real^K) (h:real^2->real) k A A'.
       open s /\ wan_w12 s u /\ compact k /\ k SUBSET s /\
       smooth_map_on (:real^2) (\x. lift(h x)) /\ (!x. &0 <= h x) /\
       (!x v. abs(drop(frechet_derivative (\x. lift(h x)) (at x) v)) <= norm v / &2) /\
       open A /\ lebesgue_measurable A' /\ A' SUBSET k /\
       (!x. x IN A ==> x IN A' /\ (&0 < h x ==> ball(x,h x) SUBSET A'))
       ==> wan_w12 A (hmrm_vr h (\x. if x IN s then u x else vec 0)) /\
           wan_dir A (hmrm_vr h (\x. if x IN s then u x else vec 0)) <=
           Cv * drop(integral A' (\x. lift(norm(wan_wd s 1 u x) pow 2 +
                                          norm(wan_wd s 2 u x) pow 2)))`,
  X_CHOOSE_THEN `Cy:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "YG")) HMRM_KA_YOUNG THEN
  MP_TAC(INST_TYPE [`:2`,`:M`] WAN_MK_BOUND) THEN
  DISCH_THEN(X_CHOOSE_THEN `Bm:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `&9 * Cy` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(MATCH_MP HMRM_DH_FACTS (CONJ
    (ASSUME `smooth_map_on (:real^2) (\x. lift((h:real^2->real) x))`) th))) THEN
  STRIP_TAC THEN
  ABBREV_TAC `u0 = \x:real^2. if x IN s then (u:real^2->real^K) x else vec 0` THEN
  SUBGOAL_THEN `(u:real^2->real^K) IN lspace s (&2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[wan_w12]; ALL_TAC] THEN
  SUBGOAL_THEN `(u0:real^2->real^K) IN lspace (:real^2) (&2)` ASSUME_TAC THENL
   [EXPAND_TAC "u0" THEN ASM_SIMP_TAC[WAN_LSPACE_RESTRICT_UNIV; REAL_ARITH `&0 < &2`];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_lloc (:real^2) (u0:real^2->real^K)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_LSPACE2_IMP_LLOC]; ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN k ==> (u0:real^2->real^K) z = u z` ASSUME_TAC THENL
   [EXPAND_TAC "u0" THEN REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(A:real^2->bool) SUBSET k /\ bounded A /\ lebesgue_measurable A`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(A:real^2->bool) SUBSET k` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN] THEN
    ASM_MESON_TAC[BOUNDED_SUBSET; COMPACT_IMP_BOUNDED];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `u:real^2->real^K`; `\i. wan_wd s i (u:real^2->real^K)`;
                 `k:real^2->bool`] WAN_W12_LOCAL_APPROX) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[WAN_LSPACE2_IMP_L2LOC] THEN REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC WAN_LSPACE2_IMP_L2LOC; ALL_TAC] THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `i:num`; `u:real^2->real^K`] WAN_WD_WORKS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_2] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:num->real^2->real^K` (CONJUNCTS_THEN2 (LABEL_TAC "wt")
    (CONJUNCTS_THEN2 (LABEL_TAC "w0") (CONJUNCTS_THEN2 (LABEL_TAC "w1")
      (X_CHOOSE_THEN `tn:real^2->bool` STRIP_ASSUME_TAC))))) THEN
  (* facts on the approximating maps *)
  SUBGOAL_THEN `!n. smooth_map_on (:real^2) ((w:num->real^2->real^K) n)` ASSUME_TAC THENL
   [GEN_TAC THEN USE_THEN "wt" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[wan_vtest]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. (w:num->real^2->real^K) n IN lspace (:real^2) (&2)` ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`(:real^2)`; `(w:num->real^2->real^K) n`] WAN_VTEST_W12) THEN
    REWRITE_TAC[OPEN_UNIV] THEN ANTS_TAC THENL
     [USE_THEN "wt" (MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[wan_vtest; SUBSET_UNIV] THEN
      MESON_TAC[];
      MESON_TAC[wan_w12]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (\z. (w:num->real^2->real^K) n z - u0 z) IN lspace (:real^2) (&2)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. wan_lloc (:real^2) ((w:num->real^2->real^K) n) /\
        wan_lloc (:real^2) (\z. (w:num->real^2->real^K) n z - u0 z) /\
        wan_lloc (:real^2) (\z. lift(norm((w:num->real^2->real^K) n z - u0 z) pow 2))`
  ASSUME_TAC THENL
   [GEN_TAC THEN ASM_SIMP_TAC[WAN_LSPACE2_IMP_LLOC] THEN REWRITE_TAC[wan_lloc] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(:real^2)` THEN ASM_SIMP_TAC[SUBSET_UNIV; LEBESGUE_MEASURABLE_COMPACT] THEN
    MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
    ASM_SIMP_TAC[WAN_LSPACE2_SQNORM_INTEGRABLE] THEN
    REWRITE_TAC[DIMINDEX_1] THEN MAP_EVERY X_GEN_TAC [`z:real^2`; `j:num`] THEN
    STRIP_TAC THEN SUBGOAL_THEN `j = 1` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[GSYM drop; LIFT_DROP; REAL_LE_POW_2]];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_lloc (:real^2) (\z. lift(norm((u0:real^2->real^K) z) pow 2))`
  ASSUME_TAC THENL
   [REWRITE_TAC[wan_lloc] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(:real^2)` THEN ASM_SIMP_TAC[SUBSET_UNIV; LEBESGUE_MEASURABLE_COMPACT] THEN
    MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
    ASM_SIMP_TAC[WAN_LSPACE2_SQNORM_INTEGRABLE] THEN
    REWRITE_TAC[DIMINDEX_1] THEN MAP_EVERY X_GEN_TAC [`z:real^2`; `j:num`] THEN
    STRIP_TAC THEN SUBGOAL_THEN `j = 1` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[GSYM drop; LIFT_DROP; REAL_LE_POW_2]];
    ALL_TAC] THEN
  (* the pointwise comparison of M_n and M on A *)
  SUBGOAL_THEN
   `!n x. x IN A
          ==> norm(hmrm_vr h ((w:num->real^2->real^K) n) x - hmrm_vr h u0 x) pow 2 <=
              hmrm_ka h (\z. norm(w n z - u0 z) pow 2) x`
  (LABEL_TAC "JX") THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM HMRM_VR_SUB] THEN
    MATCH_MP_TAC HMRM_VR_JENSEN THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* integrals of |w_n - u0|^2 over A' are bounded by those of |w_n - u|^2 over k *)
  SUBGOAL_THEN
   `!n. (\z. lift(norm((w:num->real^2->real^K) n z - u0 z) pow 2)) integrable_on A' /\
        drop(integral A' (\z. lift(norm(w n z - u0 z) pow 2))) <=
        drop(integral k (\z. lift(norm(w n z - u z) pow 2)))`
  (LABEL_TAC "AK") THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `(\z. lift(norm((w:num->real^2->real^K) n z - u0 z) pow 2))
                  integrable_on (:real^2)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[WAN_LSPACE2_SQNORM_INTEGRABLE]; ALL_TAC] THEN
    SUBGOAL_THEN `!t. lebesgue_measurable t
                      ==> (\z. lift(norm((w:num->real^2->real^K) n z - u0 z) pow 2))
                          integrable_on t` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[SUBSET_UNIV] THEN
      MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[DIMINDEX_1] THEN MAP_EVERY X_GEN_TAC [`z:real^2`; `j:num`] THEN
      STRIP_TAC THEN SUBGOAL_THEN `j = 1` SUBST1_TAC THENL
       [ASM_ARITH_TAC; REWRITE_TAC[GSYM drop; LIFT_DROP; REAL_LE_POW_2]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN
     `integral k (\z. lift(norm((w:num->real^2->real^K) n z - u z) pow 2)) =
      integral k (\z. lift(norm(w n z - u0 z) pow 2))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC INTEGRAL_EQ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT; LIFT_DROP; REAL_LE_POW_2];
    ALL_TAC] THEN
  (* pointwise convergence on A off tn, measurability of M on A *)
  SUBGOAL_THEN
   `!x. x IN A DIFF tn
        ==> ((\n. hmrm_vr h ((w:num->real^2->real^K) n) x) --> hmrm_vr h u0 x) sequentially`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
    ASM_CASES_TAC `h(x:real^2) = &0` THENL
     [ASM_SIMP_TAC[HMRM_VR_ZERO] THEN
      SUBGOAL_THEN `(u0:real^2->real^K) x = u x` SUBST1_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < h(x:real^2)` ASSUME_TAC THENL
     [ASM_MESON_TAC[REAL_LT_LE]; ALL_TAC] THEN
    MATCH_MP_TAC HMRM_LIM_FROM_SQ THEN
    MAP_EVERY EXISTS_TAC
     [`Bm * inv(h(x:real^2)) pow 2`;
      `\n. drop(integral k (\z. lift(norm((w:num->real^2->real^K) n z - u z) pow 2)))`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `n:num` THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `hmrm_ka h (\z. norm((w:num->real^2->real^K) n z - u0 z) pow 2) x` THEN
    CONJ_TAC THENL [USE_THEN "JX" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `Bm * inv(h(x:real^2)) pow 2 *
                drop(integral A' (\z. lift(norm((w:num->real^2->real^K) n z - u0 z) pow 2)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HMRM_KA_KERNEL_BOUND THEN
      USE_THEN "AK" (MP_TAC o SPEC `n:num`) THEN ASM_SIMP_TAC[REAL_LE_POW_2] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
      USE_THEN "AK" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(hmrm_vr h (u0:real^2->real^K)) measurable_on A` ASSUME_TAC THENL
   [MATCH_MP_TAC MEASURABLE_ON_LIMIT THEN
    MAP_EVERY EXISTS_TAC [`\n. hmrm_vr h ((w:num->real^2->real^K) n)`; `tn:real^2->bool`] THEN
    ASM_REWRITE_TAC[] THEN GEN_TAC THEN
    MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    ASM_SIMP_TAC[SUBSET_UNIV; HMRM_SMOOTH_CONT; HMRM_VR_SMOOTH];
    ALL_TAC] THEN
  (* restriction to A' of nonnegative integrable functions, and Young *)
  SUBGOAL_THEN
   `!Fv:real^2->real.
      (!z. &0 <= Fv z) /\ (\z. lift(Fv z)) integrable_on (:real^2)
      ==> (!z. &0 <= (\z. if z IN A' then Fv z else &0) z) /\
          (\z. lift((\z. if z IN A' then Fv z else &0) z)) integrable_on (:real^2) /\
          wan_lloc (:real^2) (\z. lift((\z. if z IN A' then Fv z else &0) z)) /\
          drop(integral (:real^2) (\z. lift((\z. if z IN A' then Fv z else &0) z))) =
          drop(integral A' (\z. lift(Fv z)))`
  (LABEL_TAC "RA") THENL
   [GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(\z. lift(if z IN A' then (Fv:real^2->real) z else &0)) =
                  (\z. if z IN A' then lift(Fv z) else vec 0)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[LIFT_NUM];
      ALL_TAC] THEN
    SUBGOAL_THEN `(\z. lift((Fv:real^2->real) z)) absolutely_integrable_on (:real^2)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[DIMINDEX_1] THEN MAP_EVERY X_GEN_TAC [`z:real^2`; `j:num`] THEN
      STRIP_TAC THEN SUBGOAL_THEN `j = 1` SUBST1_TAC THENL
       [ASM_ARITH_TAC; ASM_REWRITE_TAC[GSYM drop; LIFT_DROP]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(\z. lift((Fv:real^2->real) z)) absolutely_integrable_on A'` ASSUME_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
      ALL_TAC] THEN
    REWRITE_TAC[INTEGRAL_RESTRICT_UNIV; INTEGRABLE_RESTRICT_UNIV] THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN CONJ_TAC THENL
     [GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    REWRITE_TAC[wan_lloc] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(:real^2)` THEN ASM_SIMP_TAC[SUBSET_UNIV; LEBESGUE_MEASURABLE_COMPACT] THEN
    ASM_REWRITE_TAC[ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV];
    ALL_TAC] THEN
  (* M is in L^2 on A *)
  SUBGOAL_THEN `hmrm_vr h (u0:real^2->real^K) IN lspace A (&2)` ASSUME_TAC THENL
   [USE_THEN "RA" (MP_TAC o SPEC `\z. norm((u0:real^2->real^K) z) pow 2`) THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[WAN_LSPACE2_SQNORM_INTEGRABLE]; STRIP_TAC] THEN
    USE_THEN "YG" (MP_TAC o SPECL
      [`h:real^2->real`; `\z. if z IN A' then norm((u0:real^2->real^K) z) pow 2 else &0`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MATCH_MP_TAC WAN_L2_BOUND_LSPACE THEN
    EXISTS_TAC `\x. hmrm_ka h (\z. if z IN A' then norm((u0:real^2->real^K) z) pow 2
                                   else &0) x` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[SUBSET_UNIV] THEN
      MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[DIMINDEX_1] THEN MAP_EVERY X_GEN_TAC [`z:real^2`; `j:num`] THEN
      STRIP_TAC THEN SUBGOAL_THEN `j = 1` SUBST1_TAC THENL
       [ASM_ARITH_TAC; REWRITE_TAC[GSYM drop; LIFT_DROP]] THEN
      MATCH_MP_TAC HMRM_KA_POS THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `hmrm_ka h (\z. norm((u0:real^2->real^K) z) pow 2) x` THEN CONJ_TAC THENL
     [MATCH_MP_TAC HMRM_VR_JENSEN THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC HMRM_KA_LOCAL THEN
      EXISTS_TAC `A':real^2->bool` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  (* L^2 convergence of M_n to M on A *)
  SUBGOAL_THEN
   `!n. drop(integral A (\x. lift(norm(hmrm_vr h ((w:num->real^2->real^K) n) x -
                                       hmrm_vr h u0 x) pow 2))) <=
        Cy * drop(integral k (\z. lift(norm(w n z - u z) pow 2)))`
  (LABEL_TAC "LN") THENL
   [GEN_TAC THEN
    USE_THEN "RA" (MP_TAC o SPEC `\z. norm((w:num->real^2->real^K) n z - u0 z) pow 2`) THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[WAN_LSPACE2_SQNORM_INTEGRABLE]; STRIP_TAC] THEN
    USE_THEN "YG" (MP_TAC o SPECL
      [`h:real^2->real`;
       `\z. if z IN A' then norm((w:num->real^2->real^K) n z - u0 z) pow 2 else &0`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[] THEN STRIP_TAC] THEN
    ABBREV_TAC
     `Hn = \x. hmrm_ka h (\z. if z IN A' then norm((w:num->real^2->real^K) n z - u0 z) pow 2
                             else &0) x` THEN
    SUBGOAL_THEN `!x. &0 <= (Hn:real^2->real) x` ASSUME_TAC THENL
     [GEN_TAC THEN EXPAND_TAC "Hn" THEN REWRITE_TAC[] THEN MATCH_MP_TAC HMRM_KA_POS THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(\x. lift((Hn:real^2->real) x)) integrable_on (:real^2)` ASSUME_TAC THENL
     [EXPAND_TAC "Hn" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(\x. lift((Hn:real^2->real) x)) integrable_on A` ASSUME_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[SUBSET_UNIV] THEN
      MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[DIMINDEX_1] THEN MAP_EVERY X_GEN_TAC [`z:real^2`; `j:num`] THEN
      STRIP_TAC THEN SUBGOAL_THEN `j = 1` SUBST1_TAC THENL
       [ASM_ARITH_TAC; ASM_REWRITE_TAC[GSYM drop; LIFT_DROP]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!x. x IN A
          ==> norm(hmrm_vr h ((w:num->real^2->real^K) n) x - hmrm_vr h u0 x) pow 2 <=
              (Hn:real^2->real) x`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN EXPAND_TAC "Hn" THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `hmrm_ka h (\z. norm((w:num->real^2->real^K) n z - u0 z) pow 2) x` THEN
      CONJ_TAC THENL
       [USE_THEN "JX" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC HMRM_KA_LOCAL THEN
        EXISTS_TAC `A':real^2->bool` THEN ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\x. hmrm_vr h ((w:num->real^2->real^K) n) x - hmrm_vr h u0 x) IN lspace A (&2)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC WAN_L2_BOUND_LSPACE THEN EXISTS_TAC `Hn:real^2->real` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MEASURABLE_ON_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_SIMP_TAC[SUBSET_UNIV; HMRM_SMOOTH_CONT; HMRM_VR_SMOOTH];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `drop(integral A (\x. lift((Hn:real^2->real) x)))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_SIMP_TAC[WAN_LSPACE2_SQNORM_INTEGRABLE] THEN
      ASM_SIMP_TAC[LIFT_DROP];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `drop(integral (:real^2) (\x. lift((Hn:real^2->real) x)))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN ASM_SIMP_TAC[SUBSET_UNIV; LIFT_DROP];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `Cy * drop(integral (:real^2)
                  (\z. lift(if z IN A' then norm((w:num->real^2->real^K) n z - u0 z) pow 2
                            else &0)))` THEN
    CONJ_TAC THENL [EXPAND_TAC "Hn" THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; USE_THEN "AK" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[]];
    ALL_TAC] THEN
  (* the energy densities of the approximating maps *)
  SUBGOAL_THEN
   `!n i. 1 <= i /\ i <= 2
          ==> (\z. partial_derivative i ((w:num->real^2->real^K) n) z) continuous_on (:real^2) /\
              (\z. partial_derivative i (w n) z) IN lspace (:real^2) (&2)`
  (LABEL_TAC "PW") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "wt" (MP_TAC o SPEC `n:num`) THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [wan_vtest] THEN
    DISCH_THEN(X_CHOOSE_THEN `kw:real^2->bool` STRIP_ASSUME_TAC o CONJUNCT2) THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `(w:num->real^2->real^K) n`; `kw:real^2->bool`; `i:num`]
                  WAN_VTEST_PARTIAL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC WAN_SOB_LSPACE_ZERO_EXT THEN EXISTS_TAC `kw:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC HMRM_CONT_LSPACE2 THEN EXISTS_TAC `kw:real^2->bool` THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT; SUBSET_REFL] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    ALL_TAC] THEN
  (* the energy of M_n on A *)
  SUBGOAL_THEN
   `!n. wan_w12 A (hmrm_vr h ((w:num->real^2->real^K) n)) /\
        wan_dir A (hmrm_vr h (w n)) <=
        &9 * Cy * drop(integral A' (\z. lift(norm(partial_derivative 1 (w n) z) pow 2 +
                                            norm(partial_derivative 2 (w n) z) pow 2)))`
  (LABEL_TAC "EN") THENL
   [GEN_TAC THEN
    ABBREV_TAC
     `en = \z. norm(partial_derivative 1 ((w:num->real^2->real^K) n) z) pow 2 +
               norm(partial_derivative 2 (w n) z) pow 2` THEN
    SUBGOAL_THEN
     `drop(integral A' (\z. lift(norm(partial_derivative 1 ((w:num->real^2->real^K) n) z) pow 2 +
                                norm(partial_derivative 2 (w n) z) pow 2))) =
      drop(integral A' (\z. lift((en:real^2->real) z)))`
    SUBST1_TAC THENL [EXPAND_TAC "en" THEN REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(!z. &0 <= (en:real^2->real) z) /\ (\z. lift(en z)) integrable_on (:real^2)`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "en" THEN SIMP_TAC[REAL_LE_ADD; REAL_LE_POW_2] THEN REWRITE_TAC[LIFT_ADD] THEN
      MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THEN
      MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THENL
       [USE_THEN "PW" (MP_TAC o SPECL [`n:num`; `1`]);
        USE_THEN "PW" (MP_TAC o SPECL [`n:num`; `2`])] THEN
      CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
      ALL_TAC] THEN
    USE_THEN "RA" (MP_TAC o SPEC `en:real^2->real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[] THEN STRIP_TAC] THEN
    USE_THEN "YG" (MP_TAC o SPECL
      [`h:real^2->real`; `\z. if z IN A' then (en:real^2->real) z else &0`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[] THEN STRIP_TAC] THEN
    SUBGOAL_THEN `smooth_map_on (:real^2) (hmrm_vr h ((w:num->real^2->real^K) n))`
    ASSUME_TAC THENL [ASM_SIMP_TAC[HMRM_VR_SMOOTH]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!i. (\x. partial_derivative i (hmrm_vr h ((w:num->real^2->real^K) n)) x)
          continuous_on (:real^2)`
    ASSUME_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC HMRM_SMOOTH_CONT THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN ASM_REWRITE_TAC[OPEN_UNIV];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!i. (\x. partial_derivative i (hmrm_vr h ((w:num->real^2->real^K) n)) x)
          IN lspace A (&2)`
    (LABEL_TAC "PL") THENL
     [GEN_TAC THEN MATCH_MP_TAC HMRM_CONT_LSPACE2 THEN
      EXISTS_TAC `k:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`A:real^2->bool`; `hmrm_vr h ((w:num->real^2->real^K) n)`]
      (REWRITE_RULE[WAN_W12_C1_STATEMENT] (ISPECL [`(:2)`; `(:K)`] WAN_W12_C1))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[DIMINDEX_2] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
        ASM_MESON_TAC[smooth_map_on; SUBSET_UNIV];
        MATCH_MP_TAC HMRM_CONT_LSPACE2 THEN EXISTS_TAC `k:real^2->bool` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `(:real^2)` THEN ASM_SIMP_TAC[HMRM_SMOOTH_CONT; SUBSET_UNIV]];
      REWRITE_TAC[DIMINDEX_2] THEN STRIP_TAC] THEN
    ASM_REWRITE_TAC[SUM_2] THEN
    MP_TAC(ISPECL [`h:real^2->real`; `(w:num->real^2->real^K) n`] HMRM_VR_PARTIAL_BOUND) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(LABEL_TAC "PB")] THEN
    ABBREV_TAC
     `G = \x. hmrm_ka h (\z. if z IN A' then (en:real^2->real) z else &0) x` THEN
    SUBGOAL_THEN
     `!x. x IN A
          ==> norm(partial_derivative 1 (hmrm_vr h ((w:num->real^2->real^K) n)) x) pow 2 +
              norm(partial_derivative 2 (hmrm_vr h (w n)) x) pow 2 <= &9 * (G:real^2->real) x`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN EXPAND_TAC "G" THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `hmrm_ka h (\z. if z IN A' then (en:real^2->real) z else &0) x = hmrm_ka h en x`
      SUBST1_TAC THENL
       [MATCH_MP_TAC HMRM_KA_LOCAL THEN EXISTS_TAC `A':real^2->bool` THEN ASM_SIMP_TAC[];
        ALL_TAC] THEN
      EXPAND_TAC "en" THEN
      USE_THEN "PB" (MP_TAC o SPECL [`x:real^2`; `1`]) THEN
      USE_THEN "PB" (MP_TAC o SPECL [`x:real^2`; `2`]) THEN
      CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `!x. &0 <= (G:real^2->real) x` ASSUME_TAC THENL
     [GEN_TAC THEN EXPAND_TAC "G" THEN REWRITE_TAC[] THEN MATCH_MP_TAC HMRM_KA_POS THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(\x. lift((G:real^2->real) x)) integrable_on (:real^2) /\
                  drop(integral (:real^2) (\x. lift(G x))) <=
                  Cy * drop(integral A' (\z. lift((en:real^2->real) z)))`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "G" THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(\x. lift((G:real^2->real) x)) integrable_on A` ASSUME_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      EXISTS_TAC `(:real^2)` THEN ASM_REWRITE_TAC[SUBSET_UNIV] THEN
      MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[DIMINDEX_1] THEN MAP_EVERY X_GEN_TAC [`z:real^2`; `j:num`] THEN
      STRIP_TAC THEN SUBGOAL_THEN `j = 1` SUBST1_TAC THENL
       [ASM_ARITH_TAC; ASM_REWRITE_TAC[GSYM drop; LIFT_DROP]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`A:real^2->bool`;
                   `\x. partial_derivative 1 (hmrm_vr h ((w:num->real^2->real^K) n)) x`]
                  WAN_LSPACE2_SQNORM_INTEGRABLE) THEN
    MP_TAC(ISPECL [`A:real^2->bool`;
                   `\x. partial_derivative 2 (hmrm_vr h ((w:num->real^2->real^K) n)) x`]
                  WAN_LSPACE2_SQNORM_INTEGRABLE) THEN
    USE_THEN "PL" (fun th -> REWRITE_TAC[th]) THEN REPEAT DISCH_TAC THEN
    ASM_SIMP_TAC[GSYM DROP_ADD; GSYM INTEGRAL_ADD] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `drop(integral A (\x. lift(&9 * (G:real^2->real) x)))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_DROP_LE THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[DROP_ADD; LIFT_DROP]];
      ALL_TAC] THEN
    REWRITE_TAC[LIFT_CMUL] THEN ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `drop(integral (:real^2) (\x. lift((G:real^2->real) x)))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
    ASM_SIMP_TAC[SUBSET_UNIV; LIFT_DROP];
    ALL_TAC] THEN
  (* convergence of the energies of the approximating maps on A' *)
  SUBGOAL_THEN
   `((\n. drop(integral A'
             (\z. lift(norm(partial_derivative 1 ((w:num->real^2->real^K) n) z) pow 2 +
                       norm(partial_derivative 2 (w n) z) pow 2)))) --->
     drop(integral A' (\x. lift(norm(wan_wd s 1 (u:real^2->real^K) x) pow 2 + norm(wan_wd s 2 u x) pow 2))))
    sequentially`
  (LABEL_TAC "EC") THENL
   [MP_TAC(ISPECL [`\n. partial_derivative 1 ((w:num->real^2->real^K) n)`;
                   `\n. partial_derivative 2 ((w:num->real^2->real^K) n)`;
                   `wan_wd s 1 (u:real^2->real^K)`; `wan_wd s 2 (u:real^2->real^K)`;
                   `k:real^2->bool`; `A':real^2->bool`] HMRM_L2SQ_CONV2) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT; WAN_WD_WORKS; DIMINDEX_2; ARITH];
      MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT; WAN_WD_WORKS; DIMINDEX_2; ARITH];
      GEN_TAC THEN MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT; SUBSET_UNIV] THEN
      USE_THEN "PW" (MP_TAC o SPECL [`n:num`; `1`]) THEN CONV_TAC NUM_REDUCE_CONV THEN
      SIMP_TAC[ETA_AX];
      GEN_TAC THEN MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT; SUBSET_UNIV] THEN
      USE_THEN "PW" (MP_TAC o SPECL [`n:num`; `2`]) THEN CONV_TAC NUM_REDUCE_CONV THEN
      SIMP_TAC[ETA_AX];
      USE_THEN "w1" (MP_TAC o SPEC `1`) THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
      USE_THEN "w1" (MP_TAC o SPEC `2`) THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  (* lower semicontinuity applied to the tails of the sequence *)
  SUBGOAL_THEN
   `!d. &0 < d
        ==> wan_w12 A (hmrm_vr h (u0:real^2->real^K)) /\
            wan_dir A (hmrm_vr h u0) <=
            (&9 * Cy) * drop(integral A' (\x. lift(norm(wan_wd s 1 (u:real^2->real^K) x) pow 2 +
                                                  norm(wan_wd s 2 u x) pow 2))) + d`
  (LABEL_TAC "DL") THENL
   [X_GEN_TAC `d:real` THEN DISCH_TAC THEN
    USE_THEN "EC" (MP_TAC o SPEC `&9 * Cy` o MATCH_MP REALLIM_LMUL) THEN
    REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN DISCH_THEN(MP_TAC o SPEC `d:real`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "NN")) THEN
    MP_TAC(ISPECL [`A:real^2->bool`; `\n. hmrm_vr h ((w:num->real^2->real^K) (n + N))`;
                   `hmrm_vr h (u0:real^2->real^K)`;
                   `(&9 * Cy) * drop(integral A' (\x. lift(norm(wan_wd s 1 (u:real^2->real^K) x)
                                                       pow 2 +
                                                       norm(wan_wd s 2 u x) pow 2))) + d`]
      (REWRITE_RULE[WAN_DIR_LSC_STATEMENT] (ISPECL [`(:2)`; `(:K)`] WAN_DIR_LSC))) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      X_GEN_TAC `n:num` THEN USE_THEN "EN" (MP_TAC o SPEC `n + N:num`) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "NN" (MP_TAC o SPEC `n + N:num`) THEN
      ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC
       `wan_dir A (hmrm_vr h ((w:num->real^2->real^K) (n + N))) <=
        &9 * Cy * drop(integral A' (\z. lift(norm(partial_derivative 1 (w (n + N)) z) pow 2 +
                                            norm(partial_derivative 2 (w (n + N)) z) pow 2)))` THEN
      REAL_ARITH_TAC;
      ASM_REWRITE_TAC[];
      X_GEN_TAC `k':real^2->bool` THEN STRIP_TAC THEN
      MATCH_MP_TAC HMRM_REALLIM_FROM_SQ THEN
      MAP_EVERY EXISTS_TAC
       [`Cy:real`;
        `\n. drop(integral k (\z. lift(norm((w:num->real^2->real^K) (n + N) z - u z) pow 2)))`] THEN
      REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        X_GEN_TAC `n:num` THEN
        SUBGOAL_THEN
         `(\x. hmrm_vr h ((w:num->real^2->real^K) (n + N)) x - hmrm_vr h u0 x) IN lspace A (&2)`
        ASSUME_TAC THENL
         [MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN
          CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
          USE_THEN "EN" (MP_TAC o SPEC `n + N:num`) THEN SIMP_TAC[wan_w12];
          ALL_TAC] THEN
        SUBGOAL_THEN
         `(\x. hmrm_vr h ((w:num->real^2->real^K) (n + N)) x - hmrm_vr h u0 x)
          IN lspace k' (&2)`
        ASSUME_TAC THENL
         [MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `A:real^2->bool` THEN
          ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT];
          ALL_TAC] THEN
        CONJ_TAC THENL [MATCH_MP_TAC LNORM_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        ASM_SIMP_TAC[WAN_SOB_LNORM2_SQ] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC
         `drop(integral A (\x. lift(norm(hmrm_vr h ((w:num->real^2->real^K) (n + N)) x -
                                        hmrm_vr h u0 x) pow 2)))` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
          ASM_SIMP_TAC[WAN_LSPACE2_SQNORM_INTEGRABLE; LIFT_DROP; REAL_LE_POW_2];
          USE_THEN "LN" (MP_TAC o SPEC `n + N:num`) THEN REWRITE_TAC[]];
        MP_TAC(ISPECL
         [`\n. drop(integral k (\z. lift(norm((w:num->real^2->real^K) n z - u z) pow 2)))`;
          `&0`; `N:num`] REAL_SEQ_OFFSET) THEN
        REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN USE_THEN "w0" ACCEPT_TAC]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [USE_THEN "DL" (MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN SIMP_TAC[];
    MATCH_MP_TAC HMRM_EPS_LE THEN X_GEN_TAC `d:real` THEN DISCH_TAC THEN
    USE_THEN "DL" (MP_TAC o SPEC `d:real`) THEN ASM_SIMP_TAC[]]);;

(* ========================================================================= *)
(* The mollification of a map with values a.e. in a closed set S stays close *)
(* to S: by Jensen, the kernel bound and the Poincare inequality on          *)
(* ball(x,h x),                                                              *)
(*   dist(M x, closest_point S (M x))^2 <= C wan_dir (ball(x,h x)) u.       *)
(* Also: the Dirichlet integral on an open subset in terms of the weak      *)
(* partials on the big set.                                                  *)
(* ========================================================================= *)

let HMRM_VR_CONST = prove
 (`!(h:real^2->real) (c:real^K) x. hmrm_vr h (\z. c) x = c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hmrm_vr] THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MP_TAC(ISPECL [`\y:real^2. lift(wan_mk y)`; `lift(&1)`; `(:real^2)`;
                 `\v:real^1. drop v % (c:real^K)`] HAS_INTEGRAL_LINEAR) THEN
  REWRITE_TAC[o_DEF; LIFT_DROP; VECTOR_MUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[WAN_MK_PROPS] THEN REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN
  VECTOR_ARITH_TAC);;

let HMRM_VR_AVG_BOUND = prove
 (`!(h:real^2->real) (f:real^2->real^K) x Bm.
     &0 < h x /\ (!w:real^2. wan_mk w <= Bm) /\ wan_lloc (:real^2) f /\
     wan_lloc (:real^2) (\z. lift(norm(f z) pow 2))
     ==> norm(hmrm_vr h f x) pow 2 <=
         Bm * inv(h x) pow 2 * drop(integral (ball(x,h x)) (\z. lift(norm(f z) pow 2)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `hmrm_ka h (\z. norm((f:real^2->real^K) z) pow 2) x` THEN CONJ_TAC THENL
   [MATCH_MP_TAC HMRM_VR_JENSEN THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  MATCH_MP_TAC HMRM_KA_KERNEL_BOUND THEN ASM_REWRITE_TAC[SUBSET_REFL; REAL_LE_POW_2] THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
  EXISTS_TAC `cball(x:real^2,h x)` THEN
  REWRITE_TAC[BALL_SUBSET_CBALL; LEBESGUE_MEASURABLE_BALL] THEN
  UNDISCH_TAC `wan_lloc (:real^2) (\z. lift(norm((f:real^2->real^K) z) pow 2))` THEN
  REWRITE_TAC[wan_lloc] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[COMPACT_CBALL; SUBSET_UNIV]);;

(* Averaging the pointwise bound dist(m,S) <= |m - u y| over a set where u  *)
(* takes values in S a.e.                                                    *)

let HMRM_NEAR_AVG = prove
 (`!(S:real^K->bool) (u:real^2->real^K) B Z m c.
     closed S /\ measurable B /\ negligible Z /\ u IN lspace B (&2) /\
     (!y. y IN B DIFF Z ==> u y IN S)
     ==> measure B * dist(m,closest_point S m) pow 2 <=
         &2 * measure B * norm(m - c) pow 2 +
         &2 * drop(integral B (\y. lift(norm(u y - c) pow 2)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\y. (u:real^2->real^K) y - c) IN lspace B (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC LSPACE_SUB THEN ASM_SIMP_TAC[LSPACE_CONST; ETA_AX] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\y. lift(norm((u:real^2->real^K) y - c) pow 2)) integrable_on B`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP WAN_LSPACE2_SQNORM_INTEGRABLE) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!d:real. ((\y:real^2. lift d) has_integral (measure B % lift d)) B`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_CONST_GEN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `e = dist(m:real^K,closest_point S m) pow 2` THEN
  ABBREV_TAC `q = norm(m - c:real^K) pow 2` THEN
  MP_TAC(ISPECL [`(\y. lift e):real^2->real^1`;
                 `\y. lift(&2 * q) + &2 % lift(norm((u:real^2->real^K) y - c) pow 2)`;
                 `B:real^2->bool`; `Z:real^2->bool`] INTEGRAL_DROP_LE_AE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[integrable_on];
      MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
       [ASM_MESON_TAC[integrable_on]; MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    REWRITE_TAC[DROP_ADD; DROP_CMUL; LIFT_DROP] THEN
    SUBGOAL_THEN `(u:real^2->real^K) y IN S` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `dist(m:real^K,closest_point S m) <= dist(m,u(y:real^2))` ASSUME_TAC THENL
     [MATCH_MP_TAC CLOSEST_POINT_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `dist(m:real^K,u(y:real^2)) <= norm(m - c:real^K) + norm(u y - c)`
    ASSUME_TAC THENL [NORM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`norm(m - c:real^K)`; `norm((u:real^2->real^K) y - c)`] HMRM_SQ_SUM_LE) THEN
    MAP_EVERY EXPAND_TAC ["e"; "q"] THEN
    ABBREV_TAC `d1 = dist(m:real^K,closest_point S m)` THEN
    ABBREV_TAC `a1 = norm(m - c:real^K)` THEN
    ABBREV_TAC `b1 = norm((u:real^2->real^K) y - c)` THEN
    SUBGOAL_THEN `&0 <= d1` ASSUME_TAC THENL
     [EXPAND_TAC "d1" THEN REWRITE_TAC[DIST_POS_LE]; ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(a1 + b1) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `integral B ((\y. lift e):real^2->real^1) = measure B % lift e` SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_UNIQUE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `integral B (\y. lift(&2 * q) + &2 % lift(norm((u:real^2->real^K) y - c) pow 2)) =
    measure B % lift(&2 * q) + &2 % integral B (\y. lift(norm(u y - c) pow 2))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_UNIQUE THEN MATCH_MP_TAC HAS_INTEGRAL_ADD THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HAS_INTEGRAL_CMUL THEN
    ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL];
    ALL_TAC] THEN
  REWRITE_TAC[DROP_ADD; DROP_CMUL; LIFT_DROP] THEN REAL_ARITH_TAC);;

(* The Dirichlet integral on an open subset t of s through the weak         *)
(* partials on s.                                                             *)

let HMRM_DIR_RESTRICT = prove
 (`!(s:real^2->bool) t (u:real^2->real^K).
     open t /\ t SUBSET s /\ wan_w12 s u
     ==> wan_dir t u =
         drop(integral t (\x. lift(norm(wan_wd s 1 u x) pow 2 + norm(wan_wd s 2 u x) pow 2)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `t:real^2->bool`; `u:real^2->real^K`; `1`]
                WAN_WD_RESTRICT) THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `t:real^2->bool`; `u:real^2->real^K`; `2`]
                WAN_WD_RESTRICT) THEN
  ASM_REWRITE_TAC[DIMINDEX_2; ARITH] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[WAN_DIR_2D_EQ] THEN AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE THEN
  EXISTS_TAC `{x | x IN t /\ ~(wan_wd t 1 (u:real^2->real^K) x = wan_wd s 1 u x)} UNION
              {x | x IN t /\ ~(wan_wd t 2 (u:real^2->real^K) x = wan_wd s 2 u x)}` THEN
  ASM_SIMP_TAC[NEGLIGIBLE_UNION] THEN
  REWRITE_TAC[IN_DIFF; IN_UNION; IN_ELIM_THM; DE_MORGAN_THM] THEN
  X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_wd t 1 (u:real^2->real^K) x = wan_wd s 1 u x /\
                wan_wd t 2 (u:real^2->real^K) x = wan_wd s 2 u x`
  (fun th -> REWRITE_TAC[th]) THEN
  ASM_MESON_TAC[]);;

(* The mollification at a point with h x > 0 is close to S.                *)

let HMRM_VR_NEAR = prove
 (`?C. &0 < C /\
     !(S:real^K->bool) (u:real^2->real^K) s (h:real^2->real) x.
       closed S /\ open s /\ wan_w12 s u /\
       (?Z. negligible Z /\ !y. y IN s DIFF Z ==> u y IN S) /\
       &0 < h x /\ ball(x,h x) SUBSET s
       ==> dist(hmrm_vr h (\y. if y IN s then u y else vec 0) x,
                closest_point S (hmrm_vr h (\y. if y IN s then u y else vec 0) x)) pow 2
           <= C * wan_dir (ball(x,h x)) u`,
  MP_TAC(INST_TYPE [`:2`,`:M`] WAN_MK_BOUND) THEN
  DISCH_THEN(X_CHOOSE_THEN `Bm:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `M1 = measure(ball(vec 0:real^2,&1))` THEN
  SUBGOAL_THEN `&0 < M1` ASSUME_TAC THENL
   [EXPAND_TAC "M1" THEN REWRITE_TAC[MEASURE_BALL_POS; REAL_LT_01]; ALL_TAC] THEN
  EXISTS_TAC `&32 * Bm + &32 * inv M1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
     (X_CHOOSE_THEN `Z:real^2->bool` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC)))) THEN
  ABBREV_TAC `u0 = \y:real^2. if y IN s then (u:real^2->real^K) y else vec 0` THEN
  ABBREV_TAC `t = (h:real^2->real) x` THEN
  SUBGOAL_THEN `measure(ball(x:real^2,t)) = t pow 2 * M1` ASSUME_TAC THENL
   [EXPAND_TAC "M1" THEN MATCH_MP_TAC HMRM_MEASURE_BALL2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 (ball(x:real^2,t)) (u:real^2->real^K)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_W12_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  ABBREV_TAC `c = inv(measure(ball(x:real^2,t))) % integral (ball(x,t)) (u:real^2->real^K)` THEN
  ABBREV_TAC `D = wan_dir (ball(x:real^2,t)) (u:real^2->real^K)` THEN
  SUBGOAL_THEN `&0 <= D` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC WAN_DIR_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Poincare *)
  SUBGOAL_THEN
   `drop(integral (ball(x:real^2,t)) (\y. lift(norm((u:real^2->real^K) y - c) pow 2))) <=
    &16 * t pow 2 * D`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`x:real^2`; `t:real`; `u:real^2->real^K`] WAN_POINCARE_BALL_BOUND) THEN
    ASM_REWRITE_TAC[DIMINDEX_2] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* local integrability of u0 - c and of its square norm *)
  SUBGOAL_THEN `(u0:real^2->real^K) IN lspace (:real^2) (&2)` ASSUME_TAC THENL
   [EXPAND_TAC "u0" THEN ASM_SIMP_TAC[WAN_LSPACE_RESTRICT_UNIV; REAL_ARITH `&0 < &2`] THEN
    ASM_SIMP_TAC[WAN_W12_IMP_LSPACE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. compact k ==> (\y. (u0:real^2->real^K) y - c) IN lspace k (&2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LSPACE_SUB THEN
    ASM_SIMP_TAC[LSPACE_CONST; MEASURABLE_COMPACT; ETA_AX] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT; SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_lloc (:real^2) (\y. (u0:real^2->real^K) y - c) /\
                wan_lloc (:real^2) (\y. lift(norm((u0:real^2->real^K) y - c) pow 2))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[wan_lloc] THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `(\y. (u0:real^2->real^K) y - c) IN lspace k (&1)` MP_TAC THENL
       [MATCH_MP_TAC LSPACE_MONO THEN EXISTS_TAC `&2` THEN
        ASM_SIMP_TAC[MEASURABLE_COMPACT] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
        REWRITE_TAC[LSPACE_1; IN_ELIM_THM]];
      ALL_TAC] THEN
    REWRITE_TAC[wan_lloc] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN CONJ_TAC THENL
     [REWRITE_TAC[DIMINDEX_1] THEN MAP_EVERY X_GEN_TAC [`z:real^2`; `j:num`] THEN
      STRIP_TAC THEN SUBGOAL_THEN `j = 1` SUBST1_TAC THENL
       [ASM_ARITH_TAC; REWRITE_TAC[GSYM drop; LIFT_DROP; REAL_LE_POW_2]];
      FIRST_X_ASSUM(MP_TAC o SPEC `k:real^2->bool`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o MATCH_MP WAN_LSPACE2_SQNORM_INTEGRABLE) THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the distance of M x to the average *)
  SUBGOAL_THEN `norm(hmrm_vr h (u0:real^2->real^K) x - c) pow 2 <= &16 * Bm * D`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `hmrm_vr h (u0:real^2->real^K) x - c = hmrm_vr h (\y. u0 y - c) x`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL [`h:real^2->real`; `u0:real^2->real^K`; `(\y. c):real^2->real^K`;
                     `x:real^2`] HMRM_VR_SUB) THEN
      REWRITE_TAC[HMRM_VR_CONST] THEN ANTS_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_IMP_LE; WAN_LSPACE2_IMP_LLOC; WAN_CONTINUOUS_LLOC;
                     CONTINUOUS_ON_CONST];
        DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`h:real^2->real`; `\y. (u0:real^2->real^K) y - c`; `x:real^2`; `Bm:real`]
                  HMRM_VR_AVG_BOUND) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `integral (ball(x:real^2,t)) (\z. lift(norm((u0:real^2->real^K) z - c) pow 2)) =
      integral (ball(x,t)) (\z. lift(norm((u:real^2->real^K) z - c) pow 2))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
      EXPAND_TAC "u0" THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `(z:real^2) IN s` (fun th -> REWRITE_TAC[th]) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `Bm * inv t pow 2 * &16 * t pow 2 * D` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `Bm * inv t pow 2 *
                  drop(integral (ball(x:real^2,t))
                         (\z. lift(norm((u:real^2->real^K) z - c) pow 2)))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  (* averaging over the ball *)
  MP_TAC(ISPECL [`S:real^K->bool`; `u:real^2->real^K`; `ball(x:real^2,t)`; `Z:real^2->bool`;
                 `hmrm_vr h (u0:real^2->real^K) x`; `c:real^K`] HMRM_NEAR_AVG) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MEASURABLE_BALL; WAN_W12_IMP_LSPACE] THEN
    REWRITE_TAC[IN_DIFF] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `e = dist(hmrm_vr h (u0:real^2->real^K) x,
                       closest_point S (hmrm_vr h u0 x)) pow 2` THEN
  ABBREV_TAC `q = norm(hmrm_vr h (u0:real^2->real^K) x - c) pow 2` THEN
  ABBREV_TAC `P = drop(integral (ball(x:real^2,t))
                         (\y. lift(norm((u:real^2->real^K) y - c) pow 2)))` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 < t pow 2 * M1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `t pow 2 * M1` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * (t pow 2 * M1) * q + &2 * P` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(t pow 2 * M1) * (&32 * Bm + &32 * inv M1) * D =
    &2 * (t pow 2 * M1) * (&16 * Bm * D) + &2 * (&16 * t pow 2 * D)`
  SUBST1_TAC THENL [UNDISCH_TAC `&0 < M1` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The radius function of the hole-filling competitor, h(x) = c0 e           *)
(* smooth_bump e (2e) (x - b): smooth, between 0 and c0 e, equal to c0 e on  *)
(* cball(b,e), zero off ball(b,2e), and with derivative bounded by 1/2 (c0   *)
(* universal, c0 <= 1/4).                                                    *)
(* ========================================================================= *)

let HMRM_FD_CMUL = prove
 (`!(f:real^N->real^1) c x.
     f differentiable (at x)
     ==> !v. frechet_derivative (\y. c % f y) (at x) v = c % frechet_derivative f (at x) v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FRECHET_DERIVATIVE_WORKS] THEN
  DISCH_THEN(MP_TAC o SPEC `c:real` o MATCH_MP HAS_DERIVATIVE_CMUL) THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN REWRITE_TAC[]);;

let HMRM_H_CUTOFF = prove
 (`?c0. &0 < c0 /\ c0 <= &1 / &4 /\
        !(b:real^N) e.
          &0 < e
          ==> smooth_map_on (:real^N) (\x. lift(c0 * e * smooth_bump e (&2 * e) (x - b))) /\
              (!x. &0 <= c0 * e * smooth_bump e (&2 * e) (x - b) /\
                   c0 * e * smooth_bump e (&2 * e) (x - b) <= c0 * e) /\
              (!x. norm(x - b) <= e ==> c0 * e * smooth_bump e (&2 * e) (x - b) = c0 * e) /\
              (!x. &2 * e <= norm(x - b) ==> c0 * e * smooth_bump e (&2 * e) (x - b) = &0) /\
              (!x v. abs(drop(frechet_derivative
                              (\x. lift(c0 * e * smooth_bump e (&2 * e) (x - b))) (at x) v))
                     <= norm v / &2)`,
  X_CHOOSE_THEN `Bc:real` STRIP_ASSUME_TAC (INST_TYPE [`:N`,`:N`] WAN_POINT_CUTOFF_DBOUND) THEN
  EXISTS_TAC `inv(&4 * (Bc + &1))` THEN
  SUBGOAL_THEN `&0 < &4 * (Bc + &1)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `&4 * (Bc + &1)` THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv(&4 * (Bc + &1)) /\ inv(&4 * (Bc + &1)) * Bc <= &1 / &2`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV_EQ] THEN
    ASM_SIMP_TAC[REAL_FIELD `&0 < a ==> inv a * b = b / a`; REAL_LE_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `c0 = inv(&4 * (Bc + &1))` THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`b:real^N`; `e:real`] WAN_POINT_CUTOFF_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < c0 * e` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(c0 * e * smooth_bump e (&2 * e) (x - b))) =
    (\x:real^N. (c0 * e) % lift(smooth_bump e (&2 * e) (x - b)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; LIFT_CMUL; VECTOR_MUL_ASSOC]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[OPEN_UNIV];
    GEN_TAC THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ASM_SIMP_TAC[REAL_MUL_RID];
    ASM_SIMP_TAC[REAL_MUL_RZERO];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `v:real^N`] THEN
  SUBGOAL_THEN `(\y:real^N. lift(smooth_bump e (&2 * e) (y - b))) differentiable (at x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^N)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[BETA_RULE(MATCH_MP HMRM_FD_CMUL th)]) THEN
  REWRITE_TAC[DROP_CMUL; REAL_ABS_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(c0 * e) * Bc / e * norm(v:real^N)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c0 * e) * Bc / e * norm(v:real^N) = (c0 * Bc) * norm v` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < e` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 / &2 * norm(v:real^N)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE]; REAL_ARITH_TAC]);;

