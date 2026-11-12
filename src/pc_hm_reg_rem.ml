(* ========================================================================= *)
(* Unit pc_hm_reg_rem (a unit of the harmonic map regularity chain of        *)
(* pc_hm_regularity): removable point singularities of finite-energy         *)
(* harmonic maps (CM_REMOVABLE).  Route: the Pohozaev identity on circles    *)
(* around the point (radial and angular energies), the Sacks-Uhlenbeck       *)
(* comparison on dyadic annuli, geometric decay of the energy and of the     *)
(* oscillation, hence a limit at the point; the Euler-Lagrange identity      *)
(* extends across the point (2D capacity cutoffs of pc_wan_sob2), so the     *)
(* extension is weakly harmonic, and smooth by CM_REG01.                     *)
(* ========================================================================= *)

needs "src/pc_hm_reg_smth.ml";;
needs "src/pc_hm_reg_sph.ml";;

prioritize_real();;
type_invention_error := true;;

let HMRR_ELD_ZERO = prove
 (`!S (G:real^K->real^K^K) d p q.
     cm_target S G d /\ p IN S ==> hmrm_eld S G p q (vec 0) (vec 0) = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `p:real^K`; `q:real^K`;
                 `vec 0:real^K`; `vec 0:real^K`; `vec 0:real^K`; `vec 0:real^K`]
    HMRC_ELD_SUB) THEN
  ASM_REWRITE_TAC[VECTOR_SUB_REFL] THEN REAL_ARITH_TAC);;

let HMRR_CUTOFF_LOCAL = prove
 (`!(a:real^N) e x i.
     &0 < e /\ norm(x - a) < e
     ==> wan_dpart i (\y. smooth_bump e (&2 * e) (y - a)) x = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_dpart] THEN
  SUBGOAL_THEN `frechet_derivative (\y. lift(smooth_bump e (&2 * e) (y - a))) (at (x:real^N)) =
                (\h. vec 0:real^1)` (fun th -> REWRITE_TAC[th; DROP_VEC]) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
  MAP_EVERY EXISTS_TAC [`\y:real^N. lift(&1)`; `e - norm(x - a:real^N)`] THEN
  REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN
  MP_TAC(ISPECL [`a:real^N`; `e:real`] WAN_POINT_CUTOFF_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o el 2 o CONJUNCTS) THEN
  UNDISCH_TAC `dist(y:real^N,x) < e - norm(x - a)` THEN REWRITE_TAC[dist] THEN
  CONV_TAC NORM_ARITH);;

(* Moving an integral of a density in the weak partials to a smaller set. *)

let HMRR_INTEGRAL_TRANSFER = prove
 (`!(s:real^2->bool) t (u:real^2->real^K) i (Fd:real^2->real^K->real).
     open s /\ open t /\ t SUBSET s /\ wan_w12 s u /\ 1 <= i /\ i <= 2 /\
     (!x. x IN s DIFF t ==> Fd x (wan_wd s i u x) = &0)
     ==> integral t (\x. lift(Fd x (wan_wd t i u x))) =
         integral s (\x. lift(Fd x (wan_wd s i u x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `t:real^2->bool`; `u:real^2->real^K`; `i:num`]
    WAN_WD_RESTRICT) THEN
  ASM_REWRITE_TAC[DIMINDEX_2] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM INTEGRAL_RESTRICT_UNIV] THEN MATCH_MP_TAC INTEGRAL_SPIKE THEN
  EXISTS_TAC `{x | x IN t /\ ~(wan_wd t i (u:real^2->real^K) x = wan_wd s i u x)}` THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; IN_ELIM_THM] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(x:real^2) IN t` THENL
   [SUBGOAL_THEN `(x:real^2) IN s /\ wan_wd t i (u:real^2->real^K) x = wan_wd s i u x`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[]];
    ASM_CASES_TAC `(x:real^2) IN s` THEN ASM_SIMP_TAC[IN_DIFF; LIFT_NUM]]);;

(* The identity for tests vanishing near the point. *)

let HMRR_EL_PHIE = prove
 (`!S (G:real^K->real^K^K) d (u:real^2->real^K) a r s' (phi:real^2->real^K) e.
     cm_target S G d /\ &0 < r /\ cm_wharmonic S G (ball(a,r) DELETE a) u /\
     wan_w12 s' u /\ (!x. x IN s' ==> u x IN S) /\
     open s' /\ bounded s' /\ closure s' SUBSET ball(a,r) /\ wan_vtest s' phi /\ &0 < e
     ==> sum(1..2) (\i. drop(integral s'
           (\x. lift(hmrm_eld S G (u x) (wan_wd s' i u x)
                   ((&1 - smooth_bump e (&2 * e) (x - a)) % phi x)
                   (partial_derivative i
                      (\x. (&1 - smooth_bump e (&2 * e) (x - a)) % phi x) x))))) = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^2`; `e:real`] WAN_POINT_CUTOFF_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s':real^2->bool`; `phi:real^2->real^K`;
                 `\x:real^2. smooth_bump e (&2 * e) (x - a)`; `a:real^2`; `e:real`]
    WAN_VTEST_MUL_CUTOFF) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[IN_BALL] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `dist(a:real^2,x) < e` THEN REWRITE_TAC[dist] THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pd")) THEN
  (* vanishing near the point *)
  SUBGOAL_THEN
   `!i x. norm(x - a:real^2) < e
          ==> (&1 - smooth_bump e (&2 * e) (x - a)) % (phi:real^2->real^K) x = vec 0 /\
              partial_derivative i
                (\x. (&1 - smooth_bump e (&2 * e) (x - a)) % phi x) x = vec 0`
  (LABEL_TAC "zero") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN USE_THEN "pd" (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `smooth_bump e (&2 * e) (x - a:real^2) = &1` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> t = `&1`)) (concl th) &&
        can (find_term (fun t -> t = `e:real`)) (concl th) &&
        is_forall (concl th) && not(can (find_term (fun t -> t = `&0`)) (concl th)))) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`a:real^2`; `e:real`; `x:real^2`; `i:num`] HMRR_CUTOFF_LOCAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_SUB_REFL; VECTOR_MUL_LZERO; VECTOR_SUB_REFL];
    ALL_TAC] THEN
  (* the smaller open set *)
  ABBREV_TAC `t = (s':real^2->bool) DIFF cball(a,e / &2)` THEN
  SUBGOAL_THEN `open (t:real^2->bool) /\ bounded t /\ t SUBSET s' /\
                closure t SUBSET ball(a:real^2,r) DELETE a`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_DIFF THEN ASM_REWRITE_TAC[CLOSED_CBALL];
      MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `s':real^2->bool` THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; SET_TAC[]];
      SET_TAC[];
      SUBGOAL_THEN `closure((s':real^2->bool) DIFF cball(a,e / &2)) SUBSET
                    closure s' INTER {x | e / &2 <= norm(x - a)}` MP_TAC THENL
       [MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL
         [MP_TAC(ISPEC `s':real^2->bool` CLOSURE_SUBSET) THEN
          REWRITE_TAC[SUBSET; IN_DIFF; IN_INTER; IN_ELIM_THM; IN_CBALL; dist] THEN
          REPEAT STRIP_TAC THENL
           [ASM_SIMP_TAC[]; ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REAL_ARITH_TAC];
          MATCH_MP_TAC CLOSED_INTER THEN REWRITE_TAC[CLOSED_CLOSURE] THEN
          SUBGOAL_THEN `{x:real^2 | e / &2 <= norm(x - a)} = (:real^2) DIFF ball(a,e / &2)`
          SUBST1_TAC THENL
           [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_BALL; dist; REAL_NOT_LT] THEN
            X_GEN_TAC `y:real^2` THEN MP_TAC(ISPECL [`y:real^2`; `a:real^2`] NORM_SUB) THEN
            REAL_ARITH_TAC;
            REWRITE_TAC[GSYM OPEN_CLOSED; OPEN_BALL]]];
        UNDISCH_TAC `closure s' SUBSET ball(a:real^2,r)` THEN
        REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; IN_DELETE] THEN
        DISCH_TAC THEN DISCH_TAC THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        CONJ_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `e / &2 <= norm(a - a:real^2)` THEN
          REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN ASM_REAL_ARITH_TAC]]];
    ALL_TAC] THEN
  (* the test on t *)
  SUBGOAL_THEN `wan_vtest t (\x. (&1 - smooth_bump e (&2 * e) (x - a)) % (phi:real^2->real^K) x)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `wan_vtest (s' DIFF {a})
                   (\x. (&1 - smooth_bump e (&2 * e) (x - a)) % (phi:real^2->real^K) x)` THEN
    UNDISCH_TAC `wan_vtest s' (phi:real^2->real^K)` THEN
    REWRITE_TAC[wan_vtest] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:real^2->bool` STRIP_ASSUME_TAC)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `k DIFF ball(a:real^2,e)` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_DIFF THEN ASM_REWRITE_TAC[OPEN_BALL];
      EXPAND_TAC "t" THEN REWRITE_TAC[SUBSET; IN_DIFF; IN_BALL; IN_CBALL] THEN
      X_GEN_TAC `y:real^2` THEN STRIP_TAC THEN CONJ_TAC THENL
       [ASM SET_TAC[]; ASM_REAL_ARITH_TAC];
      X_GEN_TAC `y:real^2` THEN REWRITE_TAC[IN_DIFF; IN_BALL; DE_MORGAN_THM] THEN
      STRIP_TAC THENL
       [ASM_SIMP_TAC[VECTOR_MUL_RZERO];
        USE_THEN "zero" (MP_TAC o SPECL [`1`; `y:real^2`]) THEN
        ANTS_TAC THENL
         [UNDISCH_TAC `dist(a:real^2,y) < e` THEN REWRITE_TAC[dist] THEN CONV_TAC NORM_ARITH;
          SIMP_TAC[]]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                 `ball(a:real^2,r) DELETE a`; `u:real^2->real^K`; `t:real^2->bool`;
                 `\x. (&1 - smooth_bump e (&2 * e) (x - a)) % (phi:real^2->real^K) x`]
    HMRM_WHARMONIC_EL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN REMOVE_THEN "pd" (K ALL_TAC) THEN
  MP_TAC(ISPECL [`s':real^2->bool`; `t:real^2->bool`; `u:real^2->real^K`; `i:num`;
                 `\x q. hmrm_eld S G ((u:real^2->real^K) x) q
                          ((&1 - smooth_bump e (&2 * e) (x - a)) % (phi:real^2->real^K) x)
                          (partial_derivative i
                            (\x. (&1 - smooth_bump e (&2 * e) (x - a)) % phi x) x)`]
    HMRR_INTEGRAL_TRANSFER) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real^2` THEN EXPAND_TAC "t" THEN
  REWRITE_TAC[IN_DIFF; IN_CBALL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `dist(a:real^2,x) <= e / &2` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  USE_THEN "zero" (MP_TAC o SPECL [`i:num`; `x:real^2`]) THEN ANTS_TAC THENL
   [UNDISCH_TAC `dist(a:real^2,x) <= e / &2` THEN REWRITE_TAC[dist] THEN
    MP_TAC(ISPECL [`a:real^2`; `x:real^2`] NORM_SUB) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN (fun th -> REWRITE_TAC[th])) THEN
  MATCH_MP_TAC HMRR_ELD_ZERO THEN
  EXISTS_TAC `d:real` THEN ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* The divergence theorem on an annulus in polar form.  For a C^1 vector     *)
(* field V on an open set containing the closed annulus r1 <= |x - a| <= r2, *)
(* the integral of div V over the open annulus is the difference of the      *)
(* circle integrals of V(c) dot (c - a), c = wan_circ a r t.  Proof: polar   *)
(* Fubini (WAN_POLAR_ANNULUS), the polar form                                *)
(* r div V = d/dr (V.(c - a)) + d/dt (V.ie) of the divergence, the angular   *)
(* fundamental theorem (periodicity) and Fubini for continuous integrands    *)
(* with the radial fundamental theorem.                                      *)
(* ========================================================================= *)

(* The radial derivative integrand. *)

let hmrr_gr = new_definition
 `hmrr_gr (V:real^2->real^2) (a:real^2) r t =
    (Re(cexp(ii * Cx t)) % partial_derivative 1 V (a + Cx r * cexp(ii * Cx t)) +
     Im(cexp(ii * Cx t)) % partial_derivative 2 V (a + Cx r * cexp(ii * Cx t))) dot
    (Cx r * cexp(ii * Cx t)) +
    V(a + Cx r * cexp(ii * Cx t)) dot cexp(ii * Cx t)`;;

let HMRR_LINEAR_COMPLEX = prove
 (`!(L:complex->real^N) z.
     linear L ==> L z = Re z % L(basis 1) + Im z % L(basis 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `z = Re z % basis 1 + Im z % basis 2` (fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
   [SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
             BASIS_COMPONENT; ARITH] THEN
    REWRITE_TAC[RE_DEF; IM_DEF] THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL]]);;

let HMRR_TRACE_ALG = prove
 (`!(p1:complex) p2 (Vc:complex) (E:complex) r.
     Re E pow 2 + Im E pow 2 = &1
     ==> ((Re E % p1 + Im E % p2) dot (Cx r * E) + Vc dot E) +
         (Vc dot (ii * ii * E) + ((r * --(Im E)) % p1 + (r * Re E) % p2) dot (ii * E)) =
         r * (Re p1 + Im p2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[DOT_2; GSYM RE_DEF; GSYM IM_DEF; RE_ADD; IM_ADD; COMPLEX_CMUL;
              RE_MUL_CX; IM_MUL_CX; RE_MUL_II; IM_MUL_II] THEN
  POP_ASSUM MP_TAC THEN CONV_TAC REAL_RING);;

let HMRR_CEXP_NORM2 = prove
 (`!t. Re(cexp(ii * Cx t)) pow 2 + Im(cexp(ii * Cx t)) pow 2 = &1`,
  GEN_TAC THEN REWRITE_TAC[RE_CEXP; IM_CEXP; RE_MUL_II; IM_MUL_II; RE_CX; IM_CX] THEN
  REWRITE_TAC[REAL_NEG_0; REAL_EXP_0; REAL_MUL_LID] THEN
  MESON_TAC[SIN_CIRCLE; REAL_ADD_SYM]);;

(* The angular identity on one circle. *)

let HMRR_DIV_ANGULAR = prove
 (`!(V:real^2->real^2) s a r.
     open s /\ continuously_differentiable 1 s V /\
     (!t. a + Cx r * cexp(ii * Cx t) IN s)
     ==> r % integral (interval[vec 0,lift(&2 * pi)])
               (\t. lift(partial_derivative 1 V (a + Cx r * cexp(ii * Cx(drop t)))$1 +
                         partial_derivative 2 V (a + Cx r * cexp(ii * Cx(drop t)))$2)) =
         integral (interval[vec 0,lift(&2 * pi)]) (\t. lift(hmrr_gr V a r (drop t)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `V:real^2->real^2`] WAN_C1_OPEN_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the angular derivative of V(c) dot (ii E) *)
  SUBGOAL_THEN
   `!t. ((\t. lift((V:real^2->real^2)(a + Cx r * cexp(ii * Cx(drop t))) dot
                   (ii * cexp(ii * Cx(drop t)))))
         has_vector_derivative
         (lift(V(a + Cx r * cexp(ii * Cx(drop t))) dot (ii * ii * cexp(ii * Cx(drop t)))) +
          lift(frechet_derivative V (at (a + Cx r * cexp(ii * Cx(drop t))))
                 (Cx r * cexp(ii * Cx(drop t)) * ii) dot (ii * cexp(ii * Cx(drop t))))))
        (at t)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real^1` THEN
    MP_TAC(ISPECL [`\x y:real^2. lift(x dot y)`;
                   `\t. (V:real^2->real^2)(a + Cx r * cexp(ii * Cx(drop t)))`;
                   `\t:real^1. ii * cexp(ii * Cx(drop t))`;
                   `frechet_derivative (V:real^2->real^2)
                      (at (a + Cx r * cexp(ii * Cx(drop t))))
                      (Cx r * cexp(ii * Cx(drop t)) * ii)`;
                   `ii * ii * cexp(ii * Cx(drop t))`; `t:real^1`]
      HAS_VECTOR_DERIVATIVE_BILINEAR_AT) THEN
    REWRITE_TAC[BILINEAR_DOT] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_F_POLAR THEN REWRITE_TAC[differentiable] THEN
        ASM_MESON_TAC[];
        MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_REAL_COMPLEX THEN
        COMPLEX_DIFF_TAC THEN CONV_TAC COMPLEX_RING];
      REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the fundamental theorem on [0, 2 pi] with periodicity *)
  SUBGOAL_THEN
   `((\t. lift((V:real^2->real^2)(a + Cx r * cexp(ii * Cx(drop t))) dot
               (ii * ii * cexp(ii * Cx(drop t)))) +
          lift(frechet_derivative V (at (a + Cx r * cexp(ii * Cx(drop t))))
                 (Cx r * cexp(ii * Cx(drop t)) * ii) dot (ii * cexp(ii * Cx(drop t)))))
     has_integral vec 0) (interval[vec 0,lift(&2 * pi)])`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`\t. lift((V:real^2->real^2)(a + Cx r * cexp(ii * Cx(drop t))) dot
                (ii * cexp(ii * Cx(drop t))))`;
      `\t. lift((V:real^2->real^2)(a + Cx r * cexp(ii * Cx(drop t))) dot
                (ii * ii * cexp(ii * Cx(drop t)))) +
           lift(frechet_derivative V (at (a + Cx r * cexp(ii * Cx(drop t))))
                  (Cx r * cexp(ii * Cx(drop t)) * ii) dot (ii * cexp(ii * Cx(drop t))))`;
      `vec 0:real^1`; `lift(&2 * pi)`] FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
    REWRITE_TAC[DROP_VEC; LIFT_DROP; CEXP_2PII; CEXP_0II] THEN
    REWRITE_TAC[VECTOR_SUB_REFL] THEN DISCH_THEN MATCH_MP_TAC THEN
    SIMP_TAC[REAL_LE_MUL; REAL_POS; PI_POS_LE] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the pointwise polar identity *)
  SUBGOAL_THEN
   `!t. r % lift(partial_derivative 1 (V:real^2->real^2) (a + Cx r * cexp(ii * Cx(drop t)))$1 +
                 partial_derivative 2 V (a + Cx r * cexp(ii * Cx(drop t)))$2) =
        lift(hmrr_gr V a r (drop t)) +
        (lift(V(a + Cx r * cexp(ii * Cx(drop t))) dot (ii * ii * cexp(ii * Cx(drop t)))) +
         lift(frechet_derivative V (at (a + Cx r * cexp(ii * Cx(drop t))))
                (Cx r * cexp(ii * Cx(drop t)) * ii) dot (ii * cexp(ii * Cx(drop t)))))`
  (LABEL_TAC "pw") THENL
   [X_GEN_TAC `t:real^1` THEN REWRITE_TAC[hmrr_gr] THEN
    ABBREV_TAC `E = cexp(ii * Cx(drop t))` THEN
    ABBREV_TAC `c = a + Cx r * (E:complex)` THEN
    SUBGOAL_THEN `linear(frechet_derivative (V:real^2->real^2) (at c))` ASSUME_TAC THENL
     [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN REWRITE_TAC[differentiable] THEN
      EXPAND_TAC "c" THEN EXPAND_TAC "E" THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`frechet_derivative (V:real^2->real^2) (at c)`; `Cx r * E * ii`]
      HMRR_LINEAR_COMPLEX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[partial_derivative] THEN
    REWRITE_TAC[GSYM LIFT_ADD; GSYM LIFT_CMUL; LIFT_EQ] THEN
    REWRITE_TAC[RE_MUL_CX; IM_MUL_CX; RE_MUL_II; IM_MUL_II] THEN
    REWRITE_TAC[GSYM RE_DEF; GSYM IM_DEF] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC HMRR_TRACE_ALG THEN
    EXPAND_TAC "E" THEN REWRITE_TAC[HMRR_CEXP_NORM2];
    ALL_TAC] THEN
  (* integrability of the divergence along the circle *)
  SUBGOAL_THEN
   `(\t. lift(partial_derivative 1 (V:real^2->real^2) (a + Cx r * cexp(ii * Cx(drop t)))$1 +
              partial_derivative 2 V (a + Cx r * cexp(ii * Cx(drop t)))$2))
    integrable_on interval[vec 0,lift(&2 * pi)]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
    SUBGOAL_THEN
     `(\t. lift(partial_derivative 1 (V:real^2->real^2) (a + Cx r * cexp(ii * Cx(drop t)))$1 +
                partial_derivative 2 V (a + Cx r * cexp(ii * Cx(drop t)))$2)) =
      (\x. lift(partial_derivative 1 V x$1 + partial_derivative 2 V x$2)) o
      (\t. a + Cx r * cexp(ii * Cx(drop t)))`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    REWRITE_TAC[CONTINUOUS_ON_POLAR_PATH_INTERVAL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN CONJ_TAC THENL
     [REWRITE_TAC[LIFT_ADD; partial_derivative] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
      CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HAS_INTEGRAL_INTEGRABLE) THEN
  SUBGOAL_THEN
   `(\t. lift(hmrr_gr (V:real^2->real^2) a r (drop t))) integrable_on
    interval[vec 0,lift(&2 * pi)]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_EQ THEN
    EXISTS_TAC
     `\t. r % lift(partial_derivative 1 (V:real^2->real^2)
                     (a + Cx r * cexp(ii * Cx(drop t)))$1 +
                   partial_derivative 2 V (a + Cx r * cexp(ii * Cx(drop t)))$2) -
          (lift(V(a + Cx r * cexp(ii * Cx(drop t))) dot (ii * ii * cexp(ii * Cx(drop t)))) +
           lift(frechet_derivative V (at (a + Cx r * cexp(ii * Cx(drop t))))
                  (Cx r * cexp(ii * Cx(drop t)) * ii) dot (ii * cexp(ii * Cx(drop t)))))` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      USE_THEN "pw" (fun th -> REWRITE_TAC[th]) THEN VECTOR_ARITH_TAC;
      MATCH_MP_TAC INTEGRABLE_SUB THEN CONJ_TAC THENL
       [MATCH_MP_TAC INTEGRABLE_CMUL THEN FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM INTEGRAL_CMUL] THEN
  USE_THEN "pw" (fun th -> REWRITE_TAC[th]) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) INTEGRAL_ADD o lhand o snd) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN
  REWRITE_TAC[VECTOR_ADD_RID]);;

(* The radial fundamental theorem along one ray. *)

let HMRR_DIV_RADIAL = prove
 (`!(V:real^2->real^2) s a r1 r2 t.
     open s /\ continuously_differentiable 1 s V /\ r1 <= r2 /\
     (!r. r1 <= r /\ r <= r2 ==> a + Cx r * cexp(ii * Cx t) IN s)
     ==> integral (interval[lift r1,lift r2]) (\rho. lift(hmrr_gr V a (drop rho) t)) =
         lift(V(a + Cx r2 * cexp(ii * Cx t)) dot (Cx r2 * cexp(ii * Cx t))) -
         lift(V(a + Cx r1 * cexp(ii * Cx t)) dot (Cx r1 * cexp(ii * Cx t)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `V:real^2->real^2`] WAN_C1_OPEN_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MP_TAC(ISPECL [`\rho. lift((V:real^2->real^2)(a + Cx(drop rho) * cexp(ii * Cx t)) dot
                             (Cx(drop rho) * cexp(ii * Cx t)))`;
                 `\rho. lift(hmrr_gr (V:real^2->real^2) a (drop rho) t)`;
                 `lift r1`; `lift r2`] FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `rho:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN STRIP_TAC THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
  SUBGOAL_THEN `a + Cx(drop rho) * cexp(ii * Cx t) IN s` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `linear(frechet_derivative (V:real^2->real^2) (at (a + Cx(drop rho) * cexp(ii * Cx t))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN REWRITE_TAC[differentiable] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x y:real^2. lift(x dot y)`;
                 `\rho. (V:real^2->real^2)(a + Cx(drop rho) * cexp(ii * Cx t))`;
                 `\rho:real^1. Cx(drop rho) * cexp(ii * Cx t)`;
                 `frechet_derivative (V:real^2->real^2)
                    (at (a + Cx(drop rho) * cexp(ii * Cx t))) (cexp(ii * Cx t))`;
                 `cexp(ii * Cx t)`; `rho:real^1`] HAS_VECTOR_DERIVATIVE_BILINEAR_AT) THEN
  REWRITE_TAC[BILINEAR_DOT] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_F_RADIAL THEN REWRITE_TAC[differentiable] THEN
      ASM_MESON_TAC[];
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_REAL_COMPLEX THEN
      COMPLEX_DIFF_TAC THEN CONV_TAC COMPLEX_RING];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[hmrr_gr; partial_derivative] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[ISPEC `cexp(ii * Cx t)` (MATCH_MP HMRR_LINEAR_COMPLEX th)]) THEN
  REWRITE_TAC[GSYM LIFT_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

(* Joint continuity of the radial integrand on the polar rectangle. *)

let HMRR_POLAR_COMPOSE_CONT = prove
 (`!(g:real^2->real^N) s a r1 r2.
     g continuous_on s /\
     (!r t. r1 <= r /\ r <= r2 ==> a + Cx r * cexp(ii * Cx t) IN s)
     ==> (\z. g(a + Cx(drop(fstcart z)) * cexp(ii * Cx(drop(sndcart z))))) continuous_on
         interval[pastecart (lift r1) (vec 0),pastecart (lift r2) (lift(&2 * pi))]`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z. (g:real^2->real^N)(a + Cx(drop(fstcart z)) * cexp(ii * Cx(drop(sndcart z))))) =
    g o (\z. a + Cx(drop(fstcart z)) * cexp(ii * Cx(drop(sndcart z))))`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC[CONTINUOUS_ON_POLAR_PASTECART] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[GSYM PCROSS_INTERVAL; FORALL_PASTECART; PASTECART_IN_PCROSS;
              FSTCART_PASTECART; SNDCART_PASTECART; IN_INTERVAL_1; LIFT_DROP] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let HMRR_DIV_JOINT = prove
 (`!(V:real^2->real^2) s a r1 r2.
     open s /\ continuously_differentiable 1 s V /\
     (!r t. r1 <= r /\ r <= r2 ==> a + Cx r * cexp(ii * Cx t) IN s)
     ==> (\z. lift(hmrr_gr V a (drop(fstcart z)) (drop(sndcart z)))) continuous_on
         interval[pastecart (lift r1) (vec 0),pastecart (lift r2) (lift(&2 * pi))]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `V:real^2->real^2`] WAN_C1_OPEN_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!g:real^2->real^2. g continuous_on s
        ==> (\z. g(a + Cx(drop(fstcart z)) * cexp(ii * Cx(drop(sndcart z))))) continuous_on
            interval[pastecart (lift r1) (vec 0),pastecart (lift r2) (lift(&2 * pi))]`
  (LABEL_TAC "comp") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HMRR_POLAR_COMPOSE_CONT THEN
    EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. lift(Re(cexp(ii * Cx(drop(sndcart z)))))) continuous_on
    interval[pastecart (lift r1) (vec 0),pastecart (lift r2) (lift(&2 * pi))] /\
    (\z. lift(Im(cexp(ii * Cx(drop(sndcart z)))))) continuous_on
    interval[pastecart (lift r1) (vec 0),pastecart (lift r2) (lift(&2 * pi))]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[RE_DEF; IM_DEF] THEN CONJ_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
    REWRITE_TAC[CONTINUOUS_ON_CEXP_SNDCART];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. partial_derivative i (V:real^2->real^2) continuous_on s` ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `partial_derivative i (V:real^2->real^2) =
                  (\x. frechet_derivative V (at x) (basis i))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; partial_derivative]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[hmrr_gr; LIFT_ADD] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
      ASM_REWRITE_TAC[o_DEF] THEN
      USE_THEN "comp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[ETA_AX];
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN REWRITE_TAC[CONTINUOUS_ON_CEXP_SNDCART] THEN
      MATCH_MP_TAC CONTINUOUS_ON_CX_DROP THEN MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
      REWRITE_TAC[LINEAR_FSTCART]];
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN CONJ_TAC THENL
     [USE_THEN "comp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[ETA_AX];
      REWRITE_TAC[CONTINUOUS_ON_CEXP_SNDCART]]]);;

(* The divergence theorem on the annulus. *)

let HMRR_DIV_ANNULUS = prove
 (`!(V:real^2->real^2) s a r1 r2.
     open s /\ continuously_differentiable 1 s V /\ &0 < r1 /\ r1 <= r2 /\
     {x | r1 <= norm(x - a) /\ norm(x - a) <= r2} SUBSET s
     ==> (\x. lift(partial_derivative 1 V x$1 + partial_derivative 2 V x$2))
           absolutely_integrable_on {x | r1 < norm(x - a) /\ norm(x - a) < r2} /\
         integral {x | r1 < norm(x - a) /\ norm(x - a) < r2}
           (\x. lift(partial_derivative 1 V x$1 + partial_derivative 2 V x$2)) =
         integral (interval[vec 0,lift(&2 * pi)])
           (\t. lift(V(wan_circ a r2 (drop t)) dot (wan_circ a r2 (drop t) - a))) -
         integral (interval[vec 0,lift(&2 * pi)])
           (\t. lift(V(wan_circ a r1 (drop t)) dot (wan_circ a r1 (drop t) - a)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `V:real^2->real^2`] WAN_C1_OPEN_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!r t. r1 <= r /\ r <= r2 ==> a + Cx r * cexp(ii * Cx t) IN s`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `{x:real^2 | r1 <= norm(x - a) /\ norm(x - a) <= r2} SUBSET s` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[GSYM WAN_CIRC_CEXP; WAN_CIRC_NORM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. lift(partial_derivative 1 (V:real^2->real^2) x$1 +
                          partial_derivative 2 V x$2)) continuous_on s` ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_ADD; partial_derivative] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
    CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. lift(partial_derivative 1 (V:real^2->real^2) x$1 +
                          partial_derivative 2 V x$2))
                absolutely_integrable_on {x | r1 < norm(x - a) /\ norm(x - a) < r2}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `{x:real^2 | r1 <= norm(x - a) /\ norm(x - a) <= r2}` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC WAN_CONT_COMPACT_ABS_INT THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
        ASM_REWRITE_TAC[];
        SUBGOAL_THEN `{x:real^2 | r1 <= norm(x - a) /\ norm(x - a) <= r2} =
                      cball(a,r2) DIFF ball(a,r1)` SUBST1_TAC THENL
         [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_CBALL; IN_BALL; dist] THEN
          GEN_TAC THEN REWRITE_TAC[NORM_SUB] THEN REAL_ARITH_TAC;
          MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[COMPACT_CBALL; OPEN_BALL]]];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      MESON_TAC[WAN_ANNULUS_EQ]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!r. r1 <= r /\ r <= r2
        ==> (\t. lift((V:real^2->real^2)(a + Cx r * cexp(ii * Cx(drop t))) dot
                      (Cx r * cexp(ii * Cx(drop t)))))
            integrable_on interval[vec 0,lift(&2 * pi)]`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\t. (V:real^2->real^2)(a + Cx r * cexp(ii * Cx(drop t)))) =
                    V o (\t. a + Cx r * cexp(ii * Cx(drop t)))` SUBST1_TAC THENL
       [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      REWRITE_TAC[CONTINUOUS_ON_POLAR_PATH_INTERVAL] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
      ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE];
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_MUL THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
      REWRITE_TAC[SUBSET_UNIV; CONT_CEXP_POLAR]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. lift(partial_derivative 1 (V:real^2->real^2) x$1 +
                           partial_derivative 2 V x$2)`;
                 `a:real^2`; `&0`; `r1:real`; `r2:real`] WAN_POLAR_ANNULUS) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_LID; WAN_CIRC_CEXP] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2 o CONJUNCT2) THEN
  REWRITE_TAC[WAN_CIRC_CEXP; VECTOR_ARITH `(a + x) - a:real^N = x`] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `integral (interval[lift r1,lift r2])
                (\r. integral (interval[vec 0,lift(&2 * pi)])
                       (\t. lift(hmrr_gr (V:real^2->real^2) a (drop r) (drop t))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `rho:real^1` THEN
    REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN STRIP_TAC THEN
    MATCH_MP_TAC HMRR_DIV_ANGULAR THEN EXISTS_TAC `s:real^2->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\rho t. lift(hmrr_gr (V:real^2->real^2) a (drop rho) (drop t))`;
                 `lift r1`; `lift r2`; `vec 0:real^1`; `lift(&2 * pi)`]
    INTEGRAL_SWAP_CONTINUOUS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC HMRR_DIV_JOINT THEN EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `integral (interval[vec 0,lift(&2 * pi)])
      (\t. lift((V:real^2->real^2)(a + Cx r2 * cexp(ii * Cx(drop t))) dot
                (Cx r2 * cexp(ii * Cx(drop t)))) -
           lift(V(a + Cx r1 * cexp(ii * Cx(drop t))) dot (Cx r1 * cexp(ii * Cx(drop t)))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC HMRR_DIV_RADIAL THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC INTEGRAL_SUB THEN CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The Pohozaev identity on circles around an isolated point.  The stress    *)
(* field hmrr_tv (the energy-momentum tensor of u applied to x - a) is       *)
(* divergence free by the Cauchy-Riemann form of the Hopf differential       *)
(* (HMR_HOPF_CR); the polar divergence theorem gives constant circle fluxes, *)
(* which tend to 0 at the point when |x - a|^2 |Du(x)|^2 -> 0.  Flux zero is *)
(* radial = angular G-energy.                                                *)
(* ========================================================================= *)

let hmrr_f1 = new_definition
 `hmrr_f1 (G:real^K->real^K^K) (u:real^2->real^K) (x:real^2) =
    partial_derivative 1 u x dot (G(u x) ** partial_derivative 1 u x) -
    partial_derivative 2 u x dot (G(u x) ** partial_derivative 2 u x)`;;

let hmrr_f2 = new_definition
 `hmrr_f2 (G:real^K->real^K^K) (u:real^2->real^K) (x:real^2) =
    partial_derivative 1 u x dot (G(u x) ** partial_derivative 2 u x)`;;

let hmrr_tv = new_definition
 `hmrr_tv (G:real^K->real^K^K) (u:real^2->real^K) (a:real^2) (x:real^2) =
    vector[inv(&2) * hmrr_f1 G u x * (x$1 - a$1) + &1 * hmrr_f2 G u x * (x$2 - a$2);
           &1 * hmrr_f2 G u x * (x$1 - a$1) + --inv(&2) * hmrr_f1 G u x * (x$2 - a$2)]:real^2`;;

let HMRR_F12_SMOOTH = prove
 (`!S (G:real^K->real^K^K) d s (u:real^2->real^K).
     cm_target S G d /\ open s /\ smooth_map_on s u
     ==> smooth_map_on s (\x. lift(hmrr_f1 G u x)) /\
         smooth_map_on s (\x. lift(hmrr_f2 G u x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!i j. smooth_map_on s
            (\x. lift(partial_derivative i (u:real^2->real^K) x dot
                       ((G:real^K->real^K^K)(u x) ** partial_derivative j u x)))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC HMR_GPAIR_SMOOTH THEN
    MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[hmrr_f1; hmrr_f2] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CML_SM_SUB THEN ASM_REWRITE_TAC[]);;

(* Derivative of a two-term combination with affine coordinate factors. *)

let HMRR_D_AFF = prove
 (`!s k c z i.
     open s /\ 1 <= k /\ k <= 2
     ==> smooth_map_on s (\y:real^2. lift(y$k - c)) /\
         cml_d i (\y:real^2. y$k - c) z = if i = k then &1 else &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on s (\y:real^2. lift(y$k)) /\
                smooth_map_on s (\y:real^2. lift c)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[CML_SM_COORD; CML_SM_CONST]; ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC CML_SM_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^2)`; `\y:real^2. y$k`; `\y:real^2. (c:real)`; `z:real^2`; `i:num`]
    CML_D_SUB) THEN
  REWRITE_TAC[OPEN_UNIV; IN_UNIV; CML_SM_CONST] THEN
  ASM_SIMP_TAC[CML_SM_COORD; OPEN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[HMR_D_COORD; CML_D_CONST; REAL_SUB_RZERO]);;

let HMRR_D_LIN2 = prove
 (`!s (p:real^2->real) q al be c1 c2 k1 k2 z i.
     open s /\ smooth_map_on s (\x. lift(p x)) /\ smooth_map_on s (\x. lift(q x)) /\
     z IN s /\ 1 <= k1 /\ k1 <= 2 /\ 1 <= k2 /\ k2 <= 2
     ==> cml_d i (\y. al * p y * (y$k1 - c1) + be * q y * (y$k2 - c2)) z =
         al * (p z * (if i = k1 then &1 else &0) + cml_d i p z * (z$k1 - c1)) +
         be * (q z * (if i = k2 then &1 else &0) + cml_d i q z * (z$k2 - c2))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `k1:num`; `c1:real`; `z:real^2`; `i:num`] HMRR_D_AFF) THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `k2:num`; `c2:real`; `z:real^2`; `i:num`] HMRR_D_AFF) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `smooth_map_on s (\y:real^2. lift((p:real^2->real) y * (y$k1 - c1))) /\
    smooth_map_on s (\y:real^2. lift((q:real^2->real) y * (y$k2 - c2)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CML_SM_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on s (\y:real^2. lift(al * (p:real^2->real) y * (y$k1 - c1))) /\
    smooth_map_on s (\y:real^2. lift(be * (q:real^2->real) y * (y$k2 - c2)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CML_SM_CMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `\y:real^2. al * (p:real^2->real) y * (y$k1 - c1)`;
                 `\y:real^2. be * (q:real^2->real) y * (y$k2 - c2)`; `z:real^2`; `i:num`]
    CML_D_ADD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `al:real`; `\y:real^2. (p:real^2->real) y * (y$k1 - c1)`;
                 `z:real^2`; `i:num`] CML_D_CMUL) THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `be:real`; `\y:real^2. (q:real^2->real) y * (y$k2 - c2)`;
                 `z:real^2`; `i:num`] CML_D_CMUL) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `p:real^2->real`; `\y:real^2. y$k1 - c1`;
                 `z:real^2`; `i:num`] CML_D_MUL) THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `q:real^2->real`; `\y:real^2. y$k2 - c2`;
                 `z:real^2`; `i:num`] CML_D_MUL) THEN
  ASM_REWRITE_TAC[ETA_AX] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  ASM_REWRITE_TAC[]);;

(* The stress field is smooth and divergence free. *)

let HMRR_TV_SMOOTH = prove
 (`!S (G:real^K->real^K^K) d s (u:real^2->real^K) a.
     cm_target S G d /\ open s /\ smooth_map_on s u
     ==> smooth_map_on s (hmrr_tv G u a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                 `u:real^2->real^K`] HMRR_F12_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [MATCH_MP SMOOTH_MAP_ON_COMPONENTWISE (ASSUME `open(s:real^2->bool)`)] THEN
  REWRITE_TAC[DIMINDEX_2; ARITH_RULE `1 <= k /\ k <= 2 <=> k = 1 \/ k = 2`] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[hmrr_tv; VECTOR_2] THEN
  MATCH_MP_TAC CML_SM_ADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  MATCH_MP_TAC CML_SM_CMUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CML_SM_MUL THEN
  ASM_SIMP_TAC[HMRR_D_AFF; ARITH]);;

let HMRR_TV_DIV = prove
 (`!S (G:real^K->real^K^K) d s (u:real^2->real^K) a x.
     cm_target S G d /\ open s /\ cm_harmonic S G s u /\ x IN s
     ==> partial_derivative 1 (hmrr_tv G u a) x$1 +
         partial_derivative 2 (hmrr_tv G u a) x$2 = &0`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_harmonic]) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                 `u:real^2->real^K`] HMRR_F12_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                 `u:real^2->real^K`; `a:real^2`] HMRR_TV_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(hmrr_tv (G:real^K->real^K^K) u a) differentiable (at x)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i k. partial_derivative i (hmrr_tv (G:real^K->real^K^K) u a) x$k =
                      cml_d i (\y. hmrr_tv G u a y$k) x`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[cml_d] THEN
    ASM_SIMP_TAC[PARTIAL_DERIVATIVE_COMPONENT; LIFT_DROP; ETA_AX];
    ALL_TAC] THEN
  REWRITE_TAC[hmrr_tv; VECTOR_2] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `hmrr_f1 (G:real^K->real^K^K) u`;
                 `hmrr_f2 (G:real^K->real^K^K) u`; `inv(&2)`; `&1`; `(a:real^2)$1`;
                 `(a:real^2)$2`; `1`; `2`; `x:real^2`; `1`] HMRR_D_LIN2) THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `hmrr_f2 (G:real^K->real^K^K) u`;
                 `hmrr_f1 (G:real^K->real^K^K) u`; `&1`; `--inv(&2)`; `(a:real^2)$1`;
                 `(a:real^2)$2`; `1`; `2`; `x:real^2`; `2`] HMRR_D_LIN2) THEN
  ASM_REWRITE_TAC[ARITH] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                 `u:real^2->real^K`; `x:real^2`] HMR_HOPF_CR) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM hmrr_f1; GSYM hmrr_f2; ETA_AX] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* The flux density and its bound. *)

let HMRR_TV_DOT = prove
 (`!(G:real^K->real^K^K) u a x.
     hmrr_tv G u a x dot (x - a) =
     inv(&2) * hmrr_f1 G u x * ((x$1 - a$1) pow 2 - (x$2 - a$2) pow 2) +
     &2 * hmrr_f2 G u x * (x$1 - a$1) * (x$2 - a$2)`,
  REWRITE_TAC[hmrr_tv; DOT_2; VECTOR_2; VECTOR_SUB_COMPONENT] THEN REAL_ARITH_TAC);;

let HMRR_TV_ALG = prove
 (`!F1 F2 Y1 Y2 E Lam.
     &0 <= E /\ &0 <= Lam /\ abs F1 <= Lam * E /\ abs F2 <= Lam * E / &2
     ==> abs(inv(&2) * F1 * (Y1 pow 2 - Y2 pow 2) + &2 * F2 * Y1 * Y2)
         <= Lam * (Y1 pow 2 + Y2 pow 2) * E`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs(Y1 pow 2 - Y2 pow 2) <= Y1 pow 2 + Y2 pow 2 /\
                abs(&2 * Y1 * Y2) <= Y1 pow 2 + Y2 pow 2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPEC `Y1:real` REAL_LE_POW_2) THEN MP_TAC(SPEC `Y2:real` REAL_LE_POW_2) THEN
      REAL_ARITH_TAC;
      MP_TAC(SPEC `Y1 - Y2` REAL_LE_POW_2) THEN MP_TAC(SPEC `Y1 + Y2` REAL_LE_POW_2) THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(F1 * (Y1 pow 2 - Y2 pow 2)) <= (Lam * E) * (Y1 pow 2 + Y2 pow 2) /\
                abs(F2 * (&2 * Y1 * Y2)) <= (Lam * E / &2) * (Y1 pow 2 + Y2 pow 2)`
  MP_TAC THENL
   [CONJ_TAC THEN GEN_REWRITE_TAC LAND_CONV [REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    REAL_ARITH_TAC]);;

let HMRR_TV_BOUND = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> ?Lam. &0 <= Lam /\
               !(u:real^2->real^K) a x.
                 abs(hmrr_tv G u a x dot (x - a)) <= Lam * norm(x - a) pow 2 * hmr_e u x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC o MATCH_MP HMC_G_BOUNDS) THEN
  EXISTS_TAC `Lam:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  SUBGOAL_THEN `!z. transp((G:real^K->real^K^K) z) = G z` ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_target]; ALL_TAC] THEN
  REWRITE_TAC[HMRR_TV_DOT] THEN
  SUBGOAL_THEN `norm(x - a:real^2) pow 2 = (x$1 - a$1) pow 2 + (x$2 - a$2) pow 2`
  SUBST1_TAC THENL
   [REWRITE_TAC[NORM_POW_2; DOT_2; VECTOR_SUB_COMPONENT] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC HMRR_TV_ALG THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[hmr_e; hmrr_f1; hmrr_f2; GSYM NORM_POW_2] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_POW_2];
    MP_TAC(ISPECL [`(u:real^2->real^K) x`; `partial_derivative 1 (u:real^2->real^K) x`]
      (ASSUME `!z xi. &0 <= xi dot ((G:real^K->real^K^K) z ** xi) /\
                      xi dot (G z ** xi) <= Lam * norm xi pow 2`)) THEN
    MP_TAC(ISPECL [`(u:real^2->real^K) x`; `partial_derivative 2 (u:real^2->real^K) x`]
      (ASSUME `!z xi. &0 <= xi dot ((G:real^K->real^K^K) z ** xi) /\
                      xi dot (G z ** xi) <= Lam * norm xi pow 2`)) THEN
    REAL_ARITH_TAC;
    MP_TAC(ISPECL [`(G:real^K->real^K^K)((u:real^2->real^K) x)`; `Lam:real`;
                   `partial_derivative 1 (u:real^2->real^K) x`;
                   `partial_derivative 2 (u:real^2->real^K) x`] HMR_GPAIR_BOUND) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* Continuous functions along circles. *)

let HMRR_CIRC_CONT = prove
 (`!(h:real^2->real^N) s a r.
     h continuous_on s /\ (!t. wan_circ a r t IN s)
     ==> (\t. h(wan_circ a r (drop t))) continuous_on (:real^1) /\
         (\t. h(wan_circ a r (drop t))) integrable_on interval[vec 0,lift(&2 * pi)]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\t. (h:real^2->real^N)(wan_circ a r (drop t))) continuous_on (:real^1)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\t. (h:real^2->real^N)(wan_circ a r (drop t))) =
                  h o (\t. wan_circ a r (&0 + drop t))` SUBST1_TAC THENL
     [REWRITE_TAC[o_DEF; REAL_ADD_LID]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC[WAN_CIRC_CONT] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; REAL_ADD_LID; IN_UNIV];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV]]);;

(* The Pohozaev identity. *)

let HMRR_POHOZAEV = prove
 (`!S (G:real^K->real^K^K) d (u:real^2->real^K) a r.
     cm_target S G d /\ &0 < r /\ cm_harmonic S G (ball(a,r) DELETE a) u /\
     (!e. &0 < e ==> ?del. &0 < del /\
                           !x. &0 < norm(x - a) /\ norm(x - a) < del
                               ==> norm(x - a) pow 2 * hmr_e u x < e)
     ==> !rho. &0 < rho /\ rho < r
               ==> integral (interval[vec 0,lift(&2 * pi)])
                     (\t. lift(hmrr_tv G u a (wan_circ a rho (drop t)) dot
                               (wan_circ a rho (drop t) - a))) = vec 0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sg")))) THEN
  X_GEN_TAC `rho:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(ball(a:real^2,r) DELETE a)` ASSUME_TAC THENL
   [SIMP_TAC[OPEN_DELETE; OPEN_BALL]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_harmonic]) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                 `ball(a:real^2,r) DELETE a`; `u:real^2->real^K`; `a:real^2`]
    HMRR_TV_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `continuously_differentiable 1 (ball(a:real^2,r) DELETE a)
                  (hmrr_tv (G:real^K->real^K^K) u a)` ASSUME_TAC THENL
   [ASM_MESON_TAC[smooth_map_on]; ALL_TAC] THEN
  SUBGOAL_THEN `!e t. &0 < e /\ e < r ==> wan_circ a e t IN ball(a:real^2,r) DELETE a`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[IN_DELETE; IN_BALL] THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist; WAN_CIRC_NORM] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`a:real^2`; `e:real`; `t:real`] WAN_CIRC_NORM) THEN
    ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(hmrr_tv (G:real^K->real^K^K) u a x dot (x - a))) continuous_on
    (ball(a:real^2,r) DELETE a)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[ETA_AX];
      SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST]];
    ALL_TAC] THEN
  (* constant fluxes *)
  SUBGOAL_THEN
   `!e. &0 < e /\ e <= rho
        ==> integral (interval[vec 0,lift(&2 * pi)])
              (\t. lift(hmrr_tv (G:real^K->real^K^K) u a (wan_circ a rho (drop t)) dot
                        (wan_circ a rho (drop t) - a))) =
            integral (interval[vec 0,lift(&2 * pi)])
              (\t. lift(hmrr_tv G u a (wan_circ a e (drop t)) dot
                        (wan_circ a e (drop t) - a)))`
  (LABEL_TAC "cf") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`hmrr_tv (G:real^K->real^K^K) u a`; `ball(a:real^2,r) DELETE a`;
                   `a:real^2`; `e:real`; `rho:real`] HMRR_DIV_ANNULUS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DELETE; IN_BALL] THEN
      X_GEN_TAC `y:real^2` THEN STRIP_TAC THEN
      ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
      UNDISCH_TAC `e <= norm(y - a:real^2)` THEN
      ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    SUBGOAL_THEN
     `integral {x | e < norm(x - a) /\ norm(x - a) < rho}
        (\x. lift(partial_derivative 1 (hmrr_tv (G:real^K->real^K^K) u a) x$1 +
                  partial_derivative 2 (hmrr_tv G u a) x$2)) = vec 0`
    SUBST1_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `integral {x | e < norm(x - a) /\ norm(x - a) < rho}
                    (\x:real^2. vec 0:real^1)` THEN
      CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[INTEGRAL_0]] THEN
      MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `y:real^2` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN
      MATCH_MP_TAC HMRR_TV_DIV THEN
      MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`; `ball(a:real^2,r) DELETE a`] THEN
      ASM_REWRITE_TAC[IN_DELETE; IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
      REWRITE_TAC[dist] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_TAC THEN UNDISCH_TAC `e < norm(y - a:real^2)` THEN
      ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN(MP_TAC o SYM) THEN REWRITE_TAC[VECTOR_SUB_EQ]];
    ALL_TAC] THEN
  (* the fluxes tend to zero *)
  FIRST_ASSUM(X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC o MATCH_MP HMRR_TV_BOUND) THEN
  SUBGOAL_THEN
   `!eta. &0 < eta
          ==> norm(integral (interval[vec 0,lift(&2 * pi)])
                (\t. lift(hmrr_tv (G:real^K->real^K^K) u a (wan_circ a rho (drop t)) dot
                          (wan_circ a rho (drop t) - a)))) <= eta`
  ASSUME_TAC THENL
   [X_GEN_TAC `eta:real` THEN DISCH_TAC THEN
    USE_THEN "sg" (MP_TAC o SPEC `eta / (&2 * pi * (Lam + &1))`) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[PI_POS] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `del:real` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `e = min rho (del / &2)` THEN
    SUBGOAL_THEN `&0 < e /\ e <= rho /\ e < del /\ e < r` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "cf" (fun th ->
      REWRITE_TAC[MATCH_MP th (CONJ (ASSUME `&0 < e`) (ASSUME `e <= rho`))]) THEN
    MP_TAC(ISPECL [`\x. lift(hmrr_tv (G:real^K->real^K^K) u a x dot (x - a))`;
                   `ball(a:real^2,r) DELETE a`; `a:real^2`; `e:real`] HMRR_CIRC_CONT) THEN
    ASM_SIMP_TAC[] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP INTEGRABLE_INTEGRAL) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\t. lift(hmrr_tv (G:real^K->real^K^K) u a (wan_circ a e (drop t)) dot
                             (wan_circ a e (drop t) - a))`;
                   `vec 0:real^1`; `lift(&2 * pi)`;
                   `integral (interval[vec 0,lift(&2 * pi)])
                      (\t. lift(hmrr_tv (G:real^K->real^K^K) u a (wan_circ a e (drop t)) dot
                                (wan_circ a e (drop t) - a)))`;
                   `Lam * eta / (&2 * pi * (Lam + &1))`] HAS_INTEGRAL_BOUND) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[PI_POS_LE] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN REWRITE_TAC[NORM_LIFT] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `Lam * norm(wan_circ a e (drop t) - a) pow 2 *
                  hmr_e (u:real^2->real^K) (wan_circ a e (drop t))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[WAN_CIRC_NORM] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SIMP_TAC[CONTENT_1; DROP_VEC; LIFT_DROP; REAL_LE_MUL; REAL_POS; PI_POS_LE] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= e ==> x <= y ==> x <= e`) THEN
    SUBGOAL_THEN `(Lam * eta / (&2 * pi * (Lam + &1))) * (&2 * pi - &0) =
                  (Lam / (Lam + &1)) * eta` SUBST1_TAC THENL
     [SUBGOAL_THEN `~(Lam + &1 = &0) /\ ~(pi = &0)` MP_TAC THENL
       [MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 <= Lam ==> &0 < Lam + &1`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM NORM_EQ_0] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(&0 < x) ==> x = &0`) THEN
  REWRITE_TAC[NORM_POS_LE] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `norm(integral (interval[vec 0,lift(&2 * pi)])
      (\t. lift(hmrr_tv (G:real^K->real^K^K) u a (wan_circ a rho (drop t)) dot
                (wan_circ a rho (drop t) - a)))) / &2`) THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Annuli, Euclidean energies and the small-energy gradient bound near the   *)
(* point.  hmrr_en u a r1 r2 is the Euclidean Dirichlet integral of u over   *)
(* the open annulus r1 < |x-a| < r2.  From HMR_EPS_E on the balls            *)
(* B(x, |x - a| / 2): |x - a|^2 |Du(x)|^2 <= C hmrr_en u a 0 (3 |x - a| / 2) *)
(* once the energy is small, and |x - a|^2 |Du(x)|^2 -> 0 as x -> a.         *)
(* ========================================================================= *)

let hmrr_ann = new_definition
 `hmrr_ann (a:real^2) r1 r2 = {x:real^2 | r1 < norm(x - a) /\ norm(x - a) < r2}`;;

let hmrr_en = new_definition
 `hmrr_en (u:real^2->real^K) (a:real^2) r1 r2 =
    drop(integral (hmrr_ann a r1 r2) (\x. lift(hmr_e u x)))`;;

let HMRR_ANN_FACTS = prove
 (`!(a:real^2) r1 r2.
     open(hmrr_ann a r1 r2) /\ lebesgue_measurable(hmrr_ann a r1 r2) /\
     measurable(hmrr_ann a r1 r2) /\ bounded(hmrr_ann a r1 r2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hmrr_ann] THEN
  MP_TAC(ISPECL [`a:real^2`; `r1:real`; `r2:real`] WAN_ANNULUS_EQ) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_DIFF THEN REWRITE_TAC[OPEN_BALL; CLOSED_CBALL];
    MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `ball(a:real^2,r2)` THEN
    REWRITE_TAC[BOUNDED_BALL] THEN SET_TAC[]]);;

let HMRR_ANN_DELETE = prove
 (`!(a:real^2) r. hmrr_ann a (&0) r = ball(a,r) DELETE a`,
  REWRITE_TAC[hmrr_ann; EXTENSION; IN_ELIM_THM; IN_DELETE; IN_BALL; dist] THEN
  MAP_EVERY X_GEN_TAC [`a:real^2`; `r:real`; `x:real^2`] THEN
  REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ] THEN
  MP_TAC(ISPECL [`a:real^2`; `x:real^2`] NORM_SUB) THEN DISCH_THEN SUBST1_TAC THEN
  CONV_TAC TAUT);;

let HMRR_ANN_SUBSET = prove
 (`!(a:real^2) r1 r2 r1' r2'.
     r1' <= r1 /\ r2 <= r2' ==> hmrr_ann a r1 r2 SUBSET hmrr_ann a r1' r2'`,
  REWRITE_TAC[hmrr_ann; SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

(* The G-energy is bounded by a multiple of the Euclidean energy. *)

let HMRR_GDIR_UPPER = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> ?Lam. &0 <= Lam /\
               !s (u:real^2->real^K).
                  open s /\ smooth_map_on s u /\ wan_w12 s u
                  ==> (\x. lift(hmr_e u x)) integrable_on s /\
                      wan_gdir s G u <= Lam * drop(integral s (\x. lift(hmr_e u x)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_target]) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Lam0:real` STRIP_ASSUME_TAC o MATCH_MP HMC_G_BOUNDS) THEN
  EXISTS_TAC `Lam0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`s:real^2->bool`; `u:real^2->real^K`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `continuously_differentiable 1 s (u:real^2->real^K)` ASSUME_TAC THENL
   [ASM_MESON_TAC[smooth_map_on]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> (\x. lift(partial_derivative i (u:real^2->real^K) x dot partial_derivative i u x))
            integrable_on s /\
            (\x. lift(partial_derivative i u x dot ((G:real^K->real^K^K)(u x) **
                                                    partial_derivative i u x)))
            integrable_on s`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(\x. partial_derivative i (u:real^2->real^K) x) IN lspace s (&2)` ASSUME_TAC THENL
     [MATCH_MP_TAC HMC_PD_LSPACE THEN ASM_REWRITE_TAC[DIMINDEX_2]; ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `(\x. partial_derivative i (u:real^2->real^K) x) IN lspace s (&2)` THEN
      REWRITE_TAC[lspace; IN_ELIM_THM; RPOW_POW; NORM_POW_2] THEN SIMP_TAC[];
      MATCH_MP_TAC HMC_QUAD_INTEGRABLE THEN EXISTS_TAC `Lam0:real` THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
        ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN] THEN
        SUBGOAL_THEN `(vectorize:real^K^K->real^(K,K)finite_prod) o
                      (\x. (G:real^K->real^K^K)((u:real^2->real^K) x)) =
                      ((vectorize:real^K^K->real^(K,K)finite_prod) o G) o u` SUBST1_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^K)` THEN
        ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SUBSET_UNIV];
        REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_ABS_REFL; REAL_ARITH `&0 <= x ==> abs x = x`]]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[hmr_e; LIFT_ADD] THEN MATCH_MP_TAC INTEGRABLE_ADD THEN
    FIRST_ASSUM(fun th -> MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `G:real^K->real^K^K`; `u:real^2->real^K`] HMC_GDIR_CLASSICAL) THEN
  ASM_REWRITE_TAC[DIMINDEX_2; SUM_2] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[hmr_e; LIFT_ADD] THEN
  ASM_SIMP_TAC[INTEGRAL_ADD; DROP_ADD; REAL_ADD_LDISTRIB] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
  REWRITE_TAC[GSYM DROP_CMUL] THEN ASM_SIMP_TAC[GSYM INTEGRAL_CMUL] THEN
  MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_SIMP_TAC[INTEGRABLE_CMUL] THEN
  REWRITE_TAC[DROP_CMUL; LIFT_DROP] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM NORM_POW_2] THEN ASM_REWRITE_TAC[]);;

(* Energies on annuli inside the punctured disc. *)

let HMRR_EN_FACTS = prove
 (`!(u:real^2->real^K) a r.
     (\x. lift(hmr_e u x)) integrable_on (ball(a,r) DELETE a)
     ==> (!r1 r2. &0 <= r1 /\ r2 <= r
                  ==> (\x. lift(hmr_e u x)) integrable_on hmrr_ann a r1 r2 /\
                      &0 <= hmrr_en u a r1 r2) /\
         (!r1 r2 r1' r2'. &0 <= r1' /\ r1' <= r1 /\ r2 <= r2' /\ r2' <= r
                          ==> hmrr_en u a r1 r2 <= hmrr_en u a r1' r2')`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(\x. lift(hmr_e (u:real^2->real^K) x)) absolutely_integrable_on
                (ball(a,r) DELETE a)` ASSUME_TAC THENL
   [MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DIMINDEX_1; ARITH_RULE `1 <= i /\ i <= 1 <=> i = 1`] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[GSYM drop; LIFT_DROP; HMR_E_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r1 r2. &0 <= r1 /\ r2 <= r
                        ==> (\x. lift(hmr_e (u:real^2->real^K) x)) integrable_on
                            hmrr_ann a r1 r2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `ball(a:real^2,r) DELETE a` THEN ASM_REWRITE_TAC[HMRR_ANN_FACTS] THEN
    REWRITE_TAC[GSYM HMRR_ANN_DELETE] THEN MATCH_MP_TAC HMRR_ANN_SUBSET THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[hmrr_en] THEN
    MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_SIMP_TAC[LIFT_DROP; HMR_E_POS];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[hmrr_en] THEN
  MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HMRR_ANN_SUBSET THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[LIFT_DROP; HMR_E_POS]]);;

(* The small-energy gradient bound at a point of the punctured disc. *)

let HMRR_EPS_ALG = prove
 (`!t h g E C1 Lam.
     &0 < C1 /\ &0 <= Lam /\ &0 <= E /\
     (t / &2) pow 2 * h <= C1 * g /\ g <= Lam * E
     ==> t pow 2 * h <= (&4 * C1 * (Lam + &1)) * E`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `C1 * g <= C1 * (Lam + &1) * E` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Lam * E` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `t pow 2 * h = &4 * ((t / &2) pow 2 * h)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let HMRR_EPS_POINT = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> ?e0 C. &0 < e0 /\ &0 < C /\
                !(u:real^2->real^K) a r x.
                  cm_harmonic S G (ball(a,r) DELETE a) u /\
                  wan_w12 (ball(a,r) DELETE a) u /\
                  &0 < norm(x - a) /\ &3 / &2 * norm(x - a) <= r /\
                  hmrr_en u a (&0) (&3 / &2 * norm(x - a)) <= e0
                  ==> norm(x - a) pow 2 * hmr_e u x <=
                      C * hmrr_en u a (&0) (&3 / &2 * norm(x - a))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e1:real` (X_CHOOSE_THEN `C1:real` STRIP_ASSUME_TAC) o
    MATCH_MP HMR_EPS_E) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC o MATCH_MP HMRR_GDIR_UPPER) THEN
  MAP_EVERY EXISTS_TAC [`e1 / (Lam + &1)`; `&4 * C1 * (Lam + &1)`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:real^2->real^K`; `a:real^2`; `r:real`; `x:real^2`] THEN
  STRIP_TAC THEN
  ABBREV_TAC `t = norm(x - a:real^2)` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_harmonic]) THEN
  SUBGOAL_THEN `open(ball(a:real^2,r) DELETE a)` ASSUME_TAC THENL
   [SIMP_TAC[OPEN_DELETE; OPEN_BALL]; ALL_TAC] THEN
  SUBGOAL_THEN `(\y. lift(hmr_e (u:real^2->real^K) y)) integrable_on (ball(a,r) DELETE a)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPECL [`ball(a:real^2,r) DELETE a`; `u:real^2->real^K`] o
      check (fun th -> can (find_term (fun t -> t = `Lam:real`)) (concl th) &&
                       is_forall (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^2->real^K`; `a:real^2`; `r:real`] HMRR_EN_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "enf1") (LABEL_TAC "enf2")) THEN
  SUBGOAL_THEN `ball(x:real^2,t / &2) SUBSET hmrr_ann a (&0) (&3 / &2 * t)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL; hmrr_ann; IN_ELIM_THM; dist] THEN X_GEN_TAC `y:real^2` THEN
    UNDISCH_TAC `norm(x - a:real^2) = t` THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN `hmrr_ann a (&0) (&3 / &2 * t) SUBSET ball(a:real^2,r) DELETE a`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM HMRR_ANN_DELETE] THEN MATCH_MP_TAC HMRR_ANN_SUBSET THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(x:real^2,t / &2) SUBSET ball(a,r) DELETE a` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `cm_harmonic S G (ball(x,t / &2)) (u:real^2->real^K) /\
                wan_w12 (ball(x,t / &2)) u /\ smooth_map_on (ball(x,t / &2)) u`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HMC_HARMONIC_SUBSET THEN EXISTS_TAC `ball(a:real^2,r) DELETE a` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC WAN_W12_SUBSET THEN EXISTS_TAC `ball(a:real^2,r) DELETE a` THEN
      ASM_REWRITE_TAC[OPEN_BALL];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(a:real^2,r) DELETE a` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_gdir (ball(x,t / &2)) G (u:real^2->real^K) <=
                Lam * hmrr_en u a (&0) (&3 / &2 * t)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `Lam * drop(integral (ball(x:real^2,t / &2)) (\y. lift(hmr_e (u:real^2->real^K) y)))` THEN
    FIRST_ASSUM(MP_TAC o SPECL [`ball(x:real^2,t / &2)`; `u:real^2->real^K`] o
      check (fun th -> can (find_term (fun t -> t = `Lam:real`)) (concl th) &&
                       is_forall (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[OPEN_BALL]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[hmrr_en] THEN
    MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN ASM_REWRITE_TAC[LIFT_DROP; HMR_E_POS] THEN
    USE_THEN "enf1" (MP_TAC o SPECL [`&0`; `&3 / &2 * t`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= hmrr_en (u:real^2->real^K) a (&0) (&3 / &2 * t)` ASSUME_TAC THENL
   [USE_THEN "enf1" (MP_TAC o SPECL [`&0`; `&3 / &2 * t`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC HMRR_EPS_ALG THEN
  EXISTS_TAC `wan_gdir (ball(x,t / &2)) G (u:real^2->real^K)` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^2`; `t / &2`; `u:real^2->real^K`] o
    check (fun th -> can (find_term (fun t -> t = `C1:real`)) (concl th) &&
                     is_forall (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `Lam * hmrr_en (u:real^2->real^K) a (&0) (&3 / &2 * t)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(Lam + &1) * hmrr_en (u:real^2->real^K) a (&0) (&3 / &2 * t)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(Lam + &1) * e1 / (Lam + &1)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      SUBGOAL_THEN `~(Lam + &1 = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN
  REWRITE_TAC[CENTRE_IN_BALL] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]);;

(* Absolute continuity: small energy on small punctured balls. *)

let HMRR_EN_SMALL = prove
 (`!(u:real^2->real^K) a r.
     &0 < r /\ (\x. lift(hmr_e u x)) integrable_on (ball(a,r) DELETE a)
     ==> !eta. &0 < eta ==> ?t. &0 < t /\ t <= r /\ hmrr_en u a (&0) t < eta`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `eta:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(\x. lift(hmr_e (u:real^2->real^K) x)) absolutely_integrable_on
                (ball(a,r) DELETE a)` ASSUME_TAC THENL
   [MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DIMINDEX_1; ARITH_RULE `1 <= i /\ i <= 1 <=> i = 1`] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[GSYM drop; LIFT_DROP; HMR_E_POS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. lift(hmr_e (u:real^2->real^K) x)`; `ball(a:real^2,r) DELETE a`;
                 `eta:real`] ABSOLUTELY_CONTINUOUS_INTEGRAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `dd:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min r (min (&1) (dd / &8))` THEN
  ABBREV_TAC `t = min r (min (&1) (dd / &8))` THEN
  SUBGOAL_THEN `&0 < t /\ t <= r /\ t <= &1 /\ t <= dd / &8` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[hmrr_en] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `hmrr_ann a (&0) t`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[HMRR_ANN_FACTS] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM HMRR_ANN_DELETE] THEN MATCH_MP_TAC HMRR_ANN_SUBSET THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `measure(ball(a:real^2,t))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MEASURE_SUBSET THEN REWRITE_TAC[HMRR_ANN_FACTS; MEASURABLE_BALL] THEN
      REWRITE_TAC[hmrr_ann; SUBSET; IN_ELIM_THM; IN_BALL; dist] THEN
      X_GEN_TAC `y:real^2` THEN MP_TAC(ISPECL [`y:real^2`; `a:real^2`] NORM_SUB) THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(&2 * t) pow dimindex(:2)` THEN
    ASM_SIMP_TAC[MEASURE_BALL_BOUND; REAL_LT_IMP_LE; DIMINDEX_2] THEN
    SUBGOAL_THEN `t pow 2 <= t` MP_TAC THENL
     [REWRITE_TAC[REAL_POW_2] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    REWRITE_TAC[NORM_1] THEN REAL_ARITH_TAC]);;

(* The small-gradient property at the point. *)

let HMRR_SG = prove
 (`!S (G:real^K->real^K^K) d (u:real^2->real^K) a r.
     cm_target S G d /\ &0 < r /\ cm_harmonic S G (ball(a,r) DELETE a) u /\
     wan_w12 (ball(a,r) DELETE a) u
     ==> !e. &0 < e ==> ?del. &0 < del /\
                             !x. &0 < norm(x - a) /\ norm(x - a) < del
                                 ==> norm(x - a) pow 2 * hmr_e u x < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e0:real` (X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) o
    MATCH_MP HMRR_EPS_POINT) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC o MATCH_MP HMRR_GDIR_UPPER) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_harmonic]) THEN
  SUBGOAL_THEN `(\y. lift(hmr_e (u:real^2->real^K) y)) integrable_on (ball(a,r) DELETE a)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPECL [`ball(a:real^2,r) DELETE a`; `u:real^2->real^K`] o
      check (fun th -> can (find_term (fun t -> t = `Lam:real`)) (concl th) &&
                       is_forall (concl th))) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[OPEN_DELETE; OPEN_BALL]; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^2->real^K`; `a:real^2`; `r:real`] HMRR_EN_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "enf1") (LABEL_TAC "enf2")) THEN
  MP_TAC(ISPECL [`u:real^2->real^K`; `a:real^2`; `r:real`] HMRR_EN_SMALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `min e0 (e / (C + &1))`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `&2 / &3 * t0` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
  SUBGOAL_THEN `hmrr_en (u:real^2->real^K) a (&0) (&3 / &2 * norm(x - a)) <=
                hmrr_en u a (&0) t0` ASSUME_TAC THENL
   [USE_THEN "enf2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^2->real^K`; `a:real^2`; `r:real`; `x:real^2`]
    (ASSUME `!(u:real^2->real^K) a r x.
               cm_harmonic S G (ball(a,r) DELETE a) u /\
               wan_w12 (ball(a,r) DELETE a) u /\
               &0 < norm(x - a) /\ &3 / &2 * norm(x - a) <= r /\
               hmrr_en u a (&0) (&3 / &2 * norm(x - a)) <= e0
               ==> norm(x - a) pow 2 * hmr_e u x <=
                   C * hmrr_en u a (&0) (&3 / &2 * norm(x - a))`)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `hmrr_en (u:real^2->real^K) a (&0) t0` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `x < min a (e / (C + &1)) ==> x <= a`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `y < e ==> x <= y ==> x < e`) THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `C * e / (C + &1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `hmrr_en (u:real^2->real^K) a (&0) t0` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `x < min e0 b ==> x <= b`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `C * e / (C + &1) = (C / (C + &1)) * e` SUBST1_TAC THENL
   [SUBGOAL_THEN `~(C + &1 = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 < C ==> &0 < C + &1`] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Radial and angular derivatives along circles, circle averages, Wirtinger  *)
(* on circles, and the consequences of the Pohozaev identity: on each circle *)
(* the radial energy is at most Lam / lam times the angular energy           *)
(* (HMRR_POH_CIRCLE), the boundary term of the comparison argument is        *)
(* bounded by the circle energy (HMRR_PSI_BOUND), and on annuli the energy   *)
(* is controlled by the angular energy (HMRR_POH_ANNULUS).                   *)
(* ========================================================================= *)

let hmrr_rad = new_definition
 `hmrr_rad (u:real^2->real^K) (a:real^2) (x:real^2) =
    (x$1 - a$1) % partial_derivative 1 u x + (x$2 - a$2) % partial_derivative 2 u x`;;

let hmrr_ang = new_definition
 `hmrr_ang (u:real^2->real^K) (a:real^2) (x:real^2) =
    (a$2 - x$2) % partial_derivative 1 u x + (x$1 - a$1) % partial_derivative 2 u x`;;

let hmrr_avg = new_definition
 `hmrr_avg (u:real^2->real^K) (a:real^2) s =
    inv(&2 * pi) % integral (interval[vec 0,lift(&2 * pi)]) (\t. u(wan_circ a s (drop t)))`;;

let HMRR_NORM2_SUB = prove
 (`!(x:real^2) a. norm(x - a) pow 2 = (x$1 - a$1) pow 2 + (x$2 - a$2) pow 2`,
  REWRITE_TAC[NORM_POW_2; DOT_2; VECTOR_SUB_COMPONENT] THEN REAL_ARITH_TAC);;

let HMRR_RAD_ANG_NORM = prove
 (`!(u:real^2->real^K) a x.
     norm(hmrr_rad u a x) pow 2 + norm(hmrr_ang u a x) pow 2 =
     norm(x - a) pow 2 * hmr_e u x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HMRR_NORM2_SUB; hmrr_rad; hmrr_ang; hmr_e; NORM_POW_2] THEN
  REWRITE_TAC[DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL] THEN
  MP_TAC(ISPECL [`partial_derivative 1 (u:real^2->real^K) x`;
                 `partial_derivative 2 (u:real^2->real^K) x`] DOT_SYM) THEN
  CONV_TAC REAL_RING);;

let HMRR_TV_RADANG = prove
 (`!(G:real^K->real^K^K) u a x.
     transp(G(u x)) = G(u x)
     ==> hmrr_tv G u a x dot (x - a) =
         inv(&2) * (hmrr_rad u a x dot (G(u x) ** hmrr_rad u a x) -
                    hmrr_ang u a x dot (G(u x) ** hmrr_ang u a x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HMRR_TV_DOT; hmrr_f1; hmrr_f2; hmrr_rad; hmrr_ang] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL] THEN
  REWRITE_TAC[DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL] THEN
  SUBGOAL_THEN
   `partial_derivative 2 (u:real^2->real^K) x dot
    ((G:real^K->real^K^K)(u x) ** partial_derivative 1 u x) =
    partial_derivative 1 u x dot (G(u x) ** partial_derivative 2 u x)`
  MP_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [DOT_SYM] THEN ASM_SIMP_TAC[HMR_SYM_DOT];
    CONV_TAC REAL_RING]);;

(* Smoothness of the radial and angular derivatives. *)

let HMRR_RADANG_SMOOTH = prove
 (`!(u:real^2->real^K) U a.
     open U /\ smooth_map_on U u
     ==> smooth_map_on U (hmrr_rad u a) /\ smooth_map_on U (hmrr_ang u a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!c k. 1 <= k /\ k <= 2
                      ==> smooth_map_on U (\x:real^2. lift(x$k - c)) /\
                          smooth_map_on U (\x:real^2. lift(c - x$k))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CML_SM_SUB THEN
    ASM_SIMP_TAC[CML_SM_COORD; CML_SM_CONST];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. smooth_map_on U (partial_derivative i (u:real^2->real^K))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]; ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `hmrr_rad (u:real^2->real^K) a =
                  (\x. drop(lift(x$1 - a$1)) % partial_derivative 1 u x +
                       drop(lift(x$2 - a$2)) % partial_derivative 2 u x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; hmrr_rad; LIFT_DROP]; ALL_TAC];
    SUBGOAL_THEN `hmrr_ang (u:real^2->real^K) a =
                  (\x. drop(lift(a$2 - x$2)) % partial_derivative 1 u x +
                       drop(lift(x$1 - a$1)) % partial_derivative 2 u x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; hmrr_ang; LIFT_DROP]; ALL_TAC]] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_SIMP_TAC[ETA_AX; ARITH]);;

(* Chain rule along paths and the angular derivative along circles. *)

let HMRR_PATH_CHAIN = prove
 (`!(u:real^2->real^K) p p' t.
     (p has_vector_derivative p') (at t) /\ u differentiable at (p t)
     ==> ((\t. u(p t)) has_vector_derivative frechet_derivative u (at (p t)) p') (at t)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
  MP_TAC(ISPECL [`p:real^1->real^2`; `u:real^2->real^K`; `\h:real^1. drop h % (p':real^2)`;
                 `frechet_derivative (u:real^2->real^K) (at (p(t:real^1)))`; `t:real^1`]
    DIFF_CHAIN_AT) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_REWRITE_TAC[GSYM has_vector_derivative];
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]];
    ALL_TAC] THEN
  REWRITE_TAC[has_vector_derivative; o_DEF] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `h:real^1` THEN ASM_SIMP_TAC[LINEAR_CMUL]);;

let HMRR_CIRC_ANG_DERIV = prove
 (`!(u:real^2->real^K) a s t.
     u differentiable at (wan_circ a s (drop t))
     ==> ((\t. u(wan_circ a s (drop t))) has_vector_derivative
          hmrr_ang u a (wan_circ a s (drop t))) (at t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^2`; `s:real`; `&0`; `t:real^1`] WAN_CIRC_VDERIV) THEN
  REWRITE_TAC[REAL_ADD_LID] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`u:real^2->real^K`; `\t. wan_circ a s (drop t)`;
                 `s % vector[--sin(drop t); cos(drop t)]:real^2`; `t:real^1`]
    HMRR_PATH_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
  REWRITE_TAC[WAN_VECTOR2_BASIS] THEN ASM_SIMP_TAC[LINEAR_CMUL; LINEAR_ADD] THEN
  REWRITE_TAC[hmrr_ang; partial_derivative] THEN
  ABBREV_TAC `c = wan_circ a s (drop t)` THEN
  SUBGOAL_THEN `(c:real^2)$1 - (a:real^2)$1 = s * cos(drop t) /\
                (a:real^2)$2 - c$2 = --(s * sin(drop t))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN
    REWRITE_TAC[wan_circ; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_2] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC);;

(* Circle averages. *)

let HMRR_AVG_ZERO = prove
 (`!(u:real^2->real^K) a s.
     (\t. u(wan_circ a s (drop t))) integrable_on interval[vec 0,lift(&2 * pi)]
     ==> ((\t. u(wan_circ a s (drop t)) - hmrr_avg u a s) has_integral vec 0)
         (interval[vec 0,lift(&2 * pi)])`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `vec 0:real^K =
    integral (interval[vec 0,lift(&2 * pi)]) (\t. u(wan_circ a s (drop t))) -
    content(interval[vec 0,lift(&2 * pi)]) % hmrr_avg u a s`
  SUBST1_TAC THENL
   [SIMP_TAC[CONTENT_1; DROP_VEC; LIFT_DROP; REAL_LE_MUL; REAL_POS; PI_POS_LE] THEN
    REWRITE_TAC[hmrr_avg; VECTOR_MUL_ASSOC; REAL_SUB_RZERO] THEN
    SIMP_TAC[REAL_MUL_RINV; REAL_ENTIRE; PI_NZ; REAL_OF_NUM_EQ; ARITH] THEN
    VECTOR_ARITH_TAC;
    MATCH_MP_TAC HAS_INTEGRAL_SUB THEN
    ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL; HAS_INTEGRAL_CONST]]);;

let HMRR_AVG_DIST = prove
 (`!(u:real^2->real^K) a s z B.
     (\t. u(wan_circ a s (drop t))) integrable_on interval[vec 0,lift(&2 * pi)] /\
     (!t. norm(z - u(wan_circ a s t)) <= B)
     ==> norm(z - hmrr_avg u a s) <= B`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(z - (u:real^2->real^K)(wan_circ a s (&0)))` THEN
    ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\t. z - (u:real^2->real^K)(wan_circ a s (drop t))) has_integral
     (&2 * pi) % (z - hmrr_avg u a s)) (interval[vec 0,lift(&2 * pi)])`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(&2 * pi) % (z - hmrr_avg (u:real^2->real^K) a s) =
      content(interval[vec 0,lift(&2 * pi)]) % z -
      integral (interval[vec 0,lift(&2 * pi)]) (\t. u(wan_circ a s (drop t)))`
    SUBST1_TAC THENL
     [SIMP_TAC[CONTENT_1; DROP_VEC; LIFT_DROP; REAL_LE_MUL; REAL_POS; PI_POS_LE] THEN
      REWRITE_TAC[hmrr_avg; VECTOR_SUB_LDISTRIB; VECTOR_MUL_ASSOC; REAL_SUB_RZERO] THEN
      SIMP_TAC[REAL_MUL_RINV; REAL_ENTIRE; PI_NZ; REAL_OF_NUM_EQ; ARITH] THEN
      VECTOR_ARITH_TAC;
      MATCH_MP_TAC HAS_INTEGRAL_SUB THEN
      ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL; HAS_INTEGRAL_CONST]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. z - (u:real^2->real^K)(wan_circ a s (drop t))`; `vec 0:real^1`;
                 `lift(&2 * pi)`; `(&2 * pi) % (z - hmrr_avg (u:real^2->real^K) a s)`;
                 `B:real`] HAS_INTEGRAL_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[CONTENT_1; DROP_VEC; LIFT_DROP; REAL_LE_MUL; REAL_POS; PI_POS_LE] THEN
  REWRITE_TAC[NORM_MUL; REAL_SUB_RZERO] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `&2 * pi` THEN
  MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC);;

(* Wirtinger on circles. *)

let HMRR_NORM2_CONT = prove
 (`!(g:real^2->real^N) U. g continuous_on U ==> (\x. lift(norm(g x) pow 2)) continuous_on U`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_POW_2] THEN
  MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN ASM_REWRITE_TAC[ETA_AX]);;

let HMRR_CIRC_WIRTINGER = prove
 (`!(u:real^2->real^K) U a s.
     open U /\ smooth_map_on U u /\ (!t. wan_circ a s t IN U)
     ==> drop(integral (interval[vec 0,lift(&2 * pi)])
               (\t. lift(norm(u(wan_circ a s (drop t)) - hmrr_avg u a s) pow 2))) <=
         drop(integral (interval[vec 0,lift(&2 * pi)])
               (\t. lift(norm(hmrr_ang u a (wan_circ a s (drop t))) pow 2)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(u:real^2->real^K) continuous_on U /\ hmrr_ang u a continuous_on U`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; HMRR_RADANG_SMOOTH]; ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^2->real^K`; `U:real^2->bool`; `a:real^2`; `s:real`] HMRR_CIRC_CONT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. lift(norm(hmrr_ang (u:real^2->real^K) a x) pow 2)`; `U:real^2->bool`;
                 `a:real^2`; `s:real`] HMRR_CIRC_CONT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HMRR_NORM2_CONT THEN ASM_REWRITE_TAC[ETA_AX];
    DISCH_THEN(STRIP_ASSUME_TAC o BETA_RULE)] THEN
  MP_TAC(ISPEC `(:K)` WAN_WIRTINGER_VEC) THEN REWRITE_TAC[WAN_WIRTINGER_VEC_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`\th. (u:real^2->real^K)(wan_circ a s th) - hmrr_avg u a s`;
    `\th. hmrr_ang (u:real^2->real^K) a (wan_circ a s th)`]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ALL_TAC; SIMP_TAC[]] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\t. (u:real^2->real^K)(wan_circ a s (drop t)) - hmrr_avg u a s`;
                   `\t. hmrr_ang (u:real^2->real^K) a (wan_circ a s (drop t))`;
                   `vec 0:real^1`; `lift x`] FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
    REWRITE_TAC[DROP_VEC; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM VECTOR_SUB_RZERO] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST] THEN
    MATCH_MP_TAC HMRR_CIRC_ANG_DERIV THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^2->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[WAN_CIRC_2PI];
    MATCH_MP_TAC HMRR_AVG_ZERO THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

(* Integrability of continuous integrands along circles. *)

let HMRR_CIRC_INT = prove
 (`!(h:real^2->real^N) U a s.
     h continuous_on U /\ (!t. wan_circ a s t IN U)
     ==> (\t. h(wan_circ a s (drop t))) integrable_on interval[vec 0,lift(&2 * pi)]`,
  MESON_TAC[HMRR_CIRC_CONT]);;

let HMRR_GQUAD_SMOOTH = prove
 (`!S (G:real^K->real^K^K) d U (u:real^2->real^K) (Y:real^2->real^K).
     cm_target S G d /\ open U /\ smooth_map_on U u /\ smooth_map_on U Y
     ==> smooth_map_on U (\x. lift(Y x dot (G(u x) ** Y x)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN
  ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC HMR_MATVEC_SMOOTH THEN
  EXISTS_TAC `(:real^K)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
  ASM_MESON_TAC[cm_target]);;

(* Pohozaev on one circle: radial energy <= (Lam / lam) angular energy. *)

let HMRR_DIV_ALG = prove
 (`!lam Lam x y. &0 < lam /\ lam * x <= Lam * y ==> x <= Lam / lam * y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `Lam / lam * y = (Lam * y) / lam` SUBST1_TAC THENL
   [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

let HMRR_POH_CIRCLE = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> ?K0. &0 <= K0 /\
              !(u:real^2->real^K) U a s.
                open U /\ smooth_map_on U u /\ (!t. wan_circ a s t IN U) /\
                integral (interval[vec 0,lift(&2 * pi)])
                  (\t. lift(hmrr_tv G u a (wan_circ a s (drop t)) dot
                            (wan_circ a s (drop t) - a))) = vec 0
                ==> drop(integral (interval[vec 0,lift(&2 * pi)])
                          (\t. lift(norm(hmrr_rad u a (wan_circ a s (drop t))) pow 2))) <=
                    K0 * drop(integral (interval[vec 0,lift(&2 * pi)])
                               (\t. lift(norm(hmrr_ang u a (wan_circ a s (drop t))) pow 2)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_target]) THEN
  EXISTS_TAC `Lam / lam` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:real^2->real^K`; `U:real^2->bool`; `a:real^2`; `s:real`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^2->real^K`; `U:real^2->bool`; `a:real^2`] HMRR_RADANG_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!Y. smooth_map_on U Y
        ==> (\t. lift(norm((Y:real^2->real^K)(wan_circ a s (drop t))) pow 2)) integrable_on
            interval[vec 0,lift(&2 * pi)] /\
            (\t. lift(Y(wan_circ a s (drop t)) dot
                      ((G:real^K->real^K^K)(u(wan_circ a s (drop t))) **
                       Y(wan_circ a s (drop t))))) integrable_on
            interval[vec 0,lift(&2 * pi)]`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THENL
     [MP_TAC(ISPECL [`\x. lift(norm((Y:real^2->real^K) x) pow 2)`; `U:real^2->bool`;
                     `a:real^2`; `s:real`] HMRR_CIRC_INT) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HMRR_NORM2_CONT THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
      MP_TAC(ISPECL [`\x. lift((Y:real^2->real^K) x dot
                               ((G:real^K->real^K^K)((u:real^2->real^K) x) ** Y x))`;
                     `U:real^2->bool`; `a:real^2`; `s:real`] HMRR_CIRC_INT) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN MATCH_MP_TAC HMRR_GQUAD_SMOOTH THEN
      MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `hmrr_rad (u:real^2->real^K) a`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `hmrr_ang (u:real^2->real^K) a`) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  (* the pointwise bounds of the two G-energies *)
  SUBGOAL_THEN
   `lam * drop(integral (interval[vec 0,lift(&2 * pi)])
            (\t. lift(norm(hmrr_rad (u:real^2->real^K) a (wan_circ a s (drop t))) pow 2))) <=
    drop(integral (interval[vec 0,lift(&2 * pi)])
      (\t. lift(hmrr_rad u a (wan_circ a s (drop t)) dot
                ((G:real^K->real^K^K)(u(wan_circ a s (drop t))) **
                 hmrr_rad u a (wan_circ a s (drop t))))))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM DROP_CMUL] THEN ASM_SIMP_TAC[GSYM INTEGRAL_CMUL] THEN
    MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_SIMP_TAC[INTEGRABLE_CMUL] THEN
    REWRITE_TAC[DROP_CMUL; LIFT_DROP] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `drop(integral (interval[vec 0,lift(&2 * pi)])
      (\t. lift(hmrr_ang (u:real^2->real^K) a (wan_circ a s (drop t)) dot
                ((G:real^K->real^K^K)(u(wan_circ a s (drop t))) **
                 hmrr_ang u a (wan_circ a s (drop t)))))) <=
    Lam * drop(integral (interval[vec 0,lift(&2 * pi)])
            (\t. lift(norm(hmrr_ang u a (wan_circ a s (drop t))) pow 2)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM DROP_CMUL] THEN ASM_SIMP_TAC[GSYM INTEGRAL_CMUL] THEN
    MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_SIMP_TAC[INTEGRABLE_CMUL] THEN
    REWRITE_TAC[DROP_CMUL; LIFT_DROP] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the two G-energies along the circle have equal integrals *)
  SUBGOAL_THEN
   `drop(integral (interval[vec 0,lift(&2 * pi)])
      (\t. lift(hmrr_rad (u:real^2->real^K) a (wan_circ a s (drop t)) dot
                ((G:real^K->real^K^K)(u(wan_circ a s (drop t))) **
                 hmrr_rad u a (wan_circ a s (drop t)))))) =
    drop(integral (interval[vec 0,lift(&2 * pi)])
      (\t. lift(hmrr_ang u a (wan_circ a s (drop t)) dot
                (G(u(wan_circ a s (drop t))) ** hmrr_ang u a (wan_circ a s (drop t))))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `inv(&2) * (x - y) = &0 ==> x = y`) THEN
    REWRITE_TAC[GSYM DROP_SUB; GSYM DROP_CMUL] THEN
    ASM_SIMP_TAC[GSYM INTEGRAL_SUB; GSYM INTEGRAL_CMUL; INTEGRABLE_SUB] THEN
    FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC (RAND_CONV) [GSYM DROP_VEC] THEN
                             GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) o
      check (fun th -> is_eq(concl th) && rand(concl th) = `vec 0:real^1`)) THEN
    AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^2->real^K`; `a:real^2`;
                   `wan_circ a s (drop t)`] HMRR_TV_RADANG) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[LIFT_CMUL; LIFT_SUB];
    ALL_TAC] THEN
  MATCH_MP_TAC HMRR_DIV_ALG THEN ASM_REAL_ARITH_TAC);;

(* The boundary term of the comparison argument. *)

let HMRR_DOT_AMGM = prove
 (`!p q:real^N. abs(p dot q) <= (norm p pow 2 + norm q pow 2) / &2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NORM_POW_2] THEN
  MP_TAC(ISPEC `p - q:real^N` DOT_POS_LE) THEN MP_TAC(ISPEC `p + q:real^N` DOT_POS_LE) THEN
  REWRITE_TAC[DOT_LADD; DOT_RADD; DOT_LSUB; DOT_RSUB] THEN
  MP_TAC(ISPECL [`p:real^N`; `q:real^N`] DOT_SYM) THEN REAL_ARITH_TAC);;

let HMRR_PSI_ALG = prove
 (`!P I1 I2 I3 I4 K0.
     abs P <= (I1 + I2) / &2 /\ I1 <= I3 /\ I2 <= K0 * I3 /\ I3 <= I4 /\
     &0 <= K0 /\ &0 <= I3
     ==> abs P <= (&1 + K0) / &2 * I4`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&1 + K0) / &2 * I3` THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]);;

let HMRR_PSI_BOUND = prove
 (`!(u:real^2->real^K) U a s K0.
     open U /\ smooth_map_on U u /\ (!t. wan_circ a s t IN U) /\ &0 <= K0 /\
     drop(integral (interval[vec 0,lift(&2 * pi)])
            (\t. lift(norm(hmrr_rad u a (wan_circ a s (drop t))) pow 2))) <=
     K0 * drop(integral (interval[vec 0,lift(&2 * pi)])
            (\t. lift(norm(hmrr_ang u a (wan_circ a s (drop t))) pow 2)))
     ==> abs(drop(integral (interval[vec 0,lift(&2 * pi)])
               (\t. lift((u(wan_circ a s (drop t)) - hmrr_avg u a s) dot
                         hmrr_rad u a (wan_circ a s (drop t)))))) <=
         (&1 + K0) / &2 *
         drop(integral (interval[vec 0,lift(&2 * pi)])
               (\t. lift(norm(wan_circ a s (drop t) - a) pow 2 *
                         hmr_e u (wan_circ a s (drop t)))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^2->real^K`; `U:real^2->bool`; `a:real^2`] HMRR_RADANG_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(u:real^2->real^K) continuous_on U /\ hmrr_rad u a continuous_on U /\
                hmrr_ang u a continuous_on U /\
                (\x. lift(hmr_e u x)) continuous_on U`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; HMR_E_SMOOTH]; ALL_TAC] THEN
  SUBGOAL_THEN `(\x:real^2. lift(norm(x - a) pow 2 * hmr_e (u:real^2->real^K) x))
                continuous_on U` ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    ASM_REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC HMRR_NORM2_CONT THEN
    SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x:real^2. lift(((u:real^2->real^K) x - hmrr_avg u a s) dot hmrr_rad u a x))
    continuous_on U /\
    (\x:real^2. lift(norm((u:real^2->real^K) x - hmrr_avg u a s) pow 2)) continuous_on U /\
    (\x:real^2. lift(norm(hmrr_rad (u:real^2->real^K) a x) pow 2)) continuous_on U /\
    (\x:real^2. lift(norm(hmrr_ang (u:real^2->real^K) a x) pow 2)) continuous_on U`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN ASM_REWRITE_TAC[ETA_AX] THEN
      ASM_SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; ETA_AX];
      MATCH_MP_TAC HMRR_NORM2_CONT THEN ASM_SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; ETA_AX];
      MATCH_MP_TAC HMRR_NORM2_CONT THEN ASM_REWRITE_TAC[ETA_AX];
      MATCH_MP_TAC HMRR_NORM2_CONT THEN ASM_REWRITE_TAC[ETA_AX]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!h:real^2->real^1. h continuous_on U
        ==> (\t. h(wan_circ a s (drop t))) integrable_on interval[vec 0,lift(&2 * pi)]`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HMRR_CIRC_INT THEN EXISTS_TAC `U:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY (fun tm -> FIRST_ASSUM(MP_TAC o BETA_RULE o C MATCH_MP (ASSUME tm) o
                         check (fun th -> is_forall(concl th) &&
                                          can (find_term (fun t -> t = `h:real^2->real^1`))
                                            (concl th))))
   [`(\x:real^2. lift(((u:real^2->real^K) x - hmrr_avg u a s) dot hmrr_rad u a x))
     continuous_on U`;
    `(\x:real^2. lift(norm((u:real^2->real^K) x - hmrr_avg u a s) pow 2)) continuous_on U`;
    `(\x:real^2. lift(norm(hmrr_rad (u:real^2->real^K) a x) pow 2)) continuous_on U`;
    `(\x:real^2. lift(norm(hmrr_ang (u:real^2->real^K) a x) pow 2)) continuous_on U`;
    `(\x:real^2. lift(norm(x - a) pow 2 * hmr_e (u:real^2->real^K) x)) continuous_on U`] THEN
  REPEAT DISCH_TAC THEN
  MATCH_MP_TAC HMRR_PSI_ALG THEN
  MAP_EVERY EXISTS_TAC
   [`drop(integral (interval[vec 0,lift(&2 * pi)])
      (\t. lift(norm((u:real^2->real^K)(wan_circ a s (drop t)) - hmrr_avg u a s) pow 2)))`;
    `drop(integral (interval[vec 0,lift(&2 * pi)])
      (\t. lift(norm(hmrr_rad (u:real^2->real^K) a (wan_circ a s (drop t))) pow 2)))`;
    `drop(integral (interval[vec 0,lift(&2 * pi)])
      (\t. lift(norm(hmrr_ang (u:real^2->real^K) a (wan_circ a s (drop t))) pow 2)))`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* the AM-GM bound for the boundary term *)
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `drop(integral (interval[vec 0,lift(&2 * pi)])
        (\t. inv(&2) % (lift(norm((u:real^2->real^K)(wan_circ a s (drop t)) -
                                  hmrr_avg u a s) pow 2) +
                        lift(norm(hmrr_rad u a (wan_circ a s (drop t))) pow 2))))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM NORM_1] THEN MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
      ASM_SIMP_TAC[INTEGRABLE_CMUL; INTEGRABLE_ADD] THEN
      X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
      REWRITE_TAC[NORM_LIFT; DROP_CMUL; DROP_ADD; LIFT_DROP] THEN
      MP_TAC(ISPECL [`(u:real^2->real^K)(wan_circ a s (drop t)) - hmrr_avg u a s`;
                     `hmrr_rad (u:real^2->real^K) a (wan_circ a s (drop t))`] HMRR_DOT_AMGM) THEN
      REAL_ARITH_TAC;
      ASM_SIMP_TAC[INTEGRAL_CMUL; INTEGRAL_ADD; INTEGRABLE_ADD; DROP_CMUL; DROP_ADD] THEN
      REAL_ARITH_TAC];
    (* Wirtinger *)
    MATCH_MP_TAC HMRR_CIRC_WIRTINGER THEN EXISTS_TAC `U:real^2->bool` THEN ASM_REWRITE_TAC[];
    (* angular <= full energy *)
    MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
    REWRITE_TAC[GSYM HMRR_RAD_ANG_NORM] THEN
    MP_TAC(SPEC `norm(hmrr_rad (u:real^2->real^K) a (wan_circ a s (drop t)))` REAL_LE_POW_2) THEN
    REAL_ARITH_TAC;
    (* positivity *)
    MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2]]);;

(* Pohozaev on a circle in energy form. *)

let HMRR_POH_CIRCLE_E = prove
 (`!(u:real^2->real^K) U a s K0.
     open U /\ smooth_map_on U u /\ (!t. wan_circ a s t IN U) /\ &0 < s /\ &0 <= K0 /\
     drop(integral (interval[vec 0,lift(&2 * pi)])
            (\t. lift(norm(hmrr_rad u a (wan_circ a s (drop t))) pow 2))) <=
     K0 * drop(integral (interval[vec 0,lift(&2 * pi)])
            (\t. lift(norm(hmrr_ang u a (wan_circ a s (drop t))) pow 2)))
     ==> drop(integral (interval[vec 0,lift(&2 * pi)])
                (\t. lift(hmr_e u (wan_circ a s (drop t))))) <=
         (&1 + K0) *
         drop(integral (interval[vec 0,lift(&2 * pi)])
                (\t. lift(norm(hmrr_ang u a (wan_circ a s (drop t))) pow 2 /
                          norm(wan_circ a s (drop t) - a) pow 2)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^2->real^K`; `U:real^2->bool`; `a:real^2`] HMRR_RADANG_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\t. lift(norm(hmrr_rad (u:real^2->real^K) a (wan_circ a s (drop t))) pow 2)) integrable_on
    interval[vec 0,lift(&2 * pi)] /\
    (\t. lift(norm(hmrr_ang (u:real^2->real^K) a (wan_circ a s (drop t))) pow 2)) integrable_on
    interval[vec 0,lift(&2 * pi)]`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`\x. lift(norm(hmrr_rad (u:real^2->real^K) a x) pow 2)`;
                     `U:real^2->bool`; `a:real^2`; `s:real`] HMRR_CIRC_INT);
      MP_TAC(ISPECL [`\x. lift(norm(hmrr_ang (u:real^2->real^K) a x) pow 2)`;
                     `U:real^2->bool`; `a:real^2`; `s:real`] HMRR_CIRC_INT)] THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HMRR_NORM2_CONT THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\t. lift(hmr_e (u:real^2->real^K) (wan_circ a s (drop t)))) =
    (\t. inv(s pow 2) % (lift(norm(hmrr_rad u a (wan_circ a s (drop t))) pow 2) +
                         lift(norm(hmrr_ang u a (wan_circ a s (drop t))) pow 2)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `t:real^1` THEN
    REWRITE_TAC[GSYM LIFT_ADD; GSYM LIFT_CMUL; LIFT_EQ; HMRR_RAD_ANG_NORM; WAN_CIRC_NORM] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < s ==> abs s = s`] THEN
    SUBGOAL_THEN `~(s pow 2 = &0)` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_EQ_0; REAL_LT_IMP_NZ] THEN ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\t. lift(norm(hmrr_ang (u:real^2->real^K) a (wan_circ a s (drop t))) pow 2 /
              norm(wan_circ a s (drop t) - a) pow 2)) =
    (\t. inv(s pow 2) % lift(norm(hmrr_ang u a (wan_circ a s (drop t))) pow 2))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; WAN_CIRC_NORM; GSYM LIFT_CMUL; LIFT_EQ] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < s ==> abs s = s`] THEN REWRITE_TAC[real_div] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGRAL_CMUL; INTEGRAL_ADD; INTEGRABLE_ADD; DROP_CMUL; DROP_ADD] THEN
  MATCH_MP_TAC(REAL_ARITH `c * i2 <= c * (k * i3) ==> c * (i2 + i3) <= (&1 + k) * (c * i3)`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ; REAL_LE_POW_2]);;

(* Pohozaev on annuli: the energy is controlled by the angular energy. *)

let HMRR_POH_ANNULUS = prove
 (`!(u:real^2->real^K) U a r1 r2 K0.
     open U /\ smooth_map_on U u /\ &0 < r1 /\ r1 <= r2 /\
     {x | r1 <= norm(x - a) /\ norm(x - a) <= r2} SUBSET U /\ &0 <= K0 /\
     (!s. r1 <= s /\ s <= r2
          ==> drop(integral (interval[vec 0,lift(&2 * pi)])
                 (\t. lift(norm(hmrr_rad u a (wan_circ a s (drop t))) pow 2))) <=
              K0 * drop(integral (interval[vec 0,lift(&2 * pi)])
                 (\t. lift(norm(hmrr_ang u a (wan_circ a s (drop t))) pow 2))))
     ==> hmrr_en u a r1 r2 <=
         (&1 + K0) * drop(integral (hmrr_ann a r1 r2)
                           (\x. lift(norm(hmrr_ang u a x) pow 2 / norm(x - a) pow 2)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^2->real^K`; `U:real^2->bool`; `a:real^2`] HMRR_RADANG_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `KK = {x:real^2 | r1 <= norm(x - a) /\ norm(x - a) <= r2}` THEN
  SUBGOAL_THEN `compact(KK:real^2->bool) /\ hmrr_ann a r1 r2 SUBSET KK` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "KK" THEN CONJ_TAC THENL
     [SUBGOAL_THEN `{x:real^2 | r1 <= norm(x - a) /\ norm(x - a) <= r2} =
                    cball(a,r2) DIFF ball(a,r1)` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_CBALL; IN_BALL; dist] THEN
        GEN_TAC THEN REWRITE_TAC[NORM_SUB] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[COMPACT_CBALL; OPEN_BALL]];
      REWRITE_TAC[hmrr_ann; SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2. x IN KK ==> ~(norm(x - a) pow 2 = &0)` ASSUME_TAC THENL
   [EXPAND_TAC "KK" THEN REWRITE_TAC[IN_ELIM_THM; REAL_POW_EQ_0] THEN
    REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(hmr_e (u:real^2->real^K) x)) absolutely_integrable_on hmrr_ann a r1 r2 /\
    (\x. lift(norm(hmrr_ang (u:real^2->real^K) a x) pow 2 / norm(x - a) pow 2))
    absolutely_integrable_on hmrr_ann a r1 r2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `KK:real^2->bool` THEN ASM_REWRITE_TAC[HMRR_ANN_FACTS] THEN
    MATCH_MP_TAC WAN_CONT_COMPACT_ABS_INT THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `U:real^2->bool` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; HMR_E_SMOOTH] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `KK:real^2->bool` THEN
      ASM_REWRITE_TAC[SUBSET_REFL] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\x. lift(norm(hmrr_ang (u:real^2->real^K) a x) pow 2 / norm(x - a) pow 2)) =
      (\x. inv(norm(x - a) pow 2) % lift(norm(hmrr_ang u a x) pow 2))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_CMUL; LIFT_EQ; real_div] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`\x:real^2. norm(x - a) pow 2`; `KK:real^2->bool`] CONTINUOUS_ON_INV) THEN
      ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC HMRR_NORM2_CONT THEN
      SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
      MATCH_MP_TAC HMRR_NORM2_CONT THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `U:real^2->bool` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; ETA_AX]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. lift(hmr_e (u:real^2->real^K) x)`; `a:real^2`; `&0`;
                 `r1:real`; `r2:real`] WAN_POLAR_ANNULUS) THEN
  MP_TAC(ISPECL [`\x. lift(norm(hmrr_ang (u:real^2->real^K) a x) pow 2 / norm(x - a) pow 2)`;
                 `a:real^2`; `&0`; `r1:real`; `r2:real`] WAN_POLAR_ANNULUS) THEN
  REWRITE_TAC[REAL_ADD_LID; GSYM hmrr_ann] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[hmrr_en] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM DROP_CMUL] THEN
  ASM_SIMP_TAC[GSYM INTEGRAL_CMUL; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
  MATCH_MP_TAC INTEGRAL_DROP_LE THEN
  ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; INTEGRABLE_CMUL] THEN
  X_GEN_TAC `rho:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN STRIP_TAC THEN
  REWRITE_TAC[DROP_CMUL] THEN
  MATCH_MP_TAC(REAL_ARITH `r * x <= r * (k * y) ==> r * x <= k * (r * y)`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC HMRR_POH_CIRCLE_E THEN EXISTS_TAC `U:real^2->bool` THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  X_GEN_TAC `t:real` THEN
  UNDISCH_TAC `(KK:real^2->bool) SUBSET U` THEN REWRITE_TAC[SUBSET] THEN
  DISCH_THEN MATCH_MP_TAC THEN EXPAND_TAC "KK" THEN
  REWRITE_TAC[IN_ELIM_THM; WAN_CIRC_NORM] THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The Sacks-Uhlenbeck comparison map on a dyadic annulus s/2 < |x - a| < s. *)
(* hmrr_phi is the harmonic function log(|x - a|^2 / (s/2)^2) / (2 log 2),   *)
(* equal to 0 on the inner and 1 on the outer circle; hmrr_q interpolates    *)
(* the two circle averages of u.  Its radial derivative is constant, its     *)
(* angular derivative and vector Laplacian vanish.                           *)
(* ========================================================================= *)

let hmrr_phi = new_definition
 `hmrr_phi (a:real^2) s (x:real^2) =
    inv(&2 * log(&2)) * (log(norm(x - a) pow 2) - log((s / &2) pow 2))`;;

let hmrr_q = new_definition
 `hmrr_q (u:real^2->real^K) (a:real^2) s (x:real^2) =
    hmrr_avg u a (s / &2) + hmrr_phi a s x % (hmrr_avg u a s - hmrr_avg u a (s / &2))`;;

let HMRR_D_SQN = prove
 (`!(a:real^2) i z. 1 <= i /\ i <= 2
                    ==> cml_d i (\y:real^2. norm(y - a) pow 2) z = &2 * (z$i - a$i)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_POW_2] THEN
  MP_TAC(ISPECL [`(:real^2)`; `\y:real^2. y - a`; `z:real^2`; `i:num`] HMR_D_SQ) THEN
  REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN ANTS_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `partial_derivative i (\y:real^2. y - a) z = basis i` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`i:num`; `\y:real^2. y`; `\y:real^2. a:real^2`; `z:real^2`]
                  PARTIAL_DERIVATIVE_SUB) THEN
    REWRITE_TAC[DIFFERENTIABLE_CONST; DIFFERENTIABLE_ID; PARTIAL_DERIVATIVE_ID;
                PARTIAL_DERIVATIVE_CONST; VECTOR_SUB_RZERO; ETA_AX];
    ASM_SIMP_TAC[DOT_BASIS; DIMINDEX_2; VECTOR_SUB_COMPONENT]]);;

let HMRR_PUNCT = prove
 (`!(a:real^2). open((:real^2) DELETE a) /\
                (!x. x IN (:real^2) DELETE a ==> &0 < norm(x - a) pow 2)`,
  SIMP_TAC[OPEN_DELETE; OPEN_UNIV; IN_DELETE; IN_UNIV] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_POW_LT THEN
  ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]);;

let HMRR_PHI_SMOOTH = prove
 (`!(a:real^2) s. smooth_map_on ((:real^2) DELETE a) (\x. lift(hmrr_phi a s x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hmrr_phi] THEN
  MP_TAC(SPEC `a:real^2` HMRR_PUNCT) THEN STRIP_TAC THEN
  MATCH_MP_TAC CML_SM_CMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CML_SM_SUB THEN ASM_REWRITE_TAC[CML_SM_CONST] THEN
  MATCH_MP_TAC CML_SM_LOG THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
  REWRITE_TAC[HMR_SQ_SMOOTH; SUBSET_UNIV]);;

let HMRR_PHI_EQ = prove
 (`!(a:real^2) s. hmrr_phi a s =
                  (\x. inv(&2 * log(&2)) * (log(norm(x - a) pow 2) - log((s / &2) pow 2)))`,
  REWRITE_TAC[FUN_EQ_THM; hmrr_phi]);;

let HMRR_LOG2_POS = prove
 (`&0 < log(&2)`,
  MATCH_MP_TAC LOG_POS_LT THEN REAL_ARITH_TAC);;

let HMRR_PHI_D = prove
 (`!(a:real^2) s x i.
     ~(x = a) /\ 1 <= i /\ i <= 2
     ==> cml_d i (hmrr_phi a s) x = (x$i - a$i) / (log(&2) * norm(x - a) pow 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `a:real^2` HMRR_PUNCT) THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^2) IN (:real^2) DELETE a` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_DELETE; IN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on ((:real^2) DELETE a) (\x:real^2. lift(norm(x - a) pow 2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[HMR_SQ_SMOOTH; SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on ((:real^2) DELETE a) (\x:real^2. lift(log(norm(x - a) pow 2)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CML_SM_LOG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[HMRR_PHI_EQ] THEN
  MP_TAC(ISPECL [`(:real^2) DELETE (a:real^2)`; `inv(&2 * log(&2))`;
                 `\x:real^2. log(norm(x - a) pow 2) - log((s / &2) pow 2)`; `x:real^2`; `i:num`]
    CML_D_CMUL) THEN
  ASM_SIMP_TAC[CML_SM_SUB; CML_SM_CONST] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`(:real^2) DELETE (a:real^2)`; `\x:real^2. log(norm(x - a) pow 2)`;
                 `\x:real^2. log((s / &2) pow 2)`; `x:real^2`; `i:num`] CML_D_SUB) THEN
  ASM_REWRITE_TAC[CML_SM_CONST] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`(:real^2) DELETE (a:real^2)`; `\x:real^2. norm(x - a) pow 2`;
                 `x:real^2`; `i:num`] CML_D_LOG) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[HMRR_D_SQN; CML_D_CONST] THEN
  SUBGOAL_THEN `&0 < norm(x - a:real^2) pow 2` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC HMRR_LOG2_POS THEN CONV_TAC REAL_FIELD);;

let HMRR_PHI_LAP = prove
 (`!(a:real^2) s x. ~(x = a) ==> cml_lap (hmrr_phi a s) x = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `a:real^2` HMRR_PUNCT) THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^2) IN (:real^2) DELETE a` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_DELETE; IN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on ((:real^2) DELETE a) (\x:real^2. lift(norm(x - a) pow 2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[HMR_SQ_SMOOTH; SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on ((:real^2) DELETE a) (\x:real^2. lift(log(norm(x - a) pow 2)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CML_SM_LOG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* first derivatives on the punctured plane *)
  SUBGOAL_THEN
   `!i y. y IN (:real^2) DELETE a
          ==> cml_d i (hmrr_phi a s) y =
              inv(&2 * log(&2)) * cml_d i (\x:real^2. log(norm(x - a) pow 2)) y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[HMRR_PHI_EQ] THEN
    MP_TAC(ISPECL [`(:real^2) DELETE (a:real^2)`; `inv(&2 * log(&2))`;
                   `\x:real^2. log(norm(x - a) pow 2) - log((s / &2) pow 2)`; `y:real^2`; `i:num`]
      CML_D_CMUL) THEN
    ASM_SIMP_TAC[CML_SM_SUB; CML_SM_CONST] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`(:real^2) DELETE (a:real^2)`; `\x:real^2. log(norm(x - a) pow 2)`;
                   `\x:real^2. log((s / &2) pow 2)`; `y:real^2`; `i:num`] CML_D_SUB) THEN
    ASM_REWRITE_TAC[CML_SM_CONST] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[CML_D_CONST; REAL_SUB_RZERO; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. cml_d i (cml_d i (hmrr_phi a s)) x =
        inv(&2 * log(&2)) * cml_d i (cml_d i (\x:real^2. log(norm(x - a) pow 2))) x`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`(:real^2) DELETE (a:real^2)`; `cml_d i (hmrr_phi a s)`;
                   `\y. inv(&2 * log(&2)) * cml_d i (\x:real^2. log(norm(x - a) pow 2)) y`;
                   `x:real^2`; `i:num`] CML_D_LOCAL) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`(:real^2) DELETE (a:real^2)`; `inv(&2 * log(&2))`;
                   `cml_d i (\x:real^2. log(norm(x - a) pow 2))`; `x:real^2`; `i:num`]
      CML_D_CMUL) THEN
    ASM_SIMP_TAC[CML_D_SMOOTH; ETA_AX];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[cml_lap; GSYM REAL_ADD_LDISTRIB] THEN
  REWRITE_TAC[GSYM cml_lap] THEN
  MP_TAC(ISPECL [`(:real^2) DELETE (a:real^2)`; `\x:real^2. norm(x - a) pow 2`; `x:real^2`]
    CML_LAP_LOG) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[HMR_LAP_SQ; cml_grad2] THEN
  SIMP_TAC[HMRR_D_SQN; ARITH] THEN REWRITE_TAC[HMRR_NORM2_SUB] THEN
  REWRITE_TAC[REAL_ENTIRE] THEN DISJ2_TAC THEN
  REWRITE_TAC[real_div; REAL_ENTIRE] THEN DISJ1_TAC THEN REAL_ARITH_TAC);;

(* Values of the interpolating function. *)

let HMRR_PHI_VALUES = prove
 (`!(a:real^2) s x.
     &0 < s
     ==> (norm(x - a) = s ==> hmrr_phi a s x = &1) /\
         (norm(x - a) = s / &2 ==> hmrr_phi a s x = &0) /\
         (s / &2 <= norm(x - a) /\ norm(x - a) <= s
          ==> &0 <= hmrr_phi a s x /\ hmrr_phi a s x <= &1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `log(s pow 2) = log((s / &2) pow 2) + &2 * log(&2)` ASSUME_TAC THENL
   [SUBGOAL_THEN `s pow 2 = (s / &2) pow 2 * &2 pow 2` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[LOG_MUL; REAL_POW_LT; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH; LOG_POW] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC HMRR_LOG2_POS THEN DISCH_TAC THEN
  REWRITE_TAC[hmrr_phi] THEN REPEAT CONJ_TAC THENL
   [DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < log(&2)` THEN CONV_TAC REAL_FIELD;
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO];
    STRIP_TAC THEN
    SUBGOAL_THEN `log((s / &2) pow 2) <= log(norm(x - a:real^2) pow 2) /\
                  log(norm(x - a:real^2) pow 2) <= log(s pow 2)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
      REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_POW_LE2) THEN
      TRY(MATCH_MP_TAC REAL_POW_LT) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < inv(&2 * log(&2))` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `inv(&2 * log(&2)) * (&2 * log(&2))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < log(&2)` THEN
        CONV_TAC REAL_FIELD]]]);;

(* Affine functions of a scalar: derivatives. *)

let HMRR_AFF_SMOOTH = prove
 (`!s (f:real^2->real) (A:real^K) V.
     open s /\ smooth_map_on s (\x. lift(f x))
     ==> smooth_map_on s (\x. A + f x % V)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
  SUBGOAL_THEN `(\x. (f:real^2->real) x % (V:real^K)) = (\x. drop(lift(f x)) % V)`
  SUBST1_TAC THENL [REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST]);;

let HMRR_AFF_PD = prove
 (`!s (f:real^2->real) (A:real^K) V x i.
     open s /\ smooth_map_on s (\x. lift(f x)) /\ x IN s
     ==> partial_derivative i (\x. A + f x % V) x = cml_d i f x % V`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^2. lift(f x)) differentiable (at x)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. (f:real^2->real) x % (V:real^K)) = (\x. drop(lift(f x)) % V)`
  ASSUME_TAC THENL [REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN `(\x. (f:real^2->real) x % (V:real^K)) differentiable (at x)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`i:num`; `\x:real^2. (A:real^K)`; `\x. (f:real^2->real) x % (V:real^K)`;
                 `x:real^2`] PARTIAL_DERIVATIVE_ADD) THEN
  ASM_REWRITE_TAC[DIFFERENTIABLE_CONST] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[PARTIAL_DERIVATIVE_CONST; VECTOR_ADD_LID] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`i:num`; `\x:real^2. lift((f:real^2->real) x)`; `\x:real^2. (V:real^K)`;
                 `x:real^2`] PARTIAL_DERIVATIVE_MUL) THEN
  ASM_REWRITE_TAC[DIFFERENTIABLE_CONST] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[PARTIAL_DERIVATIVE_CONST; VECTOR_MUL_RZERO; VECTOR_ADD_LID; cml_d]);;

let HMRR_AFF_VLAP = prove
 (`!s (f:real^2->real) (A:real^K) V x.
     open s /\ smooth_map_on s (\x. lift(f x)) /\ x IN s
     ==> hmr_vlap (\x. A + f x % V) x = cml_lap f x % V`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hmr_vlap; DIMINDEX_2; VSUM_2; cml_lap] THEN
  SUBGOAL_THEN
   `!i. partial_derivative i (partial_derivative i (\x. (A:real^K) + (f:real^2->real) x % V))
          (x:real^2) =
        cml_d i (cml_d i f) x % V`
  (fun th -> REWRITE_TAC[th; VECTOR_ADD_RDISTRIB]) THEN
  GEN_TAC THEN
  MP_TAC(ISPECL [`i:num`; `partial_derivative i (\x. (A:real^K) + (f:real^2->real) x % V)`;
                 `\y. vec 0 + cml_d i (f:real^2->real) y % (V:real^K)`; `s:real^2->bool`;
                 `x:real^2`] PARTIAL_DERIVATIVE_LOCAL_OPEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN REWRITE_TAC[VECTOR_ADD_LID] THEN
    MATCH_MP_TAC HMRR_AFF_PD THEN EXISTS_TAC `s:real^2->bool` THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC HMRR_AFF_PD THEN EXISTS_TAC `s:real^2->bool` THEN
  ASM_SIMP_TAC[CML_D_SMOOTH]);;

(* The comparison map. *)

let HMRR_Q_EQ = prove
 (`!(u:real^2->real^K) a s.
     hmrr_q u a s =
     (\x. hmrr_avg u a (s / &2) + hmrr_phi a s x % (hmrr_avg u a s - hmrr_avg u a (s / &2)))`,
  REWRITE_TAC[FUN_EQ_THM; hmrr_q]);;

let HMRR_Q_FACTS = prove
 (`!(u:real^2->real^K) a s x.
     ~(x = a)
     ==> (!i. partial_derivative i (hmrr_q u a s) x =
              cml_d i (hmrr_phi a s) x % (hmrr_avg u a s - hmrr_avg u a (s / &2))) /\
         hmr_vlap (hmrr_q u a s) x = vec 0 /\
         hmrr_rad (hmrr_q u a s) a x =
         inv(log(&2)) % (hmrr_avg u a s - hmrr_avg u a (s / &2)) /\
         hmrr_ang (hmrr_q u a s) a x = vec 0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `a:real^2` HMRR_PUNCT) THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^2) IN (:real^2) DELETE a` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_DELETE; IN_UNIV]; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^2`; `s:real`] HMRR_PHI_SMOOTH) THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!i. partial_derivative i (hmrr_q (u:real^2->real^K) a s) x =
        cml_d i (hmrr_phi a s) x % (hmrr_avg u a s - hmrr_avg u a (s / &2))`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[HMRR_Q_EQ] THEN MATCH_MP_TAC HMRR_AFF_PD THEN
    EXISTS_TAC `(:real^2) DELETE (a:real^2)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[HMRR_Q_EQ] THEN
    MP_TAC(ISPECL [`(:real^2) DELETE (a:real^2)`; `hmrr_phi a s`;
                   `hmrr_avg (u:real^2->real^K) a (s / &2)`;
                   `hmrr_avg (u:real^2->real^K) a s - hmrr_avg u a (s / &2)`; `x:real^2`]
      HMRR_AFF_VLAP) THEN
    ASM_REWRITE_TAC[ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[HMRR_PHI_LAP; VECTOR_MUL_LZERO];
    ALL_TAC] THEN
  ASM_SIMP_TAC[hmrr_rad; hmrr_ang; HMRR_PHI_D; ARITH; VECTOR_MUL_ASSOC;
               GSYM VECTOR_ADD_RDISTRIB] THEN
  SUBGOAL_THEN `~(norm(x - a:real^2) pow 2 = &0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_NZ]; ALL_TAC] THEN
  MP_TAC HMRR_LOG2_POS THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[real_div] THEN
    UNDISCH_TAC `~(norm(x - a:real^2) pow 2 = &0)` THEN REWRITE_TAC[HMRR_NORM2_SUB] THEN
    UNDISCH_TAC `&0 < log(&2)` THEN CONV_TAC REAL_FIELD;
    REWRITE_TAC[VECTOR_MUL_EQ_0] THEN DISJ1_TAC THEN REWRITE_TAC[real_div] THEN
    CONV_TAC REAL_RING]);;

let HMRR_Q_SMOOTH = prove
 (`!(u:real^2->real^K) a s. smooth_map_on ((:real^2) DELETE a) (hmrr_q u a s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HMRR_Q_EQ] THEN MATCH_MP_TAC HMRR_AFF_SMOOTH THEN
  REWRITE_TAC[HMRR_PUNCT; HMRR_PHI_SMOOTH]);;

let HMRR_Q_VALUES = prove
 (`!(u:real^2->real^K) a s x.
     &0 < s
     ==> (norm(x - a) = s ==> hmrr_q u a s x = hmrr_avg u a s) /\
         (norm(x - a) = s / &2 ==> hmrr_q u a s x = hmrr_avg u a (s / &2)) /\
         (!z B. s / &2 <= norm(x - a) /\ norm(x - a) <= s /\
                norm(z - hmrr_avg u a s) <= B /\ norm(z - hmrr_avg u a (s / &2)) <= B
                ==> norm(z - hmrr_q u a s x) <= B)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`a:real^2`; `s:real`; `x:real^2`] HMRR_PHI_VALUES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REWRITE_TAC[hmrr_q] THEN REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN ASM_SIMP_TAC[] THEN VECTOR_ARITH_TAC;
    DISCH_TAC THEN ASM_SIMP_TAC[] THEN VECTOR_ARITH_TAC;
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_conj o snd o dest_imp o concl) o
      check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ABBREV_TAC `p = hmrr_phi a s x` THEN
    SUBGOAL_THEN
     `z - (hmrr_avg (u:real^2->real^K) a (s / &2) +
           p % (hmrr_avg u a s - hmrr_avg u a (s / &2))) =
      (&1 - p) % (z - hmrr_avg u a (s / &2)) + p % (z - hmrr_avg u a s)`
    SUBST1_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 - p) * B + p * B` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm((&1 - p) % (z - hmrr_avg (u:real^2->real^K) a (s / &2))) +
                  norm(p % (z - hmrr_avg u a s))` THEN
      REWRITE_TAC[NORM_TRIANGLE; NORM_MUL] THEN
      MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC]]);;

(* ========================================================================= *)
(* The Sacks-Uhlenbeck inequality on one dyadic annulus.  For w = u - q      *)
(* (q the comparison map hmrr_q) the field                                   *)
(* hmrr_sf w = (w.D_1 w, w.D_2 w) has divergence |Dw|^2 + w.Lap u;           *)
(* its circle fluxes are the boundary terms Psi(s), Psi(s/2) (the q part     *)
(* integrates to 0 against u - avg); with the Pohozaev lower bound           *)
(* |Dw|^2 >= |ang u|^2 / |x - a|^2 and |w| <= osc u:                         *)
(*   (1/(1 + K0) - osc B0) E(s/2, s) <= Psi(s) - Psi(s/2).                 *)
(* ========================================================================= *)

let hmrr_sf = new_definition
 `hmrr_sf (w:real^2->real^K) (x:real^2) =
    vector[w x dot partial_derivative 1 w x; w x dot partial_derivative 2 w x]:real^2`;;

let HMRR_SF_SMOOTH = prove
 (`!(w:real^2->real^K) U. open U /\ smooth_map_on U w ==> smooth_map_on U (hmrr_sf w)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [MATCH_MP SMOOTH_MAP_ON_COMPONENTWISE (ASSUME `open(U:real^2->bool)`)] THEN
  REWRITE_TAC[DIMINDEX_2; ARITH_RULE `1 <= k /\ k <= 2 <=> k = 1 \/ k = 2`] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[hmrr_sf; VECTOR_2] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; ETA_AX]);;

let HMRR_SF_DIV = prove
 (`!(w:real^2->real^K) U x.
     open U /\ smooth_map_on U w /\ x IN U
     ==> partial_derivative 1 (hmrr_sf w) x$1 + partial_derivative 2 (hmrr_sf w) x$2 =
         hmr_e w x + w x dot hmr_vlap w x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(hmrr_sf (w:real^2->real^K)) differentiable (at x)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^2->bool` THEN
    ASM_SIMP_TAC[HMRR_SF_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i k. partial_derivative i (hmrr_sf (w:real^2->real^K)) x$k =
                      cml_d i (\y. hmrr_sf w y$k) x`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[cml_d] THEN
    ASM_SIMP_TAC[PARTIAL_DERIVATIVE_COMPONENT; LIFT_DROP; ETA_AX];
    ALL_TAC] THEN
  REWRITE_TAC[hmrr_sf; VECTOR_2] THEN
  SUBGOAL_THEN `!i. smooth_map_on U (partial_derivative i (w:real^2->real^K))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `w:real^2->real^K`; `partial_derivative 1 (w:real^2->real^K)`;
                 `x:real^2`; `1`] HMR_D_DOT) THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `w:real^2->real^K`; `partial_derivative 2 (w:real^2->real^K)`;
                 `x:real^2`; `2`] HMR_D_DOT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[hmr_e; hmr_vlap; DIMINDEX_2; VSUM_2; DOT_RADD] THEN REAL_ARITH_TAC);;

let HMRR_SF_DOT = prove
 (`!(w:real^2->real^K) a x. hmrr_sf w x dot (x - a) = w x dot hmrr_rad w a x`,
  REWRITE_TAC[hmrr_sf; hmrr_rad; DOT_2; VECTOR_2; VECTOR_SUB_COMPONENT; DOT_RADD; DOT_RMUL] THEN
  REAL_ARITH_TAC);;

(* Differences of maps. *)

let HMRR_SUB_FACTS = prove
 (`!(u:real^2->real^K) q U a x.
     open U /\ smooth_map_on U u /\ smooth_map_on U q /\ x IN U
     ==> (!i. partial_derivative i (\y. u y - q y) x =
              partial_derivative i u x - partial_derivative i q x) /\
         hmr_vlap (\y. u y - q y) x = hmr_vlap u x - hmr_vlap q x /\
         hmrr_rad (\y. u y - q y) a x = hmrr_rad u a x - hmrr_rad q a x /\
         hmrr_ang (\y. u y - q y) a x = hmrr_ang u a x - hmrr_ang q a x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!y i. y IN U ==> partial_derivative i (\y. (u:real^2->real^K) y - q y) y =
                     partial_derivative i u y - partial_derivative i q y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC PARTIAL_DERIVATIVE_SUB THEN
    CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC;
    ASM_SIMP_TAC[hmrr_rad] THEN VECTOR_ARITH_TAC;
    ASM_SIMP_TAC[hmrr_ang] THEN VECTOR_ARITH_TAC] THEN
  REWRITE_TAC[hmr_vlap; DIMINDEX_2; VSUM_2] THEN
  SUBGOAL_THEN
   `!i. partial_derivative i (partial_derivative i (\y. (u:real^2->real^K) y - q y)) x =
        partial_derivative i (partial_derivative i u) x -
        partial_derivative i (partial_derivative i q) x`
  (fun th -> REWRITE_TAC[th] THEN VECTOR_ARITH_TAC) THEN
  GEN_TAC THEN
  MP_TAC(ISPECL [`i:num`; `partial_derivative i (\y. (u:real^2->real^K) y - q y)`;
                 `\y. partial_derivative i (u:real^2->real^K) y - partial_derivative i q y`;
                 `U:real^2->bool`; `x:real^2`] PARTIAL_DERIVATIVE_LOCAL_OPEN) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC PARTIAL_DERIVATIVE_SUB THEN
  CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `U:real^2->bool` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]);;

(* Absolute integrability on annuli of maps continuous near the closed annulus. *)

let HMRR_ANN_ABSINT = prove
 (`!(g:real^2->real^N) U a r1 r2.
     g continuous_on U /\ {x | r1 <= norm(x - a) /\ norm(x - a) <= r2} SUBSET U
     ==> g absolutely_integrable_on hmrr_ann a r1 r2`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
  EXISTS_TAC `{x:real^2 | r1 <= norm(x - a) /\ norm(x - a) <= r2}` THEN
  REWRITE_TAC[HMRR_ANN_FACTS] THEN CONJ_TAC THENL
   [MATCH_MP_TAC WAN_CONT_COMPACT_ABS_INT THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      SUBGOAL_THEN `{x:real^2 | r1 <= norm(x - a) /\ norm(x - a) <= r2} =
                    cball(a,r2) DIFF ball(a,r1)` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_CBALL; IN_BALL; dist] THEN
        GEN_TAC THEN REWRITE_TAC[NORM_SUB] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[COMPACT_CBALL; OPEN_BALL]]];
    REWRITE_TAC[hmrr_ann; SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC]);;

(* The constant part of the radial derivative does not contribute at a node. *)

let HMRR_FLUX_NODE = prove
 (`!(u:real^2->real^K) U a t C.
     open U /\ smooth_map_on U u /\ (!th. wan_circ a t th IN U)
     ==> integral (interval[vec 0,lift(&2 * pi)])
           (\th. lift((u(wan_circ a t (drop th)) - hmrr_avg u a t) dot
                      (hmrr_rad u a (wan_circ a t (drop th)) - C))) =
         integral (interval[vec 0,lift(&2 * pi)])
           (\th. lift((u(wan_circ a t (drop th)) - hmrr_avg u a t) dot
                      hmrr_rad u a (wan_circ a t (drop th))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^2->real^K`; `U:real^2->bool`; `a:real^2`] HMRR_RADANG_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(u:real^2->real^K) continuous_on U /\ hmrr_rad u a continuous_on U`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]; ALL_TAC] THEN
  SUBGOAL_THEN `(\th. (u:real^2->real^K)(wan_circ a t (drop th))) integrable_on
                interval[vec 0,lift(&2 * pi)]` ASSUME_TAC THENL
   [MATCH_MP_TAC HMRR_CIRC_INT THEN EXISTS_TAC `U:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\th. lift(((u:real^2->real^K)(wan_circ a t (drop th)) - hmrr_avg u a t) dot C))
     has_integral vec 0) (interval[vec 0,lift(&2 * pi)])`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\th. (u:real^2->real^K)(wan_circ a t (drop th)) - hmrr_avg u a t`;
                   `vec 0:real^K`; `interval[vec 0:real^1,lift(&2 * pi)]`;
                   `\x:real^K. lift(x dot C)`] HAS_INTEGRAL_LINEAR) THEN
    REWRITE_TAC[o_DEF; DOT_LZERO; LIFT_NUM] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC HMRR_AVG_ZERO THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[linear; DOT_LADD; DOT_LMUL; LIFT_ADD; LIFT_CMUL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\th. lift(((u:real^2->real^K)(wan_circ a t (drop th)) - hmrr_avg u a t) dot
               hmrr_rad u a (wan_circ a t (drop th)))) integrable_on
    interval[vec 0,lift(&2 * pi)]`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\x. lift(((u:real^2->real^K) x - hmrr_avg u a t) dot hmrr_rad u a x)`;
                   `U:real^2->bool`; `a:real^2`; `t:real`] HMRR_CIRC_INT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; ETA_AX];
    ALL_TAC] THEN
  MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  SUBGOAL_THEN
   `integral (interval[vec 0,lift(&2 * pi)])
      (\th. lift(((u:real^2->real^K)(wan_circ a t (drop th)) - hmrr_avg u a t) dot
                 hmrr_rad u a (wan_circ a t (drop th)))) =
    integral (interval[vec 0,lift(&2 * pi)])
      (\th. lift(((u:real^2->real^K)(wan_circ a t (drop th)) - hmrr_avg u a t) dot
                 hmrr_rad u a (wan_circ a t (drop th)))) - vec 0`
  SUBST1_TAC THENL [REWRITE_TAC[VECTOR_SUB_RZERO]; ALL_TAC] THEN
  REWRITE_TAC[DOT_RSUB; LIFT_SUB] THEN MATCH_MP_TAC HAS_INTEGRAL_SUB THEN
  ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL]);;

(* The Sacks-Uhlenbeck inequality on one dyadic annulus. *)

let HMRR_SAU_ANNULUS = prove
 (`!(u:real^2->real^K) U a s K0 B0 Om.
     open U /\ smooth_map_on U u /\ (!x. x IN U ==> ~(x = a)) /\ &0 < s /\
     {x | s / &2 <= norm(x - a) /\ norm(x - a) <= s} SUBSET U /\
     &0 <= K0 /\ &0 <= B0 /\
     (!t. s / &2 <= t /\ t <= s
          ==> drop(integral (interval[vec 0,lift(&2 * pi)])
                 (\th. lift(norm(hmrr_rad u a (wan_circ a t (drop th))) pow 2))) <=
              K0 * drop(integral (interval[vec 0,lift(&2 * pi)])
                 (\th. lift(norm(hmrr_ang u a (wan_circ a t (drop th))) pow 2)))) /\
     (!x. s / &2 <= norm(x - a) /\ norm(x - a) <= s
          ==> norm(hmr_vlap u x) <= B0 * hmr_e u x) /\
     (!y z. s / &2 <= norm(y - a) /\ norm(y - a) <= s /\
            s / &2 <= norm(z - a) /\ norm(z - a) <= s
            ==> norm(u y - u z) <= Om)
     ==> (inv(&1 + K0) - Om * B0) * hmrr_en u a (s / &2) s <=
         drop(integral (interval[vec 0,lift(&2 * pi)])
                (\th. lift((u(wan_circ a s (drop th)) - hmrr_avg u a s) dot
                           hmrr_rad u a (wan_circ a s (drop th))))) -
         drop(integral (interval[vec 0,lift(&2 * pi)])
                (\th. lift((u(wan_circ a (s / &2) (drop th)) - hmrr_avg u a (s / &2)) dot
                           hmrr_rad u a (wan_circ a (s / &2) (drop th)))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "poh") (CONJUNCTS_THEN2 (LABEL_TAC "lap")
     (LABEL_TAC "osc")))))))))) THEN
  ABBREV_TAC `KK = {x:real^2 | s / &2 <= norm(x - a) /\ norm(x - a) <= s}` THEN
  SUBGOAL_THEN `!t th. (t = s \/ t = s / &2) ==> wan_circ a t th IN (KK:real^2->bool)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "KK" THEN
    REWRITE_TAC[IN_ELIM_THM; WAN_CIRC_NORM] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t th. (t = s \/ t = s / &2) ==> wan_circ a t th IN (U:real^2->bool)`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Om` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm((u:real^2->real^K)(wan_circ a s (&0)) - u(wan_circ a s (&0)))` THEN
    REWRITE_TAC[NORM_POS_LE] THEN USE_THEN "osc" MATCH_MP_TAC THEN
    REWRITE_TAC[WAN_CIRC_NORM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the comparison map and the field *)
  ABBREV_TAC `q = hmrr_q (u:real^2->real^K) a s` THEN
  SUBGOAL_THEN `smooth_map_on U (q:real^2->real^K)` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `(:real^2) DELETE a` THEN REWRITE_TAC[HMRR_Q_SMOOTH] THEN
    REWRITE_TAC[SUBSET; IN_DELETE; IN_UNIV] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `w = \y. (u:real^2->real^K) y - q y` THEN
  SUBGOAL_THEN `smooth_map_on U (w:real^2->real^K)` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  (* the divergence theorem *)
  MP_TAC(ISPECL [`hmrr_sf (w:real^2->real^K)`; `U:real^2->bool`; `a:real^2`;
                 `s / &2`; `s:real`] HMRR_DIV_ANNULUS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `smooth_map_on U (hmrr_sf (w:real^2->real^K))` MP_TAC THENL
       [MATCH_MP_TAC HMRR_SF_SMOOTH THEN ASM_REWRITE_TAC[]; SIMP_TAC[smooth_map_on]];
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM hmrr_ann] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  (* the fluxes are the boundary terms *)
  SUBGOAL_THEN
   `!t. (t = s \/ t = s / &2)
        ==> integral (interval[vec 0,lift(&2 * pi)])
              (\th. lift(hmrr_sf (w:real^2->real^K) (wan_circ a t (drop th)) dot
                         (wan_circ a t (drop th) - a))) =
            integral (interval[vec 0,lift(&2 * pi)])
              (\th. lift(((u:real^2->real^K)(wan_circ a t (drop th)) - hmrr_avg u a t) dot
                         hmrr_rad u a (wan_circ a t (drop th))))`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `integral (interval[vec 0,lift(&2 * pi)])
        (\th. lift(((u:real^2->real^K)(wan_circ a t (drop th)) - hmrr_avg u a t) dot
                   (hmrr_rad u a (wan_circ a t (drop th)) -
                    inv(log(&2)) % (hmrr_avg u a s - hmrr_avg u a (s / &2)))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `th:real^1` THEN DISCH_TAC THEN
      REWRITE_TAC[HMRR_SF_DOT] THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `wan_circ a t (drop th) IN (U:real^2->bool)` ASSUME_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`u:real^2->real^K`; `q:real^2->real^K`; `U:real^2->bool`; `a:real^2`;
                     `wan_circ a t (drop th)`] HMRR_SUB_FACTS) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `~(wan_circ a t (drop th) = a)` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`u:real^2->real^K`; `a:real^2`; `s:real`; `wan_circ a t (drop th)`]
        HMRR_Q_FACTS) THEN
      MP_TAC(ISPECL [`u:real^2->real^K`; `a:real^2`; `s:real`; `wan_circ a t (drop th)`]
        HMRR_Q_VALUES) THEN
      ASM_REWRITE_TAC[WAN_CIRC_NORM] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < s ==> abs s = s /\ abs(s / &2) = s / &2`] THEN
      REPEAT STRIP_TAC THEN EXPAND_TAC "w" THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o check (is_disj o concl)) THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < s ==> abs s = s /\ abs(s / &2) = s / &2`];
      MATCH_MP_TAC HMRR_FLUX_NODE THEN EXISTS_TAC `U:real^2->bool` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM DROP_SUB] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  (* integrability of the comparison integrands *)
  SUBGOAL_THEN `{x:real^2 | s / &2 <= norm(x - a) /\ norm(x - a) <= s} SUBSET U`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^2->real^K`; `U:real^2->bool`; `a:real^2`] HMRR_RADANG_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x. lift(hmr_e (u:real^2->real^K) x)) continuous_on U /\
                (\x. lift(norm(hmrr_ang (u:real^2->real^K) a x) pow 2 / norm(x - a) pow 2))
                continuous_on U`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; HMR_E_SMOOTH]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\x. lift(norm(hmrr_ang (u:real^2->real^K) a x) pow 2 / norm(x - a) pow 2)) =
      (\x. inv(norm(x - a) pow 2) % lift(norm(hmrr_ang u a x) pow 2))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_CMUL; LIFT_EQ; real_div] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`\x:real^2. norm(x - a) pow 2`; `U:real^2->bool`] CONTINUOUS_ON_INV) THEN
      REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC HMRR_NORM2_CONT THEN
        SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
        REWRITE_TAC[REAL_POW_EQ_0; NORM_EQ_0; VECTOR_SUB_EQ] THEN ASM_MESON_TAC[]];
      MATCH_MP_TAC HMRR_NORM2_CONT THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; ETA_AX]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(hmr_e (u:real^2->real^K) x)) absolutely_integrable_on hmrr_ann a (s / &2) s /\
    (\x. lift(norm(hmrr_ang (u:real^2->real^K) a x) pow 2 / norm(x - a) pow 2))
    absolutely_integrable_on hmrr_ann a (s / &2) s`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC HMRR_ANN_ABSINT THEN EXISTS_TAC `U:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the Pohozaev lower bound on the annulus *)
  MP_TAC(ISPECL [`u:real^2->real^K`; `U:real^2->bool`; `a:real^2`; `s / &2`; `s:real`;
                 `K0:real`] HMRR_POH_ANNULUS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(ASM_REAL_ARITH_TAC THEN NO_TAC) THEN
    REPEAT STRIP_TAC THEN USE_THEN "poh" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  (* the pointwise lower bound of the divergence *)
  SUBGOAL_THEN
   `!x. x IN hmrr_ann a (s / &2) s
        ==> norm(hmrr_ang (u:real^2->real^K) a x) pow 2 / norm(x - a) pow 2 -
            (Om * B0) * hmr_e u x <=
            partial_derivative 1 (hmrr_sf (w:real^2->real^K)) x$1 +
            partial_derivative 2 (hmrr_sf w) x$2`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN REWRITE_TAC[hmrr_ann; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN KK` ASSUME_TAC THENL
     [EXPAND_TAC "KK" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^2) IN U /\ ~(x = a)` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`w:real^2->real^K`; `U:real^2->bool`; `x:real^2`] HMRR_SF_DIV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`u:real^2->real^K`; `q:real^2->real^K`; `U:real^2->bool`; `a:real^2`;
                   `x:real^2`] HMRR_SUB_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`u:real^2->real^K`; `a:real^2`; `s:real`; `x:real^2`] HMRR_Q_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `norm(hmrr_ang (u:real^2->real^K) a x) pow 2 / norm(x - a) pow 2 <=
                  hmr_e (w:real^2->real^K) x` ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 < norm(x - a:real^2) pow 2` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      MP_TAC(ISPECL [`w:real^2->real^K`; `a:real^2`; `x:real^2`] HMRR_RAD_ANG_NORM) THEN
      SUBGOAL_THEN `hmrr_ang (w:real^2->real^K) a x = hmrr_ang u a x` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[VECTOR_SUB_RZERO]; ALL_TAC] THEN
      MP_TAC(SPEC `norm(hmrr_rad (w:real^2->real^K) a x)` REAL_LE_POW_2) THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `hmr_vlap (u:real^2->real^K) x - hmr_vlap q x = hmr_vlap u x` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[VECTOR_SUB_RZERO]; ALL_TAC] THEN
    SUBGOAL_THEN `norm((w:real^2->real^K) x) <= Om` ASSUME_TAC THENL
     [EXPAND_TAC "w" THEN REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`u:real^2->real^K`; `a:real^2`; `s:real`; `x:real^2`] HMRR_Q_VALUES) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN CONJ_TAC THEN MATCH_MP_TAC HMRR_AVG_DIST THEN
      (CONJ_TAC THENL
        [MATCH_MP_TAC HMRR_CIRC_INT THEN EXISTS_TAC `U:real^2->bool` THEN
         ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
         X_GEN_TAC `th:real` THEN USE_THEN "osc" MATCH_MP_TAC THEN
         ASM_REWRITE_TAC[WAN_CIRC_NORM] THEN ASM_REAL_ARITH_TAC]);
      ALL_TAC] THEN
    SUBGOAL_THEN `abs((w:real^2->real^K) x dot hmr_vlap u x) <= Om * (B0 * hmr_e u x)`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm((w:real^2->real^K) x) * norm(hmr_vlap (u:real^2->real^K) x)` THEN
      REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_REWRITE_TAC[NORM_POS_LE] THEN USE_THEN "lap" MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* integrate the lower bound *)
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `drop(integral (hmrr_ann a (s / &2) s)
      (\x. lift(norm(hmrr_ang (u:real^2->real^K) a x) pow 2 / norm(x - a) pow 2) -
           (Om * B0) % lift(hmr_e u x)))` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[INTEGRAL_SUB; INTEGRAL_CMUL; INTEGRABLE_CMUL;
                 ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; DROP_SUB; DROP_CMUL] THEN
    REWRITE_TAC[GSYM hmrr_en] THEN
    MATCH_MP_TAC(REAL_ARITH `i * e <= j ==> (i - c) * e <= j - c * e`) THEN
    SUBGOAL_THEN `&0 < &1 + K0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC INTEGRAL_DROP_LE THEN
    ASM_SIMP_TAC[INTEGRABLE_SUB; INTEGRABLE_CMUL; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
    REWRITE_TAC[DROP_SUB; DROP_CMUL; LIFT_DROP] THEN ASM_SIMP_TAC[]]);;

(* ========================================================================= *)
(* Oscillation on closed dyadic annuli.                                    *)
(* Two points of t/2 <= |x - a| <= t are joined inside the annulus by two   *)
(* radial segments and at most two chords of the outer circle subtending    *)
(* at most a right angle, so |u y - u z| <= 12 L t when the partials are    *)
(* bounded by L; with the small-energy bound this gives                     *)
(* osc u <= 24 sqrt(C E(0, 3t/2)) on the annulus.                           *)
(* ========================================================================= *)

let HMRR_SEG_RADIAL = prove
 (`!(a:real^2) t y.
     &0 < t /\ t / &2 <= norm(y - a) /\ norm(y - a) <= t
     ==> segment[y,a + (t / norm(y - a)) % (y - a)] SUBSET
         {x | t / &2 <= norm(x - a) /\ norm(x - a) <= t} /\
         norm(y - (a + (t / norm(y - a)) % (y - a))) <= t / &2 /\
         norm((a + (t / norm(y - a)) % (y - a)) - a) = t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `n = norm(y - a:real^2)` THEN
  SUBGOAL_THEN `&0 < n` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!c. norm(c % (y - a:real^2)) = abs c * n` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_MUL]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_SEGMENT; IN_ELIM_THM] THEN X_GEN_TAC `x:real^2` THEN
    DISCH_THEN(X_CHOOSE_THEN `l:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `x - a:real^2 = ((&1 - l) + l * t / n) % (y - a)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `abs((&1 - l) + l * t / n) * n = (&1 - l) * n + l * t` SUBST1_TAC THENL
     [SUBGOAL_THEN `&0 <= (&1 - l) + l * t / n` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
      UNDISCH_TAC `&0 < n` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 - l) * n + l * n` THEN
      CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_ADD2 THEN REWRITE_TAC[REAL_LE_REFL] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 - l) * t + l * t` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_ADD2 THEN REWRITE_TAC[REAL_LE_REFL] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC]];
    SUBGOAL_THEN `y - (a + (t / n) % (y - a)) = (&1 - t / n) % (y - a:real^2)` SUBST1_TAC THENL
     [VECTOR_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `abs(&1 - t / n) * n = t - n` SUBST1_TAC THENL
     [SUBGOAL_THEN `&1 <= t / n` ASSUME_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_ARITH `&1 <= x ==> abs(&1 - x) = x - &1`] THEN
      UNDISCH_TAC `&0 < n` THEN CONV_TAC REAL_FIELD;
      ASM_REAL_ARITH_TAC];
    REWRITE_TAC[VECTOR_ARITH `(a + x) - a:real^N = x`] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= t / n` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`; REAL_DIV_RMUL; REAL_LT_IMP_NZ]]);;

let HMRR_SEG_CHORD = prove
 (`!(a:real^2) t p q.
     &0 < t /\ norm(p - a) = t /\ norm(q - a) = t /\ &0 <= (p - a) dot (q - a)
     ==> segment[p,q] SUBSET {x | t / &2 <= norm(x - a) /\ norm(x - a) <= t} /\
         norm(p - q) <= &2 * t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC(NORM_ARITH
      `norm(p - a:real^2) = t /\ norm(q - a) = t ==> norm(p - q) <= &2 * t`) THEN
    ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[SUBSET; IN_SEGMENT; IN_ELIM_THM] THEN X_GEN_TAC `x:real^2` THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `x - a:real^2 = (&1 - l) % (p - a) + l % (q - a)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm((&1 - l) % (p - a:real^2)) + norm(l % (q - a:real^2))` THEN
    REWRITE_TAC[NORM_TRIANGLE; NORM_MUL] THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= l /\ l <= &1 ==> abs(&1 - l) = &1 - l /\ abs l = l`] THEN
    REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN REWRITE_TAC[ARITH; NORM_POS_LE] THEN
  REWRITE_TAC[NORM_POW_2; DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL] THEN
  SUBGOAL_THEN `(p - a:real^2) dot (p - a) = t pow 2 /\ (q - a:real^2) dot (q - a) = t pow 2`
  STRIP_ASSUME_TAC THENL [REWRITE_TAC[GSYM NORM_POW_2] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(q - a:real^2) dot (p - a) = (p - a) dot (q - a)` SUBST1_TAC THENL
   [REWRITE_TAC[DOT_SYM]; ALL_TAC] THEN
  ABBREV_TAC `D = (p - a:real^2) dot (q - a)` THEN
  SUBGOAL_THEN `&0 <= l * (&1 - l) * D /\ &0 <= (&2 * l - &1) pow 2 * t pow 2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2]];
    ALL_TAC] THEN
  MP_TAC(SPEC `t:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC);;

let HMRR_PERP_CHOICE = prove
 (`!(v:real^2) w. ?m. norm m = norm v /\ &0 <= v dot m /\ &0 <= m dot w`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `&0 <= (vector[--((v:real^2)$2); v$1]:real^2) dot w` THENL
   [EXISTS_TAC `vector[--((v:real^2)$2); v$1]:real^2`;
    EXISTS_TAC `--(vector[--((v:real^2)$2); v$1]:real^2)`] THEN
  ASM_REWRITE_TAC[NORM_NEG; DOT_RNEG; DOT_LNEG] THEN
  REWRITE_TAC[NORM_EQ; DOT_2; VECTOR_2] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[DOT_2; VECTOR_2] THEN REAL_ARITH_TAC);;

let HMRR_OSC_ANNULUS = prove
 (`!(u:real^2->real^K) U a t L.
     open U /\ smooth_map_on U u /\ &0 < t /\
     {x | t / &2 <= norm(x - a) /\ norm(x - a) <= t} SUBSET U /\
     (!z i. t / &2 <= norm(z - a) /\ norm(z - a) <= t /\ 1 <= i /\ i <= 2
            ==> norm(partial_derivative i u z) <= L)
     ==> !y z. t / &2 <= norm(y - a) /\ norm(y - a) <= t /\
               t / &2 <= norm(z - a) /\ norm(z - a) <= t
               ==> norm(u y - u z) <= &12 * L * t`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dl"))))) THEN
  SUBGOAL_THEN
   `!p q. segment[p,q] SUBSET {x | t / &2 <= norm(x - a) /\ norm(x - a) <= t}
          ==> norm((u:real^2->real^K) p - u q) <= &2 * L * norm(p - q)`
  (LABEL_TAC "mvt") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HMD_SEGMENT_MVT THEN EXISTS_TAC `U:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN USE_THEN "dl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `segment[p:real^2,q] SUBSET {x | t / &2 <= norm(x - a) /\ norm(x - a) <= t}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^2` THEN X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= L` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(partial_derivative 1 (u:real^2->real^K) y)` THEN
    REWRITE_TAC[NORM_POS_LE] THEN USE_THEN "dl" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^2`; `t:real`; `y:real^2`] HMRR_SEG_RADIAL) THEN
  MP_TAC(ISPECL [`a:real^2`; `t:real`; `z:real^2`] HMRR_SEG_RADIAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `y' = a + (t / norm(y - a)) % (y - a:real^2)` THEN
  ABBREV_TAC `z' = a + (t / norm(z - a)) % (z - a:real^2)` THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`y' - a:real^2`; `z' - a:real^2`] HMRR_PERP_CHOICE) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`a:real^2`; `t:real`; `y':real^2`; `a + m:real^2`] HMRR_SEG_CHORD) THEN
  MP_TAC(ISPECL [`a:real^2`; `t:real`; `a + m:real^2`; `z':real^2`] HMRR_SEG_CHORD) THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `(a + m) - a:real^2 = m`] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= L * t` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm((u:real^2->real^K) y - u y') + norm(u y' - u(a + m)) +
              norm(u(a + m) - u z') + norm(u z' - u z)` THEN
  CONJ_TAC THENL [CONV_TAC NORM_ARITH; ALL_TAC] THEN
  SUBGOAL_THEN `norm((u:real^2->real^K) y - u y') <= L * t /\
                norm((u:real^2->real^K) y' - u(a + m)) <= &4 * L * t /\
                norm((u:real^2->real^K)(a + m) - u z') <= &4 * L * t /\
                norm((u:real^2->real^K) z' - u z) <= L * t`
  MP_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * L * norm(y - y':real^2)` THEN
    CONJ_TAC THENL [USE_THEN "mvt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= L /\ L * n <= L * (t / &2) ==> &2 * L * n <= L * t`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * L * norm(y' - (a + m):real^2)` THEN
    CONJ_TAC THENL [USE_THEN "mvt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= L /\ L * n <= L * (&2 * t) ==> &2 * L * n <= &4 * L * t`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * L * norm((a + m) - z':real^2)` THEN
    CONJ_TAC THENL [USE_THEN "mvt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= L /\ L * n <= L * (&2 * t) ==> &2 * L * n <= &4 * L * t`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[NORM_SUB] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * L * norm(z - z':real^2)` THEN
    CONJ_TAC THENL [USE_THEN "mvt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= L /\ L * n <= L * (t / &2) ==> &2 * L * n <= L * t`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]]);;

(* The oscillation of the harmonic map on dyadic annuli near the point. *)

let HMRR_PD_SQ_LE = prove
 (`!(u:real^2->real^K) x i. 1 <= i /\ i <= 2
                            ==> norm(partial_derivative i u x) pow 2 <= hmr_e u x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ARITH_RULE `1 <= i /\ i <= 2 <=> i = 1 \/ i = 2`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[hmr_e; GSYM NORM_POW_2] THEN
  MP_TAC(SPEC `norm(partial_derivative 1 (u:real^2->real^K) x)` REAL_LE_POW_2) THEN
  MP_TAC(SPEC `norm(partial_derivative 2 (u:real^2->real^K) x)` REAL_LE_POW_2) THEN
  REAL_ARITH_TAC);;

let HMRR_SQRT_ALG = prove
 (`!C E t. &0 <= C /\ &0 <= E /\ &0 < t
           ==> &12 * (sqrt(&4 * C * E) / t) * t = (&24 * sqrt C) * sqrt E`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sqrt(&4 * C * E) = &2 * sqrt C * sqrt E` SUBST1_TAC THENL
   [REWRITE_TAC[SQRT_MUL] THEN
    SUBGOAL_THEN `sqrt(&4) = &2` (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC SQRT_UNIQUE THEN REAL_ARITH_TAC;
    UNDISCH_TAC `&0 < t` THEN CONV_TAC REAL_FIELD]);;

let HMRR_OSC_HARMONIC = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> ?e0 C2. &0 < e0 /\ &0 <= C2 /\
                 !(u:real^2->real^K) a r t.
                   cm_harmonic S G (ball(a,r) DELETE a) u /\
                   wan_w12 (ball(a,r) DELETE a) u /\
                   &0 < t /\ &3 / &2 * t <= r /\
                   hmrr_en u a (&0) (&3 / &2 * t) <= e0
                   ==> !y z. t / &2 <= norm(y - a) /\ norm(y - a) <= t /\
                             t / &2 <= norm(z - a) /\ norm(z - a) <= t
                             ==> norm(u y - u z) <=
                                 C2 * sqrt(hmrr_en u a (&0) (&3 / &2 * t))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e0:real` (X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) o
    MATCH_MP HMRR_EPS_POINT) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC o MATCH_MP HMRR_GDIR_UPPER) THEN
  MAP_EVERY EXISTS_TAC [`e0:real`; `&24 * sqrt C`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:real^2->real^K`; `a:real^2`; `r:real`; `t:real`] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_harmonic]) THEN
  SUBGOAL_THEN `(\y. lift(hmr_e (u:real^2->real^K) y)) integrable_on (ball(a,r) DELETE a)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPECL [`ball(a:real^2,r) DELETE a`; `u:real^2->real^K`] o
      check (fun th -> can (find_term (fun t -> t = `Lam:real`)) (concl th) &&
                       is_forall (concl th))) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[OPEN_DELETE; OPEN_BALL]; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^2->real^K`; `a:real^2`; `r:real`] HMRR_EN_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "enf1") (LABEL_TAC "enf2")) THEN
  ABBREV_TAC `E = hmrr_en (u:real^2->real^K) a (&0) (&3 / &2 * t)` THEN
  SUBGOAL_THEN `&0 <= E` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN USE_THEN "enf1" (MP_TAC o SPECL [`&0`; `&3 / &2 * t`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&24 * sqrt C) * sqrt E = &12 * (sqrt(&4 * C * E) / t) * t` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC HMRR_SQRT_ALG THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC HMRR_OSC_ANNULUS THEN EXISTS_TAC `ball(a:real^2,r) DELETE a` THEN
  ASM_SIMP_TAC[OPEN_DELETE; OPEN_BALL] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DELETE; IN_BALL] THEN X_GEN_TAC `x:real^2` THEN
    STRIP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
    UNDISCH_TAC `t / &2 <= norm(x - a:real^2)` THEN
    ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^2`; `i:num`] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt((&4 * C * E) / t pow 2)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `hmr_e (u:real^2->real^K) x` THEN ASM_SIMP_TAC[HMRR_PD_SQ_LE] THEN
    SUBGOAL_THEN `&0 < t pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    MP_TAC(ISPECL [`u:real^2->real^K`; `a:real^2`; `r:real`; `x:real^2`]
      (ASSUME `!(u:real^2->real^K) a r x.
                 cm_harmonic S G (ball(a,r) DELETE a) u /\
                 wan_w12 (ball(a,r) DELETE a) u /\
                 &0 < norm(x - a) /\ &3 / &2 * norm(x - a) <= r /\
                 hmrr_en u a (&0) (&3 / &2 * norm(x - a)) <= e0
                 ==> norm(x - a) pow 2 * hmr_e u x <=
                     C * hmrr_en u a (&0) (&3 / &2 * norm(x - a))`)) THEN
    SUBGOAL_THEN `hmrr_en (u:real^2->real^K) a (&0) (&3 / &2 * norm(x - a)) <= E`
    ASSUME_TAC THENL
     [EXPAND_TAC "E" THEN USE_THEN "enf2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `t pow 2 <= &4 * norm(x - a:real^2) pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `(t / &2) pow 2 <= n ==> t pow 2 <= &4 * n`) THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= hmr_e (u:real^2->real^K) x` ASSUME_TAC THENL
     [REWRITE_TAC[HMR_E_POS]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `hmr_e (u:real^2->real^K) x * (&4 * norm(x - a:real^2) pow 2)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&4 * C * hmrr_en (u:real^2->real^K) a (&0) (&3 / &2 * norm(x - a))` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SQRT_DIV] THEN
    SUBGOAL_THEN `sqrt(t pow 2) = t` SUBST1_TAC THENL
     [MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_LE_REFL]]);;

(* ========================================================================= *)
(* Energy profiles and the decay of the energy at the point.  hmrr_psi is    *)
(* the boundary term of the comparison argument and hmrr_ce the circle       *)
(* energy; on small dyadic annuli                                            *)
(*   c E(t/2, t) <= Psi(t) - Psi(t/2),   |Psi(t)| <= K1 t^2 ce(t),         *)
(* telescoping and Psi -> 0 give c E(0, rho) <= K1 rho^2 ce(rho), and the  *)
(* polar formula turns this into E(0, rho/2) <= theta E(0, rho).            *)
(* ========================================================================= *)

let hmrr_psi = new_definition
 `hmrr_psi (u:real^2->real^K) (a:real^2) t =
    drop(integral (interval[vec 0,lift(&2 * pi)])
           (\th. lift((u(wan_circ a t (drop th)) - hmrr_avg u a t) dot
                      hmrr_rad u a (wan_circ a t (drop th)))))`;;

let hmrr_ce = new_definition
 `hmrr_ce (u:real^2->real^K) (a:real^2) t =
    drop(integral (interval[vec 0,lift(&2 * pi)])
           (\th. lift(hmr_e u (wan_circ a t (drop th)))))`;;

let hmrr_prof = new_definition
 `hmrr_prof (u:real^2->real^K) (a:real^2) (rho:real^1) =
    drop rho % integral (interval[vec 0,lift(&2 * pi)])
                 (\t. lift(hmr_e u (wan_circ a (drop rho) (drop t))))`;;

(* The polar formula for the energy on annuli. *)

let HMRR_EN_POLAR = prove
 (`!(u:real^2->real^K) a r r1 r2.
     (\x. lift(hmr_e u x)) integrable_on (ball(a,r) DELETE a) /\
     &0 <= r1 /\ r1 <= r2 /\ r2 <= r
     ==> hmrr_prof u a integrable_on interval[lift r1,lift r2] /\
         hmrr_en u a r1 r2 = drop(integral (interval[lift r1,lift r2]) (hmrr_prof u a))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^2->real^K`; `a:real^2`; `r:real`] HMRR_EN_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x. lift(hmr_e (u:real^2->real^K) x)) absolutely_integrable_on
                hmrr_ann a r1 r2` ASSUME_TAC THENL
   [MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
    REWRITE_TAC[DIMINDEX_1; ARITH_RULE `1 <= i /\ i <= 1 <=> i = 1`] THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[GSYM drop; LIFT_DROP; HMR_E_POS];
      FIRST_X_ASSUM(MP_TAC o SPECL [`r1:real`; `r2:real`] o
        check (fun th -> is_forall(concl th) &&
                         length(fst(strip_forall(concl th))) = 2)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. lift(hmr_e (u:real^2->real^K) x)`; `a:real^2`; `&0`;
                 `r1:real`; `r2:real`] WAN_POLAR_ANNULUS) THEN
  REWRITE_TAC[REAL_ADD_LID; GSYM hmrr_ann] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `hmrr_prof (u:real^2->real^K) a =
    (\r. drop r % integral (interval[vec 0,lift(&2 * pi)])
                    (\t. lift(hmr_e u (wan_circ a (drop r) (drop t)))))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; hmrr_prof]; ALL_TAC] THEN
  ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; hmrr_en]);;

let HMRR_EN_ADD = prove
 (`!(u:real^2->real^K) a r r1 r2 r3.
     (\x. lift(hmr_e u x)) integrable_on (ball(a,r) DELETE a) /\
     &0 <= r1 /\ r1 <= r2 /\ r2 <= r3 /\ r3 <= r
     ==> hmrr_en u a r1 r3 = hmrr_en u a r1 r2 + hmrr_en u a r2 r3`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^2->real^K`; `a:real^2`; `r:real`; `r1:real`; `r3:real`]
    HMRR_EN_POLAR) THEN
  MP_TAC(ISPECL [`u:real^2->real^K`; `a:real^2`; `r:real`; `r1:real`; `r2:real`]
    HMRR_EN_POLAR) THEN
  MP_TAC(ISPECL [`u:real^2->real^K`; `a:real^2`; `r:real`; `r2:real`; `r3:real`]
    HMRR_EN_POLAR) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC]) THEN
  ASM_REWRITE_TAC[GSYM DROP_ADD] THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_COMBINE THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let HMRR_EN_EMPTY = prove
 (`!(u:real^2->real^K) a t. hmrr_en u a t t = &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hmrr_en] THEN
  SUBGOAL_THEN `hmrr_ann (a:real^2) t t = {}` SUBST1_TAC THENL
   [REWRITE_TAC[hmrr_ann; EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN REAL_ARITH_TAC;
    REWRITE_TAC[INTEGRAL_EMPTY; DROP_VEC]]);;

(* The comparison inequalities for the harmonic map near the point. *)

let HMRR_CIRC_IN = prove
 (`!(a:real^2) r t th. &0 < t /\ t < r ==> wan_circ a t th IN ball(a,r) DELETE a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_DELETE; IN_BALL] THEN
  ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist; WAN_CIRC_NORM] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`a:real^2`; `t:real`; `th:real`] WAN_CIRC_NORM) THEN
  ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN ASM_REAL_ARITH_TAC);;

let HMRR_ANN_IN = prove
 (`!(a:real^2) r r1 r2. &0 < r1 /\ r2 < r
                        ==> {x | r1 <= norm(x - a) /\ norm(x - a) <= r2} SUBSET
                            ball(a,r) DELETE a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DELETE; IN_BALL] THEN
  X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
  REWRITE_TAC[dist] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN UNDISCH_TAC `r1 <= norm(x - a:real^2)` THEN
  ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN ASM_REAL_ARITH_TAC);;

let HMRR_SMALL_ALG = prove
 (`!x s c. &0 <= x /\ &0 <= s /\ &0 < c /\ s <= c / (&2 * (x + &1)) ==> x * s <= c / &2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `x * c / (&2 * (x + &1))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `x * c / (&2 * (x + &1)) = c / &2 - c / (&2 * (x + &1))` SUBST1_TAC THENL
   [SUBGOAL_THEN `~(x + &1 = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> x - y <= x`) THEN
  MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC);;

let HMRR_SAU_SETUP = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> ?c K1. &0 < c /\ &0 <= K1 /\
                !(u:real^2->real^K) a r.
                  &0 < r /\ cm_harmonic S G (ball(a,r) DELETE a) u /\
                  wan_w12 (ball(a,r) DELETE a) u
                  ==> (!t. &0 < t /\ t < r
                           ==> abs(hmrr_psi u a t) <= K1 * t pow 2 * hmrr_ce u a t) /\
                      ?R0. &0 < R0 /\ &2 * R0 <= r /\
                           !t. &0 < t /\ t <= R0
                               ==> c * hmrr_en u a (t / &2) t <=
                                   hmrr_psi u a t - hmrr_psi u a (t / &2)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `K0:real` STRIP_ASSUME_TAC o MATCH_MP HMRR_POH_CIRCLE) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `B0:real` (X_CHOOSE_THEN `B1:real` STRIP_ASSUME_TAC) o
    MATCH_MP HMR_VLAP_BOUNDS) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e0:real` (X_CHOOSE_THEN `C2:real` STRIP_ASSUME_TAC) o
    MATCH_MP HMRR_OSC_HARMONIC) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC o MATCH_MP HMRR_GDIR_UPPER) THEN
  MAP_EVERY EXISTS_TAC [`inv(&1 + K0) / &2`; `(&1 + K0) / &2`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:real^2->real^K`; `a:real^2`; `r:real`] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_harmonic]) THEN
  SUBGOAL_THEN `open(ball(a:real^2,r) DELETE a)` ASSUME_TAC THENL
   [SIMP_TAC[OPEN_DELETE; OPEN_BALL]; ALL_TAC] THEN
  (* Pohozaev on every circle *)
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `u:real^2->real^K`;
                 `a:real^2`; `r:real`] HMRR_SG) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `u:real^2->real^K`;
                 `a:real^2`; `r:real`] HMRR_POHOZAEV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!t. &0 < t /\ t < r
        ==> drop(integral (interval[vec 0,lift(&2 * pi)])
                 (\th. lift(norm(hmrr_rad (u:real^2->real^K) a (wan_circ a t (drop th))) pow 2))) <=
            K0 * drop(integral (interval[vec 0,lift(&2 * pi)])
                 (\th. lift(norm(hmrr_ang u a (wan_circ a t (drop th))) pow 2)))`
  (LABEL_TAC "poh") THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> t = `K0:real`)) (concl th) && is_forall (concl th))) THEN
    EXISTS_TAC `ball(a:real^2,r) DELETE a` THEN ASM_SIMP_TAC[HMRR_CIRC_IN];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* the bound for the boundary term *)
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`u:real^2->real^K`; `ball(a:real^2,r) DELETE a`; `a:real^2`; `t:real`;
                   `K0:real`] HMRR_PSI_BOUND) THEN
    ASM_SIMP_TAC[HMRR_CIRC_IN; GSYM hmrr_psi] THEN
    MATCH_MP_TAC(REAL_ARITH `x = y ==> a <= x ==> a <= y`) THEN
    REWRITE_TAC[hmrr_ce] THEN AP_TERM_TAC THEN
    SUBGOAL_THEN
     `(\th. lift(norm(wan_circ a t (drop th) - a) pow 2 *
                 hmr_e (u:real^2->real^K) (wan_circ a t (drop th)))) =
      (\th. t pow 2 % lift(hmr_e u (wan_circ a t (drop th))))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; WAN_CIRC_NORM; LIFT_CMUL] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM DROP_CMUL] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC INTEGRAL_CMUL THEN
    MP_TAC(ISPECL [`\x. lift(hmr_e (u:real^2->real^K) x)`; `ball(a:real^2,r) DELETE a`;
                   `a:real^2`; `t:real`] HMRR_CIRC_INT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[HMRR_CIRC_IN; SMOOTH_MAP_ON_CONTINUOUS_ON; HMR_E_SMOOTH];
    ALL_TAC] THEN
  (* the small-energy radius *)
  ABBREV_TAC `c0 = inv(&1 + K0)` THEN
  SUBGOAL_THEN `&0 < c0` ASSUME_TAC THENL
   [EXPAND_TAC "c0" THEN REWRITE_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(\y. lift(hmr_e (u:real^2->real^K) y)) integrable_on (ball(a,r) DELETE a)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPECL [`ball(a:real^2,r) DELETE a`; `u:real^2->real^K`] o
      check (fun th -> can (find_term (fun t -> t = `Lam:real`)) (concl th) &&
                       is_forall (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^2->real^K`; `a:real^2`; `r:real`] HMRR_EN_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "enf1") (LABEL_TAC "enf2")) THEN
  ABBREV_TAC `eta = min e0 ((c0 / (&2 * (C2 * B0 + &1))) pow 2)` THEN
  SUBGOAL_THEN `&0 < eta /\ eta <= e0 /\ sqrt eta <= c0 / (&2 * (C2 * B0 + &1))`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < c0 / (&2 * (C2 * B0 + &1))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "eta" THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[]; MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]];
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sqrt((c0 / (&2 * (C2 * B0 + &1))) pow 2)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_MONO_LE THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC POW_2_SQRT THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^2->real^K`; `a:real^2`; `r:real`] HMRR_EN_SMALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `eta:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t0 / &2` THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `hmrr_en (u:real^2->real^K) a (&0) (&3 / &2 * t) <= eta` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `hmrr_en (u:real^2->real^K) a (&0) t0` THEN
    CONJ_TAC THENL [USE_THEN "enf2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `Om = C2 * sqrt(hmrr_en (u:real^2->real^K) a (&0) (&3 / &2 * t))` THEN
  SUBGOAL_THEN `Om * B0 <= c0 / &2` ASSUME_TAC THENL
   [SUBGOAL_THEN `Om * B0 = (C2 * B0) * sqrt(hmrr_en (u:real^2->real^K) a (&0) (&3 / &2 * t))`
    SUBST1_TAC THENL [EXPAND_TAC "Om" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC HMRR_SMALL_ALG THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SQRT_POS_LE THEN USE_THEN "enf1" (MP_TAC o SPECL [`&0`; `&3 / &2 * t`]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt eta` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^2->real^K`; `ball(a:real^2,r) DELETE a`; `a:real^2`; `t:real`;
                 `K0:real`; `B0:real`; `Om:real`] HMRR_SAU_ANNULUS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SIMP_TAC[IN_DELETE];
      MATCH_MP_TAC HMRR_ANN_IN THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN USE_THEN "poh" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`ball(a:real^2,r) DELETE a`; `u:real^2->real^K`;
                                    `x:real^2`] o check (fun th ->
        can (find_term (fun t -> t = `B0:real`)) (concl th) && is_forall (concl th))) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`a:real^2`; `r:real`; `t / &2`; `t:real`] HMRR_ANN_IN) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[SUBSET; IN_ELIM_THM]] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        SIMP_TAC[]];
      EXPAND_TAC "Om" THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^2->real^K`; `a:real^2`; `r:real`; `t:real`] o
        check (fun th ->
        can (find_term (fun t -> t = `C2:real`)) (concl th) && is_forall (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM hmrr_psi] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> y <= z ==> x <= z`) THEN
  SUBGOAL_THEN `&0 <= hmrr_en (u:real^2->real^K) a (t / &2) t` ASSUME_TAC THENL
   [USE_THEN "enf1" (MP_TAC o SPECL [`t / &2`; `t:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Telescoping over dyadic annuli. *)

let HMRR_TELESCOPE = prove
 (`!(u:real^2->real^K) a r c R0 rho.
     (\x. lift(hmr_e u x)) integrable_on (ball(a,r) DELETE a) /\ &0 < R0 /\ R0 <= r /\
     (!t. &0 < t /\ t <= R0
          ==> c * hmrr_en u a (t / &2) t <= hmrr_psi u a t - hmrr_psi u a (t / &2)) /\
     &0 < rho /\ rho <= R0
     ==> !n. c * hmrr_en u a (rho / &2 pow n) rho <=
             hmrr_psi u a rho - hmrr_psi u a (rho / &2 pow n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[real_pow; REAL_DIV_1; HMRR_EN_EMPTY] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `rho / &2 pow SUC n = (rho / &2 pow n) / &2` SUBST1_TAC THENL
   [REWRITE_TAC[real_pow; real_div; REAL_INV_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < rho / &2 pow n /\ rho / &2 pow n <= rho` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POW_LE_1; REAL_OF_NUM_LE; ARITH];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^2->real^K`; `a:real^2`; `r:real`; `(rho / &2 pow n) / &2`;
                 `rho / &2 pow n`; `rho:real`] HMRR_EN_ADD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `rho / &2 pow n` o check (fun th ->
    is_forall(concl th) && can (find_term (fun t -> t = `R0:real`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The circle energy is small when the scaled energy density is small. *)

let HMRR_CE_SMALL = prove
 (`!(u:real^2->real^K) a t e.
     (\th. lift(hmr_e u (wan_circ a t (drop th)))) integrable_on interval[vec 0,lift(&2 * pi)] /\
     (!th. t pow 2 * hmr_e u (wan_circ a t th) <= e)
     ==> t pow 2 * hmrr_ce u a t <= &2 * pi * e`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hmrr_ce; GSYM DROP_CMUL] THEN
  ASM_SIMP_TAC[GSYM INTEGRAL_CMUL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (interval[vec 0,lift(&2 * pi)]) (\th:real^1. lift e))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN
    ASM_SIMP_TAC[INTEGRABLE_CMUL; INTEGRABLE_CONST] THEN
    REWRITE_TAC[DROP_CMUL; LIFT_DROP] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[INTEGRAL_CONST] THEN
    SIMP_TAC[CONTENT_1; DROP_VEC; LIFT_DROP; REAL_LE_MUL; REAL_POS; PI_POS_LE] THEN
    REWRITE_TAC[DROP_CMUL; LIFT_DROP] THEN REAL_ARITH_TAC]);;

(* The decay inequality: c E(0, rho) <= K1 rho^2 ce(rho). *)

let HMRR_DECAY_INEQ = prove
 (`!(u:real^2->real^K) a r c K1 R0.
     smooth_map_on (ball(a,r) DELETE a) u /\
     (\x. lift(hmr_e u x)) integrable_on (ball(a,r) DELETE a) /\
     &0 < R0 /\ R0 < r /\ &0 < c /\ &0 <= K1 /\
     (!t. &0 < t /\ t < r ==> abs(hmrr_psi u a t) <= K1 * t pow 2 * hmrr_ce u a t) /\
     (!t. &0 < t /\ t <= R0
          ==> c * hmrr_en u a (t / &2) t <= hmrr_psi u a t - hmrr_psi u a (t / &2)) /\
     (!e. &0 < e ==> ?del. &0 < del /\
                           !x. &0 < norm(x - a) /\ norm(x - a) < del
                               ==> norm(x - a) pow 2 * hmr_e u x < e)
     ==> !rho. &0 < rho /\ rho <= R0
               ==> c * hmrr_en u a (&0) rho <= K1 * rho pow 2 * hmrr_ce u a rho`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "psi")
   (CONJUNCTS_THEN2 (LABEL_TAC "sau") (LABEL_TAC "sg"))))))))) THEN
  X_GEN_TAC `rho:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^2->real^K`; `a:real^2`; `r:real`] HMRR_EN_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "enf1") (LABEL_TAC "enf2")) THEN
  SUBGOAL_THEN
   `!t. &0 < t /\ t < r
        ==> (\th. lift(hmr_e (u:real^2->real^K) (wan_circ a t (drop th)))) integrable_on
            interval[vec 0,lift(&2 * pi)]`
  (LABEL_TAC "cint") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\x. lift(hmr_e (u:real^2->real^K) x)`; `ball(a:real^2,r) DELETE a`;
                   `a:real^2`; `t:real`] HMRR_CIRC_INT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[HMRR_CIRC_IN; SMOOTH_MAP_ON_CONTINUOUS_ON; HMR_E_SMOOTH; OPEN_DELETE;
                 OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!eta. &0 < eta
          ==> c * hmrr_en (u:real^2->real^K) a (&0) rho <=
              K1 * rho pow 2 * hmrr_ce u a rho + eta`
  ASSUME_TAC THENL
   [X_GEN_TAC `eta:real` THEN DISCH_TAC THEN
    USE_THEN "sg" (MP_TAC o SPEC `eta / (&4 * pi * (K1 + &1))`) THEN ANTS_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[PI_POS] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `del:real` STRIP_ASSUME_TAC)] THEN
    MP_TAC(ISPECL [`u:real^2->real^K`; `a:real^2`; `r:real`] HMRR_EN_SMALL) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `eta / (&2 * c)`) THEN ANTS_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`inv(&2)`; `min del t1 / rho`] REAL_ARCH_POW_INV) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      DISCH_THEN(X_CHOOSE_TAC `n:num`)] THEN
    SUBGOAL_THEN `&0 < rho / &2 pow n /\ rho / &2 pow n < min del t1 /\
                  rho / &2 pow n <= rho` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_DIV; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN CONJ_TAC THENL
       [REWRITE_TAC[real_div; GSYM REAL_POW_INV] THEN
        ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
        UNDISCH_TAC `inv(&2) pow n < min del t1 / rho` THEN
        ASM_SIMP_TAC[REAL_LT_RDIV_EQ];
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POW_LE_1; REAL_OF_NUM_LE; ARITH]];
      ALL_TAC] THEN
    ABBREV_TAC `tn = rho / &2 pow n` THEN STRIP_TAC THEN
    (* the three estimates *)
    SUBGOAL_THEN `c * hmrr_en (u:real^2->real^K) a (&0) tn <= eta / &2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `c * hmrr_en (u:real^2->real^K) a (&0) t1` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        USE_THEN "enf2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_IMP_LE THEN
        SUBGOAL_THEN `eta / &2 = c * eta / (&2 * c)` SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `abs(hmrr_psi (u:real^2->real^K) a tn) <= eta / &2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `K1 * tn pow 2 * hmrr_ce (u:real^2->real^K) a tn` THEN CONJ_TAC THENL
       [USE_THEN "psi" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `K1 * &2 * pi * eta / (&4 * pi * (K1 + &1))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC HMRR_CE_SMALL THEN CONJ_TAC THENL
         [USE_THEN "cint" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
          X_GEN_TAC `th:real` THEN
          SUBGOAL_THEN `norm(wan_circ a tn th - a:real^2) = tn` ASSUME_TAC THENL
           [REWRITE_TAC[WAN_CIRC_NORM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `wan_circ a tn th:real^2` o check (fun th ->
            is_forall(concl th) && can (find_term (fun t -> t = `del:real`)) (concl th))) THEN
          ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
        SUBGOAL_THEN `K1 * &2 * pi * eta / (&4 * pi * (K1 + &1)) =
                      (K1 / (K1 + &1)) * eta / &2` SUBST1_TAC THENL
         [SUBGOAL_THEN `~(pi = &0) /\ ~(K1 + &1 = &0)` MP_TAC THENL
           [MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
          ALL_TAC] THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
         [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 <= K1 ==> &0 < K1 + &1`] THEN
          REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`u:real^2->real^K`; `a:real^2`; `r:real`; `c:real`; `R0:real`; `rho:real`]
      HMRR_TELESCOPE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`u:real^2->real^K`; `a:real^2`; `r:real`; `&0`; `tn:real`; `rho:real`]
      HMRR_EN_ADD) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "psi" (MP_TAC o SPEC `rho:real`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `~(y < x) ==> x <= y`) THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `(c * hmrr_en (u:real^2->real^K) a (&0) rho - K1 * rho pow 2 * hmrr_ce u a rho) / &2`) THEN
  ASM_REAL_ARITH_TAC);;

(* One dyadic step of the decay. *)

let HMRR_CE_POS = prove
 (`!(u:real^2->real^K) a t.
     (\th. lift(hmr_e u (wan_circ a t (drop th)))) integrable_on interval[vec 0,lift(&2 * pi)]
     ==> &0 <= hmrr_ce u a t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hmrr_ce] THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
  ASM_REWRITE_TAC[LIFT_DROP; HMR_E_POS]);;

let HMRR_DECAY_STEP = prove
 (`!(u:real^2->real^K) a r c K1 R0.
     smooth_map_on (ball(a,r) DELETE a) u /\
     (\x. lift(hmr_e u x)) integrable_on (ball(a,r) DELETE a) /\
     &0 < R0 /\ R0 < r /\ &0 < c /\ &0 < K1 /\
     (!rho. &0 < rho /\ rho <= R0
            ==> c * hmrr_en u a (&0) rho <= K1 * rho pow 2 * hmrr_ce u a rho)
     ==> !rho. &0 < rho /\ rho <= R0
               ==> hmrr_en u a (&0) (rho / &2) <=
                   (&2 * K1) / (&2 * K1 + c) * hmrr_en u a (&0) rho`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dec"))))))) THEN
  X_GEN_TAC `rho:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^2->real^K`; `a:real^2`; `r:real`] HMRR_EN_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "enf1") (LABEL_TAC "enf2")) THEN
  SUBGOAL_THEN
   `!t. &0 < t /\ t < r
        ==> (\th. lift(hmr_e (u:real^2->real^K) (wan_circ a t (drop th)))) integrable_on
            interval[vec 0,lift(&2 * pi)]`
  (LABEL_TAC "cint") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\x. lift(hmr_e (u:real^2->real^K) x)`; `ball(a:real^2,r) DELETE a`;
                   `a:real^2`; `t:real`] HMRR_CIRC_INT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[HMRR_CIRC_IN; SMOOTH_MAP_ON_CONTINUOUS_ON; HMR_E_SMOOTH; OPEN_DELETE;
                 OPEN_BALL];
    ALL_TAC] THEN
  ABBREV_TAC `E2 = hmrr_en (u:real^2->real^K) a (&0) (rho / &2)` THEN
  SUBGOAL_THEN `&0 <= E2` ASSUME_TAC THENL
   [EXPAND_TAC "E2" THEN USE_THEN "enf1" (MP_TAC o SPECL [`&0`; `rho / &2`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  (* the annulus energy is at least c E2 / (2 K1) *)
  SUBGOAL_THEN `c * E2 / (&2 * K1) <= hmrr_en (u:real^2->real^K) a (rho / &2) rho`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`u:real^2->real^K`; `a:real^2`; `r:real`; `rho / &2`; `rho:real`]
      HMRR_EN_POLAR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `drop(integral (interval[lift(rho / &2),lift rho])
                  (\s:real^1. lift((c * E2) / (K1 * rho))))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[INTEGRAL_CONST; DROP_CMUL; LIFT_DROP] THEN
      SUBGOAL_THEN `drop(lift(rho / &2)) <= drop(lift rho)` ASSUME_TAC THENL
       [REWRITE_TAC[LIFT_DROP] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[CONTENT_1; LIFT_DROP] THEN
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      SUBGOAL_THEN `~(K1 = &0) /\ ~(rho = &0)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_REWRITE_TAC[INTEGRABLE_CONST] THEN
    X_GEN_TAC `s:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN STRIP_TAC THEN
    REWRITE_TAC[hmrr_prof; DROP_CMUL; GSYM hmrr_ce] THEN
    SUBGOAL_THEN `&0 < drop s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= hmrr_ce (u:real^2->real^K) a (drop s)` ASSUME_TAC THENL
     [MATCH_MP_TAC HMRR_CE_POS THEN USE_THEN "cint" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "dec" (MP_TAC o SPEC `drop s`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `E2 <= hmrr_en (u:real^2->real^K) a (&0) (drop s)` ASSUME_TAC THENL
     [EXPAND_TAC "E2" THEN USE_THEN "enf2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < K1 * rho` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `K1 * drop s pow 2 * hmrr_ce (u:real^2->real^K) a (drop s)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `c * hmrr_en (u:real^2->real^K) a (&0) (drop s)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `K1 * drop s pow 2 * hmrr_ce (u:real^2->real^K) a (drop s) =
                  (drop s * hmrr_ce u a (drop s)) * (K1 * drop s)` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^2->real^K`; `a:real^2`; `r:real`; `&0`; `rho / &2`; `rho:real`]
    HMRR_EN_ADD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `&0 < &2 * K1 + c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `x / y * z = (x * z) / y`] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  SUBGOAL_THEN `c * E2 = (&2 * K1) * (c * E2 / (&2 * K1))` MP_TAC THENL
   [SUBGOAL_THEN `~(K1 = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * K1) * (c * E2 / (&2 * K1)) <=
                (&2 * K1) * hmrr_en (u:real^2->real^K) a (rho / &2) rho` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let HMRR_DECAY_ITER = prove
 (`!(u:real^2->real^K) a R0 th.
     (!rho. &0 < rho /\ rho <= R0
            ==> hmrr_en u a (&0) (rho / &2) <= th * hmrr_en u a (&0) rho) /\
     &0 < R0 /\ &0 <= th
     ==> !n. hmrr_en u a (&0) (R0 / &2 pow n) <= th pow n * hmrr_en u a (&0) R0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[real_pow; REAL_DIV_1; REAL_MUL_LID; REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `R0 / &2 pow SUC n = (R0 / &2 pow n) / &2` SUBST1_TAC THENL
   [REWRITE_TAC[real_pow; real_div; REAL_INV_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `th * hmrr_en (u:real^2->real^K) a (&0) (R0 / &2 pow n)` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POW_LE_1; REAL_OF_NUM_LE; ARITH];
    REWRITE_TAC[real_pow; GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The limit at the point.  Geometric bounds for chains, limits of geometric *)
(* Cauchy sequences, dyadic location of a radius; then the energy decay      *)
(* E(0, R/2^n) <= theta^n E(0, R) and the oscillation bound on dyadic annuli *)
(* give a limit L of u at a.                                                 *)
(* ========================================================================= *)

let HMRR_CHAIN_BOUND = prove
 (`!(f:num->real^K) A q n0.
     &0 <= A /\ &0 <= q /\ q < &1 /\
     (!k. n0 <= k ==> norm(f k - f(SUC k)) <= A * q pow k)
     ==> !n m. n0 <= n /\ n <= m ==> norm(f n - f m) <= A * q pow n / (&1 - q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!n d. n0 <= n
          ==> norm((f:num->real^K) n - f(n + d)) <= A * (q pow n - q pow (n + d)) / (&1 - q)`
  ASSUME_TAC THENL
   [GEN_TAC THEN INDUCT_TAC THENL
     [REWRITE_TAC[ADD_CLAUSES; VECTOR_SUB_REFL; NORM_0; REAL_SUB_REFL] THEN
      REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_LE_REFL];
      ALL_TAC] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n + d:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm((f:num->real^K) n - f(n + d)) + norm(f(n + d) - f(SUC(n + d)))` THEN
    CONJ_TAC THENL [CONV_TAC NORM_ARITH; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `A * (q pow n - q pow (n + d)) / (&1 - q) + A * q pow (n + d)` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LE_ADD2]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC[real_pow] THEN
    SUBGOAL_THEN `~(&1 - q = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `m - n:num`]) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `n + (m - n:num) = m` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  REWRITE_TAC[REAL_LE_INV_EQ] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> x - y <= x`) THEN ASM_SIMP_TAC[REAL_POW_LE];
    ASM_REAL_ARITH_TAC]);;

let HMRR_SEQ_LIMIT = prove
 (`!(f:num->real^K) A q n0.
     &0 <= A /\ &0 <= q /\ q < &1 /\
     (!k. n0 <= k ==> norm(f k - f(SUC k)) <= A * q pow k)
     ==> ?L. !n. n0 <= n ==> norm(f n - L) <= A * q pow n / (&1 - q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:num->real^K`; `A:real`; `q:real`; `n0:num`] HMRR_CHAIN_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?L. ((f:num->real^K) --> L) sequentially` MP_TAC THENL
   [REWRITE_TAC[CONVERGENT_EQ_CAUCHY; cauchy] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`q:real`; `e * (&1 - q) / (A + &1)`] REAL_ARCH_POW_INV) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_TAC `N:num`)] THEN
    EXISTS_TAC `n0 + N:num` THEN REWRITE_TAC[GE] THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `!i j. n0 + N <= i /\ i <= j ==> dist((f:num->real^K) i,f j) < e`
    MP_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[dist] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `A * q pow i / (&1 - q)` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `q pow i <= q pow N` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_POW_MONO_INV THEN
        REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_ARITH_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < &1 - q` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(A + &1) * q pow N / (&1 - q)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_POW_LE] THEN ASM_REAL_ARITH_TAC;
          ASM_SIMP_TAC[REAL_LE_DIV2_EQ]];
        ALL_TAC] THEN
      REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
      ASM_SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ] THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC `(A + &1) * (e * (&1 - q) / (A + &1))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN
        SUBGOAL_THEN `~(A + &1 = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]];
      DISCH_TAC THEN DISJ_CASES_TAC(ARITH_RULE `m <= n \/ n <= m:num`) THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ONCE_REWRITE_TAC[DIST_SYM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `L:real^K` THEN DISCH_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
  EXISTS_TAC `\m. (f:num->real^K) n - f m` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LIM_SUB THEN ASM_REWRITE_TAC[LIM_CONST]; ALL_TAC] THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `n:num` THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let HMRR_DYADIC_LOCATE = prove
 (`!t0 s. &0 < t0 /\ &0 < s /\ s <= t0
          ==> ?n. t0 / &2 pow (SUC n) < s /\ s <= t0 / &2 pow n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?m. t0 / &2 pow m < s` MP_TAC THENL
   [MP_TAC(ISPECL [`inv(&2)`; `s / t0`] REAL_ARCH_POW_INV) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m:num` THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; real_div; GSYM REAL_POW_INV] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(m = 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `t0 / &2 pow 0 < s` THEN REWRITE_TAC[real_pow; REAL_DIV_1] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `m - 1` THEN
  SUBGOAL_THEN `SUC(m - 1) = m` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM REAL_NOT_LT] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let HMRR_SQRT_POW = prove
 (`!x n. &0 <= x ==> sqrt(x pow n) = sqrt x pow n`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SQRT_UNIQUE THEN
  ASM_SIMP_TAC[REAL_POW_LE; SQRT_POS_LE; REAL_POW_POW] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[GSYM REAL_POW_POW] THEN
  ASM_SIMP_TAC[SQRT_POW_2]);;

let HMRR_DYADIC_FACTS = prove
 (`!R n. &0 < R
         ==> &0 < R / &2 pow n /\ R / &2 pow n <= R /\
             R / &2 pow (SUC n) = (R / &2 pow n) / &2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POW_LE_1; REAL_OF_NUM_LE; ARITH];
    REWRITE_TAC[real_pow; real_div; REAL_INV_MUL] THEN REAL_ARITH_TAC]);;

let HMRR_DYADIC_MONO = prove
 (`!R m n. &0 < R /\ m <= n ==> R / &2 pow n <= R / &2 pow m`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  ASM_SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
  MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* The limit of the harmonic map at the point. *)

let HMRR_LIMIT = prove
 (`!S (G:real^K->real^K^K) d (u:real^2->real^K) a r.
     cm_target S G d /\ &0 < r /\ cm_harmonic S G (ball(a,r) DELETE a) u /\
     wan_w12 (ball(a,r) DELETE a) u
     ==> ?L. !e. &0 < e
                 ==> ?del. &0 < del /\
                           !x. &0 < norm(x - a) /\ norm(x - a) < del
                               ==> norm(u x - L) < e`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `K1:real` STRIP_ASSUME_TAC) o
    MATCH_MP HMRR_SAU_SETUP) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^2->real^K`; `a:real^2`; `r:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "psi")
    (X_CHOOSE_THEN `R0:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sau"))))) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e0:real` (X_CHOOSE_THEN `C2:real` STRIP_ASSUME_TAC) o
    MATCH_MP HMRR_OSC_HARMONIC) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC o MATCH_MP HMRR_GDIR_UPPER) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_harmonic]) THEN
  SUBGOAL_THEN `(\y. lift(hmr_e (u:real^2->real^K) y)) integrable_on (ball(a,r) DELETE a)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPECL [`ball(a:real^2,r) DELETE a`; `u:real^2->real^K`] o
      check (fun th -> can (find_term (fun t -> t = `Lam:real`)) (concl th) &&
                       is_forall (concl th))) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[OPEN_DELETE; OPEN_BALL]; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^2->real^K`; `a:real^2`; `r:real`] HMRR_EN_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "enf1") (LABEL_TAC "enf2")) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `u:real^2->real^K`;
                 `a:real^2`; `r:real`] HMRR_SG) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "sg") THEN
  (* the decay of the energy *)
  MP_TAC(ISPECL [`u:real^2->real^K`; `a:real^2`; `r:real`; `c:real`; `K1:real`; `R0:real`]
    HMRR_DECAY_INEQ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN
   `!rho. &0 < rho /\ rho <= R0
          ==> hmrr_en (u:real^2->real^K) a (&0) (rho / &2) <=
              (&2 * (K1 + &1)) / (&2 * (K1 + &1) + c) * hmrr_en u a (&0) rho`
  (LABEL_TAC "step") THENL
   [MATCH_MP_TAC HMRR_DECAY_STEP THEN EXISTS_TAC `r:real` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `rho:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `rho:real` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `K1:real`)) (concl th) &&
      can (find_term (fun t -> t = `c:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC HMRR_CE_POS THEN
    SUBGOAL_THEN `rho < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`\x. lift(hmr_e (u:real^2->real^K) x)`; `ball(a:real^2,r) DELETE a`;
                   `a:real^2`; `rho:real`] HMRR_CIRC_INT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[HMRR_CIRC_IN; SMOOTH_MAP_ON_CONTINUOUS_ON; HMR_E_SMOOTH; OPEN_DELETE;
                 OPEN_BALL];
    ALL_TAC] THEN
  ABBREV_TAC `th = (&2 * (K1 + &1)) / (&2 * (K1 + &1) + c)` THEN
  SUBGOAL_THEN `&0 < th /\ th < &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "th" THEN
    SUBGOAL_THEN `&0 < &2 * (K1 + &1) + c /\ &0 < &2 * (K1 + &1)` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      MP_TAC(ISPECL [`&2 * (K1 + &1)`; `&1`; `&2 * (K1 + &1) + c`] REAL_LT_LDIV_EQ) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
      UNDISCH_TAC `&0 < c` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the smaller radius with energy below the threshold of the oscillation lemma *)
  MP_TAC(ISPECL [`u:real^2->real^K`; `a:real^2`; `r:real`] HMRR_EN_SMALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e0:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `R1 = min R0 (t1 / &2)` THEN
  SUBGOAL_THEN `&0 < R1 /\ R1 <= R0 /\ &2 * R1 <= t1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "R1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^2->real^K`; `a:real^2`; `R1:real`; `th:real`] HMRR_DECAY_ITER) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REPEAT STRIP_TAC THEN USE_THEN "step" MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    DISCH_THEN(LABEL_TAC "iter")] THEN
  ABBREV_TAC `E1 = hmrr_en (u:real^2->real^K) a (&0) R1` THEN
  SUBGOAL_THEN `&0 <= E1` ASSUME_TAC THENL
   [EXPAND_TAC "E1" THEN USE_THEN "enf1" (MP_TAC o SPECL [`&0`; `R1:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `q = sqrt th` THEN
  SUBGOAL_THEN `&0 < q /\ q < &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `sqrt th < sqrt(&1)` MP_TAC THENL
       [MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[SQRT_1]]];
    ALL_TAC] THEN
  ABBREV_TAC `A = C2 * sqrt E1` THEN
  SUBGOAL_THEN `&0 <= A` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE];
    ALL_TAC] THEN
  (* oscillation on the dyadic annuli *)
  SUBGOAL_THEN
   `!k y z. R1 / &2 pow (SUC k) / &2 <= norm(y - a) /\ norm(y - a) <= R1 / &2 pow (SUC k) /\
            R1 / &2 pow (SUC k) / &2 <= norm(z - a) /\ norm(z - a) <= R1 / &2 pow (SUC k)
            ==> norm((u:real^2->real^K) y - u z) <= A * q pow k`
  (LABEL_TAC "osc") THENL
   [X_GEN_TAC `k:num` THEN
    MP_TAC(ISPECL [`R1:real`; `SUC k`] HMRR_DYADIC_FACTS) THEN
    MP_TAC(ISPECL [`R1:real`; `k:num`] HMRR_DYADIC_FACTS) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `C2 * sqrt(hmrr_en (u:real^2->real^K) a (&0) (&3 / &2 * R1 / &2 pow SUC k))` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^2->real^K`; `a:real^2`; `r:real`;
                                    `R1 / &2 pow SUC k`] o check (fun th ->
        is_forall(concl th) && can (find_term (fun t -> t = `C2:real`)) (concl th))) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `hmrr_en (u:real^2->real^K) a (&0) t1` THEN
        CONJ_TAC THENL [USE_THEN "enf2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
                        ASM_REAL_ARITH_TAC];
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    EXPAND_TAC "A" THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt(th pow k * E1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LE THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `hmrr_en (u:real^2->real^K) a (&0) (R1 / &2 pow k)` THEN CONJ_TAC THENL
       [USE_THEN "enf2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        USE_THEN "iter" (fun th -> REWRITE_TAC[th])];
      REWRITE_TAC[SQRT_MUL] THEN EXPAND_TAC "q" THEN
      ASM_SIMP_TAC[HMRR_SQRT_POW; REAL_LT_IMP_LE] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  (* the sequence of values on the dyadic circles *)
  MP_TAC(ISPECL [`\k. (u:real^2->real^K)(a + (R1 / &2 pow (SUC k)) % basis 1)`;
                 `A:real`; `q:real`; `0`] HMRR_SEQ_LIMIT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "osc" MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`R1:real`; `SUC k`] HMRR_DYADIC_FACTS) THEN
    MP_TAC(ISPECL [`R1:real`; `SUC(SUC k)`] HMRR_DYADIC_FACTS) THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `(a + x) - a:real^N = x`; NORM_MUL] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_2; ARITH; REAL_MUL_RID] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
    ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `L:real^K` (LABEL_TAC "lim"))] THEN
  EXISTS_TAC `L:real^K` THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`q:real`; `e / (A * (&1 + inv(&1 - q)) + &1)`] REAL_ARCH_POW_INV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
    REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_TAC `N:num`)] THEN
  EXISTS_TAC `R1 / &2 pow (SUC N)` THEN
  MP_TAC(ISPECL [`R1:real`; `SUC N`] HMRR_DYADIC_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`R1:real`; `norm(x - a:real^2)`] HMRR_DYADIC_LOCATE) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `?m. n = SUC m /\ N <= m` STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `n <= N:num` THENL
     [MP_TAC(ISPECL [`R1:real`; `SUC n`; `SUC N`] HMRR_DYADIC_MONO) THEN
      ASM_REWRITE_TAC[LE_SUC] THEN ASM_REAL_ARITH_TAC;
      EXISTS_TAC `n - 1` THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `n = SUC m` THEN DISCH_THEN SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`R1:real`; `SUC m`] HMRR_DYADIC_FACTS) THEN
  MP_TAC(ISPECL [`R1:real`; `SUC(SUC m)`] HMRR_DYADIC_FACTS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  USE_THEN "osc" (MP_TAC o SPECL [`m:num`; `x:real^2`;
                                  `a + (R1 / &2 pow SUC m) % basis 1:real^2`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[VECTOR_ARITH `(a + x) - a:real^N = x`; NORM_MUL] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_2; ARITH; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  USE_THEN "lim" (MP_TAC o SPEC `m:num`) THEN REWRITE_TAC[LE_0] THEN DISCH_TAC THEN
  SUBGOAL_THEN `q pow m <= q pow N` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_MONO_INV THEN
    REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 - q /\ &0 <= &1 + inv(&1 - q)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
    REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `(A * (&1 + inv(&1 - q))) * q pow m` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `A * q pow m + A * q pow m / (&1 - q)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(NORM_ARITH
       `norm(x - (u:real^2->real^K)(a + (R1 / &2 pow SUC m) % basis 1)) <= b1 /\
        norm(u(a + (R1 / &2 pow SUC m) % basis 1) - l) <= b2
        ==> norm(x - l) <= b1 + b2`) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[real_div] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `(A * (&1 + inv(&1 - q)) + &1) * q pow N` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE] THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < A * (&1 + inv(&1 - q)) + &1` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `q pow N < e / (A * (&1 + inv(&1 - q)) + &1)` THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Transfer lemmas (Sobolev and harmonic notions depend only on the values   *)
(* on the set) and the first variation density with zero displacement.       *)
(* ========================================================================= *)

let HMRR_LSPACE_EQ_ON = prove
 (`!(s:real^N->bool) p (f:real^N->real^K) g.
     f IN lspace s p /\ (!x. x IN s ==> g x = f x) ==> g IN lspace s p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lspace; IN_ELIM_THM] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_ON_EQ THEN EXISTS_TAC `f:real^N->real^K` THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC INTEGRABLE_EQ THEN
    EXISTS_TAC `\x. lift(norm((f:real^N->real^K) x) rpow p)` THEN ASM_SIMP_TAC[]]);;

let HMRR_W12_EQ_ON = prove
 (`!(s:real^N->bool) (u:real^N->real^K) w.
     wan_w12 s u /\ (!x. x IN s ==> w x = u x) ==> wan_w12 s w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_w12] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC HMRR_LSPACE_EQ_ON THEN EXISTS_TAC `u:real^N->real^K` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real^N->real^K` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC WAN_WPD_EQ_ON THEN
    EXISTS_TAC `u:real^N->real^K` THEN ASM_REWRITE_TAC[]]);;

let HMRR_WD_EQ_ON = prove
 (`!(s:real^N->bool) i (u:real^N->real^K) w.
     (!x. x IN s ==> w x = u x) ==> wan_wd s i w = wan_wd s i u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_wd] THEN AP_TERM_TAC THEN ABS_TAC THEN
  AP_TERM_TAC THEN EQ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC WAN_WPD_EQ_ON THENL
   [EXISTS_TAC `w:real^N->real^K`; EXISTS_TAC `u:real^N->real^K`] THEN
  ASM_SIMP_TAC[]);;

let HMRR_GDIR_EQ_ON = prove
 (`!(s:real^N->bool) (G:real^K->real^K^K) (u:real^N->real^K) w.
     (!x. x IN s ==> w x = u x) ==> wan_gdir s G w = wan_gdir s G u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_gdir] THEN
  ASM_SIMP_TAC[HMRR_WD_EQ_ON] THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num` THEN
  DISCH_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN
  ASM_SIMP_TAC[]);;

let HMRR_HARMONIC_EQ_ON = prove
 (`!S (G:real^K->real^K^K) s (u:real^2->real^K) w.
     open s /\ cm_harmonic S G s u /\ (!x. x IN s ==> w x = u x)
     ==> cm_harmonic S G s w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cm_harmonic] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN EXISTS_TAC `u:real^2->real^K` THEN
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`phi:real^2->real^K`; `s':real^2->bool`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`phi:real^2->real^K`; `s':real^2->bool`] o
      check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `e:real` THEN
    REWRITE_TAC[cm_gen] THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC HMRR_GDIR_EQ_ON THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x:real^2) IN s` (fun th -> ASM_SIMP_TAC[th]) THEN
    MP_TAC(ISPEC `s':real^2->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[]]);;

(* The first variation density with zero displacement. *)

let HMRR_ELD_LEFT0 = prove
 (`!S (G:real^K->real^K^K) d p q k.
     cm_target S G d /\ p IN S
     ==> hmrm_eld S G p q (vec 0) k =
         k dot (&2 % (jacobian (closest_point S) (at p) ** (G p ** q)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  SUBGOAL_THEN `(p:real^K) IN cm_tube S d` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!Ff:real^K->real^(K,K)finite_prod.
                  Ff differentiable at p ==> frechet_derivative Ff (at p) (vec 0) = vec 0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPEC `frechet_derivative (Ff:real^K->real^(K,K)finite_prod) (at p)` LINEAR_0) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mderiv (\y. jacobian (closest_point S) (at y)) (p:real^K) (vec 0) = mat 0`
  ASSUME_TAC THENL
   [REWRITE_TAC[mderiv] THEN
    SUBGOAL_THEN
     `frechet_derivative ((vectorize:real^K^K->real^(K,K)finite_prod) o
                          (\y. jacobian (closest_point S) (at y))) (at (p:real^K)) (vec 0) =
      vec 0`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `cm_tube (S:real^K->bool) d` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[MATRIFY_0]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mderiv (G:real^K->real^K^K) p (vec 0) = mat 0` ASSUME_TAC THENL
   [REWRITE_TAC[mderiv] THEN
    SUBGOAL_THEN
     `frechet_derivative ((vectorize:real^K^K->real^(K,K)finite_prod) o (G:real^K->real^K^K))
                         (at (p:real^K)) (vec 0) = vec 0`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `(:real^K)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      REWRITE_TAC[MATRIFY_0]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[hmrm_eld; MATRIX_VECTOR_MUL_LZERO; MATRIX_VECTOR_MUL_RZERO;
                  VECTOR_ADD_LID; DOT_RZERO; REAL_ADD_RID] THEN
  REWRITE_TAC[DOT_RMUL] THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN
  SUBGOAL_THEN `transp(jacobian (closest_point S) (at (p:real^K))) =
                jacobian (closest_point S) (at p)`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM DOT_MATRIX_TRANSP_LMUL] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[DOT_SYM]);;

(* ========================================================================= *)
(* The Euler-Lagrange identity extends across the point.  For the tests      *)
(* (1 - eta_n) phi (point cutoffs at radius e_n -> 0) the identity holds     *)
(* (HMRR_EL_PHIE); the terms with (1 - eta_n) phi and (1 - eta_n) D_i phi    *)
(* converge to the terms for phi (HMRC_ELD_LIMIT), and the terms with        *)
(* D_i eta_n phi tend to 0 (WAN_BAD_TERM_ABS: a point has 2D capacity 0).    *)
(* ========================================================================= *)

let HMRR_CONT_LSPACE2 = prove
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

let HMRR_VTEST_BOUNDS = prove
 (`!(s:real^2->bool) (phi:real^2->real^K).
     wan_vtest s phi
     ==> phi continuous_on (:real^2) /\
         (!i. partial_derivative i phi continuous_on (:real^2)) /\
         ?M. &0 <= M /\ !x. norm(phi x) <= M`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_vtest] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:real^2->bool` STRIP_ASSUME_TAC)) THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; OPEN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `bounded(IMAGE (phi:real^2->real^K) k)` MP_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SUBSET_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `B:real` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `x:real^2` THEN ASM_CASES_TAC `(x:real^2) IN k` THEN ASM_SIMP_TAC[] THEN
  ASM_SIMP_TAC[NORM_0] THEN ASM_REAL_ARITH_TAC);;

(* The bad term: the derivative of the cutoff against phi. *)

let HMRR_BAD_LIMIT = prove
 (`!S (G:real^K->real^K^K) d (w:real^2->real^K) a s' (phi:real^2->real^K) r0 d0 i.
     cm_target S G d /\ open s' /\ w continuous_on s' /\ (!x. x IN s' ==> w x IN S) /\
     wan_w12 s' w /\ wan_vtest s' phi /\ &0 < r0 /\ cball(a,r0) SUBSET s' /\
     &0 < d0 /\ &2 * d0 <= r0 /\ d0 <= &1 /\ 1 <= i /\ i <= 2
     ==> ((\n. drop(integral s'
              (\x. lift(hmrm_eld S G (w x) (wan_wd s' i w x) (vec 0)
                         (wan_dpart i (\y. smooth_bump (d0 * inv(&n + &1))
                                             (&2 * (d0 * inv(&n + &1))) (y - a)) x %
                          phi x)))))
          ---> &0) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s':real^2->bool`; `phi:real^2->real^K`] HMRR_VTEST_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Ca:real` (X_CHOOSE_THEN `Cb:real` STRIP_ASSUME_TAC) o
    MATCH_MP HMRC_ELD_BOUND) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  X_CHOOSE_THEN `CL:real` STRIP_ASSUME_TAC (INST_TYPE [`:2`,`:N`] WAN_POINT_CUTOFF_L2) THEN
  X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC (INST_TYPE [`:2`,`:N`] WAN_POINT_CUTOFF_DPART) THEN
  ABBREV_TAC
   `A = \x. &2 % (jacobian (closest_point S) (at ((w:real^2->real^K) x)) **
                 ((G:real^K->real^K^K)(w x) ** wan_wd s' i w x))` THEN
  SUBGOAL_THEN
   `!x. x IN s'
        ==> !v. hmrm_eld S G ((w:real^2->real^K) x) (wan_wd s' i w x) (vec 0) v =
                v dot (A:real^2->real^K) x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "A" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC HMRR_ELD_LEFT0 THEN EXISTS_TAC `d:real` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the vector A is square integrable near the point *)
  SUBGOAL_THEN `(A:real^2->real^K) IN lspace (cball(a,r0)) (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC(INST_TYPE [`:K`,`:P`] LSPACE_BOUNDED_MEASURABLE) THEN
    EXISTS_TAC `\x. Cb % wan_wd s' i (w:real^2->real^K) x` THEN
    REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      ALL_TAC;
      MATCH_MP_TAC LSPACE_CMUL THEN MATCH_MP_TAC LSPACE_SUBSET THEN
      EXISTS_TAC `s':real^2->bool` THEN ASM_SIMP_TAC[LEBESGUE_MEASURABLE_CBALL] THEN
      MP_TAC(ISPECL [`s':real^2->bool`; `i:num`; `w:real^2->real^K`] WAN_WD_WORKS) THEN
      ASM_SIMP_TAC[DIMINDEX_2; ETA_AX];
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(x:real^2) IN s'` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[NORM_MUL] THEN
      SUBGOAL_THEN `norm((A:real^2->real^K) x) pow 2 <=
                    Cb * norm(wan_wd s' i (w:real^2->real^K) x) * norm(A x)` ASSUME_TAC THENL
       [REWRITE_TAC[NORM_POW_2] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `(A:real^2->real^K) x` o C MATCH_MP
          (ASSUME `(x:real^2) IN s'`) o check (fun th -> is_forall(concl th) &&
             can (find_term (fun t -> t = `A:real^2->real^K`)) (concl th))) THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        MATCH_MP_TAC(REAL_ARITH `abs x <= y ==> x <= y`) THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `Ca * norm(vec 0:real^K) * norm(wan_wd s' i (w:real^2->real^K) x) pow 2 +
                    Cb * norm(wan_wd s' i w x) * norm((A:real^2->real^K) x)` THEN
        CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[NORM_0; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_LID; REAL_LE_REFL];
        ALL_TAC] THEN
      ASM_CASES_TAC `(A:real^2->real^K) x = vec 0` THENL
       [ASM_REWRITE_TAC[NORM_0] THEN MATCH_MP_TAC REAL_LE_MUL THEN
        REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE];
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < norm((A:real^2->real^K) x)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC `norm((A:real^2->real^K) x)` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `Cb * norm(wan_wd s' i (w:real^2->real^K) x) * norm((A:real^2->real^K) x)` THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[GSYM REAL_POW_2]; ALL_TAC] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      REWRITE_TAC[NORM_POS_LE] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      REWRITE_TAC[NORM_POS_LE] THEN REAL_ARITH_TAC] THEN
    (* measurability of A *)
    SUBGOAL_THEN
     `((vectorize:real^K^K->real^(K,K)finite_prod) o
       (\x. jacobian (closest_point S) (at ((w:real^2->real^K) x)))) continuous_on s' /\
      ((vectorize:real^K^K->real^(K,K)finite_prod) o
       (\x. (G:real^K->real^K^K)((w:real^2->real^K) x))) continuous_on s'`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [SUBGOAL_THEN
         `((vectorize:real^K^K->real^(K,K)finite_prod) o
           (\x. jacobian (closest_point (S:real^K->bool)) (at ((w:real^2->real^K) x)))) =
          ((vectorize:real^K^K->real^(K,K)finite_prod) o
           (\y. jacobian (closest_point S) (at y))) o w`
        SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cm_tube (S:real^K->bool) d` THEN
        ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM SET_TAC[];
        SUBGOAL_THEN
         `((vectorize:real^K^K->real^(K,K)finite_prod) o
           (\x. (G:real^K->real^K^K)((w:real^2->real^K) x))) =
          ((vectorize:real^K^K->real^(K,K)finite_prod) o G) o w`
        SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^K)` THEN
        ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SUBSET_UNIV]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(A:real^2->real^K) =
      (\x. &2 % ((matrify(((vectorize:real^K^K->real^(K,K)finite_prod) o
                    (\x. jacobian (closest_point S) (at ((w:real^2->real^K) x)))) x)
                  :real^K^K) **
                 ((matrify(((vectorize:real^K^K->real^(K,K)finite_prod) o
                    (\x. (G:real^K->real^K^K)(w x))) x):real^K^K) ** wan_wd s' i w x)))`
    SUBST1_TAC THENL
     [EXPAND_TAC "A" THEN REWRITE_TAC[FUN_EQ_THM; o_THM; MATRIFY_VECTORIZE]; ALL_TAC] THEN
    MATCH_MP_TAC MEASURABLE_ON_CMUL THEN
    SUBGOAL_THEN `!f:real^2->real^(K,K)finite_prod. f continuous_on s'
                    ==> f measurable_on cball(a:real^2,r0)` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      REWRITE_TAC[LEBESGUE_MEASURABLE_CBALL] THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      ALL_TAC] THEN
    MATCH_MP_TAC HMC_MEAS_MATMUL THEN ASM_SIMP_TAC[ETA_AX] THEN
    MATCH_MP_TAC HMC_MEAS_MATMUL THEN ASM_SIMP_TAC[ETA_AX] THEN
    MATCH_MP_TAC MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `s':real^2->bool` THEN ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_CBALL] THEN
    MP_TAC(ISPECL [`s':real^2->bool`; `i:num`; `w:real^2->real^K`] WAN_WD_WORKS) THEN
    ASM_SIMP_TAC[DIMINDEX_2; lspace; IN_ELIM_THM; ETA_AX];
    ALL_TAC] THEN
  (* the bad term lemma *)
  MP_TAC(ISPECL [`s':real^2->bool`; `A:real^2->real^K`; `phi:real^2->real^K`;
                 `\n x. wan_dpart i (\y. smooth_bump (d0 * inv(&n + &1))
                                           (&2 * (d0 * inv(&n + &1))) (y - a)) x`;
                 `a:real^2`; `r0:real`; `\n. &2 * (d0 * inv(&n + &1))`; `CL:real`; `M:real`]
    WAN_BAD_TERM_ABS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^2`; `d0 * inv(&n + &1)`; `i:num`] o
        check (fun th -> can (find_term (fun t -> t = `B:real`)) (concl th) &&
                         is_forall (concl th))) THEN
      ASM_SIMP_TAC[WAN_EN_FACTS];
      GEN_TAC THEN EXISTS_TAC `B / (d0 * inv(&n + &1))` THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^2`; `d0 * inv(&n + &1)`; `i:num`] o
        check (fun th -> can (find_term (fun t -> t = `B:real`)) (concl th) &&
                         is_forall (concl th))) THEN
      ASM_SIMP_TAC[WAN_EN_FACTS];
      REPEAT GEN_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^2`; `d0 * inv(&n + &1)`; `i:num`] o
        check (fun th -> can (find_term (fun t -> t = `B:real`)) (concl th) &&
                         is_forall (concl th))) THEN
      ASM_SIMP_TAC[WAN_EN_FACTS];
      GEN_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^2`; `d0 * inv(&n + &1)`; `i:num`] o
        check (fun th -> can (find_term (fun t -> t = `CL:real`)) (concl th) &&
                         is_forall (concl th))) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      MP_TAC(ISPECL [`d0:real`; `n:num`] WAN_EN_FACTS) THEN
      ASM_REWRITE_TAC[DIMINDEX_2; LE_REFL] THEN ASM_REAL_ARITH_TAC;
      GEN_TAC THEN MP_TAC(ISPECL [`d0:real`; `n:num`] WAN_EN_FACTS) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_CUTOFF_SEQ THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[TENDSTO_REAL; o_DEF; LIFT_DROP; LIFT_NUM] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN
  MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN
  FIRST_X_ASSUM((fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(x:real^2) IN s'`)]) o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `A:real^2->real^K`)) (concl th))) THEN
  REWRITE_TAC[DOT_LMUL] THEN AP_TERM_TAC THEN REWRITE_TAC[DOT_SYM]);;

(* Square integrals of bounded maps supported in small balls. *)

let HMRR_SMALL_SUPPORT_L2 = prove
 (`!(s:real^2->bool) (g:real^2->real^K) a e M.
     measurable s /\ (\x. lift(norm(g x) pow 2)) integrable_on s /\ &0 <= e /\
     (!x. x IN s ==> norm(g x) <= M) /\
     (!x. x IN s /\ ~(x IN cball(a,e)) ==> g x = vec 0)
     ==> drop(integral s (\x. lift(norm(g x) pow 2))) <= M pow 2 * (&2 * e) pow 2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral s (\x. if x IN cball(a:real^2,e) then lift(M pow 2) else vec 0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[INTEGRABLE_RESTRICT_INTER; INTEGRABLE_ON_CONST] THEN DISJ2_TAC THEN
      ASM_SIMP_TAC[MEASURABLE_INTER; MEASURABLE_CBALL];
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
      COND_CASES_TAC THEN REWRITE_TAC[LIFT_DROP; DROP_VEC] THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[NORM_POS_LE];
        ASM_SIMP_TAC[NORM_0] THEN REAL_ARITH_TAC]];
    REWRITE_TAC[INTEGRAL_RESTRICT_INTER] THEN
    ASM_SIMP_TAC[INTEGRAL_CONST_GEN; MEASURABLE_INTER; MEASURABLE_CBALL; DROP_CMUL;
                 LIFT_DROP] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `measure(cball(a:real^2,e))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MEASURE_SUBSET THEN
      ASM_SIMP_TAC[MEASURABLE_INTER; MEASURABLE_CBALL; INTER_SUBSET];
      MP_TAC(ISPECL [`a:real^2`; `e:real`] MEASURE_CBALL_BOUND) THEN
      ASM_REWRITE_TAC[DIMINDEX_2]]]);;

let HMRR_INV_SEQ_NULL = prove
 (`!c. ((\n. c * inv(&n + &1)) ---> &0) sequentially`,
  GEN_TAC THEN MATCH_MP_TAC REALLIM_NULL_LMUL THEN REWRITE_TAC[REALLIM_1_OVER_N_OFFSET]);;

let HMRR_VTEST_PD = prove
 (`!(s:real^N->bool) (phi:real^N->real^K) i.
     wan_vtest s phi ==> wan_vtest s (partial_derivative i phi)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_vtest]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[wan_vtest] THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; OPEN_UNIV] THEN
  EXISTS_TAC `k:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `phi:real^N->real^K`; `k:real^N->bool`; `i:num`]
    WAN_VTEST_PARTIAL) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let HMRR_CUT_FACTS = prove
 (`!(a:real^N) e.
     &0 < e
     ==> (\x. lift(&1 - smooth_bump e (&2 * e) (x - a))) continuous_on (:real^N) /\
         (!x. &0 <= &1 - smooth_bump e (&2 * e) (x - a) /\
              &1 - smooth_bump e (&2 * e) (x - a) <= &1) /\
         (!x. &2 * e <= norm(x - a) ==> &1 - smooth_bump e (&2 * e) (x - a) = &1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `e:real`] WAN_POINT_CUTOFF_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^N` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o check (is_conj o snd o dest_forall o concl)) THEN
    REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN REAL_ARITH_TAC]);;

(* The truncation error of a bounded continuous map tends to 0 in L2. *)

let HMRR_CUT_L2_NULL = prove
 (`!(s:real^2->bool) (g:real^2->real^K) a d0 M1.
     open s /\ bounded s /\ g continuous_on (:real^2) /\ &0 < d0 /\
     (!x. norm(g x) <= M1)
     ==> ((\n. lnorm s (&2)
                 (\x. (&1 - smooth_bump (d0 * inv(&n + &1)) (&2 * (d0 * inv(&n + &1))) (x - a)) %
                      g x - g x)) ---> &0) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `measurable(s:real^2->bool) /\ compact(closure s:real^2->bool) /\
                s SUBSET closure s /\ lebesgue_measurable(s:real^2->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MEASURABLE_OPEN; COMPACT_CLOSURE; CLOSURE_SUBSET; LEBESGUE_MEASURABLE_OPEN];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (\x. (&1 - smooth_bump (d0 * inv(&n + &1)) (&2 * (d0 * inv(&n + &1))) (x - a)) %
             (g:real^2->real^K) x - g x) IN lspace s (&2)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC HMRR_CONT_LSPACE2 THEN EXISTS_TAC `closure s:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    ASM_REWRITE_TAC[o_DEF] THEN
    MP_TAC(ISPECL [`a:real^2`; `d0 * inv(&n + &1)`] HMRR_CUT_FACTS) THEN
    ASM_SIMP_TAC[WAN_EN_FACTS];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\n x. (&1 - smooth_bump (d0 * inv(&n + &1)) (&2 * (d0 * inv(&n + &1))) (x - a)) %
           (g:real^2->real^K) x - g x`; `s:real^2->bool`] WAN_LNORM2_NULL) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. M1 pow 2 * (&2 * (&2 * (d0 * inv(&n + &1)))) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`d0:real`; `n:num`] WAN_EN_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`a:real^2`; `d0 * inv(&n + &1)`] HMRR_CUT_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `&0 <= drop(integral s
        (\x. lift(norm((&1 - smooth_bump (d0 * inv(&n + &1)) (&2 * (d0 * inv(&n + &1))) (x - a)) %
                        (g:real^2->real^K) x - g x) pow 2)))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC INTEGRAL_DROP_POS THEN
      ASM_SIMP_TAC[WAN_LSPACE2_SQNORM_INTEGRABLE; LIFT_DROP; REAL_LE_POW_2];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
    MATCH_MP_TAC HMRR_SMALL_SUPPORT_L2 THEN EXISTS_TAC `a:real^2` THEN
    ASM_SIMP_TAC[WAN_LSPACE2_SQNORM_INTEGRABLE] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THEN X_GEN_TAC `x:real^2` THEN STRIP_TAC THENL
     [REWRITE_TAC[VECTOR_ARITH `c % g - g:real^N = (c - &1) % g`; NORM_MUL] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * norm((g:real^2->real^K) x)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2` o check (is_conj o snd o dest_forall o concl)) THEN
        REAL_ARITH_TAC;
        ASM_REWRITE_TAC[REAL_MUL_LID]];
      SUBGOAL_THEN `&2 * (d0 * inv(&n + &1)) <= norm(x - a:real^2)` ASSUME_TAC THENL
       [UNDISCH_TAC `~((x:real^2) IN cball(a,&2 * (d0 * inv(&n + &1))))` THEN
        REWRITE_TAC[IN_CBALL] THEN CONV_TAC NORM_ARITH;
        ASM_SIMP_TAC[] THEN VECTOR_ARITH_TAC]];
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_NULL_LMUL THEN MATCH_MP_TAC REALLIM_NULL_POW THEN
  REWRITE_TAC[ARITH_EQ] THEN
  SUBGOAL_THEN `(\n. &2 * (&2 * (d0 * inv(&n + &1)))) = (\n. (&4 * d0) * inv(&n + &1))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; REWRITE_TAC[HMRR_INV_SEQ_NULL]]);;

(* The main terms converge. *)

let HMRR_T1_LIMIT = prove
 (`!S (G:real^K->real^K^K) d (w:real^2->real^K) a s' (phi:real^2->real^K) d0 i.
     cm_target S G d /\ open s' /\ bounded s' /\ w continuous_on s' /\
     (!x. x IN s' ==> w x IN S) /\ wan_w12 s' w /\ wan_vtest s' phi /\ &0 < d0 /\
     1 <= i /\ i <= 2
     ==> ((\n. drop(integral s'
              (\x. lift(hmrm_eld S G (w x) (wan_wd s' i w x)
                     ((&1 - smooth_bump (d0 * inv(&n + &1)) (&2 * (d0 * inv(&n + &1))) (x - a)) %
                      phi x)
                     ((&1 - smooth_bump (d0 * inv(&n + &1)) (&2 * (d0 * inv(&n + &1))) (x - a)) %
                      partial_derivative i phi x)))))
          ---> drop(integral s' (\x. lift(hmrm_eld S G (w x) (wan_wd s' i w x) (phi x)
                                          (partial_derivative i phi x))))) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s':real^2->bool`; `phi:real^2->real^K`] HMRR_VTEST_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`s':real^2->bool`; `partial_derivative i (phi:real^2->real^K)`]
    HMRR_VTEST_BOUNDS) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[HMRR_VTEST_PD]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_THEN `M1:real` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `compact(closure s':real^2->bool) /\ s' SUBSET closure s' /\
                lebesgue_measurable(s':real^2->bool)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_CLOSURE; CLOSURE_SUBSET; LEBESGUE_MEASURABLE_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!f:real^2->real^K. f continuous_on (:real^2) ==> f IN lspace s' (&2)`
  (LABEL_TAC "cl2") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HMRR_CONT_LSPACE2 THEN
    EXISTS_TAC `closure s':real^2->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n (f:real^2->real^K). f continuous_on (:real^2)
        ==> (\x. (&1 - smooth_bump (d0 * inv(&n + &1)) (&2 * (d0 * inv(&n + &1))) (x - a)) %
                 f x) continuous_on (:real^2)`
  (LABEL_TAC "cmul") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN ASM_REWRITE_TAC[o_DEF] THEN
    MP_TAC(ISPECL [`a:real^2`; `d0 * inv(&n + &1)`] HMRR_CUT_FACTS) THEN
    ASM_SIMP_TAC[WAN_EN_FACTS];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:real^2->real^K) continuous_on s'` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (\x. (&1 - smooth_bump (d0 * inv(&n + &1)) (&2 * (d0 * inv(&n + &1))) (x - a)) %
             (phi:real^2->real^K) x) continuous_on s'`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN USE_THEN "cmul" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n x. x IN s'
          ==> norm((&1 - smooth_bump (d0 * inv(&n + &1)) (&2 * (d0 * inv(&n + &1))) (x - a)) %
                   (phi:real^2->real^K) x) <= M`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_MUL] THEN
    MP_TAC(ISPECL [`a:real^2`; `d0 * inv(&n + &1)`] HMRR_CUT_FACTS) THEN
    ASM_SIMP_TAC[WAN_EN_FACTS] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * norm((phi:real^2->real^K) x)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2` o check (is_conj o snd o dest_forall o concl)) THEN
      REAL_ARITH_TAC;
      ASM_REWRITE_TAC[REAL_MUL_LID]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN s' DIFF {a:real^2}
        ==> ((\n. (&1 - smooth_bump (d0 * inv(&n + &1)) (&2 * (d0 * inv(&n + &1))) (x - a)) %
                  (phi:real^2->real^K) x) --> phi x) sequentially`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_DIFF; IN_SING] THEN STRIP_TAC THEN
    MATCH_MP_TAC LIM_EVENTUALLY THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    MP_TAC(ISPECL [`d0:real`; `a:real^2`; `x:real^2`] WAN_CUTOFF_SEQ) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
    DISCH_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`a:real^2`; `d0 * inv(&n + &1)`] HMRR_CUT_FACTS) THEN
    ASM_SIMP_TAC[WAN_EN_FACTS] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&2 * (d0 * inv(&n + &1)) <= norm(x - a:real^2)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (\x. (&1 - smooth_bump (d0 * inv(&n + &1)) (&2 * (d0 * inv(&n + &1))) (x - a)) %
             partial_derivative i (phi:real^2->real^K) x) IN lspace s' (&2)`
  ASSUME_TAC THENL
   [GEN_TAC THEN USE_THEN "cl2" MATCH_MP_TAC THEN USE_THEN "cmul" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `partial_derivative i (phi:real^2->real^K) IN lspace s' (&2)` ASSUME_TAC THENL
   [USE_THEN "cl2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s':real^2->bool`; `partial_derivative i (phi:real^2->real^K)`; `a:real^2`;
                 `d0:real`; `M1:real`] HMRR_CUT_L2_NULL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s':real^2->bool`; `i:num`; `w:real^2->real^K`] WAN_WD_WORKS) THEN
  ASM_REWRITE_TAC[DIMINDEX_2] THEN STRIP_TAC THEN
  MP_TAC(BETA_RULE(ISPECL
   [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s':real^2->bool`; `w:real^2->real^K`;
    `wan_wd s' i (w:real^2->real^K)`;
    `\n x. (&1 - smooth_bump (d0 * inv(&n + &1)) (&2 * (d0 * inv(&n + &1))) (x - a)) %
           (phi:real^2->real^K) x`;
    `\n x. (&1 - smooth_bump (d0 * inv(&n + &1)) (&2 * (d0 * inv(&n + &1))) (x - a)) %
           partial_derivative i (phi:real^2->real^K) x`;
    `phi:real^2->real^K`; `partial_derivative i (phi:real^2->real^K)`;
    `M:real`; `{a:real^2}`] HMRC_ELD_LIMIT)) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[NEGLIGIBLE_SING]);;

(* For each cutoff radius the identity for (1 - eta) phi splits into the   *)
(* main terms and the cutoff-derivative terms.                              *)

let HMRR_EL_SPLIT = prove
 (`!S (G:real^K->real^K^K) d (w:real^2->real^K) a r s' (phi:real^2->real^K) e.
     cm_target S G d /\ &0 < r /\ cm_wharmonic S G (ball(a,r) DELETE a) w /\
     wan_w12 s' w /\ w continuous_on s' /\ (!x. x IN s' ==> w x IN S) /\
     open s' /\ bounded s' /\ closure s' SUBSET ball(a,r) /\ wan_vtest s' phi /\ &0 < e
     ==> sum(1..2) (\i. drop(integral s'
           (\x. lift(hmrm_eld S G (w x) (wan_wd s' i w x)
                   ((&1 - smooth_bump e (&2 * e) (x - a)) % phi x)
                   ((&1 - smooth_bump e (&2 * e) (x - a)) % partial_derivative i phi x))))) =
         sum(1..2) (\i. drop(integral s'
           (\x. lift(hmrm_eld S G (w x) (wan_wd s' i w x) (vec 0)
                   (wan_dpart i (\y. smooth_bump e (&2 * e) (y - a)) x % phi x)))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^2`; `e:real`] WAN_POINT_CUTOFF_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s':real^2->bool`; `phi:real^2->real^K`;
                 `\x:real^2. smooth_bump e (&2 * e) (x - a)`; `a:real^2`; `e:real`]
    WAN_VTEST_MUL_CUTOFF) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[IN_BALL] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `dist(a:real^2,x) < e` THEN REWRITE_TAC[dist] THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "pd")) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `w:real^2->real^K`;
                 `a:real^2`; `r:real`; `s':real^2->bool`; `phi:real^2->real^K`; `e:real`]
    HMRR_EL_PHIE) THEN
  ASM_REWRITE_TAC[] THEN USE_THEN "pd" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(LABEL_TAC "el") THEN
  MP_TAC(ISPECL [`s':real^2->bool`; `phi:real^2->real^K`] HMRR_VTEST_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`a:real^2`; `e:real`] HMRR_CUT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact(closure s':real^2->bool) /\ s' SUBSET closure s' /\
                lebesgue_measurable(s':real^2->bool)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_CLOSURE; CLOSURE_SUBSET; LEBESGUE_MEASURABLE_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!f:real^2->real^K. f continuous_on (:real^2) ==> f IN lspace s' (&2)`
  (LABEL_TAC "cl2") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HMRR_CONT_LSPACE2 THEN
    EXISTS_TAC `closure s':real^2->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. (&1 - smooth_bump e (&2 * e) (x - a)) % (phi:real^2->real^K) x) continuous_on s' /\
    (!x. x IN s'
         ==> norm((&1 - smooth_bump e (&2 * e) (x - a)) % (phi:real^2->real^K) x) <= M) /\
    (!i. (\x. (&1 - smooth_bump e (&2 * e) (x - a)) % partial_derivative i (phi:real^2->real^K) x)
         IN lspace s' (&2)) /\
    (!i. (\x. wan_dpart i (\y. smooth_bump e (&2 * e) (y - a)) x % (phi:real^2->real^K) x)
         IN lspace s' (&2))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
      ASM_REWRITE_TAC[o_DEF];
      REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_MUL] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * norm((phi:real^2->real^K) x)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2` o check (fun th ->
          is_conj(snd(dest_forall(concl th))) &&
          can (find_term (fun t -> t = `&1 - smooth_bump e (&2 * e) (x - a:real^2)`))
              (concl th))) THEN
        REAL_ARITH_TAC;
        ASM_REWRITE_TAC[REAL_MUL_LID]];
      GEN_TAC THEN USE_THEN "cl2" MATCH_MP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
      ASM_REWRITE_TAC[o_DEF; ETA_AX];
      GEN_TAC THEN USE_THEN "cl2" MATCH_MP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
      ASM_REWRITE_TAC[o_DEF] THEN
      MP_TAC(ISPECL [`i:num`; `\y:real^2. smooth_bump e (&2 * e) (y - a)`] WAN_DPART_SMOOTH) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> (\x. lift(hmrm_eld S G ((w:real^2->real^K) x) (wan_wd s' i w x)
                   ((&1 - smooth_bump e (&2 * e) (x - a)) % (phi:real^2->real^K) x)
                   ((&1 - smooth_bump e (&2 * e) (x - a)) % partial_derivative i phi x)))
            integrable_on s' /\
            (\x. lift(hmrm_eld S G (w x) (wan_wd s' i w x) (vec 0)
                   (wan_dpart i (\y. smooth_bump e (&2 * e) (y - a)) x % phi x)))
            integrable_on s'`
  (LABEL_TAC "int") THENL
   [GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`s':real^2->bool`; `i:num`; `w:real^2->real^K`] WAN_WD_WORKS) THEN
    ASM_REWRITE_TAC[DIMINDEX_2] THEN STRIP_TAC THEN CONJ_TAC THEN
    MATCH_MP_TAC HMRC_ELD_INTEGRABLE THEN
    MAP_EVERY EXISTS_TAC [`d:real`; `M:real`] THEN
    ASM_REWRITE_TAC[CONTINUOUS_ON_CONST; NORM_0; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> drop(integral s'
             (\x. lift(hmrm_eld S G ((w:real^2->real^K) x) (wan_wd s' i w x)
                   ((&1 - smooth_bump e (&2 * e) (x - a)) % (phi:real^2->real^K) x)
                   ((&1 - smooth_bump e (&2 * e) (x - a)) % partial_derivative i phi x -
                    wan_dpart i (\x. smooth_bump e (&2 * e) (x - a)) x % phi x)))) =
            drop(integral s'
             (\x. lift(hmrm_eld S G (w x) (wan_wd s' i w x)
                   ((&1 - smooth_bump e (&2 * e) (x - a)) % phi x)
                   ((&1 - smooth_bump e (&2 * e) (x - a)) % partial_derivative i phi x)))) -
            drop(integral s'
             (\x. lift(hmrm_eld S G (w x) (wan_wd s' i w x) (vec 0)
                   (wan_dpart i (\y. smooth_bump e (&2 * e) (y - a)) x % phi x))))`
  (LABEL_TAC "split") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "int" (MP_TAC o C MATCH_MP (ASSUME `1 <= i /\ i <= 2`)) THEN STRIP_TAC THEN
    ASM_SIMP_TAC[GSYM DROP_SUB; GSYM INTEGRAL_SUB] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM LIFT_SUB] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `(w:real^2->real^K) x`;
                   `wan_wd s' i (w:real^2->real^K) x`;
                   `(&1 - smooth_bump e (&2 * e) (x - a)) % (phi:real^2->real^K) x`;
                   `vec 0:real^K`;
                   `(&1 - smooth_bump e (&2 * e) (x - a)) %
                    partial_derivative i (phi:real^2->real^K) x`;
                   `wan_dpart i (\y. smooth_bump e (&2 * e) (y - a)) x %
                    (phi:real^2->real^K) x`]
      HMRC_ELD_SUB) THEN
    ASM_SIMP_TAC[VECTOR_SUB_RZERO];
    ALL_TAC] THEN
  USE_THEN "el" MP_TAC THEN REWRITE_TAC[SUM_2] THEN
  USE_THEN "split" (MP_TAC o SPEC `1`) THEN USE_THEN "split" (MP_TAC o SPEC `2`) THEN
  REWRITE_TAC[ARITH_RULE `1 <= 1 /\ 1 <= 2 /\ 2 <= 2`] THEN REAL_ARITH_TAC);;

let HMRR_SUM_LIMIT_ZERO = prove
 (`!(f:num->num->real) g l.
     (!i. 1 <= i /\ i <= 2 ==> ((\n. f i n) ---> l i) sequentially) /\
     (!i. 1 <= i /\ i <= 2 ==> ((\n. g i n) ---> &0) sequentially) /\
     (!n. sum(1..2) (\i. f i n) = sum(1..2) (\i. g i n))
     ==> sum(1..2) l = &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ETA_AX] THEN STRIP_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
  EXISTS_TAC `\n. sum(1..2) (\i. (f:num->num->real) i n)` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_SUM THEN ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG];
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`sequentially`; `g:num->num->real`; `\i:num. &0`; `1..2`] REALLIM_SUM) THEN
    REWRITE_TAC[SUM_0; FINITE_NUMSEG; IN_NUMSEG] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[]]);;

(* The Euler-Lagrange identity across the point. *)

let HMRR_EL_ACROSS = prove
 (`!S (G:real^K->real^K^K) d (w:real^2->real^K) a r s' (phi:real^2->real^K).
     cm_target S G d /\ &0 < r /\ cm_wharmonic S G (ball(a,r) DELETE a) w /\
     wan_w12 s' w /\ w continuous_on s' /\ (!x. x IN s' ==> w x IN S) /\
     open s' /\ bounded s' /\ closure s' SUBSET ball(a,r) /\ wan_vtest s' phi
     ==> sum(1..2) (\i. drop(integral s'
           (\x. lift(hmrm_eld S G (w x) (wan_wd s' i w x) (phi x)
                              (partial_derivative i phi x))))) = &0`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `(a:real^2) IN s'` THENL
   [MP_TAC(ISPEC `s':real^2->bool` OPEN_CONTAINS_CBALL) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `a:real^2`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?d0. &0 < d0 /\ &2 * d0 <= r0 /\ d0 <= &1` STRIP_ASSUME_TAC THENL
     [EXISTS_TAC `min (r0 / &2) (&1)` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC HMRR_SUM_LIMIT_ZERO THEN
    EXISTS_TAC `\i n. drop(integral s'
       (\x. lift(hmrm_eld S G ((w:real^2->real^K) x) (wan_wd s' i w x)
          ((&1 - smooth_bump (d0 * inv(&n + &1)) (&2 * (d0 * inv(&n + &1))) (x - a)) %
           (phi:real^2->real^K) x)
          ((&1 - smooth_bump (d0 * inv(&n + &1)) (&2 * (d0 * inv(&n + &1))) (x - a)) %
           partial_derivative i phi x))))` THEN
    EXISTS_TAC `\i n. drop(integral s'
       (\x. lift(hmrm_eld S G ((w:real^2->real^K) x) (wan_wd s' i w x) (vec 0)
          (wan_dpart i (\y. smooth_bump (d0 * inv(&n + &1)) (&2 * (d0 * inv(&n + &1)))
                              (y - a)) x %
           (phi:real^2->real^K) x))))` THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC HMRR_T1_LIMIT THEN EXISTS_TAC `d:real` THEN
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC HMRR_BAD_LIMIT THEN
      MAP_EVERY EXISTS_TAC [`d:real`; `r0:real`] THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `n:num` THEN MATCH_MP_TAC HMRR_EL_SPLIT THEN
      MAP_EVERY EXISTS_TAC [`d:real`; `r:real`] THEN ASM_SIMP_TAC[WAN_EN_FACTS]];
    ALL_TAC] THEN
  (* the point is outside the set: the support stays away from it *)
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_vtest] o
    check (fun th -> concl th = `wan_vtest s' (phi:real^2->real^K)`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:real^2->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`k:real^2->bool`; `a:real^2`] SEPARATE_POINT_CLOSED) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < d1 / &4` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^2`; `d1 / &4`] HMRR_CUT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. (&1 - smooth_bump (d1 / &4) (&2 * d1 / &4) (x - a)) % (phi:real^2->real^K) x = phi x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN ASM_CASES_TAC `(x:real^2) IN k` THENL
     [SUBGOAL_THEN `&2 * d1 / &4 <= norm(x - a:real^2)` ASSUME_TAC THENL
       [MP_TAC(MATCH_MP (ASSUME `!x. x IN k ==> d1 <= dist(a:real^2,x)`)
                        (ASSUME `(x:real^2) IN k`)) THEN
        REWRITE_TAC[dist] THEN MP_TAC(ISPECL [`a:real^2`; `x:real^2`] NORM_SUB) THEN
        ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[VECTOR_MUL_LID]];
      ASM_SIMP_TAC[VECTOR_MUL_RZERO]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `w:real^2->real^K`;
                 `a:real^2`; `r:real`; `s':real^2->bool`; `phi:real^2->real^K`; `d1 / &4`]
    HMRR_EL_PHIE) THEN
  ASM_REWRITE_TAC[ETA_AX] THEN SIMP_TAC[]);;

(* ========================================================================= *)
(* The removable singularity theorem.                                     *)
(* The harmonic map extends by its limit L at the point (HMRR_LIMIT); the  *)
(* extension is continuous with values in S, lies in W^1,2 of the ball      *)
(* (a point has zero capacity, WAN_REMOVABLE_POINT), and satisfies the      *)
(* Euler-Lagrange identity across the point (HMRR_EL_ACROSS), so it is      *)
(* weakly harmonic on the ball and hence smooth harmonic (CM_REG01).        *)
(* ========================================================================= *)

let HMRR_EXT_CONT = prove
 (`!(u:real^2->real^K) w a r L.
     u continuous_on (ball(a,r) DELETE a) /\ w a = L /\ (!x. ~(x = a) ==> w x = u x) /\
     (!e. &0 < e ==> ?del. &0 < del /\
                           !x. &0 < norm(x - a) /\ norm(x - a) < del ==> norm(u x - L) < e)
     ==> w continuous_on ball(a,r)`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_BALL] THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN ASM_CASES_TAC `x:real^2 = a` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ASM_REWRITE_TAC[CONTINUOUS_AT; LIM_AT] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `del:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^2` THEN REWRITE_TAC[dist] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(y:real^2 = a)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `&0 < norm(a - a:real^2)` THEN REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN
      REAL_ARITH_TAC;
      ASM_SIMP_TAC[]];
    MATCH_MP_TAC CONTINUOUS_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [`u:real^2->real^K`; `dist(x:real^2,a)`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[DIST_POS_LT];
      X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(y:real^2 = a)` (fun th -> ASM_SIMP_TAC[th]) THEN
      DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `dist(a:real^2,x) < dist(x,a)` THEN
      REWRITE_TAC[dist] THEN CONV_TAC NORM_ARITH;
      UNDISCH_TAC `(u:real^2->real^K) continuous_on (ball(a,r) DELETE a)` THEN
      SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_DELETE; OPEN_BALL] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DELETE]]]);;

let HMRR_LIMIT_IN = prove
 (`!(S:real^K->bool) (u:real^2->real^K) a r L.
     closed S /\ &0 < r /\ (!x. x IN ball(a,r) DELETE a ==> u x IN S) /\
     (!e. &0 < e ==> ?del. &0 < del /\
                           !x. &0 < norm(x - a) /\ norm(x - a) < del ==> norm(u x - L) < e)
     ==> L IN S`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:real^K`; `S:real^K->bool`] CLOSED_APPROACHABLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `del:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?c. &0 < c /\ c < del /\ c < r` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min del r / &2` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `norm((a + c % basis 1) - a:real^2) = c` ASSUME_TAC THENL
   [REWRITE_TAC[VECTOR_ARITH `(a + x) - a:real^N = x`; NORM_MUL] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_2; ARITH; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `(u:real^2->real^K)(a + c % basis 1)` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_DELETE; IN_BALL; dist] THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN UNDISCH_TAC `norm((a + c % basis 1) - a:real^2) = c` THEN
      ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[dist] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* The extension by the limit is weakly harmonic on the ball. *)

let HMRR_EXT_WHARMONIC = prove
 (`!S (G:real^K->real^K^K) d (u:real^2->real^K) (w:real^2->real^K) a r L.
     cm_target S G d /\ &0 < r /\ cm_harmonic S G (ball(a,r) DELETE a) u /\
     wan_w12 (ball(a,r) DELETE a) u /\ w a = L /\ (!x. ~(x = a) ==> w x = u x) /\
     (!e. &0 < e ==> ?del. &0 < del /\
                           !x. &0 < norm(x - a) /\ norm(x - a) < del ==> norm(u x - L) < e)
     ==> cm_wharmonic S G (ball(a,r)) w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!x. x IN ball(a:real^2,r) DELETE a ==> (w:real^2->real^K) x = u x`
  ASSUME_TAC THENL [ASM_SIMP_TAC[IN_DELETE]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_harmonic] o
    check (fun th -> concl th =
      `cm_harmonic S (G:real^K->real^K^K) (ball(a:real^2,r) DELETE a) u`)) THEN
  SUBGOAL_THEN `cm_harmonic S (G:real^K->real^K^K) (ball(a:real^2,r) DELETE a) w`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HMRR_HARMONIC_EQ_ON THEN EXISTS_TAC `u:real^2->real^K` THEN
    ASM_SIMP_TAC[OPEN_DELETE; OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 (ball(a:real^2,r) DELETE a) (w:real^2->real^K)` ASSUME_TAC THENL
   [MATCH_MP_TAC HMRR_W12_EQ_ON THEN EXISTS_TAC `u:real^2->real^K` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 (ball(a:real^2,r)) (w:real^2->real^K)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:2)`; `(:K)`] WAN_REMOVABLE_POINT) THEN
    REWRITE_TAC[WAN_REMOVABLE_POINT_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPECL [`ball(a:real^2,r)`; `a:real^2`; `w:real^2->real^K`]) THEN
    ASM_REWRITE_TAC[OPEN_BALL; DIMINDEX_2; LE_REFL;
                    SET_RULE `(s:real^2->bool) DIFF {a} = s DELETE a`] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^2->real^K) continuous_on ball(a,r)` ASSUME_TAC THENL
   [MATCH_MP_TAC HMRR_EXT_CONT THEN
    MAP_EVERY EXISTS_TAC [`u:real^2->real^K`; `L:real^K`] THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN ball(a:real^2,r) ==> (w:real^2->real^K) x IN S` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN ASM_CASES_TAC `x:real^2 = a` THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HMRR_LIMIT_IN THEN
      MAP_EVERY EXISTS_TAC [`u:real^2->real^K`; `a:real^2`; `r:real`] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `cm_target S (G:real^K->real^K^K) d` THEN
      SIMP_TAC[cm_target; COMPACT_IMP_CLOSED];
      ASM_SIMP_TAC[IN_DELETE]];
    ALL_TAC] THEN
  REWRITE_TAC[cm_wharmonic] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`phi:real^2->real^K`; `s':real^2->bool`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(s':real^2->bool) SUBSET ball(a,r)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `s':real^2->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 s' (w:real^2->real^K) /\ w continuous_on s' /\
                (!x. x IN s' ==> w x IN S)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC WAN_W12_SUBSET THEN EXISTS_TAC `ball(a:real^2,r)` THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s':real^2->bool`;
                 `w:real^2->real^K`; `phi:real^2->real^K`] HMRM_FIRST_VARIATION_W12) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `w:real^2->real^K`;
                 `a:real^2`; `r:real`; `s':real^2->bool`; `phi:real^2->real^K`]
    HMRR_EL_ACROSS) THEN
  ASM_SIMP_TAC[CM_HARMONIC_IMP_WHARMONIC] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO]);;

(* The headline: removable point singularities (CM_REMOVABLE). *)

let CM_REMOVABLE = prove
 (`!kk:K->bool. CM_REMOVABLE_STATEMENT kk`,
  GEN_TAC THEN REWRITE_TAC[CM_REMOVABLE_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:real^2`; `r:real`; `u:real^2->real^K`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `u:real^2->real^K`;
                 `a:real^2`; `r:real`] HMRR_LIMIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `L:real^K`) THEN
  EXISTS_TAC `\x:real^2. if x = a then L else (u:real^2->real^K) x` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPEC `kk:K->bool` CM_REG01) THEN REWRITE_TAC[CM_REG01_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[OPEN_BALL] THEN
    MATCH_MP_TAC HMRR_EXT_WHARMONIC THEN
    MAP_EVERY EXISTS_TAC [`d:real`; `u:real^2->real^K`; `L:real^K`] THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    SIMP_TAC[IN_DELETE]]);;

