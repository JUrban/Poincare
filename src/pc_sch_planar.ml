(* ========================================================================= *)
(* pc_sch_planar: collared smooth Schoenflies in the plane, SCH_R2_STATEMENT *)
(* and SCH_COLLAR2_STATEMENT.                                                *)
(*                                                                           *)
(* Route (conformal): Beltrami straightening of the collar near the          *)
(* circle of radius 5/8 (bel_fsol of pc_an_beltrami), the analytic-collar    *)
(* Schoenflies theorem SCH2_ANALYTIC_COLLAR of pc_sch_conf, extension of the *)
(* circle map J z = z cexp(L z) to a diffeomorphism of the plane by the      *)
(* isotopy z cexp(t L z) (injective on a thin annulus by Noshiro-            *)
(* Warschawski in log coordinates) and isotopy extension (pc_sch_isoext),    *)
(* and gluing with f outside radius 5/8.                                     *)
(* ========================================================================= *)

needs "src/pc_sch_conf.ml";;
needs "src/pc_sch_isoext.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The logarithmic derivative 1 + z L'(z) of J z = z cexp(L z)               *)
(* is real and positive on the unit circle; Noshiro-Warschawski.             *)
(* ------------------------------------------------------------------------- *)

let SCH2_CNJ_CONJ_DERIV = prove
 (`!f:complex->complex f' z.
        (f has_complex_derivative f') (at (cnj z))
        ==> ((\w. cnj(f(cnj w))) has_complex_derivative cnj f') (at z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_complex_derivative] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(cnj has_derivative cnj) (at (z:complex)) /\
                (cnj has_derivative cnj) (at ((f:complex->complex)(cnj z)))`
  STRIP_ASSUME_TAC THENL [SIMP_TAC[HAS_DERIVATIVE_LINEAR; LINEAR_CNJ]; ALL_TAC] THEN
  MP_TAC(ISPECL [`cnj`; `f:complex->complex`; `cnj`; `\h:complex. f' * h`; `z:complex`]
                DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(f:complex->complex) o cnj`; `cnj`; `(\h:complex. f' * h) o cnj`;
                 `cnj`; `z:complex`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[o_THM] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; CNJ_MUL; CNJ_CNJ]);;

let SCH2_UNIT_INV_CNJ = prove
 (`!z. norm z = &1 ==> inv(cnj z) = z /\ inv z = cnj z /\ ~(z = Cx(&0))`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(z = Cx(&0))` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `norm(z:complex) = &1` THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `inv z = cnj(z:complex)` ASSUME_TAC THENL
   [REWRITE_TAC[COMPLEX_INV_CNJ] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM CNJ_INV; CNJ_CNJ]);;

let SCH2_LOGDER_REAL = prove
 (`!L r0 z. &0 < r0 /\ r0 < &1 /\ L holomorphic_on annulus r0 (inv r0) /\
            (!z. z IN annulus r0 (inv r0) ==> L(inv(cnj z)) = --cnj(L z)) /\
            norm z = &1
            ==> cnj(z * complex_derivative L z) = z * complex_derivative L z`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH2_UNIT_INV_CNJ) THEN
  SUBGOAL_THEN `&1 < inv r0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INV_1_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(z:complex) IN annulus r0 (inv r0)` ASSUME_TAC THENL
   [REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `open(annulus r0 (inv r0):complex->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[OPEN_ANNULUS]; ALL_TAC] THEN
  SUBGOAL_THEN `!w. w IN annulus r0 (inv r0)
                    ==> ((L:complex->complex) has_complex_derivative complex_derivative L w) (at w)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT THEN
    EXISTS_TAC `annulus r0 (inv r0):complex->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* M w = --cnj(L(cnj(inv w))) has derivative cnj(L' z) inv(z^2) at z. *)
  SUBGOAL_THEN `((\w. --cnj((L:complex->complex)(cnj(inv w)))) has_complex_derivative
                 (cnj(complex_derivative L z) * inv(z pow 2))) (at z)` ASSUME_TAC THENL
   [SUBGOAL_THEN `cnj(complex_derivative (L:complex->complex) z) * inv(z pow 2) =
                  --(cnj(complex_derivative L (cnj(inv z))) * --inv(z pow 2))`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[CNJ_CNJ] THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_NEG THEN
    MP_TAC(ISPECL [`inv:complex->complex`; `\w. cnj((L:complex->complex)(cnj w))`;
                   `--inv((z:complex) pow 2)`;
                   `cnj(complex_derivative (L:complex->complex) (cnj(inv z)))`;
                   `z:complex`] COMPLEX_DIFF_CHAIN_AT) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_INV_BASIC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SCH2_CNJ_CONJ_DERIV THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[CNJ_CNJ]];
    ALL_TAC] THEN
  (* M = L near z, so the derivatives agree. *)
  SUBGOAL_THEN `((L:complex->complex) has_complex_derivative
                 (cnj(complex_derivative L z) * inv(z pow 2))) (at z)` ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `\w. --cnj((L:complex->complex)(cnj(inv w)))` THEN
    MP_TAC(ISPEC `annulus r0 (inv r0):complex->bool` OPEN_CONTAINS_BALL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(w:complex) IN annulus r0 (inv r0)` ASSUME_TAC THENL
     [UNDISCH_TAC `ball(z:complex,d) SUBSET annulus r0 (inv r0)` THEN
      REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
      ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[CNJ_INV] THEN
    UNDISCH_TAC `!z. z IN annulus r0 (inv r0)
                     ==> (L:complex->complex)(inv(cnj z)) = --cnj(L z)` THEN
    DISCH_THEN(fun th -> REWRITE_TAC[MP (SPEC `w:complex` th)
      (ASSUME `(w:complex) IN annulus r0 (inv r0)`)]) THEN
    REWRITE_TAC[CNJ_NEG; CNJ_CNJ; COMPLEX_NEG_NEG];
    ALL_TAC] THEN
  SUBGOAL_THEN `complex_derivative (L:complex->complex) z =
                cnj(complex_derivative L z) * inv(z pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPLEX_DERIVATIVE_UNIQUE_AT THEN
    EXISTS_TAC `L:complex->complex` THEN EXISTS_TAC `z:complex` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th]) THEN
  REWRITE_TAC[CNJ_MUL] THEN
  UNDISCH_TAC `inv z = cnj(z:complex)` THEN UNDISCH_TAC `~(z = Cx(&0))` THEN
  CONV_TAC COMPLEX_FIELD);;

let SCH2_JT_DERIV = prove
 (`!L:complex->complex z t.
        L complex_differentiable at z
        ==> ((\w. w * cexp(Cx t * L w)) has_complex_derivative
             cexp(Cx t * L z) * (Cx(&1) + Cx t * z * complex_derivative L z)) (at z)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[GSYM HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE]) THEN
  SUBGOAL_THEN `((\w. cexp(Cx t * (L:complex->complex) w)) has_complex_derivative
                 (cexp(Cx t * L z) * (Cx t * complex_derivative L z))) (at z)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\w. Cx t * (L:complex->complex) w`; `cexp`;
                   `Cx t * complex_derivative (L:complex->complex) z`;
                   `cexp(Cx t * (L:complex->complex) z)`; `z:complex`] COMPLEX_DIFF_CHAIN_AT) THEN
    REWRITE_TAC[o_DEF; HAS_COMPLEX_DERIVATIVE_CEXP] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_LMUL_AT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\w:complex. w`; `Cx(&1)`; `\w. cexp(Cx t * (L:complex->complex) w)`;
                 `cexp(Cx t * (L:complex->complex) z) * (Cx t * complex_derivative L z)`;
                 `z:complex`] HAS_COMPLEX_DERIVATIVE_MUL_AT) THEN
  ASM_REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_ID] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC COMPLEX_RING);;

let SCH2_LOGDER_POS = prove
 (`!L r0 z. &0 < r0 /\ r0 < &1 /\ L holomorphic_on annulus r0 (inv r0) /\
            (!z. z IN annulus r0 (inv r0) ==> L(inv(cnj z)) = --cnj(L z)) /\
            (!z. z IN annulus r0 (&1) ==> norm(z * cexp(L z)) < &1) /\
            (!w z. w IN annulus r0 (&1) /\ z IN annulus r0 (&1) /\
                   w * cexp(L w) = z * cexp(L z) ==> w = z) /\
            norm z = &1
            ==> &0 < Re(Cx(&1) + z * complex_derivative L z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`L:complex->complex`; `r0:real`] SCH2_J_INJ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "JI") THEN
  MP_TAC(SPECL [`L:complex->complex`; `r0:real`] SCH2_J_NORMS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "JN") THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH2_UNIT_INV_CNJ) THEN
  SUBGOAL_THEN `&1 < inv r0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INV_1_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(z:complex) IN annulus r0 (inv r0)` ASSUME_TAC THENL
   [REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `lam = Cx(&1) + z * complex_derivative (L:complex->complex) z` THEN
  SUBGOAL_THEN `lam = Cx(Re lam)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`L:complex->complex`; `r0:real`; `z:complex`] SCH2_LOGDER_REAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `real(lam:complex)` MP_TAC THENL
     [REWRITE_TAC[REAL_CNJ] THEN EXPAND_TAC "lam" THEN
      ASM_REWRITE_TAC[CNJ_ADD; CNJ_CX];
      REWRITE_TAC[real; COMPLEX_EQ; RE_CX; IM_CX] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(L:complex->complex) complex_differentiable at z` ASSUME_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT THEN
    EXISTS_TAC `annulus r0 (inv r0):complex->bool` THEN ASM_REWRITE_TAC[OPEN_ANNULUS];
    ALL_TAC] THEN
  MP_TAC(SPECL [`L:complex->complex`; `z:complex`; `&1`] SCH2_JT_DERIV) THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_LID] THEN DISCH_TAC THEN
  (* lam is nonzero since J is injective. *)
  SUBGOAL_THEN `~(lam = Cx(&0))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\w:complex. w * cexp((L:complex->complex) w)`;
                   `annulus r0 (inv r0):complex->bool`] HOLOMORPHIC_INJECTIVE_IMP_REGULAR) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[OPEN_ANNULUS] THEN CONJ_TAC THENL
       [MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN REWRITE_TAC[HOLOMORPHIC_ON_ID] THEN
        GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM o_DEF] THEN
        MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE THEN ASM_REWRITE_TAC[HOLOMORPHIC_ON_CEXP];
        USE_THEN "JI" ACCEPT_TAC];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP HAS_COMPLEX_DERIVATIVE_DERIVATIVE th]) THEN
    REWRITE_TAC[COMPLEX_ENTIRE; CEXP_NZ];
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 < Re lam` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `Re lam < &0` ASSUME_TAC THENL
   [SUBGOAL_THEN `~(Re lam = &0)` MP_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~(lam = Cx(&0))` THEN REWRITE_TAC[] THEN
      GEN_REWRITE_TAC LAND_CONV [ASSUME `lam = Cx(Re lam)`] THEN
      REWRITE_TAC[ASSUME `Re lam = &0`];
      UNDISCH_TAC `~(&0 < Re lam)` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `a = --Re lam` THEN
  SUBGOAL_THEN `&0 < a /\ lam = Cx(--a)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN REWRITE_TAC[REAL_NEG_NEG] THEN CONJ_TAC THENL
     [UNDISCH_TAC `Re lam < &0` THEN REAL_ARITH_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  (* First-order expansion of J at z along the inward normal. *)
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HAS_COMPLEX_DERIVATIVE_AT] o check (fun th ->
    can (find_term ((=) `has_complex_derivative`)) (concl th))) THEN
  REWRITE_TAC[LIM_AT] THEN DISCH_THEN(MP_TAC o SPEC `a / &2`) THEN
  ANTS_TAC THENL [UNDISCH_TAC `&0 < a` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LIMD"))) THEN
  ABBREV_TAC `e = min (d / &2) ((&1 - r0) / &2)` THEN
  SUBGOAL_THEN `&0 < e /\ e < d /\ e < &1 - r0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN UNDISCH_TAC `&0 < d` THEN UNDISCH_TAC `r0 < &1` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `w = Cx(&1 - e) * z` THEN
  SUBGOAL_THEN `w - z = Cx(--e) * z` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN REWRITE_TAC[CX_SUB; CX_NEG] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(w:complex) = &1 - e /\ norm(w - z) = e` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "w" THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN ASM_REWRITE_TAC[REAL_MUL_RID] THEN
    UNDISCH_TAC `&0 < e` THEN UNDISCH_TAC `e < &1 - r0` THEN UNDISCH_TAC `&0 < r0` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm((w * cexp((L:complex->complex) w) - z * cexp(L z)) / (w - z) -
                     cexp(L z) * lam) < a / &2` ASSUME_TAC THENL
   [USE_THEN "LIMD" (MP_TAC o SPEC `w:complex`) THEN REWRITE_TAC[dist] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:complex) IN annulus r0 (&1)` ASSUME_TAC THENL
   [REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < e` THEN UNDISCH_TAC `e < &1 - r0` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(w * cexp((L:complex->complex) w)) < &1` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `annulus r0 (&1):complex->bool`)) (concl th) &&
      not(is_conj(lhand(snd(strip_forall(concl th))))))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(z * cexp((L:complex->complex) z)) = &1` ASSUME_TAC THENL
   [USE_THEN "JN" (fun th -> REWRITE_TAC[MP (SPEC `z:complex` th)
      (ASSUME `(z:complex) IN annulus r0 (inv r0)`)]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(w - z = Cx(&0))` ASSUME_TAC THENL
   [DISCH_THEN(fun th -> UNDISCH_TAC `norm(w - z:complex) = e` THEN
      REWRITE_TAC[th; COMPLEX_NORM_0]) THEN
    UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Q = (w * cexp((L:complex->complex) w) - z * cexp(L z)) / (w - z)` THEN
  SUBGOAL_THEN `w * cexp((L:complex->complex) w) =
                (z * cexp(L z)) * (Cx(&1) + Cx(e * a)) +
                (w - z) * (Q - cexp(L z) * lam)` SUBST1_TAC THENL
   [EXPAND_TAC "Q" THEN UNDISCH_TAC `~(w - z = Cx(&0))` THEN
    REWRITE_TAC[ASSUME `w - z = Cx(--e) * z`; ASSUME `lam = Cx(--a)`] THEN
    REWRITE_TAC[CX_MUL; CX_NEG] THEN CONV_TAC COMPLEX_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < e * a / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; UNDISCH_TAC `&0 < a` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < e * a / &2 /\ &1 + e * a / &2 <= x ==> x < &1 ==> F`) THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `!x r s. r - s <= x /\ &1 + e * a / &2 <= r - s
                                    ==> &1 + e * a / &2 <= x`) THEN
  MAP_EVERY EXISTS_TAC [`&1 + e * a`; `e * a / &2`] THEN
  CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  MATCH_MP_TAC(NORM_ARITH `!x y:complex r s. norm x = r /\ norm y <= s ==> r - s <= norm(x + y)`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[COMPLEX_NORM_MUL; ASSUME `norm(z * cexp((L:complex->complex) z)) = &1`] THEN
    REWRITE_TAC[REAL_MUL_LID; GSYM CX_ADD; COMPLEX_NORM_CX] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs(&1 + x) = &1 + x`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    UNDISCH_TAC `&0 < a` THEN UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; ASSUME `norm(w - z:complex) = e`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM ACCEPT_TAC);;

(* Noshiro-Warschawski: Re g' > 0 on a convex open set makes g injective. *)

let SCH2_NW = prove
 (`!g s. convex s /\ open s /\ g holomorphic_on s /\
         (!z. z IN s ==> &0 < Re(complex_derivative g z))
         ==> !w z. w IN s /\ z IN s /\ g w = g z ==> w = z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`w:complex`; `z:complex`] THEN
  STRIP_TAC THEN ASM_CASES_TAC `w:complex = z` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(w - z = Cx(&0))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_SUB_0]; ALL_TAC] THEN
  ABBREV_TAC `d = w - z:complex` THEN
  SUBGOAL_THEN `!t. &0 <= t /\ t <= &1 ==> z + t % d IN (s:complex->bool)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `z + t % d = (&1 - t) % z + t % (w:complex)` SUBST1_TAC THENL
     [EXPAND_TAC "d" THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `convex(s:complex->bool)` THEN REWRITE_TAC[CONVEX_ALT] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t:real^1. lift(Re((g:complex->complex)(z + drop t % d) / d))`;
                 `\t:real^1 h:real^1. lift(Re((complex_derivative (g:complex->complex)
                                                  (z + drop t % d) * (drop h % d)) / d))`;
                 `vec 0:real^1`; `vec 1:real^1`] MVT_VERY_SIMPLE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DROP_VEC; REAL_POS] THEN
    X_GEN_TAC `t:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
    SUBGOAL_THEN `(\t:real^1. lift(Re((g:complex->complex)(z + drop t % d) / d))) =
                  (\v. lift(Re(v / d))) o (g:complex->complex) o (\t:real^1. z + drop t % d)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    SUBGOAL_THEN `(\h:real^1. lift(Re((complex_derivative (g:complex->complex)
                                       (z + drop t % d) * (drop h % d)) / d))) =
                  (\v. lift(Re(v / d))) o
                  ((\v. complex_derivative (g:complex->complex) (z + drop t % d) * v) o
                   (\h:real^1. drop h % d))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`\t:real^1. z:complex`; `\h:real^1. vec 0:complex`;
                       `\t:real^1. drop t % (d:complex)`; `\h:real^1. drop h % (d:complex)`;
                       `at (t:real^1)`]
          HAS_DERIVATIVE_ADD) THEN
        REWRITE_TAC[HAS_DERIVATIVE_CONST; VECTOR_ADD_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
        MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
        MATCH_MP_TAC LINEAR_VMUL_DROP THEN REWRITE_TAC[LINEAR_ID];
        REWRITE_TAC[GSYM has_complex_derivative] THEN
        REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE] THEN
        MATCH_MP_TAC HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT THEN
        EXISTS_TAC `s:complex->bool` THEN ASM_SIMP_TAC[]];
      MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
      REWRITE_TAC[linear; complex_div; COMPLEX_ADD_RDISTRIB; RE_ADD; LIFT_ADD;
                  COMPLEX_CMUL; GSYM COMPLEX_MUL_ASSOC; RE_MUL_CX; LIFT_CMUL]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^1` (CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o BETA_RULE))) THEN
  REWRITE_TAC[DROP_VEC; DROP_SUB; REAL_SUB_RZERO; VECTOR_MUL_LID; VECTOR_MUL_LZERO;
              VECTOR_ADD_RID] THEN
  SUBGOAL_THEN `z + d = w:complex` SUBST1_TAC THENL
   [EXPAND_TAC "d" THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `(g:complex->complex) w = g z`; VECTOR_SUB_REFL] THEN
  SUBGOAL_THEN `(complex_derivative (g:complex->complex) (z + drop t % d) * d) / d =
                complex_derivative g (z + drop t % d)` SUBST1_TAC THENL
   [UNDISCH_TAC `~(d = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD; ALL_TAC] THEN
  REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN
  UNDISCH_TAC `(t:real^1) IN interval[vec 0,vec 1]` THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < Re(complex_derivative (g:complex->complex) (z + drop t % d))` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `complex_derivative:(complex->complex)->complex->complex`))
          (concl th))) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `d:complex`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The isotopy z cexp(t L z), 0 <= t <= 1, on a thin annulus                 *)
(* around the unit circle: injective (Noshiro-Warschawski in log            *)
(* coordinates) and immersive; hence J z = z cexp(L z) extends to a         *)
(* diffeomorphism of the plane preserving the unit disc (isotopy extension). *)
(* ------------------------------------------------------------------------- *)

let SCH2_RE_STRIP_OPEN_CONVEX = prove
 (`!a b. open {w:complex | a < Re w /\ Re w < b} /\
         convex {w:complex | a < Re w /\ Re w < b}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{w:complex | a < Re w /\ Re w < b} = {w | Re w > a} INTER {w | Re w < b}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; real_gt]; ALL_TAC] THEN
  SIMP_TAC[OPEN_INTER; CONVEX_INTER; OPEN_HALFSPACE_RE_GT; OPEN_HALFSPACE_RE_LT;
           CONVEX_HALFSPACE_RE_GT; CONVEX_HALFSPACE_RE_LT]);;

let SCH2_LOGDER_MARGIN = prove
 (`!L r0. &0 < r0 /\ r0 < &1 /\ L holomorphic_on annulus r0 (inv r0) /\
          (!z. z IN annulus r0 (inv r0) ==> L(inv(cnj z)) = --cnj(L z)) /\
          (!z. z IN annulus r0 (&1) ==> norm(z * cexp(L z)) < &1) /\
          (!w z. w IN annulus r0 (&1) /\ z IN annulus r0 (&1) /\
                 w * cexp(L w) = z * cexp(L z) ==> w = z)
          ==> ?d. &0 < d /\ d < &1 - r0 /\
                  !z. abs(norm z - &1) < d
                      ==> z IN annulus r0 (inv r0) /\
                          &0 < Re(Cx(&1) + z * complex_derivative L z)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&1 < inv r0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INV_1_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `v = {z | z IN annulus r0 (inv r0) /\
                       (\z. Cx(&1) + z * complex_derivative (L:complex->complex) z) z IN
                       {w | Re w > &0}}` THEN
  SUBGOAL_THEN `open(v:complex->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    REWRITE_TAC[OPEN_ANNULUS; OPEN_HALFSPACE_RE_GT] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_IMP_CONTINUOUS_ON THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_ADD THEN REWRITE_TAC[HOLOMORPHIC_ON_CONST] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN REWRITE_TAC[HOLOMORPHIC_ON_ID; ETA_AX] THEN
    MATCH_MP_TAC HOLOMORPHIC_COMPLEX_DERIVATIVE THEN ASM_REWRITE_TAC[OPEN_ANNULUS];
    ALL_TAC] THEN
  SUBGOAL_THEN `sphere(Cx(&0),&1) SUBSET v` ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; SCH2_IN_C0; real_gt] THEN
    X_GEN_TAC `z:complex` THEN DISCH_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SCH2_LOGDER_POS THEN EXISTS_TAC `r0:real` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `v:complex->bool` SCH2_CIRCLE_MARGIN) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d ((&1 - r0) / &2)` THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:complex) IN v` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXPAND_TAC "v" THEN REWRITE_TAC[IN_ELIM_THM; real_gt]);;

(* Log coordinates: J_t o cexp = cexp o (\w. w + t L(cexp w)). *)

let SCH2_JT_LOG_INJ = prove
 (`!L r0 d t.
        &0 < r0 /\ r0 < &1 /\ L holomorphic_on annulus r0 (inv r0) /\
        &0 < d /\ d < &1 /\ &0 <= t /\ t <= &1 /\
        (!z. abs(norm z - &1) < d
             ==> z IN annulus r0 (inv r0) /\
                 &0 < Re(Cx(&1) + z * complex_derivative L z))
        ==> !w z. abs(norm w - &1) < d /\ abs(norm z - &1) < d /\
                  w * cexp(Cx t * L w) = z * cexp(Cx t * L z) ==> w = z`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "MARG")))))))) THEN
  ABBREV_TAC `S = {w:complex | log(&1 - d) < Re w /\ Re w < log(&1 + d)}` THEN
  SUBGOAL_THEN `open(S:complex->bool) /\ convex S` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[SCH2_RE_STRIP_OPEN_CONVEX]; ALL_TAC] THEN
  SUBGOAL_THEN `!w. w IN S ==> abs(norm(cexp w) - &1) < d` (LABEL_TAC "EXPS") THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM; NORM_CEXP] THEN
    X_GEN_TAC `w:complex` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&1 - d < exp(Re w) /\ exp(Re w) < &1 + d` MP_TAC THENL
     [CONJ_TAC THENL
       [SUBGOAL_THEN `&1 - d = exp(log(&1 - d))` SUBST1_TAC THENL
         [CONV_TAC SYM_CONV THEN MATCH_MP_TAC EXP_LOG THEN ASM_REAL_ARITH_TAC;
          ASM_REWRITE_TAC[REAL_EXP_MONO_LT]];
        SUBGOAL_THEN `&1 + d = exp(log(&1 + d))` SUBST1_TAC THENL
         [CONV_TAC SYM_CONV THEN MATCH_MP_TAC EXP_LOG THEN ASM_REAL_ARITH_TAC;
          ASM_REWRITE_TAC[REAL_EXP_MONO_LT]]];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. abs(norm z - &1) < d ==> ~(z = Cx(&0)) /\ clog z IN S`
  (LABEL_TAC "LOGS") THENL
   [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(z = Cx(&0))` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `abs(norm(z:complex) - &1) < d` THEN
      ASM_REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_SIMP_TAC[RE_CLOG] THEN
    SUBGOAL_THEN `&0 < norm(z:complex)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[COMPLEX_NORM_NZ]; ALL_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. w IN S ==> cexp w IN annulus r0 (inv r0) /\
                               &0 < Re(Cx(&1) + cexp w * complex_derivative L (cexp w))`
  (LABEL_TAC "EXPA") THENL
   [X_GEN_TAC `w:complex` THEN DISCH_TAC THEN USE_THEN "MARG" MATCH_MP_TAC THEN
    USE_THEN "EXPS" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Lt = \w:complex. w + Cx t * (L:complex->complex)(cexp w)` THEN
  SUBGOAL_THEN `!w. w IN S ==> ((Lt:complex->complex) has_complex_derivative
                   Cx(&1) + Cx t * (cexp w * complex_derivative L (cexp w))) (at w)`
  (LABEL_TAC "LTD") THENL
   [X_GEN_TAC `w:complex` THEN DISCH_TAC THEN EXPAND_TAC "Lt" THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_ID] THEN
    SUBGOAL_THEN `Cx t * (cexp w * complex_derivative (L:complex->complex) (cexp w)) =
                  Cx t * (complex_derivative L (cexp w) * cexp w)` SUBST1_TAC THENL
     [REWRITE_TAC[COMPLEX_MUL_AC]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_LMUL_AT THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM o_DEF] THEN
    MATCH_MP_TAC COMPLEX_DIFF_CHAIN_AT THEN REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_CEXP] THEN
    REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT THEN
    EXISTS_TAC `annulus r0 (inv r0):complex->bool` THEN ASM_REWRITE_TAC[OPEN_ANNULUS] THEN
    USE_THEN "EXPA" (fun th -> REWRITE_TAC[CONJUNCT1(MP (SPEC `w:complex` th)
      (ASSUME `(w:complex) IN S`))]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!w z. w IN S /\ z IN S /\ (Lt:complex->complex) w = Lt z ==> w = z`
  (LABEL_TAC "NWI") THENL
   [MATCH_MP_TAC SCH2_NW THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[HOLOMORPHIC_ON_OPEN] THEN X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
      EXISTS_TAC `Cx(&1) + Cx t * (cexp w * complex_derivative (L:complex->complex) (cexp w))` THEN
      USE_THEN "LTD" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
    USE_THEN "LTD" (fun th -> REWRITE_TAC[MATCH_MP HAS_COMPLEX_DERIVATIVE_DERIVATIVE
      (MP (SPEC `w:complex` th) (ASSUME `(w:complex) IN S`))]) THEN
    USE_THEN "EXPA" (MP_TAC o CONJUNCT2 o C MP (ASSUME `(w:complex) IN S`) o SPEC `w:complex`) THEN
    REWRITE_TAC[RE_ADD; RE_CX; RE_MUL_CX] THEN
    ABBREV_TAC `Y = Re(cexp w * complex_derivative (L:complex->complex) (cexp w))` THEN
    DISCH_TAC THEN ASM_CASES_TAC `t = &0` THENL
     [ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < t * (&1 + Y)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `t <= &1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`w:complex`; `z:complex`] THEN STRIP_TAC THEN
  USE_THEN "LOGS" (STRIP_ASSUME_TAC o C MP (ASSUME `abs(norm(w:complex) - &1) < d`) o
                   SPEC `w:complex`) THEN
  USE_THEN "LOGS" (STRIP_ASSUME_TAC o C MP (ASSUME `abs(norm(z:complex) - &1) < d`) o
                   SPEC `z:complex`) THEN
  SUBGOAL_THEN `cexp((Lt:complex->complex)(clog w)) = cexp(Lt(clog z))` MP_TAC THENL
   [EXPAND_TAC "Lt" THEN REWRITE_TAC[CEXP_ADD] THEN ASM_SIMP_TAC[CEXP_CLOG]; ALL_TAC] THEN
  REWRITE_TAC[CEXP_EQ] THEN DISCH_THEN(X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `z3 = clog z + Cx(&2 * n * pi) * ii` THEN
  SUBGOAL_THEN `cexp z3 = z` ASSUME_TAC THENL
   [EXPAND_TAC "z3" THEN REWRITE_TAC[CEXP_ADD] THEN ASM_SIMP_TAC[CEXP_INTEGER_2PI; CEXP_CLOG] THEN
    REWRITE_TAC[COMPLEX_MUL_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z3:complex) IN S` ASSUME_TAC THENL
   [UNDISCH_TAC `clog z IN S` THEN EXPAND_TAC "S" THEN EXPAND_TAC "z3" THEN
    REWRITE_TAC[IN_ELIM_THM; RE_ADD; RE_MUL_II; IM_CX; REAL_NEG_0; REAL_ADD_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `clog w = z3` ASSUME_TAC THENL
   [USE_THEN "NWI" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "Lt" THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(Lt:complex->complex)(clog w) = Lt(clog z) + Cx(&2 * n * pi) * ii` THEN
    EXPAND_TAC "Lt" THEN ASM_SIMP_TAC[CEXP_CLOG] THEN DISCH_THEN SUBST1_TAC THEN
    EXPAND_TAC "z3" THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  MP_TAC(SPEC `w:complex` CEXP_CLOG) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ACCEPT_TAC o SYM));;

let SCH2_JT_SMOOTH = prove
 (`!L:complex->complex U.
        open U /\ L holomorphic_on U
        ==> smooth_family U (\t z. z * cexp(Cx t * L z))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smooth_family] THEN
  SUBGOAL_THEN `open((:real^1) PCROSS (U:complex->bool))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on ((:real^1) PCROSS (U:complex->bool))
                  (sndcart:real^(1,2)finite_sum->complex)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:real^1) PCROSS (U:complex->bool)`; `\z:real^(1,2)finite_sum. z`]
      SMOOTH_MAP_ON_SNDCART_OPEN) THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; o_DEF; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on ((:real^1) PCROSS (U:complex->bool))
                  (\p:real^(1,2)finite_sum. Cx(drop(fstcart p)))` ASSUME_TAC THENL
   [SUBGOAL_THEN `(\p:real^(1,2)finite_sum. Cx(drop(fstcart p))) =
                  (\x. drop x % Cx(&1)) o (fstcart:real^(1,2)finite_sum->real^1)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; COMPLEX_CMUL; COMPLEX_MUL_RID]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_SIMP_TAC[SCHI_FSTCART_SMOOTH] THEN
    MATCH_MP_TAC LINEAR_VMUL_DROP THEN REWRITE_TAC[LINEAR_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on ((:real^1) PCROSS (U:complex->bool))
                  (\p:real^(1,2)finite_sum. (L:complex->complex)(sndcart p))` ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `U:complex->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; SNDCART_PASTECART] THEN
      SIMP_TAC[];
      MATCH_MP_TAC BEL_HOLOMORPHIC_SMOOTH THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on ((:real^1) PCROSS (U:complex->bool))
                  (\p:real^(1,2)finite_sum. cexp(Cx(drop(fstcart p)) * (L:complex->complex)(sndcart p)))`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:complex)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`(:real^1) PCROSS (U:complex->bool)`; `( * ):complex->complex->complex`;
                     `\p:real^(1,2)finite_sum. Cx(drop(fstcart p))`;
                     `\p:real^(1,2)finite_sum. (L:complex->complex)(sndcart p)`]
        SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
      ASM_REWRITE_TAC[BILINEAR_COMPLEX_MUL];
      MATCH_MP_TAC BEL_HOLOMORPHIC_SMOOTH THEN REWRITE_TAC[OPEN_UNIV; HOLOMORPHIC_ON_CEXP]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`(:real^1) PCROSS (U:complex->bool)`; `( * ):complex->complex->complex`;
                 `sndcart:real^(1,2)finite_sum->complex`;
                 `\p:real^(1,2)finite_sum. cexp(Cx(drop(fstcart p)) * (L:complex->complex)(sndcart p))`]
    SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
  ASM_REWRITE_TAC[BILINEAR_COMPLEX_MUL]);;

let SCH2_JT_IMMERSE = prove
 (`!L:complex->complex U t z h.
        open U /\ L holomorphic_on U /\ z IN U /\ &0 <= t /\ t <= &1 /\
        &0 < Re(Cx(&1) + z * complex_derivative L z) /\
        frechet_derivative (\z. z * cexp(Cx t * L z)) (at z) h = vec 0
        ==> h = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(L:complex->complex) complex_differentiable at z` ASSUME_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT THEN
    EXISTS_TAC `U:complex->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `t:real` o MATCH_MP SCH2_JT_DERIV) THEN
  REWRITE_TAC[has_complex_derivative] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  DISCH_THEN(fun th -> UNDISCH_TAC
    `frechet_derivative (\z. z * cexp(Cx t * (L:complex->complex) z)) (at z) h = vec 0` THEN
    REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_ENTIRE; CEXP_NZ] THEN
  MATCH_MP_TAC(TAUT `~p ==> p \/ q ==> q`) THEN
  DISCH_THEN(MP_TAC o AP_TERM `Re`) THEN
  REWRITE_TAC[RE_ADD; RE_CX; RE_MUL_CX; GSYM COMPLEX_MUL_ASSOC] THEN
  UNDISCH_TAC `&0 < Re(Cx(&1) + z * complex_derivative (L:complex->complex) z)` THEN
  REWRITE_TAC[RE_ADD; RE_CX] THEN
  ABBREV_TAC `Y = Re(z * complex_derivative (L:complex->complex) z)` THEN
  DISCH_TAC THEN ASM_CASES_TAC `t = &0` THENL
   [ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t * (&1 + Y)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `t <= &1` THEN REAL_ARITH_TAC);;

(* The collar extension: J extends from a closed thin annulus to a          *)
(* diffeomorphism of the plane mapping the unit disc onto itself.           *)

let SCH2_COLLAR_EXTEND = prove
 (`!L r0. &0 < r0 /\ r0 < &1 /\ L holomorphic_on annulus r0 (inv r0) /\
          (!z. z IN annulus r0 (inv r0) ==> L(inv(cnj z)) = --cnj(L z)) /\
          (!z. z IN annulus r0 (&1) ==> norm(z * cexp(L z)) < &1) /\
          (!w z. w IN annulus r0 (&1) /\ z IN annulus r0 (&1) /\
                 w * cexp(L w) = z * cexp(L z) ==> w = z)
          ==> ?d E E'. &0 < d /\ d < &1 - r0 /\
                       diffeomorphism_on (:complex) (:complex) E E' /\
                       (!z. abs(norm z - &1) <= d ==> E z = z * cexp(L z)) /\
                       IMAGE E (ball(Cx(&0),&1)) = ball(Cx(&0),&1) /\
                       IMAGE E (cball(Cx(&0),&1)) = cball(Cx(&0),&1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `d0:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "MARG"))) o MATCH_MP SCH2_LOGDER_MARGIN) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SCH2_J_ONTO) THEN DISCH_THEN(LABEL_TAC "ONTO") THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  SUBGOAL_THEN `d0 < &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `U = annulus (&1 - d0) (&1 + d0):complex->bool` THEN
  SUBGOAL_THEN `!z:complex. z IN U <=> abs(norm z - &1) < d0` (LABEL_TAC "INU") THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `open(U:complex->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[OPEN_ANNULUS]; ALL_TAC] THEN
  SUBGOAL_THEN `(U:complex->bool) SUBSET annulus r0 (inv r0)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN USE_THEN "INU" (fun th -> REWRITE_TAC[th]) THEN
    X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    USE_THEN "MARG" (fun th -> REWRITE_TAC[CONJUNCT1(MP (SPEC `z:complex` th)
      (ASSUME `abs(norm(z:complex) - &1) < d0`))]);
    ALL_TAC] THEN
  ABBREV_TAC `K = cball(Cx(&0),&1 + d0 / &2) DIFF ball(Cx(&0),&1 - d0 / &2)` THEN
  SUBGOAL_THEN `!z:complex. z IN K <=> abs(norm z - &1) <= d0 / &2` (LABEL_TAC "INK") THENL
   [EXPAND_TAC "K" THEN REWRITE_TAC[IN_DIFF; SCH2_IN_C0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `compact(K:complex->bool) /\ K SUBSET U` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "K" THEN MATCH_MP_TAC COMPACT_DIFF THEN
      REWRITE_TAC[COMPACT_CBALL; OPEN_BALL];
      REWRITE_TAC[SUBSET] THEN USE_THEN "INK" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "INU" (fun th -> REWRITE_TAC[th]) THEN
      UNDISCH_TAC `&0 < d0` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t z. z * cexp(Cx t * (L:complex->complex) z)`; `U:complex->bool`;
                 `K:complex->bool`; `(:complex)`] SCHI_ISOTOPY_EXTENSION_01) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SCH2_JT_SMOOTH THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN
      EXISTS_TAC `annulus r0 (inv r0):complex->bool` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[] THEN USE_THEN "INU" (fun th -> REWRITE_TAC[th]) THEN
      REPEAT STRIP_TAC THEN
      MP_TAC(SPECL [`L:complex->complex`; `r0:real`; `d0:real`; `t:real`] SCH2_JT_LOG_INJ) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN USE_THEN "MARG" ACCEPT_TAC;
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[] THEN USE_THEN "INU" (fun th -> REWRITE_TAC[th]) THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SCH2_JT_IMMERSE THEN
      MAP_EVERY EXISTS_TAC [`L:complex->complex`; `annulus r0 (inv r0):complex->bool`;
                            `t:real`; `x:complex`] THEN
      ASM_REWRITE_TAC[OPEN_ANNULUS] THEN
      USE_THEN "MARG" (fun th -> REWRITE_TAC[MP (SPEC `x:complex` th)
        (ASSUME `abs(norm(x:complex) - &1) < d0`)]);
      REWRITE_TAC[COMPLEX_MUL_LZERO; CEXP_0; COMPLEX_MUL_RID]];
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_MUL_LID] THEN
  DISCH_THEN(X_CHOOSE_THEN `E:complex->complex` (X_CHOOSE_THEN `E':complex->complex`
    (X_CHOOSE_THEN `L1:complex->bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `homeomorphism ((:complex),(:complex)) (E:complex->complex,E')` ASSUME_TAC
  THENL
   [UNDISCH_TAC `diffeomorphism_on (:complex) (:complex) (E:complex->complex) E'` THEN
    REWRITE_TAC[diffeomorphism_on; homeomorphism; IN_UNIV] THEN
    MESON_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (E:complex->complex) (sphere(Cx(&0),&1)) = sphere(Cx(&0),&1)`
  ASSUME_TAC THENL
   [USE_THEN "ONTO" (fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THEN
    MATCH_MP_TAC IMAGE_EQ THEN X_GEN_TAC `z:complex` THEN
    REWRITE_TAC[SCH2_IN_C0] THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN USE_THEN "INK" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_NUM] THEN UNDISCH_TAC `&0 < d0` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (E:complex->complex) (ball(Cx(&0),&1)) = ball(Cx(&0),&1)` ASSUME_TAC
  THENL
   [MP_TAC(ISPECL [`E:complex->complex`; `E':complex->complex`; `sphere(Cx(&0),&1)`]
      SCH_INSIDE_HOMEOMORPHISM) THEN
    ASM_REWRITE_TAC[INSIDE_SPHERE] THEN DISCH_THEN(ACCEPT_TAC o SYM);
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`d0 / &2`; `E:complex->complex`; `E':complex->complex`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `z:complex` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    USE_THEN "INK" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM BALL_UNION_SPHERE; IMAGE_UNION] THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Beltrami straightening.  For an orientation-preserving                    *)
(* diffeomorphism f of an open set V (|f_zbar| < |f_z|) and a compact B in   *)
(* V there is a diffeomorphism w of the plane (bel_fsol of the cut-off       *)
(* coefficient -f_zbar / cnj f_z o f^-1) with w o f holomorphic on any open  *)
(* W inside B.                                                               *)
(* ------------------------------------------------------------------------- *)

let SCH2_WIRT_CHAIN = prove
 (`!w f:complex->complex z.
        f differentiable at z /\ w differentiable at (f z)
        ==> wirtinger_dbar (w o f) z =
            wirtinger_dz w (f z) * wirtinger_dbar f z +
            wirtinger_dbar w (f z) * cnj(wirtinger_dz f z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FRECHET_DERIVATIVE_WORKS] THEN STRIP_TAC THEN
  SUBGOAL_THEN `((w:complex->complex) o (f:complex->complex) has_derivative
                 frechet_derivative w (at (f z)) o frechet_derivative f (at z)) (at z)`
  ASSUME_TAC THENL [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[WIRTINGER_DBAR_FRECHET] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  REWRITE_TAC[o_THM] THEN
  REWRITE_TAC[MATCH_MP FRECHET_WIRTINGER (ASSUME
    `((w:complex->complex) has_derivative frechet_derivative w (at (f(z:complex))))
     (at (f z))`)] THEN
  REWRITE_TAC[MATCH_MP FRECHET_WIRTINGER (ASSUME
    `((f:complex->complex) has_derivative frechet_derivative f (at z)) (at z)`)] THEN
  REWRITE_TAC[CNJ_ADD; CNJ_MUL; CNJ_II; CNJ_CX; CNJ_NEG] THEN
  MP_TAC COMPLEX_POW_II_2 THEN CONV_TAC COMPLEX_RING);;

let SCH2_CMUL_SMOOTH = prove
 (`!s c (g:real^M->complex).
        open s /\ smooth_map_on s g ==> smooth_map_on s (\x. c * g x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `( * ):complex->complex->complex`;
                 `\x:real^M. c:complex`; `g:real^M->complex`] SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
  ASM_REWRITE_TAC[BILINEAR_COMPLEX_MUL; SMOOTH_MAP_ON_CONST]);;

let SCH2_MUL_SMOOTH = prove
 (`!s (f:real^M->complex) g.
        open s /\ smooth_map_on s f /\ smooth_map_on s g
        ==> smooth_map_on s (\x. f x * g x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `( * ):complex->complex->complex`;
                 `f:real^M->complex`; `g:real^M->complex`] SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
  ASM_REWRITE_TAC[BILINEAR_COMPLEX_MUL]);;

let SCH2_CNJ_SMOOTH = prove
 (`!s (g:real^M->complex). open s /\ smooth_map_on s g ==> smooth_map_on s (\x. cnj(g x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. cnj((g:real^M->complex) x)) = cnj o g` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[LINEAR_CNJ]);;

let SCH2_INV_SMOOTH = prove
 (`!s (g:real^M->complex).
        open s /\ smooth_map_on s g /\ (!x. x IN s ==> ~(g x = Cx(&0)))
        ==> smooth_map_on s (\x. inv(g x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. inv((g:real^M->complex) x)) = (\z. inv z) o g` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `{z:complex | ~(z = Cx(&0))}` THEN
  ASM_REWRITE_TAC[BEL_OPEN_NONZERO_C] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC BEL_HOLOMORPHIC_SMOOTH THEN REWRITE_TAC[BEL_OPEN_NONZERO_C] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_INV THEN REWRITE_TAC[HOLOMORPHIC_ON_ID; IN_ELIM_THM]]);;

let SCH2_WIRT_SMOOTH_ON = prove
 (`!s f:complex->complex.
        open s /\ smooth_map_on s f
        ==> smooth_map_on s (wirtinger_dbar f) /\ smooth_map_on s (wirtinger_dz f)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[BEL_WIRTINGER_PD] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN MATCH_MP_TAC SCH2_CMUL_SMOOTH THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; ETA_AX]);;

(* The Beltrami coefficient of f^-1, smooth on the image. *)

let SCH2_NU_SMOOTH = prove
 (`!f f' V.
        diffeomorphism_on V (IMAGE f V) f f' /\
        (!z. z IN V ==> ~(wirtinger_dz f z = Cx(&0)))
        ==> smooth_map_on (IMAGE f V)
              (\y. --(wirtinger_dbar f (f' y) / cnj(wirtinger_dz f (f' y))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on V (wirtinger_dbar (f:complex->complex)) /\
                smooth_map_on V (wirtinger_dz (f:complex->complex))` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC SCH2_WIRT_SMOOTH_ON THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!h:complex->complex. smooth_map_on V h
                ==> smooth_map_on (IMAGE f V) (h o (f':complex->complex))` (LABEL_TAC "COMP")
  THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `V:complex->bool` THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (IMAGE f V) (\y. wirtinger_dbar f ((f':complex->complex) y)) /\
                smooth_map_on (IMAGE f V) (\y. wirtinger_dz f ((f':complex->complex) y))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
    USE_THEN "COMP" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_NEG_OPEN THEN ASM_REWRITE_TAC[complex_div] THEN
  MATCH_MP_TAC SCH2_MUL_SMOOTH THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SCH2_INV_SMOOTH THEN ASM_REWRITE_TAC[CNJ_EQ_0] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SCH2_CNJ_SMOOTH THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[]]);;

let SCH2_BELTRAMI_STRAIGHTEN = prove
 (`!f f' V W B.
     diffeomorphism_on V (IMAGE f V) f f' /\
     (!z. z IN V ==> norm(wirtinger_dbar f z) < norm(wirtinger_dz f z)) /\
     open W /\ W SUBSET B /\ compact B /\ B SUBSET V
     ==> ?w w'. diffeomorphism_on (:complex) (:complex) w w' /\
                (\z. w(f z)) holomorphic_on W`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z. z IN V ==> ~(wirtinger_dz (f:complex->complex) z = Cx(&0))`
  (LABEL_TAC "DZ") THENL
   [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:complex` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `wirtinger_dbar:(complex->complex)->complex->complex`)) (concl th))) THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_0] THEN REWRITE_TAC[NORM_POS_LE; REAL_NOT_LT];
    ALL_TAC] THEN
  MP_TAC(SPECL [`f:complex->complex`; `f':complex->complex`; `V:complex->bool`]
    SCH2_NU_SMOOTH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN USE_THEN "DZ" ACCEPT_TAC; DISCH_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[diffeomorphism_on] o check (fun th ->
    can (find_term ((=) `diffeomorphism_on:(complex->bool)->(complex->bool)->(complex->complex)->(complex->complex)->bool`)) (concl th))) THEN
  ABBREV_TAC `Tim = IMAGE (f:complex->complex) V` THEN
  ABBREV_TAC `nu = \y. --(wirtinger_dbar f ((f':complex->complex) y) /
                          cnj(wirtinger_dz (f:complex->complex) (f' y)))` THEN
  SUBGOAL_THEN `!y. y IN Tim ==> norm((nu:complex->complex) y) < &1` (LABEL_TAC "NUB") THENL
   [X_GEN_TAC `y:complex` THEN DISCH_TAC THEN EXPAND_TAC "nu" THEN
    REWRITE_TAC[NORM_NEG; COMPLEX_NORM_DIV; COMPLEX_NORM_CNJ] THEN
    SUBGOAL_THEN `(f':complex->complex) y IN V` ASSUME_TAC THENL
     [UNDISCH_TAC `IMAGE (f':complex->complex) Tim = V` THEN
      UNDISCH_TAC `(y:complex) IN Tim` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < norm(wirtinger_dz (f:complex->complex) ((f':complex->complex) y))`
    ASSUME_TAC THENL
     [REWRITE_TAC[COMPLEX_NORM_NZ] THEN USE_THEN "DZ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LID] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `wirtinger_dbar:(complex->complex)->complex->complex`)) (concl th) &&
      is_imp(snd(strip_forall(concl th))) &&
      is_binary "real_lt" (rand(snd(strip_forall(concl th)))))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `K = IMAGE (f:complex->complex) B` THEN
  SUBGOAL_THEN `compact(K:complex->bool) /\ K SUBSET Tim` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN EXPAND_TAC "Tim" THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `V:complex->bool` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
      MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:complex->bool`; `Tim:complex->bool`] GRGE_EUCLID_CUTOFF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:complex->real` (X_CHOOSE_THEN `L1:complex->bool`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `mu = \y. if y IN Tim then Cx((psi:complex->real) y) * (nu:complex->complex) y
                       else Cx(&0)` THEN
  (* Smoothness of mu. *)
  SUBGOAL_THEN `smooth_map_on (:complex) (\y. Cx((psi:complex->real) y))` ASSUME_TAC THENL
   [SUBGOAL_THEN `(\y. Cx((psi:complex->real) y)) =
                  (\x:real^1. drop x % Cx(&1)) o (\y. lift(psi y))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP; COMPLEX_CMUL; COMPLEX_MUL_RID]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[OPEN_UNIV] THEN
    MATCH_MP_TAC LINEAR_VMUL_DROP THEN REWRITE_TAC[LINEAR_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:complex) (mu:complex->complex)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    X_GEN_TAC `y:complex` THEN ASM_CASES_TAC `(y:complex) IN Tim` THENL
     [EXISTS_TAC `Tim:complex->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
      EXISTS_TAC `\y. Cx((psi:complex->real) y) * (nu:complex->complex) y` THEN
      CONJ_TAC THENL
       [EXPAND_TAC "mu" THEN SIMP_TAC[];
        MATCH_MP_TAC SCH2_MUL_SMOOTH THEN ASM_REWRITE_TAC[ETA_AX] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:complex)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV]];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((y:complex) IN L1)` ASSUME_TAC THENL
     [UNDISCH_TAC `(L1:complex->bool) SUBSET Tim` THEN
      UNDISCH_TAC `~((y:complex) IN Tim)` THEN SET_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `(:complex) DIFF L1` THEN ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_DIFF THEN ASM_SIMP_TAC[OPEN_UNIV; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `\y:complex. Cx(&0)` THEN
    REWRITE_TAC[SMOOTH_MAP_ON_CONST; IN_DIFF; IN_UNIV] THEN
    X_GEN_TAC `u:complex` THEN DISCH_TAC THEN EXPAND_TAC "mu" THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(psi:complex->real) u = &0` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `L1:complex->bool`)) (concl th) &&
        can (find_term ((=) `&0`)) (concl th))) THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[COMPLEX_MUL_LZERO]];
    ALL_TAC] THEN
  (* Support and bound. *)
  SUBGOAL_THEN `?R. bel_supp R (mu:complex->complex)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `L1:complex->bool` COMPACT_IMP_BOUNDED) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[BOUNDED_POS] THEN DISCH_THEN(X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `b:real` THEN REWRITE_TAC[bel_supp] THEN X_GEN_TAC `u:complex` THEN
    DISCH_TAC THEN EXPAND_TAC "mu" THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(psi:complex->real) u = &0` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `L1:complex->bool`)) (concl th) &&
        can (find_term ((=) `&0`)) (concl th))) THEN
      DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `u:complex` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `b:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[COMPLEX_MUL_LZERO]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?k. &0 <= k /\ k < &1 /\ !y. y IN L1 ==> norm((nu:complex->complex) y) <= k`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `L1:complex->bool = {}` THENL
     [EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`\y. norm((nu:complex->complex) y)`; `L1:complex->bool`]
      CONTINUOUS_ATTAINS_SUP) THEN
    ASM_REWRITE_TAC[o_DEF] THEN ANTS_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `Tim:complex->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y0:complex` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `norm((nu:complex->complex) y0)` THEN
    ASM_REWRITE_TAC[NORM_POS_LE] THEN USE_THEN "NUB" MATCH_MP_TAC THEN
    UNDISCH_TAC `(L1:complex->bool) SUBSET Tim` THEN
    UNDISCH_TAC `(y0:complex) IN L1` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. norm((mu:complex->complex) y) <= k` ASSUME_TAC THENL
   [X_GEN_TAC `u:complex` THEN EXPAND_TAC "mu" THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_0] THEN
    ASM_CASES_TAC `(u:complex) IN L1` THENL
     [REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm((nu:complex->complex) u)` THEN
      CONJ_TAC THENL
       [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
        ASM_SIMP_TAC[REAL_ARITH `&0 <= x /\ x <= &1 ==> abs x <= &1`];
        ASM_SIMP_TAC[]];
      SUBGOAL_THEN `(psi:complex->real) u = &0` SUBST1_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `L1:complex->bool`)) (concl th) &&
          can (find_term ((=) `&0`)) (concl th) &&
          not(can (find_term ((=) `nu:complex->complex`)) (concl th)))) THEN
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_NORM_0]]];
    ALL_TAC] THEN
  (* The solution w. *)
  MP_TAC(ISPECL [`R:real`; `mu:complex->complex`; `k:real`] BEL_FSOL_PROPS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "BELT")))) THEN
  MP_TAC(ISPECL [`R:real`; `mu:complex->complex`; `k:real`] BEL_FSOL_HOMEO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `g:complex->complex`) THEN
  MP_TAC(ISPECL [`R:real`; `mu:complex->complex`; `k:real`; `g:complex->complex`]
    BEL_FSOL_INV_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`bel_fsol (mu:complex->complex)`; `g:complex->complex`] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `homeomorphism ((:complex),(:complex)) (bel_fsol (mu:complex->complex),g)` THEN
    REWRITE_TAC[homeomorphism; diffeomorphism_on; OPEN_UNIV] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[HOLOMORPHIC_ON_OPEN] THEN X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM complex_differentiable] THEN
  SUBGOAL_THEN `(z:complex) IN V` ASSUME_TAC THENL
   [UNDISCH_TAC `(W:complex->bool) SUBSET B` THEN UNDISCH_TAC `(B:complex->bool) SUBSET V` THEN
    UNDISCH_TAC `(z:complex) IN W` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:complex->complex) differentiable at z` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `V:complex->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `bel_fsol (mu:complex->complex) differentiable at ((f:complex->complex) z)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:complex)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM o_DEF] THEN
  MP_TAC(ISPECL [`bel_fsol (mu:complex->complex) o (f:complex->complex)`; `z:complex`]
    WIRTINGER_DBAR_EQ_ZERO) THEN
  ANTS_TAC THENL [MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[MATCH_MP SCH2_WIRT_CHAIN (CONJ
    (ASSUME `(f:complex->complex) differentiable at z`)
    (ASSUME `bel_fsol (mu:complex->complex) differentiable at ((f:complex->complex) z)`))] THEN
  USE_THEN "BELT" (fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `(mu:complex->complex)((f:complex->complex) z) =
                --(wirtinger_dbar f z / cnj(wirtinger_dz f z))` SUBST1_TAC THENL
   [EXPAND_TAC "mu" THEN
    SUBGOAL_THEN `(f:complex->complex) z IN Tim /\ f z IN K` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "Tim" THEN EXPAND_TAC "K" THEN CONJ_TAC THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(W:complex->bool) SUBSET B` THEN UNDISCH_TAC `(z:complex) IN W` THEN
      SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(psi:complex->real) ((f:complex->complex) z) = &1` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `K:complex->bool`)) (concl th) &&
        can (find_term ((=) `&1`)) (concl th))) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "nu" THEN REWRITE_TAC[COMPLEX_MUL_LID] THEN
    SUBGOAL_THEN `(f':complex->complex) ((f:complex->complex) z) = z` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `f':complex->complex`)) (concl th) &&
        is_imp(snd(strip_forall(concl th))) &&
        can (find_term ((=) `V:complex->bool`)) (concl th) &&
        is_eq(rand(snd(strip_forall(concl th)))))) THEN ASM_REWRITE_TAC[];
      REFL_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(cnj(wirtinger_dz (f:complex->complex) z) = Cx(&0))` MP_TAC THENL
   [REWRITE_TAC[CNJ_EQ_0] THEN USE_THEN "DZ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    CONV_TAC COMPLEX_FIELD]);;

(* ------------------------------------------------------------------------- *)
(* Planar topology of necks.  Sides of the circles of a                      *)
(* continuous injective map of an annulus (the proof of SCH2_SIDES with     *)
(* invariance of domain), rescaling, and nesting of the image circles.      *)
(* ------------------------------------------------------------------------- *)

let SCH2_SIDES_CONT = prove
 (`!(Fa:complex->complex) r1 r2.
        &0 < r1 /\ r1 < &1 /\ &1 < r2 /\ Fa continuous_on annulus r1 r2 /\
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
   [MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN ASM_REWRITE_TAC[OPEN_ANNULUS] THEN
    USE_THEN "INJ" ACCEPT_TAC;
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

let SCH2_UNBOUNDED_IN_OUTSIDE = prove
 (`!s c:real^N->bool. connected c /\ ~bounded c /\ c INTER s = {} ==> c SUBSET outside s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; outside; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(c:real^N->bool) SUBSET (:real^N) DIFF s` ASSUME_TAC THENL
   [UNDISCH_TAC `(c:real^N->bool) INTER s = {}` THEN SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `(c:real^N->bool) SUBSET (:real^N) DIFF s` THEN
    UNDISCH_TAC `(x:real^N) IN c` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^N->bool) SUBSET connected_component ((:real^N) DIFF s) x` MP_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN DISCH_TAC THEN
  UNDISCH_TAC `~bounded(c:real^N->bool)` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC BOUNDED_SUBSET THEN
  EXISTS_TAC `connected_component ((:real^N) DIFF s) (x:real^N)` THEN ASM_REWRITE_TAC[]);;

(* Rescaling a circle of radius r to the unit circle. *)

let SCH2_SCALE_SPHERE = prove
 (`!r. &0 < r ==> IMAGE (\z. Cx r * z) (sphere(Cx(&0),&1)) = sphere(Cx(&0),r)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; SCH2_IN_C0] THEN
  X_GEN_TAC `w:complex` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `z:complex` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC THEN EXISTS_TAC `Cx(inv r) * w` THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; COMPLEX_MUL_ASSOC; GSYM CX_MUL] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; COMPLEX_MUL_LID; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`; REAL_MUL_LINV; REAL_LT_IMP_NZ]]);;

let SCH2_SIDES_RADIUS = prove
 (`!(f:complex->complex) a b r.
        &0 < a /\ a < r /\ r < b /\ f continuous_on annulus a b /\
        (!w z. w IN annulus a b /\ z IN annulus a b /\ f w = f z ==> w = z)
        ==> ((!z. z IN annulus a r ==> f z IN inside(IMAGE f (sphere(Cx(&0),r)))) /\
             (!z. z IN annulus r b ==> f z IN outside(IMAGE f (sphere(Cx(&0),r))))) \/
            ((!z. z IN annulus a r ==> f z IN outside(IMAGE f (sphere(Cx(&0),r)))) /\
             (!z. z IN annulus r b ==> f z IN inside(IMAGE f (sphere(Cx(&0),r)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`\z. (f:complex->complex)(Cx r * z)`; `a / r`; `b / r`] SCH2_SIDES_CONT) THEN
  SUBGOAL_THEN `!z. z IN annulus (a / r) (b / r) <=> Cx r * z IN annulus a b`
  (LABEL_TAC "SC") THENL
   [GEN_TAC THEN REWRITE_TAC[annulus; IN_ELIM_THM; COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`; REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_DIV];
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
        REWRITE_TAC[linear; COMPLEX_CMUL] THEN CONV_TAC COMPLEX_RING;
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `annulus a b:complex->bool` THEN
        ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
        USE_THEN "SC" (fun th -> REWRITE_TAC[GSYM th])];
      MAP_EVERY X_GEN_TAC [`w:complex`; `z:complex`] THEN
      USE_THEN "SC" (fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN
      SUBGOAL_THEN `Cx r * w = Cx r * z` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[COMPLEX_EQ_MUL_LCANCEL; CX_INJ] THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (\z. (f:complex->complex)(Cx r * z)) (sphere(Cx(&0),&1)) =
                IMAGE f (sphere(Cx(&0),r))` SUBST1_TAC THENL
   [GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
      [GSYM(MATCH_MP SCH2_SCALE_SPHERE (ASSUME `&0 < r`))] THEN
    REWRITE_TAC[GSYM IMAGE_o; o_DEF];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!z. z IN annulus a r ==> Cx(inv r) * z IN annulus (a / r) (&1) /\
                                       (f:complex->complex) z = f(Cx r * (Cx(inv r) * z))) /\
                (!z. z IN annulus r b ==> Cx(inv r) * z IN annulus (&1) (b / r) /\
                                       (f:complex->complex) z = f(Cx r * (Cx(inv r) * z)))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[COMPLEX_MUL_ASSOC; GSYM CX_MUL] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; COMPLEX_MUL_LID] THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN
    SUBGOAL_THEN `!z. norm(Cx(inv r) * z) = norm z / r` (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_ABS_INV] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`] THEN
      REWRITE_TAC[real_div; REAL_MUL_SYM];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV2_EQ; REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_MUL_LID] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THENL [DISJ1_TAC; DISJ2_TAC] THEN CONJ_TAC THEN X_GEN_TAC `z:complex` THEN
  DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IMP_CONJ]) THEN ASM_MESON_TAC[]);;

(* Image curves of a neck: compactness, and the outside of the outer circle  *)
(* is outside the inner one.                                                 *)

let SCH2_NECK_CURVE_FACTS = prove
 (`!(f:complex->complex) a b r.
        &0 < a /\ a < r /\ r < b /\ f continuous_on annulus a b
        ==> compact(IMAGE f (sphere(Cx(&0),r))) /\
            closed(IMAGE f (sphere(Cx(&0),r))) /\
            bounded(IMAGE f (sphere(Cx(&0),r))) /\
            ~(IMAGE f (sphere(Cx(&0),r)) = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact(IMAGE (f:complex->complex) (sphere(Cx(&0),r)))` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN REWRITE_TAC[COMPACT_SPHERE] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `annulus a b:complex->bool` THEN
    ASM_REWRITE_TAC[SUBSET; SCH2_IN_C0; annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED; COMPACT_IMP_BOUNDED; IMAGE_EQ_EMPTY] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `Cx r` THEN
  REWRITE_TAC[SCH2_IN_C0; COMPLEX_NORM_CX] THEN ASM_REAL_ARITH_TAC);;

let SCH2_NECK_SIDES = prove
 (`!(f:complex->complex) a b s.
        &0 < a /\ a < s /\ s < &1 /\ &1 < b /\ f continuous_on annulus a b /\
        (!w z. w IN annulus a b /\ z IN annulus a b /\ f w = f z ==> w = z) /\
        (!z. z IN annulus a (&1) ==> f z IN inside(IMAGE f (sphere(Cx(&0),&1))))
        ==> (!z. z IN annulus (&1) b ==> f z IN outside(IMAGE f (sphere(Cx(&0),&1)))) /\
            outside(IMAGE f (sphere(Cx(&0),&1))) SUBSET outside(IMAGE f (sphere(Cx(&0),s))) /\
            (!z. z IN annulus a s ==> f z IN inside(IMAGE f (sphere(Cx(&0),s)))) /\
            (!z. z IN annulus s b ==> f z IN outside(IMAGE f (sphere(Cx(&0),s))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "INJ") (LABEL_TAC "IN1"))))))) THEN
  MP_TAC(ISPECL [`IMAGE (f:complex->complex) (sphere(Cx(&0),&1))`] INSIDE_INTER_OUTSIDE) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`IMAGE (f:complex->complex) (sphere(Cx(&0),s))`] INSIDE_INTER_OUTSIDE) THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`f:complex->complex`; `a:real`; `b:real`; `&1`] SCH2_NECK_CURVE_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`f:complex->complex`; `a:real`; `b:real`; `s:real`] SCH2_NECK_CURVE_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  (* The outer side of the unit circle goes outside. *)
  SUBGOAL_THEN `!z. z IN annulus (&1) b
                    ==> (f:complex->complex) z IN outside(IMAGE f (sphere(Cx(&0),&1)))`
  (LABEL_TAC "OUT1") THENL
   [MP_TAC(SPECL [`f:complex->complex`; `a:real`; `b:real`; `&1`] SCH2_SIDES_RADIUS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `Cx((a + &1) / &2) IN annulus a (&1)` ASSUME_TAC THENL
     [REWRITE_TAC[annulus; IN_ELIM_THM; COMPLEX_NORM_CX] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `F ==> p`) THEN
    UNDISCH_TAC `inside(IMAGE (f:complex->complex) (sphere(Cx(&0),&1))) INTER
                 outside(IMAGE f (sphere(Cx(&0),&1))) = {}` THEN
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `(f:complex->complex)(Cx((a + &1) / &2))`) THEN
    REWRITE_TAC[DE_MORGAN_THM] THEN CONJ_TAC THENL
     [USE_THEN "IN1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* The small circle lies inside the unit one; outsides are nested. *)
  SUBGOAL_THEN `IMAGE (f:complex->complex) (sphere(Cx(&0),s)) SUBSET
                inside(IMAGE f (sphere(Cx(&0),&1)))` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; SCH2_IN_C0] THEN X_GEN_TAC `z:complex` THEN
    DISCH_TAC THEN USE_THEN "IN1" MATCH_MP_TAC THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `outside(IMAGE (f:complex->complex) (sphere(Cx(&0),&1))) SUBSET
                outside(IMAGE f (sphere(Cx(&0),s)))` ASSUME_TAC THENL
   [MATCH_MP_TAC SCH2_UNBOUNDED_IN_OUTSIDE THEN
    ASM_SIMP_TAC[CONNECTED_OUTSIDE; UNBOUNDED_OUTSIDE; DIMINDEX_2; LE_REFL] THEN
    UNDISCH_TAC `IMAGE (f:complex->complex) (sphere(Cx(&0),s)) SUBSET
                 inside(IMAGE f (sphere(Cx(&0),&1)))` THEN
    UNDISCH_TAC `inside(IMAGE (f:complex->complex) (sphere(Cx(&0),&1))) INTER
                 outside(IMAGE f (sphere(Cx(&0),&1))) = {}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`f:complex->complex`; `a:real`; `b:real`; `s:real`] SCH2_SIDES_RADIUS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `Cx((&1 + b) / &2) IN annulus (&1) b /\ Cx((&1 + b) / &2) IN annulus s b`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[annulus; IN_ELIM_THM; COMPLEX_NORM_CX] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN
  UNDISCH_TAC `inside(IMAGE (f:complex->complex) (sphere(Cx(&0),s))) INTER
               outside(IMAGE f (sphere(Cx(&0),s))) = {}` THEN
  REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  DISCH_THEN(MP_TAC o SPEC `(f:complex->complex)(Cx((&1 + b) / &2))`) THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `annulus s b:complex->bool`)) (concl th) &&
      can (find_term ((=) `inside:(complex->bool)->complex->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `outside(IMAGE (f:complex->complex) (sphere(Cx(&0),&1))) SUBSET
                 outside(IMAGE f (sphere(Cx(&0),s)))` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    USE_THEN "OUT1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let SCH2_NECK_NEST_SET = prove
 (`!(f:complex->complex) a b s.
        &0 < a /\ a < s /\ s < &1 /\ &1 < b /\ f continuous_on annulus a b /\
        (!w z. w IN annulus a b /\ z IN annulus a b /\ f w = f z ==> w = z) /\
        (!z. z IN annulus a (&1) ==> f z IN inside(IMAGE f (sphere(Cx(&0),&1))))
        ==> IMAGE f (sphere(Cx(&0),&1)) UNION inside(IMAGE f (sphere(Cx(&0),&1))) =
            (IMAGE f (sphere(Cx(&0),s)) UNION inside(IMAGE f (sphere(Cx(&0),s)))) UNION
            IMAGE f {z | s <= norm z /\ norm z <= &1}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH2_NECK_SIDES) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  MP_TAC(SPECL [`f:complex->complex`; `a:real`; `b:real`; `&1`] SCH2_NECK_CURVE_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`f:complex->complex`; `a:real`; `b:real`; `s:real`] SCH2_NECK_CURVE_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `!t:complex->bool. t SUBSET annulus a b /\ open t
                ==> open(IMAGE (f:complex->complex) t)` (LABEL_TAC "OPEN") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `annulus a b:complex->bool` THEN
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 2)) THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (f:complex->complex) (annulus s (&1))) /\
                open(IMAGE (f:complex->complex) (annulus s b))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "OPEN" MATCH_MP_TAC THEN REWRITE_TAC[OPEN_ANNULUS] THEN
    REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `closed(IMAGE (f:complex->complex) {z | s <= norm z /\ norm z <= &1})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `annulus a b:complex->bool` THEN
      ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM; annulus] THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `{z:complex | s <= norm z /\ norm z <= &1} =
                    cball(Cx(&0),&1) DIFF ball(Cx(&0),s)` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; SCH2_IN_C0] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[COMPACT_CBALL; OPEN_BALL]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (f:complex->complex) {z | s <= norm z /\ norm z <= &1} =
    IMAGE f (sphere(Cx(&0),s)) UNION IMAGE f (annulus s (&1)) UNION
    IMAGE f (sphere(Cx(&0),&1)) /\
    IMAGE (f:complex->complex) (annulus s b) =
    IMAGE f (annulus s (&1)) UNION IMAGE f (sphere(Cx(&0),&1)) UNION IMAGE f (annulus (&1) b)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_UNION] THEN CONJ_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM; SCH2_IN_C0; annulus] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (f:complex->complex) (annulus s (&1)) SUBSET inside(IMAGE f (sphere(Cx(&0),&1))) /\
    IMAGE (f:complex->complex) (annulus s (&1)) SUBSET outside(IMAGE f (sphere(Cx(&0),s))) /\
    IMAGE (f:complex->complex) (sphere(Cx(&0),&1)) SUBSET outside(IMAGE f (sphere(Cx(&0),s))) /\
    IMAGE (f:complex->complex) (sphere(Cx(&0),s)) SUBSET inside(IMAGE f (sphere(Cx(&0),&1))) /\
    IMAGE (f:complex->complex) (annulus (&1) b) SUBSET outside(IMAGE f (sphere(Cx(&0),&1)))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN REPEAT CONJ_TAC THEN X_GEN_TAC `z:complex` THEN
    REWRITE_TAC[annulus; IN_ELIM_THM; SCH2_IN_C0] THEN DISCH_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `C1 = IMAGE (f:complex->complex) (sphere(Cx(&0),&1))` THEN
  ABBREV_TAC `Cs = IMAGE (f:complex->complex) (sphere(Cx(&0),s))` THEN
  ABBREV_TAC `U = IMAGE (f:complex->complex) (annulus s (&1))` THEN
  ABBREV_TAC `M = IMAGE (f:complex->complex) {z | s <= norm z /\ norm z <= &1}` THEN
  ABBREV_TAC `E = IMAGE (f:complex->complex) (annulus s b)` THEN
  ABBREV_TAC `O = IMAGE (f:complex->complex) (annulus (&1) b)` THEN
  MP_TAC(ISPEC `C1:complex->bool` INSIDE_INTER_OUTSIDE) THEN
  MP_TAC(ISPEC `Cs:complex->bool` INSIDE_INTER_OUTSIDE) THEN
  MP_TAC(ISPEC `C1:complex->bool` INSIDE_UNION_OUTSIDE) THEN
  MP_TAC(ISPEC `Cs:complex->bool` INSIDE_UNION_OUTSIDE) THEN
  MP_TAC(ISPEC `C1:complex->bool` INSIDE_NO_OVERLAP) THEN
  MP_TAC(ISPEC `Cs:complex->bool` OUTSIDE_NO_OVERLAP) THEN
  REPEAT DISCH_TAC THEN
  (* The key claim: points inside C1 and outside Cs lie in M. *)
  SUBGOAL_THEN `(inside C1 INTER outside Cs) DIFF M = ({}:complex->bool)` ASSUME_TAC THENL
   [ABBREV_TAC `e1 = (inside C1 INTER outside Cs) DIFF (M:complex->bool)` THEN
    ABBREV_TAC `e2 = (E:complex->bool) UNION outside C1` THEN
    SUBGOAL_THEN `open(e1:complex->bool) /\ open(e2:complex->bool)` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "e1" THEN EXPAND_TAC "e2" THEN
      ASM_SIMP_TAC[OPEN_DIFF; OPEN_INTER; OPEN_INSIDE; OPEN_OUTSIDE; OPEN_UNION];
      ALL_TAC] THEN
    SUBGOAL_THEN `outside Cs SUBSET (e1:complex->bool) UNION e2` ASSUME_TAC THENL
     [EXPAND_TAC "e1" THEN EXPAND_TAC "e2" THEN
      UNDISCH_TAC `inside C1 UNION outside C1 = (:complex) DIFF C1` THEN
      UNDISCH_TAC `(M:complex->bool) = Cs UNION U UNION C1` THEN
      UNDISCH_TAC `(E:complex->bool) = U UNION C1 UNION O` THEN
      UNDISCH_TAC `outside Cs INTER (Cs:complex->bool) = {}` THEN
      UNDISCH_TAC `inside C1 INTER (C1:complex->bool) = {}` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(e1:complex->bool) INTER e2 INTER outside Cs = {}` ASSUME_TAC THENL
     [EXPAND_TAC "e1" THEN EXPAND_TAC "e2" THEN
      UNDISCH_TAC `(M:complex->bool) = Cs UNION U UNION C1` THEN
      UNDISCH_TAC `(E:complex->bool) = U UNION C1 UNION O` THEN
      UNDISCH_TAC `(O:complex->bool) SUBSET outside C1` THEN
      UNDISCH_TAC `inside C1 INTER outside C1 = ({}:complex->bool)` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((e2:complex->bool) INTER outside Cs = {})` ASSUME_TAC THENL
     [EXPAND_TAC "e2" THEN
      UNDISCH_TAC `(C1:complex->bool) SUBSET outside Cs` THEN
      UNDISCH_TAC `(E:complex->bool) = U UNION C1 UNION O` THEN
      UNDISCH_TAC `~((C1:complex->bool) = {})` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(e1:complex->bool) SUBSET outside Cs` ASSUME_TAC THENL
     [EXPAND_TAC "e1" THEN SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPEC `Cs:complex->bool` CONNECTED_OUTSIDE) THEN
    ASM_REWRITE_TAC[DIMINDEX_2; LE_REFL] THEN
    REWRITE_TAC[connected; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`e1:complex->bool`; `e2:complex->bool`]) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(e1:complex->bool) SUBSET outside Cs` THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(inside C1 INTER outside Cs) DIFF M = ({}:complex->bool)` THEN
  UNDISCH_TAC `inside Cs UNION outside Cs = (:complex) DIFF Cs` THEN
  UNDISCH_TAC `inside C1 UNION outside C1 = (:complex) DIFF C1` THEN
  UNDISCH_TAC `outside C1 SUBSET outside (Cs:complex->bool)` THEN
  UNDISCH_TAC `inside Cs INTER outside Cs = ({}:complex->bool)` THEN
  UNDISCH_TAC `(M:complex->bool) = Cs UNION U UNION C1` THEN
  UNDISCH_TAC `(U:complex->bool) SUBSET inside C1` THEN
  UNDISCH_TAC `(Cs:complex->bool) SUBSET inside C1` THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Gluing diffeomorphisms; homeomorphisms and outsides;                      *)
(* injective holomorphic maps are diffeomorphisms onto their images.         *)
(* ------------------------------------------------------------------------- *)

let SCH2_DIFFEO_RESTRICT = prove
 (`!s t (f:real^N->real^N) g s'.
        diffeomorphism_on s t f g /\ open s' /\ s' SUBSET s
        ==> diffeomorphism_on s' (IMAGE f s') f g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (f:real^N->real^N) s' = {y | y IN t /\ (g:real^N->real^N) y IN s'}`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (f:real^N->real^N) s')` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `IMAGE (f:real^N->real^N) s' = {y | y IN t /\ (g:real^N->real^N) y IN s'}` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM SET_TAC[];
    ASM SET_TAC[];
    ASM SET_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* Two diffeomorphisms on an open cover agreeing with one injective map. *)

let SCH2_GLUE_DIFFEO = prove
 (`!(c:real^N->real^N) d1 d1' d2 d2' u1 u2.
        diffeomorphism_on u1 (IMAGE d1 u1) d1 d1' /\
        diffeomorphism_on u2 (IMAGE d2 u2) d2 d2' /\
        (!x. x IN u1 ==> c x = d1 x) /\ (!x. x IN u2 ==> c x = d2 x) /\
        (!x y. x IN u1 UNION u2 /\ y IN u1 UNION u2 /\ c x = c y ==> x = y)
        ==> ?c'. diffeomorphism_on (u1 UNION u2) (IMAGE c (u1 UNION u2)) c c'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[diffeomorphism_on] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "C1") (CONJUNCTS_THEN2 (LABEL_TAC "C2")
       (LABEL_TAC "INJ"))))) THEN
  SUBGOAL_THEN `IMAGE (c:real^N->real^N) u1 = IMAGE d1 u1 /\
                IMAGE (c:real^N->real^N) u2 = IMAGE d2 u2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC IMAGE_EQ THENL
     [USE_THEN "C1" ACCEPT_TAC; USE_THEN "C2" ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN IMAGE (d1:real^N->real^N) u1 /\ y IN IMAGE (d2:real^N->real^N) u2
                    ==> (d1':real^N->real^N) y = d2' y` (LABEL_TAC "AGREE") THENL
   [X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x1:real^N` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `x2:real^N` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(c:real^N->real^N) x1 = y /\ (c:real^N->real^N) x2 = y`
    STRIP_ASSUME_TAC THENL
     [USE_THEN "C1" (fun th -> REWRITE_TAC[MP (SPEC `x1:real^N` th)
        (ASSUME `(x1:real^N) IN u1`)]) THEN
      USE_THEN "C2" (fun th -> REWRITE_TAC[MP (SPEC `x2:real^N` th)
        (ASSUME `(x2:real^N) IN u2`)]) THEN
      CONJ_TAC THEN CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `x1:real^N = x2` SUBST_ALL_TAC THENL
     [USE_THEN "INJ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_UNION]; ALL_TAC] THEN
    SUBGOAL_THEN `(d1':real^N->real^N) y = x2 /\ (d2':real^N->real^N) y = x2`
    (fun th -> REWRITE_TAC[th]) THEN CONJ_TAC THENL
     [UNDISCH_TAC `(y:real^N) = (d1:real^N->real^N) x2` THEN DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[];
      UNDISCH_TAC `(y:real^N) = (d2:real^N->real^N) x2` THEN DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `c' = \y. if y IN IMAGE (d1:real^N->real^N) u1 then (d1':real^N->real^N) y
                       else d2' y` THEN
  SUBGOAL_THEN `(!y. y IN IMAGE (d1:real^N->real^N) u1 ==> (c':real^N->real^N) y = d1' y) /\
                (!y. y IN IMAGE (d2:real^N->real^N) u2 ==> (c':real^N->real^N) y = d2' y)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c'" THEN CONJ_TAC THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "AGREE" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!y. y IN IMAGE (d1:real^N->real^N) u1 ==> (d1':real^N->real^N) y IN u1) /\
                (!y. y IN IMAGE (d2:real^N->real^N) u2 ==> (d2':real^N->real^N) y IN u2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THENL
     [UNDISCH_TAC `IMAGE (d1':real^N->real^N) (IMAGE d1 u1) = u1`;
      UNDISCH_TAC `IMAGE (d2':real^N->real^N) (IMAGE d2 u2) = u2`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `c':real^N->real^N` THEN
  REWRITE_TAC[IMAGE_UNION] THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[OPEN_UNION] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `IMAGE (c':real^N->real^N) (IMAGE (d1:real^N->real^N) u1) =
                  IMAGE (d1':real^N->real^N) (IMAGE d1 u1) /\
                  IMAGE (c':real^N->real^N) (IMAGE (d2:real^N->real^N) u2) =
                  IMAGE (d2':real^N->real^N) (IMAGE d2 u2)`
    (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN MATCH_MP_TAC IMAGE_EQ THEN ASM_SIMP_TAC[]; ASM_REWRITE_TAC[]];
    REWRITE_TAC[IN_UNION] THEN X_GEN_TAC `x:real^N` THEN STRIP_TAC THENL
     [USE_THEN "C1" (fun th -> REWRITE_TAC[MP (SPEC `x:real^N` th)
        (ASSUME `(x:real^N) IN u1`)]) THEN
      SUBGOAL_THEN `(d1:real^N->real^N) x IN IMAGE d1 u1` ASSUME_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ASM_SIMP_TAC[]];
      USE_THEN "C2" (fun th -> REWRITE_TAC[MP (SPEC `x:real^N` th)
        (ASSUME `(x:real^N) IN u2`)]) THEN
      SUBGOAL_THEN `(d2:real^N->real^N) x IN IMAGE d2 u2` ASSUME_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ASM_SIMP_TAC[]]];
    REWRITE_TAC[IN_UNION] THEN X_GEN_TAC `y:real^N` THEN STRIP_TAC THENL
     [SUBGOAL_THEN `(d1':real^N->real^N) y IN u1` ASSUME_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[];
      SUBGOAL_THEN `(d2':real^N->real^N) y IN u2` ASSUME_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[]];
    MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_SIMP_TAC[OPEN_UNION; IN_UNION] THEN
    X_GEN_TAC `x:real^N` THEN STRIP_TAC THENL
     [EXISTS_TAC `u1:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `d1:real^N->real^N` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "C1" (fun th -> SIMP_TAC[th]);
      EXISTS_TAC `u2:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `d2:real^N->real^N` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "C2" (fun th -> SIMP_TAC[th])];
    MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_SIMP_TAC[OPEN_UNION; IN_UNION] THEN
    X_GEN_TAC `y:real^N` THEN STRIP_TAC THENL
     [EXISTS_TAC `IMAGE (d1:real^N->real^N) u1` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `d1':real^N->real^N` THEN
      ASM_SIMP_TAC[];
      EXISTS_TAC `IMAGE (d2:real^N->real^N) u2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `d2':real^N->real^N` THEN
      ASM_SIMP_TAC[]]]);;

let SCH2_OUTSIDE_HOMEOMORPHISM = prove
 (`!f:real^N->real^N g s.
        homeomorphism ((:real^N),(:real^N)) (f,g)
        ==> outside(IMAGE f s) = IMAGE f (outside s)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH_HOMEO_INVERSES) THEN
  REWRITE_TAC[OUTSIDE_INSIDE] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP SCH_INSIDE_HOMEOMORPHISM th]) THEN
  REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNION; IN_IMAGE; IN_UNIV] THEN ASM_MESON_TAC[]);;

let SCH2_HOLO_INJ_DIFFEO = prove
 (`!f:complex->complex s.
        open s /\ f holomorphic_on s /\
        (!w z. w IN s /\ z IN s /\ f w = f z ==> w = z)
        ==> ?g. diffeomorphism_on s (IMAGE f s) f g`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:complex->complex`; `s:complex->bool`] HOLOMORPHIC_ON_INVERSE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `g:complex->complex`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `g:complex->complex` THEN ASM_SIMP_TAC[diffeomorphism_on] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[] THEN X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(f:complex->complex) x` THEN
    ASM_SIMP_TAC[] THEN EXISTS_TAC `x:complex` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC BEL_HOLOMORPHIC_SMOOTH THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC BEL_HOLOMORPHIC_SMOOTH THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The straightened collar map Fa z = w(f(s z)) near the unit                *)
(* circle, and the circle map J of its analytic collar.                      *)
(* ------------------------------------------------------------------------- *)

let SCH2_FA_PROPS = prove
 (`!(f:complex->complex) w w' s r1 r2 a b.
     &0 < a /\ a < s * r1 /\ r1 < &1 /\ &1 < r2 /\ s * r2 < b /\ &0 < s /\
     f continuous_on annulus a b /\
     (!x y. x IN annulus a b /\ y IN annulus a b /\ f x = f y ==> x = y) /\
     diffeomorphism_on (:complex) (:complex) w w' /\
     (\z. w(f z)) holomorphic_on annulus (s * r1) (s * r2) /\
     (!z. z IN annulus a s ==> f z IN inside(IMAGE f (sphere(Cx(&0),s)))) /\
     (!z. z IN annulus s b ==> f z IN outside(IMAGE f (sphere(Cx(&0),s))))
     ==> (\z. w(f(Cx s * z))) holomorphic_on annulus r1 r2 /\
         (!x y. x IN annulus r1 r2 /\ y IN annulus r1 r2 /\
                w(f(Cx s * x)) = w(f(Cx s * y)) ==> x = y) /\
         IMAGE (\z. w(f(Cx s * z))) (sphere(Cx(&0),&1)) = IMAGE w (IMAGE f (sphere(Cx(&0),s))) /\
         (!z. z IN annulus r1 (&1)
              ==> w(f(Cx s * z)) IN inside(IMAGE (\z. w(f(Cx s * z))) (sphere(Cx(&0),&1)))) /\
         (!z. z IN annulus (&1) r2
              ==> w(f(Cx s * z)) IN outside(IMAGE (\z. w(f(Cx s * z))) (sphere(Cx(&0),&1))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `homeomorphism ((:complex),(:complex)) (w:complex->complex,w')` ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on (:complex) (:complex) (w:complex->complex) w'` THEN
    REWRITE_TAC[diffeomorphism_on; homeomorphism; IN_UNIV] THEN
    MESON_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH_HOMEO_INVERSES) THEN
  SUBGOAL_THEN `!z. z IN annulus r1 r2 ==> Cx s * z IN annulus (s * r1) (s * r2) /\
                                         Cx s * z IN annulus a b` (LABEL_TAC "SC") THENL
   [GEN_TAC THEN REWRITE_TAC[annulus; IN_ELIM_THM; COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < s ==> abs s = s`; REAL_LT_LMUL_EQ] THEN STRIP_TAC THEN
    SUBGOAL_THEN `s * r1 < s * norm(z:complex) /\ s * norm z < s * r2` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_LMUL_EQ]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (\z. (w:complex->complex)((f:complex->complex)(Cx s * z)))
                      (sphere(Cx(&0),&1)) = IMAGE w (IMAGE f (sphere(Cx(&0),s)))`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV)
      [GSYM(MATCH_MP SCH2_SCALE_SPHERE (ASSUME `&0 < s`))] THEN
    REWRITE_TAC[GSYM IMAGE_o; o_DEF];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`w:complex->complex`; `w':complex->complex`;
                 `IMAGE (f:complex->complex) (sphere(Cx(&0),s))`] SCH_INSIDE_HOMEOMORPHISM) THEN
  MP_TAC(ISPECL [`w:complex->complex`; `w':complex->complex`;
                 `IMAGE (f:complex->complex) (sphere(Cx(&0),s))`] SCH2_OUTSIDE_HOMEOMORPHISM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `(\z. (w:complex->complex)((f:complex->complex)(Cx s * z))) =
                  (\z. w(f z)) o (\z. Cx s * z)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE_GEN THEN
    EXISTS_TAC `annulus (s * r1) (s * r2):complex->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HOLOMORPHIC_ON_LMUL THEN REWRITE_TAC[HOLOMORPHIC_ON_ID];
      USE_THEN "SC" (fun th -> SIMP_TAC[th])];
    MAP_EVERY X_GEN_TAC [`x:complex`; `y:complex`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `Cx s * x = Cx s * y` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `annulus a b:complex->bool`)) (concl th) &&
        length(fst(strip_forall(concl th))) = 2)) THEN
      USE_THEN "SC" (fun th -> ASM_SIMP_TAC[th]) THEN
      FIRST_X_ASSUM(MP_TAC o AP_TERM `w':complex->complex` o check (fun th ->
        is_eq(concl th) && can (find_term ((=) `w:complex->complex`)) (concl th) &&
        not(is_forall(concl th)))) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[COMPLEX_EQ_MUL_LCANCEL; CX_INJ] THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ]];
    X_GEN_TAC `z:complex` THEN DISCH_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `annulus a s:complex->bool`)) (concl th))) THEN
    UNDISCH_TAC `(z:complex) IN annulus r1 (&1)` THEN
    REWRITE_TAC[annulus; IN_ELIM_THM; COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < s ==> abs s = s`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `s * r1 < s * norm(z:complex) /\ s * norm z < s * &1` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_LMUL_EQ]; ASM_REAL_ARITH_TAC];
    X_GEN_TAC `z:complex` THEN DISCH_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `annulus s b:complex->bool`)) (concl th))) THEN
    UNDISCH_TAC `(z:complex) IN annulus (&1) r2` THEN
    REWRITE_TAC[annulus; IN_ELIM_THM; COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < s ==> abs s = s`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `s * &1 < s * norm(z:complex) /\ s * norm z < s * r2` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_LMUL_EQ]; ASM_REAL_ARITH_TAC]]);;

(* The circle map J of an analytic collar is injective, and maps the inner   *)
(* half of its annulus into the unit disc (open mapping).                    *)

let SCH2_J_INNER = prove
 (`!(Fa:complex->complex) Phi R rho L r1 r2.
     &0 < r1 /\ r1 <= rho /\ inv r2 <= rho /\ rho < &1 /\ &1 < r2 /\ &1 < R /\
     (!w z. w IN annulus r1 r2 /\ z IN annulus r1 r2 /\ Fa w = Fa z ==> w = z) /\
     (!z. z IN annulus r1 (&1) ==> Fa z IN inside(IMAGE Fa (sphere(Cx(&0),&1)))) /\
     (!w z. w IN ball(Cx(&0),R) /\ z IN ball(Cx(&0),R) /\ Phi w = Phi z ==> w = z) /\
     IMAGE Phi (cball(Cx(&0),&1)) =
       IMAGE Fa (sphere(Cx(&0),&1)) UNION inside(IMAGE Fa (sphere(Cx(&0),&1))) /\
     L holomorphic_on annulus rho (inv rho) /\
     (!z. z IN annulus rho (inv rho)
          ==> z * cexp(L z) IN ball(Cx(&0),R) /\ Phi(z * cexp(L z)) = Fa z)
     ==> (!w z. w IN annulus rho (inv rho) /\ z IN annulus rho (inv rho) /\
                w * cexp(L w) = z * cexp(L z) ==> w = z) /\
         (!z. z IN annulus rho (&1) ==> norm(z * cexp(L z)) < &1)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "FINJ") (CONJUNCTS_THEN2 (LABEL_TAC "FIN")
    (CONJUNCTS_THEN2 (LABEL_TAC "PINJ") (CONJUNCTS_THEN2 (LABEL_TAC "PIM")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "JC")))))))))))) THEN
  SUBGOAL_THEN `&0 < rho /\ inv rho <= r2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(annulus rho (inv rho):complex->bool) SUBSET annulus r1 r2 /\
                (annulus rho (&1):complex->bool) SUBSET annulus rho (inv rho) /\
                (annulus rho (&1):complex->bool) SUBSET annulus r1 (&1)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 < inv rho` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_INV_1_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!w z. w IN annulus rho (inv rho) /\ z IN annulus rho (inv rho) /\
                      w * cexp((L:complex->complex) w) = z * cexp(L z) ==> w = z`
  (LABEL_TAC "JINJ") THENL
   [MAP_EVERY X_GEN_TAC [`w:complex`; `z:complex`] THEN STRIP_TAC THEN
    USE_THEN "FINJ" MATCH_MP_TAC THEN
    USE_THEN "JC" (fun th -> REWRITE_TAC[GSYM(CONJUNCT2(MP (SPEC `w:complex` th)
      (ASSUME `(w:complex) IN annulus rho (inv rho)`))); GSYM(CONJUNCT2(MP (SPEC `z:complex` th)
      (ASSUME `(z:complex) IN annulus rho (inv rho)`)))]) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(annulus rho (inv rho):complex->bool) SUBSET annulus r1 r2` THEN
    UNDISCH_TAC `(w:complex) IN annulus rho (inv rho)` THEN
    UNDISCH_TAC `(z:complex) IN annulus rho (inv rho)` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `IMAGE (\z. z * cexp((L:complex->complex) z)) (annulus rho (&1)) SUBSET
                cball(Cx(&0),&1)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:complex) IN annulus rho (inv rho)` ASSUME_TAC THENL
     [UNDISCH_TAC `(annulus rho (&1):complex->bool) SUBSET annulus rho (inv rho)` THEN
      UNDISCH_TAC `(z:complex) IN annulus rho (&1)` THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "JC" (STRIP_ASSUME_TAC o C MP (ASSUME `(z:complex) IN annulus rho (inv rho)`) o
      SPEC `z:complex`) THEN
    SUBGOAL_THEN `(Fa:complex->complex) z IN IMAGE (Phi:complex->complex) (cball(Cx(&0),&1))`
    MP_TAC THENL
     [USE_THEN "PIM" SUBST1_TAC THEN REWRITE_TAC[IN_UNION] THEN DISJ2_TAC THEN
      USE_THEN "FIN" MATCH_MP_TAC THEN
      UNDISCH_TAC `(annulus rho (&1):complex->bool) SUBSET annulus r1 (&1)` THEN
      UNDISCH_TAC `(z:complex) IN annulus rho (&1)` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `u:complex` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `u = z * cexp((L:complex->complex) z)` (fun th -> ASM_REWRITE_TAC[GSYM th]) THEN
    USE_THEN "PINJ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(u:complex) IN cball(Cx(&0),&1)` THEN
    REWRITE_TAC[SCH2_IN_C0] THEN UNDISCH_TAC `&1 < R` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (\z. z * cexp((L:complex->complex) z)) (annulus rho (&1)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN REWRITE_TAC[OPEN_ANNULUS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HOLOMORPHIC_ON_IMP_CONTINUOUS_ON THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN
      EXISTS_TAC `annulus rho (inv rho):complex->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN REWRITE_TAC[HOLOMORPHIC_ON_ID] THEN
      GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM o_DEF] THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE THEN ASM_REWRITE_TAC[HOLOMORPHIC_ON_CEXP];
      MAP_EVERY X_GEN_TAC [`w:complex`; `z:complex`] THEN STRIP_TAC THEN
      USE_THEN "JINJ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(annulus rho (&1):complex->bool) SUBSET annulus rho (inv rho)` THEN
      UNDISCH_TAC `(w:complex) IN annulus rho (&1)` THEN
      UNDISCH_TAC `(z:complex) IN annulus rho (&1)` THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`cball(Cx(&0),&1)`;
                 `IMAGE (\z. z * cexp((L:complex->complex) z)) (annulus rho (&1))`]
    INTERIOR_MAXIMAL) THEN
  ASM_REWRITE_TAC[INTERIOR_CBALL] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; SCH2_IN_C0]);;

(* The inner chart x |-> w'(Phi(E(x / s))) is a diffeomorphism onto its     *)
(* image on ball(0,s t) when E maps ball(0,t) into the domain of Phi.        *)

let SCH2_INNER_CHART = prove
 (`!(w:complex->complex) w' Phi R E E' s t.
     diffeomorphism_on (:complex) (:complex) w w' /\
     Phi holomorphic_on ball(Cx(&0),R) /\
     (!x y. x IN ball(Cx(&0),R) /\ y IN ball(Cx(&0),R) /\ Phi x = Phi y ==> x = y) /\
     diffeomorphism_on (:complex) (:complex) E E' /\
     &0 < s /\ &0 < t /\ IMAGE E (ball(Cx(&0),t)) SUBSET ball(Cx(&0),R)
     ==> ?k. diffeomorphism_on (ball(Cx(&0),s * t))
               (IMAGE (\x. w'(Phi(E(Cx(inv s) * x)))) (ball(Cx(&0),s * t)))
               (\x. w'(Phi(E(Cx(inv s) * x)))) k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `diffeomorphism_on (:complex) (:complex) (\x. Cx(inv s) * x) (\y. Cx s * y)`
  ASSUME_TAC THENL
   [REWRITE_TAC[diffeomorphism_on; OPEN_UNIV] THEN
    SUBGOAL_THEN `!c:complex. smooth_map_on (:complex) (\x. c * x)` ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC SCH2_CMUL_SMOOTH THEN REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[COMPLEX_MUL_ASSOC; GSYM CX_MUL] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_MUL_LINV; REAL_LT_IMP_NZ; COMPLEX_MUL_LID; IN_UNIV] THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN CONJ_TAC THEN X_GEN_TAC `y:complex` THENL
     [EXISTS_TAC `Cx s * y`; EXISTS_TAC `Cx(inv s) * y`] THEN
    REWRITE_TAC[COMPLEX_MUL_ASSOC; GSYM CX_MUL] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_MUL_LINV; REAL_LT_IMP_NZ; COMPLEX_MUL_LID];
    ALL_TAC] THEN
  ABBREV_TAC `U0 = ball(Cx(&0),s * t)` THEN
  SUBGOAL_THEN `open(U0:complex->bool) /\
                IMAGE (\x. Cx(inv s) * x) U0 SUBSET ball(Cx(&0),t)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "U0" THEN REWRITE_TAC[OPEN_BALL; SUBSET; FORALL_IN_IMAGE; SCH2_IN_C0] THEN
    X_GEN_TAC `x:complex` THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < s ==> abs s = s`] THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `U1 = IMAGE (\x. Cx(inv s) * x) U0` THEN
  MP_TAC(ISPECL [`(:complex)`; `(:complex)`; `\x. Cx(inv s) * x`; `\y. Cx s * y`;
                 `U0:complex->bool`] SCH2_DIFFEO_RESTRICT) THEN
  ASM_REWRITE_TAC[SUBSET_UNIV] THEN DISCH_TAC THEN
  SUBGOAL_THEN `open(U1:complex->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
  ABBREV_TAC `U2 = IMAGE (E:complex->complex) U1` THEN
  MP_TAC(ISPECL [`(:complex)`; `(:complex)`; `E:complex->complex`; `E':complex->complex`;
                 `U1:complex->bool`] SCH2_DIFFEO_RESTRICT) THEN
  ASM_REWRITE_TAC[SUBSET_UNIV] THEN DISCH_TAC THEN
  SUBGOAL_THEN `open(U2:complex->bool) /\ U2 SUBSET ball(Cx(&0),R)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
    EXPAND_TAC "U2" THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (E:complex->complex) (ball(Cx(&0),t))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]; FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Phi:complex->complex`; `ball(Cx(&0),R)`] SCH2_HOLO_INJ_DIFFEO) THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN DISCH_THEN(X_CHOOSE_TAC `Phi':complex->complex`) THEN
  MP_TAC(ISPECL [`ball(Cx(&0),R)`; `IMAGE (Phi:complex->complex) (ball(Cx(&0),R))`;
                 `Phi:complex->complex`; `Phi':complex->complex`;
                 `U2:complex->bool`] SCH2_DIFFEO_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `U3 = IMAGE (Phi:complex->complex) U2` THEN
  SUBGOAL_THEN `open(U3:complex->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(:complex)`; `(:complex)`; `w':complex->complex`; `w:complex->complex`;
                 `U3:complex->bool`] SCH2_DIFFEO_RESTRICT) THEN
  ASM_SIMP_TAC[SUBSET_UNIV; DIFFEOMORPHISM_ON_SYM] THEN DISCH_TAC THEN
  EXISTS_TAC `(((\y. Cx s * y) o (E':complex->complex)) o (Phi':complex->complex)) o
              (w:complex->complex)` THEN
  SUBGOAL_THEN `(\x. (w':complex->complex)((Phi:complex->complex)((E:complex->complex)
                   (Cx(inv s) * x)))) = w' o Phi o E o (\x. Cx(inv s) * x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN EXISTS_TAC `U3:complex->bool` THEN
  CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
  MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN EXISTS_TAC `U2:complex->bool` THEN
  CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
  MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN EXISTS_TAC `U1:complex->bool` THEN
  CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

let SCH2_SCALE_CBALL = prove
 (`!r. &0 < r ==> IMAGE (\z. Cx(inv r) * z) (cball(Cx(&0),r)) = cball(Cx(&0),&1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; SCH2_IN_C0] THEN
  X_GEN_TAC `w:complex` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `z:complex` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID];
    DISCH_TAC THEN EXISTS_TAC `Cx r * w` THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; COMPLEX_MUL_ASSOC; GSYM CX_MUL] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; COMPLEX_MUL_LID;
                 REAL_ARITH `&0 < r ==> abs r = r`] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

(* ------------------------------------------------------------------------- *)
(* The collared planar Schoenflies theorem for a normalized                  *)
(* neck (orientation-preserving, inner half inside).                          *)
(* ------------------------------------------------------------------------- *)

let SCH2_R2_CORE = prove
 (`!f f':complex->complex.
     diffeomorphism_on (annulus (&1 / &2) (&2)) (IMAGE f (annulus (&1 / &2) (&2))) f f' /\
     (!z. z IN annulus (&1 / &2) (&2) ==> norm(wirtinger_dbar f z) < norm(wirtinger_dz f z)) /\
     (!z. z IN annulus (&1 / &2) (&1) ==> f z IN inside(IMAGE f (sphere(Cx(&0),&1))))
     ==> ?c c'. diffeomorphism_on (ball(Cx(&0),&2)) (IMAGE c (ball(Cx(&0),&2))) c c' /\
                IMAGE c (cball(Cx(&0),&1)) =
                  IMAGE f (sphere(Cx(&0),&1)) UNION inside(IMAGE f (sphere(Cx(&0),&1))) /\
                (!x. x IN annulus (&3 / &4) (&2) ==> c x = f x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "IN1"))) THEN
  SUBGOAL_THEN `(f:complex->complex) continuous_on annulus (&1 / &2) (&2) /\
                (!x y. x IN annulus (&1 / &2) (&2) /\ y IN annulus (&1 / &2) (&2) /\
                       f x = f y ==> x = y)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on (annulus (&1 / &2) (&2))
                   (IMAGE (f:complex->complex) (annulus (&1 / &2) (&2))) f f'` THEN
    REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`f:complex->complex`; `&1 / &2`; `&2`; `&5 / &8`] SCH2_NECK_SIDES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN USE_THEN "IN1" ACCEPT_TAC;
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "INS") (LABEL_TAC "OUTS"))))] THEN
  MP_TAC(SPECL [`f:complex->complex`; `&1 / &2`; `&2`; `&5 / &8`] SCH2_NECK_NEST_SET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN USE_THEN "IN1" ACCEPT_TAC;
    DISCH_THEN(LABEL_TAC "NEST")] THEN
  (* Beltrami straightening near the circle of radius 5/8. *)
  MP_TAC(ISPECL [`f:complex->complex`; `f':complex->complex`;
                 `annulus (&1 / &2) (&2):complex->bool`;
                 `annulus (&9 / &16) (&11 / &16):complex->bool`;
                 `cball(Cx(&0),&11 / &16) DIFF ball(Cx(&0),&9 / &16)`]
    SCH2_BELTRAMI_STRAIGHTEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_ANNULUS] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM; IN_DIFF; SCH2_IN_C0] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[COMPACT_CBALL; OPEN_BALL];
      REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM; IN_DIFF; SCH2_IN_C0] THEN REAL_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `w:complex->complex` (X_CHOOSE_THEN `w':complex->complex`
      STRIP_ASSUME_TAC))] THEN
  MP_TAC(SPECL [`f:complex->complex`; `w:complex->complex`; `w':complex->complex`;
                `&5 / &8`; `&9 / &10`; `&11 / &10`; `&1 / &2`; `&2`] SCH2_FA_PROPS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [USE_THEN "INS" ACCEPT_TAC; USE_THEN "OUTS" ACCEPT_TAC];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "FAINJ")
      (CONJUNCTS_THEN2 (LABEL_TAC "FAIM") (CONJUNCTS_THEN2 (LABEL_TAC "FAIN")
        (LABEL_TAC "FAOUT")))))] THEN
  (* The analytic collar of Fa and the extension of its circle map. *)
  MP_TAC(ISPECL [`\z. (w:complex->complex)((f:complex->complex)(Cx(&5 / &8) * z))`;
                 `&9 / &10`; `&11 / &10`] SCH2_ANALYTIC_COLLAR) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Phi:complex->complex` (X_CHOOSE_THEN `R:real`
    (X_CHOOSE_THEN `rho:real` (X_CHOOSE_THEN `L:complex->complex`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "PINJ") (CONJUNCTS_THEN2 (LABEL_TAC "PIM")
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "SYM")
        (LABEL_TAC "JC")))))))))))))) THEN
  MP_TAC(ISPECL [`\z. (w:complex->complex)((f:complex->complex)(Cx(&5 / &8) * z))`;
                 `Phi:complex->complex`; `R:real`; `rho:real`; `L:complex->complex`;
                 `&9 / &10`; `&11 / &10`] SCH2_J_INNER) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "JINJ") (LABEL_TAC "JB")) THEN
  SUBGOAL_THEN `&0 < rho /\ &1 < inv rho /\ &2 - rho <= inv rho` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < rho` ASSUME_TAC THENL
     [UNDISCH_TAC `&9 / &10 <= rho` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INV_1_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM REAL_INV_INV] THEN REWRITE_TAC[REAL_INV_INV] THEN
    SUBGOAL_THEN `inv rho = &1 / rho` SUBST1_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_LID]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    MP_TAC(SPEC `&1 - rho` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`L:complex->complex`; `rho:real`] SCH2_COLLAR_EXTEND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`u:complex`; `v:complex`] THEN STRIP_TAC THEN
    USE_THEN "JINJ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(u:complex) IN annulus rho (&1)` THEN
    UNDISCH_TAC `(v:complex) IN annulus rho (&1)` THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN UNDISCH_TAC `&1 < inv rho` THEN REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `E:complex->complex`
      (X_CHOOSE_THEN `E':complex->complex` (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 (LABEL_TAC "EJ") (CONJUNCTS_THEN2 (LABEL_TAC "EB")
             (LABEL_TAC "ECB")))))))))] THEN
  ABBREV_TAC `e = min d (&1 / &10)` THEN
  SUBGOAL_THEN `&0 < e /\ e <= d /\ e <= &1 / &10 /\ e < &1 - rho` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN UNDISCH_TAC `&0 < d` THEN UNDISCH_TAC `d < &1 - rho` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* J z = E z for z near the unit circle, and these z lie in the collar annulus. *)
  SUBGOAL_THEN `!z. abs(norm z - &1) < e
                    ==> z IN annulus rho (inv rho) /\ (E:complex->complex) z = z * cexp(L z)`
  (LABEL_TAC "EJ2") THENL
   [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[annulus; IN_ELIM_THM] THEN
      UNDISCH_TAC `abs(norm(z:complex) - &1) < e` THEN UNDISCH_TAC `e < &1 - rho` THEN
      UNDISCH_TAC `&2 - rho <= inv rho` THEN REAL_ARITH_TAC;
      USE_THEN "EJ" MATCH_MP_TAC THEN
      UNDISCH_TAC `abs(norm(z:complex) - &1) < e` THEN UNDISCH_TAC `e <= d` THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!y. (w':complex->complex)((w:complex->complex) y) = y) /\
                (!y. (w:complex->complex)((w':complex->complex) y) = y) /\
                homeomorphism ((:complex),(:complex)) (w:complex->complex,w') /\
                homeomorphism ((:complex),(:complex)) (w':complex->complex,w)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on (:complex) (:complex) (w:complex->complex) w'` THEN
    REWRITE_TAC[diffeomorphism_on; homeomorphism; IN_UNIV] THEN
    MESON_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  (* The inner chart and the outer chart. *)
  MP_TAC(ISPECL [`w:complex->complex`; `w':complex->complex`; `Phi:complex->complex`;
                 `R:real`; `E:complex->complex`; `E':complex->complex`; `&5 / &8`;
                 `&1 + e`] SCH2_INNER_CHART) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN CONJ_TAC THENL
     [UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; SCH2_IN_C0] THEN X_GEN_TAC `z:complex` THEN
    DISCH_TAC THEN ASM_CASES_TAC `norm(z:complex) < &1` THENL
     [SUBGOAL_THEN `(E:complex->complex) z IN ball(Cx(&0),&1)` MP_TAC THENL
       [USE_THEN "EB" (SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        ASM_REWRITE_TAC[SCH2_IN_C0];
        REWRITE_TAC[SCH2_IN_C0] THEN UNDISCH_TAC `&1 < R` THEN REAL_ARITH_TAC];
      SUBGOAL_THEN `abs(norm(z:complex) - &1) < e` ASSUME_TAC THENL
       [UNDISCH_TAC `~(norm(z:complex) < &1)` THEN UNDISCH_TAC `norm(z:complex) < &1 + e` THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      USE_THEN "EJ2" (STRIP_ASSUME_TAC o C MP (ASSUME `abs(norm(z:complex) - &1) < e`) o
        SPEC `z:complex`) THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "JC" (fun th -> REWRITE_TAC[GSYM SCH2_IN_C0; CONJUNCT1(MP (SPEC `z:complex` th)
        (ASSUME `(z:complex) IN annulus rho (inv rho)`))])];
    DISCH_THEN(X_CHOOSE_TAC `k:complex->complex`)] THEN
  MP_TAC(ISPECL [`annulus (&1 / &2) (&2):complex->bool`;
                 `IMAGE (f:complex->complex) (annulus (&1 / &2) (&2))`;
                 `f:complex->complex`; `f':complex->complex`;
                 `annulus (&5 / &8 * (&1 - e)) (&2):complex->bool`] SCH2_DIFFEO_RESTRICT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_ANNULUS] THEN REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN
    UNDISCH_TAC `e <= &1 / &10` THEN REAL_ARITH_TAC;
    DISCH_TAC] THEN
  ABBREV_TAC `inner = \x. (w':complex->complex)((Phi:complex->complex)
                            ((E:complex->complex)(Cx(inv(&5 / &8)) * x)))` THEN
  (* The two charts agree on the overlap. *)
  SUBGOAL_THEN `!x. &5 / &8 * (&1 - e) < norm x /\ norm x < &5 / &8 * (&1 + e)
                    ==> (inner:complex->complex) x = (f:complex->complex) x` (LABEL_TAC "OVL")
  THENL
   [X_GEN_TAC `x:complex` THEN STRIP_TAC THEN EXPAND_TAC "inner" THEN
    ABBREV_TAC `z = Cx(inv(&5 / &8)) * x` THEN
    SUBGOAL_THEN `abs(norm(z:complex) - &1) < e` ASSUME_TAC THENL
     [EXPAND_TAC "z" THEN REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      UNDISCH_TAC `&5 / &8 * (&1 - e) < norm(x:complex)` THEN
      UNDISCH_TAC `norm(x:complex) < &5 / &8 * (&1 + e)` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "EJ2" (STRIP_ASSUME_TAC o C MP (ASSUME `abs(norm(z:complex) - &1) < e`) o
      SPEC `z:complex`) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "JC" (fun th -> REWRITE_TAC[CONJUNCT2(MP (SPEC `z:complex` th)
      (ASSUME `(z:complex) IN annulus rho (inv rho)`))]) THEN
    SUBGOAL_THEN `Cx(&5 / &8) * z = x` SUBST1_TAC THENL
     [EXPAND_TAC "z" THEN REWRITE_TAC[COMPLEX_MUL_ASSOC; GSYM CX_MUL] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[COMPLEX_MUL_LID];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* The inner chart fills the closed side of the circle of radius 5/8. *)
  SUBGOAL_THEN `IMAGE (inner:complex->complex) (cball(Cx(&0),&5 / &8)) =
                IMAGE (f:complex->complex) (sphere(Cx(&0),&5 / &8)) UNION
                inside(IMAGE f (sphere(Cx(&0),&5 / &8)))` (LABEL_TAC "INIM") THENL
   [SUBGOAL_THEN `IMAGE (inner:complex->complex) (cball(Cx(&0),&5 / &8)) =
                  IMAGE (w':complex->complex) (IMAGE (Phi:complex->complex)
                    (IMAGE (E:complex->complex)
                      (IMAGE (\x. Cx(inv(&5 / &8)) * x) (cball(Cx(&0),&5 / &8)))))`
    SUBST1_TAC THENL
     [EXPAND_TAC "inner" THEN REWRITE_TAC[GSYM IMAGE_o; o_DEF]; ALL_TAC] THEN
    REWRITE_TAC[MATCH_MP SCH2_SCALE_CBALL (EQT_ELIM(REAL_RAT_REDUCE_CONV `&0 < &5 / &8`))] THEN
    USE_THEN "ECB" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "PIM" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "FAIM" (fun th -> REWRITE_TAC[th]) THEN
    MP_TAC(ISPECL [`w:complex->complex`; `w':complex->complex`;
                   `IMAGE (f:complex->complex) (sphere(Cx(&0),&5 / &8))`]
      SCH_INSIDE_HOMEOMORPHISM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[GSYM IMAGE_UNION; GSYM IMAGE_o; o_DEF] THEN
    ASM_REWRITE_TAC[IMAGE_ID];
    ALL_TAC] THEN
  ABBREV_TAC `Cs = IMAGE (f:complex->complex) (sphere(Cx(&0),&5 / &8))` THEN
  ABBREV_TAC `c = \x. if norm x < &5 / &8 * (&1 + e) then (inner:complex->complex) x
                      else (f:complex->complex) x` THEN
  SUBGOAL_THEN `(!x. norm x < &5 / &8 * (&1 + e) ==> (c:complex->complex) x = inner x) /\
                (!x. &5 / &8 * (&1 - e) < norm x ==> (c:complex->complex) x = f x)`
  (CONJUNCTS_THEN2 (LABEL_TAC "CIN") (LABEL_TAC "COUT")) THENL
   [EXPAND_TAC "c" THEN CONJ_TAC THEN X_GEN_TAC `x:complex` THEN DISCH_TAC THENL
     [ASM_REWRITE_TAC[];
      COND_CASES_TAC THEN REWRITE_TAC[] THEN USE_THEN "OVL" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* Injectivity. *)
  SUBGOAL_THEN `!x y. norm x <= &5 / &8 * (&1 - e) /\ &5 / &8 * (&1 + e) <= norm y /\
                      norm y < &2 ==> ~((c:complex->complex) x = c y)` (LABEL_TAC "SEP") THENL
   [MAP_EVERY X_GEN_TAC [`x:complex`; `y:complex`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(c:complex->complex) x IN Cs UNION inside Cs` MP_TAC THENL
     [SUBGOAL_THEN `(c:complex->complex) x = inner x` SUBST1_TAC THENL
       [USE_THEN "CIN" MATCH_MP_TAC THEN
        UNDISCH_TAC `norm(x:complex) <= &5 / &8 * (&1 - e)` THEN
        UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      USE_THEN "INIM" (SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      REWRITE_TAC[SCH2_IN_C0] THEN
      UNDISCH_TAC `norm(x:complex) <= &5 / &8 * (&1 - e)` THEN
      UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(c:complex->complex) y IN outside Cs` MP_TAC THENL
     [SUBGOAL_THEN `(c:complex->complex) y = f y` SUBST1_TAC THENL
       [USE_THEN "COUT" MATCH_MP_TAC THEN
        UNDISCH_TAC `&5 / &8 * (&1 + e) <= norm(y:complex)` THEN
        UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      USE_THEN "OUTS" MATCH_MP_TAC THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN
      UNDISCH_TAC `&5 / &8 * (&1 + e) <= norm(y:complex)` THEN
      UNDISCH_TAC `norm(y:complex) < &2` THEN UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPEC `Cs:complex->bool` OUTSIDE_NO_OVERLAP) THEN
    MP_TAC(ISPEC `Cs:complex->bool` INSIDE_INTER_OUTSIDE) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y. norm x < &2 /\ norm y < &2 /\ (c:complex->complex) x = c y ==> x = y`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:complex`; `y:complex`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `norm(x:complex) < &5 / &8 * (&1 + e) /\ norm(y:complex) < &5 / &8 * (&1 + e)`
    THENL
     [FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
      SUBGOAL_THEN `(inner:complex->complex) x = inner y` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o AP_TERM `k:complex->complex`) THEN
      UNDISCH_TAC `diffeomorphism_on (ball(Cx(&0),&5 / &8 * (&1 + e)))
                     (IMAGE (inner:complex->complex) (ball(Cx(&0),&5 / &8 * (&1 + e))))
                     inner k` THEN
      REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[SCH2_IN_C0];
      ALL_TAC] THEN
    ASM_CASES_TAC `&5 / &8 * (&1 - e) < norm(x:complex) /\ &5 / &8 * (&1 - e) < norm(y:complex)`
    THENL
     [FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `annulus (&1 / &2) (&2):complex->bool`)) (concl th) &&
        length(fst(strip_forall(concl th))) = 2)) THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN
      SUBGOAL_THEN `(f:complex->complex) x = (c:complex->complex) x /\ f y = c y`
      (fun th -> REWRITE_TAC[th]) THENL
       [CONJ_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          is_forall(concl th) &&
          can (find_term ((=) `f:complex->complex`)) (concl th) &&
          can (find_term ((=) `c:complex->complex`)) (concl th) &&
          not(can (find_term ((=) `inner:complex->complex`)) (concl th)))) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `e <= &1 / &10` THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `F ==> p`) THEN
    SUBGOAL_THEN `(norm(x:complex) <= &5 / &8 * (&1 - e) /\
                   &5 / &8 * (&1 + e) <= norm(y:complex)) \/
                  (norm(y:complex) <= &5 / &8 * (&1 - e) /\
                   &5 / &8 * (&1 + e) <= norm(x:complex))` MP_TAC THENL
     [UNDISCH_TAC `~(norm(x:complex) < &5 / &8 * (&1 + e) /\
                     norm(y:complex) < &5 / &8 * (&1 + e))` THEN
      UNDISCH_TAC `~(&5 / &8 * (&1 - e) < norm(x:complex) /\
                     &5 / &8 * (&1 - e) < norm(y:complex))` THEN
      UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    STRIP_TAC THENL
     [REMOVE_THEN "SEP" (MP_TAC o SPECL [`x:complex`; `y:complex`]);
      REMOVE_THEN "SEP" (MP_TAC o SPECL [`y:complex`; `x:complex`])] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* Gluing the two charts. *)
  SUBGOAL_THEN `ball(Cx(&0),&5 / &8 * (&1 + e)) UNION annulus (&5 / &8 * (&1 - e)) (&2) =
                ball(Cx(&0),&2)` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; SCH2_IN_C0; annulus; IN_ELIM_THM] THEN
    UNDISCH_TAC `&0 < e` THEN UNDISCH_TAC `e <= &1 / &10` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:complex->complex`; `inner:complex->complex`; `k:complex->complex`;
                 `f:complex->complex`; `f':complex->complex`;
                 `ball(Cx(&0),&5 / &8 * (&1 + e))`;
                 `annulus (&5 / &8 * (&1 - e)) (&2):complex->bool`] SCH2_GLUE_DIFFEO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SCH2_IN_C0] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN X_GEN_TAC `x:complex` THEN STRIP_TAC THEN
    USE_THEN "COUT" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[ASSUME `ball(Cx(&0),&5 / &8 * (&1 + e)) UNION
                        annulus (&5 / &8 * (&1 - e)) (&2) = ball(Cx(&0),&2)`] THEN
    DISCH_THEN(X_CHOOSE_TAC `c':complex->complex`)] THEN
  MAP_EVERY EXISTS_TAC [`c:complex->complex`; `c':complex->complex`] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN CONJ_TAC THENL
   [(* The image of the closed unit disc. *)
    SUBGOAL_THEN `cball(Cx(&0),&1) =
                  cball(Cx(&0),&5 / &8) UNION {z:complex | &5 / &8 <= norm z /\ norm z <= &1}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_UNION; SCH2_IN_C0; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IMAGE_UNION] THEN
    SUBGOAL_THEN `IMAGE (c:complex->complex) (cball(Cx(&0),&5 / &8)) =
                  IMAGE (inner:complex->complex) (cball(Cx(&0),&5 / &8)) /\
                  IMAGE (c:complex->complex) {z:complex | &5 / &8 <= norm z /\ norm z <= &1} =
                  IMAGE (f:complex->complex) {z:complex | &5 / &8 <= norm z /\ norm z <= &1}`
    (fun th -> REWRITE_TAC[th])
    THENL
     [CONJ_TAC THEN MATCH_MP_TAC IMAGE_EQ THEN REWRITE_TAC[SCH2_IN_C0; IN_ELIM_THM] THEN
      X_GEN_TAC `x:complex` THEN DISCH_TAC THENL
       [USE_THEN "CIN" MATCH_MP_TAC; USE_THEN "COUT" MATCH_MP_TAC] THEN
      UNDISCH_TAC `&0 < e` THEN UNDISCH_TAC `e <= &1 / &10` THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "INIM" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "NEST" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
    (* c is f on the outer collar. *)
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN X_GEN_TAC `x:complex` THEN STRIP_TAC THEN
    USE_THEN "COUT" MATCH_MP_TAC THEN
    UNDISCH_TAC `&3 / &4 < norm(x:complex)` THEN UNDISCH_TAC `e <= &1 / &10` THEN
    UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Reductions.  Orientation of a neck (the sign of                          *)
(* |f_z|^2 - |f_zbar|^2 = det Df is constant on the connected annulus),     *)
(* composition with cnj and with the inversion, and SCH_R2, SCH_COLLAR2.     *)
(* ------------------------------------------------------------------------- *)

let SCH2_DIFFEO_DERIV_INJ = prove
 (`!(f:real^N->real^N) g s t x h.
        diffeomorphism_on s t f g /\ x IN s /\ frechet_derivative f (at x) h = vec 0
        ==> h = vec 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(f:real^N->real^N) x IN t` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (f:real^N->real^N) s = t` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(f has_derivative frechet_derivative (f:real^N->real^N) (at x)) (at x) /\
    (g has_derivative frechet_derivative (g:real^N->real^N) (at (f x))) (at (f x))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `f:real^N->real^N`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    MP_TAC(ISPECL [`t:real^N->bool`; `g:real^N->real^N`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((g:real^N->real^N) o (f:real^N->real^N) has_derivative
     frechet_derivative g (at (f x)) o frechet_derivative f (at x)) (at x)`
  ASSUME_TAC THENL [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\y:real^N. y) has_derivative
     frechet_derivative (g:real^N->real^N) (at (f x)) o frechet_derivative f (at x)) (at x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `(g:real^N->real^N) o (f:real^N->real^N)` THEN
    MP_TAC(ISPEC `s:real^N->bool` OPEN_CONTAINS_BALL) THEN
    REWRITE_TAC[ASSUME `open(s:real^N->bool)`] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN REWRITE_TAC[ASSUME `(x:real^N) IN s`] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN EXISTS_TAC `r:real` THEN
    ASM_REWRITE_TAC[o_THM] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `s:real^N->bool`)) (concl th) &&
      is_imp(snd(strip_forall(concl th))))) THEN
    UNDISCH_TAC `ball(x:real^N,r) SUBSET s` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (g:real^N->real^N) (at (f x)) o
    frechet_derivative (f:real^N->real^N) (at x) = (\h. h)`
  MP_TAC THENL
   [MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_AT THEN
    MAP_EVERY EXISTS_TAC [`\y:real^N. y`; `x:real^N`] THEN
    ASM_REWRITE_TAC[HAS_DERIVATIVE_ID];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o C AP_THM `h:real^N`) THEN ASM_REWRITE_TAC[o_THM] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC(ISPEC `frechet_derivative (g:real^N->real^N) (at ((f:real^N->real^N) x))`
    LINEAR_0) THEN
  UNDISCH_TAC `(g has_derivative frechet_derivative (g:real^N->real^N) (at (f x)))
               (at ((f:real^N->real^N) x))` THEN
  SIMP_TAC[has_derivative]);;

let SCH2_DIFFEO_DET_NZ = prove
 (`!(f:real^N->real^N) g s t x.
        diffeomorphism_on s t f g /\ x IN s ==> ~(det(jacobian f (at x)) = &0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(f:real^N->real^N) differentiable at x` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^N->bool` THEN
    UNDISCH_TAC `diffeomorphism_on s t (f:real^N->real^N) g` THEN
    SIMP_TAC[diffeomorphism_on] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `det(jacobian (f:real^N->real^N) (at x)) = &0` THEN
  REWRITE_TAC[GSYM HOMOGENEOUS_LINEAR_EQUATIONS_DET; jacobian] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MATRIX_WORKS (MATCH_MP LINEAR_FRECHET_DERIVATIVE th)]) THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `~(h:real^N = vec 0)` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC SCH2_DIFFEO_DERIV_INJ THEN
  MAP_EVERY EXISTS_TAC [`f:real^N->real^N`; `g:real^N->real^N`; `s:real^N->bool`;
                        `t:real^N->bool`; `x:real^N`] THEN
  ASM_REWRITE_TAC[]);;

let SCH2_WIRT_DET = prove
 (`!f:complex->complex z.
        norm(wirtinger_dz f z) pow 2 - norm(wirtinger_dbar f z) pow 2 =
        det(jacobian f (at z))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[wirtinger_dz; wirtinger_dbar; COMPLEX_SQNORM; DET_2] THEN
  REWRITE_TAC[RE_DIV_CX; IM_DIV_CX; RE; IM] THEN REAL_ARITH_TAC);;

(* A diffeomorphism of a connected annulus preserves or reverses orientation. *)

let SCH2_ORIENT_DICHOTOMY = prove
 (`!(f:complex->complex) f' a b.
        diffeomorphism_on (annulus a b) (IMAGE f (annulus a b)) f f'
        ==> (!z. z IN annulus a b ==> norm(wirtinger_dbar f z) < norm(wirtinger_dz f z)) \/
            (!z. z IN annulus a b ==> norm(wirtinger_dz f z) < norm(wirtinger_dbar f z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on (annulus a b) (f:complex->complex)` ASSUME_TAC THENL
   [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
  ABBREV_TAC `D = \z. norm(wirtinger_dz (f:complex->complex) z) - norm(wirtinger_dbar f z)` THEN
  SUBGOAL_THEN `!z. z IN annulus a b ==> ~((D:complex->real) z = &0)` (LABEL_TAC "DNZ") THENL
   [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN EXPAND_TAC "D" THEN
    REWRITE_TAC[REAL_SUB_0] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`f:complex->complex`; `f':complex->complex`; `annulus a b:complex->bool`;
                   `IMAGE (f:complex->complex) (annulus a b)`; `z:complex`]
      SCH2_DIFFEO_DET_NZ) THEN
    ASM_REWRITE_TAC[GSYM SCH2_WIRT_DET; REAL_SUB_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z. lift((D:complex->real) z)) continuous_on annulus a b` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MP_TAC(ISPECL [`annulus a b:complex->bool`; `f:complex->complex`] SCH2_WIRT_SMOOTH_ON) THEN
    ASM_SIMP_TAC[OPEN_ANNULUS];
    ALL_TAC] THEN
  ABBREV_TAC `e1 = {z | z IN annulus a b /\
                        (\z. lift((D:complex->real) z)) z IN {x:real^1 | x$1 > &0}}` THEN
  ABBREV_TAC `e2 = {z | z IN annulus a b /\
                        (\z. lift((D:complex->real) z)) z IN {x:real^1 | x$1 < &0}}` THEN
  SUBGOAL_THEN `open(e1:complex->bool) /\ open(e2:complex->bool)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e1" THEN EXPAND_TAC "e2" THEN CONJ_TAC THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_REWRITE_TAC[OPEN_ANNULUS; OPEN_HALFSPACE_COMPONENT_GT; OPEN_HALFSPACE_COMPONENT_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN e1 <=> z IN annulus a b /\ &0 < (D:complex->real) z` (LABEL_TAC "E1")
  THENL [EXPAND_TAC "e1" THEN REWRITE_TAC[IN_ELIM_THM; LIFT_COMPONENT; real_gt]; ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN e2 <=> z IN annulus a b /\ (D:complex->real) z < &0` (LABEL_TAC "E2")
  THENL [EXPAND_TAC "e2" THEN REWRITE_TAC[IN_ELIM_THM; LIFT_COMPONENT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real`; `b:real`] SCH2_CONNECTED_ANN) THEN
  REWRITE_TAC[connected; NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`e1:complex->bool`; `e2:complex->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `annulus a b SUBSET (e1:complex->bool) UNION e2 /\
                e1 INTER e2 INTER annulus a b = ({}:complex->bool)` (fun th -> REWRITE_TAC[th])
  THENL
   [REWRITE_TAC[SUBSET; IN_UNION; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    USE_THEN "E1" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "E2" (fun th -> REWRITE_TAC[th]) THEN
    CONJ_TAC THENL
     [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "DNZ" (MP_TAC o C MP (ASSUME `(z:complex) IN annulus a b`) o SPEC `z:complex`) THEN
      REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THENL
   [DISJ2_TAC; DISJ1_TAC] THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  USE_THEN "DNZ" (MP_TAC o C MP (ASSUME `(z:complex) IN annulus a b`) o SPEC `z:complex`) THENL
   [UNDISCH_TAC `e1 INTER annulus a b = ({}:complex->bool)`;
    UNDISCH_TAC `e2 INTER annulus a b = ({}:complex->bool)`] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN
  USE_THEN "E1" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "E2" (fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "D" THEN REAL_ARITH_TAC);;

let SCH2_WIRT_CNJ = prove
 (`!f:complex->complex z.
        f differentiable at (cnj z)
        ==> wirtinger_dz (f o cnj) z = wirtinger_dbar f (cnj z) /\
            wirtinger_dbar (f o cnj) z = wirtinger_dz f (cnj z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FRECHET_DERIVATIVE_WORKS] THEN DISCH_TAC THEN
  SUBGOAL_THEN `((f:complex->complex) o cnj has_derivative
                 frechet_derivative f (at (cnj z)) o cnj) (at z)` ASSUME_TAC THENL
   [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR; LINEAR_CNJ];
    ALL_TAC] THEN
  REWRITE_TAC[WIRTINGER_DZ_FRECHET; WIRTINGER_DBAR_FRECHET] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  REWRITE_TAC[o_THM] THEN
  REWRITE_TAC[MATCH_MP FRECHET_WIRTINGER (ASSUME
    `((f:complex->complex) has_derivative frechet_derivative f (at (cnj z))) (at (cnj z))`)] THEN
  REWRITE_TAC[CNJ_CNJ; CNJ_CX; CNJ_II; CNJ_NEG; GSYM WIRTINGER_DZ_FRECHET;
              GSYM WIRTINGER_DBAR_FRECHET] THEN
  MP_TAC COMPLEX_POW_II_2 THEN CONV_TAC COMPLEX_RING);;

let SCH2_CNJ_SETS = prove
 (`(!a b. IMAGE cnj (annulus a b) = annulus a b) /\
   (!r. IMAGE cnj (sphere(Cx(&0),r)) = sphere(Cx(&0),r)) /\
   (!r. IMAGE cnj (ball(Cx(&0),r)) = ball(Cx(&0),r)) /\
   (!r. IMAGE cnj (cball(Cx(&0),r)) = cball(Cx(&0),r))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; annulus; IN_ELIM_THM; SCH2_IN_C0] THEN
  X_GEN_TAC `w:complex` THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_CNJ] THEN EXISTS_TAC `cnj w` THEN
  ASM_REWRITE_TAC[CNJ_CNJ; COMPLEX_NORM_CNJ]);;

let SCH2_CNJ_DIFFEO = prove
 (`!s:complex->bool. open s /\ IMAGE cnj s = s ==> diffeomorphism_on s s cnj cnj`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[diffeomorphism_on; CNJ_CNJ] THEN
  SUBGOAL_THEN `smooth_map_on s (cnj:complex->complex)` (fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`s:complex->bool`; `\z:complex. z`] SCH2_CNJ_SMOOTH) THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; ETA_AX]);;

(* The collared conclusion for necks whose inner half goes inside. *)

let SCH2_R2_INSIDE = prove
 (`!f f':complex->complex.
     diffeomorphism_on (annulus (&1 / &2) (&2)) (IMAGE f (annulus (&1 / &2) (&2))) f f' /\
     (!z. z IN annulus (&1 / &2) (&1) ==> f z IN inside(IMAGE f (sphere(Cx(&0),&1))))
     ==> ?c c'. diffeomorphism_on (ball(Cx(&0),&2)) (IMAGE c (ball(Cx(&0),&2))) c c' /\
                IMAGE c (cball(Cx(&0),&1)) =
                  IMAGE f (sphere(Cx(&0),&1)) UNION inside(IMAGE f (sphere(Cx(&0),&1))) /\
                (!x. x IN annulus (&3 / &4) (&2) ==> c x = f x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP SCH2_ORIENT_DICHOTOMY) THENL
   [MATCH_MP_TAC SCH2_R2_CORE THEN EXISTS_TAC `f':complex->complex` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN annulus (&1 / &2) (&2) ==> cnj z IN annulus (&1 / &2) (&2)`
  ASSUME_TAC THENL
   [REWRITE_TAC[annulus; IN_ELIM_THM; COMPLEX_NORM_CNJ]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(f:complex->complex) o cnj`; `(cnj:complex->complex) o (f':complex->complex)`]
    SCH2_R2_CORE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `IMAGE ((f:complex->complex) o cnj) (annulus (&1 / &2) (&2)) =
                    IMAGE f (annulus (&1 / &2) (&2))` SUBST1_TAC THENL
       [REWRITE_TAC[IMAGE_o; SCH2_CNJ_SETS]; ALL_TAC] THEN
      MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN
      EXISTS_TAC `annulus (&1 / &2) (&2):complex->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SCH2_CNJ_DIFFEO THEN REWRITE_TAC[OPEN_ANNULUS; SCH2_CNJ_SETS];
      X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(f:complex->complex) differentiable at (cnj z)` ASSUME_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
        EXISTS_TAC `annulus (&1 / &2) (&2):complex->bool` THEN
        ASM_SIMP_TAC[OPEN_ANNULUS] THEN
        UNDISCH_TAC `diffeomorphism_on (annulus (&1 / &2) (&2))
                       (IMAGE (f:complex->complex) (annulus (&1 / &2) (&2))) f f'` THEN
        SIMP_TAC[diffeomorphism_on];
        ALL_TAC] THEN
      ASM_SIMP_TAC[SCH2_WIRT_CNJ];
      REWRITE_TAC[o_THM; IMAGE_o; SCH2_CNJ_SETS] THEN X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `inside:(complex->bool)->complex->bool`)) (concl th))) THEN
      UNDISCH_TAC `(z:complex) IN annulus (&1 / &2) (&1)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM; COMPLEX_NORM_CNJ]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:complex->complex` (X_CHOOSE_THEN `c':complex->complex`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`(c:complex->complex) o cnj`; `(cnj:complex->complex) o (c':complex->complex)`] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `IMAGE ((c:complex->complex) o cnj) (ball(Cx(&0),&2)) =
                  IMAGE c (ball(Cx(&0),&2))` SUBST1_TAC THENL
     [REWRITE_TAC[IMAGE_o; SCH2_CNJ_SETS]; ALL_TAC] THEN
    MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN EXISTS_TAC `ball(Cx(&0),&2)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SCH2_CNJ_DIFFEO THEN
    REWRITE_TAC[OPEN_BALL; SCH2_CNJ_SETS];
    ASM_REWRITE_TAC[IMAGE_o; SCH2_CNJ_SETS];
    X_GEN_TAC `x:complex` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `cnj x IN annulus (&3 / &4) (&2)` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:complex) IN annulus (&3 / &4) (&2)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM; COMPLEX_NORM_CNJ];
      ASM_SIMP_TAC[o_THM; CNJ_CNJ]]]);;

(* The planar core of the smooth Schoenflies theorem, collared form. *)

let SCH_R2 = prove
 (`SCH_R2_STATEMENT`,
  REWRITE_TAC[SCH_R2_STATEMENT; sch_neck; sch_fills; sch_ball; COMPLEX_VEC_0] THEN
  MAP_EVERY X_GEN_TAC [`f:complex->complex`; `f':complex->complex`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(f:complex->complex) continuous_on annulus (&1 / &2) (&2) /\
                (!x y. x IN annulus (&1 / &2) (&2) /\ y IN annulus (&1 / &2) (&2) /\
                       f x = f y ==> x = y)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on (annulus (&1 / &2) (&2))
                   (IMAGE (f:complex->complex) (annulus (&1 / &2) (&2))) f f'` THEN
    REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`f:complex->complex`; `&1 / &2`; `&2`; `&1`] SCH2_SIDES_RADIUS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  STRIP_TAC THENL
   [MP_TAC(SPECL [`f:complex->complex`; `f':complex->complex`] SCH2_R2_INSIDE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:complex->complex` (X_CHOOSE_THEN `c':complex->complex`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`c:complex->complex`; `c':complex->complex`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* The inner half goes outside: compose with the inversion. *)
  ABBREV_TAC `iv = \x:complex. inv(norm x pow 2) % x` THEN
  SUBGOAL_THEN `diffeomorphism_on (annulus (&1 / &2) (&2)) (annulus (&1 / &2) (&2))
                  (iv:complex->complex) iv` ASSUME_TAC THENL
   [MP_TAC(SPECL [`&1 / &2`; `&2`] (INST_TYPE [`:2`,`:N`] SMT_DIFFEO_INVERSION_ANNULUS)) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!x. x IN sphere(Cx(&0),&1) ==> (iv:complex->complex) x = x) /\
                (!z. z IN annulus (&1 / &2) (&1) ==> (iv:complex->complex) z IN annulus (&1) (&2))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "iv" THEN REWRITE_TAC[SCH2_IN_C0] THEN CONJ_TAC THENL
     [SIMP_TAC[REAL_POW_ONE; REAL_INV_1; VECTOR_MUL_LID]; ALL_TAC] THEN
    X_GEN_TAC `z:complex` THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(z:complex = vec 0)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `&1 / &2 < norm(z:complex)` THEN
      ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[SMT_INVERSION_NORM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INV_1_LT THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE ((f:complex->complex) o (iv:complex->complex)) (sphere(Cx(&0),&1)) =
                IMAGE f (sphere(Cx(&0),&1))` ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_o] THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM IMAGE_ID] THEN MATCH_MP_TAC IMAGE_EQ THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(f:complex->complex) o (iv:complex->complex)`; `(iv:complex->complex) o (f':complex->complex)`]
    SCH2_R2_INSIDE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `IMAGE ((f:complex->complex) o (iv:complex->complex)) (annulus (&1 / &2) (&2)) =
                    IMAGE f (annulus (&1 / &2) (&2))` SUBST1_TAC THENL
       [REWRITE_TAC[IMAGE_o] THEN
        UNDISCH_TAC `diffeomorphism_on (annulus (&1 / &2) (&2)) (annulus (&1 / &2) (&2))
                       (iv:complex->complex) iv` THEN
        SIMP_TAC[diffeomorphism_on];
        ALL_TAC] THEN
      MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN
      EXISTS_TAC `annulus (&1 / &2) (&2):complex->bool` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[o_THM] THEN X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `annulus (&1) (&2):complex->bool`)) (concl th) &&
        can (find_term ((=) `inside:(complex->bool)->complex->bool`)) (concl th))) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:complex->complex` (X_CHOOSE_THEN `c':complex->complex`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`c:complex->complex`; `c':complex->complex`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `IMAGE ((f:complex->complex) o (iv:complex->complex)) (sphere(Cx(&0),&1)) =
                IMAGE f (sphere(Cx(&0),&1))`]) THEN
  ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:complex` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `annulus (&3 / &4) (&2):complex->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[o_THM] THEN EXPAND_TAC "iv" THEN REWRITE_TAC[]);;

let SCH_COLLAR2 = prove
 (`SCH_COLLAR2_STATEMENT`,
  REWRITE_TAC[SCH_COLLAR2_STATEMENT] THEN
  MESON_TAC[REWRITE_RULE[SCH_R2_STATEMENT] SCH_R2]);;

