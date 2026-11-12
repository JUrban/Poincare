(* ========================================================================= *)
(* Unit pc_cm_target (for Part 4): the embedded Colding-Minicozzi target of  *)
(* a closed Riemannian manifold and the dictionary between the intrinsic P4  *)
(* vocabulary (the p4_s2 family, pc_p4_defs) and the ambient CM vocabulary   *)
(* (the cm family, pc_cm_defs).                                              *)
(* T1 CM_EMB_EXISTS: cm_emb data exist (embedding layer E1-E8).             *)
(* T2 CM_S2_GRAM: chart Gram matrices of u are ambient Gram matrices of     *)
(* f o u for any pullback pair (R,Q).                                        *)
(* T3 CM_SHELL_INTEGRAL: shell integrals of degree -2 homogeneous functions *)
(* are 3/2 times p4_s2_integral.                                             *)
(* T4 CM_AMBIENT_TENSOR, CM_AMBIENT_RICCI: smooth ambient extensions.       *)
(* T5 CM_P4_BRIDGE: energies, areas and trace integrals agree.              *)
(* T6 CM_SHARMONIC_EQ: harmonic spheres agree.                               *)
(* T7 radial extension calculus.  T8 transfer of regularity and sweepouts. *)
(* ========================================================================= *)

needs "src/pc_cm_defs.ml";;
needs "src/pc_mfd_embmetric.ml";;
needs "src/pc_wan_weak.ml";;
needs "src/pc_grg_rfint.ml";;
needs "src/pc_lrg_flowsmooth.ml";;
needs "src/pc_p4_width.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* T3: integrals of degree -2 homogeneous functions over wan_shell are 3/2   *)
(* times p4_s2_integral.  Only scalings and additivity over annuli are used: *)
(* the annulus integrals of h are linear in the radii (a functional          *)
(* equation), those of the degree 0 function phi z = h(z / |z|) are cubic,   *)
(* and a squeeze on thin annuli fixes the constant.                          *)
(* ------------------------------------------------------------------------- *)

let CMT_IMAGE_SCALE_ANNULUS = prove
 (`!s a b. &0 < s
           ==> IMAGE (\x:real^3. s % x) {z:real^3 | a < norm z /\ norm z < b} =
               {z:real^3 | s * a < norm z /\ norm z < s * b}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < s ==> abs s = s`; REAL_LT_LMUL_EQ];
    STRIP_TAC THEN EXISTS_TAC `inv s % y:real^3` THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < s ==> abs s = s`] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[]]);;

let CMT_HAS_INTEGRAL_SCALE_ANNULUS = prove
 (`!(ff:real^3->real^1) s a b i.
        &0 < s /\ (ff has_integral i) {z:real^3 | a < norm z /\ norm z < b}
        ==> ((\x. ff(inv s % x)) has_integral (s pow 3 % i))
            {z:real^3 | s * a < norm z /\ norm z < s * b}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ff:real^3->real^1`; `i:real^1`;
                 `{z:real^3 | a < norm z /\ norm z < b}`; `inv s:real`; `vec 0:real^3`]
                HAS_INTEGRAL_AFFINITY) THEN
  ASM_SIMP_TAC[REAL_INV_EQ_0; REAL_LT_IMP_NZ; VECTOR_ADD_RID; VECTOR_MUL_RZERO;
               VECTOR_NEG_0; REAL_INV_INV; DIMINDEX_3] THEN
  ASM_SIMP_TAC[CMT_IMAGE_SCALE_ANNULUS] THEN
  SUBGOAL_THEN `inv(abs(inv s) pow 3) = s pow 3` SUBST1_TAC THENL
   [ASM_SIMP_TAC[REAL_ABS_INV; REAL_ARITH `&0 < s ==> abs s = s`; REAL_POW_INV;
                 REAL_INV_INV];
    REWRITE_TAC[]]);;

let CMT_ANNULUS_SPLIT = prove
 (`!(ff:real^3->real^1) a b e i j.
        a < b /\ b < e /\
        (ff has_integral i) {z:real^3 | a < norm z /\ norm z < b} /\
        (ff has_integral j) {z:real^3 | b < norm z /\ norm z < e}
        ==> (ff has_integral (i + j)) {z:real^3 | a < norm z /\ norm z < e}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_SPIKE_SET THEN
  EXISTS_TAC `{z:real^3 | a < norm z /\ norm z < b} UNION
              {z:real^3 | b < norm z /\ norm z < e}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `sphere(vec 0:real^3,b)` THEN
    REWRITE_TAC[NEGLIGIBLE_SPHERE; SUBSET; IN_DIFF; IN_UNION; IN_ELIM_THM;
                IN_SPHERE_0] THEN
    X_GEN_TAC `z:real^3` THEN UNDISCH_TAC `a < b` THEN UNDISCH_TAC `b < e` THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC HAS_INTEGRAL_UNION THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `{}:real^3->bool` THEN
    REWRITE_TAC[NEGLIGIBLE_EMPTY; SUBSET; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    REAL_ARITH_TAC]);;

let CMT_FUNEQ_LINEAR = prove
 (`!c:real->real->real.
        (!s a b. &0 < s /\ &0 < a /\ a < b ==> c (s * a) (s * b) = s * c a b) /\
        (!a b e. &0 < a /\ a < b /\ b < e ==> c a e = c a b + c b e)
        ==> !a b. &0 < a /\ a < b ==> c a b = (b - a) * c (&1) (&2)`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "SC") (LABEL_TAC "AD")) THEN
  SUBGOAL_THEN `!x. &1 < x ==> c (&1) x = (x - &1) * c (&1) (&2)` (LABEL_TAC "GAM") THENL
   [X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    USE_THEN "AD" (MP_TAC o SPECL [`&1`; `x:real`; `&2 * x`]) THEN
    USE_THEN "AD" (MP_TAC o SPECL [`&1`; `&2`; `&2 * x`]) THEN
    USE_THEN "SC" (MP_TAC o SPECL [`x:real`; `&1`; `&2`]) THEN
    USE_THEN "SC" (MP_TAC o SPECL [`&2`; `&1`; `x:real`]) THEN
    REWRITE_TAC[REAL_MUL_RID] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `x * &2 = &2 * x`] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `a * (b / a) = b` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 < b / a` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_MUL_LID]; ALL_TAC] THEN
  USE_THEN "SC" (MP_TAC o SPECL [`a:real`; `&1`; `b / a`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LT_01]; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_MUL_RID] THEN DISCH_THEN SUBST1_TAC THEN
  USE_THEN "GAM" (MP_TAC o C MATCH_MP (ASSUME `&1 < b / a`)) THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[REAL_MUL_ASSOC; REAL_SUB_LDISTRIB; REAL_MUL_RID]);;

let CMT_LE_EPS = prove
 (`!x c. &0 <= c /\ (!e. &0 < e /\ e <= &1 ==> x <= e * c) ==> x <= &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &2 * c + &2` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 <= c` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `min (&1) (x / (&2 * c + &2))`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL; REAL_LT_01] THEN
    ASM_SIMP_TAC[REAL_LT_DIV];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `y < x ==> x <= y ==> F`) THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `x / (&2 * c + &2) * c` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `x / (&2 * c + &2) * c = (x * c) / (&2 * c + &2)` SUBST1_TAC THENL
   [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
  SUBGOAL_THEN `&0 <= x * c` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `&0 < x` THEN REAL_ARITH_TAC);;

let CMT_SQUEEZE = prove
 (`!k i. &0 <= i /\
         (!e. &0 < e /\ e <= &1
              ==> inv((&1 + e) pow 2) * (((&1 + e) pow 3 - &1) * i) <= e * k /\
                  e * k <= ((&1 + e) pow 3 - &1) * i)
         ==> k = &3 * i`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SQ")) THEN
  MATCH_MP_TAC(REAL_ARITH `k - &3 * i <= &0 /\ &3 * i - k <= &0 ==> k = &3 * i`) THEN
  CONJ_TAC THEN MATCH_MP_TAC CMT_LE_EPS THENL
   [EXISTS_TAC `&4 * i` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `e:real` THEN STRIP_TAC THEN
    USE_THEN "SQ" (MP_TAC o CONJUNCT2 o C MATCH_MP (CONJ (ASSUME `&0 < e`)
      (ASSUME `e <= &1`))) THEN
    SUBGOAL_THEN `((&1 + e) pow 3 - &1) * i = e * ((&3 + &3 * e + e pow 2) * i)`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN
    SUBGOAL_THEN `&0 <= e * i /\ e * i <= i /\ e * (e * i) <= e * i` MP_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `&0 <= (&1 - e) * i ==> e * i <= i`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `&0 <= (&1 - e) * (e * i) ==> e * (e * i) <= e * i`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    EXISTS_TAC `abs(&2 * k - &3 * i) + abs(k - i)` THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `e:real` THEN STRIP_TAC THEN
    USE_THEN "SQ" (MP_TAC o CONJUNCT1 o C MATCH_MP (CONJ (ASSUME `&0 < e`)
      (ASSUME `e <= &1`))) THEN
    SUBGOAL_THEN `&0 < (&1 + e) pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [REAL_MUL_SYM] THEN
    REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    SUBGOAL_THEN
     `(((&1 + e) pow 3 - &1) * i <= (e * k) * (&1 + e) pow 2) <=>
      e * ((&3 + &3 * e + e pow 2) * i) <= e * ((&1 + &2 * e + e pow 2) * k)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `a = c /\ b = d ==> (a <= b <=> c <= d)`) THEN
      CONJ_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN DISCH_TAC THEN
    SUBGOAL_THEN `e * (&2 * k - &3 * i) <= e * abs(&2 * k - &3 * i)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `e pow 2 * (k - i) <= e * abs(k - i)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e pow 2 * abs(k - i)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS; REAL_POW_2] THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    UNDISCH_TAC `(&3 + &3 * e + e pow 2) * i <= (&1 + &2 * e + e pow 2) * k` THEN
    UNDISCH_TAC `e * (&2 * k - &3 * i) <= e * abs(&2 * k - &3 * i)` THEN
    UNDISCH_TAC `e pow 2 * (k - i) <= e * abs(k - i)` THEN REAL_ARITH_TAC]);;

let CMT_HOMOG_DECOMP = prove
 (`!(h:real^3->real) z.
        (!t z. &0 < t /\ ~(z = vec 0) ==> h(t % z) = inv(t pow 2) * h z) /\
        ~(z = vec 0)
        ==> h z = inv(norm z pow 2) * h(inv(norm z) % z)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`norm(z:real^3)`; `inv(norm z) % z:real^3`]) THEN
  ASM_SIMP_TAC[NORM_POS_LT; VECTOR_MUL_ASSOC; REAL_MUL_RINV; NORM_EQ_0; VECTOR_MUL_LID;
               VECTOR_MUL_EQ_0; REAL_INV_EQ_0]);;


let CMT_ANNULUS_OPEN_BOUNDED = prove
 (`!a b. open {z:real^3 | a < norm z /\ norm z < b} /\
         bounded {z:real^3 | a < norm z /\ norm z < b} /\
         lebesgue_measurable {z:real^3 | a < norm z /\ norm z < b}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{z:real^3 | a < norm z /\ norm z < b} = ball(vec 0,b) DIFF cball(vec 0,a)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_BALL_0; IN_CBALL_0] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[OPEN_DIFF; OPEN_BALL; CLOSED_CBALL; BOUNDED_DIFF; BOUNDED_BALL;
           LEBESGUE_MEASURABLE_OPEN]);;

let CMT_HOMOG_BOUND = prove
 (`!(h:real^3->real) B a z.
        (!y. y IN sphere(vec 0,&1) ==> abs(h y) <= B) /\
        (!t z. &0 < t /\ ~(z = vec 0) ==> h(t % z) = inv(t pow 2) * h z) /\
        &0 < a /\ a <= norm z
        ==> abs(h z) <= B / a pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(z:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `a <= norm(z:real^3)` THEN
    ASM_REWRITE_TAC[NORM_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:real^3->real`; `z:real^3`] CMT_HOMOG_DECOMP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `abs((h:real^3->real)(inv(norm z) % z)) <= B` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[P4_RADIAL_SPHERE]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_NORM] THEN
  REWRITE_TAC[real_div] THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_INV THEN REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC);;

let CMT_HOMOG_ABS_INTEGRABLE = prove
 (`!(h:real^3->real) B a b.
        (\z. lift(h z)) measurable_on (:real^3) /\
        (!y. y IN sphere(vec 0,&1) ==> abs(h y) <= B) /\
        (!t z. &0 < t /\ ~(z = vec 0) ==> h(t % z) = inv(t pow 2) * h z) /\
        &0 < a
        ==> (\z. lift(h z)) absolutely_integrable_on
            {z:real^3 | a < norm z /\ norm z < b}`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
  EXISTS_TAC `(\z. lift(B / a pow 2)):real^3->real^1` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(:real^3)` THEN ASM_REWRITE_TAC[SUBSET_UNIV; CMT_ANNULUS_OPEN_BOUNDED];
    REWRITE_TAC[INTEGRABLE_ON_CONST] THEN DISJ2_TAC THEN
    MATCH_MP_TAC MEASURABLE_OPEN THEN REWRITE_TAC[CMT_ANNULUS_OPEN_BOUNDED];
    REWRITE_TAC[IN_ELIM_THM; NORM_LIFT; LIFT_DROP] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC CMT_HOMOG_BOUND THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

let CMT_PHI_PROPS = prove
 (`!(h:real^3->real) B.
        (\z. lift(h z)) measurable_on (:real^3) /\
        (!y. y IN sphere(vec 0,&1) ==> abs(h y) <= B) /\
        (!t z. &0 < t /\ ~(z = vec 0) ==> h(t % z) = inv(t pow 2) * h z)
        ==> (!s z. &0 < s
                   ==> h(inv(norm(s % z)) % (s % z)) = h(inv(norm z) % z)) /\
            (!a b. (\z. lift(h(inv(norm z) % z))) absolutely_integrable_on
                   {z:real^3 | a < norm z /\ norm z < b})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[NORM_MUL; VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < s ==> abs s = s`] THEN
    ASM_CASES_TAC `z:real^3 = vec 0` THEN ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `~(norm(z:real^3) = &0)` MP_TAC THENL
     [ASM_REWRITE_TAC[NORM_EQ_0]; ALL_TAC] THEN
    UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
  EXISTS_TAC `(\z. lift(max B (abs((h:real^3->real)(vec 0))))):real^3->real^1` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(:real^3)` THEN REWRITE_TAC[SUBSET_UNIV; CMT_ANNULUS_OPEN_BOUNDED] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] MEASURABLE_ON_SPIKE) THEN
    EXISTS_TAC `\z:real^3. lift(norm z pow 2 * h z)` THEN
    EXISTS_TAC `{vec 0:real^3}` THEN REWRITE_TAC[NEGLIGIBLE_SING; IN_DIFF; IN_UNIV;
        IN_SING] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN AP_TERM_TAC THEN
      MP_TAC(ISPECL [`h:real^3->real`; `z:real^3`] CMT_HOMOG_DECOMP) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
          [th]) THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN
      SUBGOAL_THEN `~(norm(z:real^3) pow 2 = &0)` MP_TAC THENL
       [ASM_REWRITE_TAC[REAL_POW_EQ_0; NORM_EQ_0] THEN ARITH_TAC; ALL_TAC] THEN
      CONV_TAC REAL_FIELD;
      MATCH_MP_TAC MEASURABLE_ON_LIFT_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN
      MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[REAL_POW_2; LIFT_CMUL] THEN
      MATCH_MP_TAC CONTINUOUS_MUL THEN
      REWRITE_TAC[CONTINUOUS_AT_LIFT_NORM; REWRITE_RULE[o_DEF] CONTINUOUS_AT_LIFT_NORM]];
    REWRITE_TAC[INTEGRABLE_ON_CONST] THEN DISJ2_TAC THEN
    MATCH_MP_TAC MEASURABLE_OPEN THEN REWRITE_TAC[CMT_ANNULUS_OPEN_BOUNDED];
    REWRITE_TAC[IN_ELIM_THM; NORM_LIFT; LIFT_DROP] THEN X_GEN_TAC `z:real^3` THEN
    DISCH_TAC THEN ASM_CASES_TAC `z:real^3 = vec 0` THENL
     [ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `x <= B ==> x <= max B c`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[P4_RADIAL_SPHERE]]]);;


let CMT_BALL_AS_ANNULUS = prove
 (`!a b. &0 < a /\ &0 < b
         ==> {z:real^3 | --b < norm z /\ norm z < a} =
             {z:real^3 | --a < norm z /\ norm z < a} /\
             ball(vec 0:real^3,a) = {z:real^3 | --a < norm z /\ norm z < a}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_BALL_0] THEN
  X_GEN_TAC `z:real^3` THEN MP_TAC(ISPEC `z:real^3` NORM_POS_LE) THEN
  ASM_REAL_ARITH_TAC);;

let CMT_SHELL_LINEAR = prove
 (`!(h:real^3->real) B.
        (\z. lift(h z)) measurable_on (:real^3) /\
        (!y. y IN sphere(vec 0,&1) ==> abs(h y) <= B) /\
        (!t z. &0 < t /\ ~(z = vec 0) ==> h(t % z) = inv(t pow 2) * h z)
        ==> !a b. &0 < a /\ a < b
                  ==> drop(integral {z:real^3 | a < norm z /\ norm z < b}
                                    (\z. lift(h z))) =
                      (b - a) *
                      drop(integral {z:real^3 | &1 < norm z /\ norm z < &2}
                                    (\z. lift(h z)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "HOM"))) THEN
  ABBREV_TAC
   `c = \a b. drop(integral {z:real^3 | a < norm z /\ norm z < b}
                            (\z. lift((h:real^3->real) z)))` THEN
  SUBGOAL_THEN
   `!a b. drop(integral {z:real^3 | a < norm z /\ norm z < b}
                        (\z. lift((h:real^3->real) z))) = (c:real->real->real) a b`
  (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "c" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. &0 < a
          ==> ((\z. lift((h:real^3->real) z)) has_integral lift((c:real->real->real) a b))
              {z:real^3 | a < norm z /\ norm z < b}`
  (LABEL_TAC "HI") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "c" THEN REWRITE_TAC[LIFT_DROP] THEN
    REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL] THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC CMT_HOMOG_ABS_INTEGRABLE THEN EXISTS_TAC `B:real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CMT_FUNEQ_LINEAR THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&0 < s * a` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
    USE_THEN "HI" (MP_TAC o C MATCH_MP (ASSUME `&0 < a`) o SPECL [`a:real`; `b:real`]) THEN
    DISCH_THEN(MP_TAC o MATCH_MP CMT_HAS_INTEGRAL_SCALE_ANNULUS o CONJ (ASSUME `&0 < s`))
        THEN
    DISCH_THEN(MP_TAC o SPEC `inv(s pow 2)` o MATCH_MP HAS_INTEGRAL_CMUL) THEN
    REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `((\z. lift((h:real^3->real) z)) has_integral
       (inv(s pow 2) % s pow 3 % lift((c:real->real->real) a b)))
      {z:real^3 | s * a < norm z /\ norm z < s * b}`
    MP_TAC THENL
     [MATCH_MP_TAC HAS_INTEGRAL_EQ THEN
      EXISTS_TAC `\x:real^3. inv(s pow 2) % lift((h:real^3->real)(inv s % x))` THEN
      CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
      X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `s * a < norm(x:real^3)` THEN
        ASM_REWRITE_TAC[NORM_0; REAL_NOT_LT] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      USE_THEN "HOM" (MP_TAC o SPECL [`inv s:real`; `x:real^3`]) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV_EQ]; DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[LIFT_CMUL; VECTOR_MUL_ASSOC; REAL_POW_INV; REAL_INV_INV] THEN
      SUBGOAL_THEN `inv(s pow 2) * s pow 2 = &1` (fun th -> REWRITE_TAC[th;
          VECTOR_MUL_LID]) THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN
      ASM_SIMP_TAC[REAL_POW_EQ_0; REAL_LT_IMP_NZ];
      ALL_TAC] THEN
    USE_THEN "HI" (MP_TAC o C MATCH_MP (ASSUME `&0 < s * a`) o SPECL [`s * a`; `s * b`])
        THEN
    DISCH_THEN(fun th1 -> DISCH_THEN(fun th2 ->
      MP_TAC(MATCH_MP HAS_INTEGRAL_UNIQUE (CONJ th1 th2)))) THEN
    DISCH_THEN(MP_TAC o AP_TERM `drop`) THEN
    REWRITE_TAC[LIFT_DROP; DROP_CMUL] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `~(s = &0)` MP_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_NZ]; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\z. lift((h:real^3->real) z)`; `a:real`; `b:real`; `e:real`;
                   `lift((c:real->real->real) a b)`; `lift((c:real->real->real) b e)`]
                  CMT_ANNULUS_SPLIT) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN USE_THEN "HI" MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "HI" (MP_TAC o C MATCH_MP (ASSUME `&0 < a`) o SPECL [`a:real`; `e:real`]) THEN
    DISCH_THEN(fun th1 -> DISCH_THEN(fun th2 ->
      MP_TAC(MATCH_MP HAS_INTEGRAL_UNIQUE (CONJ th1 th2)))) THEN
    REWRITE_TAC[GSYM LIFT_ADD; LIFT_EQ]]);;

let CMT_PHI_THIN = prove
 (`!(h:real^3->real) B.
        (\z. lift(h z)) measurable_on (:real^3) /\
        (!y. y IN sphere(vec 0,&1) ==> abs(h y) <= B) /\
        (!t z. &0 < t /\ ~(z = vec 0) ==> h(t % z) = inv(t pow 2) * h z)
        ==> !e. &0 < e
                ==> drop(integral {z:real^3 | &1 < norm z /\ norm z < &1 + e}
                                  (\z. lift(h(inv(norm z) % z)))) =
                    ((&1 + e) pow 3 - &1) *
                    drop(integral (ball(vec 0:real^3,&1))
                                  (\z. lift(h(inv(norm z) % z))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CMT_PHI_PROPS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "PH") (LABEL_TAC "PI")) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  REWRITE_TAC[CONJUNCT2(MP (SPECL [`&1`; `&1`] CMT_BALL_AS_ANNULUS)
                           (REAL_ARITH `&0 < &1 /\ &0 < &1`))] THEN
  SUBGOAL_THEN
   `!a b. ((\z. lift((h:real^3->real)(inv(norm z) % z))) has_integral
           integral {z:real^3 | a < norm z /\ norm z < b} (\z. lift(h(inv(norm z) % z))))
          {z:real^3 | a < norm z /\ norm z < b}`
  (LABEL_TAC "HI") THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL] THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    USE_THEN "PI" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\z. lift((h:real^3->real)(inv(norm z) % z))) has_integral
     ((&1 + e) pow 3 %
      integral {z:real^3 | -- &1 < norm z /\ norm z < &1} (\z. lift(h(inv(norm z) % z)))))
    {z:real^3 | --(&1 + e) < norm z /\ norm z < &1 + e}`
  (LABEL_TAC "SC") THENL
   [MP_TAC(ISPECL [`\z. lift((h:real^3->real)(inv(norm z) % z))`; `&1 + e`; `-- &1`; `&1`;
                   `integral {z:real^3 | -- &1 < norm z /\ norm z < &1}
                             (\z. lift((h:real^3->real)(inv(norm z) % z)))`]
                  CMT_HAS_INTEGRAL_SCALE_ANNULUS) THEN
    ANTS_TAC THENL [USE_THEN "HI" (fun th -> REWRITE_TAC[th]) THEN ASM_REAL_ARITH_TAC;
                    ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_RNEG; REAL_MUL_RID] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_EQ) THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
    USE_THEN "PH" (MP_TAC o SPECL [`inv(&1 + e)`; `x:real^3`]) THEN
    ANTS_TAC THENL [REWRITE_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z. lift((h:real^3->real)(inv(norm z) % z))`; `-- &1`; `&1`; `&1 + e`;
                 `integral {z:real^3 | -- &1 < norm z /\ norm z < &1}
                           (\z. lift((h:real^3->real)(inv(norm z) % z)))`;
                 `integral {z:real^3 | &1 < norm z /\ norm z < &1 + e}
                           (\z. lift((h:real^3->real)(inv(norm z) % z)))`]
                CMT_ANNULUS_SPLIT) THEN
  ANTS_TAC THENL [USE_THEN "HI" (fun th -> REWRITE_TAC[th]) THEN ASM_REAL_ARITH_TAC;
                  ALL_TAC] THEN
  MP_TAC(SPECL [`&1 + e`; `&1`] CMT_BALL_AS_ANNULUS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o CONJUNCT1)] THEN
  DISCH_THEN(fun th2 -> REMOVE_THEN "SC" (fun th1 ->
    MP_TAC(MATCH_MP HAS_INTEGRAL_UNIQUE (CONJ th1 th2)))) THEN
  DISCH_THEN(MP_TAC o AP_TERM `drop`) THEN REWRITE_TAC[DROP_ADD; DROP_CMUL] THEN
  MATCH_ACCEPT_TAC(REAL_ARITH `!i j s. s * i = i + j ==> j = (s - &1) * i`));;

let CMT_THIN_POINTWISE = prove
 (`!(h:real^3->real) e z.
        (!t z. &0 < t /\ ~(z = vec 0) ==> h(t % z) = inv(t pow 2) * h z) /\
        (!z. &0 <= h z) /\ &0 < e /\ &1 < norm z /\ norm z < &1 + e
        ==> inv((&1 + e) pow 2) * h(inv(norm z) % z) <= h z /\
            h z <= h(inv(norm z) % z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(z:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `&1 < norm(z:real^3)` THEN ASM_REWRITE_TAC[NORM_0] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:real^3->real`; `z:real^3`] CMT_HOMOG_DECOMP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `&0 <= (h:real^3->real)(inv(norm z) % z)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC(REAL_ARITH `x * p <= &1 * p ==> x * p <= p`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_INV_LE_1 THEN MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REAL_ARITH_TAC]);;

let CMT_SHELL_NONNEG = prove
 (`!(h:real^3->real) B.
        (\z. lift(h z)) measurable_on (:real^3) /\
        (!y. y IN sphere(vec 0,&1) ==> abs(h y) <= B) /\
        (!t z. &0 < t /\ ~(z = vec 0) ==> h(t % z) = inv(t pow 2) * h z) /\
        (!z. &0 <= h z)
        ==> drop(integral wan_shell (\z. lift(h z))) = &3 / &2 * p4_s2_integral h`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "HOM") (LABEL_TAC "POS")))) THEN
  SUBGOAL_THEN
   `(\z. lift((h:real^3->real) z)) measurable_on (:real^3) /\
    (!y. y IN sphere(vec 0,&1) ==> abs(h y) <= B) /\
    (!t z. &0 < t /\ ~(z = vec 0) ==> h(t % z) = inv(t pow 2) * h z)`
  (LABEL_TAC "H") THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "H" (LABEL_TAC "LIN" o MATCH_MP CMT_SHELL_LINEAR) THEN
  USE_THEN "H" (LABEL_TAC "THIN" o MATCH_MP CMT_PHI_THIN) THEN
  USE_THEN "H" (LABEL_TAC "PI" o CONJUNCT2 o MATCH_MP CMT_PHI_PROPS) THEN
  SUBGOAL_THEN
   `!a b. &0 < a ==> (\z. lift((h:real^3->real) z)) integrable_on
                     {z:real^3 | a < norm z /\ norm z < b}`
  (LABEL_TAC "HINT") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC CMT_HOMOG_ABS_INTEGRABLE THEN EXISTS_TAC `B:real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. (\z. lift((h:real^3->real)(inv(norm z) % z))) integrable_on
          {z:real^3 | a < norm z /\ norm z < b}`
  (LABEL_TAC "PINT") THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    USE_THEN "PI" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  REWRITE_TAC[wan_shell; p4_s2_integral] THEN
  USE_THEN "LIN" (MP_TAC o SPECL [`&1 / &2`; `&2`]) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  SUBGOAL_THEN
   `drop(integral {z:real^3 | &1 < norm z /\ norm z < &2} (\z. lift((h:real^3->real) z))) =
    &3 * drop(integral (ball(vec 0:real^3,&1)) (\z. lift(h(inv(norm z) % z))))`
  (fun th -> REWRITE_TAC[th] THEN REAL_ARITH_TAC) THEN
  MATCH_MP_TAC CMT_SQUEEZE THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_POS THEN
    REWRITE_TAC[CONJUNCT2(MP (SPECL [`&1`; `&1`] CMT_BALL_AS_ANNULUS)
                             (REAL_ARITH `&0 < &1 /\ &0 < &1`))] THEN
    USE_THEN "PINT" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[LIFT_DROP];
    ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  USE_THEN "LIN" (MP_TAC o SPECL [`&1`; `&1 + e`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(&1 + e) - &1 = e`] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  USE_THEN "THIN" (MP_TAC o C MATCH_MP (ASSUME `&0 < e`) o SPEC `e:real`) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`\z. lift((h:real^3->real)(inv(norm z) % z))`; `inv((&1 + e) pow 2)`;
                   `{z:real^3 | &1 < norm z /\ norm z < &1 + e}`] INTEGRAL_CMUL) THEN
    USE_THEN "PINT" (fun th -> REWRITE_TAC[th]) THEN
    DISCH_THEN(MP_TAC o AP_TERM `drop`) THEN REWRITE_TAC[DROP_CMUL] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC INTEGRAL_DROP_LE THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_CMUL THEN USE_THEN "PINT" (fun th -> REWRITE_TAC[th]);
      USE_THEN "HINT" MATCH_MP_TAC THEN REAL_ARITH_TAC;
      REWRITE_TAC[IN_ELIM_THM; DROP_CMUL; LIFT_DROP] THEN X_GEN_TAC `x:real^3` THEN
      STRIP_TAC THEN
      MP_TAC(ISPECL [`h:real^3->real`; `e:real`; `x:real^3`] CMT_THIN_POINTWISE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ACCEPT_TAC o CONJUNCT1)]];
    MATCH_MP_TAC INTEGRAL_DROP_LE THEN REPEAT CONJ_TAC THENL
     [USE_THEN "HINT" MATCH_MP_TAC THEN REAL_ARITH_TAC;
      USE_THEN "PINT" (fun th -> REWRITE_TAC[th]);
      REWRITE_TAC[IN_ELIM_THM; LIFT_DROP] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`h:real^3->real`; `e:real`; `x:real^3`] CMT_THIN_POINTWISE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ACCEPT_TAC o CONJUNCT2)]]]);;

let CMT_HOMOG_PARTS = prove
 (`!(h:real^3->real) B s.
        (\z. lift(h z)) measurable_on (:real^3) /\
        (!y. y IN sphere(vec 0,&1) ==> abs(h y) <= B) /\
        (!t z. &0 < t /\ ~(z = vec 0) ==> h(t % z) = inv(t pow 2) * h z) /\
        abs s = &1
        ==> (\z. lift((abs(h z) + s * h z) / &2)) measurable_on (:real^3) /\
            (!y. y IN sphere(vec 0,&1) ==> abs((abs(h y) + s * h y) / &2) <= abs B) /\
            (!t z. &0 < t /\ ~(z = vec 0)
                   ==> (abs(h(t % z)) + s * h(t % z)) / &2 =
                       inv(t pow 2) * ((abs(h z) + s * h z) / &2)) /\
            (!z. &0 <= (abs(h z) + s * h z) / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z:real^3. abs(s * (h:real^3->real) z) = abs(h z)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_ABS_MUL; REAL_MUL_LID]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `(\z. lift((abs((h:real^3->real) z) + s * h z) / &2)) =
                  (\z. inv(&2) % (lift(norm(lift(h z))) + s % lift(h z)))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
      REWRITE_TAC[NORM_LIFT; GSYM LIFT_CMUL; GSYM LIFT_ADD] THEN AP_TERM_TAC THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC MEASURABLE_ON_CMUL THEN MATCH_MP_TAC MEASURABLE_ON_ADD THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_ON_NORM THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MEASURABLE_ON_CMUL THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `abs((h:real^3->real) y) <= B` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `y:real^3`) THEN REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`t:real`; `z:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_POW;
                 REAL_ARITH `&0 < t ==> abs t = t`] THEN
    REAL_ARITH_TAC;
    GEN_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `z:real^3`) THEN REAL_ARITH_TAC]);;

let CMT_SHELL_SUB = prove
 (`!(h1:real^3->real) h2 B1 B2.
        (\z. lift(h1 z)) measurable_on (:real^3) /\
        (!y. y IN sphere(vec 0,&1) ==> abs(h1 y) <= B1) /\
        (!t z. &0 < t /\ ~(z = vec 0) ==> h1(t % z) = inv(t pow 2) * h1 z) /\
        (\z. lift(h2 z)) measurable_on (:real^3) /\
        (!y. y IN sphere(vec 0,&1) ==> abs(h2 y) <= B2) /\
        (!t z. &0 < t /\ ~(z = vec 0) ==> h2(t % z) = inv(t pow 2) * h2 z)
        ==> drop(integral wan_shell (\z. lift(h1 z - h2 z))) =
            drop(integral wan_shell (\z. lift(h1 z))) -
            drop(integral wan_shell (\z. lift(h2 z))) /\
            p4_s2_integral (\z. h1 z - h2 z) = p4_s2_integral h1 - p4_s2_integral h2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\z. lift((h1:real^3->real) z)) integrable_on wan_shell /\
                (\z. lift((h2:real^3->real) z)) integrable_on wan_shell`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[wan_shell] THEN CONJ_TAC THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC CMT_HOMOG_ABS_INTEGRABLE THENL
     [EXISTS_TAC `B1:real`; EXISTS_TAC `B2:real`] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. lift((h1:real^3->real)(inv(norm z) % z))) integrable_on ball(vec 0:real^3,&1) /\
    (\z. lift((h2:real^3->real)(inv(norm z) % z))) integrable_on ball(vec 0:real^3,&1)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[CONJUNCT2(MP (SPECL [`&1`; `&1`] CMT_BALL_AS_ANNULUS)
                             (REAL_ARITH `&0 < &1 /\ &0 < &1`))] THEN
    CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THENL
     [MP_TAC(ISPECL [`h1:real^3->real`; `B1:real`] CMT_PHI_PROPS);
      MP_TAC(ISPECL [`h2:real^3->real`; `B2:real`] CMT_PHI_PROPS)] THEN
    ANTS_TAC THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[LIFT_SUB] THEN ASM_SIMP_TAC[INTEGRAL_SUB; DROP_SUB];
    REWRITE_TAC[p4_s2_integral; LIFT_SUB] THEN ASM_SIMP_TAC[INTEGRAL_SUB; DROP_SUB] THEN
    REAL_ARITH_TAC]);;

let CM_SHELL_INTEGRAL = prove
 (`!h:real^3->real.
     (\z. lift(h z)) measurable_on (:real^3) /\
     (?B. !y. y IN sphere(vec 0,&1) ==> abs(h y) <= B) /\
     (!t z. &0 < t /\ ~(z = vec 0) ==> h(t % z) = inv(t pow 2) * h z)
     ==> (\z. lift(h z)) absolutely_integrable_on wan_shell /\
         drop(integral wan_shell (\z. lift(h z))) = &3 / &2 * p4_s2_integral h`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_TAC `B:real`) ASSUME_TAC)) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[wan_shell] THEN MATCH_MP_TAC CMT_HOMOG_ABS_INTEGRABLE THEN
    EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. abs s = &1
        ==> drop(integral wan_shell
                   (\z. lift((abs((h:real^3->real) z) + s * h z) / &2))) =
            &3 / &2 * p4_s2_integral (\z. (abs(h z) + s * h z) / &2) /\
            (\z. lift((abs(h z) + s * h z) / &2)) measurable_on (:real^3) /\
            (!y. y IN sphere(vec 0,&1) ==> abs((abs(h y) + s * h y) / &2) <= abs B) /\
            (!t z. &0 < t /\ ~(z = vec 0)
                   ==> (abs(h(t % z)) + s * h(t % z)) / &2 =
                       inv(t pow 2) * ((abs(h z) + s * h z) / &2))`
  (LABEL_TAC "PART") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`h:real^3->real`; `B:real`; `s:real`] CMT_HOMOG_PARTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\z:real^3. (abs((h:real^3->real) z) + s * h z) / &2`; `abs B`]
                  CMT_SHELL_NONNEG) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "PART" (MP_TAC o SPEC `&1`) THEN
  USE_THEN "PART" (MP_TAC o SPEC `-- &1`) THEN
  REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_NUM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "EN") (LABEL_TAC "HN")) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "EP") (LABEL_TAC "HP")) THEN
  SUBGOAL_THEN
   `(h:real^3->real) =
    (\z. (abs(h z) + &1 * h z) / &2 - (abs(h z) + -- &1 * h z) / &2)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`\z:real^3. (abs((h:real^3->real) z) + &1 * h z) / &2`;
                 `\z:real^3. (abs((h:real^3->real) z) + -- &1 * h z) / &2`;
                 `abs B`; `abs B`] CMT_SHELL_SUB) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  USE_THEN "EP" SUBST1_TAC THEN USE_THEN "EN" SUBST1_TAC THEN REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* T7: the radial extension calculus.  wan_rext u is constant on rays, so    *)
(* its Jacobian scales like inv t and kills the radial direction; all CM    *)
(* quantities of u only depend on u on S^2 (the weak derivatives, energies, *)
(* areas and traces on wan_shell are local).                                 *)
(* ------------------------------------------------------------------------- *)

let CM_REXT_SCALE = prove
 (`!(u:real^3->real^K) t z. &0 < t ==> wan_rext u (t % z) = wan_rext u z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_rext] THEN AP_TERM_TAC THEN
  REWRITE_TAC[NORM_MUL; VECTOR_MUL_ASSOC; REAL_INV_MUL] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(a * b) * c:real = b * (a * c)`] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_RID]);;

let CM_REXT_SPHERE = prove
 (`!(u:real^3->real^K) y. y IN sphere(vec 0,&1) ==> wan_rext u y = u y`,
  SIMP_TAC[wan_rext; IN_SPHERE_0; REAL_INV_1; VECTOR_MUL_LID]);;

let CM_REXT_JACOBIAN = prove
 (`!(u:real^3->real^K) z t.
     ~(z = vec 0) /\ &0 < t /\ wan_rext u differentiable at z
     ==> wan_rext u differentiable at (t % z) /\
         jacobian (wan_rext u) (at (t % z)) = inv t %% jacobian (wan_rext u) (at z) /\
         jacobian (wan_rext u) (at z) ** z = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s x. &0 < s ==> wan_rext (u:real^3->real^K) (s % x) = wan_rext u x`
  (LABEL_TAC "SC") THENL [SIMP_TAC[CM_REXT_SCALE]; ALL_TAC] THEN
  ABBREV_TAC `D = frechet_derivative (wan_rext (u:real^3->real^K)) (at z)` THEN
  SUBGOAL_THEN `(wan_rext (u:real^3->real^K) has_derivative D) (at z)` (LABEL_TAC "HD")
      THENL
   [EXPAND_TAC "D" THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]; ALL_TAC] THEN
  SUBGOAL_THEN `linear (D:real^3->real^K)` (LABEL_TAC "LD") THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `jacobian (wan_rext (u:real^3->real^K)) (at z) = matrix D` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[jacobian]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(wan_rext (u:real^3->real^K) has_derivative (D o (\x. inv t % x))) (at (t % z))`
  (LABEL_TAC "HDT") THENL
   [SUBGOAL_THEN `wan_rext (u:real^3->real^K) = wan_rext u o (\x. inv t % x)`
    (fun th -> GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [th]) THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `x:real^3` THEN
      CONV_TAC SYM_CONV THEN USE_THEN "SC" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[REAL_LT_INV_EQ];
      ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
      MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN REWRITE_TAC[LINEAR_ID];
      ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID]];
    ALL_TAC] THEN
  REWRITE_TAC[jacobian] THEN
  USE_THEN "HDT" (SUBST1_TAC o MATCH_MP HAS_FRECHET_DERIVATIVE_UNIQUE_AT) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[differentiable] THEN EXISTS_TAC `(D:real^3->real^K) o (\x. inv t % x)` THEN
    USE_THEN "HDT" ACCEPT_TAC;
    REWRITE_TAC[MATRIX_EQ; MATRIX_VECTOR_LMUL] THEN X_GEN_TAC `x:real^3` THEN
    SUBGOAL_THEN `linear ((D:real^3->real^K) o (\x. inv t % x))` ASSUME_TAC THENL
     [MATCH_MP_TAC LINEAR_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN REWRITE_TAC[LINEAR_ID];
      ALL_TAC] THEN
    ASM_SIMP_TAC[MATRIX_WORKS; o_THM] THEN ASM_SIMP_TAC[LINEAR_CMUL];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_WORKS] THEN
  SUBGOAL_THEN `linear (\s:real^1. drop s % (z:real^3))` (LABEL_TAC "LG") THENL
   [REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `((wan_rext (u:real^3->real^K) o (\s:real^1. drop s % z)) has_derivative
     (D o (\s:real^1. drop s % z))) (at (lift(&1)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[LIFT_DROP; VECTOR_MUL_LID]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\s:real^1. wan_rext (u:real^3->real^K) z) has_derivative
     (D o (\s:real^1. drop s % z))) (at (lift(&1)))`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [`wan_rext (u:real^3->real^K) o (\s:real^1. drop s % z)`; `&1`]
        THEN
    ASM_REWRITE_TAC[REAL_LT_01; o_THM] THEN X_GEN_TAC `s:real^1` THEN
    REWRITE_TAC[dist; NORM_REAL; GSYM drop; DROP_SUB; LIFT_DROP] THEN DISCH_TAC THEN
    USE_THEN "SC" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJ (ISPECL [`wan_rext (u:real^3->real^K) z`; `at(lift(&1))`]
                                    HAS_DERIVATIVE_CONST)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_UNIQUE_AT) THEN
  DISCH_THEN(MP_TAC o C AP_THM `lift(&1)`) THEN
  REWRITE_TAC[o_THM; LIFT_DROP; VECTOR_MUL_LID] THEN MESON_TAC[]);;

let CMT_LSPACE_EQ = prove
 (`!(s:real^M->bool) (f:real^M->real^N) g p.
        (!x. x IN s ==> f x = g x) ==> (f IN lspace s p <=> g IN lspace s p)`,
  SUBGOAL_THEN
   `!(s:real^M->bool) (f:real^M->real^N) g p.
        (!x. x IN s ==> f x = g x) /\ f IN lspace s p ==> g IN lspace s p`
  (fun th -> MESON_TAC[th]) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[lspace; IN_ELIM_THM] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_ON_EQ THEN EXISTS_TAC `f:real^M->real^N` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC INTEGRABLE_EQ THEN
    EXISTS_TAC `\x. lift(norm((f:real^M->real^N) x) rpow p)` THEN ASM_SIMP_TAC[]]);;

let CMT_WAN_LLOC_EQ = prove
 (`!(s:real^N->bool) (u:real^N->real^K) u'.
        (!x. x IN s ==> u x = u' x) ==> (wan_lloc s u <=> wan_lloc s u')`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_lloc] THEN EQ_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ABSOLUTELY_INTEGRABLE_EQ) THEN
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN ASM SET_TAC[]);;

let CMT_WAN_WPD_EQ = prove
 (`!(s:real^N->bool) i (u:real^N->real^K) u' v.
        (!x. x IN s ==> u x = u' x) ==> (wan_wpd s i u v <=> wan_wpd s i u' v)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_wpd] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `u:real^N->real^K`; `u':real^N->real^K`]
                CMT_WAN_LLOC_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `!phi. integral s (\x. wan_dpart i phi x % (u:real^N->real^K) x) =
                      integral s (\x. wan_dpart i phi x % u' x)`
  (fun th -> REWRITE_TAC[th]) THEN
  GEN_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN ASM_SIMP_TAC[]);;

let CMT_WAN_WD_EQ = prove
 (`!(s:real^N->bool) i (u:real^N->real^K) u'.
        (!x. x IN s ==> u x = u' x) ==> wan_wd s i u = wan_wd s i u'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_wd] THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `v:real^N->real^K` THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `i:num`; `u:real^N->real^K`; `u':real^N->real^K`;
                 `v:real^N->real^K`] CMT_WAN_WPD_EQ) THEN
  ASM_SIMP_TAC[]);;

let CMT_WAN_W12_EQ = prove
 (`!(s:real^N->bool) (u:real^N->real^K) u'.
        (!x. x IN s ==> u x = u' x) ==> (wan_w12 s u <=> wan_w12 s u')`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_w12] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `u:real^N->real^K`; `u':real^N->real^K`; `&2`]
                CMT_LSPACE_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `!i v. wan_wpd s i (u:real^N->real^K) v <=> wan_wpd s i u' v`
  (fun th -> REWRITE_TAC[th]) THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC CMT_WAN_WPD_EQ THEN ASM_REWRITE_TAC[]);;

let CMT_WAN_GDIR_EQ = prove
 (`!(s:real^N->bool) (G:real^K->real^K^K) (u:real^N->real^K) u'.
        (!x. x IN s ==> u x = u' x) ==> wan_gdir s G u = wan_gdir s G u'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_gdir] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `i:num`; `u:real^N->real^K`; `u':real^N->real^K`]
                CMT_WAN_WD_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC INTEGRAL_EQ THEN ASM_SIMP_TAC[]);;

let CMT_WGRAM_EQ = prove
 (`!(s:real^3->bool) (G:real^K->real^K^K) (v:real^3->real^K) v'.
        (!z. z IN s ==> v z = v' z)
        ==> !z. z IN s ==> cm_wgram s G v z = cm_wgram s G v' z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cm_wgram] THEN
  SUBGOAL_THEN `!i. wan_wd s i (v:real^3->real^K) = wan_wd s i v'`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC CMT_WAN_WD_EQ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[]);;

let CMT_REXT_SPHERE_EQ = prove
 (`!(u:real^3->real^K) u'.
        (!y. y IN sphere(vec 0,&1) ==> u y = u' y)
        ==> !z. ~(z = vec 0) ==> wan_rext u z = wan_rext u' z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_rext] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[P4_RADIAL_SPHERE]);;

let CMT_SHELL_NONZERO = prove
 (`!z:real^3. z IN wan_shell ==> ~(z = vec 0)`,
  REWRITE_TAC[wan_shell; IN_ELIM_THM] THEN GEN_TAC THEN STRIP_TAC THEN
  DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `&1 / &2 < norm(vec 0:real^3)` THEN
  REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC);;

let CMT_REXT_SHELL_EQ = prove
 (`!(u:real^3->real^K) u'.
        (!y. y IN sphere(vec 0,&1) ==> u y = u' y)
        ==> !z. z IN wan_shell ==> wan_rext u z = wan_rext u' z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^3->real^K`; `u':real^3->real^K`] CMT_REXT_SPHERE_EQ) THEN
  ASM_SIMP_TAC[CMT_SHELL_NONZERO]);;

let CMT_SEN_SPHERE_EQ = prove
 (`!(G:real^K->real^K^K) (u:real^3->real^K) u'.
        (!y. y IN sphere(vec 0,&1) ==> u y = u' y) ==> cm_sen G u = cm_sen G u'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cm_sen] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC CMT_WAN_GDIR_EQ THEN MATCH_MP_TAC CMT_REXT_SHELL_EQ THEN
  ASM_REWRITE_TAC[]);;

let CM_SPHERE_ONLY = prove
 (`!(S:real^K->bool) (G:real^K->real^K^K) (Q:real^K->real^K^K) (u:real^3->real^K) u'.
     (!y. y IN sphere(vec 0,&1) ==> u y = u' y)
     ==> (!z. ~(z = vec 0) ==> wan_rext u z = wan_rext u' z) /\
         cm_sen G u = cm_sen G u' /\ cm_sarea G u = cm_sarea G u' /\
         cm_strace G Q u = cm_strace G Q u' /\
         (cm_smap S u <=> cm_smap S u') /\ (cm_sharmonic S G u <=> cm_sharmonic S G u')`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CMT_REXT_SPHERE_EQ) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CMT_REXT_SHELL_EQ) THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC CMT_SEN_SPHERE_EQ THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[cm_sarea] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`wan_shell`; `G:real^K->real^K^K`; `wan_rext (u:real^3->real^K)`;
                   `wan_rext (u':real^3->real^K)`] CMT_WGRAM_EQ) THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[cm_strace] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`wan_shell`; `G:real^K->real^K^K`; `wan_rext (u:real^3->real^K)`;
                   `wan_rext (u':real^3->real^K)`] CMT_WGRAM_EQ) THEN
    MP_TAC(ISPECL [`wan_shell`; `Q:real^K->real^K^K`; `wan_rext (u:real^3->real^K)`;
                   `wan_rext (u':real^3->real^K)`] CMT_WGRAM_EQ) THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[cm_smap; wan_s2_w12] THEN
    SUBGOAL_THEN `(u:real^3->real^K) continuous_on sphere(vec 0,&1) <=>
                  (u':real^3->real^K) continuous_on sphere(vec 0,&1)` SUBST1_TAC THENL
     [EQ_TAC THEN MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_EQ) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `wan_w12 wan_shell (wan_rext (u:real^3->real^K)) <=>
                  wan_w12 wan_shell (wan_rext (u':real^3->real^K))` SUBST1_TAC THENL
     [MATCH_MP_TAC CMT_WAN_W12_EQ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[cm_sharmonic] THEN
    SUBGOAL_THEN `smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext (u:real^3->real^K)) <=>
                  smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext (u':real^3->real^K))`
    SUBST1_TAC THENL
     [EQ_TAC THEN MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] SMOOTH_MAP_ON_EQ) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!phi:real^3->real^K.
        (\e. cm_sen G (\y. closest_point S ((u:real^3->real^K) y + e % phi y))) =
        (\e. cm_sen G (\y. closest_point S ((u':real^3->real^K) y + e % phi y)))`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `e:real` THEN
      MATCH_MP_TAC CMT_SEN_SPHERE_EQ THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* T2: chart Gram matrices of a C^1 map u of S^2 are the ambient Gram        *)
(* matrices of f o u for any pullback pair (R,Q).  CMT_GRAM_PULLBACK is E8   *)
(* (MFD_EMBED_GRAM of pc_mfd_embmetric) for an arbitrary pair, without the   *)
(* riemannian hypothesis that E8 carries but does not use.                   *)
(* ------------------------------------------------------------------------- *)

let CMT_OPEN_NONZERO = prove
 (`!a:real^N. open {z:real^N | ~(z = a)}`,
  GEN_TAC THEN
  SUBGOAL_THEN `{z:real^N | ~(z = a)} = (:real^N) DELETE a` SUBST1_TAC THENL
   [SET_TAC[]; SIMP_TAC[OPEN_DELETE; OPEN_UNIV]]);;

let CMT_NORMALIZE_CONTINUOUS = prove
 (`(\z:real^3. inv(norm z) % z) continuous_on {z:real^3 | ~(z = vec 0)}`,
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
  REWRITE_TAC[o_DEF] THEN
  MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_INV) THEN
  REWRITE_TAC[IN_ELIM_THM; NORM_EQ_0] THEN
  REWRITE_TAC[REWRITE_RULE[o_DEF] CONTINUOUS_ON_LIFT_NORM]);;

let CMT_NORMALIZE_MAP = prove
 (`continuous_map (subtopology euclidean {z:real^3 | ~(z = vec 0)},
                   subtopology euclidean (sphere(vec 0:real^3,&1)))
                  (\z:real^3. inv(norm z) % z)`,
  REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2; CMT_NORMALIZE_CONTINUOUS] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  REWRITE_TAC[P4_RADIAL_SPHERE]);;

let CMT_REXT_MAP_CONTINUOUS = prove
 (`!top (u:real^3->A).
        continuous_map (subtopology euclidean (sphere(vec 0:real^3,&1)),top) u
        ==> continuous_map (subtopology euclidean {z:real^3 | ~(z = vec 0)},top)
                           (\z. u(inv(norm z) % z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z:real^3. (u:real^3->A)(inv(norm z) % z)) = u o (\z. inv(norm z) % z)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology euclidean (sphere(vec 0:real^3,&1))` THEN
  ASM_REWRITE_TAC[CMT_NORMALIZE_MAP]);;

let CMT_CHART_SET_OPEN = prove
 (`!top (u:real^3->A) U.
        continuous_map (subtopology euclidean (sphere(vec 0:real^3,&1)),top) u /\
        open_in top U
        ==> open {z:real^3 | ~(z = vec 0) /\ u(inv(norm z) % z) IN U}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN
  EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN REWRITE_TAC[CMT_OPEN_NONZERO] THEN
  MP_TAC(ISPECL [`\z:real^3. (u:real^3->A)(inv(norm z) % z)`;
                 `subtopology euclidean {z:real^3 | ~(z = vec 0)}`; `top:A topology`;
                 `U:A->bool`] OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
  ASM_SIMP_TAC[CMT_REXT_MAP_CONTINUOUS; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; IN_ELIM_THM]);;

let CMT_C1_DIFFERENTIABLE_AT = prove
 (`!s (f:real^M->real^N) x.
        open s /\ continuously_differentiable 1 s f /\ x IN s ==> f differentiable at x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`0`; `s:real^M->bool`; `f:real^M->real^N`]
                CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN) THEN
  ASM_REWRITE_TAC[GSYM ONE] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^M->real^M->real^N` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[differentiable] THEN EXISTS_TAC `(f':real^M->real^M->real^N) x` THEN
  ASM_SIMP_TAC[]);;

let CMT_GRAM_PULLBACK = prove
 (`!top atlas (g:A->real^N^N) (f:A->real^K) (G:real^K->real^K^K) (u:real^M->A) s y.
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
     smooth_immersion_into atlas f /\
     (!c w. c IN atlas /\ w IN IMAGE (SND c) (FST c)
            ==> metric_local atlas c g w =
                transp(matrix(frechet_derivative (f o chart_inv c) (at w))) **
                G(f(chart_inv c w)) **
                matrix(frechet_derivative (f o chart_inv c) (at w))) /\
     open s /\ y IN s /\ continuous_map (subtopology euclidean s,top) u /\
     (\z. SND(chart_at atlas (u y)) (u z)) differentiable at y
     ==> transp(jacobian (f o u) (at y)) ** G(f(u y)) ** jacobian (f o u) (at y) =
         transp(jacobian (\z. SND(chart_at atlas (u y)) (u z)) (at y)) ** g(u y) **
         jacobian (\z. SND(chart_at atlas (u y)) (u z)) (at y)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "PB") STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(u:real^M->A) y IN topspace top` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE o
      check (is_comb o concl)) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(u:real^M->A) y`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((u:real^M->A) y)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:A->real^K`; `c:(A->bool)#(A->real^N)`] GRGE_IMMERSION_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `phi = \z:real^M. SND(c:(A->bool)#(A->real^N)) ((u:real^M->A) z)` THEN
  SUBGOAL_THEN
   `((phi:real^M->real^N) has_derivative frechet_derivative phi (at y)) (at y)`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]; ALL_TAC] THEN
  SUBGOAL_THEN `(phi:real^M->real^N) y = SND(c:(A->bool)#(A->real^N)) ((u:real^M->A) y)`
  ASSUME_TAC THENL [EXPAND_TAC "phi" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(((f:A->real^K) o chart_inv (c:(A->bool)#(A->real^N))) has_derivative
     frechet_derivative (f o chart_inv c) (at (SND c ((u:real^M->A) y))))
    (at (SND c (u y)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open {z | z IN s /\ (u:real^M->A) z IN FST(c:(A->bool)#(A->real^N))}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `s:real^M->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`u:real^M->A`; `subtopology euclidean (s:real^M->bool)`;
                   `top:A topology`; `FST(c:(A->bool)#(A->real^N))`]
                  OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(((f:A->real^K) o (u:real^M->A)) has_derivative
     (frechet_derivative (f o chart_inv (c:(A->bool)#(A->real^N)))
                         (at (SND c (u y))) o
      frechet_derivative (phi:real^M->real^N) (at y))) (at y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    EXISTS_TAC `((f:A->real^K) o chart_inv (c:(A->bool)#(A->real^N))) o
                (phi:real^M->real^N)` THEN
    EXISTS_TAC `{z | z IN s /\ (u:real^M->A) z IN FST(c:(A->bool)#(A->real^N))}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [EXPAND_TAC "phi" THEN REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `jacobian ((f:A->real^K) o (u:real^M->A)) (at y) =
    matrix(frechet_derivative (f o chart_inv (c:(A->bool)#(A->real^N)))
                              (at (SND c (u y)))) **
    jacobian (phi:real^M->real^N) (at y)`
  SUBST1_TAC THENL
   [REWRITE_TAC[jacobian] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT o
      check (fun th -> can (find_term (fun t -> t = `(f:A->real^K) o (u:real^M->A)`))
                           (concl th))) THEN
    MATCH_MP_TAC MATRIX_COMPOSE THEN
    ASM_MESON_TAC[has_derivative];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_TRANSP_MUL; GSYM MATRIX_MUL_ASSOC] THEN AP_TERM_TAC THEN
  REWRITE_TAC[MATRIX_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN
  USE_THEN "PB" (MP_TAC o SPECL [`c:(A->bool)#(A->real^N)`;
                                 `SND(c:(A->bool)#(A->real^N)) ((u:real^M->A) y)`]) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  EXPAND_TAC "c" THEN MATCH_MP_TAC METRIC_LOCAL_AT THEN
  EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]);;

let CM_S2_GRAM = prove
 (`!top atlas (R:A->real^N^N) (f:A->real^K) (Q:real^K->real^K^K) (u:real^3->A) y.
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
     smooth_immersion_into atlas f /\
     (!c w. c IN atlas /\ w IN IMAGE (SND c) (FST c)
            ==> metric_local atlas c R w =
                transp(matrix(frechet_derivative (f o chart_inv c) (at w))) **
                Q(f(chart_inv c w)) **
                matrix(frechet_derivative (f o chart_inv c) (at w))) /\
     p4_s2_c1 (top,atlas) u /\ y IN sphere(vec 0,&1)
     ==> p4_s2_gram atlas R u y =
         transp(jacobian (wan_rext (f o u)) (at y)) ** Q(f(u y)) **
         jacobian (wan_rext (f o u)) (at y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p4_s2_c1] THEN STRIP_TAC THEN
  SUBGOAL_THEN `inv(norm(y:real^3)) % y = y` ASSUME_TAC THENL
   [UNDISCH_TAC `y IN sphere(vec 0:real^3,&1)` THEN
    SIMP_TAC[IN_SPHERE_0; REAL_INV_1; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `y IN sphere(vec 0:real^3,&1)` THEN
    ASM_REWRITE_TAC[IN_SPHERE_0; NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^3->A) y IN topspace top` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(u:real^3->A) y`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `R:A->real^N^N`;
                 `f:A->real^K`; `Q:real^K->real^K^K`;
                 `\z:real^3. (u:real^3->A)(inv(norm z) % z)`;
                 `{z:real^3 | ~(z = vec 0)}`; `y:real^3`] CMT_GRAM_PULLBACK) THEN
  ASM_REWRITE_TAC[CMT_OPEN_NONZERO; IN_ELIM_THM] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CMT_REXT_MAP_CONTINUOUS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CMT_C1_DIFFERENTIABLE_AT THEN
    EXISTS_TAC `{z:real^3 | ~(z = vec 0) /\
                            (u:real^3->A)(inv(norm z) % z) IN
                            FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (u y))}` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CMT_CHART_SET_OPEN THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `chart_at (atlas:((A->bool)#(A->real^N))->bool) ((u:real^3->A) y)`]
                    MFDM_CHART) THEN
      ASM_SIMP_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_rext ((f:A->real^K) o (u:real^3->A)) =
                f o (\z:real^3. u(inv(norm z) % z))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; wan_rext; o_THM]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[p4_s2_gram; p4_s2_jac]);;


(* ------------------------------------------------------------------------- *)
(* T7 (classical form): for C^1 radial extensions the weak-derivative CM     *)
(* energy and area are the S^2 integrals of the classical Gram densities.   *)
(* Continuity of the densities off the origin gives measurability and       *)
(* bounds on S^2, so T3 applies to them.                                     *)
(* ------------------------------------------------------------------------- *)

let CMT_CONT_QUAD = prove
 (`!s (G:real^K->real^K^K) (U:real^M->real^K) (a:real^M->real^K) b.
        (vectorize o G) continuous_on (:real^K) /\ U continuous_on s /\
        a continuous_on s /\ b continuous_on s
        ==> (\x. lift(a x dot (G(U x) ** b x))) continuous_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`(vectorize:real^K^K->real^(K,K)finite_prod) o (G:real^K->real^K^K) o
                  (U:real^M->real^K)`;
                 `b:real^M->real^K`;
                 `\(m:real^(K,K)finite_prod) (v:real^K). (matrify m:real^K^K) ** v`;
                 `s:real^M->bool`] BILINEAR_CONTINUOUS_ON_COMPOSE) THEN
  REWRITE_TAC[GRGE_BILINEAR_MATRIFY_MUL; o_THM; MATRIFY_VECTORIZE] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[o_ASSOC] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `(:real^K)` THEN ASM_REWRITE_TAC[SUBSET_UNIV]);;

let CMT_GRAM_ENTRY = prove
 (`!(J:real^M^N) (A:real^N^N) i j.
        1 <= i /\ i <= dimindex(:M) /\ 1 <= j /\ j <= dimindex(:M)
        ==> (transp J ** A ** J)$i$j = (J ** basis i) dot (A ** (J ** basis j))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_VECTOR_MUL_BASIS] THEN
  ASM_SIMP_TAC[matrix_mul; LAMBDA_BETA; dot; column] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LAMBDA_BETA; TRANSP_COMPONENT]);;

let CMT_TRACE_GRAM = prove
 (`!(J:real^M^N) (A:real^N^N).
        trace(transp J ** A ** J) =
        sum(1..dimindex(:M)) (\i. (J ** basis i) dot (A ** (J ** basis i)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[trace] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  SIMP_TAC[CMT_GRAM_ENTRY]);;

let CMT_CONT_TRACE = prove
 (`!s (A:real^M->real^N^N).
        (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
               ==> (\x. lift(A x$i$j)) continuous_on s)
        ==> (\x. lift(trace(A x))) continuous_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[trace; LIFT_SUM; o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  ASM_SIMP_TAC[]);;

let CMT_CONT_MATMUL = prove
 (`!s (A:real^M->real^N^P) (B:real^M->real^Q^N).
        (!i j. 1 <= i /\ i <= dimindex(:P) /\ 1 <= j /\ j <= dimindex(:N)
               ==> (\x. lift(A x$i$j)) continuous_on s) /\
        (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:Q)
               ==> (\x. lift(B x$i$j)) continuous_on s)
        ==> !i j. 1 <= i /\ i <= dimindex(:P) /\ 1 <= j /\ j <= dimindex(:Q)
                  ==> (\x. lift((A x ** B x)$i$j)) continuous_on s`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[matrix_mul; LAMBDA_BETA] THEN
  REWRITE_TAC[LIFT_SUM; o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[LIFT_CMUL] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[o_DEF] THEN ASM_SIMP_TAC[]);;

let CMT_CONT_E2 = prove
 (`!s (A:real^M->real^3^3).
        (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
               ==> (\x. lift(A x$i$j)) continuous_on s)
        ==> (\x. lift(p4_e2(A x))) continuous_on s`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[p4_e2; REAL_ARITH `x / &2 = inv(&2) * x`; LIFT_CMUL; LIFT_SUB] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN MATCH_MP_TAC CMT_CONT_TRACE THEN
    ASM_REWRITE_TAC[DIMINDEX_3];
    MATCH_MP_TAC CMT_CONT_TRACE THEN REWRITE_TAC[DIMINDEX_3] THEN
    MP_TAC(ISPECL [`s:real^M->bool`; `A:real^M->real^3^3`; `A:real^M->real^3^3`]
                  CMT_CONT_MATMUL) THEN
    ASM_REWRITE_TAC[DIMINDEX_3]]);;

let CMT_E2_CMUL = prove
 (`!c (m:real^3^3). p4_e2(c %% m) = c pow 2 * p4_e2 m`,
  REWRITE_TAC[p4_e2; TRACE_CMUL; MATRIX_MUL_LMUL; MATRIX_MUL_RMUL;
              MATRIX_CMUL_ASSOC] THEN
  REAL_ARITH_TAC);;

let CMT_C1_FACTS = prove
 (`!s (U:real^M->real^N).
        open s /\ continuously_differentiable 1 s U
        ==> U continuous_on s /\
            (!x. x IN s ==> U differentiable at x) /\
            (!i x. x IN s ==> partial_derivative i U x = jacobian U (at x) ** basis i) /\
            (!i. (\x. partial_derivative i U x) continuous_on s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x. x IN s ==> (U:real^M->real^N) differentiable at x` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMT_C1_DIFFERENTIABLE_AT THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
    EXISTS_TAC `1` THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN REWRITE_TAC[partial_derivative; jacobian] THEN
    ASM_SIMP_TAC[MATRIX_WORKS; LINEAR_FRECHET_DERIVATIVE];
    GEN_TAC THEN REWRITE_TAC[partial_derivative] THEN
    MP_TAC(ISPECL [`0`; `s:real^M->bool`; `U:real^M->real^N`]
                  CONTINUOUSLY_DIFFERENTIABLE_FRECHET) THEN
    ASM_REWRITE_TAC[GSYM ONE] THEN
    DISCH_THEN(MP_TAC o SPEC `basis i:real^M`) THEN
    REWRITE_TAC[continuously_differentiable]]);;

let CMT_CONT_NONZERO_MEASURABLE = prove
 (`!h:real^3->real.
        (\z. lift(h z)) continuous_on {z:real^3 | ~(z = vec 0)}
        ==> (\z. lift(h z)) measurable_on (:real^3)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] MEASURABLE_ON_SPIKE_SET) THEN
  EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN CONJ_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `{vec 0:real^3}` THEN
    REWRITE_TAC[NEGLIGIBLE_SING] THEN SET_TAC[];
    MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; CMT_OPEN_NONZERO]]);;

let CMT_CONT_SPHERE_BOUND = prove
 (`!h:real^3->real.
        (\z. lift(h z)) continuous_on {z:real^3 | ~(z = vec 0)}
        ==> ?B. !y. y IN sphere(vec 0,&1) ==> abs(h y) <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z:real^3. lift(h z)`; `sphere(vec 0:real^3,&1)`]
                COMPACT_CONTINUOUS_IMAGE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_SPHERE] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET))
        THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_SPHERE_0] THEN X_GEN_TAC `x:real^3` THEN
    ASM_CASES_TAC `x:real^3 = vec 0` THEN ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN MESON_TAC[]);;

let CMT_T3_CONT = prove
 (`!h:real^3->real.
        (\z. lift(h z)) continuous_on {z:real^3 | ~(z = vec 0)} /\
        (!t z. &0 < t /\ ~(z = vec 0) ==> h(t % z) = inv(t pow 2) * h z)
        ==> (\z. lift(h z)) absolutely_integrable_on wan_shell /\
            drop(integral wan_shell (\z. lift(h z))) = &3 / &2 * p4_s2_integral h`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CM_SHELL_INTEGRAL THEN
  ASM_SIMP_TAC[CMT_CONT_NONZERO_MEASURABLE; CMT_CONT_SPHERE_BOUND]);;


let CMT_CONT_LSPACE_SHELL = prove
 (`!f:real^3->real^N.
        f continuous_on {z:real^3 | ~(z = vec 0)} ==> f IN lspace wan_shell (&2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LSPACE_SUBSET THEN
  EXISTS_TAC `cball(vec 0:real^3,&2) DIFF ball(vec 0,&1 / &2)` THEN
  REWRITE_TAC[wan_shell; CMT_ANNULUS_OPEN_BOUNDED] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`{z:real^3 | ~(z = vec 0)}`; `f:real^3->real^N`]
                  WAN_CONTINUOUS_ON_L2LOC) THEN
    ASM_REWRITE_TAC[wan_l2loc] THEN DISCH_THEN MATCH_MP_TAC THEN
    SIMP_TAC[COMPACT_DIFF; COMPACT_CBALL; OPEN_BALL] THEN
    REWRITE_TAC[SUBSET; IN_DIFF; IN_CBALL_0; IN_BALL_0; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN ASM_CASES_TAC `x:real^3 = vec 0` THEN
    ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_DIFF; IN_CBALL_0; IN_BALL_0; IN_ELIM_THM] THEN
    REAL_ARITH_TAC]);;

let CMT_REXT_PD_HOMOG = prove
 (`!(u:real^3->real^K) i t z.
        continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext u) /\
        ~(z = vec 0) /\ &0 < t
        ==> partial_derivative i (wan_rext u) (t % z) =
            inv t % partial_derivative i (wan_rext u) z /\
            jacobian (wan_rext u) (at (t % z)) = inv t %% jacobian (wan_rext u) (at z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`{z:real^3 | ~(z = vec 0)}`; `wan_rext (u:real^3->real^K)`]
                CMT_C1_FACTS) THEN
  ASM_REWRITE_TAC[CMT_OPEN_NONZERO; IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^3->real^K`; `z:real^3`; `t:real`] CM_REXT_JACOBIAN) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `~(t % z:real^3 = vec 0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_LMUL]);;

let CMT_REXT_GRAM_HOMOG = prove
 (`!(G:real^K->real^K^K) (u:real^3->real^K) t z.
        continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext u) /\
        ~(z = vec 0) /\ &0 < t
        ==> transp(jacobian (wan_rext u) (at (t % z))) ** G(wan_rext u (t % z)) **
            jacobian (wan_rext u) (at (t % z)) =
            inv(t pow 2) %%
            (transp(jacobian (wan_rext u) (at z)) ** G(wan_rext u z) **
             jacobian (wan_rext u) (at z))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^3->real^K`; `1`; `t:real`; `z:real^3`] CMT_REXT_PD_HOMOG) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  ASM_SIMP_TAC[CM_REXT_SCALE; TRANSP_MATRIX_CMUL; MATRIX_MUL_LMUL; MATRIX_MUL_RMUL;
               MATRIX_CMUL_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[REAL_POW_2; REAL_INV_MUL]);;

let CMT_SHELL_OPEN = prove
 (`open wan_shell`,
  REWRITE_TAC[wan_shell; CMT_ANNULUS_OPEN_BOUNDED]);;

let CMT_CONT_ABSINT_SHELL = prove
 (`!f:real^3->real^N.
        f continuous_on {z:real^3 | ~(z = vec 0)} ==> f absolutely_integrable_on wan_shell`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM LSPACE_1] THEN MATCH_MP_TAC LSPACE_MONO THEN
  EXISTS_TAC `&2` THEN ASM_SIMP_TAC[CMT_CONT_LSPACE_SHELL] THEN
  CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  MATCH_MP_TAC MEASURABLE_OPEN THEN REWRITE_TAC[wan_shell; CMT_ANNULUS_OPEN_BOUNDED]);;

let CMT_WGRAM_CLASSICAL = prove
 (`!(s:real^3->bool) (G:real^K->real^K^K) (v:real^3->real^K) z.
        (!i. 1 <= i /\ i <= 3 ==> wan_wd s i v z = jacobian v (at z) ** basis i)
        ==> cm_wgram s G v z =
            transp(jacobian v (at z)) ** G(v z) ** jacobian v (at z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cm_wgram] THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; DIMINDEX_3] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[CMT_GRAM_ENTRY; DIMINDEX_3]);;

let CM_CLASSICAL = prove
 (`!(G:real^K->real^K^K) (Q:real^K->real^K^K) (u:real^3->real^K).
     continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext u) /\
     smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o G) /\
     smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o Q)
     ==> wan_s2_w12 u /\
         cm_sen G u =
         p4_s2_integral
          (\y. trace(transp(jacobian (wan_rext u) (at y)) ** G(u y) **
                     jacobian (wan_rext u) (at y)) / &2) /\
         cm_sarea G u =
         p4_s2_integral
          (\y. sqrt(p4_e2(transp(jacobian (wan_rext u) (at y)) ** G(u y) **
                          jacobian (wan_rext u) (at y))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "C1") (CONJUNCTS_THEN2 (LABEL_TAC "GS")
    (K ALL_TAC))) THEN
  MP_TAC(ISPECL [`{z:real^3 | ~(z = vec 0)}`; `wan_rext (u:real^3->real^K)`]
                CMT_C1_FACTS) THEN
  ASM_REWRITE_TAC[CMT_OPEN_NONZERO; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "UC") (CONJUNCTS_THEN2 (LABEL_TAC "UD")
    (CONJUNCTS_THEN2 (LABEL_TAC "PD") (LABEL_TAC "PC" o REWRITE_RULE[ETA_AX])))) THEN
  SUBGOAL_THEN
   `((vectorize:real^K^K->real^(K,K)finite_prod) o (G:real^K->real^K^K))
    continuous_on (:real^K)` (LABEL_TAC "GC") THENL
   [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN EXISTS_TAC `0` THEN
    USE_THEN "GS" (MP_TAC o REWRITE_RULE[smooth_map_on]) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
          ==> (\x. lift((transp(jacobian (wan_rext (u:real^3->real^K)) (at x)) **
                         (G:real^K->real^K^K)(wan_rext u x) **
                         jacobian (wan_rext u) (at x))$i$j))
              continuous_on {z:real^3 | ~(z = vec 0)}`
  (LABEL_TAC "GRC") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `\x. lift(partial_derivative i (wan_rext (u:real^3->real^K)) x dot
                         ((G:real^K->real^K^K)(wan_rext u x) **
                          partial_derivative j (wan_rext u) x))` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN AP_TERM_TAC THEN
      MP_TAC(ISPECL [`jacobian (wan_rext (u:real^3->real^K)) (at x)`;
                     `(G:real^K->real^K^K)(wan_rext (u:real^3->real^K) x)`;
                     `i:num`; `j:num`] CMT_GRAM_ENTRY) THEN
      ASM_SIMP_TAC[DIMINDEX_3];
      MATCH_MP_TAC CMT_CONT_QUAD THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(trace(transp(jacobian (wan_rext (u:real^3->real^K)) (at x)) **
                    (G:real^K->real^K^K)(wan_rext u x) ** jacobian (wan_rext u) (at x))))
    continuous_on {z:real^3 | ~(z = vec 0)}`
  (LABEL_TAC "CTT") THENL
   [MATCH_MP_TAC CMT_CONT_TRACE THEN ASM_REWRITE_TAC[DIMINDEX_3]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t z. &0 < t /\ ~(z = vec 0)
          ==> transp(jacobian (wan_rext (u:real^3->real^K)) (at (t % z))) **
              (G:real^K->real^K^K)(wan_rext u (t % z)) **
              jacobian (wan_rext u) (at (t % z)) =
              inv(t pow 2) %%
              (transp(jacobian (wan_rext u) (at z)) ** G(wan_rext u z) **
               jacobian (wan_rext u) (at z))`
  (LABEL_TAC "GH") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMT_REXT_GRAM_HOMOG THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `\x. trace(transp(jacobian (wan_rext (u:real^3->real^K)) (at x)) **
                         (G:real^K->real^K^K)(wan_rext u x) **
                         jacobian (wan_rext u) (at x)) / &2` CMT_T3_CONT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_ARITH `x / &2 = inv(&2) * x`; LIFT_CMUL] THEN
      MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[TRACE_CMUL] THEN REAL_ARITH_TAC];
    REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "TH")] THEN
  MP_TAC(ISPEC `\x. sqrt(p4_e2(transp(jacobian (wan_rext (u:real^3->real^K)) (at x)) **
                              (G:real^K->real^K^K)(wan_rext u x) **
                              jacobian (wan_rext u) (at x)))` CMT_T3_CONT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_LIFT_SQRT_COMPOSE THEN REWRITE_TAC[o_DEF] THEN
      MATCH_MP_TAC CMT_CONT_E2 THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[CMT_E2_CMUL; SQRT_MUL; POW_2_SQRT_ABS; REAL_ABS_INV; REAL_ABS_POW] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`]];
    REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "TA")] THEN
  MP_TAC(REWRITE_RULE[WAN_W12_C1_STATEMENT] (ISPECL [`(:3)`; `(:K)`] WAN_W12_C1)) THEN
  DISCH_THEN(MP_TAC o SPECL [`wan_shell`; `wan_rext (u:real^3->real^K)`]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[CMT_SHELL_OPEN];
      MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN
      EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REWRITE_TAC[CMT_SHELL_NONZERO];
      MATCH_MP_TAC CMT_CONT_LSPACE_SHELL THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC CMT_CONT_LSPACE_SHELL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "W12") (CONJUNCTS_THEN2
    (LABEL_TAC "WPD" o REWRITE_RULE[ETA_AX]) (K ALL_TAC))) THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 3
        ==> negligible {x | x IN wan_shell /\
                            ~(wan_wd wan_shell i (wan_rext (u:real^3->real^K)) x =
                              partial_derivative i (wan_rext u) x)}`
  (LABEL_TAC "NEG") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_WD_UNIQUE THEN REWRITE_TAC[ETA_AX] THEN
    ASM_SIMP_TAC[DIMINDEX_3; CMT_SHELL_OPEN];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[wan_s2_w12];
    REWRITE_TAC[cm_sen] THEN
    SUBGOAL_THEN
     `wan_gdir wan_shell (G:real^K->real^K^K) (wan_rext (u:real^3->real^K)) =
      drop(integral wan_shell
            (\x. lift(trace(transp(jacobian (wan_rext u) (at x)) ** G(wan_rext u x) **
                            jacobian (wan_rext u) (at x)))))`
    SUBST1_TAC THENL
     [REWRITE_TAC[wan_gdir; DIMINDEX_3] THEN MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `sum(1..3) (\i. drop(integral wan_shell
                    (\x. lift(partial_derivative i (wan_rext (u:real^3->real^K)) x dot
                              ((G:real^K->real^K^K)(wan_rext u x) **
                               partial_derivative i (wan_rext u) x)))))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN
        STRIP_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
        MATCH_MP_TAC INTEGRAL_SPIKE THEN
        EXISTS_TAC `{x | x IN wan_shell /\
                         ~(wan_wd wan_shell i (wan_rext (u:real^3->real^K)) x =
                           partial_derivative i (wan_rext u) x)}` THEN
        CONJ_TAC THENL [USE_THEN "NEG" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `integral wan_shell
          (\x. lift(trace(transp(jacobian (wan_rext (u:real^3->real^K)) (at x)) **
                          (G:real^K->real^K^K)(wan_rext u x) **
                          jacobian (wan_rext u) (at x)))) =
        integral wan_shell
          (\x. vsum(1..3) (\i. lift(partial_derivative i (wan_rext u) x dot
                                    (G(wan_rext u x) **
                                     partial_derivative i (wan_rext u) x))))`
      SUBST1_TAC THENL
       [MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
        REWRITE_TAC[CMT_TRACE_GRAM; DIMINDEX_3; LIFT_SUM; o_DEF] THEN
        SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
         [ASM_SIMP_TAC[CMT_SHELL_NONZERO]; ALL_TAC] THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`\i x. lift(partial_derivative i (wan_rext (u:real^3->real^K)) x dot
                                 ((G:real^K->real^K^K)(wan_rext u x) **
                                  partial_derivative i (wan_rext u) x))`;
                     `wan_shell`; `1..3`] INTEGRAL_VSUM) THEN
      REWRITE_TAC[FINITE_NUMSEG] THEN ANTS_TAC THENL
       [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
        MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
        MATCH_MP_TAC CMT_CONT_ABSINT_SHELL THEN
        MATCH_MP_TAC CMT_CONT_QUAD THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
        DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[DROP_VSUM; o_DEF];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `drop(integral wan_shell
            (\x. lift(trace(transp(jacobian (wan_rext (u:real^3->real^K)) (at x)) **
                            (G:real^K->real^K^K)(wan_rext u x) **
                            jacobian (wan_rext u) (at x))))) =
      &2 * drop(integral wan_shell
                 (\x. lift(trace(transp(jacobian (wan_rext u) (at x)) ** G(wan_rext u x) **
                                 jacobian (wan_rext u) (at x)) / &2)))`
    SUBST1_TAC THENL
     [REWRITE_TAC[REAL_ARITH `x / &2 = inv(&2) * x`; LIFT_CMUL] THEN
      MP_TAC(ISPECL [`\x. lift(trace(transp(jacobian (wan_rext (u:real^3->real^K)) (at x))
          **
                                     (G:real^K->real^K^K)(wan_rext u x) **
                                     jacobian (wan_rext u) (at x)))`;
                     `inv(&2)`; `wan_shell`] INTEGRAL_CMUL) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
        MATCH_MP_TAC CMT_CONT_ABSINT_SHELL THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[DROP_CMUL] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "TH" (SUBST1_TAC o CONJUNCT2) THEN
    MATCH_MP_TAC(REAL_ARITH `a = b ==> (&2 * (&3 / &2 * a)) / &3 = b`) THEN
    MATCH_MP_TAC P4_S2_INTEGRAL_EQ THEN SIMP_TAC[CM_REXT_SPHERE];
    REWRITE_TAC[cm_sarea] THEN
    SUBGOAL_THEN
     `integral wan_shell
        (\z. lift(sqrt(p4_e2(cm_wgram wan_shell (G:real^K->real^K^K)
                                      (wan_rext (u:real^3->real^K)) z)))) =
      integral wan_shell
        (\z. lift(sqrt(p4_e2(transp(jacobian (wan_rext u) (at z)) ** G(wan_rext u z) **
                             jacobian (wan_rext u) (at z)))))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC INTEGRAL_SPIKE THEN
      EXISTS_TAC
       `{x | x IN wan_shell /\
             ~(wan_wd wan_shell 1 (wan_rext (u:real^3->real^K)) x =
               partial_derivative 1 (wan_rext u) x)} UNION
        {x | x IN wan_shell /\
             ~(wan_wd wan_shell 2 (wan_rext (u:real^3->real^K)) x =
               partial_derivative 2 (wan_rext u) x)} UNION
        {x | x IN wan_shell /\
             ~(wan_wd wan_shell 3 (wan_rext (u:real^3->real^K)) x =
               partial_derivative 3 (wan_rext u) x)}` THEN
      CONJ_TAC THENL
       [REPEAT(MATCH_MP_TAC NEGLIGIBLE_UNION THEN CONJ_TAC) THEN
        USE_THEN "NEG" MATCH_MP_TAC THEN ARITH_TAC;
        ALL_TAC] THEN
      X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_DIFF; IN_UNION; IN_ELIM_THM] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      ASM_REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN
      SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
       [ASM_SIMP_TAC[CMT_SHELL_NONZERO]; ALL_TAC] THEN
      MP_TAC(ISPECL [`wan_shell`; `G:real^K->real^K^K`; `wan_rext (u:real^3->real^K)`;
                     `x:real^3`] CMT_WGRAM_CLASSICAL) THEN
      ANTS_TAC THENL
       [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
        SUBGOAL_THEN `i = 1 \/ i = 2 \/ i = 3` MP_TAC THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN ASM_SIMP_TAC[];
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]];
      ALL_TAC] THEN
    USE_THEN "TA" (SUBST1_TAC o CONJUNCT2) THEN
    MATCH_MP_TAC(REAL_ARITH `a = b ==> &2 / &3 * (&3 / &2 * a) = b`) THEN
    MATCH_MP_TAC P4_S2_INTEGRAL_EQ THEN SIMP_TAC[CM_REXT_SPHERE]]);;


(* ------------------------------------------------------------------------- *)
(* T1: cm_emb data exist.  The embedding (E1), tube (E3), normal quadratic   *)
(* bound (E4) and adapted metric (E7) give everything but global eigenvalue  *)
(* bounds; G is replaced by psi G + (1 - psi) I for a cutoff psi equal to 1  *)
(* on f(M), which changes nothing on f(M).                                    *)
(* ------------------------------------------------------------------------- *)

let CMT_CONVEX_BOUNDS = prove
 (`!p q n lam Lam.
        &0 <= p /\ p <= &1 /\ &0 <= n /\ lam * n <= q /\ q <= Lam * n
        ==> min lam (&1) * n <= p * q + (&1 - p) * n /\
            p * q + (&1 - p) * n <= max Lam (&1) * n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= p * (q - lam * n)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= p * (Lam * n - q)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (p * n) * (lam - min lam (&1))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= ((&1 - p) * n) * (&1 - min lam (&1))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (p * n) * (max Lam (&1) - Lam)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= ((&1 - p) * n) * (max Lam (&1) - &1)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

let CMT_GLOBAL_METRIC = prove
 (`!(G:real^K->real^K^K) S.
        smooth_map_on (:real^K) (vectorize o G) /\
        (!z. transp(G z) = G z /\ !v. ~(v = vec 0) ==> &0 < v dot (G z ** v)) /\
        compact S
        ==> ?G':real^K->real^K^K.
              smooth_map_on (:real^K) (vectorize o G') /\
              (!z. transp(G' z) = G' z) /\
              (?lam Lam. &0 < lam /\ lam <= Lam /\
                         !z v. lam * norm v pow 2 <= v dot (G' z ** v) /\
                               v dot (G' z ** v) <= Lam * norm v pow 2) /\
              (!z. z IN S ==> G' z = G z)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "GP") ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `(:real^K)`] GRGE_EUCLID_CUTOFF) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:real^K->real` (X_CHOOSE_THEN `L:real^K->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `L:real^K->bool`] GRGE_QUADFORM_BOUNDS) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `\z:real^K. psi z %% (G:real^K->real^K^K) z + (&1 - psi z) %% mat 1` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC GRGE_SMOOTH_MATADD THEN REWRITE_TAC[OPEN_UNIV] THEN
    REWRITE_TAC[o_DEF; VECTORIZE_CMUL] THEN CONJ_TAC THEN
    MATCH_MP_TAC GRGE_SMOOTH_SCALAR_MUL THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST] THENL
     [MP_TAC(ASSUME `smooth_map_on (:real^K)
                       ((vectorize:real^K^K->real^(K,K)finite_prod) o
                        (G:real^K->real^K^K))`) THEN
      REWRITE_TAC[o_DEF];
      REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
      ASM_REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST]];
    ASM_REWRITE_TAC[TRANSP_MATRIX_ADD; TRANSP_MATRIX_CMUL; TRANSP_MAT];
    MAP_EVERY EXISTS_TAC [`min lam (&1)`; `max Lam (&1)`] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`z:real^K`; `v:real^K`] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB; MATRIX_VECTOR_LMUL;
                MATRIX_VECTOR_MUL_LID; DOT_RADD; DOT_RMUL; GSYM NORM_POW_2] THEN
    ASM_CASES_TAC `(z:real^K) IN L` THENL
     [MATCH_MP_TAC CMT_CONVEX_BOUNDS THEN ASM_SIMP_TAC[REAL_LE_POW_2];
      SUBGOAL_THEN `(psi:real^K->real) z = &0` SUBST1_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID; REAL_SUB_RZERO; REAL_MUL_LID] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `a * n <= &1 * n ==> a * n <= n`);
        MATCH_MP_TAC(REAL_ARITH `&1 * n <= b * n ==> n <= b * n`)] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[REAL_SUB_REFL; MATRIX_CMUL_LZERO; MATRIX_ADD_RID; MATRIX_CMUL_LID]]);;

let CM_EMB_EXISTS = prove
 (`!top atlas (g:A->real^N^N).
     hausdorff_space top /\
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
     compact_space top /\ ~(topspace top = {}) /\ riemannian_metric atlas g /\
     2 * dimindex(:N) + 1 <= dimindex(:K)
     ==> ?(f:A->real^K) G d. cm_emb (top,atlas) g f G d`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`]
                MFD_EMBEDDING_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `f:A->real^K`) THEN
  SUBGOAL_THEN `smooth_immersion_into (atlas:((A->bool)#(A->real^N))->bool) (f:A->real^K)`
  ASSUME_TAC THENL [ASM_MESON_TAC[mfd_embedding]; ALL_TAC] THEN
  SUBGOAL_THEN `compact(IMAGE (f:A->real^K) (topspace top))` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM COMPACT_IN_EUCLIDEAN] THEN MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[GSYM compact_space] THEN
    MATCH_MP_TAC GRGE_MFD_SMOOTH_CONTINUOUS THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN
    ASM_MESON_TAC[GRGE_IMMERSION_SMOOTH];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `f:A->real^K`]
                MFD_TUBULAR_NEIGHBOURHOOD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "CP") (CONJUNCTS_THEN2 (LABEL_TAC "SM")
    (CONJUNCTS_THEN2 (LABEL_TAC "DER") (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `C2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "C2")))
    (K ALL_TAC)))))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `f:A->real^K`]
                MFD_EMBED_NORMAL_QUADRATIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "C1"))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real^K`] MFD_EMBED_AMBIENT_METRIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:real^K->real^K^K` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "GPB")
    (CONJUNCTS_THEN2 (LABEL_TAC "GO") (K ALL_TAC)))))) THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `IMAGE (f:A->real^K) (topspace top)`]
                CMT_GLOBAL_METRIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `G':real^K->real^K^K` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "GE"))))) THEN
  SUBGOAL_THEN
   `!x. x IN topspace top
        ==> jacobian (closest_point (IMAGE (f:A->real^K) (topspace top))) (at (f x)) =
            mfd_tproj (atlas:((A->bool)#(A->real^N))->bool) f x`
  (LABEL_TAC "JT") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[jacobian] THEN
    USE_THEN "DER" (MP_TAC o C MATCH_MP (ASSUME `(x:A) IN topspace top`) o SPEC `x:A`) THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP HAS_FRECHET_DERIVATIVE_UNIQUE_AT) THEN
    REWRITE_TAC[MATRIX_OF_MATRIX_VECTOR_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. (?p. p IN IMAGE (f:A->real^K) (topspace top) /\ dist(z,p) < d)
        ==> closest_point (IMAGE f (topspace top)) z IN IMAGE f (topspace top)`
  (LABEL_TAC "CPT") THENL
   [GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `p:real^K` STRIP_ASSUME_TAC) THEN
    USE_THEN "CP" (MP_TAC o SPECL [`z:real^K`; `p:real^K`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN IMAGE (f:A->real^K) (topspace top)
        ==> transp(jacobian (closest_point (IMAGE f (topspace top))) (at z)) =
            jacobian (closest_point (IMAGE f (topspace top))) (at z) /\
            jacobian (closest_point (IMAGE f (topspace top))) (at z) **
            jacobian (closest_point (IMAGE f (topspace top))) (at z) =
            jacobian (closest_point (IMAGE f (topspace top))) (at z)`
  (LABEL_TAC "JS") THENL
   [REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    USE_THEN "JT" (fun th -> ASM_SIMP_TAC[th]) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `f:A->real^K`; `x:A`] MFD_TPROJ) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?C. &0 <= C /\
        (!x y. x IN IMAGE (f:A->real^K) (topspace top) /\ y IN IMAGE f (topspace top)
               ==> norm((mat 1 - jacobian (closest_point (IMAGE f (topspace top))) (at x))
                   **
                        (y - x)) <= C * norm(y - x) pow 2) /\
        (!z. (?p. p IN IMAGE f (topspace top) /\ dist(z,p) < d)
             ==> onorm(\v. jacobian (closest_point (IMAGE f (topspace top))) (at z) ** v -
                           jacobian (closest_point (IMAGE f (topspace top)))
                                    (at (closest_point (IMAGE f (topspace top)) z)) ** v)
                 <= C * dist(z,closest_point (IMAGE f (topspace top)) z))`
  (LABEL_TAC "CC") THENL
   [EXISTS_TAC `max C1 C2` THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      USE_THEN "JT" (fun th -> ASM_SIMP_TAC[th]) THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `C1 * norm((f:A->real^K) y - f x) pow 2` THEN CONJ_TAC THENL
       [USE_THEN "C1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC];
      X_GEN_TAC `z:real^K` THEN DISCH_THEN(X_CHOOSE_THEN `p:real^K` STRIP_ASSUME_TAC) THEN
      USE_THEN "CPT" (MP_TAC o SPEC `z:real^K`) THEN
      ANTS_TAC THENL [EXISTS_TAC `p:real^K` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:A` (CONJUNCTS_THEN2 (LABEL_TAC "PZ") ASSUME_TAC)) THEN
      SUBGOAL_THEN `dist(z:real^K,f(x:A)) < d` ASSUME_TAC THENL
       [USE_THEN "PZ" (SUBST1_TAC o SYM) THEN MATCH_MP_TAC REAL_LET_TRANS THEN
        EXISTS_TAC `dist(z:real^K,p)` THEN CONJ_TAC THENL
         [MATCH_MP_TAC CLOSEST_POINT_LE THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
          FIRST_ASSUM ACCEPT_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `(closest_point (IMAGE (f:A->real^K) (topspace top))) differentiable (at z)`
      ASSUME_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
        EXISTS_TAC `{z | ?p. p IN IMAGE (f:A->real^K) (topspace top) /\ dist(z,p) < d}` THEN
        ASM_REWRITE_TAC[GRGE_TUBE_OPEN; IN_ELIM_THM] THEN
        EXISTS_TAC `p:real^K` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      USE_THEN "PZ" SUBST1_TAC THEN
      USE_THEN "JT" (fun th -> ASM_SIMP_TAC[th]) THEN
      SUBGOAL_THEN
       `!v. jacobian (closest_point (IMAGE (f:A->real^K) (topspace top))) (at z) ** v =
            frechet_derivative (closest_point (IMAGE f (topspace top))) (at z) v`
      (fun th -> REWRITE_TAC[th]) THENL
       [GEN_TAC THEN REWRITE_TAC[jacobian] THEN
        MP_TAC(ISPEC `frechet_derivative (closest_point (IMAGE (f:A->real^K) (topspace
            top)))
                                         (at z)` MATRIX_WORKS) THEN
        ASM_SIMP_TAC[LINEAR_FRECHET_DERIVATIVE];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `C2 * dist(z:real^K,f(x:A))` THEN CONJ_TAC THENL
       [USE_THEN "C2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[DIST_POS_LE] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z u v. z IN IMAGE (f:A->real^K) (topspace top)
            ==> (jacobian (closest_point (IMAGE f (topspace top))) (at z) ** u) dot
                ((G':real^K->real^K^K) z **
                 (mat 1 - jacobian (closest_point (IMAGE f (topspace top))) (at z)) ** v) =
                &0`
  (LABEL_TAC "ORTH") THENL
   [MAP_EVERY X_GEN_TAC [`z:real^K`; `u:real^K`; `v:real^K`] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "JT" (fun th -> ASM_SIMP_TAC[th]) THEN
    USE_THEN "GE" (fun th -> ASM_SIMP_TAC[th; FUN_IN_IMAGE]) THEN
    USE_THEN "GO" (fun th -> ASM_SIMP_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c y. c IN atlas /\ y IN IMAGE (SND c) (FST c)
          ==> metric_local (atlas:((A->bool)#(A->real^N))->bool) c (g:A->real^N^N) y =
              transp(matrix(frechet_derivative ((f:A->real^K) o chart_inv c) (at y))) **
              (G':real^K->real^K^K)(f(chart_inv c y)) **
              matrix(frechet_derivative (f o chart_inv c) (at y))`
  (LABEL_TAC "PB") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) y IN topspace top` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(G':real^K->real^K^K)((f:A->real^K)(chart_inv (c:(A->bool)#(A->real^N))
        y)) =
                  G(f(chart_inv c y))` SUBST1_TAC THENL
     [USE_THEN "GE" MATCH_MP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      USE_THEN "GPB" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`f:A->real^K`; `G':real^K->real^K^K`; `d:real`] THEN
  REWRITE_TAC[cm_emb; cm_target; cm_tube; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[IMAGE_EQ_EMPTY]);;


(* ------------------------------------------------------------------------- *)
(* T4: smooth symmetric 2-tensor fields on M (smooth chart representatives) *)
(* extend to smooth symmetric fields Q on real^K pulling back to them; the  *)
(* construction of E7 (MFD_EMBED_AMBIENT_METRIC) without its positivity     *)
(* parts: Q = psi (Q0 o r) + (1 - psi) I with Q0 = P^T R P + (I - J P) for  *)
(* the pseudo-inverse P of the chart Jacobian J.  In particular for Ricci.  *)
(* ------------------------------------------------------------------------- *)

let CMT_G0C_SMOOTH_GEN = prove
 (`!top atlas (g:A->real^N^N) (f:A->real^K) c.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        smooth_map_on (IMAGE (SND c) (FST c))
                      ((vectorize:real^N^N->real^(N,N)finite_prod) o metric_local atlas c
                          g) /\
        smooth_immersion_into atlas f /\ c IN atlas
        ==> smooth_map_on (IMAGE (SND c) (FST c))
             ((vectorize:real^K^K->real^(K,K)finite_prod) o
              (\y. transp(matrix_inv(transp(matrix(frechet_derivative (f o chart_inv c) (at
                  y))) **
                                     matrix(frechet_derivative (f o chart_inv c) (at y))) **
                          transp(matrix(frechet_derivative (f o chart_inv c) (at y)))) **
                   metric_local atlas c g y **
                   (matrix_inv(transp(matrix(frechet_derivative (f o chart_inv c) (at y)))
                       **
                               matrix(frechet_derivative (f o chart_inv c) (at y))) **
                    transp(matrix(frechet_derivative (f o chart_inv c) (at y)))) +
                   (mat 1 - matrix(frechet_derivative (f o chart_inv c) (at y)) **
                            (matrix_inv(transp(matrix(frechet_derivative (f o chart_inv c)
                                                                         (at y))) **
                                        matrix(frechet_derivative (f o chart_inv c) (at
                                            y))) **
                             transp(matrix(frechet_derivative (f o chart_inv c) (at
                                 y)))))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:A->real^K`; `c:(A->bool)#(A->real^N)`] GRGE_IMMERSION_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `V = IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
  ABBREV_TAC
   `Jc = \y:real^N. matrix(frechet_derivative ((f:A->real^K) o
                                chart_inv (c:(A->bool)#(A->real^N))) (at y))` THEN
  SUBGOAL_THEN
   `!y. matrix(frechet_derivative ((f:A->real^K) o chart_inv (c:(A->bool)#(A->real^N)))
                                  (at y)) = (Jc:real^N->real^N^K) y`
  (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "Jc" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on V ((vectorize:real^N^K->real^(K,N)finite_prod) o
      (Jc:real^N->real^N^K))`
  ASSUME_TAC THENL
   [EXPAND_TAC "Jc" THEN MATCH_MP_TAC GRGE_SMOOTH_JACOBIAN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on V ((vectorize:real^K^N->real^(N,K)finite_prod) o
                     (\y. transp((Jc:real^N->real^N^K) y)))`
  ASSUME_TAC THENL [MATCH_MP_TAC GRGE_SMOOTH_TRANSP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on V ((vectorize:real^N^N->real^(N,N)finite_prod) o
                     (\y. matrix_inv(transp((Jc:real^N->real^N^K) y) ** Jc y)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_SMOOTH_MATRIX_INV THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC GRGE_SMOOTH_MATMUL THEN ASM_REWRITE_TAC[ETA_AX];
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[GSYM INVERTIBLE_DET_NZ] THEN MATCH_MP_TAC GRGE_GRAM_INVERTIBLE THEN
      X_GEN_TAC `v:real^N` THEN EXPAND_TAC "Jc" THEN
      SUBGOAL_THEN
       `linear(frechet_derivative ((f:A->real^K) o chart_inv (c:(A->bool)#(A->real^N)))
                                  (at (y:real^N)))`
      ASSUME_TAC THENL
       [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
        EXISTS_TAC `V:real^N->bool` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[MATRIX_WORKS] THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on V ((vectorize:real^K^N->real^(N,K)finite_prod) o
                     (\y. matrix_inv(transp((Jc:real^N->real^N^K) y) ** Jc y) **
                          transp(Jc y)))`
  ASSUME_TAC THENL [MATCH_MP_TAC GRGE_SMOOTH_MATMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on V ((vectorize:real^N^K->real^(K,N)finite_prod) o
                     (\y. transp(matrix_inv(transp((Jc:real^N->real^N^K) y) ** Jc y) **
                                 transp(Jc y))))`
  ASSUME_TAC THENL [MATCH_MP_TAC GRGE_SMOOTH_TRANSP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC GRGE_SMOOTH_MATADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC GRGE_SMOOTH_MATMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC GRGE_SMOOTH_MATMUL THEN ASM_REWRITE_TAC[ETA_AX];
    MATCH_MP_TAC GRGE_SMOOTH_MATSUB THEN ASM_REWRITE_TAC[GRGE_SMOOTH_MATCONST] THEN
    MATCH_MP_TAC GRGE_SMOOTH_MATMUL THEN ASM_REWRITE_TAC[ETA_AX]]);;

let CMT_AMBIENT_EXT = prove
 (`!top atlas (g:A->real^N^N) (f:A->real^K).
     hausdorff_space top /\
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
     compact_space top /\ mfd_embedding (top,atlas) f /\
     (!x. x IN topspace top ==> transp(g x) = g x) /\
     (!c. c IN atlas
          ==> smooth_map_on (IMAGE (SND c) (FST c))
                ((vectorize:real^N^N->real^(N,N)finite_prod) o metric_local atlas c g))
     ==> ?G:real^K->real^K^K.
           smooth_map_on (:real^K) (vectorize o G) /\
           (!z. transp(G z) = G z) /\
           (!c y. c IN atlas /\ y IN IMAGE (SND c) (FST c)
                  ==> metric_local atlas c g y =
                      transp(matrix(frechet_derivative (f o chart_inv c) (at y))) **
                      G(f(chart_inv c y)) **
                      matrix(frechet_derivative (f o chart_inv c) (at y)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_immersion_into (atlas:((A->bool)#(A->real^N))->bool) (f:A->real^K)`
  ASSUME_TAC THENL [ASM_MESON_TAC[mfd_embedding]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (f:A->real^K)`
  ASSUME_TAC THENL [ASM_MESON_TAC[GRGE_IMMERSION_SMOOTH]; ALL_TAC] THEN
  SUBGOAL_THEN `compact(IMAGE (f:A->real^K) (topspace top))` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM COMPACT_IN_EUCLIDEAN] THEN MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[GSYM compact_space] THEN
    MATCH_MP_TAC GRGE_MFD_SMOOTH_CONTINUOUS THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:A->real^K`] GRGE_TUBE_LOCZ) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LOCZ"))) THEN
  ABBREV_TAC
   `G0 = \x:A. transp(matrix_inv(transp(mfd_emb_jac atlas f x) ** mfd_emb_jac atlas f x) **
                      transp(mfd_emb_jac atlas f x)) ** (g:A->real^N^N) x **
               (matrix_inv(transp(mfd_emb_jac atlas f x) ** mfd_emb_jac atlas f x) **
                transp(mfd_emb_jac (atlas:((A->bool)#(A->real^N))->bool) (f:A->real^K) x)) +
               (mat 1 - mfd_tproj atlas f x)` THEN
  SUBGOAL_THEN
   `!x. (G0:A->real^K^K) x =
        transp(matrix_inv(transp(mfd_emb_jac atlas f x) ** mfd_emb_jac atlas f x) **
               transp(mfd_emb_jac atlas f x)) ** (g:A->real^N^N) x **
        (matrix_inv(transp(mfd_emb_jac atlas f x) ** mfd_emb_jac atlas f x) **
         transp(mfd_emb_jac (atlas:((A->bool)#(A->real^N))->bool) (f:A->real^K) x)) +
        (mat 1 - mfd_tproj atlas f x)`
  (LABEL_TAC "G0DEF") THENL [EXPAND_TAC "G0" THEN REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC
   `G0c = \(c:(A->bool)#(A->real^N)) (y:real^N).
      transp(matrix_inv(transp(matrix(frechet_derivative ((f:A->real^K) o chart_inv c) (at
          y))) **
                        matrix(frechet_derivative (f o chart_inv c) (at y))) **
             transp(matrix(frechet_derivative (f o chart_inv c) (at y)))) **
      metric_local (atlas:((A->bool)#(A->real^N))->bool) c (g:A->real^N^N) y **
      (matrix_inv(transp(matrix(frechet_derivative (f o chart_inv c) (at y))) **
                  matrix(frechet_derivative (f o chart_inv c) (at y))) **
       transp(matrix(frechet_derivative (f o chart_inv c) (at y)))) +
      (mat 1 - matrix(frechet_derivative (f o chart_inv c) (at y)) **
               (matrix_inv(transp(matrix(frechet_derivative (f o chart_inv c) (at y))) **
                           matrix(frechet_derivative (f o chart_inv c) (at y))) **
                transp(matrix(frechet_derivative (f o chart_inv c) (at y)))))` THEN
  SUBGOAL_THEN
   `!c y. (G0c:(A->bool)#(A->real^N)->real^N->real^K^K) c y =
      transp(matrix_inv(transp(matrix(frechet_derivative ((f:A->real^K) o chart_inv c) (at
          y))) **
                        matrix(frechet_derivative (f o chart_inv c) (at y))) **
             transp(matrix(frechet_derivative (f o chart_inv c) (at y)))) **
      metric_local (atlas:((A->bool)#(A->real^N))->bool) c (g:A->real^N^N) y **
      (matrix_inv(transp(matrix(frechet_derivative (f o chart_inv c) (at y))) **
                  matrix(frechet_derivative (f o chart_inv c) (at y))) **
       transp(matrix(frechet_derivative (f o chart_inv c) (at y)))) +
      (mat 1 - matrix(frechet_derivative (f o chart_inv c) (at y)) **
               (matrix_inv(transp(matrix(frechet_derivative (f o chart_inv c) (at y))) **
                           matrix(frechet_derivative (f o chart_inv c) (at y))) **
                transp(matrix(frechet_derivative (f o chart_inv c) (at y)))))`
  (LABEL_TAC "G0CDEF") THENL [EXPAND_TAC "G0c" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!c y. c IN atlas /\ y IN IMAGE (SND c) (FST c)
          ==> (G0:A->real^K^K)(chart_inv c y) =
              (G0c:(A->bool)#(A->real^N)->real^N->real^K^K) c y`
  (LABEL_TAC "CHEQ") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC GRGE_G0_CHART_EQ THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `g:A->real^N^N`; `f:A->real^K`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "G0DEF" ACCEPT_TAC; USE_THEN "G0CDEF" ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN topspace top ==> transp((G0:A->real^K^K) x) = G0 x`
  (LABEL_TAC "G0X") THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `x:A`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `f:A->real^K`; `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`;
                   `x:A`] GRGE_EMB_JAC_FACTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    USE_THEN "G0DEF" (fun th -> REWRITE_TAC[th; mfd_tproj]) THEN
    MATCH_MP_TAC GRGE_G0_SYM THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "G0DEF" (K ALL_TAC) THEN REMOVE_THEN "G0CDEF" (K ALL_TAC) THEN
  ABBREV_TAC
   `r = \z:real^K. mfd_emb_inv top (f:A->real^K) (closest_point (IMAGE f (topspace top))
       z)` THEN
  SUBGOAL_THEN
   `!z. (?p. p IN IMAGE (f:A->real^K) (topspace top) /\ dist(z,p) < d)
        ==> (r:real^K->A) z IN topspace top`
  (LABEL_TAC "RT") THENL
   [X_GEN_TAC `z:real^K` THEN
    DISCH_THEN(fun th -> USE_THEN "LOCZ" (MP_TAC o C MATCH_MP th)) THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real^K->bool` (X_CHOOSE_THEN `c:(A->bool)#(A->real^N)`
      (X_CHOOSE_THEN `Y:real^K->real^N` STRIP_ASSUME_TAC))) THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(z:real^K) IN B`)) THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) ((Y:real^K->real^N) z) IN topspace
        top`
    ASSUME_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
    EXPAND_TAC "r" THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `f:A->real^K`; `chart_inv (c:(A->bool)#(A->real^N)) ((Y:real^K->real^N)
                       z)`]
                  GRGE_EMB_INV_LEFT) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN topspace top ==> (r:real^K->A) ((f:A->real^K) x) = x`
  (LABEL_TAC "RF") THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN EXPAND_TAC "r" THEN
    SUBGOAL_THEN `closest_point (IMAGE (f:A->real^K) (topspace top)) (f x) = f x`
    SUBST1_TAC THENL
     [MATCH_MP_TAC CLOSEST_POINT_SELF THEN ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
    MATCH_MP_TAC GRGE_EMB_INV_LEFT THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Td = {z:real^K | ?p. p IN IMAGE (f:A->real^K) (topspace top) /\ dist(z,p) <
      d}` THEN
  SUBGOAL_THEN `open(Td:real^K->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Td" THEN REWRITE_TAC[GRGE_TUBE_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on Td ((vectorize:real^K^K->real^(K,K)finite_prod) o
                      (\z. (G0:A->real^K^K) ((r:real^K->A) z)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^K` THEN EXPAND_TAC "Td" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(fun th -> USE_THEN "LOCZ" (MP_TAC o C MATCH_MP th)) THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real^K->bool` (X_CHOOSE_THEN `c:(A->bool)#(A->real^N)`
      (X_CHOOSE_THEN `Y:real^K->real^N` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "BP")))))))) THEN
    EXISTS_TAC `B:real^K->bool` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `((vectorize:real^K^K->real^(K,K)finite_prod) o
                 (G0c:(A->bool)#(A->real^N)->real^N->real^K^K) c) o (Y:real^K->real^N)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `w:real^K` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN
      USE_THEN "BP" (MP_TAC o C MATCH_MP (ASSUME `(w:real^K) IN B`)) THEN STRIP_TAC THEN
      SUBGOAL_THEN `(r:real^K->A) w = chart_inv (c:(A->bool)#(A->real^N))
          ((Y:real^K->real^N) w)`
      SUBST1_TAC THENL
       [EXPAND_TAC "r" THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC GRGE_EMB_INV_LEFT THEN
        EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
        ALL_TAC] THEN
      CONV_TAC SYM_CONV THEN USE_THEN "CHEQ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
      EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `w:real^K` THEN DISCH_TAC THEN
        USE_THEN "BP" (MP_TAC o C MATCH_MP (ASSUME `(w:real^K) IN B`)) THEN SIMP_TAC[];
        EXPAND_TAC "G0c" THEN REWRITE_TAC[] THEN MATCH_MP_TAC CMT_G0C_SMOOTH_GEN THEN
        EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`{p + w | p IN IMAGE (f:A->real^K) (topspace top) /\ w IN cball(vec 0:real^K,d / &2)}`;
    `Td:real^K->bool`] GRGE_EUCLID_CUTOFF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_SUMS THEN ASM_REWRITE_TAC[COMPACT_CBALL];
      EXPAND_TAC "Td" THEN REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_ELIM_THM; IN_CBALL_0]
          THEN
      MAP_EVERY X_GEN_TAC [`p:real^K`; `w:real^K`] THEN STRIP_TAC THEN
      EXISTS_TAC `p:real^K` THEN
      ASM_REWRITE_TAC[NORM_ARITH `dist(p + w:real^N,p) = norm w`] THEN
      UNDISCH_TAC `norm(w:real^K) <= d / &2` THEN UNDISCH_TAC `&0 < d` THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:real^K->real` (X_CHOOSE_THEN `L:real^K->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "PSI01")
    (CONJUNCTS_THEN2 (LABEL_TAC "PSI1") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "PSI0")))))))) THEN
  SUBGOAL_THEN
   `!x z. x IN topspace top /\ dist(z,(f:A->real^K) x) <= d / &2
          ==> (psi:real^K->real) z = &1`
  (LABEL_TAC "PSIN") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "PSI1" MATCH_MP_TAC THEN
    REWRITE_TAC[IN_ELIM_THM; IN_CBALL_0] THEN
    MAP_EVERY EXISTS_TAC [`(f:A->real^K) x`; `z - (f:A->real^K) x`] THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM dist] THEN ASM_REWRITE_TAC[]; VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC
   `G = \z:real^K. (psi:real^K->real) z %% (G0:A->real^K^K) ((r:real^K->A) z) +
                   (&1 - psi z) %% mat 1` THEN
  SUBGOAL_THEN
   `!x. x IN topspace top ==> (G:real^K->real^K^K) ((f:A->real^K) x) = (G0:A->real^K^K) x`
  (LABEL_TAC "GFX") THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN EXPAND_TAC "G" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(psi:real^K->real) ((f:A->real^K) x) = &1` SUBST1_TAC THENL
     [USE_THEN "PSIN" MATCH_MP_TAC THEN EXISTS_TAC `x:A` THEN
      ASM_REWRITE_TAC[DIST_REFL] THEN UNDISCH_TAC `&0 < d` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "RF" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(x:A) IN topspace top`)]) THEN
    REWRITE_TAC[REAL_SUB_REFL; MATRIX_CMUL_LZERO; MATRIX_CMUL_LID; MATRIX_ADD_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o
                                         (G:real^K->real^K^K))`
  (LABEL_TAC "GSM") THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    X_GEN_TAC `z0:real^K` THEN ASM_CASES_TAC `(z0:real^K) IN Td` THENL
     [EXISTS_TAC `Td:real^K->bool` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `(vectorize:real^K^K->real^(K,K)finite_prod) o (G:real^K->real^K^K) =
        (\z. (psi:real^K->real) z %
             ((vectorize:real^K^K->real^(K,K)finite_prod) o
              (\z. (G0:A->real^K^K) ((r:real^K->A) z))) z +
             (&1 - psi z) % vectorize(mat 1:real^K^K))`
      SUBST1_TAC THENL
       [EXPAND_TAC "G" THEN REWRITE_TAC[FUN_EQ_THM; o_THM; VECTORIZE_ADD; VECTORIZE_CMUL];
        ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
      MATCH_MP_TAC GRGE_SMOOTH_SCALAR_MUL THEN
      ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; ETA_AX] THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^K)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV];
        REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
        ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^K)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV]];
      EXISTS_TAC `(:real^K) DIFF L` THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM closed] THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[IN_DIFF; IN_UNIV] THEN ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
      EXISTS_TAC `(\z. vectorize(mat 1:real^K^K)):real^K->real^(K,K)finite_prod` THEN
      REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM closed] THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
      REWRITE_TAC[IN_DIFF; IN_UNIV; o_THM] THEN X_GEN_TAC `w:real^K` THEN DISCH_TAC THEN
      AP_TERM_TAC THEN EXPAND_TAC "G" THEN REWRITE_TAC[] THEN
      USE_THEN "PSI0" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `~((w:real^K) IN L)`)])
          THEN
      REWRITE_TAC[MATRIX_CMUL_LZERO; REAL_SUB_RZERO; MATRIX_CMUL_LID; MATRIX_ADD_LID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. transp((G:real^K->real^K^K) z) = G z` (LABEL_TAC "GPD") THENL
   [X_GEN_TAC `z:real^K` THEN EXPAND_TAC "G" THEN REWRITE_TAC[] THEN
    ASM_CASES_TAC `(psi:real^K->real) z = &0` THENL
     [ASM_REWRITE_TAC[MATRIX_CMUL_LZERO; REAL_SUB_RZERO; MATRIX_CMUL_LID; MATRIX_ADD_LID;
                      TRANSP_MAT];
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^K) IN L` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(r:real^K->A) z IN topspace top` ASSUME_TAC THENL
     [USE_THEN "RT" MATCH_MP_TAC THEN
      SUBGOAL_THEN `(z:real^K) IN Td` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "Td" THEN REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    USE_THEN "G0X" (MP_TAC o C MATCH_MP (ASSUME `(r:real^K->A) z IN topspace top`)) THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[TRANSP_MATRIX_ADD; TRANSP_MATRIX_CMUL; TRANSP_MAT];
    ALL_TAC] THEN
  EXISTS_TAC `G:real^K->real^K^K` THEN
  CONJ_TAC THENL [USE_THEN "GSM" ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [USE_THEN "GPD" ACCEPT_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^N)`; `y:real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) y IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  USE_THEN "GFX" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
    `chart_inv (c:(A->bool)#(A->real^N)) y IN topspace top`)]) THEN
  USE_THEN "CHEQ" (fun th -> REWRITE_TAC[MATCH_MP th (CONJ
    (ASSUME `(c:(A->bool)#(A->real^N)) IN atlas`)
    (ASSUME `(y:real^N) IN IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`))]) THEN
  EXPAND_TAC "G0c" THEN REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC GRGE_G0_PULLBACK THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:A->real^K`; `c:(A->bool)#(A->real^N)`] GRGE_IMMERSION_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `linear(frechet_derivative ((f:A->real^K) o chart_inv (c:(A->bool)#(A->real^N)))
                              (at (y:real^N)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_WORKS] THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[]);;


let CM_AMBIENT_TENSOR = prove
 (`!top atlas (g:A->real^N^N) (f:A->real^K) (G:real^K->real^K^K) d (R:A->real^N^N).
     cm_emb (top,atlas) g f G d /\
     (!x. x IN topspace top ==> transp(R x) = R x) /\
     (!c. c IN atlas
          ==> smooth_map_on (IMAGE (SND c) (FST c))
                ((vectorize:real^N^N->real^(N,N)finite_prod) o metric_local atlas c R))
     ==> ?Q:real^K->real^K^K.
           smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) /\
           (!z. transp(Q z) = Q z) /\
           (!c w. c IN atlas /\ w IN IMAGE (SND c) (FST c)
                  ==> metric_local atlas c R w =
                      transp(matrix(frechet_derivative (f o chart_inv c) (at w))) **
                      Q(f(chart_inv c w)) **
                      matrix(frechet_derivative (f o chart_inv c) (at w)))`,
  REWRITE_TAC[cm_emb] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CMT_AMBIENT_EXT THEN EXISTS_TAC `top:A topology` THEN
  ASM_REWRITE_TAC[]);;

(* The Ricci matrix: symmetric (the argument of P4_RICCI_MATRIX_SYM of       *)
(* pc_p4_width, restated to keep the load closure small), its chart          *)
(* representatives are the local Ricci forms of the chart metrics, which    *)
(* are smooth.                                                               *)


let CMT_LRICCI_MATRIX = prove
 (`!U (G:real^N->real^N^N) y u v.
        metric_field U G /\ y IN U
        ==> u dot ((lambda i j. lricci G y (basis i) (basis j)):real^N^N ** v) =
            lricci G y u v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `u:real^N`;
                 `v:real^N`] LRG_LRICCI_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[dot] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN
  STRIP_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[matrix_vector_mul; LAMBDA_BETA] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC);;

let CMT_RICCI_CHART = prove
 (`!top atlas (g:A->real^N^N) c w.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        c IN atlas /\ w IN IMAGE (SND c) (FST c)
        ==> metric_local atlas c (mfd_ricci_matrix atlas g) w =
            (lambda i j. lricci (metric_local atlas c g) w (basis i) (basis j))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) w IN FST c /\ SND c (chart_inv c w) = w`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `x = chart_inv (c:(A->bool)#(A->real^N)) w` THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `c0:(A->bool)#(A->real^N)`; `x:A`]
                GRGE_CHART_JAC_INVERTIBLE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV) [metric_local] THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CMT_GRAM_ENTRY; MATRIX_WORKS] THEN
  REWRITE_TAC[mfd_ricci_matrix; mfd_ricci] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`IMAGE (SND(c0:(A->bool)#(A->real^N))) (FST c0)`;
                 `metric_local (atlas:((A->bool)#(A->real^N))->bool) c0 (g:A->real^N^N)`;
                 `SND(c0:(A->bool)#(A->real^N)) x`;
                 `chart_jac (c:(A->bool)#(A->real^N)) c0 x (basis i)`;
                 `chart_jac (c:(A->bool)#(A->real^N)) c0 x (basis j)`] CMT_LRICCI_MATRIX)
                     THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
    UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)`
        THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                 `g:A->real^N^N`; `x:A`; `basis i:real^N`; `basis j:real^N`]
                LRG_LRICCI_CHART_TRANS) THEN
  REWRITE_TAC[PAIR; IN_INTER] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ACCEPT_TAC o SYM));;

let CMT_LRICCI_SMOOTH_STATIC = prove
 (`!U (G:real^N->real^N^N) v w.
        metric_field U G ==> smooth_map_on U (\y. lift(lricci G y v w))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[metric_field]) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `&0`; `&1`; `\t:real. (G:real^N->real^N^N)`;
                 `v:real^N`; `w:real^N`] LRG_LSMOOTH_LRICCI) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[lrg_lsmooth; REAL_LT_01] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(\z:real^(1,N)finite_sum. (vectorize:real^N^N->real^(N,N)finite_prod)
                                 (G(sndcart z))) =
      (vectorize o (G:real^N->real^N^N)) o sndcart`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; GRGE_SMOOTH_LINEAR; LINEAR_SNDCART] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; SNDCART_PASTECART] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(\y. lift(lricci (G:real^N->real^N^N) y v w)) =
    (\z:real^(1,N)finite_sum. lift(lricci G (sndcart z) v w)) o
    (\y. pastecart (lift(&1 / &2)) y)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; SNDCART_PASTECART]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `interval(lift(&0),lift(&1)) PCROSS (U:real^N->bool)` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    SIMP_TAC[] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_ID]]);;

let CM_AMBIENT_RICCI = prove
 (`!top atlas (g:A->real^N^N) (f:A->real^K) (G:real^K->real^K^K) d.
     cm_emb (top,atlas) g f G d
     ==> ?Q:real^K->real^K^K.
           smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) /\
           (!z. transp(Q z) = Q z) /\
           (!c w. c IN atlas /\ w IN IMAGE (SND c) (FST c)
                  ==> metric_local atlas c (mfd_ricci_matrix atlas g) w =
                      transp(matrix(frechet_derivative (f o chart_inv c) (at w))) **
                      Q(f(chart_inv c w)) **
                      matrix(frechet_derivative (f o chart_inv c) (at w)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CM_AMBIENT_TENSOR THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `g:A->real^N^N`; `G:real^K->real^K^K`; `d:real`]
      THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[cm_emb]) THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P4_RICCI_MATRIX_SYM THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND c) (FST c))
                 (metric_local (atlas:((A->bool)#(A->real^N))->bool) c (g:A->real^N^N))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)`
       THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[metric_field]) THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `(vectorize:real^N^N->real^(N,N)finite_prod) o
              (\w. (lambda i j. lricci (metric_local atlas c (g:A->real^N^N)) w
                                       (basis i) (basis j)):real^N^N)` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC CMT_RICCI_CHART THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GRGE_SMOOTH_VECTORIZE] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[LAMBDA_BETA] THEN MATCH_MP_TAC CMT_LRICCI_SMOOTH_STATIC THEN
  ASM_REWRITE_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* T8 (maps of S^2): regularity transfers between the chart picture and the *)
(* radial extension of f o u.  One direction composes the chart maps with   *)
(* f o chart_inv c; the other uses the retraction r = mfd_emb_inv o closest  *)
(* point, whose chart maps SND c o r are smooth on open subsets of the tube.  *)
(* ------------------------------------------------------------------------- *)

let CMT_P4_TO_EMB_N = prove
 (`!top atlas (f:A->real^K) (u:real^3->A) n.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        smooth_immersion_into atlas f /\
        continuous_map (subtopology euclidean (sphere(vec 0:real^3,&1)),top) u /\
        (!c. c IN atlas
             ==> continuously_differentiable n
                   {z:real^3 | ~(z = vec 0) /\ u(inv(norm z) % z) IN FST c}
                   (\z. SND c (u(inv(norm z) % z))))
        ==> continuously_differentiable n {z:real^3 | ~(z = vec 0)} (wan_rext (f o u))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `{z:real^3 | ~(z = vec 0)}`;
                 `wan_rext ((f:A->real^K) o (u:real^3->A))`]
                CONTINUOUSLY_DIFFERENTIABLE_LOCAL_OPEN) THEN
  REWRITE_TAC[CMT_OPEN_NONZERO] THEN DISCH_THEN SUBST1_TAC THEN
  X_GEN_TAC `z0:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(u:real^3->A)(inv(norm z0) % z0) IN topspace top` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; SUBSET; FORALL_IN_IMAGE] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[P4_RADIAL_SPHERE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(u:real^3->A)(inv(norm z0) % z0)`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool)
                           ((u:real^3->A)(inv(norm z0) % z0))` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:A->real^K`; `c:(A->bool)#(A->real^N)`] GRGE_IMMERSION_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `open {z:real^3 | ~(z = vec 0) /\
                     (u:real^3->A)(inv(norm z) % z) IN FST(c:(A->bool)#(A->real^N))}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMT_CHART_SET_OPEN THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `{z:real^3 | ~(z = vec 0) /\
                          (u:real^3->A)(inv(norm z) % z) IN FST(c:(A->bool)#(A->real^N))}`
                              THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_EQ_OPEN THEN
  EXISTS_TAC `((f:A->real^K) o chart_inv (c:(A->bool)#(A->real^N))) o
              (\z:real^3. SND c ((u:real^3->A)(inv(norm z) % z)))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_ELIM_THM; o_THM; wan_rext] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_COMPOSE_OPEN THEN
  EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    SIMP_TAC[FUN_IN_IMAGE];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `smooth_map_on (IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))
                               ((f:A->real^K) o chart_inv c)` THEN
    SIMP_TAC[smooth_map_on]]);;

let CM_P4_TO_EMB = prove
 (`!top atlas (g:A->real^N^N) (f:A->real^K) (G:real^K->real^K^K) d (u:real^3->A).
     cm_emb (top,atlas) g f G d
     ==> (p4_s2_c1 (top,atlas) u
          ==> continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext (f o u))) /\
         (p4_s2_smooth (top,atlas) u
          ==> smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext (f o u)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cm_emb; mfd_embedding] THEN STRIP_TAC THEN
  REWRITE_TAC[p4_s2_c1; p4_s2_smooth; smooth_map_on] THEN CONJ_TAC THEN STRIP_TAC THENL
   [MATCH_MP_TAC CMT_P4_TO_EMB_N THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `n:num` THEN MATCH_MP_TAC CMT_P4_TO_EMB_N THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_SIMP_TAC[]]);;

let CMT_EMB_INV_RIGHT = prove
 (`!top (f:A->real^K) p.
        p IN IMAGE f (topspace top)
        ==> mfd_emb_inv top f p IN topspace top /\ f(mfd_emb_inv top f p) = p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_IMAGE; mfd_emb_inv] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
  CONV_TAC SELECT_CONV THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]);;

let CMT_EMB_INV_CONTINUOUS = prove
 (`!top atlas (f:A->real^K).
        mfd_embedding (top,atlas:((A->bool)#(A->real^N))->bool) f
        ==> continuous_map (subtopology euclidean (IMAGE f (topspace top)),top)
                           (mfd_emb_inv top f)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o REWRITE_RULE[mfd_embedding]) THEN
  REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS; homeomorphic_maps; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^K->A` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN EXISTS_TAC `h:real^K->A` THEN
  ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  X_GEN_TAC `p:real^K` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(h:real^K->A) p IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `continuous_map (subtopology euclidean (IMAGE (f:A->real^K) (topspace top)),
                                 top) (h:real^K->A)` THEN
    DISCH_THEN(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN
  SUBGOAL_THEN `mfd_emb_inv top (f:A->real^K) p = mfd_emb_inv top f (f((h:real^K->A) p))`
  SUBST1_TAC THENL [AP_TERM_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC GRGE_EMB_INV_LEFT THEN
  EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[]);;

let CMT_RETRACT_SMOOTH = prove
 (`!top atlas (f:A->real^K).
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        compact_space top /\ mfd_embedding (top,atlas) f
        ==> ?d. &0 < d /\
                !c. c IN atlas
                    ==> open {z | (?p. p IN IMAGE f (topspace top) /\ dist(z,p) < d) /\
                                 mfd_emb_inv top f (closest_point (IMAGE f (topspace top))
                                     z)
                                 IN FST c} /\
                        smooth_map_on
                          {z | (?p. p IN IMAGE f (topspace top) /\ dist(z,p) < d) /\
                               mfd_emb_inv top f (closest_point (IMAGE f (topspace top)) z)
                               IN FST c}
                          (\z. SND c (mfd_emb_inv top f
                                        (closest_point (IMAGE f (topspace top)) z)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `f:A->real^K`]
                GRGE_TUBE_LOCZ) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LOCZ"))) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!z1. z1 IN {z | (?p. p IN IMAGE (f:A->real^K) (topspace top) /\ dist(z,p) < d) /\
                    mfd_emb_inv top f (closest_point (IMAGE f (topspace top)) z) IN
                    FST (c:(A->bool)#(A->real^N))}
         ==> ?N. open N /\ z1 IN N /\
                 N SUBSET {z | (?p. p IN IMAGE f (topspace top) /\ dist(z,p) < d) /\
                               mfd_emb_inv top f (closest_point (IMAGE f (topspace top)) z)
                               IN FST c} /\
                 smooth_map_on N
                   (\z. SND c (mfd_emb_inv top f (closest_point (IMAGE f (topspace top))
                       z)))`
  (LABEL_TAC "LOC") THENL
   [X_GEN_TAC `z1:real^K` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "TUB") ASSUME_TAC) THEN
    USE_THEN "TUB" (fun th -> USE_THEN "LOCZ" (MP_TAC o C MATCH_MP th)) THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real^K->bool` (X_CHOOSE_THEN `c'':(A->bool)#(A->real^N)`
      (X_CHOOSE_THEN `Y:real^K->real^N` STRIP_ASSUME_TAC))) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `f:A->real^K`;
                   `B:real^K->bool`; `c'':(A->bool)#(A->real^N)`; `Y:real^K->real^N`;
                   `c:(A->bool)#(A->real^N)`;
                   `{z:real^K | ?p. p IN IMAGE (f:A->real^K) (topspace top) /\ dist(z,p) <
                       d}`;
                   `z1:real^K`] GRGE_TUBE_RETRACT_LOCAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[GRGE_TUBE_OPEN; IN_ELIM_THM]; REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open {z | (?p. p IN IMAGE (f:A->real^K) (topspace top) /\ dist(z,p) < d) /\
              mfd_emb_inv top f (closest_point (IMAGE f (topspace top)) z) IN
              FST (c:(A->bool)#(A->real^N))}`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [OPEN_SUBOPEN] THEN X_GEN_TAC `z1:real^K` THEN
    DISCH_THEN(fun th -> USE_THEN "LOC" (MP_TAC o C MATCH_MP th)) THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z1:real^K` THEN
  DISCH_THEN(fun th -> USE_THEN "LOC" (MP_TAC o C MATCH_MP th)) THEN MESON_TAC[]);;

let CMT_EMB_TO_P4_N = prove
 (`!top atlas (f:A->real^K) (w:real^3->real^K) n.
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        compact_space top /\ mfd_embedding (top,atlas) f /\
        (!y. y IN sphere(vec 0,&1) ==> w y IN IMAGE f (topspace top)) /\
        continuously_differentiable n {z:real^3 | ~(z = vec 0)} (wan_rext w)
        ==> continuous_map (subtopology euclidean (sphere(vec 0:real^3,&1)),top)
                           (mfd_emb_inv top f o w) /\
            !c. c IN atlas
                ==> continuously_differentiable n
                      {z:real^3 | ~(z = vec 0) /\
                                  (mfd_emb_inv top f o w)(inv(norm z) % z) IN FST c}
                      (\z. SND c ((mfd_emb_inv top f o w)(inv(norm z) % z)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `continuous_map (subtopology euclidean (sphere(vec 0:real^3,&1)),top)
                   (mfd_emb_inv top (f:A->real^K) o (w:real^3->real^K))`
  (LABEL_TAC "CV") THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean (IMAGE (f:A->real^K) (topspace top))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN EXISTS_TAC `wan_rext (w:real^3->real^K)` THEN
        SIMP_TAC[CM_REXT_SPHERE] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
          EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_SPHERE_0] THEN X_GEN_TAC `x:real^3` THEN
          ASM_CASES_TAC `x:real^3 = vec 0` THEN ASM_REWRITE_TAC[NORM_0] THEN
          REAL_ARITH_TAC];
        ASM SET_TAC[]];
      MATCH_MP_TAC CMT_EMB_INV_CONTINUOUS THEN
      EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `f:A->real^K`]
                CMT_RETRACT_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "RS"))) THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  USE_THEN "RS" (MP_TAC o C MATCH_MP (ASSUME `(c:(A->bool)#(A->real^N)) IN atlas`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  SUBGOAL_THEN
   `open {z:real^3 | ~(z = vec 0) /\
                     (mfd_emb_inv top (f:A->real^K) o (w:real^3->real^K))(inv(norm z) % z)
                     IN FST(c:(A->bool)#(A->real^N))}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMT_CHART_SET_OPEN THEN EXISTS_TAC `top:A topology` THEN
    REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_EQ_OPEN THEN
  EXISTS_TAC `(\z. SND (c:(A->bool)#(A->real^N))
                       (mfd_emb_inv top (f:A->real^K)
                          (closest_point (IMAGE f (topspace top)) z))) o
              wan_rext (w:real^3->real^K)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_ELIM_THM; o_THM] THEN STRIP_TAC THEN
    REWRITE_TAC[wan_rext] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC CLOSEST_POINT_SELF THEN ASM_SIMP_TAC[P4_RADIAL_SPHERE];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_COMPOSE_OPEN THEN
  EXISTS_TAC `{z | (?p. p IN IMAGE (f:A->real^K) (topspace top) /\ dist(z,p) < d) /\
                   mfd_emb_inv top f (closest_point (IMAGE f (topspace top)) z) IN
                   FST (c:(A->bool)#(A->real^N))}` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; o_THM] THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN REWRITE_TAC[wan_rext] THEN
    SUBGOAL_THEN `(w:real^3->real^K)(inv(norm z) % z) IN IMAGE (f:A->real^K) (topspace top)`
    ASSUME_TAC THENL [ASM_SIMP_TAC[P4_RADIAL_SPHERE]; ALL_TAC] THEN
    ASM_SIMP_TAC[CLOSEST_POINT_SELF] THEN
    EXISTS_TAC `(w:real^3->real^K)(inv(norm z) % z)` THEN
    ASM_REWRITE_TAC[DIST_REFL];
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN
    EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    UNDISCH_TAC
     `smooth_map_on
        {z | (?p. p IN IMAGE (f:A->real^K) (topspace top) /\ dist(z,p) < d) /\
             mfd_emb_inv top f (closest_point (IMAGE f (topspace top)) z) IN
             FST (c:(A->bool)#(A->real^N))}
        (\z. SND c (mfd_emb_inv top f (closest_point (IMAGE f (topspace top)) z)))` THEN
    SIMP_TAC[smooth_map_on]]);;

let CM_EMB_TO_P4 = prove
 (`!top atlas (g:A->real^N^N) (f:A->real^K) (G:real^K->real^K^K) d (w:real^3->real^K).
     cm_emb (top,atlas) g f G d /\
     (!y. y IN sphere(vec 0,&1) ==> w y IN IMAGE f (topspace top))
     ==> (continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext w)
          ==> p4_s2_c1 (top,atlas) (mfd_emb_inv top f o w)) /\
         (smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext w)
          ==> p4_s2_smooth (top,atlas) (mfd_emb_inv top f o w))`,
  REWRITE_TAC[cm_emb] THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[p4_s2_c1] THEN MATCH_MP_TAC CMT_EMB_TO_P4_N THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[p4_s2_smooth] THEN
    MP_TAC(GEN `n:num` (ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                                `f:A->real^K`; `w:real^3->real^K`; `n:num`]
                               CMT_EMB_TO_P4_N)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[smooth_map_on]) THEN
    ASM_REWRITE_TAC[smooth_map_on] THEN MESON_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* T5 preparation: the classical form of the CM trace integral.  For a     *)
(* positive semidefinite Gram matrix A and a symmetric B with |B| <= c A as *)
(* quadratic forms, |e2_pol(A,B)| <= 2 c e2(A) (trace(A P) <= trace A       *)
(* trace P for positive semidefinite A, P), so the trace density is bounded *)
(* by 2 c sqrt(e2 A); it is measurable (continuous where e2 A is nonzero).  *)
(* ------------------------------------------------------------------------- *)

let CMT_POL_CMUL = prove
 (`!c (a:real^3^3) b.
        p4_e2_pol (c %% a) (c %% b) = c pow 2 * p4_e2_pol a b /\
        p4_e2_pol a (c %% a - b) = &2 * c * p4_e2 a - p4_e2_pol a b /\
        p4_e2_pol a (c %% a + b) = &2 * c * p4_e2 a + p4_e2_pol a b`,
  REWRITE_TAC[p4_e2_pol; p4_e2; TRACE_SUB; TRACE_ADD; TRACE_CMUL; MATRIX_SUB_LDISTRIB;
              MATRIX_ADD_LDISTRIB; MATRIX_MUL_RMUL; MATRIX_MUL_LMUL; MATRIX_CMUL_ASSOC] THEN
  REAL_ARITH_TAC);;


let CMT_POL_BOUND = prove
 (`!(A:real^3^3) B c.
        positive_semidefinite A /\ symmetric_matrix B /\
        (!v. abs(v dot (B ** v)) <= c * (v dot (A ** v)))
        ==> abs(p4_e2_pol A B) <= &2 * c * p4_e2 A`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "BD"))) THEN
  SUBGOAL_THEN `positive_semidefinite(c %% A - B:real^3^3) /\
                positive_semidefinite(c %% A + B:real^3^3)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `positive_semidefinite(A:real^3^3)` THEN
    UNDISCH_TAC `symmetric_matrix(B:real^3^3)` THEN
    REWRITE_TAC[positive_semidefinite; symmetric_matrix] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[TRANSP_MATRIX_SUB; TRANSP_MATRIX_ADD; TRANSP_MATRIX_CMUL] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB; MATRIX_VECTOR_MUL_ADD_RDISTRIB;
                MATRIX_VECTOR_LMUL; DOT_RSUB; DOT_RADD; DOT_RMUL] THEN
    USE_THEN "BD" (MP_TAC o SPEC `x:real^3`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`A:real^3^3`; `c %% A - B:real^3^3`] TRACE_MUL_POSITIVE_SEMIDEFINITE_LE)
      THEN
  MP_TAC(ISPECL [`A:real^3^3`; `c %% A + B:real^3^3`] TRACE_MUL_POSITIVE_SEMIDEFINITE_LE)
      THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[p4_e2_pol; p4_e2; TRACE_SUB; TRACE_ADD; TRACE_CMUL; MATRIX_SUB_LDISTRIB;
              MATRIX_ADD_LDISTRIB; MATRIX_MUL_RMUL] THEN
  REAL_ARITH_TAC);;

let CMT_QUAD_BOUND = prove
 (`!(Q:real^K->real^K^K) k.
        (vectorize o Q) continuous_on k /\ compact k
        ==> ?M. &0 <= M /\ !p v. p IN k ==> abs(v dot (Q p ** v)) <= M * norm v pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(vectorize:real^K^K->real^(K,K)finite_prod) o (Q:real^K->real^K^K)`;
                 `k:real^K->bool`] COMPACT_CONTINUOUS_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; o_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `b:real` THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  MAP_EVERY X_GEN_TAC [`p:real^K`; `v:real^K`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `norm((Q:real^K->real^K^K) p ** v) <= b * norm(v:real^K)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `onorm(\x. (Q:real^K->real^K^K) p ** x) * norm(v:real^K)` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPEC `\x. (Q:real^K->real^K^K) p ** x` ONORM) THEN
      REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN SIMP_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm(vectorize((Q:real^K->real^K^K) p))` THEN
      REWRITE_TAC[ONORM_LE_NORM_VECTORIZE] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(v:real^K) * norm((Q:real^K->real^K^K) p ** v) <=
                norm v * (b * norm v)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`v:real^K`; `(Q:real^K->real^K^K) p ** v`] NORM_CAUCHY_SCHWARZ_ABS) THEN
  UNDISCH_TAC `norm(v:real^K) * norm((Q:real^K->real^K^K) p ** v) <=
               norm v * (b * norm v)` THEN
  REAL_ARITH_TAC);;

let CMT_TRDENS_HOMOG = prove
 (`!(A:real^3^3) B c.
        &0 < c
        ==> (if p4_e2(c %% A) = &0 then &0
             else p4_e2_pol (c %% A) (c %% B) / sqrt(p4_e2(c %% A))) =
            c * (if p4_e2 A = &0 then &0 else p4_e2_pol A B / sqrt(p4_e2 A))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CMT_E2_CMUL; CMT_POL_CMUL] THEN
  SUBGOAL_THEN `~(c = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_ENTIRE; REAL_POW_EQ_0; ARITH_EQ] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
  REWRITE_TAC[SQRT_MUL; POW_2_SQRT_ABS] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < c ==> abs c = c`] THEN
  SUBGOAL_THEN `~(sqrt(p4_e2(A:real^3^3)) = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[SQRT_EQ_0]; ALL_TAC] THEN
  UNDISCH_TAC `~(c = &0)` THEN CONV_TAC REAL_FIELD);;

let CMT_CONT_POL = prove
 (`!s (A:real^M->real^3^3) B.
        (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
               ==> (\x. lift(A x$i$j)) continuous_on s) /\
        (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
               ==> (\x. lift(B x$i$j)) continuous_on s)
        ==> (\x. lift(p4_e2_pol (A x) (B x))) continuous_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p4_e2_pol; LIFT_SUB; LIFT_CMUL] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[o_DEF] THEN CONJ_TAC THEN
    MATCH_MP_TAC CMT_CONT_TRACE THEN ASM_REWRITE_TAC[DIMINDEX_3];
    MATCH_MP_TAC CMT_CONT_TRACE THEN REWRITE_TAC[DIMINDEX_3] THEN
    MP_TAC(ISPECL [`s:real^M->bool`; `A:real^M->real^3^3`; `B:real^M->real^3^3`]
                  CMT_CONT_MATMUL) THEN
    ASM_REWRITE_TAC[DIMINDEX_3]]);;

let CMT_TRDENS_MEASURABLE = prove
 (`!(A:real^3->real^3^3) B.
        (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
               ==> (\x. lift(A x$i$j)) continuous_on {z:real^3 | ~(z = vec 0)}) /\
        (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
               ==> (\x. lift(B x$i$j)) continuous_on {z:real^3 | ~(z = vec 0)})
        ==> (\z. lift(if p4_e2(A z) = &0 then &0
                      else p4_e2_pol (A z) (B z) / sqrt(p4_e2(A z))))
            measurable_on (:real^3)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `E = {z:real^3 | z IN {z | ~(z = vec 0)} /\
                    lift(p4_e2((A:real^3->real^3^3) z)) IN {y:real^1 | ~(y = vec 0)}}` THEN
  SUBGOAL_THEN `open(E:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    REWRITE_TAC[CMT_OPEN_NONZERO] THEN MATCH_MP_TAC CMT_CONT_E2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^3. z IN E <=> ~(z = vec 0) /\ ~(p4_e2((A:real^3->real^3^3) z) = &0)`
  ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN REWRITE_TAC[IN_ELIM_THM; GSYM LIFT_NUM; LIFT_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `(E:real^3->bool) SUBSET {z:real^3 | ~(z = vec 0)}` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. lift(p4_e2_pol ((A:real^3->real^3^3) z) (B z) / sqrt(p4_e2(A z))))
    continuous_on E`
  ASSUME_TAC THENL
   [REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[LIFT_CMUL]
       THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_INV) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_LIFT_SQRT_COMPOSE THEN REWRITE_TAC[o_DEF] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC CMT_CONT_E2 THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[SQRT_EQ_0] THEN MESON_TAC[]];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CMT_CONT_POL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] MEASURABLE_ON_SPIKE) THEN
  EXISTS_TAC `\z:real^3. if z IN E
                         then lift(p4_e2_pol ((A:real^3->real^3^3) z) (B z) /
                                   sqrt(p4_e2(A z)))
                         else vec 0` THEN
  EXISTS_TAC `{vec 0:real^3}` THEN REWRITE_TAC[NEGLIGIBLE_SING] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_DIFF; IN_UNIV; IN_SING] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[LIFT_NUM];
    REWRITE_TAC[MEASURABLE_ON_UNIV] THEN
    MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN]]);;

let CMT_REXT_WD_AE = prove
 (`!u:real^3->real^K.
        continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext u)
        ==> wan_w12 wan_shell (wan_rext u) /\
            !i. 1 <= i /\ i <= 3
                ==> negligible {x | x IN wan_shell /\
                                    ~(wan_wd wan_shell i (wan_rext u) x =
                                      partial_derivative i (wan_rext u) x)}`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`{z:real^3 | ~(z = vec 0)}`; `wan_rext (u:real^3->real^K)`]
                CMT_C1_FACTS) THEN
  ASM_REWRITE_TAC[CMT_OPEN_NONZERO; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "UC") (CONJUNCTS_THEN2 (LABEL_TAC "UD")
    (CONJUNCTS_THEN2 (LABEL_TAC "PD") (LABEL_TAC "PC" o REWRITE_RULE[ETA_AX])))) THEN
  MP_TAC(REWRITE_RULE[WAN_W12_C1_STATEMENT] (ISPECL [`(:3)`; `(:K)`] WAN_W12_C1)) THEN
  DISCH_THEN(MP_TAC o SPECL [`wan_shell`; `wan_rext (u:real^3->real^K)`]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[CMT_SHELL_OPEN];
      MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN
      EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REWRITE_TAC[CMT_SHELL_NONZERO];
      MATCH_MP_TAC CMT_CONT_LSPACE_SHELL THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC CMT_CONT_LSPACE_SHELL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "W12") (CONJUNCTS_THEN2
    (LABEL_TAC "WPD" o REWRITE_RULE[ETA_AX]) (K ALL_TAC))) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_WD_UNIQUE THEN REWRITE_TAC[ETA_AX] THEN
  ASM_SIMP_TAC[DIMINDEX_3; CMT_SHELL_OPEN]);;


let CMT_TRDENS_BOUND = prove
 (`!(J:real^3^K) (Gp:real^K^K) (Qp:real^K^K) lam M.
        &0 < lam /\ &0 <= M /\ transp Gp = Gp /\ transp Qp = Qp /\
        (!v. lam * norm v pow 2 <= v dot (Gp ** v)) /\
        (!v. abs(v dot (Qp ** v)) <= M * norm v pow 2)
        ==> abs(if p4_e2(transp J ** Gp ** J) = &0 then &0
                else p4_e2_pol (transp J ** Gp ** J) (transp J ** Qp ** J) /
                     sqrt(p4_e2(transp J ** Gp ** J)))
            <= &2 * (M / lam) * sqrt(p4_e2(transp J ** Gp ** J))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "GL") (LABEL_TAC "QB")))))) THEN
  SUBGOAL_THEN `positive_semidefinite(transp J ** (Gp:real^K^K) ** (J:real^3^K))`
  ASSUME_TAC THENL
   [REWRITE_TAC[positive_semidefinite; symmetric_matrix; P4_GRAM_QF_GEN] THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[MATRIX_TRANSP_MUL; TRANSP_TRANSP; MATRIX_MUL_ASSOC];
      X_GEN_TAC `v:real^3` THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `lam * norm((J:real^3^K) ** v) pow 2` THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_LE_POW_2]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(p4_e2_pol (transp J ** Gp ** J) (transp J ** (Qp:real^K^K) ** (J:real^3^K))) <=
    &2 * (M / lam) * p4_e2 (transp J ** Gp ** J)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMT_POL_BOUND THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[symmetric_matrix; MATRIX_TRANSP_MUL; TRANSP_TRANSP; MATRIX_MUL_ASSOC];
      ALL_TAC] THEN
    X_GEN_TAC `v:real^3` THEN REWRITE_TAC[P4_GRAM_QF_GEN] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `M * norm((J:real^3^K) ** v) pow 2` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `M * norm((J:real^3^K) ** v) pow 2 =
                  (M / lam) * (lam * norm(J ** v) pow 2)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= p4_e2(transp J ** (Gp:real^K^K) ** (J:real^3^K))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[P4_E2_PSD]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= M / lam` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE]; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[REAL_ABS_NUM] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_MUL; SQRT_POS_LE]];
    ALL_TAC] THEN
  ABBREV_TAC `e = p4_e2(transp J ** (Gp:real^K^K) ** (J:real^3^K))` THEN
  SUBGOAL_THEN `&0 < sqrt e` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < s ==> abs s = s`; REAL_LE_LDIV_EQ] THEN
  SUBGOAL_THEN `sqrt e * sqrt e = e` (fun th -> ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC; th])
      THEN
  ASM_SIMP_TAC[GSYM REAL_POW_2; SQRT_POW_2]);;

let CMT_CLASSICAL_TRACE = prove
 (`!(G:real^K->real^K^K) (Q:real^K->real^K^K) (u:real^3->real^K) lam.
     continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext u) /\
     smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o G) /\
     smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) /\
     (!z. transp(G z) = G z) /\ (!z. transp(Q z) = Q z) /\
     &0 < lam /\ (!z v. lam * norm v pow 2 <= v dot (G z ** v))
     ==> cm_strace G Q u =
         p4_s2_integral
          (\y. if p4_e2(transp(jacobian (wan_rext u) (at y)) ** G(u y) **
                        jacobian (wan_rext u) (at y)) = &0
               then &0
               else p4_e2_pol (transp(jacobian (wan_rext u) (at y)) ** G(u y) **
                               jacobian (wan_rext u) (at y))
                              (transp(jacobian (wan_rext u) (at y)) ** Q(u y) **
                               jacobian (wan_rext u) (at y)) /
                    sqrt(p4_e2(transp(jacobian (wan_rext u) (at y)) ** G(u y) **
                               jacobian (wan_rext u) (at y))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "C1") (CONJUNCTS_THEN2 (LABEL_TAC "GS")
    (CONJUNCTS_THEN2 (LABEL_TAC "QS") (CONJUNCTS_THEN2 (LABEL_TAC "GT")
    (CONJUNCTS_THEN2 (LABEL_TAC "QT") (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "GL")))))))
        THEN
  MP_TAC(ISPECL [`{z:real^3 | ~(z = vec 0)}`; `wan_rext (u:real^3->real^K)`]
                CMT_C1_FACTS) THEN
  ASM_REWRITE_TAC[CMT_OPEN_NONZERO; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "UC") (CONJUNCTS_THEN2 (LABEL_TAC "UD")
    (CONJUNCTS_THEN2 (LABEL_TAC "PD") (LABEL_TAC "PC" o REWRITE_RULE[ETA_AX])))) THEN
  SUBGOAL_THEN
   `((vectorize:real^K^K->real^(K,K)finite_prod) o (G:real^K->real^K^K))
    continuous_on (:real^K) /\
    ((vectorize:real^K^K->real^(K,K)finite_prod) o (Q:real^K->real^K^K))
    continuous_on (:real^K)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
    EXISTS_TAC `0` THENL
     [USE_THEN "GS" (MP_TAC o REWRITE_RULE[smooth_map_on]);
      USE_THEN "QS" (MP_TAC o REWRITE_RULE[smooth_map_on])] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!(X:real^K->real^K^K).
      ((vectorize:real^K^K->real^(K,K)finite_prod) o X) continuous_on (:real^K)
      ==> !i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
                ==> (\x. lift((transp(jacobian (wan_rext (u:real^3->real^K)) (at x)) **
                               X(wan_rext u x) ** jacobian (wan_rext u) (at x))$i$j))
                    continuous_on {z:real^3 | ~(z = vec 0)}`
  (LABEL_TAC "GRC") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `\x. lift(partial_derivative i (wan_rext (u:real^3->real^K)) x dot
                         ((X:real^K->real^K^K)(wan_rext u x) **
                          partial_derivative j (wan_rext u) x))` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN AP_TERM_TAC THEN
      MP_TAC(ISPECL [`jacobian (wan_rext (u:real^3->real^K)) (at x)`;
                     `(X:real^K->real^K^K)(wan_rext (u:real^3->real^K) x)`;
                     `i:num`; `j:num`] CMT_GRAM_ENTRY) THEN
      ASM_SIMP_TAC[DIMINDEX_3];
      MATCH_MP_TAC CMT_CONT_QUAD THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!(X:real^K->real^K^K) t z.
      &0 < t /\ ~(z = vec 0)
      ==> transp(jacobian (wan_rext (u:real^3->real^K)) (at (t % z))) **
          X(wan_rext u (t % z)) ** jacobian (wan_rext u) (at (t % z)) =
          inv(t pow 2) %%
          (transp(jacobian (wan_rext u) (at z)) ** X(wan_rext u z) **
           jacobian (wan_rext u) (at z))`
  (LABEL_TAC "GH") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMT_REXT_GRAM_HOMOG THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC
   `\z. if p4_e2(transp(jacobian (wan_rext (u:real^3->real^K)) (at z)) **
                 (G:real^K->real^K^K)(wan_rext u z) ** jacobian (wan_rext u) (at z)) = &0
        then &0
        else p4_e2_pol (transp(jacobian (wan_rext u) (at z)) ** G(wan_rext u z) **
                        jacobian (wan_rext u) (at z))
                       (transp(jacobian (wan_rext u) (at z)) **
                        (Q:real^K->real^K^K)(wan_rext u z) ** jacobian (wan_rext u) (at z))
                            /
             sqrt(p4_e2(transp(jacobian (wan_rext u) (at z)) ** G(wan_rext u z) **
                        jacobian (wan_rext u) (at z)))` CM_SHELL_INTEGRAL) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CMT_TRDENS_MEASURABLE THEN CONJ_TAC THEN
      USE_THEN "GRC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`Q:real^K->real^K^K`;
                     `IMAGE (wan_rext (u:real^3->real^K)) (sphere(vec 0,&1))`]
                    CMT_QUAD_BOUND) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^K)` THEN
          ASM_REWRITE_TAC[SUBSET_UNIV];
          MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN REWRITE_TAC[COMPACT_SPHERE] THEN
          MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
          EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_SPHERE_0] THEN X_GEN_TAC `x:real^3` THEN
          ASM_CASES_TAC `x:real^3 = vec 0` THEN ASM_REWRITE_TAC[NORM_0] THEN
          REAL_ARITH_TAC];
        DISCH_THEN(X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC)] THEN
      MP_TAC(ISPEC `\z. sqrt(p4_e2(transp(jacobian (wan_rext (u:real^3->real^K)) (at z)) **
                                   (G:real^K->real^K^K)(wan_rext u z) **
                                   jacobian (wan_rext u) (at z)))`
                   CMT_CONT_SPHERE_BOUND) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_SQRT_COMPOSE THEN
        REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC CMT_CONT_E2 THEN
        USE_THEN "GRC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `Bs:real`)] THEN
      EXISTS_TAC `&2 * (M / lam) * Bs` THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&2 * (M / lam) *
                  sqrt(p4_e2(transp(jacobian (wan_rext (u:real^3->real^K)) (at y)) **
                             (G:real^K->real^K^K)(wan_rext u y) **
                             jacobian (wan_rext u) (at y)))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CMT_TRDENS_BOUND THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE] THEN
        MATCH_MP_TAC(REAL_ARITH `abs x <= b ==> x <= b`) THEN ASM_SIMP_TAC[]];
      REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC CMT_TRDENS_HOMOG THEN ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_POW_LT]];
    REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "TT")] THEN
  MP_TAC(ISPEC `u:real^3->real^K` CMT_REXT_WD_AE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NEG")) THEN
  REWRITE_TAC[cm_strace] THEN
  SUBGOAL_THEN
   `integral wan_shell
     (\z. lift(if p4_e2(cm_wgram wan_shell (G:real^K->real^K^K)
                                 (wan_rext (u:real^3->real^K)) z) = &0
               then &0
               else p4_e2_pol (cm_wgram wan_shell G (wan_rext u) z)
                              (cm_wgram wan_shell (Q:real^K->real^K^K) (wan_rext u) z) /
                    sqrt(p4_e2(cm_wgram wan_shell G (wan_rext u) z)))) =
    integral wan_shell
     (\z. lift(if p4_e2(transp(jacobian (wan_rext u) (at z)) ** G(wan_rext u z) **
                        jacobian (wan_rext u) (at z)) = &0
               then &0
               else p4_e2_pol (transp(jacobian (wan_rext u) (at z)) ** G(wan_rext u z) **
                               jacobian (wan_rext u) (at z))
                              (transp(jacobian (wan_rext u) (at z)) ** Q(wan_rext u z) **
                               jacobian (wan_rext u) (at z)) /
                    sqrt(p4_e2(transp(jacobian (wan_rext u) (at z)) ** G(wan_rext u z) **
                               jacobian (wan_rext u) (at z)))))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_SPIKE THEN
    EXISTS_TAC
     `{x | x IN wan_shell /\
           ~(wan_wd wan_shell 1 (wan_rext (u:real^3->real^K)) x =
             partial_derivative 1 (wan_rext u) x)} UNION
      {x | x IN wan_shell /\
           ~(wan_wd wan_shell 2 (wan_rext (u:real^3->real^K)) x =
             partial_derivative 2 (wan_rext u) x)} UNION
      {x | x IN wan_shell /\
           ~(wan_wd wan_shell 3 (wan_rext (u:real^3->real^K)) x =
             partial_derivative 3 (wan_rext u) x)}` THEN
    CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC NEGLIGIBLE_UNION THEN CONJ_TAC) THEN
      USE_THEN "NEG" MATCH_MP_TAC THEN ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_DIFF; IN_UNION; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[CMT_SHELL_NONZERO]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!i. 1 <= i /\ i <= 3
          ==> wan_wd wan_shell i (wan_rext (u:real^3->real^K)) x =
              jacobian (wan_rext u) (at x) ** basis i`
    ASSUME_TAC THENL
     [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `i = 1 \/ i = 2 \/ i = 3` MP_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[CMT_WGRAM_CLASSICAL];
    ALL_TAC] THEN
  USE_THEN "TT" (SUBST1_TAC o CONJUNCT2) THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> &2 / &3 * (&3 / &2 * a) = b`) THEN
  MATCH_MP_TAC P4_S2_INTEGRAL_EQ THEN SIMP_TAC[CM_REXT_SPHERE]);;

let CM_P4_BRIDGE = prove
 (`!top atlas (g:A->real^N^N) (f:A->real^K) (G:real^K->real^K^K) d
   (R:A->real^N^N) (Q:real^K->real^K^K) (v:real^3->A).
     cm_emb (top,atlas) g f G d /\
     smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) /\
     (!z. transp(Q z) = Q z) /\
     (!c w. c IN atlas /\ w IN IMAGE (SND c) (FST c)
            ==> metric_local atlas c R w =
                transp(matrix(frechet_derivative (f o chart_inv c) (at w))) **
                Q(f(chart_inv c w)) **
                matrix(frechet_derivative (f o chart_inv c) (at w))) /\
     p4_s2_c1 (top,atlas) v
     ==> p4_s2_energy atlas g v = cm_sen G (f o v) /\
         p4_s2_area atlas g v = cm_sarea G (f o v) /\
         p4_s2_trint atlas g R v = cm_strace G Q (f o v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o SPEC `v:real^3->A` o MATCH_MP
    (REWRITE_RULE[IMP_CONJ; RIGHT_FORALL_IMP_THM] CM_P4_TO_EMB)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ASSUME `cm_emb (top,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
                        (f:A->real^K) (G:real^K->real^K^K) d`) THEN
  REWRITE_TAC[cm_emb; cm_target; mfd_embedding] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!y. y IN sphere(vec 0,&1)
        ==> p4_s2_gram atlas (g:A->real^N^N) (v:real^3->A) y =
            transp(jacobian (wan_rext ((f:A->real^K) o v)) (at y)) **
            (G:real^K->real^K^K)(f(v y)) ** jacobian (wan_rext (f o v)) (at y) /\
            p4_s2_gram atlas (R:A->real^N^N) v y =
            transp(jacobian (wan_rext (f o v)) (at y)) **
            (Q:real^K->real^K^K)(f(v y)) ** jacobian (wan_rext (f o v)) (at y)`
  (LABEL_TAC "GG") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CM_S2_GRAM THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z u. lam * norm u pow 2 <= u dot ((G:real^K->real^K^K) z ** u)`
  ASSUME_TAC THENL [REPEAT GEN_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `Q:real^K->real^K^K`; `(f:A->real^K) o
      (v:real^3->A)`]
                CM_CLASSICAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `Q:real^K->real^K^K`; `(f:A->real^K) o
      (v:real^3->A)`;
                 `lam:real`] CMT_CLASSICAL_TRACE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[p4_s2_energy; p4_s2_area; p4_s2_trint] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC P4_S2_INTEGRAL_EQ THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[p4_s2_edensity; p4_s2_density; p4_s2_trdensity; o_THM]);;


(* ------------------------------------------------------------------------- *)
(* T6 preparation: the first variation of cm_sen along smooth families of   *)
(* radially invariant maps U(s,z) of (-a,a) x (real^3 minus 0).  The energy *)
(* is a shell integral of a density psi(jet U), with psi depending on the    *)
(* value and the space derivatives of U; differentiating under the integral  *)
(* sign gives a derivative at s = 0 that only depends on U(0,.) and on the  *)
(* time derivative of U at s = 0 (symmetry of second derivatives).          *)
(* ------------------------------------------------------------------------- *)

let CMT_SEN_SHELL = prove
 (`!(G:real^K->real^K^K) (u:real^3->real^K).
     continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext u) /\
     smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o G)
     ==> cm_sen G u =
         drop(integral wan_shell
               (\x. lift(trace(transp(jacobian (wan_rext u) (at x)) ** G(wan_rext u x) **
                               jacobian (wan_rext u) (at x))))) / &3`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "C1") (LABEL_TAC "GS")) THEN
  MP_TAC(ISPECL [`{z:real^3 | ~(z = vec 0)}`; `wan_rext (u:real^3->real^K)`]
                CMT_C1_FACTS) THEN
  ASM_REWRITE_TAC[CMT_OPEN_NONZERO; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "UC") (CONJUNCTS_THEN2 (LABEL_TAC "UD")
    (CONJUNCTS_THEN2 (LABEL_TAC "PD") (LABEL_TAC "PC" o REWRITE_RULE[ETA_AX])))) THEN
  SUBGOAL_THEN
   `((vectorize:real^K^K->real^(K,K)finite_prod) o (G:real^K->real^K^K))
    continuous_on (:real^K)` (LABEL_TAC "GC") THENL
   [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN EXISTS_TAC `0` THEN
    USE_THEN "GS" (MP_TAC o REWRITE_RULE[smooth_map_on]) THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `u:real^3->real^K` CMT_REXT_WD_AE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NEG")) THEN
  REWRITE_TAC[cm_sen] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
REWRITE_TAC[wan_gdir; DIMINDEX_3] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum(1..3) (\i. drop(integral wan_shell
                (\x. lift(partial_derivative i (wan_rext (u:real^3->real^K)) x dot
                          ((G:real^K->real^K^K)(wan_rext u x) **
                           partial_derivative i (wan_rext u) x)))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN
    STRIP_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC INTEGRAL_SPIKE THEN
    EXISTS_TAC `{x | x IN wan_shell /\
                     ~(wan_wd wan_shell i (wan_rext (u:real^3->real^K)) x =
                       partial_derivative i (wan_rext u) x)}` THEN
    CONJ_TAC THENL [USE_THEN "NEG" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral wan_shell
      (\x. lift(trace(transp(jacobian (wan_rext (u:real^3->real^K)) (at x)) **
                      (G:real^K->real^K^K)(wan_rext u x) **
                      jacobian (wan_rext u) (at x)))) =
    integral wan_shell
      (\x. vsum(1..3) (\i. lift(partial_derivative i (wan_rext u) x dot
                                (G(wan_rext u x) **
                                 partial_derivative i (wan_rext u) x))))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    REWRITE_TAC[CMT_TRACE_GRAM; DIMINDEX_3; LIFT_SUM; o_DEF] THEN
    SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[CMT_SHELL_NONZERO]; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\i x. lift(partial_derivative i (wan_rext (u:real^3->real^K)) x dot
                             ((G:real^K->real^K^K)(wan_rext u x) **
                              partial_derivative i (wan_rext u) x))`;
                 `wan_shell`; `1..3`] INTEGRAL_VSUM) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC CMT_CONT_ABSINT_SHELL THEN
    MATCH_MP_TAC CMT_CONT_QUAD THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[DROP_VSUM; o_DEF]);;

let CMT_BASIS_PASTECART = prove
 (`basis 1:real^(1,3)finite_sum = pastecart (lift(&1)) (vec 0) /\
   !i. 1 <= i /\ i <= 3
       ==> basis (i + 1):real^(1,3)finite_sum = pastecart (vec 0:real^1) (basis i:real^3)`,
  REWRITE_TAC[PASTECART_EQ; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  SIMP_TAC[CART_EQ; fstcart; sndcart; LAMBDA_BETA; DIMINDEX_1; DIMINDEX_3;
           DIMINDEX_FINITE_SUM; BASIS_COMPONENT; VEC_COMPONENT; LIFT_COMPONENT] THEN
  REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [SUBGOAL_THEN `i = 1` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_FINITE_SUM; DIMINDEX_1; DIMINDEX_3; ARITH;
             LIFT_COMPONENT];
    SUBGOAL_THEN `1 <= i + 1 /\ i + 1 <= dimindex(:(1,3)finite_sum)` MP_TAC THENL
     [REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1; DIMINDEX_3] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SIMP_TAC[BASIS_COMPONENT] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= i ==> ~(i + 1 = 1)`];
    SUBGOAL_THEN `i' = 1` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_FINITE_SUM; DIMINDEX_1; DIMINDEX_3; ARITH] THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= i ==> ~(1 = i + 1)`];
    SUBGOAL_THEN `1 <= i' + 1 /\ i' + 1 <= dimindex(:(1,3)finite_sum)` MP_TAC THENL
     [REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1; DIMINDEX_3] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SIMP_TAC[BASIS_COMPONENT; EQ_ADD_RCANCEL]]);;

let CMT_PD_SLICE = prove
 (`!(Fm:real^(1,3)finite_sum->real^N) s z i.
        1 <= i /\ i <= 3 /\ Fm differentiable at (pastecart (lift s) z)
        ==> partial_derivative i (\z. Fm(pastecart (lift s) z)) z =
            partial_derivative (i + 1) Fm (pastecart (lift s) z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z:real^3. (Fm:real^(1,3)finite_sum->real^N)(pastecart (lift s) z)) =
                Fm o (\z. pastecart (lift s) z)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\z:real^3. pastecart (lift s) z) has_derivative (\h. pastecart (vec 0:real^1) h))
    (at z)` ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN
    REWRITE_TAC[HAS_DERIVATIVE_CONST; HAS_DERIVATIVE_ID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`i:num`; `\z:real^3. pastecart (lift s) z`;
                 `Fm:real^(1,3)finite_sum->real^N`; `z:real^3`] PARTIAL_DERIVATIVE_CHAIN)
                     THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP PARTIAL_DERIVATIVE_HAS_DERIVATIVE_UNIQUE th])
      THEN
  ASM_SIMP_TAC[CMT_BASIS_PASTECART; partial_derivative]);;

let CMT_TIME_DERIV = prove
 (`!(Fm:real^(1,3)finite_sum->real^1) s z.
        Fm differentiable at (pastecart (lift s) z)
        ==> ((\s. drop(Fm(pastecart (lift s) z))) has_real_derivative
             drop(partial_derivative 1 Fm (pastecart (lift s) z))) (atreal s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT] THEN
  SUBGOAL_THEN `lift o (\s. drop((Fm:real^(1,3)finite_sum->real^1)(pastecart (lift s) z)))
      o drop =
                Fm o (\t. pastecart t z)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[FRECHET_DERIVATIVE_WORKS]) THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `((\t:real^1. pastecart t (z:real^3)) has_derivative (\h. pastecart h (vec 0)))
    (at (lift s))` ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN
    REWRITE_TAC[HAS_DERIVATIVE_CONST; HAS_DERIVATIVE_ID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t:real^1. pastecart t (z:real^3)`; `Fm:real^(1,3)finite_sum->real^1`;
                 `\h:real^1. pastecart h (vec 0:real^3)`;
                 `frechet_derivative (Fm:real^(1,3)finite_sum->real^1)
                                     (at (pastecart (lift s) z))`;
                 `lift s`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; partial_derivative; CMT_BASIS_PASTECART] THEN
  X_GEN_TAC `h:real^1` THEN
  SUBGOAL_THEN `pastecart h (vec 0:real^3) = drop h % pastecart (lift(&1)) (vec 0)`
  SUBST1_TAC THENL
   [REWRITE_TAC[PASTECART_EQ; FSTCART_PASTECART; SNDCART_PASTECART; FSTCART_CMUL;
                SNDCART_CMUL; VECTOR_MUL_RZERO; GSYM LIFT_CMUL; REAL_MUL_RID; LIFT_DROP];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Fm:real^(1,3)finite_sum->real^1`; `at (pastecart (lift s) (z:real^3))`]
                LINEAR_FRECHET_DERIVATIVE) THEN
  ASM_SIMP_TAC[LINEAR_CMUL] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL] THEN REAL_ARITH_TAC);;

let cmt_jet = new_definition
 `cmt_jet (U:real^(1,3)finite_sum->real^K) (x:real^(1,3)finite_sum) =
    pastecart (U x) (pastecart (partial_derivative 2 U x)
                       (pastecart (partial_derivative 3 U x) (partial_derivative 4 U x)))`;;

let cmt_psi = new_definition
 `cmt_psi (G:real^K->real^K^K) (y:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum) =
    fstcart(sndcart y) dot (G(fstcart y) ** fstcart(sndcart y)) +
    fstcart(sndcart(sndcart y)) dot (G(fstcart y) ** fstcart(sndcart(sndcart y))) +
    sndcart(sndcart(sndcart y)) dot (G(fstcart y) ** sndcart(sndcart(sndcart y)))`;;

let CMT_PSI_SMOOTH = prove
 (`!G:real^K->real^K^K.
        smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o G)
        ==> smooth_map_on (:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum)
                          (\y. lift(cmt_psi G y))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cmt_psi; LIFT_ADD] THEN
  SUBGOAL_THEN
   `!(a:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum->real^K).
       linear a
       ==> smooth_map_on (:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum)
             (\y. lift(a y dot ((G:real^K->real^K^K)(fstcart y) ** a y)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DOT_OPEN THEN
    ASM_SIMP_TAC[OPEN_UNIV; GRGE_SMOOTH_LINEAR] THEN
    MATCH_MP_TAC GRGE_SMOOTH_MATVEC THEN ASM_SIMP_TAC[OPEN_UNIV; GRGE_SMOOTH_LINEAR] THEN
    SUBGOAL_THEN
     `(vectorize:real^K^K->real^(K,K)finite_prod) o
      (\y:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum. (G:real^K->real^K^K)(fstcart
          y)) =
      (vectorize o G) o fstcart` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^K)` THEN
    ASM_SIMP_TAC[OPEN_UNIV; SUBSET_UNIV; GRGE_SMOOTH_LINEAR; LINEAR_FSTCART];
    ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN REWRITE_TAC[OPEN_UNIV] THEN CONJ_TAC) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[linear; FSTCART_ADD; SNDCART_ADD; FSTCART_CMUL; SNDCART_CMUL]);;

let CMT_JET_SMOOTH = prove
 (`!s (U:real^(1,3)finite_sum->real^K).
        open s /\ smooth_map_on s U ==> smooth_map_on s (cmt_jet U)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `cmt_jet (U:real^(1,3)finite_sum->real^K) =
    \x. pastecart (U x) (pastecart (partial_derivative 2 U x)
                         (pastecart (partial_derivative 3 U x) (partial_derivative 4 U x)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; cmt_jet]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN REWRITE_TAC[ETA_AX] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN REWRITE_TAC[ETA_AX] THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN REWRITE_TAC[ETA_AX] THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]);;

let CMT_TIME_OPEN = prove
 (`!a. open {x:real^(1,3)finite_sum | drop(fstcart x) IN real_interval(--a,a) /\
                                      ~(sndcart x = vec 0)}`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `{x:real^(1,3)finite_sum | drop(fstcart x) IN real_interval(--a,a) /\
                              ~(sndcart x = vec 0)} =
    interval(lift(--a),lift a) PCROSS {z:real^3 | ~(z = vec 0)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_ELIM_THM;
                FSTCART_PASTECART; SNDCART_PASTECART; IN_INTERVAL_1; IN_REAL_INTERVAL;
                LIFT_DROP];
    SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; CMT_OPEN_NONZERO]]);;

let CMT_FV_ENERGY = prove
 (`!(G:real^K->real^K^K) (U:real^(1,3)finite_sum->real^K) a s.
     smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o G) /\
     smooth_map_on {x | drop(fstcart x) IN real_interval(--a,a) /\ ~(sndcart x = vec 0)} U
         /\
     (!x t. drop(fstcart x) IN real_interval(--a,a) /\ ~(sndcart x = vec 0) /\ &0 < t
            ==> U(pastecart (fstcart x) (t % sndcart x)) = U x) /\
     s IN real_interval(--a,a)
     ==> cm_sen G (\y. U(pastecart (lift s) y)) =
         drop(integral wan_shell
                (\z. lift(cmt_psi G (cmt_jet U (pastecart (lift s) z))))) / &3`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "GS") (CONJUNCTS_THEN2 (LABEL_TAC "US")
    (CONJUNCTS_THEN2 (LABEL_TAC "RAD") (LABEL_TAC "SIN")))) THEN
  ABBREV_TAC `D = {x:real^(1,3)finite_sum | drop(fstcart x) IN real_interval(--a,a) /\
                                            ~(sndcart x = vec 0)}` THEN
  SUBGOAL_THEN `open(D:real^(1,3)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[CMT_TIME_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. ~(z = vec 0) ==> pastecart (lift s) z IN D` (LABEL_TAC "PD0")
      THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART;
                                    LIFT_DROP] THEN
    USE_THEN "SIN" (fun th -> SIMP_TAC[th]);
    ALL_TAC] THEN
  ABBREV_TAC `u = \y:real^3. (U:real^(1,3)finite_sum->real^K)(pastecart (lift s) y)` THEN
  SUBGOAL_THEN `!z:real^3. ~(z = vec 0) ==> wan_rext (u:real^3->real^K) z = u z`
  (LABEL_TAC "RX") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "u" THEN REWRITE_TAC[wan_rext] THEN
    USE_THEN "RAD" (MP_TAC o SPECL [`pastecart (lift s) (z:real^3)`;
        `inv(norm(z:real^3))`]) THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_INV_EQ; NORM_POS_LT] THEN USE_THEN "SIN" ACCEPT_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on {z:real^3 | ~(z = vec 0)} (u:real^3->real^K)` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN
    SUBGOAL_THEN `(\y:real^3. (U:real^(1,3)finite_sum->real^K)(pastecart (lift s) y)) =
                  U o (\y. pastecart (lift s) y)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `D:real^(1,3)finite_sum->bool`
        THEN
    ASM_REWRITE_TAC[CMT_OPEN_NONZERO] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN USE_THEN "PD0" ACCEPT_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
      REWRITE_TAC[CMT_OPEN_NONZERO; SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_ID]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext (u:real^3->real^K))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_EQ_OPEN THEN EXISTS_TAC `u:real^3->real^K` THEN
    REWRITE_TAC[CMT_OPEN_NONZERO; IN_ELIM_THM] THEN CONJ_TAC THENL
     [USE_THEN "RX" (fun th -> SIMP_TAC[th]);
      ASM_MESON_TAC[smooth_map_on]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{z:real^3 | ~(z = vec 0)}`; `wan_rext (u:real^3->real^K)`]
                CMT_C1_FACTS) THEN
  ASM_REWRITE_TAC[CMT_OPEN_NONZERO; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "PDJ") (K ALL_TAC)))) THEN
  SUBGOAL_THEN
   `!i z. 1 <= i /\ i <= 3 /\ ~(z = vec 0)
          ==> jacobian (wan_rext (u:real^3->real^K)) (at z) ** basis i =
              partial_derivative (i + 1) (U:real^(1,3)finite_sum->real^K)
                                 (pastecart (lift s) z)`
  (LABEL_TAC "JB") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "PDJ" (MP_TAC o C MATCH_MP (ASSUME `~(z:real^3 = vec 0)`) o
                    SPECL [`i:num`; `z:real^3`]) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    TRANS_TAC EQ_TRANS `partial_derivative i (u:real^3->real^K) z` THEN CONJ_TAC THENL
     [MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN
      EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
      ASM_REWRITE_TAC[CMT_OPEN_NONZERO; IN_ELIM_THM] THEN USE_THEN "RX" ACCEPT_TAC;
      EXPAND_TAC "u" THEN MATCH_MP_TAC CMT_PD_SLICE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `D:real^(1,3)finite_sum->bool` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`] CMT_SEN_SHELL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(z:real^3 = vec 0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CMT_SHELL_NONZERO]; ALL_TAC] THEN
  REWRITE_TAC[] THEN AP_TERM_TAC THEN
  REWRITE_TAC[CMT_TRACE_GRAM; DIMINDEX_3; SUM_3; cmt_psi; cmt_jet; FSTCART_PASTECART;
              SNDCART_PASTECART] THEN
  USE_THEN "JB" (fun th -> ASM_SIMP_TAC[th; ARITH]) THEN
  USE_THEN "RX" (fun th -> ASM_SIMP_TAC[th]) THEN EXPAND_TAC "u" THEN
  REWRITE_TAC[ARITH]);;

let CMT_FIRST_VARIATION = prove
 (`!(G:real^K->real^K^K) (U:real^(1,3)finite_sum->real^K) a.
     &0 < a /\
     smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o G) /\
     smooth_map_on {x | drop(fstcart x) IN real_interval(--a,a) /\ ~(sndcart x = vec 0)} U
         /\
     (!x t. drop(fstcart x) IN real_interval(--a,a) /\ ~(sndcart x = vec 0) /\ &0 < t
            ==> U(pastecart (fstcart x) (t % sndcart x)) = U x)
     ==> ((\s. cm_sen G (\y. U(pastecart (lift s) y))) has_real_derivative
          drop(integral wan_shell
                (\z. partial_derivative 1 (\x. lift(cmt_psi G (cmt_jet U x)))
                                        (pastecart (lift(&0)) z))) / &3)
         (atreal (&0))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "GS")
    (CONJUNCTS_THEN2 (LABEL_TAC "US") (LABEL_TAC "RAD")))) THEN
  SUBGOAL_THEN
   `!s. s IN real_interval(--a,a)
        ==> cm_sen (G:real^K->real^K^K)
                   (\y. (U:real^(1,3)finite_sum->real^K)(pastecart (lift s) y)) =
            drop(integral wan_shell
                   (\z. lift(cmt_psi G (cmt_jet U (pastecart (lift s) z))))) / &3`
  (LABEL_TAC "EN") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMT_FV_ENERGY THEN EXISTS_TAC `a:real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `D = {x:real^(1,3)finite_sum | drop(fstcart x) IN real_interval(--a,a) /\
                                            ~(sndcart x = vec 0)}` THEN
  SUBGOAL_THEN `open(D:real^(1,3)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[CMT_TIME_OPEN]; ALL_TAC] THEN
  ABBREV_TAC `Phi = \x:real^(1,3)finite_sum.
                       lift(cmt_psi (G:real^K->real^K^K)
                                    (cmt_jet (U:real^(1,3)finite_sum->real^K) x))` THEN
  SUBGOAL_THEN `smooth_map_on D (Phi:real^(1,3)finite_sum->real^1)` ASSUME_TAC THENL
   [EXPAND_TAC "Phi" THEN
    SUBGOAL_THEN
     `(\x:real^(1,3)finite_sum. lift(cmt_psi (G:real^K->real^K^K)
                                    (cmt_jet (U:real^(1,3)finite_sum->real^K) x))) =
      (\y. lift(cmt_psi G y)) o cmt_jet U` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `(:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum)` THEN
    ASM_SIMP_TAC[OPEN_UNIV; SUBSET_UNIV; CMT_PSI_SMOOTH; CMT_JET_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on D (partial_derivative 1 (Phi:real^(1,3)finite_sum->real^1))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]; ALL_TAC] THEN
  SUBGOAL_THEN `!s z. s IN real_interval(--a,a) /\ ~(z = vec 0)
                      ==> pastecart (lift s) (z:real^3) IN D` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART;
                                    LIFT_DROP] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?B. !s z. s IN real_interval[--(a / &2),a / &2] /\ z IN wan_shell
              ==> abs(drop(partial_derivative 1 (Phi:real^(1,3)finite_sum->real^1)
                                              (pastecart (lift s) z))) <= B`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`partial_derivative 1 (Phi:real^(1,3)finite_sum->real^1)`;
                   `interval[lift(--(a / &2)),lift(a / &2)] PCROSS
                    (cball(vec 0:real^3,&2) DIFF ball(vec 0,&1 / &2))`]
                  COMPACT_CONTINUOUS_IMAGE) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `D:real^(1,3)finite_sum->bool`
           THEN
        ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
        EXPAND_TAC "D" THEN
        REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_ELIM_THM;
                    FSTCART_PASTECART; SNDCART_PASTECART; IN_INTERVAL_1; IN_REAL_INTERVAL;
                    LIFT_DROP; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN
        MAP_EVERY X_GEN_TAC [`t:real^1`; `w:real^3`] THEN STRIP_TAC THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC;
          DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~(norm(vec 0:real^3) < &1 / &2)` THEN
          REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC];
        MATCH_MP_TAC COMPACT_PCROSS THEN REWRITE_TAC[COMPACT_INTERVAL] THEN
        SIMP_TAC[COMPACT_DIFF; COMPACT_CBALL; OPEN_BALL]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN EXISTS_TAC `B:real` THEN
    MAP_EVERY X_GEN_TAC [`s:real`; `z:real^3`] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(partial_derivative 1 (Phi:real^(1,3)finite_sum->real^1)
                                       (pastecart (lift s) z))` THEN
    CONJ_TAC THENL [REWRITE_TAC[NORM_REAL; GSYM drop; REAL_LE_REFL]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN
    UNDISCH_TAC `(z:real^3) IN wan_shell` THEN
    UNDISCH_TAC `s IN real_interval[--(a / &2),a / &2]` THEN
    REWRITE_TAC[wan_shell; IN_ELIM_THM; IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\s z. drop((Phi:real^(1,3)finite_sum->real^1) (pastecart (lift s) z))`;
    `\s z. drop(partial_derivative 1 (Phi:real^(1,3)finite_sum->real^1)
                                   (pastecart (lift s) z))`;
    `\z:real^3. B:real`; `real_interval(--(a / &2),a / &2)`; `wan_shell`]
   GRGT_HAS_REAL_DERIVATIVE_INTEGRAL_DOMINATED) THEN
  REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[IS_REALINTERVAL_INTERVAL];
      X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN DISCH_TAC THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC CMT_CONT_ABSINT_SHELL THEN
      SUBGOAL_THEN `(\z:real^3. (Phi:real^(1,3)finite_sum->real^1) (pastecart (lift s) z)) =
                    Phi o (\z. pastecart (lift s) z)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
        REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `D:real^(1,3)finite_sum->bool`
            THEN
        ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[INTEGRABLE_ON_CONST] THEN DISJ2_TAC THEN MATCH_MP_TAC MEASURABLE_OPEN THEN
      REWRITE_TAC[wan_shell; CMT_ANNULUS_OPEN_BOUNDED];
      MAP_EVERY X_GEN_TAC [`s:real`; `z:real^3`] THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MATCH_MP_TAC CMT_TIME_DERIV THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `D:real^(1,3)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      CONJ_TAC THENL [UNDISCH_TAC `s IN real_interval(--(a / &2),a / &2)` THEN
                      REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
                      ASM_SIMP_TAC[CMT_SHELL_NONZERO]];
      MAP_EVERY X_GEN_TAC [`s:real`; `z:real^3`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `s IN real_interval(--(a / &2),a / &2)` THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `&0`) THEN ANTS_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `a / &4` THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  MP_TAC(ISPECL [`\x. drop(integral wan_shell
                            (\v. (Phi:real^(1,3)finite_sum->real^1) (pastecart (lift x)
                                v)))`;
                 `drop(integral wan_shell
                         (\v. partial_derivative 1 (Phi:real^(1,3)finite_sum->real^1)
                                                 (pastecart (lift(&0)) v)))`;
                 `&0`; `real_interval(--(a / &2),a / &2)`]
                HAS_REAL_DERIVATIVE_WITHIN_REAL_OPEN) THEN
  REWRITE_TAC[REAL_OPEN_REAL_INTERVAL; IN_REAL_INTERVAL] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `inv(&3)` o MATCH_MP HAS_REAL_DERIVATIVE_LMUL_ATREAL) THEN
  REWRITE_TAC[REAL_ARITH `inv(&3) * x = x / &3`] THEN
  MATCH_MP_TAC(MESON[HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL]
   `!f f' g x d. &0 < d /\ (!x'. abs(x' - x) < d ==> f x' = g x')
                 ==> (f has_real_derivative f') (atreal x)
                 ==> (g has_real_derivative f') (atreal x)`) THEN
  EXISTS_TAC `a / &2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `s IN real_interval(--a,a)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "EN" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `s IN real_interval(--a,a)`)])
      THEN
  EXPAND_TAC "Phi" THEN REWRITE_TAC[]);;

let CMT_JET_AT0 = prove
 (`!(W:real^(1,3)finite_sum->real^K) D z.
     open D /\ smooth_map_on D W /\ pastecart (lift(&0)) z IN D
     ==> cmt_jet W (pastecart (lift(&0)) z) =
         pastecart (W(pastecart (lift(&0)) z))
          (pastecart (partial_derivative 1 (\y. W(pastecart (lift(&0)) y)) z)
           (pastecart (partial_derivative 2 (\y. W(pastecart (lift(&0)) y)) z)
                      (partial_derivative 3 (\y. W(pastecart (lift(&0)) y)) z))) /\
         partial_derivative 1 (cmt_jet W) (pastecart (lift(&0)) z) =
         pastecart (partial_derivative 1 W (pastecart (lift(&0)) z))
          (pastecart
            (partial_derivative 1 (\y. partial_derivative 1 W (pastecart (lift(&0)) y)) z)
            (pastecart
              (partial_derivative 2 (\y. partial_derivative 1 W (pastecart (lift(&0)) y)) z)
              (partial_derivative 3 (\y. partial_derivative 1 W (pastecart (lift(&0)) y))
                  z)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!j. smooth_map_on D (partial_derivative j (W:real^(1,3)finite_sum->real^K))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(W:real^(1,3)finite_sum->real^K) differentiable at (pastecart (lift(&0)) z) /\
    !j. partial_derivative j W differentiable at (pastecart (lift(&0)) z)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; GEN_TAC] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `D:real^(1,3)finite_sum->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[cmt_jet] THEN ASM_SIMP_TAC[CMT_PD_SLICE; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN
   `cmt_jet (W:real^(1,3)finite_sum->real^K) =
    \x. pastecart (W x) (pastecart (partial_derivative 2 W x)
                         (pastecart (partial_derivative 3 W x) (partial_derivative 4 W x)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; cmt_jet]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\x. pastecart ((W:real^(1,3)finite_sum->real^K) x)
                    (pastecart (partial_derivative 2 W x)
                       (pastecart (partial_derivative 3 W x) (partial_derivative 4 W x))))
     has_derivative
     (\h. pastecart (frechet_derivative W (at (pastecart (lift(&0)) z)) h)
            (pastecart (frechet_derivative (partial_derivative 2 W)
                                           (at (pastecart (lift(&0)) z)) h)
               (pastecart (frechet_derivative (partial_derivative 3 W)
                                              (at (pastecart (lift(&0)) z)) h)
                          (frechet_derivative (partial_derivative 4 W)
                                              (at (pastecart (lift(&0)) z)) h)))))
    (at (pastecart (lift(&0)) z))`
  ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN CONJ_TAC) THEN
    REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SPEC `1` o MATCH_MP PARTIAL_DERIVATIVE_HAS_DERIVATIVE_UNIQUE)
      THEN
  REWRITE_TAC[GSYM partial_derivative] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 3
        ==> partial_derivative 1 (partial_derivative (i + 1)
            (W:real^(1,3)finite_sum->real^K))
                               (pastecart (lift(&0)) z) =
            partial_derivative i (\y. partial_derivative 1 W (pastecart (lift(&0)) y)) z`
  (fun th -> SIMP_TAC[REWRITE_RULE[ARITH] (MATCH_MP th (ARITH_RULE `1 <= 1 /\ 1 <= 3`));
                      REWRITE_RULE[ARITH] (MATCH_MP th (ARITH_RULE `1 <= 2 /\ 2 <= 3`));
                      REWRITE_RULE[ARITH] (MATCH_MP th (ARITH_RULE `1 <= 3 /\ 3 <= 3`))])
                          THEN
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
   `partial_derivative (i + 1) (partial_derivative 1 (W:real^(1,3)finite_sum->real^K))
                       (pastecart (lift(&0)) z)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PARTIAL_DERIVATIVE_SYM THEN EXISTS_TAC `D:real^(1,3)finite_sum->bool` THEN
    ASM_REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1; DIMINDEX_3] THEN
    UNDISCH_TAC `smooth_map_on D (W:real^(1,3)finite_sum->real^K)` THEN
    SIMP_TAC[smooth_map_on] THEN DISCH_TAC THEN ASM_ARITH_TAC;
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC CMT_PD_SLICE THEN ASM_REWRITE_TAC[]]);;

let CMT_FV_VALUE_EQ = prove
 (`!(G:real^K->real^K^K) (U:real^(1,3)finite_sum->real^K) U' D D' z.
     smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o G) /\
     open D /\ smooth_map_on D U /\ open D' /\ smooth_map_on D' U' /\
     (!y. ~(y = vec 0) ==> pastecart (lift(&0)) y IN D /\ pastecart (lift(&0)) y IN D') /\
     (!y. ~(y = vec 0) ==> U(pastecart (lift(&0)) y) = U'(pastecart (lift(&0)) y)) /\
     (!y. ~(y = vec 0) ==> partial_derivative 1 U (pastecart (lift(&0)) y) =
                           partial_derivative 1 U' (pastecart (lift(&0)) y)) /\
     ~(z = vec 0)
     ==> partial_derivative 1 (\x. lift(cmt_psi G (cmt_jet U x))) (pastecart (lift(&0)) z) =
         partial_derivative 1 (\x. lift(cmt_psi G (cmt_jet U' x))) (pastecart (lift(&0))
             z)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "GS") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "IND") (CONJUNCTS_THEN2 (LABEL_TAC "E0")
    (CONJUNCTS_THEN2 (LABEL_TAC "E1") ASSUME_TAC)))))))) THEN
  SUBGOAL_THEN
   `!(W:real^(1,3)finite_sum->real^K) S.
       open S /\ smooth_map_on S W /\ pastecart (lift(&0)) z IN S
       ==> partial_derivative 1 (\x. lift(cmt_psi G (cmt_jet W x))) (pastecart (lift(&0))
           z) =
           frechet_derivative (\y. lift(cmt_psi G y)) (at (cmt_jet W (pastecart (lift(&0))
               z)))
             (partial_derivative 1 (cmt_jet W) (pastecart (lift(&0)) z))`
  (LABEL_TAC "CH") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(\x. lift(cmt_psi (G:real^K->real^K^K)
                                    (cmt_jet (W:real^(1,3)finite_sum->real^K) x))) =
                  (\y. lift(cmt_psi G y)) o cmt_jet W` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC PARTIAL_DERIVATIVE_CHAIN THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `S:real^(1,3)finite_sum->bool` THEN ASM_SIMP_TAC[CMT_JET_SMOOTH];
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `(:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum)` THEN
      ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; CMT_PSI_SMOOTH]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pastecart (lift(&0)) (z:real^3) IN D /\ pastecart (lift(&0)) z IN D'`
  STRIP_ASSUME_TAC THENL [USE_THEN "IND" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "CH" (fun th ->
    REWRITE_TAC[MATCH_MP th (CONJ (ASSUME `open(D:real^(1,3)finite_sum->bool)`)
      (CONJ (ASSUME `smooth_map_on D (U:real^(1,3)finite_sum->real^K)`)
            (ASSUME `pastecart (lift(&0)) (z:real^3) IN D`)));
                MATCH_MP th (CONJ (ASSUME `open(D':real^(1,3)finite_sum->bool)`)
      (CONJ (ASSUME `smooth_map_on D' (U':real^(1,3)finite_sum->real^K)`)
            (ASSUME `pastecart (lift(&0)) (z:real^3) IN D'`)))]) THEN
  MP_TAC(ISPECL [`U:real^(1,3)finite_sum->real^K`; `D:real^(1,3)finite_sum->bool`;
                 `z:real^3`] CMT_JET_AT0) THEN
  MP_TAC(ISPECL [`U':real^(1,3)finite_sum->real^K`; `D':real^(1,3)finite_sum->bool`;
                 `z:real^3`] CMT_JET_AT0) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC) THEN
  SUBGOAL_THEN
   `!i. partial_derivative i (\y. (U:real^(1,3)finite_sum->real^K)(pastecart (lift(&0)) y))
       z =
        partial_derivative i (\y. (U':real^(1,3)finite_sum->real^K)(pastecart (lift(&0))
            y)) z /\
        partial_derivative i (\y. partial_derivative 1 U (pastecart (lift(&0)) y)) z =
        partial_derivative i (\y. partial_derivative 1 U' (pastecart (lift(&0)) y)) z`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN
    EXISTS_TAC `{y:real^3 | ~(y = vec 0)}` THEN
    ASM_REWRITE_TAC[CMT_OPEN_NONZERO; IN_ELIM_THM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* T6: harmonic spheres in the two pictures.  Smoothness transfers by T8,  *)
(* values and nonconstancy by injectivity of f; criticality one way by the  *)
(* variations emb_inv(closest_point(f o v + eps s phi)), the other way by   *)
(* the first variation formula (both families have the same time-zero data, *)
(* since the variation field of a family in f(M) is tangent).               *)
(* ------------------------------------------------------------------------- *)

let CMT_P4_SMOOTH_SPHERE_EQ = prove
 (`!top atlas (u:real^3->A) u'.
        (!y. y IN sphere(vec 0,&1) ==> u y = u' y)
        ==> (p4_s2_smooth (top,atlas:((A->bool)#(A->real^N))->bool) u <=>
             p4_s2_smooth (top,atlas) u')`,
  SUBGOAL_THEN
   `!top atlas (u:real^3->A) u'.
        (!y. y IN sphere(vec 0,&1) ==> u y = u' y) /\
        p4_s2_smooth (top,atlas:((A->bool)#(A->real^N))->bool) u
        ==> p4_s2_smooth (top,atlas) u'`
  (fun th -> MESON_TAC[th]) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[p4_s2_smooth] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "EQ") (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SM")))
    THEN
  SUBGOAL_THEN
   `!z:real^3. ~(z = vec 0) ==> (u:real^3->A)(inv(norm z) % z) = u'(inv(norm z) % z)`
  (LABEL_TAC "EQZ") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "EQ" MATCH_MP_TAC THEN
    ASM_SIMP_TAC[P4_RADIAL_SPHERE];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN EXISTS_TAC `u:real^3->A` THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
    ALL_TAC] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `{z:real^3 | ~(z = vec 0) /\ (u':real^3->A)(inv(norm z) % z) IN
       FST(c:(A->bool)#(A->real^N))} =
    {z:real^3 | ~(z = vec 0) /\ (u:real^3->A)(inv(norm z) % z) IN FST c}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
    ASM_CASES_TAC `x:real^3 = vec 0` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `\z. SND (c:(A->bool)#(A->real^N)) ((u:real^3->A)(inv(norm z) % z))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    USE_THEN "SM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let CMT_NONCONST_EQ = prove
 (`!top atlas (f:A->real^K) (v:real^3->A).
        mfd_embedding (top,atlas:((A->bool)#(A->real^N))->bool) f /\
        (!y. y IN sphere(vec 0,&1) ==> v y IN topspace top)
        ==> ((?c. !y. y IN sphere(vec 0,&1) ==> (f o v) y = c) <=>
             (?x. !y. y IN sphere(vec 0,&1) ==> v y = x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_TAC `c:real^K`) THEN
    EXISTS_TAC `mfd_emb_inv top (f:A->real^K) c` THEN X_GEN_TAC `y:real^3` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `c = (f:A->real^K)((v:real^3->A) y)` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC GRGE_EMB_INV_LEFT THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_SIMP_TAC[];
    DISCH_THEN(X_CHOOSE_TAC `x:A`) THEN EXISTS_TAC `(f:A->real^K) x` THEN ASM_SIMP_TAC[]]);;

let CMT_SNDCART_OPEN = prove
 (`!s. open s ==> open {x:real^(1,3)finite_sum | sndcart x IN s}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`sndcart:real^(1,3)finite_sum->real^3`; `(:real^(1,3)finite_sum)`;
                 `s:real^3->bool`] CONTINUOUS_OPEN_PREIMAGE) THEN
  ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; LINEAR_CONTINUOUS_ON; LINEAR_SNDCART]);;

let CMT_LFAMILY_SMOOTH = prove
 (`!(w:real^3->real^K) (phi:real^3->real^K) e.
        smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext w) /\
        smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext phi)
        ==> smooth_map_on {x:real^(1,3)finite_sum | ~(sndcart x = vec 0)}
              (\x. wan_rext w (sndcart x) +
                   (e * drop(fstcart x)) % wan_rext phi (sndcart x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open {x:real^(1,3)finite_sum | ~(sndcart x = vec 0)}` ASSUME_TAC THENL
   [MP_TAC(ISPEC `{z:real^3 | ~(z = vec 0)}` CMT_SNDCART_OPEN) THEN
    REWRITE_TAC[CMT_OPEN_NONZERO; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!h:real^3->real^K.
      smooth_map_on {z:real^3 | ~(z = vec 0)} h
      ==> smooth_map_on {x:real^(1,3)finite_sum | ~(sndcart x = vec 0)} (\x. h(sndcart x))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(\x:real^(1,3)finite_sum. (h:real^3->real^K)(sndcart x)) = h o sndcart`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
    ASM_SIMP_TAC[CMT_OPEN_NONZERO; GRGE_SMOOTH_LINEAR; LINEAR_SNDCART] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC GRGE_SMOOTH_SCALAR_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC GRGE_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[linear; FSTCART_ADD; FSTCART_CMUL; DROP_ADD; DROP_CMUL] THEN
    CONJ_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[GSYM LIFT_ADD; GSYM LIFT_CMUL; LIFT_EQ]
        THEN
    REAL_ARITH_TAC;
    FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]]);;

let CMT_TUBE_FAMILY_CONT = prove
 (`!top atlas (f:A->real^K) (w:real^3->real^K) (phi:real^3->real^K) e r.
     mfd_embedding (top,atlas:((A->bool)#(A->real^N))->bool) f /\
     (closest_point (IMAGE f (topspace top))) continuous_on
        {z | ?p. p IN IMAGE f (topspace top) /\ dist(z,p) < r} /\
     (!z. (?p. p IN IMAGE f (topspace top) /\ dist(z,p) < r)
          ==> closest_point (IMAGE f (topspace top)) z IN IMAGE f (topspace top)) /\
     w continuous_on sphere(vec 0,&1) /\ phi continuous_on sphere(vec 0,&1) /\
     (!s y. s IN real_interval(--(&1),&1) /\ y IN sphere(vec 0,&1)
            ==> ?p. p IN IMAGE f (topspace top) /\ dist(w y + (e * s) % phi y,p) < r)
     ==> continuous_map
           (prod_topology (subtopology euclideanreal (real_interval(--(&1),&1)))
                          (subtopology euclidean (sphere(vec 0:real^3,&1))),top)
           (\(s,y). mfd_emb_inv top f
                      (closest_point (IMAGE f (topspace top)) (w y + (e * s) % phi y)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\(s,y). mfd_emb_inv top (f:A->real^K)
               (closest_point (IMAGE f (topspace top))
                  ((w:real^3->real^K) y + (e * s) % (phi:real^3->real^K) y))) =
    (mfd_emb_inv top f o closest_point (IMAGE f (topspace top))) o
    (\x:real#real^3. w (SND x) + (e * FST x) % phi (SND x))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology euclidean
                {z:real^K | ?p. p IN IMAGE (f:A->real^K) (topspace top) /\ dist(z,p) < r}`
                    THEN
  CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `!h:real^3->real^K.
          h continuous_on sphere(vec 0,&1)
          ==> continuous_map
                (prod_topology (subtopology euclideanreal (real_interval(--(&1),&1)))
                               (subtopology euclidean (sphere(vec 0:real^3,&1))),euclidean)
                (\x:real#real^3. h(SND x))`
      ASSUME_TAC THENL
       [REPEAT STRIP_TAC THEN
        SUBGOAL_THEN `(\x:real#real^3. (h:real^3->real^K)(SND x)) = h o SND` SUBST1_TAC
            THENL
         [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
        EXISTS_TAC `subtopology euclidean (sphere(vec 0:real^3,&1))` THEN
        ASM_REWRITE_TAC[CONTINUOUS_MAP_SND; CONTINUOUS_MAP_EUCLIDEAN];
        ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_VECTOR_ADD THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_VECTOR_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_MAP_REAL_LMUL THEN
        MP_TAC(ISPECL [`subtopology euclideanreal (real_interval(--(&1),&1))`;
                       `subtopology euclidean (sphere(vec 0:real^3,&1))`]
                      CONTINUOUS_MAP_FST) THEN
        SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PAIR_THM; TOPSPACE_PROD_TOPOLOGY;
                  TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
                  IN_CROSS; IN_ELIM_THM] THEN
      ASM_SIMP_TAC[]];
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean (IMAGE (f:A->real^K) (topspace top))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC CMT_EMB_INV_CONTINUOUS THEN
      EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[]]]);;

let CMT_PROJ_VARIATION = prove
 (`!top atlas (g:A->real^N^N) (f:A->real^K) (G:real^K->real^K^K) d
    (v:real^3->A) (phi:real^3->real^K).
     cm_emb (top,atlas) g f G d /\
     (!y. y IN sphere(vec 0,&1) ==> v y IN topspace top) /\
     smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext (f o v)) /\
     smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext phi)
     ==> ?e. &0 < e /\
             ?V. p4_s2_variation (top,atlas) v V /\
                 !s. s IN real_interval(--(&1),&1)
                     ==> p4_s2_energy atlas g (V s) =
                         cm_sen G (\y. closest_point (IMAGE f (topspace top))
                                                     ((f o v) y + (e * s) % phi y))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "EMB") (CONJUNCTS_THEN2 (LABEL_TAC "VM")
    (CONJUNCTS_THEN2 (LABEL_TAC "WS") (LABEL_TAC "PS")))) THEN
  USE_THEN "EMB" (MP_TAC o REWRITE_RULE[cm_emb; cm_target; cm_tube; IN_ELIM_THM]) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!z. (?p. p IN IMAGE (f:A->real^K) (topspace top) /\ dist(z,p) < d)
        ==> closest_point (IMAGE f (topspace top)) z IN IMAGE f (topspace top)`
  (LABEL_TAC "CPT") THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `f:A->real^K`]
                CMT_RETRACT_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "RS"))) THEN
  SUBGOAL_THEN
   `((f:A->real^K) o (v:real^3->A)) continuous_on sphere(vec 0:real^3,&1) /\
    (phi:real^3->real^K) continuous_on sphere(vec 0,&1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THENL
     [EXISTS_TAC `wan_rext ((f:A->real^K) o (v:real^3->A))`;
      EXISTS_TAC `wan_rext (phi:real^3->real^K)`] THEN
    SIMP_TAC[CM_REXT_SPHERE] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_SPHERE_0] THEN X_GEN_TAC `x:real^3` THEN
    ASM_CASES_TAC `x:real^3 = vec 0` THEN ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?B. &0 < B /\ !y. y IN sphere(vec 0,&1) ==> norm((phi:real^3->real^K) y) <= B`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`phi:real^3->real^K`; `sphere(vec 0:real^3,&1)`]
                  COMPACT_CONTINUOUS_IMAGE) THEN
    ASM_REWRITE_TAC[COMPACT_SPHERE] THEN DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED)
        THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE];
    ALL_TAC] THEN
  ABBREV_TAC `e = min d d1 / (&2 * B)` THEN
  SUBGOAL_THEN `&0 < e /\ e * B < min d d1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `min d d1 / (&2 * B) * B = min d d1 / &2` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < B` THEN CONV_TAC REAL_FIELD; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s y. s IN real_interval(--(&1),&1) /\ y IN sphere(vec 0,&1)
          ==> ((f:A->real^K) o (v:real^3->A)) y IN IMAGE f (topspace top) /\
              dist((f o v) y + (e * s) % (phi:real^3->real^K) y,(f o v) y) < min d d1`
  (LABEL_TAC "TUB") THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[o_THM; FUN_IN_IMAGE] THEN
    REWRITE_TAC[NORM_ARITH `dist(a + b:real^N,a) = norm b`; NORM_MUL] THEN
    SUBGOAL_THEN `abs(e * s) <= e` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_ABS_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> abs e = e`] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `e * B` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_ABS_POS; NORM_POS_LE];
    ALL_TAC] THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `\s y. mfd_emb_inv top (f:A->real^K)
                      (closest_point (IMAGE f (topspace top))
                         (((f:A->real^K) o (v:real^3->A)) y + (e * s) %
                             (phi:real^3->real^K) y))` THEN
  REWRITE_TAC[p4_s2_variation] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_MUL_RZERO; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    SUBGOAL_THEN `closest_point (IMAGE (f:A->real^K) (topspace top)) ((f o (v:real^3->A))
        y) =
                  (f o v) y` SUBST1_TAC THENL
     [MATCH_MP_TAC CLOSEST_POINT_SELF THEN ASM_SIMP_TAC[o_THM; FUN_IN_IMAGE]; ALL_TAC] THEN
    REWRITE_TAC[o_THM] THEN MATCH_MP_TAC GRGE_EMB_INV_LEFT THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC CMT_TUBE_FAMILY_CONT THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `d:real`] THEN
    REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
    REPEAT STRIP_TAC THEN EXISTS_TAC `((f:A->real^K) o (v:real^3->A)) y` THEN
    USE_THEN "TUB" (MP_TAC o SPECL [`s:real`; `y:real^3`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[];
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC];
    X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    USE_THEN "RS" (MP_TAC o C MATCH_MP (ASSUME `(c:(A->bool)#(A->real^N)) IN atlas`)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "TCO") (LABEL_TAC "TCS")) THEN
    MP_TAC(ISPECL [`(f:A->real^K) o (v:real^3->A)`; `phi:real^3->real^K`; `e:real`]
                  CMT_LFAMILY_SMOOTH) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ABBREV_TAC
     `L = \x:real^(1,3)finite_sum.
            wan_rext ((f:A->real^K) o (v:real^3->A)) (sndcart x) +
            (e * drop(fstcart x)) % wan_rext (phi:real^3->real^K) (sndcart x)` THEN
    SUBGOAL_THEN
     `!x:real^(1,3)finite_sum.
        ((f:A->real^K) o (v:real^3->A)) (inv(norm(sndcart x)) % sndcart x) +
        (e * drop(fstcart x)) % (phi:real^3->real^K) (inv(norm(sndcart x)) % sndcart x) =
        L x`
    (fun th -> REWRITE_TAC[th]) THENL
     [EXPAND_TAC "L" THEN REWRITE_TAC[wan_rext]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!x:real^(1,3)finite_sum.
        drop(fstcart x) IN real_interval(--(&1),&1) /\ ~(sndcart x = vec 0)
        ==> ?p. p IN IMAGE (f:A->real^K) (topspace top) /\ dist(L x,p) < d1`
    (LABEL_TAC "LT") THENL
     [REPEAT STRIP_TAC THEN EXISTS_TAC `((f:A->real^K) o (v:real^3->A))
                                         (inv(norm(sndcart (x:real^(1,3)finite_sum))) %
                                          sndcart x)` THEN
      USE_THEN "TUB" (MP_TAC o SPECL [`drop(fstcart (x:real^(1,3)finite_sum))`;
                                      `inv(norm(sndcart (x:real^(1,3)finite_sum))) %
                                       sndcart x`]) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[P4_RADIAL_SPHERE]; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN EXPAND_TAC "L" THEN
      REWRITE_TAC[wan_rext] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `{x:real^(1,3)finite_sum | drop(fstcart x) IN real_interval(--(&1),&1) /\
                                ~(sndcart x = vec 0) /\
                                mfd_emb_inv top (f:A->real^K)
                                  (closest_point (IMAGE f (topspace top)) (L x)) IN
                                FST(c:(A->bool)#(A->real^N))} =
      {x | x IN {x:real^(1,3)finite_sum | drop(fstcart x) IN real_interval(--(&1),&1) /\
                                         ~(sndcart x = vec 0)} /\
           L x IN {z | (?p. p IN IMAGE f (topspace top) /\ dist(z,p) < d1) /\
                       mfd_emb_inv top f (closest_point (IMAGE f (topspace top)) z) IN
                       FST c}}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:real^(1,3)finite_sum` THEN
      EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN USE_THEN "LT" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\x. SND (c:(A->bool)#(A->real^N))
             (mfd_emb_inv top (f:A->real^K)
                (closest_point (IMAGE f (topspace top)) ((L:real^(1,3)finite_sum->real^K)
                    x)))) =
      (\z. SND c (mfd_emb_inv top f (closest_point (IMAGE f (topspace top)) z))) o L`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `{z | (?p. p IN IMAGE (f:A->real^K) (topspace top) /\ dist(z,p) < d1) /\
                     mfd_emb_inv top f (closest_point (IMAGE f (topspace top)) z) IN
                     FST(c:(A->bool)#(A->real^N))}` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[CMT_TIME_OPEN] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `{x:real^(1,3)finite_sum | ~(sndcart x = vec 0)}` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN SET_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `{x:real^(1,3)finite_sum | ~(sndcart x = vec 0)}` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  ABBREV_TAC
   `ws = \y. closest_point (IMAGE (f:A->real^K) (topspace top))
               (((f:A->real^K) o (v:real^3->A)) y + (e * s) % (phi:real^3->real^K) y)` THEN
  SUBGOAL_THEN
   `(\y. mfd_emb_inv top (f:A->real^K)
           (closest_point (IMAGE f (topspace top))
              (((f:A->real^K) o (v:real^3->A)) y + (e * s) % (phi:real^3->real^K) y))) =
    mfd_emb_inv top f o (ws:real^3->real^K)`
  SUBST1_TAC THENL [EXPAND_TAC "ws" THEN REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN sphere(vec 0,&1)
                    ==> (ws:real^3->real^K) y IN IMAGE (f:A->real^K) (topspace top)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "ws" THEN REWRITE_TAC[] THEN
    USE_THEN "CPT" MATCH_MP_TAC THEN
    EXISTS_TAC `((f:A->real^K) o (v:real^3->A)) y` THEN
    USE_THEN "TUB" (MP_TAC o SPECL [`s:real`; `y:real^3`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[];
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext (ws:real^3->real^K))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(f:A->real^K) o (v:real^3->A)`; `phi:real^3->real^K`; `e:real`]
                  CMT_LFAMILY_SMOOTH) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `closest_point (IMAGE (f:A->real^K) (topspace top)) o
                (\x. wan_rext ((f:A->real^K) o (v:real^3->A)) (sndcart x) +
                     (e * drop(fstcart x)) % wan_rext (phi:real^3->real^K) (sndcart x)) o
                (\z:real^3. pastecart (lift s) z)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
      EXPAND_TAC "ws" THEN REWRITE_TAC[wan_rext; o_THM];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `{z:real^K | ?p. p IN IMAGE (f:A->real^K) (topspace top) /\ dist(z,p) < d}`
        THEN
    ASM_REWRITE_TAC[CMT_OPEN_NONZERO; GRGE_TUBE_OPEN] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; o_THM; FSTCART_PASTECART;
                  SNDCART_PASTECART; LIFT_DROP; wan_rext] THEN
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      EXISTS_TAC `((f:A->real^K) o (v:real^3->A)) (inv(norm(z:real^3)) % z)` THEN
      USE_THEN "TUB" (MP_TAC o SPECL [`s:real`; `inv(norm(z:real^3)) % z`]) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[P4_RADIAL_SPHERE]; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o REWRITE_RULE[o_THM])
                                 (MP_TAC o REWRITE_RULE[o_THM])) THEN
      REWRITE_TAC[o_THM] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
      EXISTS_TAC `{x:real^(1,3)finite_sum | ~(sndcart x = vec 0)}` THEN
      ASM_SIMP_TAC[CMT_OPEN_NONZERO] THEN REPEAT CONJ_TAC THENL
       [MP_TAC(ISPEC `{z:real^3 | ~(z = vec 0)}` CMT_SNDCART_OPEN) THEN
        REWRITE_TAC[CMT_OPEN_NONZERO; IN_ELIM_THM];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; SNDCART_PASTECART] THEN
            SIMP_TAC[];
        MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
        REWRITE_TAC[CMT_OPEN_NONZERO; SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_ID]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `ws:real^3->real^K`]
                CM_EMB_TO_P4) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `continuously_differentiable 1 {z:real^3 | ~(z = vec 0)}
                  (wan_rext (ws:real^3->real^K))` ASSUME_TAC THENL
   [ASM_MESON_TAC[smooth_map_on]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `g:A->real^N^N`;
                 `G:real^K->real^K^K`; `mfd_emb_inv top (f:A->real^K) o
                     (ws:real^3->real^K)`]
                CM_P4_BRIDGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  MATCH_MP_TAC CMT_SEN_SPHERE_EQ THEN REWRITE_TAC[o_THM] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CMT_EMB_INV_RIGHT]);;

let CMT_VAR_CONT = prove
 (`!top (V:real->real^3->A).
     continuous_map
       (prod_topology (subtopology euclideanreal (real_interval(--(&1),&1)))
                      (subtopology euclidean (sphere(vec 0:real^3,&1))),top)
       (\(s,y). V s y)
     ==> continuous_map
           (subtopology euclidean
              {x:real^(1,3)finite_sum | drop(fstcart x) IN real_interval(--(&1),&1) /\
                                        ~(sndcart x = vec 0)},top)
           (\x. V (drop(fstcart x)) (inv(norm(sndcart x)) % sndcart x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x:real^(1,3)finite_sum. (V:real->real^3->A) (drop(fstcart x))
                                (inv(norm(sndcart x)) % sndcart x)) =
    (\(s,y). V s y) o (\x. drop(fstcart x),inv(norm(sndcart x)) % sndcart x)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `prod_topology (subtopology euclideanreal (real_interval(--(&1),&1)))
                            (subtopology euclidean (sphere(vec 0:real^3,&1)))` THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_PAIRED] THEN CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; CONTINUOUS_MAP_EQ_LIFT] THEN CONJ_TAC THENL
     [REWRITE_TAC[o_DEF; LIFT_DROP; CONTINUOUS_MAP_EUCLIDEAN] THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; ETA_AX; LINEAR_FSTCART];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; IN_ELIM_THM] THEN
      SIMP_TAC[]];
    REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `(\x:real^(1,3)finite_sum. inv(norm(sndcart x)) % sndcart x) =
        (\z. inv(norm z) % z) o sndcart` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
      REWRITE_TAC[CMT_NORMALIZE_CONTINUOUS] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      SIMP_TAC[P4_RADIAL_SPHERE]]]);;

let CMT_P4_C1_SPHERE_EQ = prove
 (`!top atlas (u:real^3->A) u'.
        (!y. y IN sphere(vec 0,&1) ==> u y = u' y)
        ==> (p4_s2_c1 (top,atlas:((A->bool)#(A->real^N))->bool) u <=>
             p4_s2_c1 (top,atlas) u')`,
  SUBGOAL_THEN
   `!top atlas (u:real^3->A) u'.
        (!y. y IN sphere(vec 0,&1) ==> u y = u' y) /\
        p4_s2_c1 (top,atlas:((A->bool)#(A->real^N))->bool) u
        ==> p4_s2_c1 (top,atlas) u'`
  (fun th -> MESON_TAC[th]) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[p4_s2_c1] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "EQ") (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SM")))
    THEN
  SUBGOAL_THEN
   `!z:real^3. ~(z = vec 0) ==> (u:real^3->A)(inv(norm z) % z) = u'(inv(norm z) % z)`
  (LABEL_TAC "EQZ") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "EQ" MATCH_MP_TAC THEN
    ASM_SIMP_TAC[P4_RADIAL_SPHERE];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN EXISTS_TAC `u:real^3->A` THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
    ALL_TAC] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `{z:real^3 | ~(z = vec 0) /\ (u':real^3->A)(inv(norm z) % z) IN
       FST(c:(A->bool)#(A->real^N))} =
    {z:real^3 | ~(z = vec 0) /\ (u:real^3->A)(inv(norm z) % z) IN FST c}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
    ASM_CASES_TAC `x:real^3 = vec 0` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MFDM_CONTINUOUSLY_DIFFERENTIABLE_EQ THEN
  EXISTS_TAC `\z. SND (c:(A->bool)#(A->real^N)) ((u:real^3->A)(inv(norm z) % z))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    USE_THEN "SM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let CMT_VARIATION_FAMILY = prove
 (`!top atlas (g:A->real^N^N) (f:A->real^K) (G:real^K->real^K^K) d (v:real^3->A) V.
     cm_emb (top,atlas) g f G d /\ p4_s2_variation (top,atlas) v V
     ==> smooth_map_on
           {x:real^(1,3)finite_sum | drop(fstcart x) IN real_interval(--(&1),&1) /\
                                     ~(sndcart x = vec 0)}
           (\x. f(V (drop(fstcart x)) (inv(norm(sndcart x)) % sndcart x))) /\
         (!x t. drop(fstcart x) IN real_interval(--(&1),&1) /\ ~(sndcart x = vec 0) /\
                &0 < t
                ==> f(V (drop(fstcart(pastecart (fstcart x) (t % sndcart x))))
                        (inv(norm(sndcart(pastecart (fstcart x) (t % sndcart x)))) %
                         sndcart(pastecart (fstcart x) (t % sndcart x)))) =
                    f(V (drop(fstcart x)) (inv(norm(sndcart x)) % sndcart x))) /\
         (!s. s IN real_interval(--(&1),&1)
              ==> p4_s2_energy atlas g (V s) = cm_sen G (f o V s))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "EMB") MP_TAC) THEN
  REWRITE_TAC[p4_s2_variation] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "V0") (CONJUNCTS_THEN2 (LABEL_TAC "VC")
    (LABEL_TAC "VS"))) THEN
  USE_THEN "EMB" (MP_TAC o REWRITE_RULE[cm_emb]) THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_immersion_into (atlas:((A->bool)#(A->real^N))->bool) (f:A->real^K)`
  ASSUME_TAC THENL [ASM_MESON_TAC[mfd_embedding]; ALL_TAC] THEN
  USE_THEN "VC" (ASSUME_TAC o MATCH_MP CMT_VAR_CONT) THEN
  ABBREV_TAC `D1 = {x:real^(1,3)finite_sum | drop(fstcart x) IN real_interval(--(&1),&1) /\
                                             ~(sndcart x = vec 0)}` THEN
  SUBGOAL_THEN `open(D1:real^(1,3)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "D1" THEN REWRITE_TAC[CMT_TIME_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN D1 ==> (V:real->real^3->A) (drop(fstcart x)) (inv(norm(sndcart x)) % sndcart x)
                    IN topspace top`
  (LABEL_TAC "VT") THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; SUBSET; FORALL_IN_IMAGE] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on D1
      (\x. (f:A->real^K)((V:real->real^3->A) (drop(fstcart x))
                                              (inv(norm(sndcart x)) % sndcart x)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x0:real^(1,3)finite_sum` THEN DISCH_TAC THEN
    USE_THEN "VT" (ASSUME_TAC o C MATCH_MP (ASSUME `(x0:real^(1,3)finite_sum) IN D1`)) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(V:real->real^3->A) (drop(fstcart (x0:real^(1,3)finite_sum)))
                                        (inv(norm(sndcart x0)) % sndcart x0)`] CHART_AT)
                                            THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool)
                      ((V:real->real^3->A) (drop(fstcart (x0:real^(1,3)finite_sum)))
                                           (inv(norm(sndcart x0)) % sndcart x0))` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `f:A->real^K`; `c:(A->bool)#(A->real^N)`] GRGE_IMMERSION_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `open {x:real^(1,3)finite_sum | drop(fstcart x) IN real_interval(--(&1),&1) /\
                                     ~(sndcart x = vec 0) /\
                                     (V:real->real^3->A) (drop(fstcart x))
                                       (inv(norm(sndcart x)) % sndcart x) IN
                                     FST(c:(A->bool)#(A->real^N))}`
    ASSUME_TAC THENL
     [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `D1:real^(1,3)finite_sum->bool` THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`\x:real^(1,3)finite_sum. (V:real->real^3->A) (drop(fstcart x))
                                                 (inv(norm(sndcart x)) % sndcart x)`;
                     `subtopology euclidean (D1:real^(1,3)finite_sum->bool)`;
                     `top:A topology`; `FST(c:(A->bool)#(A->real^N))`]
                    OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
      ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
      EXPAND_TAC "D1" THEN REWRITE_TAC[IN_ELIM_THM; CONJ_ASSOC];
      ALL_TAC] THEN
    EXISTS_TAC `{x:real^(1,3)finite_sum | drop(fstcart x) IN real_interval(--(&1),&1) /\
                                          ~(sndcart x = vec 0) /\
                                          (V:real->real^3->A) (drop(fstcart x))
                                            (inv(norm(sndcart x)) % sndcart x) IN
                                          FST(c:(A->bool)#(A->real^N))}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `(x0:real^(1,3)finite_sum) IN D1` THEN EXPAND_TAC "D1" THEN
      SIMP_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `((f:A->real^K) o chart_inv (c:(A->bool)#(A->real^N))) o
                (\x:real^(1,3)finite_sum. SND c ((V:real->real^3->A) (drop(fstcart x))
                                                   (inv(norm(sndcart x)) % sndcart x)))`
                                                       THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM; o_THM] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[FUN_IN_IMAGE];
      USE_THEN "VS" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; NORM_MUL; VECTOR_MUL_ASSOC;
                REAL_INV_MUL] THEN
    REPEAT AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `(a * b) * c:real = b * (a * c)`] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_RID];
    ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!y. y IN sphere(vec 0,&1) ==> (V:real->real^3->A) s y IN topspace top`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "VT" (MP_TAC o SPEC `pastecart (lift s) (y:real^3)`) THEN
    EXPAND_TAC "D1" THEN
    REWRITE_TAC[IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    SUBGOAL_THEN `~(y:real^3 = vec 0) /\ inv(norm y) % y = y` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `y IN sphere(vec 0:real^3,&1)` THEN
      REWRITE_TAC[IN_SPHERE_0] THEN DISCH_TAC THEN
      ASM_REWRITE_TAC[REAL_INV_1; VECTOR_MUL_LID] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `norm(vec 0:real^3) = &1` THEN REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `p4_s2_c1 (top,atlas:((A->bool)#(A->real^N))->bool) ((V:real->real^3->A) s)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `f:A->real^K`; `G:real^K->real^K^K`; `d:real`;
                   `(f:A->real^K) o (V:real->real^3->A) s`] CM_EMB_TO_P4) THEN
    ASM_SIMP_TAC[o_THM; FUN_IN_IMAGE] THEN
    SUBGOAL_THEN `continuously_differentiable 1 {z:real^3 | ~(z = vec 0)}
                    (wan_rext ((f:A->real^K) o (V:real->real^3->A) s))` ASSUME_TAC THENL
     [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_EQ_OPEN THEN
      EXISTS_TAC `(\x. (f:A->real^K)((V:real->real^3->A) (drop(fstcart x))
                                       (inv(norm(sndcart x)) % sndcart x))) o
                  (\z:real^3. pastecart (lift s) z)` THEN
      REWRITE_TAC[CMT_OPEN_NONZERO] THEN CONJ_TAC THENL
       [REWRITE_TAC[IN_ELIM_THM; o_THM; wan_rext; FSTCART_PASTECART; SNDCART_PASTECART;
                    LIFT_DROP];
        ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_COMPOSE_OPEN THEN
      EXISTS_TAC `D1:real^(1,3)finite_sum->bool` THEN
      ASM_REWRITE_TAC[CMT_OPEN_NONZERO] THEN REPEAT CONJ_TAC THENL
       [EXPAND_TAC "D1" THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; FSTCART_PASTECART;
                    SNDCART_PASTECART; LIFT_DROP] THEN
        ASM_SIMP_TAC[];
        SUBGOAL_THEN `smooth_map_on {z:real^3 | ~(z = vec 0)} (\z. pastecart (lift s) z)`
        MP_TAC THENL
         [MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
          REWRITE_TAC[CMT_OPEN_NONZERO; SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_ID];
          SIMP_TAC[smooth_map_on]];
        ASM_MESON_TAC[smooth_map_on]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC CMT_P4_C1_SPHERE_EQ THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN MATCH_MP_TAC GRGE_EMB_INV_LEFT THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `g:A->real^N^N`;
                 `G:real^K->real^K^K`; `(V:real->real^3->A) s`] CM_P4_BRIDGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `cm_target (IMAGE (f:A->real^K) (topspace top)) (G:real^K->real^K^K) d` THEN
    SIMP_TAC[cm_target];
    SIMP_TAC[]]);;

let CMT_PD1_AFFINE = prove
 (`!(g1:real^3->real^K) g2 s y.
        g1 differentiable at y /\ g2 differentiable at y
        ==> partial_derivative 1 (\x:real^(1,3)finite_sum. g1 (sndcart x) +
                                                           drop(fstcart x) % g2 (sndcart x))
                               (pastecart (lift s) y) = g2 y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FRECHET_DERIVATIVE_WORKS] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `((\x:real^(1,3)finite_sum. (g1:real^3->real^K) (sndcart x) +
                               drop(fstcart x) % g2 (sndcart x)) has_derivative
     (\h. frechet_derivative g1 (at y) (sndcart h) +
          (s % frechet_derivative g2 (at y) (sndcart h) +
           drop(fstcart h) % g2 y))) (at (pastecart (lift s) y))`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\x:real^(1,3)finite_sum. (g1:real^3->real^K) (sndcart x)) = g1 o
         sndcart`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      SUBGOAL_THEN `(\h:real^(1,3)finite_sum. frechet_derivative (g1:real^3->real^K) (at y)
                                                (sndcart h)) =
                    frechet_derivative g1 (at y) o sndcart` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC DIFF_CHAIN_AT THEN
      ASM_REWRITE_TAC[SNDCART_PASTECART] THEN
      MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_SNDCART];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\x:real^(1,3)finite_sum. drop(fstcart x)`;
                   `\h:real^(1,3)finite_sum. drop(fstcart h)`;
                   `\x:real^(1,3)finite_sum. (g2:real^3->real^K) (sndcart x)`;
                   `\h:real^(1,3)finite_sum. frechet_derivative (g2:real^3->real^K) (at y)
                                               (sndcart h)`;
                   `pastecart (lift s) (y:real^3)`] HAS_DERIVATIVE_MUL_AT) THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL
     [REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX] THEN
      MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_FSTCART];
      ALL_TAC] THEN
    SUBGOAL_THEN `(\x:real^(1,3)finite_sum. (g2:real^3->real^K) (sndcart x)) = g2 o sndcart`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    SUBGOAL_THEN `(\h:real^(1,3)finite_sum. frechet_derivative (g2:real^3->real^K) (at y)
                                              (sndcart h)) =
                  frechet_derivative g2 (at y) o sndcart` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN
    ASM_REWRITE_TAC[SNDCART_PASTECART] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_SNDCART];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SPEC `1` o MATCH_MP PARTIAL_DERIVATIVE_HAS_DERIVATIVE_UNIQUE) THEN
  REWRITE_TAC[CMT_BASIS_PASTECART; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP;
              VECTOR_MUL_LID] THEN
  SUBGOAL_THEN `linear(frechet_derivative (g1:real^3->real^K) (at y)) /\
                linear(frechet_derivative (g2:real^3->real^K) (at y))` STRIP_ASSUME_TAC
                    THENL
   [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
  MP_TAC(ISPEC `frechet_derivative (g1:real^3->real^K) (at y)` LINEAR_0) THEN
  MP_TAC(ISPEC `frechet_derivative (g2:real^3->real^K) (at y)` LINEAR_0) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID]);;

let CMT_TANGENT = prove
 (`!(W:real^(1,3)finite_sum->real^K) (P:real^K->real^K) D Tb S i x.
        open D /\ smooth_map_on D W /\ open Tb /\ smooth_map_on Tb P /\
        S SUBSET Tb /\ (!x. x IN D ==> W x IN S) /\ (!p. p IN S ==> P p = p) /\ x IN D
        ==> frechet_derivative P (at (W x)) (partial_derivative i W x) =
            partial_derivative i W x`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS `partial_derivative i ((P:real^K->real^K) o
                                            (W:real^(1,3)finite_sum->real^K)) x` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC PARTIAL_DERIVATIVE_CHAIN THEN CONJ_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `D:real^(1,3)finite_sum->bool`; EXISTS_TAC `Tb:real^K->bool`] THEN
    ASM SET_TAC[];
    MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN
    EXISTS_TAC `D:real^(1,3)finite_sum->bool` THEN ASM_SIMP_TAC[o_THM]]);;

let CMT_PD1_RADIAL = prove
 (`!(W:real^(1,3)finite_sum->real^K) D x t.
        open D /\ smooth_map_on D W /\ x IN D /\ &0 < t /\
        (!x. x IN D ==> pastecart (fstcart x) (t % sndcart x) IN D /\
                        W(pastecart (fstcart x) (t % sndcart x)) = W x)
        ==> partial_derivative 1 W (pastecart (fstcart x) (t % sndcart x)) =
            partial_derivative 1 W x`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `M = \x:real^(1,3)finite_sum. pastecart (fstcart x) (t % sndcart x)` THEN
  SUBGOAL_THEN `linear(M:real^(1,3)finite_sum->real^(1,3)finite_sum)` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN MATCH_MP_TAC LINEAR_PASTECART THEN
    REWRITE_TAC[LINEAR_FSTCART; ETA_AX] THEN MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN
    REWRITE_TAC[LINEAR_SNDCART; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `(M:real^(1,3)finite_sum->real^(1,3)finite_sum) (basis 1) = basis 1`
  ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN
    REWRITE_TAC[CMT_BASIS_PASTECART; FSTCART_PASTECART; SNDCART_PASTECART;
                VECTOR_MUL_RZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `pastecart (fstcart x) (t % sndcart x) =
      (M:real^(1,3)finite_sum->real^(1,3)finite_sum) x`
  SUBST1_TAC THENL [EXPAND_TAC "M" THEN REWRITE_TAC[]; ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `partial_derivative 1 ((W:real^(1,3)finite_sum->real^K) o
                          (M:real^(1,3)finite_sum->real^(1,3)finite_sum)) x` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`1`; `M:real^(1,3)finite_sum->real^(1,3)finite_sum`;
                   `W:real^(1,3)finite_sum->real^K`; `x:real^(1,3)finite_sum`]
                  PARTIAL_DERIVATIVE_CHAIN) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [ASM_MESON_TAC[differentiable; HAS_DERIVATIVE_LINEAR];
        MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
        EXISTS_TAC `D:real^(1,3)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `x:real^(1,3)finite_sum`) THEN ASM_REWRITE_TAC[] THEN
        EXPAND_TAC "M" THEN SIMP_TAC[]];
      DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[PARTIAL_DERIVATIVE_LINEAR] THEN REWRITE_TAC[partial_derivative];
    MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN
    EXISTS_TAC `D:real^(1,3)finite_sum->bool` THEN ASM_REWRITE_TAC[o_THM] THEN
    EXPAND_TAC "M" THEN ASM_SIMP_TAC[]]);;

let CMT_P4_TO_CM_CRIT = prove
 (`!top atlas (g:A->real^N^N) (f:A->real^K) (G:real^K->real^K^K) d
    (v:real^3->A) (phi:real^3->real^K).
     cm_emb (top,atlas) g f G d /\
     (!y. y IN sphere(vec 0,&1) ==> v y IN topspace top) /\
     smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext (f o v)) /\
     smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext phi) /\
     (!V. p4_s2_variation (top,atlas) v V
          ==> ((\s. p4_s2_energy atlas g (V s)) has_real_derivative &0) (atreal (&0)))
     ==> ((\e. cm_sen G (\y. closest_point (IMAGE f (topspace top)) ((f o v) y + e % phi
         y)))
          has_real_derivative &0) (atreal (&0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`;
                 `phi:real^3->real^K`] CMT_PROJ_VARIATION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `V:real->real^3->A` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "EN"))))) THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP
    (ASSUME `p4_s2_variation (top,atlas:((A->bool)#(A->real^N))->bool) (v:real^3->A) V`))
        THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `((\s. cm_sen (G:real^K->real^K^K)
            (\y. closest_point (IMAGE (f:A->real^K) (topspace top))
                   (((f:A->real^K) o (v:real^3->A)) y + (e * s) % (phi:real^3->real^K) y)))
     has_real_derivative &0) (atreal (&0))` ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    MAP_EVERY EXISTS_TAC
     [`\s. p4_s2_energy atlas (g:A->real^N^N) ((V:real->real^3->A) s)`; `&1`] THEN
    ASM_REWRITE_TAC[REAL_LT_01] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN USE_THEN "EN" MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\t:real. inv e * t`;
    `\s. cm_sen (G:real^K->real^K^K)
           (\y. closest_point (IMAGE (f:A->real^K) (topspace top))
                  (((f:A->real^K) o (v:real^3->A)) y + (e * s) % (phi:real^3->real^K) y))`;
    `inv e`; `&0`; `&0`] REAL_DIFF_CHAIN_ATREAL) THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_LZERO] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\t:real. t`; `&1`; `inv e`; `&0`] HAS_REAL_DERIVATIVE_LMUL_ATREAL) THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_ID; REAL_MUL_RID];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `t:real` THEN
  ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_MUL_LID]);;

let CMT_PROJ_FAMILY = prove
 (`!top atlas (g:A->real^N^N) (f:A->real^K) (G:real^K->real^K^K) d
    (v:real^3->A) (phi:real^3->real^K).
     cm_emb (top,atlas) g f G d /\
     (!y. y IN sphere(vec 0,&1) ==> v y IN topspace top) /\
     smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext (f o v)) /\
     smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext phi)
     ==> ?a. &0 < a /\
             smooth_map_on
               {x:real^(1,3)finite_sum | drop(fstcart x) IN real_interval(--a,a) /\
                                         ~(sndcart x = vec 0)}
               (closest_point (IMAGE f (topspace top)) o
                (\x. wan_rext (f o v) (sndcart x) +
                     drop(fstcart x) % wan_rext phi (sndcart x)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "EMB") (CONJUNCTS_THEN2 (LABEL_TAC "VM")
    (CONJUNCTS_THEN2 (LABEL_TAC "WS") (LABEL_TAC "PS")))) THEN
  USE_THEN "EMB" (MP_TAC o REWRITE_RULE[cm_emb; cm_target; cm_tube; IN_ELIM_THM]) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(phi:real^3->real^K) continuous_on sphere(vec 0,&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN EXISTS_TAC `wan_rext (phi:real^3->real^K)` THEN
    SIMP_TAC[CM_REXT_SPHERE] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_SPHERE_0] THEN X_GEN_TAC `x:real^3` THEN
    ASM_CASES_TAC `x:real^3 = vec 0` THEN ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?B. &0 < B /\ !y. y IN sphere(vec 0,&1) ==> norm((phi:real^3->real^K) y) <= B`
  (X_CHOOSE_THEN `B:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "BD"))) THENL
   [MP_TAC(ISPECL [`phi:real^3->real^K`; `sphere(vec 0:real^3,&1)`]
                  COMPACT_CONTINUOUS_IMAGE) THEN
    ASM_REWRITE_TAC[COMPACT_SPHERE] THEN DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED)
        THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE];
    ALL_TAC] THEN
  ABBREV_TAC `a = d / (&2 * B)` THEN
  SUBGOAL_THEN `&0 < a /\ a * B < d` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `d / (&2 * B) * B = d / &2` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < B` THEN CONV_TAC REAL_FIELD; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `{z:real^K | ?p. p IN IMAGE (f:A->real^K) (topspace top) /\ dist(z,p) < d}`
      THEN
  ASM_REWRITE_TAC[CMT_TIME_OPEN; GRGE_TUBE_OPEN] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^(1,3)finite_sum` THEN STRIP_TAC THEN
    EXISTS_TAC `wan_rext ((f:A->real^K) o (v:real^3->A)) (sndcart
        (x:real^(1,3)finite_sum))` THEN
    REWRITE_TAC[NORM_ARITH `dist(a + b:real^N,a) = norm b`; NORM_MUL] THEN
    SUBGOAL_THEN `inv(norm(sndcart (x:real^(1,3)finite_sum))) % sndcart x IN sphere(vec
        0,&1)`
    ASSUME_TAC THENL [ASM_SIMP_TAC[P4_RADIAL_SPHERE]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[wan_rext; o_THM] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      USE_THEN "VM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `a * B` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `drop(fstcart (x:real^(1,3)finite_sum)) IN real_interval(--a,a)` THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
      REWRITE_TAC[wan_rext] THEN USE_THEN "BD" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    SUBGOAL_THEN
     `(\x:real^(1,3)finite_sum. wan_rext ((f:A->real^K) o (v:real^3->A)) (sndcart x) +
                                drop(fstcart x) % wan_rext (phi:real^3->real^K) (sndcart
                                    x)) =
      (\x. wan_rext (f o v) (sndcart x) + (&1 * drop(fstcart x)) % wan_rext phi (sndcart
          x))`
    SUBST1_TAC THENL [REWRITE_TAC[REAL_MUL_LID]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `{x:real^(1,3)finite_sum | ~(sndcart x = vec 0)}` THEN
    ASM_SIMP_TAC[CMT_LFAMILY_SMOOTH] THEN SET_TAC[]]);;

let CMT_FV_ZERO = prove
 (`!top atlas (g:A->real^N^N) (f:A->real^K) (G:real^K->real^K^K) d (v:real^3->A)
    (W:real^(1,3)finite_sum->real^K).
     cm_emb (top,atlas) g f G d /\
     (!y. y IN sphere(vec 0,&1) ==> v y IN topspace top) /\
     smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext (f o v)) /\
     (!phi:real^3->real^K.
         smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext phi)
         ==> ((\e. cm_sen G (\y. closest_point (IMAGE f (topspace top))
                                                ((f o v) y + e % phi y)))
              has_real_derivative &0) (atreal (&0))) /\
     smooth_map_on {x | drop(fstcart x) IN real_interval(--(&1),&1) /\ ~(sndcart x = vec
         0)} W /\
     (!x t. drop(fstcart x) IN real_interval(--(&1),&1) /\ ~(sndcart x = vec 0) /\ &0 < t
            ==> W(pastecart (fstcart x) (t % sndcart x)) = W x) /\
     (!x. drop(fstcart x) IN real_interval(--(&1),&1) /\ ~(sndcart x = vec 0)
          ==> W x IN IMAGE f (topspace top)) /\
     (!y. ~(y = vec 0) ==> W(pastecart (lift(&0)) y) = wan_rext (f o v) y)
     ==> drop(integral wan_shell
               (\z. partial_derivative 1 (\x. lift(cmt_psi G (cmt_jet W x)))
                                       (pastecart (lift(&0)) z))) / &3 = &0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "EMB") (CONJUNCTS_THEN2 (LABEL_TAC "VM")
    (CONJUNCTS_THEN2 (LABEL_TAC "WS") (CONJUNCTS_THEN2 (LABEL_TAC "CRIT")
    (CONJUNCTS_THEN2 (LABEL_TAC "W1") (CONJUNCTS_THEN2 (LABEL_TAC "W2")
    (CONJUNCTS_THEN2 (LABEL_TAC "W3") (LABEL_TAC "W4")))))))) THEN
  USE_THEN "EMB" (MP_TAC o REWRITE_RULE[cm_emb; cm_target; cm_tube; IN_ELIM_THM]) THEN
  STRIP_TAC THEN
  ABBREV_TAC `D1 = {x:real^(1,3)finite_sum | drop(fstcart x) IN real_interval(--(&1),&1) /\
                                             ~(sndcart x = vec 0)}` THEN
  SUBGOAL_THEN `open(D1:real^(1,3)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "D1" THEN REWRITE_TAC[CMT_TIME_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. ~(y = vec 0) ==> pastecart (lift(&0)) y IN D1` (LABEL_TAC "P0")
  THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "D1" THEN
    REWRITE_TAC[IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP;
                IN_REAL_INTERVAL] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN D1 ==> (W:real^(1,3)finite_sum->real^K) x IN IMAGE (f:A->real^K) (topspace
       top)`
  (LABEL_TAC "W3D") THENL
   [EXPAND_TAC "D1" THEN REWRITE_TAC[IN_ELIM_THM] THEN USE_THEN "W3" ACCEPT_TAC; ALL_TAC]
       THEN
  SUBGOAL_THEN
   `!x t. x IN D1 /\ &0 < t
          ==> pastecart (fstcart x) (t % sndcart x) IN D1 /\
              (W:real^(1,3)finite_sum->real^K)(pastecart (fstcart x) (t % sndcart x)) = W x`
  (LABEL_TAC "WR") THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "D1" THEN
    REWRITE_TAC[IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ] THEN
    USE_THEN "W2" (MP_TAC o SPECL [`x:real^(1,3)finite_sum`; `t:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `X = \y:real^3. partial_derivative 1 (W:real^(1,3)finite_sum->real^K)
                                                  (pastecart (lift(&0)) y)` THEN
  SUBGOAL_THEN `smooth_map_on {z:real^3 | ~(z = vec 0)} (X:real^3->real^K)` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN
    SUBGOAL_THEN
     `(\y:real^3. partial_derivative 1 (W:real^(1,3)finite_sum->real^K)
                                       (pastecart (lift(&0)) y)) =
      (\x. frechet_derivative W (at x) (basis 1)) o (\y. pastecart (lift(&0)) y)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; partial_derivative]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `D1:real^(1,3)finite_sum->bool`
        THEN
    ASM_SIMP_TAC[CMT_OPEN_NONZERO; SMOOTH_MAP_ON_FRECHET_DERIVATIVE] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
      REWRITE_TAC[CMT_OPEN_NONZERO; SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_ID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. ~(y = vec 0) ==> wan_rext (X:real^3->real^K) y = X y`
  (LABEL_TAC "XR") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[wan_rext] THEN EXPAND_TAC "X" THEN
    MP_TAC(ISPECL [`W:real^(1,3)finite_sum->real^K`; `D1:real^(1,3)finite_sum->bool`;
                   `pastecart (lift(&0)) (y:real^3)`; `inv(norm(y:real^3))`]
                       CMT_PD1_RADIAL) THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN DISCH_THEN MATCH_MP_TAC THEN
    SUBGOAL_THEN `&0 < inv(norm(y:real^3))` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_INV_EQ; NORM_POS_LT]; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext (X:real^3->real^K))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `X:real^3->real^K` THEN
    ASM_SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  USE_THEN "CRIT" (LABEL_TAC "CX" o C MATCH_MP
    (ASSUME `smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext (X:real^3->real^K))`)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`;
                 `X:real^3->real^K`] CMT_PROJ_FAMILY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "US"))) THEN
  MP_TAC(ISPECL [`(f:A->real^K) o (v:real^3->A)`; `X:real^3->real^K`; `&1`]
                CMT_LFAMILY_SMOOTH) THEN
  ASM_REWRITE_TAC[REAL_MUL_LID] THEN DISCH_TAC THEN
  ABBREV_TAC
   `L = \x:real^(1,3)finite_sum. wan_rext ((f:A->real^K) o (v:real^3->A)) (sndcart x) +
                                 drop(fstcart x) % wan_rext (X:real^3->real^K) (sndcart x)`
                                     THEN
  ABBREV_TAC `Ut = closest_point (IMAGE (f:A->real^K) (topspace top)) o
                   (L:real^(1,3)finite_sum->real^K)` THEN
  SUBGOAL_THEN
   `!x t. drop(fstcart x) IN real_interval(--a,a) /\ ~(sndcart x = vec 0) /\ &0 < t
          ==> (Ut:real^(1,3)finite_sum->real^K)(pastecart (fstcart x) (t % sndcart x)) = Ut
              x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "Ut" THEN EXPAND_TAC "L" THEN REWRITE_TAC[o_THM] THEN
    ASM_SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART; CM_REXT_SCALE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\s. cm_sen (G:real^K->real^K^K)
            (\y. (Ut:real^(1,3)finite_sum->real^K) (pastecart (lift s) y)))
     has_real_derivative
     drop(integral wan_shell
           (\z. partial_derivative 1 (\x. lift(cmt_psi G (cmt_jet Ut x)))
                                   (pastecart (lift(&0)) z))) / &3) (atreal (&0))`
  (LABEL_TAC "FU") THENL
   [MATCH_MP_TAC CMT_FIRST_VARIATION THEN EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. cm_sen (G:real^K->real^K^K)
          (\y. (Ut:real^(1,3)finite_sum->real^K) (pastecart (lift s) y)) =
        cm_sen G (\y. closest_point (IMAGE (f:A->real^K) (topspace top))
                        (((f:A->real^K) o (v:real^3->A)) y + s % (X:real^3->real^K) y))`
  (LABEL_TAC "UE") THENL
   [GEN_TAC THEN MATCH_MP_TAC CMT_SEN_SPHERE_EQ THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC
       THEN
    EXPAND_TAC "Ut" THEN EXPAND_TAC "L" THEN REWRITE_TAC[o_THM] THEN
    ASM_SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; CM_REXT_SPHERE; o_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `drop(integral wan_shell
           (\z. partial_derivative 1
                  (\x. lift(cmt_psi (G:real^K->real^K^K)
                                    (cmt_jet (Ut:real^(1,3)finite_sum->real^K) x)))
                  (pastecart (lift(&0)) z))) / &3 = &0`
  (LABEL_TAC "U0") THENL
   [MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
    EXISTS_TAC `\s. cm_sen (G:real^K->real^K^K)
                     (\y. (Ut:real^(1,3)finite_sum->real^K) (pastecart (lift s) y))` THEN
    EXISTS_TAC `&0` THEN CONJ_TAC THENL
     [USE_THEN "FU" ACCEPT_TAC;
      USE_THEN "UE" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "CX" ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^3. ~(y = vec 0)
               ==> (L:real^(1,3)finite_sum->real^K) (pastecart (lift(&0)) y) =
                   W(pastecart (lift(&0)) y) /\
                   W(pastecart (lift(&0)) y) IN IMAGE (f:A->real^K) (topspace top)`
  (LABEL_TAC "LV") THENL
   [REPEAT STRIP_TAC THENL
     [EXPAND_TAC "L" THEN
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; VECTOR_MUL_LZERO;
                  VECTOR_ADD_RID] THEN
      CONV_TAC SYM_CONV THEN USE_THEN "W4" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "W3D" MATCH_MP_TAC THEN USE_THEN "P0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^3. ~(y = vec 0)
               ==> (Ut:real^(1,3)finite_sum->real^K) (pastecart (lift(&0)) y) =
                   W(pastecart (lift(&0)) y)`
  (LABEL_TAC "UV") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "Ut" THEN REWRITE_TAC[o_THM] THEN
    USE_THEN "LV" (MP_TAC o C MATCH_MP (ASSUME `~(y:real^3 = vec 0)`)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
    MATCH_MP_TAC CLOSEST_POINT_SELF THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^3. ~(y = vec 0)
        ==> partial_derivative 1 (W:real^(1,3)finite_sum->real^K) (pastecart (lift(&0)) y) =
            partial_derivative 1 (Ut:real^(1,3)finite_sum->real^K) (pastecart (lift(&0)) y)`
  (LABEL_TAC "UD") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "Ut" THEN
    USE_THEN "LV" (MP_TAC o C MATCH_MP (ASSUME `~(y:real^3 = vec 0)`)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "LW") ASSUME_TAC) THEN
    SUBGOAL_THEN `(L:real^(1,3)finite_sum->real^K) differentiable at (pastecart (lift(&0))
        y)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `{x:real^(1,3)finite_sum | ~(sndcart x = vec 0)}` THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; SNDCART_PASTECART] THEN
      MP_TAC(ISPEC `{z:real^3 | ~(z = vec 0)}` CMT_SNDCART_OPEN) THEN
      REWRITE_TAC[CMT_OPEN_NONZERO; IN_ELIM_THM];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `closest_point (IMAGE (f:A->real^K) (topspace top)) differentiable
      at ((W:real^(1,3)finite_sum->real^K) (pastecart (lift(&0)) y))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `{z:real^K | ?p. p IN IMAGE (f:A->real^K) (topspace top) /\ dist(z,p) <
          d}` THEN
      ASM_REWRITE_TAC[GRGE_TUBE_OPEN; IN_ELIM_THM] THEN
      EXISTS_TAC `(W:real^(1,3)finite_sum->real^K) (pastecart (lift(&0)) y)` THEN
      ASM_REWRITE_TAC[DIST_REFL];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`1`; `L:real^(1,3)finite_sum->real^K`;
                   `closest_point (IMAGE (f:A->real^K) (topspace top))`;
                   `pastecart (lift(&0)) (y:real^3)`] PARTIAL_DERIVATIVE_CHAIN) THEN
    USE_THEN "LW" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`wan_rext ((f:A->real^K) o (v:real^3->A))`; `wan_rext
        (X:real^3->real^K)`;
                   `&0`; `y:real^3`] CMT_PD1_AFFINE) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN ASM_REWRITE_TAC[CMT_OPEN_NONZERO;
          IN_ELIM_THM];
      ALL_TAC] THEN
    EXPAND_TAC "L" THEN DISCH_THEN SUBST1_TAC THEN
    USE_THEN "XR" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `~(y:real^3 = vec 0)`)]) THEN
    EXPAND_TAC "X" THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CMT_TANGENT THEN
    MAP_EVERY EXISTS_TAC
     [`D1:real^(1,3)finite_sum->bool`;
      `{z:real^K | ?p. p IN IMAGE (f:A->real^K) (topspace top) /\ dist(z,p) < d}`;
      `IMAGE (f:A->real^K) (topspace top)`] THEN
    ASM_SIMP_TAC[GRGE_TUBE_OPEN; CLOSEST_POINT_SELF] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `q:real^K` THEN DISCH_TAC THEN
    EXISTS_TAC `q:real^K` THEN ASM_REWRITE_TAC[DIST_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^3. ~(y = vec 0)
        ==> pastecart (lift(&0)) y IN
            {x:real^(1,3)finite_sum | drop(fstcart x) IN real_interval(--a,a) /\
                                      ~(sndcart x = vec 0)}`
  (LABEL_TAC "PA") THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC[IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP;
                IN_REAL_INTERVAL] THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < a` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^3. ~(z = vec 0)
        ==> partial_derivative 1
              (\x. lift(cmt_psi (G:real^K->real^K^K)
                                (cmt_jet (W:real^(1,3)finite_sum->real^K) x)))
              (pastecart (lift(&0)) z) =
            partial_derivative 1
              (\x. lift(cmt_psi G (cmt_jet (Ut:real^(1,3)finite_sum->real^K) x)))
              (pastecart (lift(&0)) z)`
  (LABEL_TAC "FVE") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMT_FV_VALUE_EQ THEN
    MAP_EVERY EXISTS_TAC
     [`D1:real^(1,3)finite_sum->bool`;
      `{x:real^(1,3)finite_sum | drop(fstcart x) IN real_interval(--a,a) /\
                                 ~(sndcart x = vec 0)}`] THEN
    ASM_REWRITE_TAC[CMT_TIME_OPEN] THEN REPEAT CONJ_TAC THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral wan_shell
      (\z. partial_derivative 1
             (\x. lift(cmt_psi (G:real^K->real^K^K)
                               (cmt_jet (W:real^(1,3)finite_sum->real^K) x)))
             (pastecart (lift(&0)) z)) =
    integral wan_shell
      (\z. partial_derivative 1
             (\x. lift(cmt_psi G (cmt_jet (Ut:real^(1,3)finite_sum->real^K) x)))
             (pastecart (lift(&0)) z))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `z:real^3` THEN
    REWRITE_TAC[wan_shell; IN_ELIM_THM] THEN DISCH_TAC THEN
    USE_THEN "FVE" MATCH_MP_TAC THEN REWRITE_TAC[GSYM NORM_EQ_0] THEN
    UNDISCH_TAC `&1 / &2 < norm(z:real^3) /\ norm z < &2` THEN REAL_ARITH_TAC;
    USE_THEN "U0" ACCEPT_TAC]);;

let CMT_CM_TO_P4_CRIT = prove
 (`!top atlas (g:A->real^N^N) (f:A->real^K) (G:real^K->real^K^K) d (v:real^3->A) V.
     cm_emb (top,atlas) g f G d /\
     (!y. y IN sphere(vec 0,&1) ==> v y IN topspace top) /\
     smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext (f o v)) /\
     (!phi:real^3->real^K.
         smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext phi)
         ==> ((\e. cm_sen G (\y. closest_point (IMAGE f (topspace top))
                                                ((f o v) y + e % phi y)))
              has_real_derivative &0) (atreal (&0))) /\
     p4_s2_variation (top,atlas) v V
     ==> ((\s. p4_s2_energy atlas g (V s)) has_real_derivative &0) (atreal (&0))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "EMB") (CONJUNCTS_THEN2 (LABEL_TAC "VM")
    (CONJUNCTS_THEN2 (LABEL_TAC "WS") (CONJUNCTS_THEN2 (LABEL_TAC "CRIT")
    (LABEL_TAC "VAR"))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`;
                 `V:real->real^3->A`] CMT_VARIATION_FAMILY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "W1") (CONJUNCTS_THEN2 (LABEL_TAC "W2")
    (LABEL_TAC "W5"))) THEN
  USE_THEN "EMB" (MP_TAC o REWRITE_RULE[cm_emb; cm_target; cm_tube; IN_ELIM_THM]) THEN
  STRIP_TAC THEN
  USE_THEN "VAR" (MP_TAC o REWRITE_RULE[p4_s2_variation]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "V0") (CONJUNCTS_THEN2 (LABEL_TAC "VC") (K
      ALL_TAC)))
    THEN
  ABBREV_TAC `D1 = {x:real^(1,3)finite_sum | drop(fstcart x) IN real_interval(--(&1),&1) /\
                                             ~(sndcart x = vec 0)}` THEN
  SUBGOAL_THEN `open(D1:real^(1,3)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "D1" THEN REWRITE_TAC[CMT_TIME_OPEN]; ALL_TAC] THEN
  ABBREV_TAC
   `W = \x:real^(1,3)finite_sum.
          (f:A->real^K)((V:real->real^3->A) (drop(fstcart x))
                                            (inv(norm(sndcart x)) % sndcart x))` THEN
  SUBGOAL_THEN
   `!x t. x IN D1 /\ &0 < t
          ==> pastecart (fstcart x) (t % sndcart x) IN D1 /\
              (W:real^(1,3)finite_sum->real^K)(pastecart (fstcart x) (t % sndcart x)) = W x`
  (LABEL_TAC "WR") THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "D1" THEN EXPAND_TAC "W" THEN
    REWRITE_TAC[IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ] THEN
    USE_THEN "W2" (MP_TAC o REWRITE_RULE[FSTCART_PASTECART; SNDCART_PASTECART] o
                   SPECL [`x:real^(1,3)finite_sum`; `t:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN D1 ==> (W:real^(1,3)finite_sum->real^K) x IN IMAGE (f:A->real^K) (topspace
       top)`
  (LABEL_TAC "W3") THENL
   [USE_THEN "VC" (ASSUME_TAC o MATCH_MP CMT_VAR_CONT) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; SUBSET; FORALL_IN_IMAGE] THEN
    EXPAND_TAC "W" THEN SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^3. ~(y = vec 0)
               ==> (W:real^(1,3)finite_sum->real^K) (pastecart (lift(&0)) y) =
                   wan_rext ((f:A->real^K) o (v:real^3->A)) y`
  (LABEL_TAC "W4") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "W" THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; wan_rext; o_THM] THEN
    AP_TERM_TAC THEN USE_THEN "V0" MATCH_MP_TAC THEN ASM_SIMP_TAC[P4_RADIAL_SPHERE];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on D1 (W:real^(1,3)finite_sum->real^K)` ASSUME_TAC THENL
   [USE_THEN "W1" ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\s. cm_sen (G:real^K->real^K^K) (\y. (W:real^(1,3)finite_sum->real^K)
                                              (pastecart (lift s) y)))
     has_real_derivative
     drop(integral wan_shell
           (\z. partial_derivative 1 (\x. lift(cmt_psi G (cmt_jet W x)))
                                   (pastecart (lift(&0)) z))) / &3) (atreal (&0))`
  (LABEL_TAC "FW") THENL
   [MATCH_MP_TAC CMT_FIRST_VARIATION THEN EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^(1,3)finite_sum) IN D1` ASSUME_TAC THENL
     [EXPAND_TAC "D1" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "WR" (MP_TAC o SPECL [`x:real^(1,3)finite_sum`; `t:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s IN real_interval(--(&1),&1)
        ==> p4_s2_energy atlas (g:A->real^N^N) ((V:real->real^3->A) s) =
            cm_sen (G:real^K->real^K^K) (\y. (W:real^(1,3)finite_sum->real^K)
                                               (pastecart (lift s) y))`
  (LABEL_TAC "WE") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "W5" (fun th -> ASM_SIMP_TAC[th]) THEN
    MATCH_MP_TAC CMT_SEN_SPHERE_EQ THEN X_GEN_TAC `y:real^3` THEN
    REWRITE_TAC[IN_SPHERE_0] THEN DISCH_TAC THEN EXPAND_TAC "W" THEN
    ASM_REWRITE_TAC[o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; REAL_INV_1;
                    VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `drop(integral wan_shell
           (\z. partial_derivative 1
                  (\x. lift(cmt_psi (G:real^K->real^K^K)
                                    (cmt_jet (W:real^(1,3)finite_sum->real^K) x)))
                  (pastecart (lift(&0)) z))) / &3 = &0`
  (fun th -> USE_THEN "FW" (MP_TAC o REWRITE_RULE[th])) THENL
   [ALL_TAC;
    DISCH_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    MAP_EVERY EXISTS_TAC
     [`\s. cm_sen (G:real^K->real^K^K) (\y. (W:real^(1,3)finite_sum->real^K)
                                              (pastecart (lift s) y))`; `&1`] THEN
    ASM_REWRITE_TAC[REAL_LT_01] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN USE_THEN "WE" MATCH_MP_TAC THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC] THEN
  MATCH_MP_TAC CMT_FV_ZERO THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                        `g:A->real^N^N`; `f:A->real^K`; `d:real`; `v:real^3->A`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    USE_THEN "CRIT" ACCEPT_TAC;
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^(1,3)finite_sum) IN D1` ASSUME_TAC THENL
     [EXPAND_TAC "D1" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "WR" (MP_TAC o SPECL [`x:real^(1,3)finite_sum`; `t:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    REPEAT STRIP_TAC THEN USE_THEN "W3" MATCH_MP_TAC THEN
    EXPAND_TAC "D1" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
    USE_THEN "W4" ACCEPT_TAC]);;

let CM_SHARMONIC_EQ = prove
 (`!top atlas (g:A->real^N^N) (f:A->real^K) (G:real^K->real^K^K) d (v:real^3->A).
     cm_emb (top,atlas) g f G d /\
     (!y. y IN sphere(vec 0,&1) ==> v y IN topspace top)
     ==> (cm_sharmonic (IMAGE f (topspace top)) G (f o v) <=>
          p4_harmonic_sphere (top,atlas) g (topspace top) v)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "EMB") (LABEL_TAC "VM")) THEN
  SUBGOAL_THEN `mfd_embedding (top,atlas:((A->bool)#(A->real^N))->bool) (f:A->real^K)`
  ASSUME_TAC THENL
   [USE_THEN "EMB" (MP_TAC o REWRITE_RULE[cm_emb]) THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN sphere(vec 0,&1)
        ==> ((f:A->real^K) o (v:real^3->A)) y IN IMAGE f (topspace top)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    USE_THEN "VM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext ((f:A->real^K) o (v:real^3->A))) <=>
    p4_s2_smooth (top,atlas:((A->bool)#(A->real^N))->bool) v`
  (LABEL_TAC "SM") THENL
   [EQ_TAC THENL
     [DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
          `g:A->real^N^N`;
                     `f:A->real^K`; `G:real^K->real^K^K`; `d:real`;
                     `(f:A->real^K) o (v:real^3->A)`] CM_EMB_TO_P4) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC CMT_P4_SMOOTH_SPHERE_EQ THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN MATCH_MP_TAC GRGE_EMB_INV_LEFT THEN
      EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_SIMP_TAC[];
      DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
          `g:A->real^N^N`;
                     `f:A->real^K`; `G:real^K->real^K^K`; `d:real`; `v:real^3->A`]
                    CM_P4_TO_EMB) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o CONJUNCT2)];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `f:A->real^K`;
                 `v:real^3->A`] CMT_NONCONST_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[cm_sharmonic; p4_harmonic_sphere] THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `p4_s2_smooth (top,atlas:((A->bool)#(A->real^N))->bool) (v:real^3->A)` THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `smooth_map_on {z:real^3 | ~(z = vec 0)} (wan_rext ((f:A->real^K) o (v:real^3->A)))`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `V:real->real^3->A` THEN DISCH_TAC THEN
    MATCH_MP_TAC CMT_CM_TO_P4_CRIT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `f:A->real^K`; `G:real^K->real^K^K`; `d:real`;
                          `v:real^3->A`] THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN X_GEN_TAC `phi:real^3->real^K` THEN DISCH_TAC THEN
    MATCH_MP_TAC CMT_P4_TO_CM_CRIT THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`; `d:real`]
        THEN
    ASM_REWRITE_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* T8 for sweepouts: a family W with values in f(M) is a p4 sweepout after  *)
(* mfd_emb_inv exactly when its radial extension is C1 on the slab and its  *)
(* end slices are constant.  One way pushes the sweepout forward by f (the  *)
(* lemma P4_SWEEP_PUSH_C1 with the euclidean target atlas), the other        *)
(* composes with the smooth chart expressions of mfd_emb_inv o closest_point *)
(* near f(M) (CMT_RETRACT_SMOOTH).                                           *)
(* ------------------------------------------------------------------------- *)

let CMT_SWEEP_TO_C1 = prove
 (`!top atlas (f:A->real^K) (W:real^3->real->real^K).
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
     mfd_embedding (top,atlas) f /\
     (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]
            ==> W y t IN IMAGE f (topspace top)) /\
     p4_sweepout (top,atlas) (\y t. mfd_emb_inv top f (W y t))
     ==> continuously_differentiable 1
           {x:real^(3,1)finite_sum |
              ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1]}
           (\x. W (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "WIN") ASSUME_TAC))) THEN
  SUBGOAL_THEN
   `!x:real^(3,1)finite_sum.
      ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1]
      ==> (W:real^3->real->real^K) (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x)) IN
          IMAGE (f:A->real^K) (topspace top)`
  (LABEL_TAC "WN") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "WIN" MATCH_MP_TAC THEN ASM_SIMP_TAC[P4_RADIAL_SPHERE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `continuous_map (top,subtopology euclidean (:real^K)) (f:A->real^K)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBTOPOLOGY_UNIV] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT2 o REWRITE_RULE[mfd_embedding]) THEN
    DISCH_THEN(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP) THEN
    SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_smooth_map (atlas:((A->bool)#(A->real^N))->bool) (open_set_atlas (:real^K))
                   (topspace top) (f:A->real^K)`
  ASSUME_TAC THENL
   [REWRITE_TAC[MFD_SMOOTH_MAP_INTO_EUCLIDEAN; mfd_smooth_on] THEN
    X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `f:A->real^K`; `c:(A->bool)#(A->real^N)`] GRGE_IMMERSION_CHART) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[mfd_embedding]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]
          ==> mfd_emb_inv top (f:A->real^K) ((W:real^3->real->real^K) y t) IN topspace top`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `f:A->real^K`; `(W:real^3->real->real^K) y t`]
                  CMT_EMB_INV_RIGHT) THEN
    ANTS_TAC THENL [USE_THEN "WIN" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `((:real^K),(\x:real^K. x)) IN open_set_atlas (:real^K)` ASSUME_TAC THENL
   [REWRITE_TAC[open_set_atlas; IN_SING]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `subtopology euclidean (:real^K)`; `open_set_atlas (:real^K)`;
                 `topspace top:A->bool`; `f:A->real^K`;
                 `\y t. mfd_emb_inv top (f:A->real^K) ((W:real^3->real->real^K) y t)`;
                 `((:real^K),(\x:real^K. x))`] P4_SWEEP_PUSH_C1) THEN
  ASM_SIMP_TAC[OPEN_SET_ATLAS; OPEN_UNIV; OPEN_IN_TOPSPACE; SUBTOPOLOGY_TOPSPACE] THEN
  REWRITE_TAC[IN_UNIV; FST; SND] THEN DISCH_TAC THEN
  MATCH_MP_TAC P4_C1_EQ_WITHIN THEN
  EXISTS_TAC `\x. (f:A->real^K) (mfd_emb_inv top f
                    ((W:real^3->real->real^K) (inv(norm(fstcart x)) % fstcart x)
                                              (drop(sndcart x))))` THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `f:A->real^K`;
                 `(W:real^3->real->real^K) (inv(norm(fstcart (x:real^(3,1)finite_sum))) %
                                            fstcart x) (drop(sndcart x))`]
                CMT_EMB_INV_RIGHT) THEN
  ANTS_TAC THENL [USE_THEN "WN" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; SIMP_TAC[]]);;

let CMT_C1_TO_SWEEP = prove
 (`!top atlas (f:A->real^K) (W:real^3->real->real^K).
     hausdorff_space top /\
     smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
     compact_space top /\ mfd_embedding (top,atlas) f /\
     (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]
            ==> W y t IN IMAGE f (topspace top)) /\
     continuously_differentiable 1
       {x:real^(3,1)finite_sum |
          ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1]}
       (\x. W (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x)))
     ==> continuous_map
           (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                          (subtopology euclideanreal (real_interval[&0,&1])),top)
           (\(y,t). mfd_emb_inv top f (W y t)) /\
         (!c. c IN atlas
              ==> continuously_differentiable 1
                    {x:real^(3,1)finite_sum |
                       ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1] /\
                       mfd_emb_inv top f (W (inv(norm(fstcart x)) % fstcart x)
                                            (drop(sndcart x))) IN FST c}
                    (\x. SND c (mfd_emb_inv top f (W (inv(norm(fstcart x)) % fstcart x)
                                                     (drop(sndcart x))))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "WIN") (LABEL_TAC "C1")))))) THEN
  SUBGOAL_THEN
   `!x:real^(3,1)finite_sum.
      ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1]
      ==> (W:real^3->real->real^K) (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x)) IN
          IMAGE (f:A->real^K) (topspace top)`
  (LABEL_TAC "WN") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "WIN" MATCH_MP_TAC THEN ASM_SIMP_TAC[P4_RADIAL_SPHERE];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `(\(y,t). mfd_emb_inv top (f:A->real^K) ((W:real^3->real->real^K) y t)) =
      mfd_emb_inv top f o (\x:real^3#real. W (FST x) (SND x))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean (IMAGE (f:A->real^K) (topspace top))` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC CMT_EMB_INV_CONTINUOUS THEN
      EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PAIR_THM; TOPSPACE_PROD_TOPOLOGY;
          IN_CROSS;
                  TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY;
                  FST; SND] THEN
      REPEAT STRIP_TAC THEN USE_THEN "WIN" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
    EXISTS_TAC `(\x. (W:real^3->real->real^K) (inv(norm(fstcart x)) % fstcart x)
                                              (drop(sndcart x))) o
                (\x:real^3#real. pastecart (FST x) (lift(SND x)))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FORALL_PAIR_THM; TOPSPACE_PROD_TOPOLOGY; IN_CROSS; FST; SND;
                  TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; o_THM;
                  FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; IN_SPHERE_0] THEN
      SIMP_TAC[REAL_INV_1; VECTOR_MUL_LID];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean
                  {x:real^(3,1)finite_sum | ~(fstcart x = vec 0) /\
                                            drop(sndcart x) IN real_interval[&0,&1]}` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN] THEN
      MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
      EXISTS_TAC `1` THEN USE_THEN "C1" ACCEPT_TAC] THEN
    REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; CONTINUOUS_MAP_PASTED] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^3,&1))`;
                     `subtopology euclideanreal (real_interval[&0,&1])`]
                         CONTINUOUS_MAP_FST) THEN
      SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; ETA_AX];
      SUBGOAL_THEN `(\x:real^3#real. lift(SND x)) = lift o SND` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      REWRITE_TAC[GSYM CONTINUOUS_MAP_EQ_LIFT] THEN
      MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^3,&1))`;
                     `subtopology euclideanreal (real_interval[&0,&1])`]
                         CONTINUOUS_MAP_SND) THEN
      SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PAIR_THM; TOPSPACE_PROD_TOPOLOGY;
          IN_CROSS;
                  TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY;
                  IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; FST; SND]
                      THEN
      SIMP_TAC[P4_SPHERE_NONZERO]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `f:A->real^K`]
                CMT_RETRACT_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "RS"))) THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  USE_THEN "RS" (MP_TAC o C MATCH_MP (ASSUME `(c:(A->bool)#(A->real^N)) IN atlas`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  MATCH_MP_TAC P4_C1_EQ_WITHIN THEN
  EXISTS_TAC
   `(\z. SND (c:(A->bool)#(A->real^N))
           (mfd_emb_inv top (f:A->real^K) (closest_point (IMAGE f (topspace top)) z))) o
    (\x:real^(3,1)finite_sum. (W:real^3->real->real^K) (inv(norm(fstcart x)) % fstcart x)
                                                      (drop(sndcart x)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; o_THM] THEN REPEAT STRIP_TAC THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC CLOSEST_POINT_SELF THEN
    USE_THEN "WN" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC P4_C1_COMPOSE_WITHIN THEN
  EXISTS_TAC
   `{z | (?p. p IN IMAGE (f:A->real^K) (topspace top) /\ dist(z,p) < d1) /\
         mfd_emb_inv top f (closest_point (IMAGE f (topspace top)) z) IN
         FST (c:(A->bool)#(A->real^N))}` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN
    EXISTS_TAC `{x:real^(3,1)finite_sum | ~(fstcart x = vec 0) /\
                                          drop(sndcart x) IN real_interval[&0,&1]}` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^(3,1)finite_sum` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(W:real^3->real->real^K) (inv(norm(fstcart (x:real^(3,1)finite_sum))) % fstcart x)
                               (drop(sndcart x)) IN IMAGE (f:A->real^K) (topspace top)`
    ASSUME_TAC THENL [USE_THEN "WN" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[CLOSEST_POINT_SELF] THEN
    EXISTS_TAC `(W:real^3->real->real^K) (inv(norm(fstcart (x:real^(3,1)finite_sum))) %
                                          fstcart x) (drop(sndcart x))` THEN
    ASM_REWRITE_TAC[DIST_REFL]]);;

let CM_SWEEP_EQ = prove
 (`!top atlas (g:A->real^N^N) (f:A->real^K) (G:real^K->real^K^K) d
   (W:real^3->real->real^K).
     cm_emb (top,atlas) g f G d /\
     (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]
            ==> W y t IN IMAGE f (topspace top))
     ==> (p4_sweepout (top,atlas) (\y t. mfd_emb_inv top f (W y t)) <=>
          continuously_differentiable 1
            {x:real^(3,1)finite_sum |
               ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1]}
            (\x. W (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x))) /\
          (!y y'. y IN sphere(vec 0,&1) /\ y' IN sphere(vec 0,&1)
                  ==> W y (&0) = W y' (&0) /\ W y (&1) = W y' (&1)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "EMB") (LABEL_TAC "WIN")) THEN
  USE_THEN "EMB" (MP_TAC o REWRITE_RULE[cm_emb]) THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]
          ==> (f:A->real^K) (mfd_emb_inv top f ((W:real^3->real->real^K) y t)) = W y t`
  (LABEL_TAC "FI") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `f:A->real^K`; `(W:real^3->real->real^K) y t`]
                  CMT_EMB_INV_RIGHT) THEN
    ANTS_TAC THENL [USE_THEN "WIN" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 IN real_interval[&0,&1] /\ &1 IN real_interval[&0,&1]`
  STRIP_ASSUME_TAC THENL [REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!y y'. y IN sphere(vec 0,&1) /\ y' IN sphere(vec 0,&1)
            ==> mfd_emb_inv top (f:A->real^K) ((W:real^3->real->real^K) y (&0)) =
                mfd_emb_inv top f (W y' (&0)) /\
                mfd_emb_inv top f (W y (&1)) = mfd_emb_inv top f (W y' (&1))) <=>
    (!y y'. y IN sphere(vec 0,&1) /\ y' IN sphere(vec 0,&1)
            ==> W y (&0) = W y' (&0) /\ W y (&1) = W y' (&1))`
  (LABEL_TAC "ENDS") THENL
   [EQ_TAC THEN DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`y:real^3`; `y':real^3`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^3`; `y':real^3`]) THEN
    ASM_REWRITE_TAC[] THENL
     [DISCH_THEN(CONJUNCTS_THEN (MP_TAC o AP_TERM `f:A->real^K`)) THEN ASM_SIMP_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[p4_sweepout] THEN USE_THEN "ENDS" (fun th -> REWRITE_TAC[th]) THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC CMT_SWEEP_TO_C1 THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `f:A->real^K`] THEN
    ASM_REWRITE_TAC[p4_sweepout];
    MATCH_MP_TAC CMT_C1_TO_SWEEP THEN ASM_REWRITE_TAC[]]);;

