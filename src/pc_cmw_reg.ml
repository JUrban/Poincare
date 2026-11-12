(* ========================================================================= *)
(* Unit pc_cmw_reg: CMW_REG_STATEMENT (pc_cmw_defs): area at most energy for *)
(* C^0 /\ W^{1,2} slices, and CM Lemma D.1 (a C^0 /\ W^{1,2} sweepout is     *)
(* close to a jointly C^1 one in C^0, energy, area and trace).               *)
(*                                                                           *)
(* Integrands of quadratic growth.  A density FF p a that is                 *)
(* continuous and 2-homogeneous in a has a quadratic modulus of continuity  *)
(* on compact sets of p; hence its integral is continuous along maps that   *)
(* converge uniformly with derivatives converging in L^2.                    *)
(* ========================================================================= *)

needs "src/pc_cmw_defs.ml";;
needs "src/pc_cmw_pos.ml";;
needs "src/pc_an_beltrami.ml";;
needs "src/pc_wan_moll.ml";;
needs "src/pc_wan_sob2v.ml";;

prioritize_real();;
type_invention_error := true;;

let CMW_HOMOG_BOUND = prove
 (`!(FF:real^M->real^N->real) k.
        compact k /\
        (\x. lift(FF (fstcart x) (sndcart x))) continuous_on (:real^(M,N)finite_sum) /\
        (!p a c. &0 < c ==> FF p (c % a) = c pow 2 * FF p a) /\
        (!p. FF p (vec 0) = &0)
        ==> ?M. &0 <= M /\ !p a. p IN k ==> abs(FF p a) <= M * norm a pow 2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "hom") ASSUME_TAC))) THEN
  SUBGOAL_THEN
   `compact (IMAGE (\x:real^(M,N)finite_sum. lift((FF:real^M->real^N->real) (fstcart x) (sndcart x)))
                   ((k:real^M->bool) PCROSS sphere(vec 0:real^N,&1)))`
  MP_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[COMPACT_PCROSS; COMPACT_SPHERE] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^(M,N)finite_sum)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; FORALL_IN_PCROSS; FSTCART_PASTECART;
              SNDCART_PASTECART; NORM_LIFT] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `B:real` THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  MAP_EVERY X_GEN_TAC [`p:real^M`; `a:real^N`] THEN DISCH_TAC THEN
  ASM_CASES_TAC `a:real^N = vec 0` THENL
   [ASM_REWRITE_TAC[NORM_0; REAL_ABS_0] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(a:real^N)` ASSUME_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(FF:real^M->real^N->real) p a = norm(a:real^N) pow 2 * FF p (inv(norm a) % a)`
  SUBST1_TAC THENL
   [USE_THEN "hom" (MP_TAC o C MP (ASSUME `&0 < norm(a:real^N)`) o
                     SPECL [`p:real^M`; `inv(norm(a:real^N)) % a`; `norm(a:real^N)`]) THEN
    SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; NORM_EQ_0; ASSUME `~(a:real^N = vec 0)`;
             VECTOR_MUL_LID];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW; REAL_ABS_NORM] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[REAL_LE_POW_2] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ]);;

let CMW_HOMOG_MODULUS = prove
 (`!(FF:real^M->real^N->real) k.
        compact k /\
        (\x. lift(FF (fstcart x) (sndcart x))) continuous_on (:real^(M,N)finite_sum) /\
        (!p a c. &0 < c ==> FF p (c % a) = c pow 2 * FF p a) /\
        (!p. FF p (vec 0) = &0)
        ==> !e. &0 < e
                ==> ?d C. &0 < d /\ &0 <= C /\
                          !p p' a b. p IN k /\ p' IN k /\ norm(p - p') < d
                                     ==> abs(FF p a - FF p' b)
                                         <= e * (norm a pow 2 + norm b pow 2) +
                                            C * norm(a - b) pow 2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC o MATCH_MP CMW_HOMOG_BOUND) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "hom") ASSUME_TAC))) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\x:real^(M,N)finite_sum. lift((FF:real^M->real^N->real) (fstcart x) (sndcart x))`;
                 `(k:real^M->bool) PCROSS cball(vec 0:real^N,&1)`]
                COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_PCROSS; COMPACT_CBALL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^(M,N)finite_sum)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[uniformly_continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "uc"))) THEN
  MAP_EVERY EXISTS_TAC [`dd / &2`; `&8 * M / dd pow 2`] THEN
  ASM_SIMP_TAC[REAL_HALF; REAL_LE_DIV; REAL_LE_MUL; REAL_POS; REAL_LE_POW_2] THEN
  MAP_EVERY X_GEN_TAC [`p:real^M`; `p':real^M`; `a:real^N`; `b:real^N`] THEN STRIP_TAC THEN
  ABBREV_TAC `r = max (norm(a:real^N)) (norm(b:real^N))` THEN
  ASM_CASES_TAC `r = &0` THENL
   [SUBGOAL_THEN `a:real^N = vec 0 /\ b:real^N = vec 0` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM NORM_EQ_0] THEN
      MP_TAC(ISPEC `a:real^N` NORM_POS_LE) THEN MP_TAC(ISPEC `b:real^N` NORM_POS_LE) THEN
      ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[NORM_0; VECTOR_SUB_REFL; REAL_SUB_REFL; REAL_ABS_0] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
   [MP_TAC(ISPEC `a:real^N` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(FF:real^M->real^N->real) p a = r pow 2 * FF p (inv r % a) /\
    (FF:real^M->real^N->real) p' b = r pow 2 * FF p' (inv r % b)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THENL
     [USE_THEN "hom" (MP_TAC o C MP (ASSUME `&0 < r`) o
                       SPECL [`p:real^M`; `inv r % (a:real^N)`; `r:real`]);
      USE_THEN "hom" (MP_TAC o C MP (ASSUME `&0 < r`) o
                       SPECL [`p':real^M`; `inv r % (b:real^N)`; `r:real`])] THEN
    SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; ASSUME `~(r = &0)`; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv r % a IN cball(vec 0:real^N,&1) /\ inv r % b IN cball(vec 0:real^N,&1)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_CBALL_0; NORM_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN
    EXPAND_TAC "r" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `r pow 2 <= norm(a:real^N) pow 2 + norm(b:real^N) pow 2` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN
    REWRITE_TAC[REAL_LE_ADDL; REAL_LE_ADDR; REAL_LE_POW_2];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; REAL_ABS_MUL; REAL_ABS_POW] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`] THEN
  ASM_CASES_TAC `norm(inv r % a - inv r % b:real^N) < dd / &2` THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= e * y /\ &0 <= z ==> x <= e * y + z`) THEN CONJ_TAC THENL
     [ALL_TAC;
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_DIV; REAL_POS; REAL_LE_POW_2; REAL_LT_IMP_LE]] THEN
    TRANS_TAC REAL_LE_TRANS `r pow 2 * e` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN
      USE_THEN "uc" (MP_TAC o SPECL [`pastecart (p':real^M) (inv r % b:real^N)`;
                                     `pastecart (p:real^M) (inv r % a:real^N)`]) THEN
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; DIST_LIFT] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[PASTECART_IN_PCROSS] THEN
      REWRITE_TAC[dist; PASTECART_SUB] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `norm(p - p':real^M) + norm(inv r % a - inv r % b:real^N)` THEN
      REWRITE_TAC[NORM_PASTECART_LE] THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `dd / &2 * r <= norm(a - b:real^N)` ASSUME_TAC THENL
   [SUBGOAL_THEN `a - b:real^N = r % (inv r % a - inv r % b)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[GSYM VECTOR_SUB_LDISTRIB; VECTOR_MUL_ASSOC; REAL_MUL_RINV;
                   REAL_LT_IMP_NZ; VECTOR_MUL_LID];
      REWRITE_TAC[NORM_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`] THEN
      GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= y /\ x <= z ==> x <= y + z`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `r pow 2 * (&2 * M)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC(REAL_ARITH `abs x <= M /\ abs y <= M ==> abs(x - y) <= &2 * M`) THEN
    SUBGOAL_THEN
     `!q c:real^N. q IN k /\ c IN cball(vec 0,&1) ==> abs((FF:real^M->real^N->real) q c) <= M`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN TRANS_TAC REAL_LE_TRANS `M * norm(c:real^N) pow 2` THEN
      CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_1_LE THEN REWRITE_TAC[NORM_POS_LE] THEN
      ASM_MESON_TAC[IN_CBALL_0];
      ALL_TAC] THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < dd pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(dd / &2 * r) pow 2 <= norm(a - b:real^N) pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_HALF];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_MUL; REAL_POW_DIV] THEN DISCH_TAC THEN
  SUBGOAL_THEN `r pow 2 * (&2 * M) = (&8 * M / dd pow 2) * ((dd pow 2 / &2 pow 2) * r pow 2)`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < dd pow 2` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_MUL; REAL_POS;
                                              REAL_LT_IMP_LE]);;

let CMW_FUNC_INTEGRABLE = prove
 (`!(FF:real^K->real^N->real) k s (w:real^M->real^K) (a:real^M->real^N).
        compact k /\
        (\x. lift(FF (fstcart x) (sndcart x))) continuous_on (:real^(K,N)finite_sum) /\
        (!p a c. &0 < c ==> FF p (c % a) = c pow 2 * FF p a) /\
        (!p. FF p (vec 0) = &0) /\
        lebesgue_measurable s /\ w measurable_on s /\ (!z. z IN s ==> w z IN k) /\
        a IN lspace s (&2)
        ==> (\z. lift(FF (w z) (a z))) measurable_on s /\
            (\z. lift(FF (w z) (a z))) absolutely_integrable_on s /\
            (\z. lift(FF (w z) (a z))) integrable_on s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`FF:real^K->real^N->real`; `k:real^K->bool`] CMW_HOMOG_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(\z. lift((FF:real^K->real^N->real) ((w:real^M->real^K) z) ((a:real^M->real^N) z)))
                measurable_on s` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\x:real^(K,N)finite_sum. lift((FF:real^K->real^N->real) (fstcart x) (sndcart x))`;
                   `\z. pastecart ((w:real^M->real^K) z) ((a:real^M->real^N) z)`; `s:real^M->bool`]
                  CMW_MEASURABLE_COMPOSE_CONT) THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MEASURABLE_ON_PASTECART THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(a:real^M->real^N) IN lspace s (&2)` THEN SIMP_TAC[lspace; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z. lift(M * norm((a:real^M->real^N) z) pow 2)) integrable_on s` ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
    MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN s ==> norm(lift((FF:real^K->real^N->real) ((w:real^M->real^K) z) ((a:real^M->real^N) z)))
                               <= drop(lift(M * norm(a z) pow 2))` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_LIFT; LIFT_DROP] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE;
    MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE] THEN
  EXISTS_TAC `\z. lift(M * norm((a:real^M->real^N) z) pow 2)` THEN ASM_REWRITE_TAC[]);;

let CMW_SQNORM_BOUND = prove
 (`!x y:real^N. norm x pow 2 <= &2 * norm y pow 2 + &2 * norm(x - y) pow 2`,
  REPEAT GEN_TAC THEN
  TRANS_TAC REAL_LE_TRANS `(norm(y:real^N) + norm(x - y:real^N)) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE; NORM_TRIANGLE_SUB];
    MP_TAC(SPEC `norm(y:real^N) - norm(x - y:real^N)` REAL_LE_POW_2) THEN REAL_ARITH_TAC]);;

let CMW_FUNC_CONV = prove
 (`!(FF:real^K->real^N->real) k s (vn:num->real^M->real^K) v (an:num->real^M->real^N) a.
        compact k /\
        (\x. lift(FF (fstcart x) (sndcart x))) continuous_on (:real^(K,N)finite_sum) /\
        (!p a c. &0 < c ==> FF p (c % a) = c pow 2 * FF p a) /\
        (!p. FF p (vec 0) = &0) /\
        lebesgue_measurable s /\
        (!n. vn n measurable_on s) /\ v measurable_on s /\
        (!n z. z IN s ==> vn n z IN k) /\ (!z. z IN s ==> v z IN k) /\
        (!e. &0 < e
             ==> eventually (\n. !z. z IN s ==> norm(vn n z - v z) < e) sequentially) /\
        (!n. an n IN lspace s (&2)) /\ a IN lspace s (&2) /\
        ((\n. drop(integral s (\z. lift(norm(an n z - a z) pow 2)))) ---> &0) sequentially
        ==> ((\n. drop(integral s (\z. lift(FF (vn n z) (an n z))))) --->
             drop(integral s (\z. lift(FF (v z) (a z))))) sequentially`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "unif")
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "l2"))))))))))))) THEN
  SUBGOAL_THEN
   `!n. (\z. lift((FF:real^K->real^N->real) ((vn:num->real^M->real^K) n z)
                    ((an:num->real^M->real^N) n z))) integrable_on s`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`FF:real^K->real^N->real`; `k:real^K->bool`; `s:real^M->bool`;
                   `(vn:num->real^M->real^K) n`; `(an:num->real^M->real^N) n`]
                  CMW_FUNC_INTEGRABLE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. lift((FF:real^K->real^N->real) ((v:real^M->real^K) z) ((a:real^M->real^N) z)))
    integrable_on s`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`FF:real^K->real^N->real`; `k:real^K->bool`; `s:real^M->bool`;
                   `v:real^M->real^K`; `a:real^M->real^N`] CMW_FUNC_INTEGRABLE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!n. (\z. lift(norm((an:num->real^M->real^N) n z) pow 2)) integrable_on s) /\
    (\z. lift(norm((a:real^M->real^N) z) pow 2)) integrable_on s /\
    (!n. (\z. lift(norm((an:num->real^M->real^N) n z - a z) pow 2)) integrable_on s)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY GEN_TAC THEN MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN
    ASM_SIMP_TAC[LSPACE_SUB; REAL_POS; ETA_AX];
    ALL_TAC] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  ABBREV_TAC `I0 = drop(integral s (\z. lift(norm((a:real^M->real^N) z) pow 2)))` THEN
  SUBGOAL_THEN `&0 <= I0` ASSUME_TAC THENL
   [EXPAND_TAC "I0" THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
    ASM_REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`FF:real^K->real^N->real`; `k:real^K->bool`] CMW_HOMOG_MODULUS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `e / (&2 * (&3 * I0 + &3))`) THEN
  ANTS_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `eps = e / (&2 * (&3 * I0 + &3))` THEN
  SUBGOAL_THEN `&0 < eps` ASSUME_TAC THENL
   [EXPAND_TAC "eps" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "unif" (MP_TAC o C MP (ASSUME `&0 < d`) o SPEC `d:real`) THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "n1")) THEN
  USE_THEN "l2" (MP_TAC o SPEC `min (&1) (e / (&2 * (C + &1)))` o
                 REWRITE_RULE[REALLIM_SEQUENTIALLY]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN; REAL_LT_01] THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "n2")) THEN
  EXISTS_TAC `N1 + N2:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  USE_THEN "n1" (MP_TAC o SPEC `n:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  USE_THEN "n2" (MP_TAC o SPEC `n:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[REAL_SUB_RZERO]] THEN
  ABBREV_TAC `Dn = drop(integral s (\z. lift(norm((an:num->real^M->real^N) n z - a z) pow 2)))` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= Dn` ASSUME_TAC THENL
   [EXPAND_TAC "Dn" THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
    ASM_REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2];
    ALL_TAC] THEN
  ABBREV_TAC `Bn = drop(integral s (\z. lift(norm((an:num->real^M->real^N) n z) pow 2)))` THEN
  SUBGOAL_THEN `Bn <= &2 * I0 + &2 * Dn` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Bn"; "I0"; "Dn"] THEN
    SUBGOAL_THEN
     `&2 * drop(integral s (\z. lift(norm((a:real^M->real^N) z) pow 2))) +
      &2 * drop(integral s (\z. lift(norm((an:num->real^M->real^N) n z - a z) pow 2))) =
      drop(integral s (\z. &2 % lift(norm(a z) pow 2) +
                           &2 % lift(norm((an:num->real^M->real^N) n z - a z) pow 2)))`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[INTEGRAL_ADD; INTEGRABLE_CMUL; INTEGRAL_CMUL; DROP_ADD; DROP_CMUL];
      ALL_TAC] THEN
    MATCH_MP_TAC INTEGRAL_DROP_LE THEN
    ASM_SIMP_TAC[INTEGRABLE_ADD; INTEGRABLE_CMUL; DROP_ADD; DROP_CMUL; LIFT_DROP] THEN
    REWRITE_TAC[CMW_SQNORM_BOUND];
    ALL_TAC] THEN
  ABBREV_TAC
   `g = \z. eps % (lift(norm((an:num->real^M->real^N) n z) pow 2) +
                   lift(norm((a:real^M->real^N) z) pow 2)) +
            C % lift(norm(an n z - a z) pow 2)` THEN
  SUBGOAL_THEN `(g:real^M->real^1) integrable_on s` ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN ASM_SIMP_TAC[INTEGRABLE_ADD; INTEGRABLE_CMUL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(drop(integral s (\z. lift((FF:real^K->real^N->real) ((vn:num->real^M->real^K) n z)
                                  ((an:num->real^M->real^N) n z)))) -
        drop(integral s (\z. lift(FF ((v:real^M->real^K) z) ((a:real^M->real^N) z)))))
    <= drop(integral s g)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM DROP_SUB; GSYM INTEGRAL_SUB] THEN
    REWRITE_TAC[GSYM NORM_1] THEN MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
    ASM_SIMP_TAC[INTEGRABLE_SUB] THEN X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN
    EXPAND_TAC "g" THEN
    REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT; DROP_ADD; DROP_CMUL; LIFT_DROP] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `C:real`)) (concl th) &&
                                                  is_forall(concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `drop(integral s (g:real^M->real^1)) = eps * (Bn + I0) + C * Dn` ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN
    ASM_SIMP_TAC[INTEGRABLE_ADD; INTEGRABLE_CMUL; INTEGRAL_ADD; INTEGRAL_CMUL; DROP_ADD;
                 DROP_CMUL] THEN
    MAP_EVERY EXPAND_TAC ["Bn"; "I0"; "Dn"] THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `drop(integral s (g:real^M->real^1))` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `eps * (&3 * I0 + &3) = e / &2` ASSUME_TAC THENL
   [EXPAND_TAC "eps" THEN UNDISCH_TAC `&0 <= I0` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `C * Dn <= C * (e / (&2 * (C + &1)))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `C * (e / (&2 * (C + &1))) < e / &2` ASSUME_TAC THENL
   [SUBGOAL_THEN `C * (e / (&2 * (C + &1))) = (e / &2) * (C / (C + &1))` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 <= C` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 <= C ==> &0 < C + &1`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `eps * (Bn + I0) <= eps * (&3 * I0 + &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `eps * (&3 * I0 + &2) < e / &2` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> can (find_term ((=) `e / &2`)) (concl th) &&
                                                     is_eq(concl th))) THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The energy, area and trace densities of a triple of                       *)
(* partials, their continuity and homogeneity.                               *)
(* ========================================================================= *)

let cmw_c3 = new_definition
 `cmw_c3 (x:real^(K,(K,K)finite_sum)finite_sum) (i:num) =
    if i = 1 then fstcart x else if i = 2 then fstcart(sndcart x) else sndcart(sndcart x)`;;

let cmw_jx = new_definition
 `cmw_jx (x:real^(K,(K,K)finite_sum)finite_sum) = (lambda k i. cmw_c3 x i$k):real^3^K`;;

let cmw_pk = new_definition
 `cmw_pk (s:real^3->bool) (v:real^3->real^K) (z:real^3) =
    pastecart (wan_wd s 1 v z) (pastecart (wan_wd s 2 v z) (wan_wd s 3 v z))`;;

let cmw_edens = new_definition
 `cmw_edens (G:real^K->real^K^K) (i:num) (p:real^K) (x:real^(K,(K,K)finite_sum)finite_sum) =
    cmw_c3 x i dot (G p ** cmw_c3 x i)`;;

let cmw_adens = new_definition
 `cmw_adens (G:real^K->real^K^K) (p:real^K) (x:real^(K,(K,K)finite_sum)finite_sum) =
    sqrt(p4_e2(transp(cmw_jx x) ** G p ** cmw_jx x))`;;

let cmw_tdens = new_definition
 `cmw_tdens (G:real^K->real^K^K) (Q:real^K->real^K^K) (p:real^K)
            (x:real^(K,(K,K)finite_sum)finite_sum) =
    if p4_e2(transp(cmw_jx x) ** G p ** cmw_jx x) = &0 then &0
    else p4_e2_pol (transp(cmw_jx x) ** G p ** cmw_jx x) (transp(cmw_jx x) ** Q p ** cmw_jx x) /
         sqrt(p4_e2(transp(cmw_jx x) ** G p ** cmw_jx x))`;;

let CMW_JX_COL = prove
 (`!(x:real^(K,(K,K)finite_sum)finite_sum) i.
        1 <= i /\ i <= 3 ==> cmw_jx x ** basis i = cmw_c3 x i`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_BASIS; DIMINDEX_3; column; cmw_jx; CART_EQ; LAMBDA_BETA]);;

let CMW_GRAM_JX = prove
 (`!(x:real^(K,(K,K)finite_sum)finite_sum) (A:real^K^K) i j.
        1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
        ==> (transp(cmw_jx x) ** A ** cmw_jx x)$i$j = cmw_c3 x i dot (A ** cmw_c3 x j)`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) CMT_GRAM_ENTRY o lhand o snd) THEN
  ASM_SIMP_TAC[DIMINDEX_3; CMW_JX_COL]);;

let CMW_C3_PK = prove
 (`!s (v:real^3->real^K) z i.
        1 <= i /\ i <= 3 ==> cmw_c3 (cmw_pk s v z) i = wan_wd s i v z`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `1 <= i /\ i <= 3 <=> i = 1 \/ i = 2 \/ i = 3`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[cmw_c3; cmw_pk; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let CMW_WGRAM_PK = prove
 (`!s (G:real^K->real^K^K) (v:real^3->real^K) z.
        cm_wgram s G v z = transp(cmw_jx (cmw_pk s v z)) ** G(v z) ** cmw_jx (cmw_pk s v z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cm_wgram; CART_EQ; DIMINDEX_3] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LAMBDA_BETA; DIMINDEX_3; CMW_GRAM_JX; CMW_C3_PK]);;

let CMW_C3_CMUL = prove
 (`!c (x:real^(K,(K,K)finite_sum)finite_sum) i. cmw_c3 (c % x) i = c % cmw_c3 x i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmw_c3] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[FSTCART_CMUL; SNDCART_CMUL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[FSTCART_CMUL; SNDCART_CMUL]);;

let CMW_JX_CMUL = prove
 (`!c (x:real^(K,(K,K)finite_sum)finite_sum). cmw_jx (c % x) = c %% cmw_jx x`,
  SIMP_TAC[cmw_jx; CART_EQ; LAMBDA_BETA; MATRIX_CMUL_COMPONENT; CMW_C3_CMUL;
           VECTOR_MUL_COMPONENT]);;

let CMW_GRAM_CMUL = prove
 (`!c (x:real^(K,(K,K)finite_sum)finite_sum) (A:real^K^K).
        transp(cmw_jx (c % x)) ** A ** cmw_jx (c % x) =
        (c pow 2) %% (transp(cmw_jx x) ** A ** cmw_jx x)`,
  REWRITE_TAC[CMW_JX_CMUL; TRANSP_MATRIX_CMUL; MATRIX_MUL_LMUL; MATRIX_MUL_RMUL;
              MATRIX_CMUL_ASSOC; REAL_POW_2]);;

let CMW_NORM_PASTECART_POW2 = prove
 (`!(x:real^M) (y:real^N). norm(pastecart x y) pow 2 = norm x pow 2 + norm y pow 2`,
  SIMP_TAC[NORM_PASTECART; SQRT_POW_2; REAL_LE_ADD; REAL_LE_POW_2]);;

let CMW_C3_NORM = prove
 (`!x:real^(K,(K,K)finite_sum)finite_sum.
        norm x pow 2 = sum(1..3) (\i. norm(cmw_c3 x i) pow 2)`,
  GEN_TAC THEN REWRITE_TAC[SUM_3; cmw_c3; ARITH] THEN
  SUBGOAL_THEN `norm(x:real^(K,(K,K)finite_sum)finite_sum) pow 2 =
                norm(pastecart (fstcart x) (sndcart x)) pow 2` SUBST1_TAC THENL
   [REWRITE_TAC[PASTECART_FST_SND]; ALL_TAC] THEN
  REWRITE_TAC[CMW_NORM_PASTECART_POW2] THEN
  SUBGOAL_THEN `norm(sndcart(x:real^(K,(K,K)finite_sum)finite_sum)) pow 2 =
                norm(pastecart (fstcart(sndcart x)) (sndcart(sndcart x))) pow 2` SUBST1_TAC THENL
   [REWRITE_TAC[PASTECART_FST_SND]; ALL_TAC] THEN
  REWRITE_TAC[CMW_NORM_PASTECART_POW2; REAL_ADD_ASSOC]);;

(* Continuity of the densities in (p,x).                                     *)

let CMW_C3_LINEAR = prove
 (`!i. linear (\x:real^(K,(K,K)finite_sum)finite_sum. cmw_c3 x i)`,
  GEN_TAC THEN REWRITE_TAC[cmw_c3] THEN
  ASM_CASES_TAC `i = 1` THEN ASM_REWRITE_TAC[LINEAR_FSTCART] THEN
  ASM_CASES_TAC `i = 2` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[linear; FSTCART_ADD; SNDCART_ADD; FSTCART_CMUL; SNDCART_CMUL]);;

let CMW_C3_SND_CONT = prove
 (`!i s. (\x:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum. cmw_c3 (sndcart x) i)
         continuous_on s`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
  MP_TAC(ISPECL [`sndcart:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum->real^(K,(K,K)finite_sum)finite_sum`;
                 `\x:real^(K,(K,K)finite_sum)finite_sum. cmw_c3 x i`] LINEAR_COMPOSE) THEN
  REWRITE_TAC[LINEAR_SNDCART; CMW_C3_LINEAR; o_DEF]);;

let CMW_GRAM_ENTRY_CONT = prove
 (`!(A:real^K->real^K^K) s.
        (vectorize o A) continuous_on (:real^K)
        ==> !i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
                  ==> (\x:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum.
                         lift((transp(cmw_jx (sndcart x)) ** A (fstcart x) **
                               cmw_jx (sndcart x))$i$j)) continuous_on s`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CMW_GRAM_JX] THEN
  MP_TAC(ISPECL [`s:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum->bool`;
                 `A:real^K->real^K^K`;
                 `fstcart:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum->real^K`;
                 `\x:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum. cmw_c3 (sndcart x) i`;
                 `\x:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum. cmw_c3 (sndcart x) j`]
                CMT_CONT_QUAD) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[CMW_C3_SND_CONT] THEN
  MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_FSTCART]);;

let CMW_EDENS_FACTS = prove
 (`!(G:real^K->real^K^K) i.
        (vectorize o G) continuous_on (:real^K)
        ==> (\x:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum.
                lift(cmw_edens G i (fstcart x) (sndcart x)))
            continuous_on (:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum) /\
            (!p a c. &0 < c ==> cmw_edens G i p (c % a) = c pow 2 * cmw_edens G i p a) /\
            (!p. cmw_edens G i p (vec 0) = &0)`,
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[cmw_edens] THEN
    MP_TAC(ISPECL [`(:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum)`;
                   `G:real^K->real^K^K`;
                   `fstcart:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum->real^K`;
                   `\x:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum. cmw_c3 (sndcart x) i`;
                   `\x:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum. cmw_c3 (sndcart x) i`]
                  CMT_CONT_QUAD) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[CMW_C3_SND_CONT] THEN
    MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_FSTCART];
    REWRITE_TAC[cmw_edens; CMW_C3_CMUL; DOT_LMUL; DOT_RMUL; MATRIX_VECTOR_MUL_RMUL] THEN
    REAL_ARITH_TAC;
    MP_TAC(ISPECL [`&0`; `vec 0:real^(K,(K,K)finite_sum)finite_sum`; `i:num`] CMW_C3_CMUL) THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; cmw_edens] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[DOT_LZERO]]);;

let CMW_GRAM_ZERO = prove
 (`!(A:real^K->real^K^K) p.
        p4_e2(transp(cmw_jx (vec 0:real^(K,(K,K)finite_sum)finite_sum)) ** A p **
              cmw_jx (vec 0)) = &0`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`&0`; `vec 0:real^(K,(K,K)finite_sum)finite_sum`; `(A:real^K->real^K^K) p`]
                CMW_GRAM_CMUL) THEN
  REWRITE_TAC[VECTOR_MUL_LZERO] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[CMT_E2_CMUL] THEN REAL_ARITH_TAC);;

let CMW_ADENS_FACTS = prove
 (`!(G:real^K->real^K^K).
        (vectorize o G) continuous_on (:real^K)
        ==> (\x:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum.
                lift(cmw_adens G (fstcart x) (sndcart x)))
            continuous_on (:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum) /\
            (!p a c. &0 < c ==> cmw_adens G p (c % a) = c pow 2 * cmw_adens G p a) /\
            (!p. cmw_adens G p (vec 0) = &0)`,
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[cmw_adens] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_SQRT_COMPOSE THEN REWRITE_TAC[o_DEF] THEN
    MATCH_MP_TAC CMT_CONT_E2 THEN MATCH_MP_TAC CMW_GRAM_ENTRY_CONT THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[cmw_adens; CMW_GRAM_CMUL; CMT_E2_CMUL; SQRT_MUL] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_POW_POW] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `c pow 4 = (c pow 2) pow 2` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_POW_POW] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    MATCH_MP_TAC POW_2_SQRT THEN REWRITE_TAC[REAL_LE_POW_2];
    REWRITE_TAC[cmw_adens; CMW_GRAM_ZERO; SQRT_0]]);;

let CMW_CONT_E2_POL = prove
 (`!s (A:real^M->real^3^3) B.
        (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3 ==> (\x. lift(A x$i$j)) continuous_on s) /\
        (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3 ==> (\x. lift(B x$i$j)) continuous_on s)
        ==> (\x. lift(p4_e2_pol (A x) (B x))) continuous_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p4_e2_pol; LIFT_SUB] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
   [REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[o_DEF] THEN
    CONJ_TAC THEN MATCH_MP_TAC CMT_CONT_TRACE THEN ASM_REWRITE_TAC[DIMINDEX_3];
    MATCH_MP_TAC CMT_CONT_TRACE THEN REWRITE_TAC[DIMINDEX_3] THEN
    MP_TAC(ISPECL [`s:real^M->bool`; `A:real^M->real^3^3`; `B:real^M->real^3^3`]
                  CMT_CONT_MATMUL) THEN
    ASM_REWRITE_TAC[DIMINDEX_3]]);;

let CMW_TDENS_HOMOG = prove
 (`!(G:real^K->real^K^K) Q.
        (!p a c. &0 < c ==> cmw_tdens G Q p (c % a) = c pow 2 * cmw_tdens G Q p a) /\
        (!p. cmw_tdens G Q p (vec 0) = &0)`,
  REPEAT GEN_TAC THEN CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[cmw_tdens; CMW_GRAM_ZERO]] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[cmw_tdens; CMW_GRAM_CMUL; CMT_E2_CMUL; CMT_POL_CMUL] THEN
  ABBREV_TAC `ee = p4_e2(transp(cmw_jx (a:real^(K,(K,K)finite_sum)finite_sum)) **
                         (G:real^K->real^K^K) p ** cmw_jx a)` THEN
  ABBREV_TAC `pp = p4_e2_pol (transp(cmw_jx (a:real^(K,(K,K)finite_sum)finite_sum)) **
                              (G:real^K->real^K^K) p ** cmw_jx a)
                             (transp(cmw_jx a) ** (Q:real^K->real^K^K) p ** cmw_jx a)` THEN
  SUBGOAL_THEN `~((c:real) pow 2 pow 2 = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_EQ_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_ENTIRE] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
  REWRITE_TAC[SQRT_MUL] THEN
  SUBGOAL_THEN `sqrt((c:real) pow 2 pow 2) = c pow 2` SUBST1_TAC THENL
   [MATCH_MP_TAC POW_2_SQRT THEN REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN `~(sqrt ee = &0)` MP_TAC THENL [ASM_REWRITE_TAC[SQRT_EQ_0]; ALL_TAC] THEN
  UNDISCH_TAC `~((c:real) pow 2 pow 2 = &0)` THEN CONV_TAC REAL_FIELD);;

let CMW_TDENS_CONT = prove
 (`!(G:real^K->real^K^K) (Q:real^K->real^K^K) lam.
        (vectorize o G) continuous_on (:real^K) /\ (vectorize o Q) continuous_on (:real^K) /\
        (!z. transp(G z) = G z) /\ (!z. transp(Q z) = Q z) /\ &0 < lam /\
        (!z v. lam * norm v pow 2 <= v dot (G z ** v))
        ==> (\x:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum.
                lift(cmw_tdens G Q (fstcart x) (sndcart x)))
            continuous_on (:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `gg = \x:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum.
           p4_e2(transp(cmw_jx (sndcart x)) ** (G:real^K->real^K^K) (fstcart x) **
                 cmw_jx (sndcart x))` THEN
  ABBREV_TAC
   `hh = \x:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum.
           p4_e2_pol (transp(cmw_jx (sndcart x)) ** (G:real^K->real^K^K) (fstcart x) **
                      cmw_jx (sndcart x))
                     (transp(cmw_jx (sndcart x)) ** (Q:real^K->real^K^K) (fstcart x) **
                      cmw_jx (sndcart x))` THEN
  SUBGOAL_THEN
   `(\x. lift((gg:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum->real) x))
    continuous_on (:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum)`
  ASSUME_TAC THENL
   [EXPAND_TAC "gg" THEN REWRITE_TAC[] THEN MATCH_MP_TAC CMT_CONT_E2 THEN
    MATCH_MP_TAC CMW_GRAM_ENTRY_CONT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift((hh:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum->real) x))
    continuous_on (:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum)`
  ASSUME_TAC THENL
   [EXPAND_TAC "hh" THEN REWRITE_TAC[] THEN MATCH_MP_TAC CMW_CONT_E2_POL THEN
    CONJ_TAC THEN MATCH_MP_TAC CMW_GRAM_ENTRY_CONT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. cmw_tdens (G:real^K->real^K^K) Q (fstcart x) (sndcart x) =
        if (gg:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum->real) x = &0 then &0
        else (hh:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum->real) x / sqrt(gg x)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MAP_EVERY EXPAND_TAC ["gg"; "hh"] THEN REWRITE_TAC[cmw_tdens]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x0:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum.
       ?C. &0 <= C /\
           !x. dist(x,x0) < &1
               ==> abs(if (gg:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum->real) x = &0
                       then &0
                       else (hh:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum->real) x /
                            sqrt(gg x))
                   <= C * sqrt(gg x)`
  (LABEL_TAC "bd") THENL
   [X_GEN_TAC `x0:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum` THEN
    MP_TAC(ISPECL [`Q:real^K->real^K^K`; `cball(fstcart(x0:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum),&1)`]
                  CMT_QUAD_BOUND) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[COMPACT_CBALL] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `(:real^K)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `&2 * (M / lam)` THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN
    X_GEN_TAC `x:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum` THEN DISCH_TAC THEN
    MAP_EVERY EXPAND_TAC ["gg"; "hh"] THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC CMT_TRDENS_BOUND THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `v:real^K` THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_CBALL; dist] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(x0 - x:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum)` THEN
    REWRITE_TAC[GSYM FSTCART_SUB; NORM_FSTCART] THEN
    UNDISCH_TAC `dist(x:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum,x0) < &1` THEN
    REWRITE_TAC[dist] THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV] THEN
  X_GEN_TAC `x0:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum` THEN
  SUBGOAL_THEN
   `(\x. lift((gg:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum->real) x)) continuous at x0 /\
    (\x. lift((hh:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum->real) x)) continuous at x0`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV]; ALL_TAC] THEN
  ASM_CASES_TAC `(gg:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum->real) x0 = &0` THENL
   [USE_THEN "bd" (X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC o SPEC `x0:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum`) THEN
    ASM_REWRITE_TAC[continuous_at; DIST_LIFT; REAL_SUB_RZERO] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    UNDISCH_TAC `(\x. lift((gg:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum->real) x))
                 continuous at x0` THEN
    REWRITE_TAC[continuous_at; DIST_LIFT] THEN
    DISCH_THEN(MP_TAC o SPEC `(e / (C + &1)) pow 2`) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min d (&1)` THEN ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LT_01] THEN
    X_GEN_TAC `x:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum` THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `C * sqrt((gg:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum->real) x)` THEN
    CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `C * (e / (C + &1))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt((e / (C + &1)) pow 2)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_MONO_LE THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `x:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum`) THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC POW_2_SQRT THEN
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `C * e / (C + &1) = e * (C / (C + &1))` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 <= C` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LT_LMUL THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 <= C ==> &0 < C + &1`] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?d. &0 < d /\
        !x. dist(x,x0) < d
            ==> ~((gg:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum->real) x = &0)`
  (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THENL
   [UNDISCH_TAC `(\x. lift((gg:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum->real) x))
                 continuous at x0` THEN
    REWRITE_TAC[continuous_at; DIST_LIFT] THEN
    DISCH_THEN(MP_TAC o SPEC
      `abs((gg:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum->real) x0)`) THEN
    ASM_REWRITE_TAC[GSYM REAL_ABS_NZ] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum`) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_TRANSFORM_AT THEN
  EXISTS_TAC `\x. lift((hh:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum->real) x /
                       sqrt((gg:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum->real) x))` THEN
  EXISTS_TAC `d:real` THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[real_div; LIFT_CMUL] THEN
  MATCH_MP_TAC CONTINUOUS_MUL THEN REWRITE_TAC[o_DEF] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. sqrt((gg:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum->real) x)`;
                 `x0:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum`] CONTINUOUS_AT_INV) THEN
  REWRITE_TAC[o_DEF; SQRT_EQ_0] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC CONTINUOUS_AT_SQRT_COMPOSE THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Continuity of energy, area and trace along slices that                    *)
(* converge uniformly and in the Dirichlet integral of the radial extension. *)
(* ========================================================================= *)

let CMW_REXT_CONT = prove
 (`!u:real^3->real^K.
        u continuous_on sphere(vec 0,&1)
        ==> wan_rext u continuous_on {z:real^3 | ~(z = vec 0)}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `wan_rext (u:real^3->real^K) = u o (\z:real^3. inv(norm z) % z)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; wan_rext; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC[CMT_NORMALIZE_CONTINUOUS] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `sphere(vec 0:real^3,&1)` THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_SPHERE_0; NORM_MUL;
                  REAL_ABS_INV; REAL_ABS_NORM] THEN
  SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0]);;

let CMW_LSPACE2 = prove
 (`!s (f:real^M->real^N).
        f IN lspace s (&2) <=>
        f measurable_on s /\ (\x. lift(norm(f x) pow 2)) integrable_on s`,
  REWRITE_TAC[lspace; IN_ELIM_THM; RPOW_POW]);;

let CMW_PK_ALT = prove
 (`!s (v:real^3->real^K).
        cmw_pk s v = \z. pastecart (wan_wd s 1 v z) (pastecart (wan_wd s 2 v z) (wan_wd s 3 v z))`,
  REWRITE_TAC[FUN_EQ_THM; cmw_pk]);;

let CMW_PK_LSPACE = prove
 (`!s (v:real^3->real^K).
        wan_w12 s v ==> cmw_pk s v IN lspace s (&2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= 3 ==> wan_wd s i (v:real^3->real^K) IN lspace s (&2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MP_TAC(ISPECL [`s:real^3->bool`; `i:num`; `v:real^3->real^K`]
                                        WAN_WD_WORKS) THEN
    ASM_SIMP_TAC[DIMINDEX_3];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CMW_LSPACE2]) THEN REWRITE_TAC[CMW_LSPACE2] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[CMW_PK_ALT] THEN REPEAT(MATCH_MP_TAC MEASURABLE_ON_PASTECART THEN CONJ_TAC) THEN
    REWRITE_TAC[ETA_AX] THEN FIRST_X_ASSUM(fun th ->
      MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th) THEN MP_TAC(SPEC `3` th)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CMW_C3_NORM] THEN
  SIMP_TAC[CMW_C3_PK; IN_NUMSEG; SUM_3; ARITH; LIFT_ADD] THEN
  REPEAT(MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC) THEN
  FIRST_X_ASSUM(fun th ->
      MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th) THEN MP_TAC(SPEC `3` th)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let CMW_PK_DIFF = prove
 (`!s (v1:real^3->real^K) v2.
        open s /\ wan_w12 s v1 /\ wan_w12 s v2
        ==> drop(integral s (\z. lift(norm(cmw_pk s v1 z - cmw_pk s v2 z) pow 2))) =
            wan_dir s (\z. v1 z - v2 z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `\z. (v1:real^3->real^K) z - v2 z`;
                 `\i z. wan_wd s i (v1:real^3->real^K) z - wan_wd s i (v2:real^3->real^K) z`]
                WAN_DIR_EQ) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[WAN_W12_SUB] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC WAN_WPD_SUB THEN ASM_SIMP_TAC[WAN_WD_WORKS; ETA_AX];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[DIMINDEX_3] THEN
  SUBGOAL_THEN
   `!z. norm(cmw_pk s (v1:real^3->real^K) z - cmw_pk s v2 z) pow 2 =
        sum(1..3) (\i. norm(wan_wd s i v1 z - wan_wd s i v2 z) pow 2)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[CMW_C3_NORM] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[GSYM CMW_C3_PK] THEN
    MP_TAC(ISPEC `i:num` CMW_C3_LINEAR) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[REWRITE_RULE[] (MATCH_MP LINEAR_SUB th)]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 3
        ==> (\z. lift(norm(wan_wd s i (v1:real^3->real^K) z - wan_wd s i v2 z) pow 2))
            integrable_on s`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN
    MATCH_MP_TAC LSPACE_SUB THEN REWRITE_TAC[REAL_POS] THEN
    ASM_SIMP_TAC[WAN_WD_WORKS; DIMINDEX_3; ETA_AX];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_3; LIFT_ADD] THEN
  FIRST_X_ASSUM(fun th ->
      MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th) THEN MP_TAC(SPEC `3` th)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[INTEGRAL_ADD; INTEGRABLE_ADD; DROP_ADD; REAL_ADD_ASSOC]);;

let CMW_SLICE_CONV = prove
 (`!S (G:real^K->real^K^K) d (Q:real^K->real^K^K) (un:num->real^3->real^K) u k.
        cm_target S G d /\
        smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) /\
        (!z. transp(Q z) = Q z) /\ compact k /\
        (!n y. y IN sphere(vec 0,&1) ==> un n y IN k) /\
        (!y. y IN sphere(vec 0,&1) ==> u y IN k) /\
        (!n. un n continuous_on sphere(vec 0,&1)) /\ u continuous_on sphere(vec 0,&1) /\
        (!n. wan_s2_w12 (un n)) /\ wan_s2_w12 u /\
        (!e. &0 < e
             ==> eventually (\n. !y. y IN sphere(vec 0,&1) ==> norm(un n y - u y) < e)
                            sequentially) /\
        ((\n. wan_dir wan_shell (\z. wan_rext (un n) z - wan_rext u z)) ---> &0) sequentially
        ==> ((\n. cm_sen G (un n)) ---> cm_sen G u) sequentially /\
            ((\n. cm_sarea G (un n)) ---> cm_sarea G u) sequentially /\
            ((\n. cm_strace G Q (un n)) ---> cm_strace G Q u) sequentially`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "tg") STRIP_ASSUME_TAC) THEN
  USE_THEN "tg" (STRIP_ASSUME_TAC o MATCH_MP CMW_TARGET_FACTS) THEN
  USE_THEN "tg" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_target]) THEN
  SUBGOAL_THEN `((vectorize:real^K^K->real^(K,K)finite_prod) o Q) continuous_on (:real^K)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN EXISTS_TAC `0` THEN
    UNDISCH_TAC `smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o Q)` THEN
    SIMP_TAC[smooth_map_on];
    ALL_TAC] THEN
  SUBGOAL_THEN `lebesgue_measurable wan_shell` ASSUME_TAC THENL
   [SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; CMT_SHELL_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. z IN wan_shell ==> inv(norm z) % z IN sphere(vec 0,&1)`
  ASSUME_TAC THENL
   [REWRITE_TAC[wan_shell; IN_ELIM_THM; IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!n. wan_rext ((un:num->real^3->real^K) n) measurable_on wan_shell) /\
    wan_rext (u:real^3->real^K) measurable_on wan_shell`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [GEN_TAC; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN ASM_SIMP_TAC[CMW_REXT_CONT] THEN
    REWRITE_TAC[SUBSET; wan_shell; IN_ELIM_THM; GSYM NORM_EQ_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!n z. z IN wan_shell ==> wan_rext ((un:num->real^3->real^K) n) z IN k) /\
    (!z. z IN wan_shell ==> wan_rext (u:real^3->real^K) z IN k) /\
    (!e. &0 < e
         ==> eventually (\n. !z. z IN wan_shell
                                 ==> norm(wan_rext (un n) z - wan_rext u z) < e)
                        sequentially)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[wan_rext] THEN ASM_SIMP_TAC[] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `eventually:(num->bool)->(num)net->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!n. cmw_pk wan_shell (wan_rext ((un:num->real^3->real^K) n)) IN lspace wan_shell (&2)) /\
    cmw_pk wan_shell (wan_rext (u:real^3->real^K)) IN lspace wan_shell (&2) /\
    ((\n. drop(integral wan_shell
            (\z. lift(norm(cmw_pk wan_shell (wan_rext (un n)) z -
                           cmw_pk wan_shell (wan_rext u) z) pow 2)))) ---> &0) sequentially`
  STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[wan_s2_w12]) THEN
    ASM_SIMP_TAC[CMW_PK_LSPACE; CMW_PK_DIFF; CMT_SHELL_OPEN];
    ALL_TAC] THEN
  ABBREV_TAC `V = \n. wan_rext ((un:num->real^3->real^K) n)` THEN
  ABBREV_TAC `A = \n. cmw_pk wan_shell (wan_rext ((un:num->real^3->real^K) n))` THEN
  SUBGOAL_THEN
   `!FF:real^K->real^(K,(K,K)finite_sum)finite_sum->real.
       (\x. lift(FF (fstcart x) (sndcart x))) continuous_on
         (:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum) /\
       (!p a c. &0 < c ==> FF p (c % a) = c pow 2 * FF p a) /\
       (!p. FF p (vec 0) = &0)
       ==> ((\n. drop(integral wan_shell (\z. lift(FF ((V:num->real^3->real^K) n z)
                                                     ((A:num->real^3->real^(K,(K,K)finite_sum)finite_sum) n z)))))
            ---> drop(integral wan_shell (\z. lift(FF (wan_rext (u:real^3->real^K) z)
                                                     (cmw_pk wan_shell (wan_rext u) z)))))
           sequentially`
  (LABEL_TAC "fc") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMW_FUNC_CONV THEN EXISTS_TAC `k:real^K->bool` THEN
    MAP_EVERY EXPAND_TAC ["V"; "A"] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[cm_sarea; CMW_WGRAM_PK] THEN MATCH_MP_TAC REALLIM_LMUL THEN
    USE_THEN "fc" (MP_TAC o SPEC `cmw_adens (G:real^K->real^K^K)`) THEN
    MAP_EVERY EXPAND_TAC ["V"; "A"] THEN REWRITE_TAC[cmw_adens] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPEC `G:real^K->real^K^K` CMW_ADENS_FACTS) THEN ASM_REWRITE_TAC[cmw_adens];
    REWRITE_TAC[cm_strace; CMW_WGRAM_PK] THEN MATCH_MP_TAC REALLIM_LMUL THEN
    USE_THEN "fc" (MP_TAC o SPEC `cmw_tdens (G:real^K->real^K^K) Q`) THEN
    MAP_EVERY EXPAND_TAC ["V"; "A"] THEN REWRITE_TAC[cmw_tdens] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    SUBGOAL_THEN
     `(\x:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum.
         lift(cmw_tdens (G:real^K->real^K^K) Q (fstcart x) (sndcart x)))
      continuous_on (:real^(K,(K,(K,K)finite_sum)finite_sum)finite_sum)`
    MP_TAC THENL
     [MATCH_MP_TAC CMW_TDENS_CONT THEN EXISTS_TAC `lam:real` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`G:real^K->real^K^K`; `Q:real^K->real^K^K`] CMW_TDENS_HOMOG) THEN
    REWRITE_TAC[cmw_tdens] THEN SIMP_TAC[]] THEN
  REWRITE_TAC[cm_sen; wan_gdir; real_div] THEN MATCH_MP_TAC REALLIM_RMUL THEN
  MATCH_MP_TAC REALLIM_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; DIMINDEX_3] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  USE_THEN "fc" (MP_TAC o SPEC `cmw_edens (G:real^K->real^K^K) i`) THEN
  MAP_EVERY EXPAND_TAC ["V"; "A"] THEN ASM_SIMP_TAC[cmw_edens; CMW_C3_PK] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `i:num`] CMW_EDENS_FACTS) THEN
  ASM_SIMP_TAC[cmw_edens]);;

(* ========================================================================= *)
(* The reflection through the equator preserves W^{1,2} of the               *)
(* shell and the Dirichlet integral (WAN_W12_DIFFEO).                        *)
(* ========================================================================= *)

let CMW_NONNEG_ABSINT = prove
 (`!(f:real^M->real) s.
        (!x. x IN s ==> &0 <= f x) /\ (\x. lift(f x)) integrable_on s
        ==> (\x. lift(f x)) absolutely_integrable_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
  ASM_REWRITE_TAC[DIMINDEX_1; ARITH_RULE `1 <= i /\ i <= 1 <=> i = 1`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[GSYM drop; LIFT_DROP] THEN ASM_SIMP_TAC[]);;

let CMW_REFL_FRECHET = prove
 (`!x:real^3. frechet_derivative bel_refl3 (at x) = bel_refl3`,
  GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[BEL_REFL3_LINEAR]);;

let CMW_REFL_VSUM = prove
 (`!(g:num->real^K) i.
        1 <= i /\ i <= 3
        ==> vsum(1..3) (\j. (bel_refl3(basis i))$j % g j) =
            (if i = 3 then --(g i) else g i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ARITH_RULE `1 <= i /\ i <= 3 <=> i = 1 \/ i = 2 \/ i = 3`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[VSUM_3] THEN
  SIMP_TAC[bel_refl3; LAMBDA_BETA; DIMINDEX_3; ARITH; BASIS_COMPONENT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN VECTOR_ARITH_TAC);;

let CMW_REFL_W12 = prove
 (`!f:real^3->real^K.
        wan_w12 wan_shell f
        ==> wan_w12 wan_shell (\x. f(bel_refl3 x)) /\
            (!i. 1 <= i /\ i <= 3
                 ==> wan_wpd wan_shell i (\x. f(bel_refl3 x))
                       (\x. if i = 3 then --(wan_wd wan_shell i f (bel_refl3 x))
                            else wan_wd wan_shell i f (bel_refl3 x))) /\
            wan_dir wan_shell (\x. f(bel_refl3 x)) = wan_dir wan_shell f`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(:3)`; `(:K)`] WAN_W12_DIFFEO) THEN REWRITE_TAC[WAN_W12_DIFFEO_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`wan_shell`; `wan_shell`; `bel_refl3`; `bel_refl3`;
                             `f:real^3->real^K`]) THEN
  REWRITE_TAC[CMW_REFL_FRECHET; DIMINDEX_3] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CMT_SHELL_OPEN] THEN
    SUBGOAL_THEN `continuously_differentiable 1 wan_shell bel_refl3` (fun th -> REWRITE_TAC[th])
    THENL
     [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN THEN
      REWRITE_TAC[CMT_SHELL_OPEN; BEL_REFL3_LINEAR];
      ALL_TAC] THEN
    REWRITE_TAC[wan_shell; IN_ELIM_THM; CMW_REFL3_FACTS] THEN MESON_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 3
        ==> wan_wpd wan_shell i (\x. (f:real^3->real^K)(bel_refl3 x))
              (\x. if i = 3 then --(wan_wd wan_shell i f (bel_refl3 x))
                   else wan_wd wan_shell i f (bel_refl3 x))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    X_GEN_TAC `x:real^3` THEN
    MP_TAC(ISPECL [`\j. wan_wd wan_shell j (f:real^3->real^K) (bel_refl3 x)`; `i:num`]
                  CMW_REFL_VSUM) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`wan_shell`; `\x. (f:real^3->real^K)(bel_refl3 x)`;
                 `\i x. if i = 3 then --(wan_wd wan_shell i (f:real^3->real^K) (bel_refl3 x))
                        else wan_wd wan_shell i f (bel_refl3 x)`] WAN_DIR_EQ) THEN
  REWRITE_TAC[CMT_SHELL_OPEN; DIMINDEX_3] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[wan_dir; DIMINDEX_3] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!x. norm(if i = 3 then --(wan_wd wan_shell i (f:real^3->real^K) (bel_refl3 x))
             else wan_wd wan_shell i f (bel_refl3 x)) pow 2 =
        norm(wan_wd wan_shell i f (bel_refl3 x)) pow 2`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[NORM_NEG]; ALL_TAC] THEN
  AP_TERM_TAC THEN
  MP_TAC(ISPECL [`\x. lift(norm(wan_wd wan_shell i (f:real^3->real^K) x) pow 2)`;
                 `bel_refl3`; `wan_shell`] INTEGRAL_CHANGE_OF_VARIABLES_LINEAR) THEN
  REWRITE_TAC[BEL_REFL3_LINEAR; CMW_REFL3_FACTS; VECTOR_MUL_LID; o_DEF] THEN
  ANTS_TAC THENL
   [DISJ1_TAC THEN MATCH_MP_TAC CMW_NONNEG_ABSINT THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_SIMP_TAC[WAN_WD_WORKS; DIMINDEX_3; ETA_AX];
    SIMP_TAC[]]);;

(* ========================================================================= *)
(* Regularization of a slice supported away from the north                   *)
(* pole, by mollification in the north chart (pc_wan_moll, WAN_S2_STEREO).  *)
(* ========================================================================= *)

let CMW_WPD_SPIKE = prove
 (`!s i (u:real^N->real^K) v v'.
        negligible {x | x IN s /\ ~(v x = v' x)} /\ wan_wpd s i u v
        ==> wan_wpd s i u v'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_wpd; wan_lloc] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `k:real^N->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] ABSOLUTELY_INTEGRABLE_SPIKE) THEN
    EXISTS_TAC `v:real^N->real^K` THEN
    EXISTS_TAC `{x | x IN s /\ ~((v:real^N->real^K) x = v' x)}` THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN ASM_MESON_TAC[SUBSET];
    X_GEN_TAC `phi:real^N->real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `phi:real^N->real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC INTEGRAL_SPIKE THEN
    EXISTS_TAC `{x | x IN s /\ ~((v:real^N->real^K) x = v' x)}` THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN MESON_TAC[]]);;

let CMW_WPD_TRUNC = prove
 (`!i (f:real^N->real^K) g r.
        (!x. ~(x IN cball(vec 0,r)) ==> f x = vec 0) /\ wan_wpd (:real^N) i f g
        ==> wan_wpd (:real^N) i f (\x. if x IN cball(vec 0,r) then g x else vec 0)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CMW_WPD_SPIKE THEN
  EXISTS_TAC `g:real^N->real^K` THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `U = (:real^N) DIFF cball(vec 0,r)` THEN
  SUBGOAL_THEN `open (U:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[GSYM closed; CLOSED_CBALL]; ALL_TAC] THEN
  SUBGOAL_THEN `negligible {x | x IN (U:real^N->bool) /\ ~((g:real^N->real^K) x = vec 0)}`
  MP_TAC THENL
   [MATCH_MP_TAC WAN_WPD_UNIQUE THEN EXISTS_TAC `i:num` THEN
    EXISTS_TAC `f:real^N->real^K` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC WAN_WPD_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      MP_TAC(ISPECL [`U:real^N->bool`; `i:num`] (INST_TYPE [`:K`,`:K`] WAN_WPD_ZERO)) THEN
      MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC CMT_WAN_WPD_EQ THEN
      EXPAND_TAC "U" THEN REWRITE_TAC[IN_DIFF; IN_UNIV] THEN ASM_MESON_TAC[]];
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] NEGLIGIBLE_SUBSET) THEN
    EXPAND_TAC "U" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DIFF; IN_UNIV] THEN
    GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]]);;

let CMW_P_FAR = prove
 (`!x:real^2. &3 <= norm x ==> &3 / &4 <= (stereo2_n_inv x)$3`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[STEX_STEREO2_N_INV_COMPONENTS] THEN
  SUBGOAL_THEN `&9 <= norm(x:real^2) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 pow 2` THEN CONJ_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&9 <= x ==> &0 < x + &1`] THEN
  ASM_REAL_ARITH_TAC);;

let CMW_N_FAR = prove
 (`!y:real^3. y IN sphere(vec 0,&1) /\ ~(y = basis 3) /\ &9 / &10 < y$3
              ==> &4 < norm(stereo2_n y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `y IN sphere(vec 0:real^3,&1) DELETE basis 3`
   (STRIP_ASSUME_TAC o MATCH_MP STEX_STEREO2_N_NORM2) THENL
   [ASM_REWRITE_TAC[IN_DELETE]; ALL_TAC] THEN
  SUBGOAL_THEN `abs((y:real^3)$3) <= &1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`y:real^3`; `3`] COMPONENT_LE_NORM) THEN
    REWRITE_TAC[DIMINDEX_3; ARITH] THEN
    UNDISCH_TAC `y IN sphere(vec 0:real^3,&1)` THEN REWRITE_TAC[IN_SPHERE_0] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `2` THEN
  REWRITE_TAC[NORM_POS_LE] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < &1 - (y:real^3)$3` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The north-chart regularization of a slice that vanishes                   *)
(* near the north pole.                                                      *)
(* ========================================================================= *)

let CMW_SQNORM_CONT = prove
 (`(\y:real^N. lift(norm y pow 2)) continuous_on (:real^N)`,
  REWRITE_TAC[NORM_POW_2] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
  REWRITE_TAC[CONTINUOUS_ON_ID]);;

let CMW_LSPACE_TRUNC = prove
 (`!(g:real^N->real^K) c.
        g IN lspace (:real^N) (&2) /\ lebesgue_measurable c
        ==> (\x. if x IN c then g x else vec 0) IN lspace (:real^N) (&2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CMW_LSPACE2] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x. if x IN c then (g:real^N->real^K) x else vec 0) measurable_on (:real^N)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MEASURABLE_ON_RESTRICT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `\x. lift(norm((g:real^N->real^K) x) pow 2)` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`\y:real^K. lift(norm y pow 2)`;
                   `\x. if x IN c then (g:real^N->real^K) x else vec 0`; `(:real^N)`]
                  CMW_MEASURABLE_COMPOSE_CONT) THEN
    ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_UNIV; CMW_SQNORM_CONT];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[NORM_LIFT; LIFT_DROP] THEN
    COND_CASES_TAC THEN
    REWRITE_TAC[NORM_0; REAL_ABS_POW; REAL_ABS_NORM; REAL_LE_REFL; REAL_LE_POW_2] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_LE_POW_2]]);;

let CMW_CONT_SUPP_LSPACE = prove
 (`!(u:real^N->real^K) r.
        u continuous_on (:real^N) /\ (!x. ~(x IN cball(vec 0,r)) ==> u x = vec 0)
        ==> u IN lspace (:real^N) (&2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CMW_LSPACE2] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_UNIV];
    MATCH_MP_TAC WAN_CONT_SUPPORT_INTEGRABLE THEN EXISTS_TAC `cball(vec 0:real^N,r)` THEN
    REWRITE_TAC[COMPACT_CBALL] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`u:real^N->real^K`; `\y:real^K. lift(norm y pow 2)`] CONTINUOUS_ON_COMPOSE) THEN
      REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^K)` THEN
      REWRITE_TAC[CMW_SQNORM_CONT; SUBSET_UNIV];
      ASM_SIMP_TAC[NORM_0; LIFT_NUM] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[LIFT_NUM]]]);;

let CMW_NORTH_REG = prove
 (`!(w:real^3->real^K) eps.
        WAN_S2_STEREO_STATEMENT (:K) /\
        w continuous_on sphere(vec 0,&1) /\ wan_s2_w12 w /\
        (!y. y IN sphere(vec 0,&1) /\ &3 / &4 <= y$3 ==> w y = vec 0) /\ &0 < eps
        ==> ?v. continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext v) /\
                (!y. y IN sphere(vec 0,&1) ==> norm(v y - w y) < eps) /\
                wan_dir wan_shell (\z. wan_rext v z - wan_rext w z) < eps`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "st") (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "van") ASSUME_TAC)))) THEN
  USE_THEN "st" (LABEL_TAC "st1" o CONJUNCT1 o GEN_REWRITE_RULE I [WAN_S2_STEREO_STATEMENT]) THEN
  ABBREV_TAC `f = \x:real^2. (w:real^3->real^K)(stereo2_n_inv x)` THEN
  SUBGOAL_THEN `(f:real^2->real^K) continuous_on (:real^2)` ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN
    SUBGOAL_THEN `(\x:real^2. (w:real^3->real^K)(stereo2_n_inv x)) = w o stereo2_n_inv`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN EXISTS_TAC `0` THEN
      MP_TAC STEX_STEREO2_N_INV_SMOOTH THEN SIMP_TAC[smooth_map_on];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `sphere(vec 0:real^3,&1)` THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0; BEL_P_CHART]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. ~(x IN cball(vec 0:real^2,&3)) ==> (f:real^2->real^K) x = vec 0`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_CBALL_0; REAL_NOT_LE] THEN DISCH_TAC THEN
    EXPAND_TAC "f" THEN USE_THEN "van" MATCH_MP_TAC THEN
    REWRITE_TAC[IN_SPHERE_0; BEL_P_CHART] THEN MATCH_MP_TAC CMW_P_FAR THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "st1" (MP_TAC o C MP (ASSUME `wan_s2_w12 (w:real^3->real^K)`) o
                  SPEC `w:real^3->real^K`) THEN
  REWRITE_TAC[ASSUME `(\x. (w:real^3->real^K)(stereo2_n_inv x)) = f`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC))) THEN
  DISCH_THEN(X_CHOOSE_TAC `g:num->real^2->real^K` o
             REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  ABBREV_TAC `gg = \i x. if x IN cball(vec 0:real^2,&3) then (g:num->real^2->real^K) i x
                         else vec 0` THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> (gg:num->real^2->real^K) i IN lspace (:real^2) (&2) /\
            wan_wpd (:real^2) i f (gg i) /\
            (!x. ~(x IN cball(vec 0,&3)) ==> gg i x = vec 0)`
  (LABEL_TAC "gg") THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN EXPAND_TAC "gg" THEN REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CMW_LSPACE_TRUNC THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_CLOSED; CLOSED_CBALL; ETA_AX];
      MATCH_MP_TAC CMW_WPD_TRUNC THEN ASM_SIMP_TAC[ETA_AX];
      SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^2->real^K`; `cball(vec 0:real^2,&4)`] WAN_MOLL_UNIFORM) THEN
  ASM_REWRITE_TAC[COMPACT_CBALL] THEN DISCH_THEN(MP_TAC o SPEC `eps / &2`) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`(gg:num->real^2->real^K) 1`; `cball(vec 0:real^2,&3)`] WAN_MOLL_L2_CONV) THEN
  USE_THEN "gg" (MP_TAC o SPEC `1`) THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[COMPACT_CBALL] THEN DISCH_THEN(MP_TAC o SPEC `eps / &3`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`(gg:num->real^2->real^K) 2`; `cball(vec 0:real^2,&3)`] WAN_MOLL_L2_CONV) THEN
  USE_THEN "gg" (MP_TAC o SPEC `2`) THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[COMPACT_CBALL] THEN DISCH_THEN(MP_TAC o SPEC `eps / &3`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d3:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `e = min (&1) (min d1 (min d2 d3)) / &2` THEN
  SUBGOAL_THEN `&0 < e /\ e < &1 /\ e < d1 /\ e < d2 /\ e < d3` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `b = wan_moll e (f:real^2->real^K)` THEN
  SUBGOAL_THEN `continuously_differentiable 1 (:real^2) (b:real^2->real^K)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`e:real`; `f:real^2->real^K`] WAN_MOLL_SMOOTH) THEN
    ASM_SIMP_TAC[smooth_map_on];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2. &4 <= norm x ==> (b:real^2->real^K) x = vec 0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`e:real`; `f:real^2->real^K`; `cball(vec 0:real^2,&3)`] WAN_MOLL_SUPPORT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_ELIM_THM; IN_CBALL_0; IN_BALL_0] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [`a:real^2`; `c:real^2`] THEN
    STRIP_TAC THEN UNDISCH_TAC `&4 <= norm(x:real^2)` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`a:real^2`; `c:real^2`] NORM_TRIANGLE) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i x. 1 <= i /\ i <= 2
          ==> partial_derivative i (b:real^2->real^K) x = wan_moll e ((gg:num->real^2->real^K) i) x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "b" THEN MATCH_MP_TAC WAN_MOLL_WPD THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `V = \y:real^3. if y = basis 3 then vec 0 else (b:real^2->real^K)(stereo2_n y)` THEN
  EXISTS_TAC `V:real^3->real^K` THEN
  SUBGOAL_THEN `basis 3 IN sphere(vec 0:real^3,&1)` ASSUME_TAC THENL
   [SIMP_TAC[IN_SPHERE_0; NORM_BASIS; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `(basis 3:real^3)$3 = &1` ASSUME_TAC THENL
   [SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. ~(x = vec 0) ==> inv(norm x) % x IN sphere(vec 0,&1)`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN sphere(vec 0,&1) ==> y$3 <= &1` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MP_TAC(ISPECL [`y:real^3`; `3`] COMPONENT_LE_NORM) THEN
    REWRITE_TAC[DIMINDEX_3; ARITH] THEN
    UNDISCH_TAC `y IN sphere(vec 0:real^3,&1)` THEN REWRITE_TAC[IN_SPHERE_0] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext (V:real^3->real^K))`
  ASSUME_TAC THENL
   [SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_LOCAL_OPEN; CMT_OPEN_NONZERO] THEN
    X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    ASM_CASES_TAC `(inv(norm z) % z:real^3)$3 < &1` THENL
     [EXISTS_TAC `{x:real^3 | ~(x = vec 0) /\ (inv(norm x) % x)$3 < &1}` THEN
      ASM_REWRITE_TAC[SMT_OPEN_NORMALIZED_HALFSPACES; IN_ELIM_THM] THEN
      CONJ_TAC THENL [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_EQ_OPEN THEN
      EXISTS_TAC `(b:real^2->real^K) o (\x:real^3. stereo2_n(inv(norm x) % x))` THEN
      REWRITE_TAC[SMT_OPEN_NORMALIZED_HALFSPACES] THEN CONJ_TAC THENL
       [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_ELIM_THM; o_THM; wan_rext] THEN STRIP_TAC THEN
        EXPAND_TAC "V" THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
        UNDISCH_TAC `(inv(norm x) % x:real^3)$3 < &1` THEN ASM_REWRITE_TAC[] THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_COMPOSE_OPEN THEN EXISTS_TAC `(:real^2)` THEN
        ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; SMT_OPEN_NORMALIZED_HALFSPACES] THEN
        MP_TAC SMT_STEREO_NORMALIZED_SMOOTH THEN SIMP_TAC[smooth_map_on]];
      EXISTS_TAC `{x:real^3 | ~(x = vec 0) /\ &9 / &10 < (inv(norm x) % x)$3}` THEN
      ASM_REWRITE_TAC[SMT_OPEN_NORMALIZED_HALFSPACES; IN_ELIM_THM] THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_EQ_OPEN THEN
      EXISTS_TAC `(\x:real^3. vec 0:real^K)` THEN
      REWRITE_TAC[SMT_OPEN_NORMALIZED_HALFSPACES] THEN CONJ_TAC THENL
       [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_ELIM_THM; wan_rext] THEN STRIP_TAC THEN
        EXPAND_TAC "V" THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
        CONV_TAC SYM_CONV THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `&4`)) (concl th) && is_forall(concl th))) THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC CMW_N_FAR THEN ASM_SIMP_TAC[];
        SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_CONST; SMT_OPEN_NORMALIZED_HALFSPACES]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN EXPAND_TAC "V" THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      SUBGOAL_THEN `(w:real^3->real^K)(basis 3) = vec 0` SUBST1_TAC THENL
       [USE_THEN "van" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(w:real^3->real^K) y = f(stereo2_n y)` SUBST1_TAC THENL
     [EXPAND_TAC "f" THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC STEX_STEREO2_N_LEFT THEN ASM_REWRITE_TAC[IN_DELETE];
      ALL_TAC] THEN
    ASM_CASES_TAC `norm(stereo2_n(y:real^3)) <= &4` THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `eps / &2` THEN CONJ_TAC THENL
       [EXPAND_TAC "b" THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `d1:real`)) (concl th) && is_forall(concl th))) THEN
        ASM_REWRITE_TAC[IN_CBALL_0];
        ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `(b:real^2->real^K)(stereo2_n y) = vec 0 /\ (f:real^2->real^K)(stereo2_n y) = vec 0`
      (fun th -> REWRITE_TAC[th; VECTOR_SUB_REFL; NORM_0] THEN ASM_REWRITE_TAC[]) THEN
      CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[IN_CBALL_0] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_s2_w12 (V:real^3->real^K)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `V:real^3->real^K` CMW_S2_C1_DIR) THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `wan_rext (\y. (V:real^3->real^K) y - w y) =
                (\z. wan_rext V z - wan_rext w z)` ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; wan_rext]; ALL_TAC] THEN
  SUBGOAL_THEN `wan_s2_w12 (\y. (V:real^3->real^K) y - w y)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[wan_s2_w12] THEN MATCH_MP_TAC WAN_W12_SUB THEN
    RULE_ASSUM_TAC(REWRITE_RULE[wan_s2_w12]) THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  USE_THEN "st1" (MP_TAC o C MP (ASSUME `wan_s2_w12 (\y. (V:real^3->real^K) y - w y)`) o
                  SPEC `\y. (V:real^3->real^K) y - w y`) THEN
  DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\y:real^2. (V:real^3->real^K)(stereo2_n_inv y) - w(stereo2_n_inv y)) =
    (\x. (b:real^2->real^K) x - f x)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^2` THEN
    EXPAND_TAC "V" THEN EXPAND_TAC "f" THEN REWRITE_TAC[] THEN
    MP_TAC(ISPEC `x:real^2` STEX_STEREO2_N_INV_IN) THEN
    REWRITE_TAC[IN_DELETE; STEX_STEREO2_N_RIGHT] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[wan_s2_dir] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 2
        ==> wan_wpd (:real^2) i (\x. (b:real^2->real^K) x - f x)
              (\x. wan_moll e ((gg:num->real^2->real^K) i) x - gg i x) /\
            (\x. wan_moll e ((gg:num->real^2->real^K) i) x - gg i x) IN lspace (:real^2) (&2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    USE_THEN "gg" (MP_TAC o C MP (CONJ (ASSUME `1 <= i`) (ASSUME `i <= 2`)) o SPEC `i:num`) THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC WAN_WPD_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN
      SUBGOAL_THEN `wan_moll e ((gg:num->real^2->real^K) i) =
                    (\x. partial_derivative i (b:real^2->real^K) x)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC WAN_WPD_C1 THEN ASM_REWRITE_TAC[OPEN_UNIV];
      MATCH_MP_TAC LSPACE_SUB THEN ASM_SIMP_TAC[REAL_POS; ETA_AX; WAN_MOLL_L2]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^2)`; `\x. (b:real^2->real^K) x - f x`;
                 `\i x. wan_moll e ((gg:num->real^2->real^K) i) x - gg i x`] WAN_DIR_EQ) THEN
  REWRITE_TAC[OPEN_UNIV; DIMINDEX_2] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN REWRITE_TAC[wan_w12; DIMINDEX_2] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CMW_CONT_SUPP_LSPACE THEN EXISTS_TAC `&4` THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN
        MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN EXISTS_TAC `1` THEN
        ASM_REWRITE_TAC[];
        X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_CBALL_0; REAL_NOT_LE] THEN DISCH_TAC THEN
        SUBGOAL_THEN `(b:real^2->real^K) x = vec 0 /\ (f:real^2->real^K) x = vec 0`
        (fun th -> REWRITE_TAC[th; VECTOR_SUB_REFL]) THEN
        CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC[IN_CBALL_0] THEN ASM_REAL_ARITH_TAC];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      EXISTS_TAC `\x. wan_moll e ((gg:num->real^2->real^K) i) x - gg i x` THEN
      ASM_SIMP_TAC[]];
    DISCH_THEN SUBST_ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUM_2]) THEN
  USE_THEN "gg" (MP_TAC o SPEC `1`) THEN USE_THEN "gg" (MP_TAC o SPEC `2`) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `drop(integral (:real^2) (\x. lift(norm(wan_moll e ((gg:num->real^2->real^K) 1) x - gg 1 x) pow 2)))
    < eps / &3 /\
    drop(integral (:real^2) (\x. lift(norm(wan_moll e ((gg:num->real^2->real^K) 2) x - gg 2 x) pow 2)))
    < eps / &3`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `eps / &3`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN NO_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Regularization of an arbitrary C^0 /\ W^{1,2} slice: a                    *)
(* cutoff in the height splits it into a part away from the north pole and *)
(* a part away from the south pole; the second is reflected.                *)
(* ========================================================================= *)

let cmw_cut = new_definition
 `cmw_cut (z:real^3) = smooth_step(&3 - &4 * (inv(norm z) % z)$3)`;;

let CMW_CUT_SMOOTH = prove
 (`smooth_map_on {z:real^3 | ~(z = vec 0)} (\z. lift(cmw_cut z))`,
  REWRITE_TAC[cmw_cut] THEN
  MP_TAC(ISPECL [`{z:real^3 | ~(z = vec 0)}`;
                 `\z:real^3. lift(&3 - &4 * (inv(norm z) % z)$3)`]
                SMOOTH_MAP_ON_SMOOTH_STEP_COMPOSE) THEN
  REWRITE_TAC[LIFT_DROP; CMT_OPEN_NONZERO] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[LIFT_SUB; LIFT_CMUL] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN REWRITE_TAC[CMT_OPEN_NONZERO; SMOOTH_MAP_ON_CONST] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN REWRITE_TAC[CMT_OPEN_NONZERO] THEN
  SUBGOAL_THEN `(\z:real^3. lift((inv(norm z) % z)$3)) =
                (\y:real^3. lift(y$3)) o (\z. inv(norm z) % z)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
  REWRITE_TAC[CMT_OPEN_NONZERO; SMOOTH_MAP_ON_NORMALIZE] THEN REWRITE_TAC[linear] THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; LIFT_ADD; LIFT_CMUL]);;

let CMW_SHELL_PARTIAL_BOUND = prove
 (`!(h:real^3->real^N).
        continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} h
        ==> ?B. !z i. z IN wan_shell /\ 1 <= i /\ i <= 3
                      ==> norm(partial_derivative i h z) <= B`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `k = cball(vec 0:real^3,&2) DIFF ball(vec 0,&1 / &2)` THEN
  SUBGOAL_THEN `compact (k:real^3->bool) /\ k SUBSET {z:real^3 | ~(z = vec 0)} /\
                wan_shell SUBSET k` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN SIMP_TAC[COMPACT_DIFF; COMPACT_CBALL; OPEN_BALL] THEN
    REWRITE_TAC[SUBSET; IN_DIFF; IN_CBALL_0; IN_BALL_0; IN_ELIM_THM; wan_shell] THEN
    CONJ_TAC THEN GEN_TAC THEN REWRITE_TAC[GSYM NORM_EQ_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{z:real^3 | ~(z = vec 0)}`; `h:real^3->real^N`] CMT_C1_FACTS) THEN
  ASM_REWRITE_TAC[CMT_OPEN_NONZERO] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!i. ?B. !z. z IN k ==> norm(partial_derivative i (h:real^3->real^N) z) <= B`
  MP_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`\z. partial_derivative i (h:real^3->real^N) z`; `k:real^3->bool`]
                  COMPACT_CONTINUOUS_IMAGE) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `BB:num->real`) THEN
  EXISTS_TAC `abs((BB:num->real) 1) + abs(BB 2) + abs(BB 3)` THEN
  REWRITE_TAC[ARITH_RULE `1 <= i /\ i <= 3 <=> i = 1 \/ i = 2 \/ i = 3`] THEN
  MAP_EVERY X_GEN_TAC [`z:real^3`; `i:num`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SUBGOAL_THEN `(z:real^3) IN k` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let CMW_SHELL_MUL = prove
 (`!(g:real^3->real) (u:real^3->real^K) B.
        smooth_map_on {z:real^3 | ~(z = vec 0)} (\z. lift(g z)) /\
        (!z. z IN wan_shell ==> abs(g z) <= B) /\
        wan_w12 wan_shell u
        ==> wan_w12 wan_shell (\z. g z % u z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:3)`; `(:K)`] WAN_MUL_W12) THEN REWRITE_TAC[WAN_MUL_W12_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`wan_shell`; `u:real^3->real^K`; `g:real^3->real`]) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[CMT_SHELL_OPEN; DIMINDEX_3] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
    ASM_REWRITE_TAC[SUBSET; wan_shell; IN_ELIM_THM; GSYM NORM_EQ_0] THEN REAL_ARITH_TAC;
    EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPEC `\z:real^3. lift(g z)` CMW_SHELL_PARTIAL_BOUND) THEN ANTS_TAC THENL
     [UNDISCH_TAC `smooth_map_on {z:real^3 | ~(z = vec 0)} (\z. lift(g z))` THEN
      SIMP_TAC[smooth_map_on];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `C:real` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`x:real^3`; `i:num`] THEN STRIP_TAC THEN
    REWRITE_TAC[wan_dpart] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^3`; `i:num`]) THEN
    ASM_REWRITE_TAC[partial_derivative; NORM_1]]);;

let CMW_CUT_FACTS = prove
 (`(!z. &0 <= cmw_cut z /\ cmw_cut z <= &1) /\
   (!z:real^3. cmw_cut(inv(norm z) % z) = cmw_cut z) /\
   (!y. y IN sphere(vec 0,&1) /\ y$3 <= &1 / &2 ==> cmw_cut y = &1) /\
   (!y. y IN sphere(vec 0,&1) /\ &3 / &4 <= y$3 ==> cmw_cut y = &0)`,
  SUBGOAL_THEN `!y:real^3. y IN sphere(vec 0,&1) ==> inv(norm y) % y = y` ASSUME_TAC THENL
   [SIMP_TAC[IN_SPHERE_0; REAL_INV_1; VECTOR_MUL_LID]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[cmw_cut; SMOOTH_STEP_BOUNDS];
    GEN_TAC THEN ASM_CASES_TAC `z:real^3 = vec 0` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN REWRITE_TAC[cmw_cut] THEN
    FIRST_X_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th (MATCH_MP SMT_NORMALIZE_SPHERE
      (ASSUME `~(z:real^3 = vec 0)`))]);
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[cmw_cut] THEN MATCH_MP_TAC SMOOTH_STEP_1 THEN
    ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[cmw_cut] THEN MATCH_MP_TAC SMOOTH_STEP_0 THEN
    ASM_REAL_ARITH_TAC]);;

let CMW_REFL_REXT = prove
 (`!(u:real^3->real^K) z. wan_rext (\y. u(bel_refl3 y)) z = wan_rext u (bel_refl3 z)`,
  REWRITE_TAC[wan_rext; CMW_REFL3_FACTS] THEN
  SIMP_TAC[CMW_REFL3_FACTS]);;

let CMW_REXT_C1_W12 = prove
 (`!u:real^3->real^K.
        continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext u)
        ==> wan_w12 wan_shell (wan_rext u)`,
  MESON_TAC[CMT_REXT_WD_AE]);;

let CMW_SLICE_REG = prove
 (`!(u:real^3->real^K) eps.
        WAN_S2_STEREO_STATEMENT (:K) /\
        u continuous_on sphere(vec 0,&1) /\ wan_s2_w12 u /\ &0 < eps
        ==> ?v. continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext v) /\
                (!y. y IN sphere(vec 0,&1) ==> norm(v y - u y) < eps) /\
                wan_dir wan_shell (\z. wan_rext v z - wan_rext u z) < eps`,
  REPEAT STRIP_TAC THEN
  STRIP_ASSUME_TAC CMW_CUT_FACTS THEN
  SUBGOAL_THEN `(\y:real^3. lift(cmw_cut y)) continuous_on sphere(vec 0,&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN EXISTS_TAC `0` THEN
      MP_TAC CMW_CUT_SMOOTH THEN SIMP_TAC[smooth_map_on];
      REWRITE_TAC[SUBSET; IN_SPHERE_0; IN_ELIM_THM] THEN GEN_TAC THEN
      DISCH_THEN(fun th -> REWRITE_TAC[GSYM NORM_EQ_0; th]) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN sphere(vec 0,&1) ==> bel_refl3 y IN sphere(vec 0,&1)`
  ASSUME_TAC THENL [REWRITE_TAC[IN_SPHERE_0; CMW_REFL3_FACTS]; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. (bel_refl3 y)$3 = --(y$3)` ASSUME_TAC THENL
   [REWRITE_TAC[BEL_REFL3_COMPONENTS]; ALL_TAC] THEN
  ABBREV_TAC `w1 = \y:real^3. cmw_cut y % (u:real^3->real^K) y` THEN
  ABBREV_TAC `w2 = \y:real^3. (&1 - cmw_cut y) % (u:real^3->real^K) y` THEN
  ABBREV_TAC `w3 = \y:real^3. (w2:real^3->real^K)(bel_refl3 y)` THEN
  SUBGOAL_THEN
   `wan_rext (w1:real^3->real^K) = (\z. cmw_cut z % wan_rext u z) /\
    wan_rext (w2:real^3->real^K) = (\z. (&1 - cmw_cut z) % wan_rext u z)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["w1"; "w2"] THEN REWRITE_TAC[FUN_EQ_THM; wan_rext] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(w1:real^3->real^K) continuous_on sphere(vec 0,&1) /\
    (w2:real^3->real^K) continuous_on sphere(vec 0,&1) /\
    (w3:real^3->real^K) continuous_on sphere(vec 0,&1)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(w1:real^3->real^K) continuous_on sphere(vec 0,&1) /\
                  (w2:real^3->real^K) continuous_on sphere(vec 0,&1)` STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["w1"; "w2"] THEN CONJ_TAC THEN
      MATCH_MP_TAC CONTINUOUS_ON_MUL THEN ASM_REWRITE_TAC[o_DEF; LIFT_SUB] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[CONTINUOUS_ON_CONST];
      ASM_REWRITE_TAC[]] THEN
    EXPAND_TAC "w3" THEN
    SUBGOAL_THEN `(\y:real^3. (w2:real^3->real^K)(bel_refl3 y)) = w2 o bel_refl3` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[BEL_REFL3_LINEAR];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `sphere(vec 0:real^3,&1)` THEN
      ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_s2_w12 (w1:real^3->real^K) /\ wan_s2_w12 (w2:real^3->real^K) /\
    wan_s2_w12 (w3:real^3->real^K)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `wan_s2_w12 (w1:real^3->real^K) /\ wan_s2_w12 (w2:real^3->real^K)`
    STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[wan_s2_w12] THEN RULE_ASSUM_TAC(REWRITE_RULE[wan_s2_w12]) THEN
      CONJ_TAC THEN
      (MATCH_MP_TAC CMW_SHELL_MUL THEN EXISTS_TAC `&1` THEN
       ASM_REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
        [REWRITE_TAC[CMW_CUT_SMOOTH; LIFT_SUB] THEN
         TRY(MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
             REWRITE_TAC[CMT_OPEN_NONZERO; SMOOTH_MAP_ON_CONST; CMW_CUT_SMOOTH]);
         X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
         MP_TAC(SPEC `z:real^3` (CONJUNCT1 CMW_CUT_FACTS)) THEN REAL_ARITH_TAC]);
      ASM_REWRITE_TAC[]] THEN
    EXPAND_TAC "w3" THEN REWRITE_TAC[wan_s2_w12] THEN
    SUBGOAL_THEN `wan_rext (\y:real^3. (w2:real^3->real^K)(bel_refl3 y)) =
                  (\z. wan_rext w2 (bel_refl3 z))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; CMW_REFL_REXT]; ALL_TAC] THEN
    MP_TAC(ISPEC `wan_rext (w2:real^3->real^K)` CMW_REFL_W12) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[wan_s2_w12]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!y. y IN sphere(vec 0,&1) /\ &3 / &4 <= y$3 ==> (w1:real^3->real^K) y = vec 0) /\
    (!y. y IN sphere(vec 0,&1) /\ &3 / &4 <= y$3 ==> (w3:real^3->real^K) y = vec 0)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["w1"; "w3"; "w2"] THEN REWRITE_TAC[] THEN CONJ_TAC THEN
    REPEAT STRIP_TAC THENL
     [SUBGOAL_THEN `cmw_cut y = &0` (fun th -> REWRITE_TAC[th; VECTOR_MUL_LZERO]) THEN
      ASM_SIMP_TAC[];
      SUBGOAL_THEN `cmw_cut(bel_refl3 y) = &1`
        (fun th -> REWRITE_TAC[th; REAL_SUB_REFL; VECTOR_MUL_LZERO]) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `&1 / &2`)) (concl th))) THEN
      ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < eps / &4` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`w1:real^3->real^K`; `eps / &4`] CMW_NORTH_REG) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:real^3->real^K` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`w3:real^3->real^K`; `eps / &4`] CMW_NORTH_REG) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v3:real^3->real^K` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\y:real^3. (v1:real^3->real^K) y + v3(bel_refl3 y)` THEN
  SUBGOAL_THEN
   `wan_rext (\y:real^3. (v1:real^3->real^K) y + v3(bel_refl3 y)) =
    (\z. wan_rext v1 z + wan_rext v3 (bel_refl3 z))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    REWRITE_TAC[GSYM CMW_REFL_REXT] THEN REWRITE_TAC[wan_rext];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!y:real^3. (u:real^3->real^K) y = w1 y + (w3:real^3->real^K) (bel_refl3 y)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MAP_EVERY EXPAND_TAC ["w1"; "w3"; "w2"] THEN
    REWRITE_TAC[CMW_REFL3_FACTS] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_ADD_OPEN THEN
    ASM_REWRITE_TAC[CMT_OPEN_NONZERO; ETA_AX] THEN
    SUBGOAL_THEN `(\z. wan_rext (v3:real^3->real^K) (bel_refl3 z)) = wan_rext v3 o bel_refl3`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_COMPOSE_OPEN THEN
    EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
    ASM_REWRITE_TAC[CMT_OPEN_NONZERO; SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; CMW_REFL3_FACTS] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN THEN
    REWRITE_TAC[CMT_OPEN_NONZERO; BEL_REFL3_LINEAR];
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(u:real^3->real^K) y = w1 y + (w3:real^3->real^K) (bel_refl3 y)`
    SUBST1_TAC THENL
     [REWRITE_TAC[ASSUME `!y:real^3. (u:real^3->real^K) y = w1 y + (w3:real^3->real^K) (bel_refl3 y)`];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `norm((v1:real^3->real^K) y - w1 y) +
                norm((v3:real^3->real^K) (bel_refl3 y) - w3(bel_refl3 y))` THEN
    CONJ_TAC THENL [CONV_TAC NORM_ARITH; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < e /\ a < e / &4 /\ b < e / &4 ==> a + b < e`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. (wan_rext (v1:real^3->real^K) z + wan_rext (v3:real^3->real^K) (bel_refl3 z)) -
         wan_rext (u:real^3->real^K) z) =
    (\z. (\z. wan_rext v1 z - wan_rext (w1:real^3->real^K) z) z +
         (\z. wan_rext v3 z - wan_rext (w3:real^3->real^K) z) (bel_refl3 z))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^3` THEN
    SUBGOAL_THEN `wan_rext (u:real^3->real^K) z =
                  wan_rext (w1:real^3->real^K) z + wan_rext (w3:real^3->real^K) (bel_refl3 z)`
    SUBST1_TAC THENL
     [EXPAND_TAC "w3" THEN REWRITE_TAC[CMW_REFL_REXT; CMW_REFL3_FACTS] THEN
      REWRITE_TAC[ASSUME `wan_rext (w1:real^3->real^K) = (\z. cmw_cut z % wan_rext u z)`;
                  ASSUME `wan_rext (w2:real^3->real^K) = (\z. (&1 - cmw_cut z) % wan_rext u z)`] THEN
      VECTOR_ARITH_TAC;
      VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_w12 wan_shell (\z. wan_rext (v1:real^3->real^K) z - wan_rext (w1:real^3->real^K) z) /\
    wan_w12 wan_shell (\z. wan_rext (v3:real^3->real^K) z - wan_rext (w3:real^3->real^K) z)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC WAN_W12_SUB THEN REWRITE_TAC[ETA_AX] THEN CONJ_TAC THEN
    TRY(MATCH_MP_TAC CMW_REXT_C1_W12 THEN FIRST_ASSUM ACCEPT_TAC) THEN
    FIRST_ASSUM(ACCEPT_TAC o REWRITE_RULE[wan_s2_w12] o check (fun th ->
      fst(strip_comb(concl th)) = `wan_s2_w12:(real^3->real^K)->bool` &&
      (rand(concl th) = `w1:real^3->real^K` || rand(concl th) = `w3:real^3->real^K`)));
    ALL_TAC] THEN
  MP_TAC(MATCH_MP CMW_REFL_W12 (ASSUME
   `wan_w12 wan_shell (\z. wan_rext (v3:real^3->real^K) z - wan_rext (w3:real^3->real^K) z)`)) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`wan_shell`;
                 `\z. wan_rext (v1:real^3->real^K) z - wan_rext (w1:real^3->real^K) z`;
                 `\x. (\z. wan_rext (v3:real^3->real^K) z - wan_rext (w3:real^3->real^K) z)
                        (bel_refl3 x)`] WAN_DIR_ADD_LE) THEN
  REWRITE_TAC[CMT_SHELL_OPEN] THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a < e / &4 /\ b' < e / &4 /\ &0 < e
                           ==> x <= &2 * a + &2 * b' ==> x < e`) THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Area at most energy.  For a symmetric 3x3 matrix with a                   *)
(* kernel vector, trace^2 <= 2 trace(M^2) (Cauchy-Schwarz against the       *)
(* projection onto the orthogonal plane), hence 2 sqrt(e2) <= trace for the *)
(* Gram matrix of a radial extension (Euler relation); then approximation.  *)
(* ========================================================================= *)

let CMW_KERNEL_TRACE_SQ = prove
 (`!(M:real^3^3) z.
        transp M = M /\ ~(z = vec 0) /\ M ** z = vec 0
        ==> trace M pow 2 <= &2 * trace(M ** M)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (z:real^3) dot z` ASSUME_TAC THENL
   [ASM_SIMP_TAC[DOT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(M:real^3^3)$1$1 * (z:real^3)$1 + M$1$2 * z$2 + M$1$3 * z$3 = &0 /\
    M$2$1 * z$1 + M$2$2 * z$2 + M$2$3 * z$3 = &0 /\
    M$3$1 * z$1 + M$3$2 * z$2 + M$3$3 * z$3 = &0`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(M:real^3^3) ** z = vec 0` THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VEC_COMPONENT] THEN
    SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT; DIMINDEX_3; ARITH; DOT_3];
    ALL_TAC] THEN
  SUBGOAL_THEN `(M:real^3^3)$1$2 = M$2$1 /\ M$1$3 = M$3$1 /\ M$2$3 = M$3$2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o LAND_CONV) [GSYM th]) THEN
    SIMP_TAC[TRANSP_COMPONENT; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  ABBREV_TAC `P = (lambda i j. (if i = j then (z:real^3) dot z else &0) - z$i * z$j):real^3^3` THEN
  SUBGOAL_THEN
   `vectorize(M:real^3^3) dot vectorize(P:real^3^3) = ((z:real^3) dot z) * trace M`
  ASSUME_TAC THENL
   [REWRITE_TAC[DOT_VECTORIZE] THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "P" THEN
    SIMP_TAC[trace; matrix_mul; LAMBDA_BETA; DIMINDEX_3; ARITH; SUM_3; DOT_3] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `(M:real^3^3)$1$1 * (z:real^3)$1 + M$1$2 * z$2 + M$1$3 * z$3 = &0` THEN
    UNDISCH_TAC `(M:real^3^3)$2$1 * (z:real^3)$1 + M$2$2 * z$2 + M$2$3 * z$3 = &0` THEN
    UNDISCH_TAC `(M:real^3^3)$3$1 * (z:real^3)$1 + M$3$2 * z$2 + M$3$3 * z$3 = &0` THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(vectorize(P:real^3^3)) pow 2 = &2 * ((z:real^3) dot z) pow 2`
  ASSUME_TAC THENL
   [REWRITE_TAC[NORM_POW_2; DOT_VECTORIZE] THEN EXPAND_TAC "P" THEN
    SIMP_TAC[trace; matrix_mul; transp; LAMBDA_BETA; DIMINDEX_3; ARITH; SUM_3; DOT_3] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(vectorize(M:real^3^3)) pow 2 = trace(M ** M)` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_POW_2; DOT_VECTORIZE] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`vectorize(M:real^3^3)`; `vectorize(P:real^3^3)`] NORM_CAUCHY_SCHWARZ_ABS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(((z:real^3) dot z) * trace(M:real^3^3)) pow 2 <=
                (norm(vectorize(M:real^3^3)) * norm(vectorize(P:real^3^3))) pow 2`
  MP_TAC THENL
   [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(vectorize(M:real^3^3)) * norm(vectorize(P:real^3^3))` THEN
    ASM_REWRITE_TAC[REAL_ABS_LE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_POW_MUL] THEN
  SUBGOAL_THEN `&0 < ((z:real^3) dot z) pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SPEC_TAC(`((z:real^3) dot z) pow 2`,`q:real`) THEN
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM(MATCH_MP REAL_LE_LMUL_EQ (ASSUME `&0 < q`))] THEN
  ASM_REAL_ARITH_TAC);;

let CMW_AREA_DENS_LE = prove
 (`!(J:real^3^K) (A:real^K^K) z.
        ~(z = vec 0) /\ J ** z = vec 0 /\ transp A = A /\ (!v. &0 <= v dot (A ** v))
        ==> &2 * sqrt(p4_e2(transp J ** A ** J)) <= trace(transp J ** A ** J)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `transp(transp J ** (A:real^K^K) ** (J:real^3^K)) = transp J ** A ** J`
  ASSUME_TAC THENL
   [REWRITE_TAC[MATRIX_TRANSP_MUL; TRANSP_TRANSP] THEN ASM_REWRITE_TAC[MATRIX_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(transp J ** (A:real^K^K) ** (J:real^3^K)) ** z = vec 0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= trace(transp J ** (A:real^K^K) ** (J:real^3^K))` ASSUME_TAC THENL
   [REWRITE_TAC[CMT_TRACE_GRAM] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`transp J ** (A:real^K^K) ** (J:real^3^K)`; `z:real^3`]
                CMW_KERNEL_TRACE_SQ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `p4_e2(transp J ** (A:real^K^K) ** (J:real^3^K)) <=
                (trace(transp J ** A ** J) / &2) pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[p4_e2] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= t / &2 ==> &2 * x <= t`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt((trace(transp J ** (A:real^K^K) ** (J:real^3^K)) / &2) pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC]);;

let CMW_JX_PK_C1 = prove
 (`!(v:real^3->real^K) z.
        continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} v /\ ~(z = vec 0) /\
        (!i. 1 <= i /\ i <= 3 ==> wan_wd wan_shell i v z = partial_derivative i v z)
        ==> cmw_jx (cmw_pk wan_shell v z) = jacobian v (at z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{z:real^3 | ~(z = vec 0)}`; `v:real^3->real^K`] CMT_C1_FACTS) THEN
  ASM_REWRITE_TAC[CMT_OPEN_NONZERO; IN_ELIM_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3] THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[cmw_jx; LAMBDA_BETA; DIMINDEX_3; CMW_C3_PK] THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_BASIS; DIMINDEX_3; column; LAMBDA_BETA]);;

let CMW_AREA_LE_EN_C1 = prove
 (`!S (G:real^K->real^K^K) d (u:real^3->real^K).
        cm_target S G d /\
        continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext u)
        ==> cm_sarea G u <= cm_sen G u`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "tg") ASSUME_TAC) THEN
  USE_THEN "tg" (STRIP_ASSUME_TAC o MATCH_MP CMW_TARGET_FACTS) THEN
  USE_THEN "tg" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_target]) THEN
  ABBREV_TAC `v = wan_rext (u:real^3->real^K)` THEN
  MP_TAC(ISPEC `u:real^3->real^K` CMT_REXT_WD_AE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ae")) THEN
  ABBREV_TAC `N = {x | x IN wan_shell /\
                       ?i. 1 <= i /\ i <= 3 /\
                           ~(wan_wd wan_shell i (v:real^3->real^K) x = partial_derivative i v x)}` THEN
  SUBGOAL_THEN `negligible (N:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC
     `{x | x IN wan_shell /\ ~(wan_wd wan_shell 1 (v:real^3->real^K) x = partial_derivative 1 v x)}
      UNION {x | x IN wan_shell /\ ~(wan_wd wan_shell 2 v x = partial_derivative 2 v x)}
      UNION {x | x IN wan_shell /\ ~(wan_wd wan_shell 3 v x = partial_derivative 3 v x)}` THEN
    CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC NEGLIGIBLE_UNION THEN CONJ_TAC) THEN
      USE_THEN "ae" MATCH_MP_TAC THEN ARITH_TAC;
      EXPAND_TAC "N" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION] THEN
      GEN_TAC THEN STRIP_TAC THEN
      SUBGOAL_THEN `i = 1 \/ i = 2 \/ i = 3` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN wan_shell DIFF N
        ==> !i. 1 <= i /\ i <= 3
                ==> wan_wd wan_shell i (v:real^3->real^K) z = partial_derivative i v z`
  ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `K1 = cball(vec 0:real^3,&2) DIFF ball(vec 0,&1 / &2)` THEN
  SUBGOAL_THEN `compact (K1:real^3->bool) /\ K1 SUBSET {z:real^3 | ~(z = vec 0)} /\
                wan_shell SUBSET K1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K1" THEN SIMP_TAC[COMPACT_DIFF; COMPACT_CBALL; OPEN_BALL] THEN
    REWRITE_TAC[SUBSET; IN_DIFF; IN_CBALL_0; IN_BALL_0; IN_ELIM_THM; wan_shell] THEN
    CONJ_TAC THEN GEN_TAC THEN REWRITE_TAC[GSYM NORM_EQ_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^3->real^K) continuous_on {z:real^3 | ~(z = vec 0)}` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN EXISTS_TAC `1` THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `k = IMAGE (v:real^3->real^K) K1` THEN
  SUBGOAL_THEN `compact (k:real^K->bool) /\ (!z. z IN wan_shell ==> (v:real^3->real^K) z IN k) /\
                (v:real^3->real^K) measurable_on wan_shell`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; CMT_SHELL_OPEN] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_TRANS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `cmw_pk wan_shell (v:real^3->real^K) IN lspace wan_shell (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC CMW_PK_LSPACE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `lebesgue_measurable wan_shell` ASSUME_TAC THENL
   [SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; CMT_SHELL_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. lift(cmw_adens (G:real^K->real^K^K) ((v:real^3->real^K) z) (cmw_pk wan_shell v z)))
    integrable_on wan_shell /\
    (!i. (\z. lift(cmw_edens G i (v z) (cmw_pk wan_shell v z))) integrable_on wan_shell)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; GEN_TAC] THENL
     [MP_TAC(ISPEC `G:real^K->real^K^K` CMW_ADENS_FACTS) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN
      MP_TAC(ISPECL [`cmw_adens (G:real^K->real^K^K)`; `k:real^K->bool`; `wan_shell`;
                     `v:real^3->real^K`; `cmw_pk wan_shell (v:real^3->real^K)`]
                    CMW_FUNC_INTEGRABLE);
      MP_TAC(ISPECL [`G:real^K->real^K^K`; `i:num`] CMW_EDENS_FACTS) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN
      MP_TAC(ISPECL [`cmw_edens (G:real^K->real^K^K) i`; `k:real^K->bool`; `wan_shell`;
                     `v:real^3->real^K`; `cmw_pk wan_shell (v:real^3->real^K)`]
                    CMW_FUNC_INTEGRABLE)] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cm_sarea G (u:real^3->real^K) =
    &2 / &3 * drop(integral wan_shell
                    (\z. lift(cmw_adens (G:real^K->real^K^K) ((v:real^3->real^K) z)
                                        (cmw_pk wan_shell v z))))`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[cm_sarea; CMW_WGRAM_PK; cmw_adens]; ALL_TAC] THEN
  SUBGOAL_THEN
   `cm_sen G (u:real^3->real^K) =
    (drop(integral wan_shell (\z. lift(cmw_edens (G:real^K->real^K^K) 1 ((v:real^3->real^K) z)
                                           (cmw_pk wan_shell v z)))) +
     drop(integral wan_shell (\z. lift(cmw_edens G 2 (v z) (cmw_pk wan_shell v z)))) +
     drop(integral wan_shell (\z. lift(cmw_edens G 3 (v z) (cmw_pk wan_shell v z))))) / &3`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[cm_sen; wan_gdir; DIMINDEX_3; SUM_3] THEN
    SIMP_TAC[cmw_edens; CMW_C3_PK; ARITH];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM DROP_ADD; GSYM INTEGRAL_ADD; INTEGRABLE_ADD] THEN
  MATCH_MP_TAC(REAL_ARITH `&2 * a <= b ==> &2 / &3 * a <= b / &3`) THEN
  ASM_SIMP_TAC[GSYM DROP_CMUL; GSYM INTEGRAL_CMUL] THEN
  MATCH_MP_TAC INTEGRAL_DROP_LE_AE THEN EXISTS_TAC `N:real^3->bool` THEN
  ASM_SIMP_TAC[INTEGRABLE_ADD; INTEGRABLE_CMUL; DROP_ADD; DROP_CMUL; LIFT_DROP] THEN
  X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(z:real^3 = vec 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^3) IN wan_shell DIFF N` THEN
    REWRITE_TAC[IN_DIFF; wan_shell; IN_ELIM_THM; GSYM NORM_EQ_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `cmw_jx (cmw_pk wan_shell (v:real^3->real^K) z) = jacobian v (at z)` ASSUME_TAC THENL
   [MATCH_MP_TAC CMW_JX_PK_C1 THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `jacobian (v:real^3->real^K) (at z) ** z = vec 0` ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN
    MP_TAC(ISPECL [`u:real^3->real^K`; `z:real^3`; `&1`] CM_REXT_JACOBIAN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LT_01] THEN MATCH_MP_TAC CMT_C1_DIFFERENTIABLE_AT THEN
      EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
      ASM_REWRITE_TAC[CMT_OPEN_NONZERO; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`jacobian (v:real^3->real^K) (at z)`; `(G:real^K->real^K^K)((v:real^3->real^K) z)`;
                 `z:real^3`] CMW_AREA_DENS_LE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_TAC THEN
    TRANS_TAC REAL_LE_TRANS `lam * norm(v':real^K) pow 2` THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_LE_POW_2];
    ALL_TAC] THEN
  REWRITE_TAC[cmw_adens; cmw_edens] THEN
  REWRITE_TAC[ASSUME `cmw_jx (cmw_pk wan_shell (v:real^3->real^K) z) = jacobian v (at z)`] THEN
  REWRITE_TAC[CMT_TRACE_GRAM; DIMINDEX_3; SUM_3] THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= 3
                    ==> jacobian (v:real^3->real^K) (at z) ** basis i =
                        cmw_c3 (cmw_pk wan_shell v z) i`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC[GSYM(ASSUME `cmw_jx (cmw_pk wan_shell (v:real^3->real^K) z) = jacobian v (at z)`)] THEN
    ASM_SIMP_TAC[CMW_JX_COL];
    ASM_SIMP_TAC[ARITH] THEN REAL_ARITH_TAC]);;

let CMW_INV_SEQ_LIM = prove
 (`!f:num->real. (!n. &0 <= f n /\ f n < inv(&n + &1)) ==> (f ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `e:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv(&n + &1)` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&N)` THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    UNDISCH_TAC `~(N = 0)` THEN UNDISCH_TAC `N <= n:num` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_EQ] THEN
    MP_TAC(SPEC `N:num` REAL_POS) THEN REAL_ARITH_TAC]);;

let CMW_AREA_LE_EN = prove
 (`!S (G:real^K->real^K^K) d (u:real^3->real^K).
        WAN_S2_STEREO_STATEMENT (:K) /\ cm_target S G d /\ cm_smap S u
        ==> cm_sarea G u <= cm_sen G u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMW_TARGET_FACTS) THEN
  UNDISCH_TAC `cm_smap S (u:real^3->real^K)` THEN REWRITE_TAC[cm_smap] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!n. ?v. continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext v) /\
            (!y. y IN sphere(vec 0,&1) ==> norm(v y - (u:real^3->real^K) y) < inv(&n + &1)) /\
            wan_dir wan_shell (\z. wan_rext v z - wan_rext u z) < inv(&n + &1)`
  MP_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CMW_SLICE_REG THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `vn:num->real^3->real^K` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `k = {x + y:real^K | x IN S /\ y IN cball(vec 0,&1)}` THEN
  SUBGOAL_THEN `compact (k:real^K->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN MATCH_MP_TAC COMPACT_SUMS THEN ASM_REWRITE_TAC[COMPACT_CBALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^K. w IN S ==> w IN k` ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`w:real^K`; `vec 0:real^K`] THEN
    ASM_REWRITE_TAC[CENTRE_IN_CBALL; REAL_POS; VECTOR_ADD_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n y. y IN sphere(vec 0,&1) ==> (vn:num->real^3->real^K) n y IN k`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "k" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`(u:real^3->real^K) y`; `(vn:num->real^3->real^K) n y - u y`] THEN
    ASM_SIMP_TAC[IN_CBALL_0; VECTOR_ARITH `a + b - a:real^N = b`] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `inv(&n + &1)` THEN ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_INV_LE_1 THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `G:real^K->real^K^K`;
                 `vn:num->real^3->real^K`; `u:real^3->real^K`; `k:real^K->bool`]
                CMW_SLICE_CONV) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN UNDISCH_TAC `cm_target S (G:real^K->real^K^K) d` THEN
    REWRITE_TAC[cm_target] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
      EXISTS_TAC `wan_rext ((vn:num->real^3->real^K) n)` THEN
      SIMP_TAC[CM_REXT_SPHERE] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN EXISTS_TAC `1` THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET; IN_SPHERE_0; IN_ELIM_THM] THEN GEN_TAC THEN
        DISCH_THEN(fun th -> REWRITE_TAC[GSYM NORM_EQ_0; th]) THEN REAL_ARITH_TAC];
      GEN_TAC THEN MP_TAC(ISPEC `(vn:num->real^3->real^K) n` CMW_S2_C1_DIR) THEN
      ASM_SIMP_TAC[];
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      MP_TAC(SPEC `e:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
      DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN EXISTS_TAC `N:num` THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `inv(&n + &1)` THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&N)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      UNDISCH_TAC `~(N = 0)` THEN UNDISCH_TAC `N <= n:num` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_EQ] THEN
      MP_TAC(SPEC `N:num` REAL_POS) THEN REAL_ARITH_TAC;
      MATCH_MP_TAC CMW_INV_SEQ_LIM THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN
      MATCH_MP_TAC WAN_DIR_POS THEN MATCH_MP_TAC WAN_W12_SUB THEN
      MP_TAC(ISPEC `(vn:num->real^3->real^K) n` CMW_S2_C1_DIR) THEN
      ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[wan_s2_w12]) THEN
      SIMP_TAC[wan_s2_w12; ETA_AX] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LE) THEN
  EXISTS_TAC `\n. cm_sarea G ((vn:num->real^3->real^K) n)` THEN
  EXISTS_TAC `\n. cm_sen G ((vn:num->real^3->real^K) n)` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  MATCH_MP_TAC ALWAYS_EVENTUALLY THEN GEN_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC CMW_AREA_LE_EN_C1 THEN
  MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Uniform continuity of a sweep in C^0 (jointly) and in the                 *)
(* shell Dirichlet integral (in t).                                          *)
(* ========================================================================= *)

let CMW_SWEEP_JOINT_UNIF = prove
 (`!(W:real^3->real->real^K).
        continuous_map
          (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                         (subtopology euclideanreal (real_interval[&0,&1])),euclidean)
          (\(y,t). W y t)
        ==> !e. &0 < e
                ==> ?r. &0 < r /\
                        !y y' t t'. y IN sphere(vec 0,&1) /\ y' IN sphere(vec 0,&1) /\
                                    t IN real_interval[&0,&1] /\ t' IN real_interval[&0,&1] /\
                                    norm(y - y') < r /\ abs(t - t') < r
                                    ==> norm(W y t - W y' t') < e`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `KK = {x:real^(3,1)finite_sum | fstcart x IN sphere(vec 0,&1) /\
                                             drop(sndcart x) IN real_interval[&0,&1]}` THEN
  SUBGOAL_THEN `compact (KK:real^(3,1)finite_sum->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `KK = (sphere(vec 0:real^3,&1)) PCROSS (interval[vec 0:real^1,vec 1])`
    SUBST1_TAC THENL
     [EXPAND_TAC "KK" THEN
      REWRITE_TAC[EXTENSION; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_ELIM_THM;
                  FSTCART_PASTECART; SNDCART_PASTECART; IN_REAL_INTERVAL; IN_INTERVAL_1;
                  DROP_VEC];
      MATCH_MP_TAC COMPACT_PCROSS THEN REWRITE_TAC[COMPACT_SPHERE; COMPACT_INTERVAL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x:real^(3,1)finite_sum. (W:real^3->real->real^K) (fstcart x) (drop(sndcart x)))
    continuous_on KK`
  ASSUME_TAC THENL
   [REWRITE_TAC[CONTINUOUS_ON_SEQUENTIALLY; o_DEF] THEN
    MAP_EVERY X_GEN_TAC [`pp:num->real^(3,1)finite_sum`; `a:real^(3,1)finite_sum`] THEN
    EXPAND_TAC "KK" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`W:real^3->real->real^K`; `fstcart(a:real^(3,1)finite_sum)`;
                   `drop(sndcart(a:real^(3,1)finite_sum))`;
                   `\n. fstcart((pp:num->real^(3,1)finite_sum) n)`;
                   `\n. drop(sndcart((pp:num->real^(3,1)finite_sum) n))`] CMW_SWEEP_SEQ) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[LIFT_DROP; ETA_AX] THEN CONJ_TAC THEN
    MATCH_MP_TAC LIM_LINEAR THEN ASM_REWRITE_TAC[LINEAR_FSTCART; LINEAR_SNDCART];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^(3,1)finite_sum. (W:real^3->real->real^K) (fstcart x) (drop(sndcart x))`;
                 `KK:real^(3,1)finite_sum->bool`] COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ASM_REWRITE_TAC[uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  MAP_EVERY X_GEN_TAC [`y:real^3`; `y':real^3`; `t:real`; `t':real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`pastecart (y':real^3) (lift t')`;
                                `pastecart (y:real^3) (lift t)`]) THEN
  EXPAND_TAC "KK" THEN
  REWRITE_TAC[IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  ASM_REWRITE_TAC[dist] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[PASTECART_SUB] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `norm(y - y':real^3) + norm(lift t - lift t')` THEN
  CONJ_TAC THENL [REWRITE_TAC[NORM_PASTECART_LE]; ALL_TAC] THEN
  REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT] THEN ASM_REAL_ARITH_TAC);;

let CMW_DIR_SUB_SYM = prove
 (`!s (f:real^N->real^K) g.
        open s /\ wan_w12 s f /\ wan_w12 s g
        ==> wan_dir s (\z. g z - f z) = wan_dir s (\z. f z - g z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\x. (f:real^N->real^K) x - g x`] WAN_DIR_NEG) THEN
  ASM_SIMP_TAC[WAN_W12_SUB; VECTOR_NEG_SUB]);;

let CMW_DIR_TRI = prove
 (`!s (a:real^N->real^K) b c.
        open s /\ wan_w12 s a /\ wan_w12 s b /\ wan_w12 s c
        ==> wan_dir s (\z. a z - b z) <=
            &2 * wan_dir s (\z. a z - c z) + &2 * wan_dir s (\z. b z - c z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\x. (a:real^N->real^K) x - c x`;
                 `\x. (c:real^N->real^K) x - b x`] WAN_DIR_ADD_LE) THEN
  ASM_SIMP_TAC[WAN_W12_SUB] THEN
  REWRITE_TAC[VECTOR_ARITH `(a - c) + (c - b):real^N = a - b`; ETA_AX] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `b:real^N->real^K`; `c:real^N->real^K`] CMW_DIR_SUB_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

let CMW_SWEEP_DIR_UNIF = prove
 (`!S (W:real^3->real->real^K).
        cm_sweep S W
        ==> !e. &0 < e
                ==> ?r. &0 < r /\
                        !t t'. t IN real_interval[&0,&1] /\ t' IN real_interval[&0,&1] /\
                               abs(t - t') < r
                               ==> wan_dir wan_shell (\z. wan_rext (\y. W y t) z -
                                                          wan_rext (\y. W y t') z) < e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cm_sweep; cm_smap; wan_s2_w12] THEN STRIP_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!t. t IN real_interval[&0,&1]
                    ==> wan_w12 wan_shell (wan_rext (\y. (W:real^3->real->real^K) y t))`
  (LABEL_TAC "w12") THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REFUTE_THEN(MP_TAC o REWRITE_RULE[NOT_EXISTS_THM; TAUT `~(a /\ b) <=> a ==> ~b`;
                                    NOT_FORALL_THM; NOT_IMP; REAL_NOT_LT]) THEN
  DISCH_THEN(MP_TAC o GEN `n:num` o SPEC `inv(&n + &1)`) THEN
  REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
  REWRITE_TAC[SKOLEM_THM; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`tn:num->real`; `tn':num->real`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`vec 0:real^1`; `vec 1:real^1`] COMPACT_INTERVAL) THEN
  REWRITE_TAC[compact] THEN DISCH_THEN(MP_TAC o SPEC `\n. lift((tn:num->real) n)`) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `n:num` THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT1 o SPEC `n:num` o check (fun th ->
      can (find_term (fun t -> t = `tn':num->real`)) (concl th))) THEN
    REWRITE_TAC[IN_INTERVAL_1; IN_REAL_INTERVAL; DROP_VEC; LIFT_DROP];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^1` (X_CHOOSE_THEN `r:num->num` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `ts = drop l` THEN
  SUBGOAL_THEN `ts IN real_interval[&0,&1]` ASSUME_TAC THENL
   [EXPAND_TAC "ts" THEN
    UNDISCH_TAC `(l:real^1) IN interval[vec 0,vec 1]` THEN
    REWRITE_TAC[IN_INTERVAL_1; IN_REAL_INTERVAL; DROP_VEC];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `ts IN real_interval[&0,&1]`) o check (fun th ->
    can (find_term (fun t -> t = `atreal`)) (concl th))) THEN
  REWRITE_TAC[REALLIM_WITHINREAL; REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &5`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!s. s IN real_interval[&0,&1] /\ abs(s - ts) < dd
        ==> wan_dir wan_shell (\z. wan_rext (\y. (W:real^3->real->real^K) y s) z -
                                   wan_rext (\y. W y ts) z) < e / &5`
  (LABEL_TAC "near") THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_CASES_TAC `s:real = ts` THENL
     [ASM_REWRITE_TAC[VECTOR_SUB_REFL] THEN SIMP_TAC[WAN_DIR_ZERO; CMT_SHELL_OPEN] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `abs x < e ==> x < e`) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\k. lift((tn:num->real) ((r:num->num) k))) --> lift ts) sequentially`
  ASSUME_TAC THENL
   [EXPAND_TAC "ts" THEN REWRITE_TAC[LIFT_DROP] THEN
    UNDISCH_TAC `(((\n. lift((tn:num->real) n)) o (r:num->num)) --> l) sequentially` THEN
    REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP MONOTONE_BIGGER) THEN
  UNDISCH_TAC `((\k. lift((tn:num->real) ((r:num->num) k))) --> lift ts) sequentially` THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; DIST_LIFT] THEN
  DISCH_THEN(MP_TAC o SPEC `dd / &2`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  MP_TAC(SPEC `dd / &2` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `k = (r:num->num)(N1 + N2)` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
    can (find_term (fun t -> t = `tn':num->real`)) (concl th))) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `abs((tn:num->real) k - ts) < dd / &2` ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> t = `N1:num`)) (concl th) && is_forall(concl th))) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(&k + &1) < dd / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&N2)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    SUBGOAL_THEN `N2 <= k:num` MP_TAC THENL
     [EXPAND_TAC "k" THEN TRANS_TAC LE_TRANS `N1 + N2:num` THEN
      ASM_SIMP_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `~(N2 = 0)` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_EQ] THEN
    MP_TAC(SPEC `N2:num` REAL_POS) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_dir wan_shell (\z. wan_rext (\y. (W:real^3->real->real^K) y ((tn:num->real) k)) z -
                           wan_rext (\y. W y ((tn':num->real) k)) z) <=
    &2 * wan_dir wan_shell (\z. wan_rext (\y. W y (tn k)) z - wan_rext (\y. W y ts) z) +
    &2 * wan_dir wan_shell (\z. wan_rext (\y. W y (tn' k)) z - wan_rext (\y. W y ts) z)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMW_DIR_TRI THEN REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[CMT_SHELL_OPEN];
    ALL_TAC] THEN
  USE_THEN "near" (MP_TAC o SPEC `(tn:num->real) k`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  USE_THEN "near" (MP_TAC o SPEC `(tn':num->real) k`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Slices along a convergent sequence of times converge uniformly and in    *)
(* the Dirichlet seminorm.                                                   *)

let CMW_SWEEP_SEQ_CONV = prove
 (`!S (W:real^3->real->real^K) tn ts.
        cm_sweep S W /\ (!n. tn n IN real_interval[&0,&1]) /\ ts IN real_interval[&0,&1] /\
        (tn ---> ts) sequentially
        ==> (!e. &0 < e
                 ==> eventually (\n. !y. y IN sphere(vec 0,&1)
                                         ==> norm(W y (tn n) - W y ts) < e) sequentially) /\
            ((\n. wan_dir wan_shell (\z. wan_rext (\y. W y (tn n)) z -
                                         wan_rext (\y. W y ts) z)) ---> &0) sequentially`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN DISCH_THEN(LABEL_TAC "tlim") THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_sweep]) THEN
  CONJ_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THENL
   [MP_TAC(ISPEC `W:real^3->real->real^K` CMW_SWEEP_JOINT_UNIF) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
    USE_THEN "tlim" (MP_TAC o C MATCH_MP (ASSUME `&0 < r0`)) THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `r0:real`)) (concl th) &&
      can (find_term (fun t -> t = `y':real^3`)) (concl th))) THEN
    ASM_SIMP_TAC[VECTOR_SUB_REFL; NORM_0];
    MP_TAC(ISPECL [`S:real^K->bool`; `W:real^3->real->real^K`] CMW_SWEEP_DIR_UNIF) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
    USE_THEN "tlim" (MP_TAC o C MATCH_MP (ASSUME `&0 < r0`)) THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x < e ==> abs x < e`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC WAN_DIR_POS THEN MATCH_MP_TAC WAN_W12_SUB THEN REWRITE_TAC[ETA_AX] THEN
      ASM_MESON_TAC[cm_smap; wan_s2_w12];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]]]);;

let CMW_INV_SUBSEQ = prove
 (`!r. (!n. n <= r n) ==> ((\n. inv(&(r n) + &1)) ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `e:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN EXISTS_TAC `N:num` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&N)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ABS_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  SUBGOAL_THEN `N <= (r:num->num) n` MP_TAC THENL [ASM_MESON_TAC[LE_TRANS]; ALL_TAC] THEN
  UNDISCH_TAC `~(N = 0)` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_EQ] THEN
  MP_TAC(SPEC `(r:num->num) n` REAL_POS) THEN MP_TAC(SPEC `N:num` REAL_POS) THEN
  REAL_ARITH_TAC);;

(* Maps close to the slices along a convergent sequence of times converge   *)
(* to the limit slice.                                                       *)

let CMW_SEQ_NEAR = prove
 (`!S (W:real^3->real->real^K) (vn:num->real^3->real^K) tn ts bn.
        cm_sweep S W /\ (!n. tn n IN real_interval[&0,&1]) /\ ts IN real_interval[&0,&1] /\
        (tn ---> ts) sequentially /\ (bn ---> &0) sequentially /\
        (!n. cm_smap S (vn n)) /\
        (!n y. y IN sphere(vec 0,&1) ==> norm(vn n y - W y (tn n)) < bn n) /\
        (!n. wan_dir wan_shell (\z. wan_rext (vn n) z - wan_rext (\y. W y (tn n)) z) < bn n)
        ==> (!e. &0 < e
                 ==> eventually (\n. !y. y IN sphere(vec 0,&1) ==> norm(vn n y - W y ts) < e)
                                sequentially) /\
            ((\n. wan_dir wan_shell (\z. wan_rext (vn n) z - wan_rext (\y. W y ts) z)) ---> &0)
            sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `W:real^3->real->real^K`; `tn:num->real`; `ts:real`]
                CMW_SWEEP_SEQ_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "c0")
    (LABEL_TAC "d0" o REWRITE_RULE[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO])) THEN
  UNDISCH_TAC `(bn ---> &0) sequentially` THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN DISCH_THEN(LABEL_TAC "b0") THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_sweep]) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < e / &2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "c0" (MP_TAC o C MATCH_MP (ASSUME `&0 < e / &2`)) THEN
    USE_THEN "b0" (MP_TAC o C MATCH_MP (ASSUME `&0 < e / &2`)) THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
    EXISTS_TAC `N1 + N2:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `norm((vn:num->real^3->real^K) n y - W y ((tn:num->real) n)) < bn n /\
                  abs(bn n) < e / &2 /\ norm(W y (tn n) - W y ts) < e / &2`
    MP_TAC THENL
     [REPEAT CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> t = `vn:num->real^3->real^K`)) (concl th))) THEN
        ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> t = `N1:num`)) (concl th))) THEN
        ASM_ARITH_TAC;
        FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> t = `N2:num`)) (concl th))) THEN
        ANTS_TAC THENL
         [ASM_ARITH_TAC; DISCH_THEN(MATCH_MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[]]];
      ALL_TAC] THEN
    CONV_TAC NORM_ARITH;
    REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < e / &4` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "d0" (MP_TAC o C MATCH_MP (ASSUME `&0 < e / &4`)) THEN
    USE_THEN "b0" (MP_TAC o C MATCH_MP (ASSUME `&0 < e / &4`)) THEN
    DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
    EXISTS_TAC `N1 + N2:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `abs(bn (n:num)) < e / &4 /\
      abs(wan_dir wan_shell (\z. wan_rext (\y. (W:real^3->real->real^K) y ((tn:num->real) n)) z -
                                 wan_rext (\y. W y ts) z)) < e / &4`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        (can (find_term (fun t -> t = `N1:num`)) (concl th) ||
         can (find_term (fun t -> t = `N2:num`)) (concl th)))) THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `wan_dir wan_shell (\z. wan_rext ((vn:num->real^3->real^K) n) z -
                             wan_rext (\y. (W:real^3->real->real^K) y ((tn:num->real) n)) z)
      < bn n`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `wan_w12 wan_shell (wan_rext ((vn:num->real^3->real^K) n)) /\
      wan_w12 wan_shell (wan_rext (\y. (W:real^3->real->real^K) y ((tn:num->real) n))) /\
      wan_w12 wan_shell (wan_rext (\y. W y ts))`
    STRIP_ASSUME_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[cm_smap; wan_s2_w12]) THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`wan_shell`; `wan_rext ((vn:num->real^3->real^K) n)`;
                   `wan_rext (\y. (W:real^3->real->real^K) y ts)`;
                   `wan_rext (\y. (W:real^3->real->real^K) y ((tn:num->real) n))`]
                  CMW_DIR_TRI) THEN
    MP_TAC(ISPECL [`wan_shell`;
                   `wan_rext (\y. (W:real^3->real->real^K) y ((tn:num->real) n))`;
                   `wan_rext (\y. (W:real^3->real->real^K) y ts)`] CMW_DIR_SUB_SYM) THEN
    MP_TAC(ISPECL [`wan_shell`; `\z. wan_rext ((vn:num->real^3->real^K) n) z -
                                     wan_rext (\y. (W:real^3->real->real^K) y ts) z`]
                  WAN_DIR_POS) THEN
    ASM_SIMP_TAC[CMT_SHELL_OPEN; WAN_W12_SUB; ETA_AX] THEN
    ASM_REAL_ARITH_TAC]);;

(* A functional that is sequentially continuous at every slice (in C^0 and  *)
(* the Dirichlet seminorm) is uniformly continuous along the sweepout.      *)

let CMW_FUNC_UNIF = prove
 (`!S (W:real^3->real->real^K) (FF:(real^3->real^K)->real).
        cm_sweep S W /\
        (!un u. (!n. cm_smap S (un n)) /\ cm_smap S u /\
                (!e. &0 < e
                     ==> eventually (\n. !y. y IN sphere(vec 0,&1) ==> norm(un n y - u y) < e)
                                    sequentially) /\
                ((\n. wan_dir wan_shell (\z. wan_rext (un n) z - wan_rext u z)) ---> &0)
                sequentially
                ==> ((\n. FF (un n)) ---> FF u) sequentially)
        ==> !mu. &0 < mu
                 ==> ?eta. &0 < eta /\
                           !t v. t IN real_interval[&0,&1] /\ cm_smap S v /\
                                 (!y. y IN sphere(vec 0,&1) ==> norm(v y - W y t) < eta) /\
                                 wan_dir wan_shell (\z. wan_rext v z - wan_rext (\y. W y t) z)
                                 < eta
                                 ==> abs(FF v - FF (\y. W y t)) < mu`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cont")) THEN
  X_GEN_TAC `mu:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_sweep]) THEN
  REFUTE_THEN(MP_TAC o REWRITE_RULE[NOT_EXISTS_THM; TAUT `~(a /\ b) <=> a ==> ~b`;
                                    NOT_FORALL_THM; NOT_IMP; REAL_NOT_LT]) THEN
  DISCH_THEN(MP_TAC o GEN `n:num` o SPEC `inv(&n + &1)`) THEN
  REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
  REWRITE_TAC[SKOLEM_THM; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`tn:num->real`; `vn:num->real^3->real^K`] THEN
  DISCH_THEN(LABEL_TAC "seq") THEN
  MP_TAC(ISPECL [`vec 0:real^1`; `vec 1:real^1`] COMPACT_INTERVAL) THEN
  REWRITE_TAC[compact] THEN DISCH_THEN(MP_TAC o SPEC `\n. lift((tn:num->real) n)`) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `n:num` THEN
    USE_THEN "seq" (MP_TAC o CONJUNCT1 o CONJUNCT1 o SPEC `n:num`) THEN
    REWRITE_TAC[IN_INTERVAL_1; IN_REAL_INTERVAL; DROP_VEC; LIFT_DROP];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^1` (X_CHOOSE_THEN `r:num->num` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `ts = drop l` THEN
  SUBGOAL_THEN `ts IN real_interval[&0,&1]` ASSUME_TAC THENL
   [EXPAND_TAC "ts" THEN
    UNDISCH_TAC `(l:real^1) IN interval[vec 0,vec 1]` THEN
    REWRITE_TAC[IN_INTERVAL_1; IN_REAL_INTERVAL; DROP_VEC];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\k. (tn:num->real) ((r:num->num) k)) ---> ts) sequentially` ASSUME_TAC THENL
   [EXPAND_TAC "ts" THEN REWRITE_TAC[TENDSTO_REAL; o_DEF; LIFT_DROP] THEN
    UNDISCH_TAC `(((\n. lift((tn:num->real) n)) o (r:num->num)) --> l) sequentially` THEN
    REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP MONOTONE_BIGGER) THEN
  SUBGOAL_THEN `!n. (tn:num->real) ((r:num->num) n) IN real_interval[&0,&1]` ASSUME_TAC THENL
   [GEN_TAC THEN USE_THEN "seq" (MP_TAC o CONJUNCT1 o CONJUNCT1 o SPEC `(r:num->num) n`) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `W:real^3->real->real^K`;
                 `\k. (tn:num->real) ((r:num->num) k)`; `ts:real`] CMW_SWEEP_SEQ_CONV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "c0") (LABEL_TAC "d0")) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `W:real^3->real->real^K`;
                 `\n. (vn:num->real^3->real^K) ((r:num->num) n)`;
                 `\n. (tn:num->real) ((r:num->num) n)`; `ts:real`;
                 `\n. inv(&((r:num->num) n) + &1)`] CMW_SEQ_NEAR) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CMW_INV_SUBSEQ; ETA_AX];
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "c1") (LABEL_TAC "d1") o BETA_RULE)] THEN
  SUBGOAL_THEN
   `((\n. (FF:(real^3->real^K)->real)
            (\y. (W:real^3->real->real^K) y ((tn:num->real) ((r:num->num) n))))
     ---> FF (\y. W y ts)) sequentially /\
    ((\n. FF ((vn:num->real^3->real^K) (r n))) ---> FF (\y. W y ts)) sequentially`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "cont" (MP_TAC o ISPECL
        [`\n:num. \y. (W:real^3->real->real^K) y ((tn:num->real) ((r:num->num) n))`;
         `\y. (W:real^3->real->real^K) y ts`]);
      USE_THEN "cont" (MP_TAC o ISPECL
        [`\n:num. (vn:num->real^3->real^K) ((r:num->num) n)`;
         `\y. (W:real^3->real->real^K) y ts`])] THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC
   `((\n. (FF:(real^3->real^K)->real)
            (\y. (W:real^3->real->real^K) y ((tn:num->real) ((r:num->num) n))))
     ---> FF (\y. W y ts)) sequentially` THEN
  UNDISCH_TAC
   `((\n. (FF:(real^3->real^K)->real) ((vn:num->real^3->real^K) ((r:num->num) n)))
     ---> FF (\y. (W:real^3->real->real^K) y ts)) sequentially` THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `mu / &2`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  DISCH_THEN(MP_TAC o SPEC `mu / &2`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  USE_THEN "seq" (MP_TAC o CONJUNCT2 o SPEC `(r:num->num)(N1 + N2)`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N1 + N2:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N1 + N2:num`) THEN
  REWRITE_TAC[LE_ADD; LE_ADDR] THEN REAL_ARITH_TAC);;

let CMW_SLICE_CONV_S = prove
 (`!S (G:real^K->real^K^K) d (Q:real^K->real^K^K) (un:num->real^3->real^K) u.
        cm_target S G d /\
        smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) /\
        (!z. transp(Q z) = Q z) /\
        (!n. cm_smap S (un n)) /\ cm_smap S u /\
        (!e. &0 < e
             ==> eventually (\n. !y. y IN sphere(vec 0,&1) ==> norm(un n y - u y) < e)
                            sequentially) /\
        ((\n. wan_dir wan_shell (\z. wan_rext (un n) z - wan_rext u z)) ---> &0) sequentially
        ==> ((\n. cm_sen G (un n)) ---> cm_sen G u) sequentially /\
            ((\n. cm_sarea G (un n)) ---> cm_sarea G u) sequentially /\
            ((\n. cm_strace G Q (un n)) ---> cm_strace G Q u) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `Q:real^K->real^K^K`;
                 `un:num->real^3->real^K`; `u:real^3->real^K`; `S:real^K->bool`]
                CMW_SLICE_CONV) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[cm_smap]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_target]) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let CMW_SLICE_UNIF = prove
 (`!S (G:real^K->real^K^K) d (Q:real^K->real^K^K) (W:real^3->real->real^K).
        cm_target S G d /\
        smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) /\
        (!z. transp(Q z) = Q z) /\ cm_sweep S W
        ==> !mu. &0 < mu
                 ==> ?eta. &0 < eta /\
                           !t v. t IN real_interval[&0,&1] /\ cm_smap S v /\
                                 (!y. y IN sphere(vec 0,&1) ==> norm(v y - W y t) < eta) /\
                                 wan_dir wan_shell (\z. wan_rext v z - wan_rext (\y. W y t) z)
                                 < eta
                                 ==> abs(cm_sen G v - cm_sen G (\y. W y t)) < mu /\
                                     abs(cm_sarea G v - cm_sarea G (\y. W y t)) < mu /\
                                     abs(cm_strace G Q v - cm_strace G Q (\y. W y t)) < mu`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `mu:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `W:real^3->real->real^K`; `cm_sen (G:real^K->real^K^K)`]
                CMW_FUNC_UNIF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `Q:real^K->real^K^K`;
                   `un:num->real^3->real^K`; `u:real^3->real^K`] CMW_SLICE_CONV_S) THEN
    ASM_SIMP_TAC[];
    DISCH_THEN(MP_TAC o SPEC `mu:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `eta1:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `W:real^3->real->real^K`; `cm_sarea (G:real^K->real^K^K)`]
                CMW_FUNC_UNIF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `Q:real^K->real^K^K`;
                   `un:num->real^3->real^K`; `u:real^3->real^K`] CMW_SLICE_CONV_S) THEN
    ASM_SIMP_TAC[];
    DISCH_THEN(MP_TAC o SPEC `mu:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `eta2:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `W:real^3->real->real^K`;
                 `cm_strace (G:real^K->real^K^K) (Q:real^K->real^K^K)`] CMW_FUNC_UNIF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `Q:real^K->real^K^K`;
                   `un:num->real^3->real^K`; `u:real^3->real^K`] CMW_SLICE_CONV_S) THEN
    ASM_SIMP_TAC[];
    DISCH_THEN(MP_TAC o SPEC `mu:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `eta3:real` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `min eta1 (min eta2 eta3)` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_MESON_TAC[]);;


(* ========================================================================= *)
(* A smooth partition of unity in the time variable, Jensen's                *)
(* inequality for the squared norm, convexity of the Dirichlet integral and *)
(* a uniform bound for the Dirichlet integrals of the slices of a sweepout. *)
(* ========================================================================= *)

let cmw_chi = new_definition
 `cmw_chi m k t = smooth_step(&m * t - &k + &1) - smooth_step(&m * t - &k)`;;

let CMW_CHI_POS = prove
 (`!m k t. &0 <= cmw_chi m k t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmw_chi; REAL_SUB_LE] THEN
  MATCH_MP_TAC SMOOTH_STEP_MONO THEN REAL_ARITH_TAC);;

let CMW_CHI_SUM = prove
 (`!m t. t IN real_interval[&0,&1] ==> sum(0..m) (\k. cmw_chi m k t) = &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`0`; `m:num`]
    (INST [`\k. smooth_step(&m * t - &k + &1)`,`f:num->real`] SUM_DIFFS)) THEN
  REWRITE_TAC[LE_0; GSYM REAL_OF_NUM_ADD; REAL_ARITH `x - (k + &1) + &1 = x - k`;
              REAL_SUB_RZERO] THEN
  REWRITE_TAC[GSYM cmw_chi] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `smooth_step(&m * t + &1) = &1 /\ smooth_step(&m * t - &m) = &0`
    (fun th -> REWRITE_TAC[th] THEN REAL_ARITH_TAC) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_STEP_1 THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 <= x + &1`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS];
    MATCH_MP_TAC SMOOTH_STEP_0 THEN
    MATCH_MP_TAC(REAL_ARITH `x <= m * &1 ==> x - m <= &0`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]]);;

let CMW_CHI_SUPPORT = prove
 (`!m k t. ~(m = 0) /\ ~(cmw_chi m k t = &0) ==> abs(t - &k / &m) < inv(&m)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &m` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_OF_NUM_LT; LE_1]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= abs(&m * t - &k)` MP_TAC THENL
   [SUBGOAL_THEN `&m * t - &k = &m * (t - &k / &m)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < &m` THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_NZ) THEN
      CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&m * inv(&m)` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_LE_REFL];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  REWRITE_TAC[cmw_chi] THEN
  DISCH_THEN(DISJ_CASES_TAC o MATCH_MP
    (REAL_ARITH `&1 <= abs x ==> &1 <= x \/ x + &1 <= &0`)) THENL
   [ASM_SIMP_TAC[SMOOTH_STEP_1; REAL_ARITH `&1 <= x ==> &1 <= x + &1`] THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[SMOOTH_STEP_0; REAL_ARITH `x + &1 <= &0 ==> x <= &0`] THEN REAL_ARITH_TAC]);;

let CMW_CHI_AT0 = prove
 (`!m k. cmw_chi m k (&0) = if k = 0 then &1 else &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmw_chi; REAL_MUL_RZERO; REAL_SUB_LZERO] THEN
  COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[REAL_NEG_0; REAL_ADD_LID] THEN
    SIMP_TAC[SMOOTH_STEP_1; SMOOTH_STEP_0; REAL_LE_REFL] THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `&1 <= &k` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_OF_NUM_LE; LE_1]; ALL_TAC] THEN
    ASM_SIMP_TAC[SMOOTH_STEP_0; REAL_ARITH `&1 <= k ==> --k + &1 <= &0`;
                 REAL_ARITH `&1 <= k ==> --k <= &0`] THEN
    REAL_ARITH_TAC]);;

let CMW_CHI_AT1 = prove
 (`!m k. k <= m ==> cmw_chi m k (&1) = if k = m then &1 else &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cmw_chi; REAL_MUL_RID] THEN COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ADD_LID] THEN
    SIMP_TAC[SMOOTH_STEP_1; SMOOTH_STEP_0; REAL_LE_REFL] THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `&k + &1 <= &m` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SMOOTH_STEP_1; REAL_ARITH `k + &1 <= m ==> &1 <= m - k + &1`;
                 REAL_ARITH `k + &1 <= m ==> &1 <= m - k`] THEN
    REAL_ARITH_TAC]);;

let CMW_CHI_SMOOTH = prove
 (`!m k (s:real^N->bool) (f:real^N->real^1).
        open s /\ smooth_map_on s f
        ==> smooth_map_on s (\x. lift(cmw_chi m k (drop(f x))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cmw_chi; LIFT_SUB] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`;
                   `\x:real^N. lift(&m * drop((f:real^N->real^1) x) - &k + &1)`]
                  SMOOTH_MAP_ON_SMOOTH_STEP_COMPOSE);
    MP_TAC(ISPECL [`s:real^N->bool`;
                   `\x:real^N. lift(&m * drop((f:real^N->real^1) x) - &k)`]
                  SMOOTH_MAP_ON_SMOOTH_STEP_COMPOSE)] THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LIFT_ADD; LIFT_SUB; LIFT_CMUL; LIFT_DROP] THEN
  REPEAT((MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN ORELSE MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN) THEN
         ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN TRY CONJ_TAC) THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_CMUL_OPEN; SMOOTH_MAP_ON_CONST; ETA_AX]);;

(* Jensen's inequality for the squared norm. *)

let CMW_SQNORM_CONVEX = prove
 (`(\x:real^N. norm x pow 2) convex_on (:real^N)`,
  REWRITE_TAC[convex_on; IN_UNIV] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`; `u:real`; `v:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `v = &1 - u` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= b - a ==> a <= b`) THEN
  SUBGOAL_THEN `(u * norm(x:real^N) pow 2 + (&1 - u) * norm(y:real^N) pow 2) -
                norm(u % x + (&1 - u) % y) pow 2 = u * (&1 - u) * norm(x - y) pow 2`
  SUBST1_TAC THENL
   [REWRITE_TAC[NORM_POW_2; DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL; DOT_LSUB; DOT_RSUB] THEN
    REWRITE_TAC[DOT_SYM] THEN CONV_TAC REAL_RING;
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]]);;

let CMW_JENSEN_SQ = prove
 (`!(c:num->real) (a:num->real^N) m.
        (!k. k <= m ==> &0 <= c k) /\ sum(0..m) c = &1
        ==> norm(vsum(0..m) (\k. c k % a k)) pow 2 <= sum(0..m) (\k. c k * norm(a k) pow 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^N. norm x pow 2`; `(:real^N)`] CONVEX_ON_JENSEN) THEN
  REWRITE_TAC[CONVEX_UNIV; CMW_SQNORM_CONVEX; IN_UNIV] THEN
  DISCH_THEN(MP_TAC o SPECL [`m + 1`; `\i. (c:num->real)(i - 1)`;
                             `\i. (a:num->real^N)(i - 1)`]) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `!f:num->real. sum(1..m+1) f = sum(0..m) (\i. f(i + 1))`
    (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN SIMP_TAC[SUM_OFFSET_0; ARITH_RULE `1 <= m + 1`; ADD_SUB]; ALL_TAC] THEN
  SUBGOAL_THEN `!f:num->real^N. vsum(1..m+1) f = vsum(0..m) (\i. f(i + 1))`
    (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN SIMP_TAC[VSUM_OFFSET_0; ARITH_RULE `1 <= m + 1`; ADD_SUB]; ALL_TAC] THEN
  REWRITE_TAC[ADD_SUB; ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_ARITH_TAC);;

(* Weak partials of finite linear combinations, on an arbitrary set. *)

let CMW_WPD_VSUM = prove
 (`!(s:real^N->bool) i (h:num->real^N->real^K) (g:num->real^N->real^K) c m.
        (!k. k <= m ==> wan_wpd s i (h k) (g k))
        ==> wan_wpd s i (\x. vsum(0..m) (\k. c k % h k x))
                        (\x. vsum(0..m) (\k. c k % g k x))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[VSUM_CLAUSES_NUMSEG; LE_0] THEN DISCH_TAC THENL
   [MATCH_MP_TAC WAN_WPD_CMUL THEN REWRITE_TAC[ETA_AX] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[LE_REFL];
    MATCH_MP_TAC WAN_WPD_ADD THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_ARITH_TAC;
      MATCH_MP_TAC WAN_WPD_CMUL THEN REWRITE_TAC[ETA_AX] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC]]);;

let CMW_W12_VSUM = prove
 (`!(s:real^N->bool) (h:num->real^N->real^K) c m.
        (!k. k <= m ==> wan_w12 s (h k))
        ==> wan_w12 s (\x. vsum(0..m) (\k. c k % h k x)) /\
            !i. 1 <= i /\ i <= dimindex(:N)
                ==> wan_wpd s i (\x. vsum(0..m) (\k. c k % h k x))
                              (\x. vsum(0..m) (\k. c k % wan_wd s i (h k) x))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [UNDISCH_TAC `!k. k <= m ==> wan_w12 (s:real^N->bool) ((h:num->real^N->real^K) k)` THEN
    SPEC_TAC(`m:num`,`m:num`) THEN INDUCT_TAC THEN
    REWRITE_TAC[VSUM_CLAUSES_NUMSEG; LE_0] THEN DISCH_TAC THENL
     [MATCH_MP_TAC WAN_W12_CMUL THEN REWRITE_TAC[ETA_AX] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[LE_REFL];
      MATCH_MP_TAC WAN_W12_ADD THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_ARITH_TAC;
        MATCH_MP_TAC WAN_W12_CMUL THEN REWRITE_TAC[ETA_AX] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC]];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CMW_WPD_VSUM THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[WAN_WD_WORKS]]);;

(* Convexity of the Dirichlet integral. *)

let CMW_DIR_CONVEX = prove
 (`!(s:real^N->bool) (h:num->real^N->real^K) c m.
        open s /\ (!k. k <= m ==> wan_w12 s (h k)) /\
        (!k. k <= m ==> &0 <= c k) /\ sum(0..m) c = &1
        ==> wan_w12 s (\x. vsum(0..m) (\k. c k % h k x)) /\
            wan_dir s (\x. vsum(0..m) (\k. c k % h k x)) <=
            sum(0..m) (\k. c k * wan_dir s (h k))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `h:num->real^N->real^K`; `c:num->real`; `m:num`]
                CMW_W12_VSUM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:real^N->bool`;
                 `\x. vsum(0..m) (\k. (c:num->real) k % (h:num->real^N->real^K) k x)`;
                 `\i x. vsum(0..m) (\k. (c:num->real) k %
                                        wan_wd s i ((h:num->real^N->real^K) k) x)`]
                WAN_DIR_EQ) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[wan_dir; GSYM SUM_LMUL] THEN
  GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!k. k <= m
        ==> (\x. lift(norm(wan_wd s i ((h:num->real^N->real^K) k) x) pow 2)) integrable_on s`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN
    REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[WAN_WD_WORKS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(0..m) (\k. (c:num->real) k *
                   drop(integral s (\x. lift(norm(wan_wd s i ((h:num->real^N->real^K) k) x)
                                             pow 2)))) =
    drop(integral s (\x. vsum(0..m) (\k. c k % lift(norm(wan_wd s i (h k) x) pow 2))))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`\k:num x:real^N. (c:num->real) k %
                       lift(norm(wan_wd s i ((h:num->real^N->real^K) k) x) pow 2)`;
                   `s:real^N->bool`; `0..m`] INTEGRAL_VSUM) THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; LE_0] THEN
    ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[DROP_VSUM; o_DEF] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL];
    ALL_TAC] THEN
  MATCH_MP_TAC INTEGRAL_DROP_LE THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `&2`;
                   `\k:num x:real^N. (c:num->real) k %
                                     wan_wd s i ((h:num->real^N->real^K) k) x`;
                   `0..m`] LSPACE_VSUM) THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; LE_0; REAL_OF_NUM_LT; ARITH] THEN
    DISCH_THEN MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC LSPACE_CMUL THEN
    ASM_SIMP_TAC[WAN_WD_WORKS; ETA_AX];
    MP_TAC(ISPECL [`\k:num x:real^N. (c:num->real) k %
                       lift(norm(wan_wd s i ((h:num->real^N->real^K) k) x) pow 2)`;
                   `s:real^N->bool`; `0..m`] INTEGRABLE_VSUM) THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; LE_0] THEN DISCH_THEN MATCH_MP_TAC THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_SIMP_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[LIFT_DROP; DROP_VSUM; o_DEF; DROP_CMUL] THEN
    MATCH_MP_TAC CMW_JENSEN_SQ THEN ASM_REWRITE_TAC[]]);;

let CMW_GRID_POINT = prove
 (`!m j. ~(m = 0) /\ j <= m ==> &j / &m IN real_interval[&0,&1]`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &m` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_OF_NUM_LT; LE_1]; ALL_TAC] THEN
  ASM_SIMP_TAC[IN_REAL_INTERVAL; REAL_LE_DIV; REAL_POS; REAL_LE_LDIV_EQ; REAL_MUL_LID;
               REAL_OF_NUM_LE]);;

(* The Dirichlet integrals of the slices of a sweepout are bounded. *)

let CMW_SWEEP_DIR_BOUNDED = prove
 (`!S (W:real^3->real->real^K).
        cm_sweep S W
        ==> ?D. !t. t IN real_interval[&0,&1]
                    ==> wan_dir wan_shell (wan_rext (\y. W y t)) <= D`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!t. t IN real_interval[&0,&1]
                    ==> wan_w12 wan_shell (wan_rext (\y. (W:real^3->real->real^K) y t))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `cm_sweep (S:real^K->bool) (W:real^3->real->real^K)` THEN
    SIMP_TAC[cm_sweep; cm_smap; wan_s2_w12];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `W:real^3->real->real^K`] CMW_SWEEP_DIR_UNIF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "unif"))) THEN
  MP_TAC(SPEC `r:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `&2 + &2 * sum(0..m) (\j. wan_dir wan_shell
                                         (wan_rext (\y. (W:real^3->real->real^K) y (&j / &m))))` THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?k. k <= m /\ ~(cmw_chi m k t = &0)` STRIP_ASSUME_TAC THENL
   [REFUTE_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; TAUT `~(a /\ ~b) <=> a ==> b`]) THEN
    MP_TAC(SPECL [`m:num`; `t:real`] CMW_CHI_SUM) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `x = &0 ==> ~(x = &1)`) THEN MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&k / &m IN real_interval[&0,&1]` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CMW_GRID_POINT]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(t - &k / &m) < r` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `inv(&m)` THEN ASM_SIMP_TAC[CMW_CHI_SUPPORT];
    ALL_TAC] THEN
  USE_THEN "unif" (MP_TAC o SPECL [`t:real`; `&k / &m`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`wan_shell`;
                 `\z. wan_rext (\y. (W:real^3->real->real^K) y t) z -
                      wan_rext (\y. W y (&k / &m)) z`;
                 `wan_rext (\y. (W:real^3->real->real^K) y (&k / &m))`] WAN_DIR_ADD_LE) THEN
  ASM_SIMP_TAC[CMT_SHELL_OPEN; WAN_W12_SUB; VECTOR_SUB_ADD; ETA_AX] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `wan_dir wan_shell (wan_rext (\y. (W:real^3->real->real^K) y (&k / &m))) <=
    sum(0..m) (\j. wan_dir wan_shell (wan_rext (\y. W y (&j / &m))))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\j. wan_dir wan_shell
                          (wan_rext (\y. (W:real^3->real->real^K) y (&j / &m)))`;
                   `sum(0..m) (\j. wan_dir wan_shell
                          (wan_rext (\y. (W:real^3->real->real^K) y (&j / &m))))`;
                   `0..m`] SUM_POS_BOUND) THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; LE_0; REAL_LE_REFL] THEN
    ANTS_TAC THENL
     [X_GEN_TAC `j:num` THEN DISCH_TAC THEN MATCH_MP_TAC WAN_DIR_POS THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[CMW_GRID_POINT];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;


(* ========================================================================= *)
(* A globally C^1 retraction onto S near S with uniformly                    *)
(* continuous Jacobian, and the Dirichlet estimate for the difference of    *)
(* two maps composed with a C^1 map (chain rule, WAN_CHAIN_W12).            *)
(* ========================================================================= *)

let CMW_CSUPP_UNIF = prove
 (`!(g:real^N->real^M) k.
        g continuous_on (:real^N) /\ compact k /\ (!x. ~(x IN k) ==> g x = vec 0)
        ==> (?B. !x. norm(g x) <= B) /\
            (!e. &0 < e ==> ?r. &0 < r /\ !x y. norm(x - y) < r ==> norm(g x - g y) < e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`g:real^N->real^M`; `k:real^N->bool`] COMPACT_CONTINUOUS_IMAGE) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN EXISTS_TAC `B:real` THEN
    X_GEN_TAC `x:real^N` THEN ASM_CASES_TAC `(x:real^N) IN k` THEN
    ASM_SIMP_TAC[NORM_0; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  ABBREV_TAC `k1 = {x + y:real^N | x IN k /\ y IN cball(vec 0,&1)}` THEN
  SUBGOAL_THEN `compact(k1:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "k1" THEN MATCH_MP_TAC COMPACT_SUMS THEN ASM_REWRITE_TAC[COMPACT_CBALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y:real^N. x IN k /\ norm(y - x) <= &1 ==> y IN k1` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "k1" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`x:real^N`; `y - x:real^N`] THEN
    ASM_REWRITE_TAC[IN_CBALL_0] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^N->real^M`; `k1:real^N->bool`] COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]; ALL_TAC] THEN
  REWRITE_TAC[uniformly_continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `dd:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min dd (&1)` THEN ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LT_01] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `(x:real^N) IN k1 /\ (y:real^N) IN k1` THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^N`; `x:real^N`] o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `dd:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[dist];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(x - x:real^N) <= &1 /\ norm(y - y:real^N) <= &1 /\
                norm(y - x:real^N) <= &1 /\ norm(x - y:real^N) <= &1`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[VECTOR_SUB_REFL; NORM_0; REAL_POS] THEN
    MP_TAC(ISPECL [`x:real^N`; `y:real^N`] NORM_SUB) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~((x:real^N) IN k) /\ ~((y:real^N) IN k)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ASM_SIMP_TAC[VECTOR_SUB_REFL; NORM_0]]);;

let CMW_FD_JAC = prove
 (`!(P:real^K->real^L).
        continuously_differentiable 1 (:real^K) P
        ==> !y v. frechet_derivative P (at y) v = jacobian P (at y) ** v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(P:real^K->real^L) differentiable (at y)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`0`; `(:real^K)`; `P:real^K->real^L`]
                  CONTINUOUSLY_DIFFERENTIABLE_IMP_DIFFERENTIABLE_ON) THEN
    ASM_REWRITE_TAC[ARITH_RULE `SUC 0 = 1`] THEN
    SIMP_TAC[DIFFERENTIABLE_ON_EQ_DIFFERENTIABLE_AT; OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[jacobian] THEN
  ASM_SIMP_TAC[MATRIX_WORKS; LINEAR_FRECHET_DERIVATIVE]);;

(* A smooth retraction: psi times the closest-point map, psi = 1 near S.   *)

let CMW_RETRACTION = prove
 (`!S (G:real^K->real^K^K) d.
        cm_target S G d
        ==> ?P:real^K->real^K.
               continuously_differentiable 1 (:real^K) P /\
               (?B. !y. norm(vectorize(jacobian P (at y))) <= B) /\
               (!e. &0 < e
                    ==> ?r. &0 < r /\
                            !a b. norm(a - b) < r
                                  ==> norm(vectorize(jacobian P (at a)) -
                                           vectorize(jacobian P (at b))) < e) /\
               (!z. (?p. p IN S /\ dist(z,p) <= d / &2) ==> P z = closest_point S z)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_target]) THEN
  ABBREV_TAC `k = {x + y:real^K | x IN S /\ y IN cball(vec 0,d / &2)}` THEN
  SUBGOAL_THEN `compact(k:real^K->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN MATCH_MP_TAC COMPACT_SUMS THEN ASM_REWRITE_TAC[COMPACT_CBALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^K. (?p. p IN S /\ dist(z,p) <= d / &2) ==> z IN k` ASSUME_TAC THENL
   [X_GEN_TAC `z:real^K` THEN DISCH_THEN(X_CHOOSE_THEN `p:real^K` STRIP_ASSUME_TAC) THEN
    EXPAND_TAC "k" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`p:real^K`; `z - p:real^K`] THEN
    ASM_REWRITE_TAC[IN_CBALL_0; GSYM dist] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open(cm_tube S d:real^K->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[cm_tube; GRGE_TUBE_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN `(k:real^K->bool) SUBSET cm_tube S d` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^K` THEN EXPAND_TAC "k" THEN
    REWRITE_TAC[IN_ELIM_THM; cm_tube; IN_CBALL_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^K` (X_CHOOSE_THEN `v:real^K` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `p:real^K` THEN
    ASM_REWRITE_TAC[dist; VECTOR_ARITH `(p + v) - p:real^N = v`] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`cm_tube S d:real^K->bool`; `k:real^K->bool`] WAN_SMOOTH_URYSOHN) THEN
  ASM_REWRITE_TAC[wan_test] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:real^K->real` (CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `kp:real^K->bool` STRIP_ASSUME_TAC))
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `open((:real^K) DIFF kp)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN
   `continuously_differentiable 1 (:real^K) (\z:real^K. psi z % closest_point S z)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`1`; `(:real^K)`; `\z:real^K. psi z % closest_point S z`]
      CONTINUOUSLY_DIFFERENTIABLE_LOCAL_OPEN) THEN
    REWRITE_TAC[OPEN_UNIV; IN_UNIV; SUBSET_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
    X_GEN_TAC `z:real^K` THEN ASM_CASES_TAC `(z:real^K) IN cm_tube S d` THENL
     [EXISTS_TAC `cm_tube S d:real^K->bool` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`1`; `cm_tube S d:real^K->bool`; `\x:real^K. lift(psi x)`;
                     `closest_point (S:real^K->bool)`]
                    CONTINUOUSLY_DIFFERENTIABLE_MUL_DROP_OPEN) THEN
      REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN EXISTS_TAC `(:real^K)` THEN
        REWRITE_TAC[SUBSET_UNIV] THEN ASM_MESON_TAC[smooth_map_on];
        ASM_MESON_TAC[smooth_map_on]];
      EXISTS_TAC `(:real^K) DIFF kp` THEN
      SUBGOAL_THEN `~((z:real^K) IN kp)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
      MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_EQ_OPEN THEN
      EXISTS_TAC `\z:real^K. vec 0:real^K` THEN
      ASM_SIMP_TAC[IN_DIFF; IN_UNIV; CONTINUOUSLY_DIFFERENTIABLE_CONST; VECTOR_MUL_LZERO]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^K. ~(z IN kp)
               ==> vectorize(jacobian (\z:real^K. psi z % closest_point S z) (at z)) = vec 0`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^K` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `((\z:real^K. psi z % closest_point S z) has_derivative (\h. vec 0)) (at z)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
      MAP_EVERY EXISTS_TAC [`\z:real^K. vec 0:real^K`; `(:real^K) DIFF kp`] THEN
      ASM_SIMP_TAC[IN_DIFF; IN_UNIV; HAS_DERIVATIVE_CONST; VECTOR_MUL_LZERO];
      ALL_TAC] THEN
    REWRITE_TAC[jacobian] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    REWRITE_TAC[MATRIX_0; VECTORIZE_0];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\a. vectorize(jacobian (\z:real^K. psi z % closest_point S z) (at a)))
    continuous_on (:real^K)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM CONTINUOUS_ON_MATRIX_VECTORIZE] THEN X_GEN_TAC `v:real^K` THEN
    MP_TAC(ISPEC `\z:real^K. psi z % closest_point S z` CMW_FD_JAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    MP_TAC(ISPECL [`0`; `\z:real^K. psi z % closest_point S z`]
                  CONTINUOUSLY_DIFFERENTIABLE_FRECHET_UNIV) THEN
    ASM_REWRITE_TAC[ARITH_RULE `SUC 0 = 1`; CONTINUOUSLY_DIFFERENTIABLE_0] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^K`) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\a. vectorize(jacobian (\z:real^K. psi z % closest_point S z) (at a))`;
                 `kp:real^K->bool`] CMW_CSUPP_UNIF) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `B:real`) ASSUME_TAC) THEN
  EXISTS_TAC `\z:real^K. psi z % closest_point S z` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `z:real^K` THEN DISCH_TAC THEN
  SUBGOAL_THEN `psi(z:real^K) = &1` (fun th -> REWRITE_TAC[th; VECTOR_MUL_LID]) THEN
  ASM_MESON_TAC[]);;

(* Pointwise estimate behind the chain-rule Dirichlet bound. *)

let CMW_JAC_DIFF_BOUND = prove
 (`!(A:real^K^K) (C:real^K^K) (a:real^K) b B om.
        norm(vectorize A) <= B /\ norm(vectorize A - vectorize C) <= om
        ==> norm(A ** a - C ** b) pow 2 <=
            &2 * B pow 2 * norm(a - b) pow 2 + &2 * om pow 2 * norm b pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(A:real^K^K) ** (a:real^K) - (C:real^K^K) ** (b:real^K) =
                A ** (a - b) + (A - C) ** b` SUBST1_TAC THENL
   [REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; MATRIX_VECTOR_MUL_SUB_RDISTRIB] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(B * norm(a - b:real^K) + om * norm(b:real^K)) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm((A:real^K^K) ** (a - b:real^K)) +
                norm(((A:real^K^K) - (C:real^K^K)) ** (b:real^K))` THEN
    REWRITE_TAC[NORM_TRIANGLE] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `norm(vectorize(A:real^K^K)) * norm(a - b:real^K)`;
      EXISTS_TAC `norm(vectorize((A:real^K^K) - (C:real^K^K))) * norm(b:real^K)`] THEN
    REWRITE_TAC[COMPATIBLE_NORM_VECTORIZE] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[NORM_POS_LE; VECTORIZE_SUB];
    MP_TAC(SPEC `B * norm(a - b:real^K) - om * norm(b:real^K)` REAL_LE_POW_2) THEN
    REAL_ARITH_TAC]);;

(* Dirichlet estimate for P o u - P o w. *)

let CMW_CHAIN_DIR_EST = prove
 (`!(s:real^N->bool) (u:real^N->real^K) w (P:real^K->real^K) B om.
        open s /\ bounded s /\ wan_w12 s u /\ wan_w12 s w /\
        continuously_differentiable 1 (:real^K) P /\
        (!y. norm(vectorize(jacobian P (at y))) <= B) /\
        (!x. x IN s
             ==> norm(vectorize(jacobian P (at (u x))) -
                      vectorize(jacobian P (at (w x)))) <= om)
        ==> wan_w12 s (\z. P(u z) - P(w z)) /\
            wan_dir s (\z. P(u z) - P(w z)) <=
            &2 * B pow 2 * wan_dir s (\z. u z - w z) + &2 * om pow 2 * wan_dir s w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y v. frechet_derivative (P:real^K->real^K) (at y) v = jacobian P (at y) ** v`
  ASSUME_TAC THENL [ASM_SIMP_TAC[CMW_FD_JAC]; ALL_TAC] THEN
  SUBGOAL_THEN `?B. !y. onorm(frechet_derivative (P:real^K->real^K) (at y)) <= B`
  ASSUME_TAC THENL
   [EXISTS_TAC `B:real` THEN X_GEN_TAC `y:real^K` THEN
    SUBGOAL_THEN `frechet_derivative (P:real^K->real^K) (at y) = (\v. jacobian P (at y) ** v)`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(vectorize(jacobian (P:real^K->real^K) (at y)))` THEN
    ASM_REWRITE_TAC[ONORM_LE_NORM_VECTORIZE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:N)`; `(:K)`; `(:K)`] WAN_CHAIN_W12) THEN
  REWRITE_TAC[WAN_CHAIN_W12_STATEMENT] THEN
  DISCH_THEN(fun th ->
    MP_TAC(ISPECL [`s:real^N->bool`; `u:real^N->real^K`; `P:real^K->real^K`] th) THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `w:real^N->real^K`; `P:real^K->real^K`] th)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dw")) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "du")) THEN
  SUBGOAL_THEN `wan_w12 s (\z. (P:real^K->real^K)(u z) - P((w:real^N->real^K) z))`
  ASSUME_TAC THENL [MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 s (\z. (u:real^N->real^K) z - w z)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[wan_dir; GSYM SUM_LMUL; GSYM SUM_ADD_NUMSEG] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\x. lift(norm(wan_wd s i (\z. (P:real^K->real^K)(u z) - P((w:real^N->real^K) z)) x)
              pow 2)) integrable_on s /\
    (\x. lift(norm(wan_wd s i (\z. (u:real^N->real^K) z - w z) x) pow 2)) integrable_on s /\
    (\x. lift(norm(wan_wd s i (w:real^N->real^K) x) pow 2)) integrable_on s`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN
    REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[WAN_WD_WORKS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `negligible {x | x IN s /\
                    ~(wan_wd s i (\z. (P:real^K->real^K)(u z) - P((w:real^N->real^K) z)) x =
                      jacobian P (at (u x)) ** wan_wd s i (u:real^N->real^K) x -
                      jacobian P (at (w x)) ** wan_wd s i w x)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_WD_UNIQUE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC WAN_WPD_SUB THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `negligible {x | x IN s /\
                    ~(wan_wd s i (\z. (u:real^N->real^K) z - w z) x =
                      wan_wd s i u x - wan_wd s i (w:real^N->real^K) x)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_WD_UNIQUE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC WAN_WPD_SUB THEN REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[WAN_WD_WORKS];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM DROP_CMUL; GSYM INTEGRAL_CMUL; GSYM DROP_ADD; GSYM INTEGRAL_ADD;
               INTEGRABLE_CMUL] THEN
  MATCH_MP_TAC INTEGRAL_DROP_LE_AE THEN
  EXISTS_TAC
   `{x | x IN s /\
         ~(wan_wd s i (\z. (P:real^K->real^K)(u z) - P((w:real^N->real^K) z)) x =
           jacobian P (at (u x)) ** wan_wd s i (u:real^N->real^K) x -
           jacobian P (at (w x)) ** wan_wd s i w x)} UNION
    {x | x IN s /\
         ~(wan_wd s i (\z. (u:real^N->real^K) z - w z) x =
           wan_wd s i u x - wan_wd s i (w:real^N->real^K) x)}` THEN
  ASM_SIMP_TAC[INTEGRABLE_CMUL; INTEGRABLE_ADD; NEGLIGIBLE_UNION_EQ] THEN
  X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[IN_DIFF; IN_UNION; IN_ELIM_THM; DE_MORGAN_THM;
              TAUT `~(a /\ ~b) <=> a ==> b`] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[DROP_ADD; DROP_CMUL; LIFT_DROP] THEN
  MATCH_MP_TAC CMW_JAC_DIFF_BOUND THEN ASM_SIMP_TAC[]);;


(* ========================================================================= *)
(* The regularized sweepout of CM Lemma D.1,                                 *)
(*   W'(y,t) = P(sum_k chi_k(t) v_k(y)),                                     *)
(* its joint C^1 property, its end slices and its C^0 and Dirichlet          *)
(* estimates in terms of the accuracy of the slices v_k.                     *)
(* ========================================================================= *)

let cmw_d1 = new_definition
 `cmw_d1 (P:real^K->real^K) m (v:num->real^3->real^K) y t =
    P(vsum(0..m) (\k. cmw_chi m k t % v k y))`;;

let CMW_C1_SWEEP_CONT = prove
 (`!(W:real^3->real->real^K).
        continuously_differentiable 1
          {x:real^(3,1)finite_sum |
             ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1]}
          (\x. W (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x)))
        ==> continuous_map
              (prod_topology (subtopology euclidean (sphere(vec 0:real^3,&1)))
                             (subtopology euclideanreal (real_interval[&0,&1])),euclidean)
              (\(y,t). W y t)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(\(y,t). (W:real^3->real->real^K) y t) = (\x. W (FST x) (SND x))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM]; ALL_TAC] THEN
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
    EXISTS_TAC `1` THEN ASM_REWRITE_TAC[]] THEN
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
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PAIR_THM; TOPSPACE_PROD_TOPOLOGY; IN_CROSS;
                TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY;
                IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; FST; SND] THEN
    SIMP_TAC[P4_SPHERE_NONZERO]]);;

let CMW_C1_SLICE_SMAP = prove
 (`!S (W:real^3->real->real^K) t.
        continuously_differentiable 1
          {x:real^(3,1)finite_sum |
             ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1]}
          (\x. W (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x))) /\
        (!y. y IN sphere(vec 0,&1) ==> W y t IN S) /\ t IN real_interval[&0,&1]
        ==> cm_smap S (\y. W y t) /\
            continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext (\y. W y t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`W:real^3->real->real^K`; `t:real`] CMW_SWEEP_C1_SLICE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[cm_smap; wan_s2_w12] THEN
  ASM_SIMP_TAC[CMW_REXT_C1_W12] THEN
  MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `wan_rext (\y. (W:real^3->real->real^K) y t)` THEN CONJ_TAC THENL
   [SIMP_TAC[CM_REXT_SPHERE]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
    EXISTS_TAC `1` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[P4_SPHERE_NONZERO]]);;

(* The end slices of a sweepout are constant; as slices they are exact. *)

let CMW_CONST_SLICE_FACTS = prove
 (`!S (W:real^3->real->real^K) t eps.
        cm_sweep S W /\ (t = &0 \/ t = &1) /\ &0 < eps
        ==> continuously_differentiable 1 {z:real^3 | ~(z = vec 0)}
              (wan_rext (\y. W (basis 3) t)) /\
            (!y. y IN sphere(vec 0,&1) ==> norm(W (basis 3) t - W y t) < eps) /\
            wan_dir wan_shell (\z. wan_rext (\y. W (basis 3) t) z - wan_rext (\y. W y t) z)
            < eps`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMW_SWEEP_FACTS) THEN
  SUBGOAL_THEN `!y. y IN sphere(vec 0,&1) ==> (W:real^3->real->real^K) y t = W (basis 3) t`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[wan_rext] THEN MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_CONST THEN
    REWRITE_TAC[CMT_OPEN_NONZERO];
    ASM_SIMP_TAC[VECTOR_SUB_REFL; NORM_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`wan_shell`;
                 `\z. wan_rext (\y. (W:real^3->real->real^K) (basis 3) t) z -
                      wan_rext (\y. W y t) z`;
                 `\z:real^3. vec 0:real^K`] CMW_DIR_EQ_ON) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[wan_rext] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `z:real^3` CMT_SHELL_NONZERO) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(ASSUME_TAC o MATCH_MP P4_RADIAL_SPHERE) THEN
    ASM_SIMP_TAC[VECTOR_SUB_REFL];
    DISCH_THEN SUBST1_TAC THEN SIMP_TAC[WAN_DIR_ZERO; CMT_SHELL_OPEN] THEN
    ASM_REWRITE_TAC[]]);;

(* The slices v_k: exact constants at t = 0 and t = 1, regularized inside. *)

let CMW_D1_SLICES = prove
 (`!S (W:real^3->real->real^K) eps m.
        WAN_S2_STEREO_STATEMENT (:K) /\ cm_sweep S W /\ &0 < eps /\ ~(m = 0)
        ==> ?v:num->real^3->real^K.
               v 0 = (\y. W (basis 3) (&0)) /\ v m = (\y. W (basis 3) (&1)) /\
               !k. k <= m
                   ==> continuously_differentiable 1 {z:real^3 | ~(z = vec 0)}
                         (wan_rext (v k)) /\
                       (!y. y IN sphere(vec 0,&1) ==> norm(v k y - W y (&k / &m)) < eps) /\
                       wan_dir wan_shell (\z. wan_rext (v k) z -
                                              wan_rext (\y. W y (&k / &m)) z) < eps`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. ?v:real^3->real^K.
        t IN real_interval[&0,&1]
        ==> continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext v) /\
            (!y. y IN sphere(vec 0,&1) ==> norm(v y - (W:real^3->real->real^K) y t) < eps) /\
            wan_dir wan_shell (\z. wan_rext v z - wan_rext (\y. W y t) z) < eps`
  MP_TAC THENL
   [X_GEN_TAC `t:real` THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `cm_smap S (\y. (W:real^3->real->real^K) y t)` MP_TAC THENL
     [UNDISCH_TAC `cm_sweep (S:real^K->bool) (W:real^3->real->real^K)` THEN
      REWRITE_TAC[cm_sweep] THEN ASM_SIMP_TAC[];
      REWRITE_TAC[cm_smap] THEN STRIP_TAC] THEN
    MP_TAC(ISPECL [`\y. (W:real^3->real->real^K) y t`; `eps:real`] CMW_SLICE_REG) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `vr:real->real^3->real^K`)] THEN
  EXISTS_TAC `\k. if k = 0 then (\y. (W:real^3->real->real^K) (basis 3) (&0))
                  else if k = m then (\y. W (basis 3) (&1))
                  else (vr:real->real^3->real^K) (&k / &m)` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(&m = &0)` ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_OF_NUM_EQ]; ALL_TAC] THEN
  ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[real_div; REAL_MUL_LZERO] THEN
    MATCH_MP_TAC CMW_CONST_SLICE_FACTS THEN EXISTS_TAC `S:real^K->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `k:num = m` THEN ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[REAL_DIV_REFL] THEN
    MATCH_MP_TAC CMW_CONST_SLICE_FACTS THEN EXISTS_TAC `S:real^K->bool` THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[CMW_GRID_POINT]]);;

(* Joint C^1 property of the regularized sweepout. *)

let CMW_D1_C1 = prove
 (`!(P:real^K->real^K) m (v:num->real^3->real^K).
        continuously_differentiable 1 (:real^K) P /\
        (!k. k <= m
             ==> continuously_differentiable 1 {z:real^3 | ~(z = vec 0)} (wan_rext (v k)))
        ==> continuously_differentiable 1
              {x:real^(3,1)finite_sum |
                 ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1]}
              (\x. cmw_d1 P m v (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open {x:real^(3,1)finite_sum | ~(fstcart x = vec 0)}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`fstcart:real^(3,1)finite_sum->real^3`; `{z:real^3 | ~(z = vec 0)}`]
                  CONTINUOUS_OPEN_PREIMAGE_UNIV) THEN
    REWRITE_TAC[CMT_OPEN_NONZERO; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    SIMP_TAC[LINEAR_CONTINUOUS_AT; LINEAR_FSTCART];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN
  EXISTS_TAC `{x:real^(3,1)finite_sum | ~(fstcart x = vec 0)}` THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[cmw_d1] THEN
  SUBGOAL_THEN
   `(\x:real^(3,1)finite_sum.
       (P:real^K->real^K)(vsum(0..m) (\k. cmw_chi m k (drop(sndcart x)) %
                                         (v:num->real^3->real^K) k
                                         (inv(norm(fstcart x)) % fstcart x)))) =
    P o (\x. vsum(0..m) (\k. drop(lift(cmw_chi m k (drop(sndcart x)))) %
                             wan_rext (v k) (fstcart x)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; wan_rext; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_COMPOSE_OPEN THEN
  EXISTS_TAC `(:real^K)` THEN ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
  MP_TAC(ISPECL [`1`; `{x:real^(3,1)finite_sum | ~(fstcart x = vec 0)}`;
                 `\k x. drop(lift(cmw_chi m k (drop(sndcart x)))) %
                        wan_rext ((v:num->real^3->real^K) k) (fstcart x)`; `0..m`]
                CONTINUOUSLY_DIFFERENTIABLE_VSUM_OPEN) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; LE_0] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`1`; `{x:real^(3,1)finite_sum | ~(fstcart x = vec 0)}`;
                 `\x:real^(3,1)finite_sum. lift(cmw_chi m k (drop(sndcart x)))`;
                 `\x:real^(3,1)finite_sum. wan_rext ((v:num->real^3->real^K) k) (fstcart x)`]
                CONTINUOUSLY_DIFFERENTIABLE_MUL_DROP_OPEN) THEN
  ASM_REWRITE_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`m:num`; `k:num`; `{x:real^(3,1)finite_sum | ~(fstcart x = vec 0)}`;
                   `sndcart:real^(3,1)finite_sum->real^1`] CMW_CHI_SMOOTH) THEN
    ASM_REWRITE_TAC[smooth_map_on] THEN ANTS_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN THEN
      ASM_REWRITE_TAC[LINEAR_SNDCART];
      SIMP_TAC[]];
    SUBGOAL_THEN
     `(\x:real^(3,1)finite_sum. wan_rext ((v:num->real^3->real^K) k) (fstcart x)) =
      wan_rext (v k) o fstcart`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_COMPOSE_OPEN THEN
    EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
    ASM_SIMP_TAC[CMT_OPEN_NONZERO; CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN; LINEAR_FSTCART] THEN
    SET_TAC[]]);;

let CMW_D1_ENDS = prove
 (`!(P:real^K->real^K) m (v:num->real^3->real^K) y.
        cmw_d1 P m v y (&0) = P(v 0 y) /\ cmw_d1 P m v y (&1) = P(v m y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmw_d1] THEN CONJ_TAC THEN AP_TERM_TAC THENL
   [TRANS_TAC EQ_TRANS `vsum(0..m) (\k. if k = 0 then (v:num->real^3->real^K) 0 y else vec 0)`;
    TRANS_TAC EQ_TRANS `vsum(0..m) (\k. if k = m then (v:num->real^3->real^K) m y else vec 0)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REWRITE_TAC[CMW_CHI_AT0] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LID; VECTOR_MUL_LZERO];
    REWRITE_TAC[VSUM_DELTA; IN_NUMSEG; LE_0; LE_REFL];
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[CMW_CHI_AT1] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LID; VECTOR_MUL_LZERO];
    REWRITE_TAC[VSUM_DELTA; IN_NUMSEG; LE_0; LE_REFL]]);;

(* C^0 estimate for the convex combination of the slices. *)

let CMW_D1_C0 = prove
 (`!(W:real^3->real->real^K) m (v:num->real^3->real^K) c0.
        ~(m = 0) /\
        (!y t t'. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1] /\
                  t' IN real_interval[&0,&1] /\ abs(t - t') < inv(&m)
                  ==> norm(W y t - W y t') < c0 / &2) /\
        (!k y. k <= m /\ y IN sphere(vec 0,&1) ==> norm(v k y - W y (&k / &m)) < c0 / &2)
        ==> !y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]
                  ==> norm(vsum(0..m) (\k. cmw_chi m k t % v k y) - W y t) <= c0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `vsum(0..m) (\k. cmw_chi m k t % (v:num->real^3->real^K) k y) - W y t =
    vsum(0..m) (\k. cmw_chi m k t % (v k y - W y t))`
  SUBST1_TAC THENL
   [REWRITE_TAC[VECTOR_SUB_LDISTRIB] THEN
    SIMP_TAC[VSUM_SUB; FINITE_NUMSEG; VSUM_RMUL] THEN
    ASM_SIMP_TAC[CMW_CHI_SUM; VECTOR_MUL_LID];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(0..m) (\k. cmw_chi m k t * c0)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; LE_0] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    REWRITE_TAC[NORM_MUL] THEN
    SIMP_TAC[CMW_CHI_POS; REAL_ARITH `&0 <= x ==> abs x = x`] THEN
    ASM_CASES_TAC `cmw_chi m k t = &0` THEN ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[CMW_CHI_POS] THEN
    SUBGOAL_THEN `abs(t - &k / &m) < inv(&m)` ASSUME_TAC THENL
     [ASM_MESON_TAC[CMW_CHI_SUPPORT]; ALL_TAC] THEN
    SUBGOAL_THEN `&k / &m IN real_interval[&0,&1]` ASSUME_TAC THENL
     [ASM_SIMP_TAC[CMW_GRID_POINT]; ALL_TAC] THEN
    SUBGOAL_THEN `norm((v:num->real^3->real^K) k y - W y (&k / &m)) < c0 / &2 /\
                  norm(W y (&k / &m) - W y t) < c0 / &2`
    MP_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      CONV_TAC NORM_ARITH];
    REWRITE_TAC[SUM_RMUL] THEN ASM_SIMP_TAC[CMW_CHI_SUM; REAL_MUL_LID; REAL_LE_REFL]]);;

(* Dirichlet estimate for the convex combination of the slices. *)

let CMW_D1_DIR = prove
 (`!S (W:real^3->real->real^K) m (v:num->real^3->real^K) e1.
        ~(m = 0) /\ cm_sweep S W /\
        (!t t'. t IN real_interval[&0,&1] /\ t' IN real_interval[&0,&1] /\
                abs(t - t') < inv(&m)
                ==> wan_dir wan_shell (\z. wan_rext (\y. W y t) z - wan_rext (\y. W y t') z)
                    < e1 / &4) /\
        (!k. k <= m
             ==> wan_w12 wan_shell (wan_rext (v k)) /\
                 wan_dir wan_shell (\z. wan_rext (v k) z - wan_rext (\y. W y (&k / &m)) z)
                 < e1 / &4)
        ==> !t. t IN real_interval[&0,&1]
                ==> wan_w12 wan_shell (\z. vsum(0..m) (\k. cmw_chi m k t % wan_rext (v k) z)) /\
                    wan_dir wan_shell
                      (\z. vsum(0..m) (\k. cmw_chi m k t % wan_rext (v k) z) -
                           wan_rext (\y. W y t) z) <= e1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "wdir") (LABEL_TAC "vk")))) THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!s. s IN real_interval[&0,&1]
                    ==> wan_w12 wan_shell (wan_rext (\y. (W:real^3->real->real^K) y s))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `cm_sweep (S:real^K->bool) (W:real^3->real->real^K)` THEN
    SIMP_TAC[cm_sweep; cm_smap; wan_s2_w12];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`wan_shell`; `\k:num. wan_rext ((v:num->real^3->real^K) k)`;
                   `\k. cmw_chi m k t`; `m:num`] CMW_W12_VSUM) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. vsum(0..m) (\k. cmw_chi m k t % wan_rext ((v:num->real^3->real^K) k) z) -
         wan_rext (\y. (W:real^3->real->real^K) y t) z) =
    (\z. vsum(0..m) (\k. cmw_chi m k t %
                         (\k z. wan_rext (v k) z - wan_rext (\y. W y t) z) k z))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; VECTOR_SUB_LDISTRIB] THEN GEN_TAC THEN
    SIMP_TAC[VSUM_SUB; FINITE_NUMSEG; VSUM_RMUL] THEN
    ASM_SIMP_TAC[CMW_CHI_SUM; VECTOR_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`wan_shell`;
                 `\k z. wan_rext ((v:num->real^3->real^K) k) z -
                        wan_rext (\y. (W:real^3->real->real^K) y t) z`;
                 `\k. cmw_chi m k t`; `m:num`] CMW_DIR_CONVEX) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CMT_SHELL_OPEN; CMW_CHI_POS; CMW_CHI_SUM; ETA_AX] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_W12_SUB THEN REWRITE_TAC[ETA_AX] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= e ==> x <= y ==> x <= e`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(0..m) (\k. cmw_chi m k t * e1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    ASM_CASES_TAC `cmw_chi m k t = &0` THEN ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[CMW_CHI_POS] THEN
    SUBGOAL_THEN `abs(t - &k / &m) < inv(&m)` ASSUME_TAC THENL
     [ASM_MESON_TAC[CMW_CHI_SUPPORT]; ALL_TAC] THEN
    SUBGOAL_THEN `&k / &m IN real_interval[&0,&1]` ASSUME_TAC THENL
     [ASM_SIMP_TAC[CMW_GRID_POINT]; ALL_TAC] THEN
    USE_THEN "vk" (MP_TAC o C MATCH_MP (ASSUME `k:num <= m`)) THEN STRIP_TAC THEN
    USE_THEN "wdir" (MP_TAC o SPECL [`t:real`; `&k / &m`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(ISPECL [`wan_shell`; `wan_rext ((v:num->real^3->real^K) k)`;
                   `wan_rext (\y. (W:real^3->real->real^K) y t)`;
                   `wan_rext (\y. (W:real^3->real->real^K) y (&k / &m))`] CMW_DIR_TRI) THEN
    ASM_SIMP_TAC[CMT_SHELL_OPEN] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SUM_RMUL] THEN ASM_SIMP_TAC[CMW_CHI_SUM; REAL_MUL_LID; REAL_LE_REFL]]);;


(* ========================================================================= *)
(* CM Lemma D.1 for embedded targets and the internal                        *)
(* statement CMW_REG_STATEMENT.                                             *)
(* ========================================================================= *)

let CMW_D1 = prove
 (`!S (G:real^K->real^K^K) d (Q:real^K->real^K^K) (W:real^3->real->real^K) mu.
        WAN_S2_STEREO_STATEMENT (:K) /\ cm_target S G d /\
        smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) /\
        (!z. transp(Q z) = Q z) /\ cm_sweep S W /\ &0 < mu
        ==> ?W':real^3->real->real^K.
               continuously_differentiable 1
                 {x:real^(3,1)finite_sum |
                    ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1]}
                 (\x. W' (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x))) /\
               (!y y'. y IN sphere(vec 0,&1) /\ y' IN sphere(vec 0,&1)
                       ==> W' y (&0) = W' y' (&0) /\ W' y (&1) = W' y' (&1)) /\
               (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]
                      ==> W' y t IN S /\ norm(W' y t - W y t) < mu) /\
               cm_shomotopic S W W' /\
               !t. t IN real_interval[&0,&1]
                   ==> abs(cm_sen G (\y. W' y t) - cm_sen G (\y. W y t)) < mu /\
                       abs(cm_sarea G (\y. W' y t) - cm_sarea G (\y. W y t)) < mu /\
                       abs(cm_strace G Q (\y. W' y t) - cm_strace G Q (\y. W y t)) < mu`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* the retraction *)
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] CMW_RETRACTION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `P:real^K->real^K` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `B:real`)
      (CONJUNCTS_THEN2 (LABEL_TAC "mod") (LABEL_TAC "Pcp"))))) THEN
  SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(vectorize(jacobian (P:real^K->real^K) (at (vec 0))))` THEN
    ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (S:real^K->bool) /\ &0 < d /\
                (!z. z IN cm_tube S d ==> closest_point S z IN S)`
  (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cpS"))) THENL
   [UNDISCH_TAC `cm_target (S:real^K->bool) (G:real^K->real^K^K) d` THEN SIMP_TAC[cm_target];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^K. w IN S ==> (P:real^K->real^K) w = w` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN TRANS_TAC EQ_TRANS `closest_point S (w:real^K)` THEN
    CONJ_TAC THENL
     [USE_THEN "Pcp" MATCH_MP_TAC THEN EXISTS_TAC `w:real^K` THEN
      ASM_REWRITE_TAC[DIST_REFL] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[CLOSEST_POINT_SELF]];
    ALL_TAC] THEN
  SUBGOAL_THEN `bounded wan_shell` ASSUME_TAC THENL
   [REWRITE_TAC[wan_shell; CMT_ANNULUS_OPEN_BOUNDED]; ALL_TAC] THEN
  (* facts on the slices of W *)
  SUBGOAL_THEN `!s. s IN real_interval[&0,&1]
                    ==> cm_smap S (\y. (W:real^3->real->real^K) y s)` ASSUME_TAC THENL
   [UNDISCH_TAC `cm_sweep (S:real^K->bool) (W:real^3->real->real^K)` THEN SIMP_TAC[cm_sweep];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN real_interval[&0,&1]
                    ==> wan_w12 wan_shell (wan_rext (\y. (W:real^3->real->real^K) y s))`
  ASSUME_TAC THENL [ASM_MESON_TAC[cm_smap; wan_s2_w12]; ALL_TAC] THEN
  SUBGOAL_THEN `!y s. y IN sphere(vec 0,&1) /\ s IN real_interval[&0,&1]
                      ==> (W:real^3->real->real^K) y s IN S` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `cm_smap S (\y. (W:real^3->real->real^K) y s)` MP_TAC THENL
     [ASM_SIMP_TAC[]; REWRITE_TAC[cm_smap] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  (* a bound for the Dirichlet integrals of the slices *)
  MP_TAC(ISPECL [`S:real^K->bool`; `W:real^3->real->real^K`] CMW_SWEEP_DIR_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `D:real`) THEN
  SUBGOAL_THEN `&0 <= D` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `wan_dir wan_shell (wan_rext (\y. (W:real^3->real->real^K) y (&0)))` THEN
    SUBGOAL_THEN `&0 IN real_interval[&0,&1]` ASSUME_TAC THENL
     [REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[WAN_DIR_POS];
    ALL_TAC] THEN
  (* closeness that controls the functionals *)
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `Q:real^K->real^K^K`;
                 `W:real^3->real->real^K`] CMW_SLICE_UNIF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `mu:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fun"))) THEN
  (* the parameters om and e1 *)
  SUBGOAL_THEN `?om. &0 < om /\ om <= &1 /\ om * (&2 * D + &1) <= eta / &4`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min (&1) (eta / (&4 * (&2 * D + &1)))` THEN
    SUBGOAL_THEN `&0 < &4 * (&2 * D + &1)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_DIV; REAL_LT_01; REAL_MIN_LE; REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `eta / (&4 * (&2 * D + &1)) * (&2 * D + &1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `eta / (&4 * (&2 * D + &1)) * (&2 * D + &1) = eta / &4`
        (fun th -> REWRITE_TAC[th; REAL_LE_REFL]) THEN
      SUBGOAL_THEN `~(&2 * D + &1 = &0)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * om pow 2 * D < eta / &2` ASSUME_TAC THENL
   [SUBGOAL_THEN `om pow 2 <= om` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC(REAL_ARITH `x * y <= x * &1 ==> x * y <= x`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `om pow 2 * D <= om * D` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?e1. &0 < e1 /\ e1 * (&2 * B pow 2 + &1) <= eta / &4` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `eta / (&4 * (&2 * B pow 2 + &1))` THEN
    SUBGOAL_THEN `&0 < &4 * (&2 * B pow 2 + &1)` ASSUME_TAC THENL
     [MP_TAC(SPEC `B:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV] THEN
    SUBGOAL_THEN `eta / (&4 * (&2 * B pow 2 + &1)) * (&2 * B pow 2 + &1) = eta / &4`
      (fun th -> REWRITE_TAC[th; REAL_LE_REFL]) THEN
    SUBGOAL_THEN `~(&2 * B pow 2 + &1 = &0)` MP_TAC THENL
     [MP_TAC(SPEC `B:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * B pow 2 * e1 < eta / &2` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the modulus of continuity of the Jacobian of P *)
  USE_THEN "mod" (MP_TAC o C MATCH_MP (ASSUME `&0 < om`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `rom:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rom"))) THEN
  (* the C^0 accuracy *)
  ABBREV_TAC `c0 = min (d / &4) (min (rom / &2) (min (mu / &4) (eta / &4)))` THEN
  SUBGOAL_THEN `&0 < c0 /\ c0 <= d / &4 /\ c0 <= rom / &2 /\ c0 <= mu / &4 /\ c0 <= eta / &4`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "c0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the time grid *)
  MP_TAC(ISPEC `W:real^3->real->real^K` CMW_SWEEP_JOINT_UNIF) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[cm_sweep]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `c0 / &2`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "r1"))) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `W:real^3->real->real^K`] CMW_SWEEP_DIR_UNIF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e1 / &4`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "r2"))) THEN
  MP_TAC(SPEC `min r1 r2` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
  (* the slices *)
  MP_TAC(ISPECL [`S:real^K->bool`; `W:real^3->real->real^K`; `min (c0 / &2) (e1 / &4)`;
                 `m:num`] CMW_D1_SLICES) THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:num->real^3->real^K` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "vk")))) THEN
  (* joint C^1 *)
  SUBGOAL_THEN
   `continuously_differentiable 1
      {x:real^(3,1)finite_sum |
         ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1]}
      (\x. cmw_d1 (P:real^K->real^K) m (v:num->real^3->real^K)
                  (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMW_D1_C1 THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "vk" (MP_TAC o C MATCH_MP (ASSUME `k:num <= m`)) THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* C^0 estimate for the convex combination *)
  MP_TAC(ISPECL [`W:real^3->real->real^K`; `m:num`; `v:num->real^3->real^K`; `c0:real`]
                CMW_D1_C0) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN USE_THEN "r1" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN
      USE_THEN "vk" (MP_TAC o C MATCH_MP (ASSUME `k:num <= m`)) THEN ASM_SIMP_TAC[]];
    DISCH_THEN(LABEL_TAC "c0est")] THEN
  (* values of W' *)
  SUBGOAL_THEN
   `!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]
          ==> cmw_d1 (P:real^K->real^K) m (v:num->real^3->real^K) y t IN S /\
              norm(cmw_d1 P m v y t - (W:real^3->real->real^K) y t) <= &2 * c0`
  (LABEL_TAC "vals") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "c0est" (MP_TAC o C MATCH_MP
      (CONJ (ASSUME `y IN sphere(vec 0:real^3,&1)`) (ASSUME `t IN real_interval[&0,&1]`))) THEN
    ABBREV_TAC `f = vsum(0..m) (\k. cmw_chi m k t % (v:num->real^3->real^K) k y)` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(W:real^3->real->real^K) y t IN S` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `cmw_d1 (P:real^K->real^K) m (v:num->real^3->real^K) y t = closest_point S f`
    SUBST1_TAC THENL
     [REWRITE_TAC[cmw_d1] THEN ASM_REWRITE_TAC[] THEN USE_THEN "Pcp" MATCH_MP_TAC THEN
      EXISTS_TAC `(W:real^3->real->real^K) y t` THEN ASM_REWRITE_TAC[dist] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [USE_THEN "cpS" MATCH_MP_TAC THEN
      REWRITE_TAC[cm_tube; IN_ELIM_THM] THEN EXISTS_TAC `(W:real^3->real->real^K) y t` THEN
      ASM_REWRITE_TAC[dist] THEN ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`S:real^K->bool`; `f:real^K`; `(W:real^3->real->real^K) y t`]
                    CLOSEST_POINT_LE) THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED; dist] THEN
      UNDISCH_TAC `norm(f - (W:real^3->real->real^K) y t) <= c0` THEN CONV_TAC NORM_ARITH];
    ALL_TAC] THEN
  (* the slices of W' *)
  SUBGOAL_THEN
   `!t. t IN real_interval[&0,&1]
        ==> cm_smap S (\y. cmw_d1 (P:real^K->real^K) m (v:num->real^3->real^K) y t) /\
            continuously_differentiable 1 {z:real^3 | ~(z = vec 0)}
              (wan_rext (\y. cmw_d1 P m v y t))`
  (LABEL_TAC "smap") THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC CMW_C1_SLICE_SMAP THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* Dirichlet estimate for the slices of W' *)
  SUBGOAL_THEN
   `!t. t IN real_interval[&0,&1]
        ==> wan_dir wan_shell
              (\z. wan_rext (\y. cmw_d1 (P:real^K->real^K) m (v:num->real^3->real^K) y t) z -
                   wan_rext (\y. (W:real^3->real->real^K) y t) z) < eta`
  (LABEL_TAC "dirs") THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `W:real^3->real->real^K`; `m:num`;
                   `v:num->real^3->real^K`; `e1:real`] CMW_D1_DIR) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN USE_THEN "r2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        X_GEN_TAC `k:num` THEN DISCH_TAC THEN
        USE_THEN "vk" (MP_TAC o C MATCH_MP (ASSUME `k:num <= m`)) THEN
        SIMP_TAC[CMW_REXT_C1_W12]];
      DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
    MP_TAC(ISPECL [`wan_shell`;
                   `\z. vsum(0..m) (\k. cmw_chi m k t %
                                        wan_rext ((v:num->real^3->real^K) k) z)`;
                   `wan_rext (\y. (W:real^3->real->real^K) y t)`; `P:real^K->real^K`;
                   `B:real`; `om:real`] CMW_CHAIN_DIR_EST) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[CMT_SHELL_OPEN] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "rom" MATCH_MP_TAC THEN
      SUBGOAL_THEN `inv(norm x) % x IN sphere(vec 0:real^3,&1)` ASSUME_TAC THENL
       [ASM_MESON_TAC[P4_RADIAL_SPHERE; CMT_SHELL_NONZERO]; ALL_TAC] THEN
      USE_THEN "c0est" (MP_TAC o C MATCH_MP
        (CONJ (ASSUME `inv(norm x) % x IN sphere(vec 0:real^3,&1)`)
              (ASSUME `t IN real_interval[&0,&1]`))) THEN
      REWRITE_TAC[wan_rext] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[] THEN STRIP_TAC] THEN
    SUBGOAL_THEN
     `wan_dir wan_shell
        (\z. wan_rext (\y. cmw_d1 (P:real^K->real^K) m (v:num->real^3->real^K) y t) z -
             wan_rext (\y. (W:real^3->real->real^K) y t) z) =
      wan_dir wan_shell
        (\z. P(vsum(0..m) (\k. cmw_chi m k t % wan_rext (v k) z)) -
             P(wan_rext (\y. W y t) z))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC CMW_DIR_EQ_ON THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `inv(norm z) % z IN sphere(vec 0:real^3,&1)` ASSUME_TAC THENL
       [ASM_MESON_TAC[P4_RADIAL_SPHERE; CMT_SHELL_NONZERO]; ALL_TAC] THEN
      REWRITE_TAC[wan_rext; cmw_d1] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `B pow 2 * wan_dir wan_shell
                  (\z. vsum(0..m) (\k. cmw_chi m k t % wan_rext ((v:num->real^3->real^K) k) z) -
                       wan_rext (\y. (W:real^3->real->real^K) y t) z) <= B pow 2 * e1 /\
      om pow 2 * wan_dir wan_shell (wan_rext (\y. (W:real^3->real->real^K) y t)) <=
      om pow 2 * D`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* end slices of W' *)
  SUBGOAL_THEN
   `!y y'. y IN sphere(vec 0,&1) /\ y' IN sphere(vec 0,&1)
           ==> cmw_d1 (P:real^K->real^K) m (v:num->real^3->real^K) y (&0) = cmw_d1 P m v y' (&0) /\
               cmw_d1 P m v y (&1) = cmw_d1 P m v y' (&1)`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[CMW_D1_ENDS]; ALL_TAC] THEN
  EXISTS_TAC `cmw_d1 (P:real^K->real^K) m (v:num->real^3->real^K)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "vals" (MP_TAC o C MATCH_MP
      (CONJ (ASSUME `y IN sphere(vec 0:real^3,&1)`) (ASSUME `t IN real_interval[&0,&1]`))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC CMW_CLOSE_SHOMOTOPIC THEN
    MAP_EVERY EXISTS_TAC [`G:real^K->real^K^K`; `d:real`] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[cm_sweep];
      MATCH_MP_TAC CMW_C1_SWEEP_CONT THEN ASM_REWRITE_TAC[];
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      USE_THEN "vals" (MP_TAC o C MATCH_MP
        (CONJ (ASSUME `y IN sphere(vec 0:real^3,&1)`) (ASSUME `t IN real_interval[&0,&1]`))) THEN
      STRIP_TAC THEN ASM_SIMP_TAC[] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REAL_ARITH_TAC;
      ASM_MESON_TAC[cm_sweep]];
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN USE_THEN "fun" MATCH_MP_TAC THEN
    USE_THEN "smap" (MP_TAC o C MATCH_MP (ASSUME `t IN real_interval[&0,&1]`)) THEN
    USE_THEN "dirs" (MP_TAC o C MATCH_MP (ASSUME `t IN real_interval[&0,&1]`)) THEN
    SIMP_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "vals" (MP_TAC o C MATCH_MP
      (CONJ (ASSUME `y IN sphere(vec 0:real^3,&1)`) (ASSUME `t IN real_interval[&0,&1]`))) THEN
    STRIP_TAC THEN ASM_REAL_ARITH_TAC]);;

(* The internal statement of the unit. *)

let CMW_REG = prove
 (`WAN_S2_STEREO_STATEMENT (:K) ==> CMW_REG_STATEMENT (:K)`,
  DISCH_TAC THEN REWRITE_TAC[CMW_REG_STATEMENT] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMW_AREA_LE_EN THEN
    MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CMW_D1 THEN EXISTS_TAC `d:real` THEN
    ASM_REWRITE_TAC[]]);;

