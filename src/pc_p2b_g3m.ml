(* ========================================================================= *)
(* Unit pc_p2b_g3m (Part 2B): measure theory on manifolds for G3             *)
(* (P2B_W920_G3_ROUTE of pc_p2b_w920g): countable additivity of the manifold *)
(* integral for nonnegative functions (chart partitions combined with        *)
(* NUMPAIR), monotone limits, integrals over compact sets.  Generic in the   *)
(* dimension.                                                                *)
(* ========================================================================= *)

needs "src/pc_grg_vol.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Series lemmas.                                                            *)
(* ========================================================================= *)

(* A series spread out along a strictly increasing sequence of indices,    *)
(* with zeros elsewhere, has the same sum.                                   *)

let P2BX_REAL_SUMS_SPARSE = prove
 (`!(r:num->num) (x:num->real) (y:num->real) l.
     (!m n. m < n ==> r m < r n) /\
     (!k. y(r k) = x k) /\ (!m. ~(?k. m = r k) ==> y m = &0) /\
     (x real_sums l) (from 0)
     ==> (y real_sums l) (from 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. n <= (r:num->num) n` ASSUME_TAC THENL
   [MATCH_MP_TAC MONOTONE_BIGGER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!m n. m <= n ==> (r:num->num) m <= r n` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[LE_LT] THEN STRIP_TAC THEN ASM_SIMP_TAC[LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!m n. (r:num->num) m = r n ==> m = n` ASSUME_TAC THENL
   [ASM_MESON_TAC[LT_CASES; LT_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `!M. sum(0..M) (y:num->real) = sum {k | (r:num->num) k <= M} x`
  ASSUME_TAC THENL
   [X_GEN_TAC `M:num` THEN
    TRANS_TAC EQ_TRANS `sum (IMAGE (r:num->num) {k | r k <= M}) (y:num->real)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_SUPERSET THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_NUMSEG; LE_0] THEN
        SIMP_TAC[];
        X_GEN_TAC `m:num` THEN REWRITE_TAC[IN_NUMSEG; LE_0; IN_IMAGE; IN_ELIM_THM] THEN
        STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]];
      W(MP_TAC o PART_MATCH (lhs o rand) SUM_IMAGE o lhs o snd) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      MATCH_MP_TAC SUM_EQ THEN ASM_REWRITE_TAC[o_THM]];
    ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  REWRITE_TAC[GRGV_SUMS_FROM0] THEN STRIP_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `((\n. sum(0..n) (x:num->real)) ---> l) sequentially` THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN DISCH_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `K0:num`) THEN
  EXISTS_TAC `(r:num->num) K0` THEN X_GEN_TAC `M:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?K. (K0 <= K /\ M < (r:num->num) (SUC K)) /\
                    (!j. j < K ==> ~(K0 <= j /\ M < r (SUC j)))`
  (X_CHOOSE_THEN `K:num` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC)) THENL
   [MP_TAC(ISPEC `\K. K0 <= K /\ M < (r:num->num) (SUC K)` num_WOP) THEN
    REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    EXISTS_TAC `K0 + M:num` THEN REWRITE_TAC[LE_ADD] THEN
    MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `SUC(K0 + M)` THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `{k | (r:num->num) k <= M} = 0..K` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG; LE_0] THEN X_GEN_TAC `k:num` THEN
    EQ_TAC THENL
     [DISCH_TAC THEN REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
      SUBGOAL_THEN `(r:num->num) (SUC K) <= r k` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
      DISCH_TAC THEN ASM_CASES_TAC `k <= K0:num` THENL
       [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(r:num->num) K0` THEN ASM_SIMP_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `k - 1` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `K:num`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `SUC(k - 1) = k` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_ARITH_TAC];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* A nonnegative double series as a single series along NUMPAIR. *)

let P2BX_NUMPAIR_MONO = prove
 (`!n i j. i < j ==> NUMPAIR n i < NUMPAIR n j`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NUMPAIR; LT_MULT_LCANCEL; EXP_EQ_0] THEN
  ASM_ARITH_TAC);;

let P2BX_REAL_SUMS_NUMPAIR = prove
 (`!(a:num->num->real) A v.
     (!n k. &0 <= a n k) /\ (!n. ((a n) real_sums A n) (from 0)) /\
     (A real_sums v) (from 0)
     ==> ((\m. if NUMPAIR (NUMFST m) (NUMSND m) = m then a (NUMFST m) (NUMSND m) else &0)
          real_sums v) (from 0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\n m. if NUMPAIR (NUMFST m) (NUMSND m) = m /\ NUMFST m = n
                        then (a:num->num->real) n (NUMSND m) else &0`;
                 `A:num->real`; `v:real`] GRGV_TONELLI) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    X_GEN_TAC `n:num` THEN MATCH_MP_TAC P2BX_REAL_SUMS_SPARSE THEN
    MAP_EVERY EXISTS_TAC [`NUMPAIR n`; `(a:num->num->real) n`] THEN
    ASM_REWRITE_TAC[NUMPAIR_DEST; P2BX_NUMPAIR_MONO] THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC o check (fun th -> is_conj(concl th))) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `NUMSND m` o REWRITE_RULE[NOT_EXISTS_THM] o
      check (fun th -> is_neg(concl th))) THEN
    UNDISCH_TAC `NUMPAIR (NUMFST m) (NUMSND m) = m` THEN UNDISCH_TAC `NUMFST m = n` THEN
    DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:num->real` (STRIP_ASSUME_TAC o BETA_RULE)) THEN
  MATCH_MP_TAC REAL_SUMS_EQ THEN EXISTS_TAC `D:num->real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_SERIES_UNIQUE THEN
  EXISTS_TAC `\n. if NUMPAIR (NUMFST m) (NUMSND m) = m /\ NUMFST m = n
                  then (a:num->num->real) n (NUMSND m) else &0` THEN
  EXISTS_TAC `from 0` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\n. if NUMPAIR (NUMFST m) (NUMSND m) = m /\ NUMFST m = n
                      then (a:num->num->real) n (NUMSND m) else &0`;
                 `{NUMFST m}`; `from 0`] REAL_SERIES_FINITE_SUPPORT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [SIMP_TAC[FINITE_INTER; FINITE_SING]; ALL_TAC] THEN
    REWRITE_TAC[IN_INTER; IN_SING; IN_FROM; LE_0] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o check (fun th -> is_conj(concl th))) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{NUMFST m} INTER from 0 = {NUMFST m}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_SING; IN_FROM; LE_0]; ALL_TAC] THEN
  REWRITE_TAC[SUM_SING] THEN DISCH_TAC THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Countable additivity of the manifold integral for nonnegative functions.  *)
(* ========================================================================= *)

let P2BX_CHART_INTEGRAND_NORM_POS = prove
 (`!atlas (g:A->real^N^N) f (c:(A->bool)#(A->real^N)) s.
     riemannian_metric atlas g /\ (!x. &0 <= f x) /\ (s = {} \/ c IN atlas) /\
     s SUBSET IMAGE (SND c) (FST c)
     ==> integral s (\y. lift(norm(mfd_chart_integrand atlas g f c y))) =
         integral s (mfd_chart_integrand atlas g f c)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[INTEGRAL_EMPTY] THEN STRIP_TAC THEN
  MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[mfd_chart_integrand; NORM_LIFT; LIFT_EQ; REAL_ABS_REFL] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC GRGV_DENSITY_POS THEN
  ASM SET_TAC[]);;

let P2BX_MFD_HAS_INTEGRAL_UNIONS_POS = prove
 (`!top atlas (g:A->real^N^N) f (S:num->A->bool) v.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     (!x. &0 <= f x) /\
     (!n. mfd_has_integral (top,atlas) g f (S n) (v n)) /\
     (!m n. ~(m = n) ==> DISJOINT (S m) (S n)) /\
     real_summable (from 0) v
     ==> mfd_has_integral (top,atlas) g f (UNIONS {S n | n IN (:num)})
                          (real_infsum (from 0) v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[mfd_has_integral] o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_has_integral")) (concl th))) THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num->num->(A->bool)#(A->real^N)`
    (X_CHOOSE_THEN `E:num->num->A->bool` (LABEL_TAC "P"))) THEN
  SUBGOAL_THEN
   `!n k. ((E:num->num->A->bool) n k = {} \/ (c:num->num->(A->bool)#(A->real^N)) n k IN atlas) /\
          E n k SUBSET FST(c n k) /\ lebesgue_measurable (IMAGE (SND(c n k)) (E n k)) /\
          E n k SUBSET (S:num->A->bool) n /\
          mfd_chart_integrand atlas (g:A->real^N^N) f (c n k) absolutely_integrable_on
            IMAGE (SND(c n k)) (E n k) /\
          drop(integral (IMAGE (SND(c n k)) (E n k))
                 (\y. lift(norm(mfd_chart_integrand atlas g f (c n k) y)))) =
          drop(integral (IMAGE (SND(c n k)) (E n k)) (mfd_chart_integrand atlas g f (c n k))) /\
          &0 <= drop(integral (IMAGE (SND(c n k)) (E n k)) (mfd_chart_integrand atlas g f (c n k)))`
  (LABEL_TAC "PK") THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `k:num`] THEN
    USE_THEN "P" (MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[mfd_chart_partition] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (CONJUNCTS_THEN2
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) o SPEC `k:num`)
        (CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC))
      (CONJUNCTS_THEN2 (ASSUME_TAC o SPEC `k:num`) (K ALL_TAC))) THEN
    SUBGOAL_THEN `IMAGE (SND((c:num->num->(A->bool)#(A->real^N)) n k)) ((E:num->num->A->bool) n k)
                  SUBSET IMAGE (SND(c n k)) (FST(c n k))` ASSUME_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "UNIONS")) (concl th))) THEN
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      EXISTS_TAC `(E:num->num->A->bool) n k` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `k:num` THEN REWRITE_TAC[];
      AP_TERM_TAC THEN MATCH_MP_TAC P2BX_CHART_INTEGRAND_NORM_POS THEN
      ASM_REWRITE_TAC[IMAGE_EQ_EMPTY];
      MATCH_MP_TAC INTEGRAL_DROP_POS THEN
      ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
      REWRITE_TAC[mfd_chart_integrand; LIFT_DROP] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC GRGV_DENSITY_POS THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th))) THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(y:real^N) IN
        IMAGE (SND((c:num->num->(A->bool)#(A->real^N)) n k)) ((E:num->num->A->bool) n k)` THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; NOT_IN_EMPTY]];
    ALL_TAC] THEN
  (* the two series *)
  SUBGOAL_THEN
   `!n. ((\k. drop(integral (IMAGE (SND((c:num->num->(A->bool)#(A->real^N)) n k))
                                   ((E:num->num->A->bool) n k))
                  (mfd_chart_integrand atlas (g:A->real^N^N) f (c n k)))) real_sums v n) (from 0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN USE_THEN "P" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\n k. drop(integral (IMAGE (SND((c:num->num->(A->bool)#(A->real^N)) n k))
                                ((E:num->num->A->bool) n k))
               (mfd_chart_integrand atlas (g:A->real^N^N) f (c n k)))`;
    `v:num->real`; `real_infsum (from 0) (v:num->real)`] P2BX_REAL_SUMS_NUMPAIR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_SUMS_INFSUM] THEN ASM_SIMP_TAC[] THEN
    REPEAT GEN_TAC THEN USE_THEN "PK" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o BETA_RULE) THEN
  REWRITE_TAC[mfd_has_integral] THEN
  EXISTS_TAC `\m. (c:num->num->(A->bool)#(A->real^N)) (NUMFST m) (NUMSND m)` THEN
  EXISTS_TAC `\m. if NUMPAIR (NUMFST m) (NUMSND m) = m
                  then (E:num->num->A->bool) (NUMFST m) (NUMSND m) else {}` THEN
  REWRITE_TAC[mfd_chart_partition] THEN
  MP_TAC(ISPEC `E:num->num->A->bool` GRGV_NUMPAIR_PIECES) THEN ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `k:num`; `n':num`; `k':num`] THEN DISCH_TAC THEN
    ASM_CASES_TAC `n:num = n'` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      USE_THEN "P" (MP_TAC o SPEC `n':num`) THEN REWRITE_TAC[mfd_chart_partition] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT1) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[];
      MATCH_MP_TAC(SET_RULE `!s t. DISJOINT s t /\ a SUBSET s /\ b SUBSET t ==> DISJOINT (a:A->bool) b`) THEN
      MAP_EVERY EXISTS_TAC [`(S:num->A->bool) n`; `(S:num->A->bool) n'`] THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `m:num` THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[EMPTY_SUBSET; IMAGE_CLAUSES; LEBESGUE_MEASURABLE_EMPTY];
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:A` THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `t:A->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `k:num` ASSUME_TAC)) MP_TAC)) THEN
      FIRST_X_ASSUM SUBST1_TAC THEN DISCH_TAC THEN
      EXISTS_TAC `(S:num->A->bool) n` THEN CONJ_TAC THENL
       [EXISTS_TAC `n:num` THEN REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "PK" (fun th -> MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(CONJUNCT2
        (SPECL [`n:num`; `k:num`] th)))))) THEN
      UNDISCH_TAC `(x:A) IN (E:num->num->A->bool) n k` THEN SET_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `t:A->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `n:num` ASSUME_TAC) MP_TAC)) THEN
      FIRST_X_ASSUM SUBST1_TAC THEN DISCH_TAC THEN
      USE_THEN "P" (MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[mfd_chart_partition] THEN
      DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT1) THEN
      DISCH_THEN(MP_TAC o SPEC `x:A` o
        REWRITE_RULE[IN_UNIONS; IN_ELIM_THM; IN_UNIV] o REWRITE_RULE[EXTENSION] o SYM) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:A->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `k:num` ASSUME_TAC) MP_TAC)) THEN
      FIRST_X_ASSUM SUBST1_TAC THEN DISCH_TAC THEN
      EXISTS_TAC `(E:num->num->A->bool) n k` THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`n:num`; `k:num`] THEN REWRITE_TAC[]];
    X_GEN_TAC `m:num` THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; ABSOLUTELY_INTEGRABLE_ON_EMPTY];
    REWRITE_TAC[real_summable] THEN EXISTS_TAC `real_infsum (from 0) (v:num->real)` THEN
    MATCH_MP_TAC REAL_SUMS_EQ THEN
    EXISTS_TAC `\m. if NUMPAIR (NUMFST m) (NUMSND m) = m
                    then drop(integral (IMAGE (SND((c:num->num->(A->bool)#(A->real^N))
                                                    (NUMFST m) (NUMSND m)))
                                               ((E:num->num->A->bool) (NUMFST m) (NUMSND m)))
                               (mfd_chart_integrand atlas (g:A->real^N^N) f
                                  (c (NUMFST m) (NUMSND m))))
                    else &0` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; INTEGRAL_EMPTY; DROP_VEC] THEN
    USE_THEN "PK" (fun th -> REWRITE_TAC[th]);
    MATCH_MP_TAC REAL_SUMS_EQ THEN
    EXISTS_TAC `\m. if NUMPAIR (NUMFST m) (NUMSND m) = m
                    then drop(integral (IMAGE (SND((c:num->num->(A->bool)#(A->real^N))
                                                    (NUMFST m) (NUMSND m)))
                                               ((E:num->num->A->bool) (NUMFST m) (NUMSND m)))
                               (mfd_chart_integrand atlas (g:A->real^N^N) f
                                  (c (NUMFST m) (NUMSND m))))
                    else &0` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; INTEGRAL_EMPTY; DROP_VEC]]);;

(* ========================================================================= *)
(* Gaussian series and Gaussian tails of the manifold integral under a cubic *)
(* volume growth bound (Bishop-Gromov).                                      *)
(* ========================================================================= *)

(* exp(-c x^2/2) (x+1)^3 <= exp(8/c) exp(-x) for x >= 0. *)

let P2BX_GAUSS_POLY_BOUND = prove
 (`!c x. &0 < c /\ &0 <= x
         ==> exp(--(c / &2 * x pow 2)) * (x + &1) pow 3 <= exp(&8 / c) * exp(--x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x + &1) pow 3 <= exp(&3 * x)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_N] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    MP_TAC(SPEC `x:real` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(--(c / &2 * x pow 2)) * exp(&3 * x)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_EXP_MONO_LE] THEN
  SUBGOAL_THEN `&0 <= c / &2 * (x - &4 / c) pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c / &2 * (x - &4 / c) pow 2 = c / &2 * x pow 2 - &4 * x + &8 / c`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD; REAL_ARITH_TAC]);;

let P2BX_GAUSS_SERIES = prove
 (`!c. &0 < c
       ==> ?K. &0 <= K /\
               !R. &0 <= R
                   ==> real_summable (from 0)
                         (\j. exp(--(c * (R + &j) pow 2)) * (R + &j + &1) pow 3) /\
                       real_infsum (from 0)
                         (\j. exp(--(c * (R + &j) pow 2)) * (R + &j + &1) pow 3)
                       <= K * exp(--(c / &2 * R pow 2))`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `exp(&8 / c) * inv(&1 - exp(--(&1)))` THEN
  SUBGOAL_THEN `&0 < exp(--(&1)) /\ exp(--(&1)) < &1` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LT] THEN
    GEN_REWRITE_TAC (RAND_CONV) [GSYM REAL_EXP_0] THEN
    REWRITE_TAC[REAL_EXP_MONO_LT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `R:real` THEN DISCH_TAC THEN
  ABBREV_TAC `M = exp(--(c / &2 * R pow 2)) * exp(&8 / c)` THEN
  SUBGOAL_THEN
   `!j. &0 <= exp(--(c * (R + &j) pow 2)) * (R + &j + &1) pow 3 /\
        exp(--(c * (R + &j) pow 2)) * (R + &j + &1) pow 3 <= M * exp(--(&1)) pow j`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= R + &j` ASSUME_TAC THENL
     [MP_TAC(SPEC `j:num` REAL_POS) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`c:real`; `R + &j`] P2BX_GAUSS_POLY_BOUND) THEN
    ASM_REWRITE_TAC[GSYM REAL_ADD_ASSOC] THEN DISCH_TAC THEN
    SUBGOAL_THEN `exp(--(c * (R + &j) pow 2)) =
                  exp(--(c / &2 * (R + &j) pow 2)) * exp(--(c / &2 * (R + &j) pow 2))`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "M" THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_EXP_MONO_LE; REAL_LE_NEG2] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN MP_TAC(SPEC `j:num` REAL_POS) THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(&8 / c) * exp(--(R + &j))` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    REWRITE_TAC[GSYM REAL_EXP_N; REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `((\j. M * exp(--(&1)) pow j) real_sums (M * inv(&1 - exp(--(&1))))) (from 0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_SERIES_LMUL THEN
    MP_TAC(SPECL [`0`; `exp(--(&1))`] REAL_SUMS_GP) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[real_pow; real_div; REAL_MUL_LID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `real_summable (from 0)
                  (\j. exp(--(c * (R + &j) pow 2)) * (R + &j + &1) pow 3)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
    EXISTS_TAC `\j. M * exp(--(&1)) pow j` THEN CONJ_TAC THENL
     [REWRITE_TAC[real_summable] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `0` THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN BETA_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `M:real`)) (concl th))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `M * inv(&1 - exp(--(&1)))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_SERIES_LE THEN
    MAP_EVERY EXISTS_TAC [`\j. exp(--(c * (R + &j) pow 2)) * (R + &j + &1) pow 3`;
                          `\j. M * exp(--(&1)) pow j`; `from 0`] THEN
    ASM_REWRITE_TAC[REAL_SUMS_INFSUM] THEN ASM_SIMP_TAC[];
    EXPAND_TAC "M" THEN REWRITE_TAC[REAL_MUL_AC; REAL_LE_REFL]]);;

(* Balls lie in the space and grow with the radius. *)

let P2BX_MFD_BALL_FACTS = prove
 (`!top atlas (g:A->real^N^N) q r1 r2.
     mfd_ball (top,atlas) g q r1 SUBSET topspace top /\
     (r1 <= r2 ==> mfd_ball (top,atlas) g q r1 SUBSET mfd_ball (top,atlas) g q r2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_ball; SUBSET; IN_ELIM_THM] THEN CONJ_TAC THENL
   [MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* Gaussian tails: if h <= C exp(-c (d(q,x)/rho)^2) / rho^3 and the balls   *)
(* about q have volume at most A r^3, then the integral of h outside the     *)
(* ball of radius rho R is at most C A K exp(-c R^2/2), with K depending on *)
(* c only.                                                                   *)

let P2BX_MFD_GAUSS_TAIL = prove
 (`!c. &0 < c
       ==> ?K. &0 <= K /\
           !top atlas (g:A->real^N^N) h q rho R C A.
             hausdorff_space top /\ smooth_manifold_atlas top atlas /\
             riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
             (!x. x IN topspace top ==> mfd_joinable (top,atlas) q x) /\
             &0 < rho /\ &0 <= R /\ &0 <= C /\ &0 <= A /\
             (!x. &0 <= h x) /\ mfd_integrable_on (top,atlas) g h (topspace top) /\
             (!r. &0 < r ==> mfd_volume (top,atlas) g (mfd_ball (top,atlas) g q r) <= A * r pow 3) /\
             (!x. x IN topspace top
                  ==> h x <= C * exp(--(c * (mfd_dist (top,atlas) g q x / rho) pow 2)) /
                             rho pow 3)
             ==> mfd_integrable_on (top,atlas) g h
                   (topspace top DIFF mfd_ball (top,atlas) g q (rho * R)) /\
                 mfd_integral (top,atlas) g
                   (topspace top DIFF mfd_ball (top,atlas) g q (rho * R)) h
                 <= C * A * K * exp(--(c / &2 * R pow 2))`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `K:real` STRIP_ASSUME_TAC o MATCH_MP P2BX_GAUSS_SERIES) THEN
  EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `B = \r. mfd_ball (top,atlas) (g:A->real^N^N) q r` THEN
  SUBGOAL_THEN `!r. (B:real->A->bool) r SUBSET topspace top /\
                    mfd_lebesgue_measurable (top,atlas) (B r) /\
                    mfd_has_volume (top,atlas) (g:A->real^N^N) (B r) (mfd_volume (top,atlas) g (B r))`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real` THEN EXPAND_TAC "B" THEN REWRITE_TAC[P2BX_MFD_BALL_FACTS] THEN
    ASM_SIMP_TAC[MFD_HAS_VOLUME_BALL] THEN MATCH_MP_TAC MFD_LEBESGUE_MEASURABLE_OPEN THEN
    ASM_SIMP_TAC[MFD_BALL_OPEN];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r1 r2. r1 <= r2 ==> (B:real->A->bool) r1 SUBSET B r2` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN SIMP_TAC[P2BX_MFD_BALL_FACTS]; ALL_TAC] THEN
  ABBREV_TAC `Ann = \j:num. (B:real->A->bool) (rho * (R + &j + &1)) DIFF B (rho * (R + &j))` THEN
  SUBGOAL_THEN
   `!j. mfd_integrable_on (top,atlas) (g:A->real^N^N) h ((Ann:num->A->bool) j) /\
        &0 <= mfd_integral (top,atlas) g (Ann j) h /\
        mfd_integral (top,atlas) g (Ann j) h <=
        C * A * (exp(--(c * (R + &j) pow 2)) * (R + &j + &1) pow 3)`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN
    SUBGOAL_THEN `mfd_lebesgue_measurable (top,atlas:((A->bool)#(A->real^N))->bool) ((Ann:num->A->bool) j) /\
                  Ann j SUBSET topspace top /\
                  Ann j SUBSET (B:real->A->bool) (rho * (R + &j + &1))`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "Ann" THEN REWRITE_TAC[] THEN
      ASM_SIMP_TAC[MFD_LEBESGUE_MEASURABLE_DIFF] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_integrable_on (top,atlas) (g:A->real^N^N) h ((Ann:num->A->bool) j)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MFD_INTEGRABLE_SUBSET THEN EXISTS_TAC `topspace top:A->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [MFD_INTEGRABLE_INTEGRAL]) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `(Ann:num->A->bool) j`; `(B:real->A->bool) (rho * (R + &j + &1))`;
                   `mfd_volume (top,atlas) (g:A->real^N^N) ((B:real->A->bool) (rho * (R + &j + &1)))`]
                  MFD_HAS_VOLUME_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_HAS_INTEGRAL_LE THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                            `g:A->real^N^N`; `\x:A. &0`; `h:A->real`; `(Ann:num->A->bool) j`] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                     `(Ann:num->A->bool) j`;
                     `mfd_volume (top,atlas) (g:A->real^N^N) ((Ann:num->A->bool) j)`; `&0`]
                    MFD_HAS_INTEGRAL_CONST) THEN
      ASM_REWRITE_TAC[REAL_MUL_LZERO];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(C * exp(--(c * (R + &j) pow 2)) / rho pow 3) * mfd_volume (top,atlas) (g:A->real^N^N) ((Ann:num->A->bool) j)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFD_HAS_INTEGRAL_LE THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                            `g:A->real^N^N`; `h:A->real`; `\x:A. (C * exp(--(c * (R + &j) pow 2)) / rho pow 3)`; `(Ann:num->A->bool) j`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MFD_HAS_INTEGRAL_CONST THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(x:A) IN topspace top /\ ~(x IN (B:real->A->bool) (rho * (R + &j)))`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(x:A) IN (Ann:num->A->bool) j` THEN EXPAND_TAC "Ann" THEN
        REWRITE_TAC[IN_DIFF] THEN ASM SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `rho * (R + &j) <= mfd_dist (top,atlas) (g:A->real^N^N) q x` ASSUME_TAC THENL
       [UNDISCH_TAC `~((x:A) IN (B:real->A->bool) (rho * (R + &j)))` THEN EXPAND_TAC "B" THEN
        REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_SIMP_TAC[REAL_NOT_LT];
        ALL_TAC] THEN
      SUBGOAL_THEN `R + &j <= mfd_dist (top,atlas) (g:A->real^N^N) q x / rho` ASSUME_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= R + &j` ASSUME_TAC THENL
       [MP_TAC(SPEC `j:num` REAL_POS) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `C * exp(--(c * (mfd_dist (top,atlas) (g:A->real^N^N) q x / rho) pow 2)) /
                  rho pow 3` THEN
      ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_POW_LT] THEN
      REWRITE_TAC[REAL_EXP_MONO_LE; REAL_LE_NEG2] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(C * exp(--(c * (R + &j) pow 2)) / rho pow 3) * A * (rho * (R + &j + &1)) pow 3` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_DIV THEN
        ASM_SIMP_TAC[REAL_EXP_POS_LE; REAL_POW_LE; REAL_LT_IMP_LE];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `mfd_volume (top,atlas) (g:A->real^N^N) ((B:real->A->bool) (rho * (R + &j + &1)))` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "B" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `j:num` REAL_POS) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    SUBGOAL_THEN `~(rho = &0)` MP_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_NZ]; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  (* the annuli tile the complement of the ball *)
  SUBGOAL_THEN `!i j. ~(i = j) ==> DISJOINT ((Ann:num->A->bool) i) (Ann j)` ASSUME_TAC THENL
   [MATCH_MP_TAC WLOG_LT THEN REWRITE_TAC[] THEN CONJ_TAC THENL
     [MESON_TAC[DISJOINT_SYM]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN DISCH_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(B:real->A->bool) (rho * (R + &i + &1)) SUBSET B (rho * (R + &j))` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `i < j:num` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN
      SUBGOAL_THEN `&i + &1 <= &j <=> &i < &j` (fun th -> REWRITE_TAC[GSYM th]) THENL
       [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ARITH_TAC;
        REAL_ARITH_TAC];
      EXPAND_TAC "Ann" THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS {(Ann:num->A->bool) j | j IN (:num)} =
                topspace top DIFF (B:real->A->bool) (rho * R)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:A` THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV; IN_DIFF] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `t:A->bool` (CONJUNCTS_THEN2 (X_CHOOSE_TAC `j:num`) MP_TAC)) THEN
      FIRST_X_ASSUM SUBST1_TAC THEN EXPAND_TAC "Ann" THEN REWRITE_TAC[IN_DIFF] THEN
      SUBGOAL_THEN `(B:real->A->bool) (rho * R) SUBSET B (rho * (R + &j))` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        MP_TAC(SPEC `j:num` REAL_POS) THEN ASM_REAL_ARITH_TAC;
        ASM SET_TAC[]];
      STRIP_TAC THEN
      SUBGOAL_THEN `rho * R <= mfd_dist (top,atlas) (g:A->real^N^N) q x /\
                    mfd_joinable (top,atlas) q x` STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC[] THEN
        UNDISCH_TAC `~((x:A) IN (B:real->A->bool) (rho * R))` THEN EXPAND_TAC "B" THEN
        REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_SIMP_TAC[REAL_NOT_LT];
        ALL_TAC] THEN
      MP_TAC(SPEC `(mfd_dist (top,atlas) (g:A->real^N^N) q x - rho * R) / rho` FLOOR_POS) THEN
      ANTS_TAC THENL [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_TAC `j:num`) THEN
      MP_TAC(SPEC `(mfd_dist (top,atlas) (g:A->real^N^N) q x - rho * R) / rho` FLOOR) THEN
      ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_LDIV_EQ] THEN STRIP_TAC THEN
      EXISTS_TAC `(Ann:num->A->bool) j` THEN CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "Ann" THEN EXPAND_TAC "B" THEN
      REWRITE_TAC[IN_DIFF; mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* countable additivity *)
  SUBGOAL_THEN `real_summable (from 0)
                  (\j. mfd_integral (top,atlas) (g:A->real^N^N) ((Ann:num->A->bool) j) h)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
    EXISTS_TAC `\j. C * A * (exp(--(c * (R + &j) pow 2)) * (R + &j + &1) pow 3)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_SUMMABLE_LMUL THEN MATCH_MP_TAC REAL_SUMMABLE_LMUL THEN ASM_SIMP_TAC[];
      EXISTS_TAC `0` THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN BETA_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `Ann:num->A->bool`)) (concl th) &&
        can (find_term ((=) `C:real`)) (concl th))) THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `h:A->real`; `Ann:num->A->bool`;
                 `\j. mfd_integral (top,atlas) (g:A->real^N^N) ((Ann:num->A->bool) j) h`]
                P2BX_MFD_HAS_INTEGRAL_UNIONS_POS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN
    REWRITE_TAC[GSYM MFD_INTEGRABLE_INTEGRAL] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th ->
    is_eq(concl th) && can (find_term ((=) `Ann:num->A->bool`)) (lhs(concl th)))) THEN
  EXPAND_TAC "B" THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `h:A->real`; `topspace top DIFF mfd_ball (top,atlas) (g:A->real^N^N) q (rho * R)`;
                 `real_infsum (from 0)
                    (\j. mfd_integral (top,atlas) (g:A->real^N^N) ((Ann:num->A->bool) j) h)`]
                MFD_HAS_INTEGRAL_INTEGRAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `C * A * real_infsum (from 0)
                         (\j. exp(--(c * (R + &j) pow 2)) * (R + &j + &1) pow 3)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_SERIES_LE THEN
    MAP_EVERY EXISTS_TAC
     [`\j. mfd_integral (top,atlas) (g:A->real^N^N) ((Ann:num->A->bool) j) h`;
      `\j. C * A * (exp(--(c * (R + &j) pow 2)) * (R + &j + &1) pow 3)`; `from 0`] THEN
    ASM_REWRITE_TAC[REAL_SUMS_INFSUM] THEN
    REPEAT(MATCH_MP_TAC REAL_SERIES_LMUL) THEN REWRITE_TAC[REAL_SUMS_INFSUM] THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[]]);;

(* ========================================================================= *)
(* Monotone convergence of the manifold integral of a nonnegative function   *)
(* along an increasing sequence of measurable sets.                          *)
(* ========================================================================= *)

let P2BX_MFD_MONO_UNIONS = prove
 (`!top atlas (g:A->real^N^N) f (S:num->A->bool) B.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ (!x. &0 <= f x) /\
     (!n. mfd_lebesgue_measurable (top,atlas) (S n)) /\ (!n. S n SUBSET S (SUC n)) /\
     (!n. mfd_integrable_on (top,atlas) g f (S n)) /\
     (!n. mfd_integral (top,atlas) g (S n) f <= B)
     ==> mfd_integrable_on (top,atlas) g f (UNIONS {S n | n IN (:num)}) /\
         ((\n. mfd_integral (top,atlas) g (S n) f) --->
          mfd_integral (top,atlas) g (UNIONS {S n | n IN (:num)}) f) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!m n. m <= n ==> (S:num->A->bool) m SUBSET S n` ASSUME_TAC THENL
   [GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[LE] THENL
     [DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[SUBSET_REFL]; ALL_TAC] THEN
    STRIP_TAC THENL
     [ASM_REWRITE_TAC[SUBSET_REFL];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(S:num->A->bool) n` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `D = \n. if n = 0 then (S:num->A->bool) 0 else S n DIFF S (n - 1)` THEN
  SUBGOAL_THEN `!n. mfd_lebesgue_measurable (top,atlas:((A->bool)#(A->real^N))->bool) ((D:num->A->bool) n) /\ D n SUBSET S n`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN EXPAND_TAC "D" THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[SUBSET_REFL; MFD_LEBESGUE_MEASURABLE_DIFF] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. mfd_integrable_on (top,atlas) (g:A->real^N^N) f ((D:num->A->bool) n)`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN MATCH_MP_TAC MFD_INTEGRABLE_SUBSET THEN
    EXISTS_TAC `(S:num->A->bool) n` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b. a < b ==> DISJOINT ((D:num->A->bool) a) (D b)` ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(D:num->A->bool) m SUBSET S (n - 1) /\ D n INTER S (n - 1) = {}`
    MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(S:num->A->bool) m` THEN
        ASM_SIMP_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
        SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        EXPAND_TAC "D" THEN ASM_REWRITE_TAC[] THEN SET_TAC[]];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!m n. ~(m = n) ==> DISJOINT ((D:num->A->bool) m) (D n)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE `~(m = n) ==> m < n \/ n < m:num`)) THEN
    ASM_SIMP_TAC[] THEN ONCE_REWRITE_TAC[DISJOINT_SYM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS {(D:num->A->bool) n | n IN (:num)} = UNIONS {(S:num->A->bool) n | n IN (:num)}`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:A` THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `t:A->bool` (CONJUNCTS_THEN2 (X_CHOOSE_TAC `n:num`) MP_TAC)) THEN
      FIRST_X_ASSUM SUBST1_TAC THEN DISCH_TAC THEN
      EXISTS_TAC `(S:num->A->bool) n` THEN CONJ_TAC THENL
       [EXISTS_TAC `n:num` THEN REWRITE_TAC[]; ASM SET_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `t:A->bool` (CONJUNCTS_THEN2 (X_CHOOSE_TAC `n:num`) MP_TAC)) THEN
      FIRST_X_ASSUM SUBST1_TAC THEN DISCH_TAC THEN
      MP_TAC(ISPEC `\n. (x:A) IN (S:num->A->bool) n` num_WOP) THEN
      REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
      ANTS_TAC THENL [EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(D:num->A->bool) k` THEN CONJ_TAC THENL
       [EXISTS_TAC `k:num` THEN REWRITE_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "D" THEN COND_CASES_TAC THENL
       [UNDISCH_TAC `(x:A) IN (S:num->A->bool) k` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  (* partial sums *)
  SUBGOAL_THEN
   `!n. mfd_integral (top,atlas) (g:A->real^N^N) ((S:num->A->bool) n) f =
        sum(0..n) (\k. mfd_integral (top,atlas) g ((D:num->A->bool) k) f)`
  ASSUME_TAC THENL
   [INDUCT_TAC THENL
     [REWRITE_TAC[SUM_SING_NUMSEG] THEN EXPAND_TAC "D" THEN REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `(S:num->A->bool) (SUC n) = S n UNION (D:num->A->bool) (SUC n) /\
                  DISJOINT (S n) (D (SUC n))` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "D" THEN REWRITE_TAC[NOT_SUC; SUC_SUB1] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `SUC n`)) (concl th) &&
        not(can (find_term (fun t -> is_const t && fst(dest_const t) = "<=")) (concl th)))) THEN
      SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "UNION")) (concl th))) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `f:A->real`; `(S:num->A->bool) n UNION (D:num->A->bool) (SUC n)`;
                   `mfd_integral (top,atlas) (g:A->real^N^N) ((S:num->A->bool) n) f +
                    mfd_integral (top,atlas) g ((D:num->A->bool) (SUC n)) f`]
                  MFD_HAS_INTEGRAL_INTEGRAL) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_HAS_INTEGRAL_UNION THEN
    ASM_REWRITE_TAC[GSYM MFD_INTEGRABLE_INTEGRAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. &0 <= mfd_integral (top,atlas) (g:A->real^N^N) ((D:num->A->bool) k) f`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN MATCH_MP_TAC MFD_HAS_INTEGRAL_LE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `g:A->real^N^N`; `\x:A. &0 * f x`; `f:A->real`;
                          `(D:num->A->bool) k`] THEN
    ASM_REWRITE_TAC[GSYM MFD_INTEGRABLE_INTEGRAL; REAL_MUL_LZERO] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `f:A->real`; `(D:num->A->bool) k`;
                   `mfd_integral (top,atlas) (g:A->real^N^N) ((D:num->A->bool) k) f`; `&0`]
                  MFD_HAS_INTEGRAL_CMUL) THEN
    ASM_REWRITE_TAC[GSYM MFD_INTEGRABLE_INTEGRAL; REAL_MUL_LZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `real_summable (from 0)
                  (\k. mfd_integral (top,atlas) (g:A->real^N^N) ((D:num->A->bool) k) f)`
  ASSUME_TAC THENL
   [REWRITE_TAC[real_summable; GRGV_SUMS_FROM0] THEN
    MP_TAC(ISPECL [`\n. sum(0..n) (\k. mfd_integral (top,atlas) (g:A->real^N^N)
                                         ((D:num->A->bool) k) f)`; `B:real`]
                  CONVERGENT_BOUNDED_INCREASING) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[] THEN CONJ_TAC THENL
       [MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN DISCH_TAC THEN
        MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
        ASM_REWRITE_TAC[FINITE_NUMSEG; SUBSET_NUMSEG; LE_REFL];
        X_GEN_TAC `n:num` THEN
        FIRST_ASSUM((fun th -> REWRITE_TAC[GSYM th]) o check (fun th ->
          is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "sum")) (concl th))) THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= b ==> abs x <= b`) THEN ASM_REWRITE_TAC[] THEN
        FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th ->
          is_forall(concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "sum")) (concl th))) THEN
        MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `D:num->A->bool`;
                 `\k. mfd_integral (top,atlas) (g:A->real^N^N) ((D:num->A->bool) k) f`]
                P2BX_MFD_HAS_INTEGRAL_UNIONS_POS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN
    REWRITE_TAC[GSYM MFD_INTEGRABLE_INTEGRAL] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `f:A->real`; `UNIONS {(S:num->A->bool) n | n IN (:num)}`;
                 `real_infsum (from 0)
                    (\k. mfd_integral (top,atlas) (g:A->real^N^N) ((D:num->A->bool) k) f)`]
                MFD_HAS_INTEGRAL_INTEGRAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM GRGV_SUMS_FROM0; REAL_SUMS_INFSUM] THEN ASM_REWRITE_TAC[]);;

