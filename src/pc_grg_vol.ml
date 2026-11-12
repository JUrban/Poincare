(* ========================================================================= *)
(* pc_grg_vol: Riemannian volume and integration on manifolds, for the       *)
(* definitions of pc_grg_voldefs (countable measurable chart partitions,     *)
(* Lebesgue integration in charts): measurable sets, independence of the    *)
(* partition, linearity, monotonicity, additivity, invariance under         *)
(* isometries, scaling, and volume.  Follows Lee, Introduction to Smooth     *)
(* Manifolds, 2nd ed., Ch. 16 (Prop. 16.41 p. 431, Prop. 16.42 p. 432,      *)
(* Prop. 16.45 p. 432), with measurable partitions for smooth partitions of  *)
(* unity.                                                                    *)
(* ========================================================================= *)

needs "src/pc_grg_voldefs.ml";;
needs "src/pc_grg_isom.ml";;
needs "100/circle.ml";;

prioritize_real();;
type_invention_error := true;;


(* ------------------------------------------------------------------------- *)
(* Series: partial sums, Tonelli and Fubini for double series of reals.      *)
(* ------------------------------------------------------------------------- *)

let GRGV_SUMS_FROM0 = prove
 (`!(f:num->real) l.
        (f real_sums l) (from 0) <=> ((\n. sum(0..n) f) ---> l) sequentially`,
  REWRITE_TAC[real_sums; FROM_INTER_NUMSEG]);;

let GRGV_SUMS_PARTIAL_LE = prove
 (`!(f:num->real) l M.
        (!n. &0 <= f n) /\ (f real_sums l) (from 0)
        ==> sum(0..M) f <= l /\ f M <= l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `sum(0..M) (f:num->real) <= l` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_SERIES_LE THEN
    MAP_EVERY EXISTS_TAC
     [`\n. if n IN 0..M then (f:num->real) n else &0`; `f:num->real`; `from 0`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_SERIES_SUM THEN EXISTS_TAC `0..M` THEN
      REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_FROM; LE_0] THEN
      SIMP_TAC[] THEN MATCH_MP_TAC SUM_EQ THEN SIMP_TAC[];
      GEN_TAC THEN DISCH_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0..M) (f:num->real)` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`{M:num}`; `0..M`; `f:num->real`] SUM_SUBSET_SIMPLE) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; SUM_SING; SING_SUBSET; IN_NUMSEG; LE_0; LE_REFL]]);;

let GRGV_SERIES_FINITE_SUM = prove
 (`!(b:num->num->real) D M.
        (!m. ((\n. b n m) real_sums D m) (from 0))
        ==> ((\n. sum(0..M) (b n)) real_sums sum(0..M) D) (from 0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN SPEC_TAC(`M:num`,`M:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_SERIES_ADD THEN ASM_REWRITE_TAC[]]);;

let GRGV_TONELLI_LE = prove
 (`!(b:num->num->real) B w.
        (!n m. &0 <= b n m) /\ (!n. ((b n) real_sums B n) (from 0)) /\
        (B real_sums w) (from 0)
        ==> ?D w'. (!m. ((\n. b n m) real_sums D m) (from 0)) /\
                   (D real_sums w') (from 0) /\ w' <= w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!m. real_summable (from 0) (\n. (b:num->num->real) n m)`
  MP_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
    EXISTS_TAC `B:num->real` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_SUMS_SUMMABLE THEN EXISTS_TAC `w:real` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`(b:num->num->real) n`; `(B:num->real) n`; `m:num`]
                  GRGV_SUMS_PARTIAL_LE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_SUMS_INFSUM] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!m. &0 <= real_infsum (from 0) (\n. (b:num->num->real) n m)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_SERIES_POS THEN
    MAP_EVERY EXISTS_TAC [`\n. (b:num->num->real) n m`; `from 0`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!M. sum(0..M) (\m. real_infsum (from 0) (\n. (b:num->num->real) n m)) <= w`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_SERIES_LE THEN
    MAP_EVERY EXISTS_TAC
     [`\n. sum(0..M) ((b:num->num->real) n)`; `B:num->real`; `from 0`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC GRGV_SERIES_FINITE_SUM THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`(b:num->num->real) n`; `(B:num->real) n`; `M:num`]
                    GRGV_SUMS_PARTIAL_LE) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?w'. ((\m. real_infsum (from 0) (\n. (b:num->num->real) n m)) real_sums w')
         (from 0)`
  MP_TAC THENL
   [REWRITE_TAC[GRGV_SUMS_FROM0] THEN MATCH_MP_TAC CONVERGENT_REAL_BOUNDED_MONOTONE THEN
    CONJ_TAC THENL
     [REWRITE_TAC[real_bounded; FORALL_IN_IMAGE; IN_UNIV] THEN
      EXISTS_TAC `w:real` THEN X_GEN_TAC `M:num` THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= w ==> abs x <= w`) THEN
      ASM_SIMP_TAC[SUM_POS_LE_NUMSEG];
      DISJ1_TAC THEN GEN_TAC THEN REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
      ASM_REWRITE_TAC[REAL_LE_ADDR]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `w':real`) THEN
  MAP_EVERY EXISTS_TAC
   [`\m. real_infsum (from 0) (\n. (b:num->num->real) n m)`; `w':real`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UBOUND) THEN
  EXISTS_TAC
   `\M. sum(0..M) (\m. real_infsum (from 0) (\n. (b:num->num->real) n m))` THEN
  ASM_REWRITE_TAC[GSYM GRGV_SUMS_FROM0; TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_TRUE]);;

let GRGV_TONELLI = prove
 (`!(b:num->num->real) B w.
        (!n m. &0 <= b n m) /\ (!n. ((b n) real_sums B n) (from 0)) /\
        (B real_sums w) (from 0)
        ==> ?D. (!m. ((\n. b n m) real_sums D m) (from 0)) /\
                (D real_sums w) (from 0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`b:num->num->real`; `B:num->real`; `w:real`] GRGV_TONELLI_LE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:num->real`
   (X_CHOOSE_THEN `w':real` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `D:num->real` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\m n. (b:num->num->real) n m`; `D:num->real`; `w':real`]
                GRGV_TONELLI_LE) THEN
  ASM_REWRITE_TAC[ETA_AX] THEN
  DISCH_THEN(X_CHOOSE_THEN `D':num->real`
   (X_CHOOSE_THEN `w'':real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `D':num->real = B` SUBST_ALL_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN
    MATCH_MP_TAC REAL_SERIES_UNIQUE THEN
    MAP_EVERY EXISTS_TAC [`(b:num->num->real) n`; `from 0`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `w'':real = w` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC REAL_SERIES_UNIQUE THEN
    MAP_EVERY EXISTS_TAC [`B:num->real`; `from 0`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `w':real = w` SUBST_ALL_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]);;

let GRGV_FUBINI_SERIES = prove
 (`!(a:num->num->real) b A B v w.
        (!n m. abs(a n m) <= b n m) /\
        (!n. ((a n) real_sums A n) (from 0)) /\
        (!n. ((b n) real_sums B n) (from 0)) /\
        (A real_sums v) (from 0) /\ (B real_sums w) (from 0)
        ==> ?C D. (!m. ((\n. a n m) real_sums C m) (from 0)) /\
                  (!m. ((\n. b n m) real_sums D m) (from 0)) /\
                  (C real_sums v) (from 0) /\ (D real_sums w) (from 0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`b:num->num->real`; `B:num->real`; `w:real`] GRGV_TONELLI) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[REAL_ABS_POS; REAL_LE_TRANS]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:num->real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`\n m. inv(&2) * ((b:num->num->real) n m + a n m)`;
                 `\n. inv(&2) * ((B:num->real) n + A n)`;
                 `inv(&2) * (w + v)`] GRGV_TONELLI) THEN
  MP_TAC(ISPECL [`\n m. inv(&2) * ((b:num->num->real) n m - a n m)`;
                 `\n. inv(&2) * ((B:num->real) n - A n)`;
                 `inv(&2) * (w - v)`] GRGV_TONELLI) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(!n m. &0 <= inv(&2) * ((b:num->num->real) n m - a n m)) /\
    (!n m. &0 <= inv(&2) * (b n m + a n m))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT GEN_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `m:num`] o check (is_forall o concl)) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(!n. ((\m. inv(&2) * ((b:num->num->real) n m - a n m)) real_sums
          (inv(&2) * (B n - A n))) (from 0)) /\
    (!n. ((\m. inv(&2) * (b n m + a n m)) real_sums
          (inv(&2) * (B n + A n))) (from 0)) /\
    (((\n. inv(&2) * (B n - A n)) real_sums (inv(&2) * (w - v))) (from 0)) /\
    (((\n. inv(&2) * (B n + A n)) real_sums (inv(&2) * (w + v))) (from 0))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY GEN_TAC THEN MATCH_MP_TAC REAL_SERIES_LMUL THEN
    (MATCH_MP_TAC REAL_SERIES_SUB ORELSE MATCH_MP_TAC REAL_SERIES_ADD) THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Q:num->real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `P:num->real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`\m. (P:num->real) m - Q m`; `D:num->real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `m:num` THEN MATCH_MP_TAC REAL_SUMS_EQ THEN
    EXISTS_TAC `\n. inv(&2) * ((b:num->num->real) n m + a n m) -
                    inv(&2) * (b n m - a n m)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_SERIES_SUB THEN ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `v = inv(&2) * (w + v) - inv(&2) * (w - v)` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_SERIES_SUB THEN ASM_REWRITE_TAC[ETA_AX]]);;

(* ------------------------------------------------------------------------- *)
(* Integrals over countable disjoint unions of measurable sets in real^N.    *)
(* ------------------------------------------------------------------------- *)

let GRGV_PARTIAL_UNIONS = prove
 (`!(s:num->real^N->bool) k.
        UNIONS {s m | m IN 0..SUC k} = UNIONS {s m | m IN 0..k} UNION s(SUC k) /\
        UNIONS {s m | m IN 0..0} = s 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NUMSEG_CLAUSES; LE_0] THEN
  REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES; UNIONS_INSERT; UNIONS_0; UNION_EMPTY] THEN
  SET_TAC[]);;

let GRGV_REAL_SUMS_VSUM = prove
 (`!(q:num->real^1) l.
        ((\n. drop(q n)) real_sums drop l) (from 0) <=>
        ((\n. vsum(0..n) q) --> l) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GRGV_SUMS_FROM0; TENDSTO_REAL] THEN
  REWRITE_TAC[o_DEF; LIFT_SUM; LIFT_DROP; ETA_AX]);;

let GRGV_ABS_INTEGRABLE_UNIONS = prove
 (`!(h:real^N->real^1) s.
        (!n. lebesgue_measurable(s n)) /\
        (!m n. ~(m = n) ==> DISJOINT (s m) (s n)) /\
        (!n. h absolutely_integrable_on s n) /\
        real_summable (from 0) (\n. drop(integral (s n) (\y. lift(norm(h y)))))
        ==> h absolutely_integrable_on UNIONS {s n | n IN (:num)} /\
            ((\n. drop(integral (s n) h)) real_sums
             drop(integral (UNIONS {s n | n IN (:num)}) h)) (from 0) /\
            ((\n. drop(integral (s n) (\y. lift(norm(h y))))) real_sums
             drop(integral (UNIONS {s n | n IN (:num)}) (\y. lift(norm(h y)))))
            (from 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!k. UNIONS {s m | m IN 0..k} INTER (s:num->real^N->bool)(SUC k) = {}`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_INTER; IN_UNIONS; IN_ELIM_THM;
                             NOT_IN_EMPTY; IN_NUMSEG] THEN
    X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `SUC k`] o check (is_forall o concl)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. (h:real^N->real^1) absolutely_integrable_on UNIONS {s m | m IN 0..k}`
  ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[GRGV_PARTIAL_UNIONS] THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_UNION THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!(G:real^N->real^1) k.
        (!n. G absolutely_integrable_on (s:num->real^N->bool) n)
        ==> integral (UNIONS {s m | m IN 0..k}) G = vsum(0..k) (\m. integral (s m) G)`
  ASSUME_TAC THENL
   [GEN_TAC THEN INDUCT_TAC THEN
    REWRITE_TAC[GRGV_PARTIAL_UNIONS; VSUM_CLAUSES_NUMSEG; LE_0] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC INTEGRAL_UNION THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; NEGLIGIBLE_EMPTY] THEN
    SUBGOAL_THEN
     `!k. (G:real^N->real^1) absolutely_integrable_on UNIONS {s m | m IN 0..k}`
     (fun th -> SIMP_TAC[th; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE]) THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC[GRGV_PARTIAL_UNIONS] THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_UNION THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (\y. lift(norm((h:real^N->real^1) y))) absolutely_integrable_on
         (s:num->real^N->bool) n`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_SUMS_INFSUM]) THEN
  ABBREV_TAC
   `w = real_infsum (from 0)
          (\n. drop(integral ((s:num->real^N->bool) n)
                       (\y. lift(norm((h:real^N->real^1) y)))))` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `(\y. lift(norm((h:real^N->real^1) y))) integrable_on UNIONS {s n | n IN (:num)}`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM INTEGRABLE_RESTRICT_UNIV] THEN
    MP_TAC(ISPECL
     [`\k y. if y IN UNIONS {(s:num->real^N->bool) m | m IN 0..k}
             then lift(norm((h:real^N->real^1) y)) else vec 0`;
      `\y. if y IN UNIONS {(s:num->real^N->bool) n | n IN (:num)}
           then lift(norm((h:real^N->real^1) y)) else vec 0`;
      `(:real^N)`] MONOTONE_CONVERGENCE_INCREASING) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [GEN_TAC THEN REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV] THEN
        MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_LIFT_NORM_INTEGRABLE THEN
        ASM_REWRITE_TAC[];
        MAP_EVERY X_GEN_TAC [`k:num`; `y:real^N`] THEN DISCH_TAC THEN
        REWRITE_TAC[GRGV_PARTIAL_UNIONS; IN_UNION] THEN
        REPEAT COND_CASES_TAC THEN
        ASM_REWRITE_TAC[REAL_LE_REFL; DROP_VEC; LIFT_DROP; NORM_POS_LE] THEN
        ASM_MESON_TAC[];
        X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
        MATCH_MP_TAC LIM_EVENTUALLY THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
        ASM_CASES_TAC `(y:real^N) IN UNIONS {s n | n IN (:num)}` THENL
         [FIRST_ASSUM(MP_TAC o REWRITE_RULE[IN_ELIM_THM; IN_UNIV] o
            GEN_REWRITE_RULE I [IN_UNIONS]) THEN
          DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool`
           (CONJUNCTS_THEN2 (X_CHOOSE_TAC `n0:num`) ASSUME_TAC)) THEN
          EXISTS_TAC `n0:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
          ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN `(y:real^N) IN UNIONS {s m | m IN 0..k}`
            (fun th -> REWRITE_TAC[th]) THEN
          REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_NUMSEG] THEN
          EXISTS_TAC `(s:num->real^N->bool) n0` THEN
          CONJ_TAC THENL [EXISTS_TAC `n0:num` THEN ASM_ARITH_TAC; ASM_MESON_TAC[]];
          EXISTS_TAC `0` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
          ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN `~((y:real^N) IN UNIONS {s m | m IN 0..k})`
            (fun th -> REWRITE_TAC[th]) THEN
          UNDISCH_TAC `~((y:real^N) IN UNIONS {s n | n IN (:num)})` THEN
          REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[]];
        REWRITE_TAC[bounded; FORALL_IN_GSPEC; IN_UNIV; INTEGRAL_RESTRICT_UNIV] THEN
        EXISTS_TAC `w:real` THEN X_GEN_TAC `k:num` THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`\y. lift(norm((h:real^N->real^1) y))`; `k:num`] o
          check (is_forall o concl)) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        GEN_REWRITE_TAC LAND_CONV [NORM_1] THEN REWRITE_TAC[DROP_VSUM; o_DEF] THEN
        MP_TAC(ISPECL
         [`\n. drop(integral ((s:num->real^N->bool) n)
                       (\y. lift(norm((h:real^N->real^1) y))))`;
          `w:real`; `k:num`] GRGV_SUMS_PARTIAL_LE) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN GEN_TAC THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
          ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; LIFT_DROP; NORM_POS_LE];
          ALL_TAC] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> x <= w /\ y <= w ==> abs x <= w`) THEN
        MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
        MATCH_MP_TAC INTEGRAL_DROP_POS THEN
        ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; LIFT_DROP; NORM_POS_LE]];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(h:real^N->real^1) absolutely_integrable_on UNIONS {s n | n IN (:num)}`
  ASSUME_TAC THENL
   [REWRITE_TAC[ABSOLUTELY_INTEGRABLE_MEASURABLE] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MEASURABLE_ON_COUNTABLE_UNIONS THEN
    REWRITE_TAC[SIMPLE_IMAGE; FORALL_IN_IMAGE; IN_UNIV] THEN
    SIMP_TAC[COUNTABLE_IMAGE; NUM_COUNTABLE] THEN
    ASM_MESON_TAC[ABSOLUTELY_INTEGRABLE_MEASURABLE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pairwise (\i j. negligible ((s:num->real^N->bool) i INTER s j)) (:num)`
  ASSUME_TAC THENL
   [REWRITE_TAC[pairwise; IN_UNIV] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(MESON[NEGLIGIBLE_EMPTY]
     `(t:real^N->bool) = {} ==> negligible t`) THEN
    ASM_MESON_TAC[DISJOINT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[GRGV_REAL_SUMS_VSUM] THEN CONJ_TAC THEN
  MATCH_MP_TAC INTEGRAL_COUNTABLE_UNIONS THEN
  ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; ABSOLUTELY_INTEGRABLE_NORM]);;

(* ------------------------------------------------------------------------- *)
(* The density under chart transitions, and the change of variables between  *)
(* two charts (Lee ISM 2nd ed., Prop. 16.41 p. 431 and Prop. 16.45 p. 432,   *)
(* here with HAS_ABSOLUTE_INTEGRAL_CHANGE_OF_VARIABLES of measure.ml).       *)
(* ------------------------------------------------------------------------- *)

let GRGV_DET_PULLBACK_SQRT = prove
 (`!(J:real^N^N) (G:real^N^N).
        sqrt(det(transp J ** G ** J)) = abs(det J) * sqrt(det G)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DET_MUL; DET_TRANSP] THEN
  SUBGOAL_THEN
   `det(J:real^N^N) * det(G:real^N^N) * det J = det J pow 2 * det G`
  SUBST1_TAC THENL [REAL_ARITH_TAC; REWRITE_TAC[SQRT_MUL; POW_2_SQRT_ABS]]);;

let GRGV_DENSITY_TRANS = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) V psi (g:A->real^N^N) x.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\
        (V,psi) IN atlas /\ x IN U INTER V
        ==> mfd_density atlas (U,phi) g (phi x) =
            abs(det(matrix(chart_jac (U,phi) (V,psi) x))) *
            mfd_density atlas (V,psi) g (psi x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_density] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`;
                `g:A->real^N^N`; `x:A`] METRIC_LOCAL_JAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GRGV_DET_PULLBACK_SQRT]);;

let GRGV_AI_EQ = prove
 (`!(f:real^N->real^1) h s.
        (!x. x IN s ==> f x = h x)
        ==> (f absolutely_integrable_on s <=> h absolutely_integrable_on s) /\
            integral s f = integral s h`,
  MESON_TAC[ABSOLUTELY_INTEGRABLE_EQ; INTEGRAL_EQ]);;

let GRGV_CHART_CHANGE_GEN = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) V psi Q (H:real^N->real^1) H' b.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\ (V,psi) IN atlas /\
        Q SUBSET U INTER V /\ lebesgue_measurable (IMAGE phi Q) /\
        (!x. x IN Q
             ==> H'(phi x) = abs(det(matrix(chart_jac (U,phi) (V,psi) x))) %
                             H(psi x))
        ==> lebesgue_measurable (IMAGE psi Q) /\
            (H' absolutely_integrable_on IMAGE phi Q /\
             integral (IMAGE phi Q) H' = b <=>
             H absolutely_integrable_on IMAGE psi Q /\
             integral (IMAGE psi Q) H = b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `V:A->bool`; `psi:A->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN
   `!x:A. x IN Q
          ==> chart_trans (U,phi) (V:A->bool,psi:A->real^N) (phi x) = psi x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CHART_TRANS_AT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (chart_trans (U:A->bool,phi:A->real^N) (V,psi)) (IMAGE phi Q) =
    IMAGE psi Q`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o] THEN
    MATCH_MP_TAC(SET_RULE
     `(!x:A. x IN s ==> (f:A->real^N) x = g x) ==> IMAGE f s = IMAGE g s`) THEN
    ASM_SIMP_TAC[o_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN IMAGE (phi:A->real^N) Q
        ==> (chart_trans (U,phi) (V:A->bool,psi:A->real^N) has_derivative
             chart_jac (U,phi) (V,psi) (chart_inv (U,phi) y))
            (at y within IMAGE phi Q)`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:A) IN U INTER V` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `chart_inv (U:A->bool,phi:A->real^N) (phi x) = x` SUBST1_TAC THENL
     [ASM_MESON_TAC[IN_INTER]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
    MATCH_MP_TAC CHART_TRANS_HAS_DERIVATIVE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y y'. y IN IMAGE (phi:A->real^N) Q /\ y' IN IMAGE phi Q /\
           chart_trans (U,phi) (V:A->bool,psi:A->real^N) y =
           chart_trans (U,phi) (V,psi) y'
           ==> y = y'`
  ASSUME_TAC THENL
   [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    X_GEN_TAC `x':A` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    DISCH_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `(x:A) IN V /\ (x':A) IN V` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_DIFFERENTIABLE_IMAGE THEN
    ASM_REWRITE_TAC[LE_REFL; differentiable_on; differentiable] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`H:real^N->real^1`;
    `chart_trans (U:A->bool,phi:A->real^N) (V,psi)`;
    `\y. chart_jac (U:A->bool,phi:A->real^N) (V:A->bool,psi:A->real^N)
                   (chart_inv (U,phi) y)`;
    `IMAGE (phi:A->real^N) Q`; `b:real^1`]
   HAS_ABSOLUTE_INTEGRAL_CHANGE_OF_VARIABLES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC(MESON[]
   `(p <=> p') /\ (i:real^1) = i' ==> (p /\ i = b <=> p' /\ i' = b)`) THEN
  MATCH_MP_TAC GRGV_AI_EQ THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:A) IN U INTER V` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN U /\ x IN V` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_INTER]; ALL_TAC] THEN
  ASM_SIMP_TAC[]);;

let GRGV_CHART_CHANGE = prove
 (`!top atlas (g:A->real^N^N) f (U:A->bool) (phi:A->real^N) V psi Q b.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\ (V,psi) IN atlas /\
        Q SUBSET U INTER V /\ lebesgue_measurable (IMAGE phi Q)
        ==> lebesgue_measurable (IMAGE psi Q) /\
            (mfd_chart_integrand atlas g f (U,phi) absolutely_integrable_on
             IMAGE phi Q /\
             integral (IMAGE phi Q) (mfd_chart_integrand atlas g f (U,phi)) = b <=>
             mfd_chart_integrand atlas g f (V,psi) absolutely_integrable_on
             IMAGE psi Q /\
             integral (IMAGE psi Q) (mfd_chart_integrand atlas g f (V,psi)) = b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC GRGV_CHART_CHANGE_GEN THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                        `U:A->bool`; `V:A->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:A) IN U INTER V` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `V:A->bool`; `psi:A->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `(x:A) IN U /\ x IN V` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_INTER]; ALL_TAC] THEN
  ASM_SIMP_TAC[mfd_chart_integrand] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`;
                 `g:A->real^N^N`; `x:A`] GRGV_DENSITY_TRANS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM LIFT_CMUL] THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let GRGV_CHART_CHANGE_NORM = prove
 (`!top atlas (g:A->real^N^N) f (U:A->bool) (phi:A->real^N) V psi Q b.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\ (V,psi) IN atlas /\
        Q SUBSET U INTER V /\ lebesgue_measurable (IMAGE phi Q)
        ==> ((\y. lift(norm(mfd_chart_integrand atlas g f (U,phi) y)))
             absolutely_integrable_on IMAGE phi Q /\
             integral (IMAGE phi Q)
               (\y. lift(norm(mfd_chart_integrand atlas g f (U,phi) y))) = b <=>
             (\y. lift(norm(mfd_chart_integrand atlas g f (V,psi) y)))
             absolutely_integrable_on IMAGE psi Q /\
             integral (IMAGE psi Q)
               (\y. lift(norm(mfd_chart_integrand atlas g f (V,psi) y))) = b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`; `Q:A->bool`;
                 `\y. lift(norm(mfd_chart_integrand atlas (g:A->real^N^N) f
                                   (V:A->bool,psi:A->real^N) y))`;
                 `\y. lift(norm(mfd_chart_integrand atlas (g:A->real^N^N) f
                                   (U:A->bool,phi:A->real^N) y))`;
                 `b:real^1`] GRGV_CHART_CHANGE_GEN) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:A) IN U INTER V` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `V:A->bool`; `psi:A->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `(x:A) IN U /\ x IN V` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_INTER]; ALL_TAC] THEN
  ASM_SIMP_TAC[mfd_chart_integrand] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`;
                 `g:A->real^N^N`; `x:A`] GRGV_DENSITY_TRANS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM LIFT_CMUL; NORM_LIFT] THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_ABS] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Independence of the chart partition (Lee ISM 2nd ed., Ch. 16 p. 432: the  *)
(* integral does not depend on the choices), by refining two partitions and  *)
(* summing the double series of the pieces.                                 *)
(* ------------------------------------------------------------------------- *)

let GRGV_IMAGE_INTER_INJ = prove
 (`!(phi:A->real^N) U A B.
        (!x y. x IN U /\ y IN U /\ phi x = phi y ==> x = y) /\ A SUBSET U
        ==> IMAGE phi (A INTER B) = IMAGE phi A INTER IMAGE phi (U INTER B)`,
  SET_TAC[]);;

let GRGV_PIECE_MEASURABLE = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) d F0.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ d IN atlas /\
        F0 SUBSET FST d /\ lebesgue_measurable (IMAGE (SND d) F0)
        ==> lebesgue_measurable (IMAGE (SND c) (FST c INTER F0))`,
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
    `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`; `F0:A->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!x y. x IN V /\ y IN V /\ (psi:A->real^N) x = psi y ==> x = y`
  ASSUME_TAC THENL [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART_INJ]; ALL_TAC] THEN
  SUBGOAL_THEN `lebesgue_measurable (IMAGE (psi:A->real^N) (U INTER F0))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `IMAGE (psi:A->real^N) (U INTER F0) = IMAGE psi F0 INTER IMAGE psi (V INTER U)`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_INTER THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_OPEN THEN MATCH_MP_TAC CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `V:A->bool`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
    ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(\x:A. mat 1):A->real^N^N`; `\x:A. &0`;
                 `V:A->bool`; `psi:A->real^N`; `U:A->bool`; `phi:A->real^N`;
                 `U INTER F0:A->bool`; `vec 0:real^1`] GRGV_CHART_CHANGE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]]);;

let GRGV_SUMS_PIECES = prove
 (`!(h:real^N->real^1) s.
        (!n. lebesgue_measurable(s n)) /\
        (!m n. ~(m = n) ==> DISJOINT (s m) (s n)) /\
        h absolutely_integrable_on UNIONS {s n | n IN (:num)}
        ==> (!n. h absolutely_integrable_on s n) /\
            ((\n. drop(integral (s n) h)) real_sums
             drop(integral (UNIONS {s n | n IN (:num)}) h)) (from 0) /\
            ((\n. drop(integral (s n) (\y. lift(norm(h y))))) real_sums
             drop(integral (UNIONS {s n | n IN (:num)}) (\y. lift(norm(h y)))))
            (from 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!n. (h:real^N->real^1) absolutely_integrable_on (s:num->real^N->bool) n`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `UNIONS {(s:num->real^N->bool) n | n IN (:num)}` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pairwise (\i j. negligible ((s:num->real^N->bool) i INTER s j)) (:num)`
  ASSUME_TAC THENL
   [REWRITE_TAC[pairwise; IN_UNIV] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(MESON[NEGLIGIBLE_EMPTY]
     `(t:real^N->bool) = {} ==> negligible t`) THEN
    ASM_MESON_TAC[DISJOINT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[GRGV_REAL_SUMS_VSUM] THEN CONJ_TAC THEN
  MATCH_MP_TAC INTEGRAL_COUNTABLE_UNIONS THEN
  ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; ABSOLUTELY_INTEGRABLE_NORM]);;

let GRGV_DISJOINT_IMAGE_INJ = prove
 (`!(f:A->real^N) U A B.
        (!x y. x IN U /\ y IN U /\ f x = f y ==> x = y) /\
        A SUBSET U /\ B SUBSET U /\ DISJOINT A B
        ==> DISJOINT (IMAGE f A) (IMAGE f B)`,
  SET_TAC[]);;

(* Unions of the images of the pieces. *)

let GRGV_UNIONS_IMAGE_PIECES = prove
 (`!(f:A->real^N) E0 S (E:num->A->bool).
        E0 SUBSET S /\ UNIONS {E n | n IN (:num)} = S
        ==> UNIONS {IMAGE f (E0 INTER E n) | n IN (:num)} = IMAGE f E0 /\
            UNIONS {IMAGE f (E n INTER E0) | n IN (:num)} = IMAGE f E0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x:A. x IN E0 ==> ?n. x IN (E:num->A->bool) n` ASSUME_TAC THENL
   [UNDISCH_TAC `UNIONS {(E:num->A->bool) n | n IN (:num)} = S` THEN
    UNDISCH_TAC `(E0:A->bool) SUBSET S` THEN
    REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM; IN_UNIV; SUBSET] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:real^N` THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool`
     (CONJUNCTS_THEN2 (X_CHOOSE_TAC `n:num`) MP_TAC)) THEN
    ASM_REWRITE_TAC[IN_IMAGE; IN_INTER] THEN MESON_TAC[];
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `n:num` o C MATCH_MP (ASSUME `(x:A) IN E0`)) THEN
    EXISTS_TAC `IMAGE (f:A->real^N) (E0 INTER (E:num->A->bool) n)` THEN
    CONJ_TAC THENL [EXISTS_TAC `n:num` THEN REWRITE_TAC[]; ASM SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool`
     (CONJUNCTS_THEN2 (X_CHOOSE_TAC `n:num`) MP_TAC)) THEN
    ASM_REWRITE_TAC[IN_IMAGE; IN_INTER] THEN MESON_TAC[];
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `n:num` o C MATCH_MP (ASSUME `(x:A) IN E0`)) THEN
    EXISTS_TAC `IMAGE (f:A->real^N) ((E:num->A->bool) n INTER E0)` THEN
    CONJ_TAC THENL [EXISTS_TAC `n:num` THEN REWRITE_TAC[]; ASM SET_TAC[]]]);;

(* A piece E0 in the chart c, cut by the pieces of another partition. *)

let GRGV_REFINE_ONE = prove
 (`!top atlas (g:A->real^N^N) f (c:(A->bool)#(A->real^N)) E0 S d E.
        smooth_manifold_atlas top atlas /\ (E0 = {} \/ c IN atlas) /\
        E0 SUBSET FST c /\ lebesgue_measurable (IMAGE (SND c) E0) /\
        mfd_chart_integrand atlas g f c absolutely_integrable_on IMAGE (SND c) E0 /\
        mfd_chart_partition atlas S d E /\ E0 SUBSET S
        ==> (!m. lebesgue_measurable (IMAGE (SND c) (E0 INTER E m))) /\
            (!m. mfd_chart_integrand atlas g f c absolutely_integrable_on
                 IMAGE (SND c) (E0 INTER E m)) /\
            ((\m. drop(integral (IMAGE (SND c) (E0 INTER E m))
                         (mfd_chart_integrand atlas g f c))) real_sums
             drop(integral (IMAGE (SND c) E0) (mfd_chart_integrand atlas g f c)))
            (from 0) /\
            ((\m. drop(integral (IMAGE (SND c) (E0 INTER E m))
                    (\y. lift(norm(mfd_chart_integrand atlas g f c y))))) real_sums
             drop(integral (IMAGE (SND c) E0)
                    (\y. lift(norm(mfd_chart_integrand atlas g f c y)))))
            (from 0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 DISJ_CASES_TAC MP_TAC)) THENL
   [ASM_REWRITE_TAC[INTER_EMPTY; IMAGE_CLAUSES; LEBESGUE_MEASURABLE_EMPTY;
                    ABSOLUTELY_INTEGRABLE_ON_EMPTY; INTEGRAL_EMPTY; DROP_VEC;
                    REAL_SERIES_0];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_chart_partition] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
     (CONJUNCTS_THEN2 (LABEL_TAC "P1") (CONJUNCTS_THEN2 (LABEL_TAC "P2")
                                                        (LABEL_TAC "P3")))
     ASSUME_TAC)))) THEN
  SUBGOAL_THEN
   `!x y. x IN FST c /\ y IN FST c /\
          SND (c:(A->bool)#(A->real^N)) x = SND c y ==> x = y`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
                  SMOOTH_MANIFOLD_ATLAS_CHART_INJ) THEN
    ASM_REWRITE_TAC[PAIR] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. lebesgue_measurable
          (IMAGE (SND (c:(A->bool)#(A->real^N))) (E0 INTER (E:num->A->bool) m))`
  ASSUME_TAC THENL
   [X_GEN_TAC `m:num` THEN
    SUBGOAL_THEN
     `IMAGE (SND (c:(A->bool)#(A->real^N))) (E0 INTER (E:num->A->bool) m) =
      IMAGE (SND c) E0 INTER IMAGE (SND c) (FST c INTER E m)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC GRGV_IMAGE_INTER_INJ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_INTER THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "P1" (MP_TAC o SPEC `m:num`) THEN STRIP_TAC THENL
     [ASM_REWRITE_TAC[INTER_EMPTY; IMAGE_CLAUSES; LEBESGUE_MEASURABLE_EMPTY];
      ALL_TAC] THEN
    MATCH_MP_TAC GRGV_PIECE_MEASURABLE THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
      `(d:num->(A->bool)#(A->real^N)) m`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`mfd_chart_integrand atlas (g:A->real^N^N) f (c:(A->bool)#(A->real^N))`;
    `\m. IMAGE (SND (c:(A->bool)#(A->real^N))) (E0 INTER (E:num->A->bool) m)`]
   GRGV_SUMS_PIECES) THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`SND (c:(A->bool)#(A->real^N))`; `E0:A->bool`; `S:A->bool`;
                 `E:num->A->bool`] GRGV_UNIONS_IMAGE_PIECES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC GRGV_DISJOINT_IMAGE_INJ THEN
  EXISTS_TAC `FST(c:(A->bool)#(A->real^N))` THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "P2" (MP_TAC o C MATCH_MP (ASSUME `~(m:num = n)`) o
                 SPECL [`m:num`; `n:num`]) THEN
  UNDISCH_TAC `(E0:A->bool) SUBSET FST(c:(A->bool)#(A->real^N))` THEN
  SET_TAC[]);;

(* A piece F0 in the chart d, assembled from its pieces in the charts of     *)
(* another partition.                                                        *)

let GRGV_REFINE_TWO = prove
 (`!top atlas (g:A->real^N^N) f (d:(A->bool)#(A->real^N)) F0 S c E
    (a:num->real) b.
        smooth_manifold_atlas top atlas /\ (F0 = {} \/ d IN atlas) /\
        F0 SUBSET FST d /\
        mfd_chart_partition atlas S c E /\ F0 SUBSET S /\
        (!n. lebesgue_measurable (IMAGE (SND(c n)) (E n INTER F0))) /\
        (!n. mfd_chart_integrand atlas g f (c n) absolutely_integrable_on
             IMAGE (SND(c n)) (E n INTER F0)) /\
        (!n. a n = drop(integral (IMAGE (SND(c n)) (E n INTER F0))
                              (mfd_chart_integrand atlas g f (c n)))) /\
        (!n. b n = drop(integral (IMAGE (SND(c n)) (E n INTER F0))
                       (\y. lift(norm(mfd_chart_integrand atlas g f (c n) y))))) /\
        real_summable (from 0) b
        ==> mfd_chart_integrand atlas g f d absolutely_integrable_on
            IMAGE (SND d) F0 /\
            (a real_sums drop(integral (IMAGE (SND d) F0)
                                (mfd_chart_integrand atlas g f d))) (from 0) /\
            (b real_sums drop(integral (IMAGE (SND d) F0)
                    (\y. lift(norm(mfd_chart_integrand atlas g f d y))))) (from 0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 DISJ_CASES_TAC MP_TAC)) THENL
   [ASM_REWRITE_TAC[INTER_EMPTY; IMAGE_CLAUSES; ABSOLUTELY_INTEGRABLE_ON_EMPTY;
                    INTEGRAL_EMPTY; DROP_VEC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(a:num->real) = (\n. &0) /\ (b:num->real) = (\n. &0)`
      (fun th -> REWRITE_TAC[th; REAL_SERIES_0]) THEN
    ASM_REWRITE_TAC[FUN_EQ_THM];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_chart_partition] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
     (CONJUNCTS_THEN2 (LABEL_TAC "P1") (CONJUNCTS_THEN2 (LABEL_TAC "P2")
                                                        (LABEL_TAC "P3")))
     STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!x y. x IN FST d /\ y IN FST d /\
          SND (d:(A->bool)#(A->real^N)) x = SND d y ==> x = y`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(d:(A->bool)#(A->real^N))`; `SND(d:(A->bool)#(A->real^N))`]
                  SMOOTH_MANIFOLD_ATLAS_CHART_INJ) THEN
    ASM_REWRITE_TAC[PAIR] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. lebesgue_measurable
          (IMAGE (SND (d:(A->bool)#(A->real^N))) ((E:num->A->bool) n INTER F0)) /\
        mfd_chart_integrand atlas (g:A->real^N^N) f d absolutely_integrable_on
          IMAGE (SND d) (E n INTER F0) /\
        drop(integral (IMAGE (SND d) (E n INTER F0))
                      (mfd_chart_integrand atlas g f d)) = (a:num->real) n /\
        drop(integral (IMAGE (SND d) (E n INTER F0))
               (\y. lift(norm(mfd_chart_integrand atlas g f d y)))) = b n`
  (LABEL_TAC "PP") THENL
   [X_GEN_TAC `n:num` THEN
    ASM_CASES_TAC `(E:num->A->bool) n INTER F0 = {}` THENL
     [ASM_REWRITE_TAC[IMAGE_CLAUSES; LEBESGUE_MEASURABLE_EMPTY;
                      ABSOLUTELY_INTEGRABLE_ON_EMPTY; INTEGRAL_EMPTY; DROP_VEC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(c:num->(A->bool)#(A->real^N)) n IN atlas /\
                  (E:num->A->bool) n SUBSET FST(c n)`
    STRIP_ASSUME_TAC THENL
     [USE_THEN "P1" (MP_TAC o SPEC `n:num`) THEN ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `f:A->real`;
                   `FST((c:num->(A->bool)#(A->real^N)) n)`;
                   `SND((c:num->(A->bool)#(A->real^N)) n)`;
                   `FST(d:(A->bool)#(A->real^N))`; `SND(d:(A->bool)#(A->real^N))`;
                   `(E:num->A->bool) n INTER F0`;
                   `integral (IMAGE (SND((c:num->(A->bool)#(A->real^N)) n))
                                    ((E:num->A->bool) n INTER F0))
                     (\y. lift(norm(mfd_chart_integrand atlas (g:A->real^N^N) f
                                       (c n) y)))`]
                  GRGV_CHART_CHANGE_NORM) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `f:A->real`;
                   `FST((c:num->(A->bool)#(A->real^N)) n)`;
                   `SND((c:num->(A->bool)#(A->real^N)) n)`;
                   `FST(d:(A->bool)#(A->real^N))`; `SND(d:(A->bool)#(A->real^N))`;
                   `(E:num->A->bool) n INTER F0`;
                   `integral (IMAGE (SND((c:num->(A->bool)#(A->real^N)) n))
                                    ((E:num->A->bool) n INTER F0))
                     (mfd_chart_integrand atlas (g:A->real^N^N) f (c n))`]
                  GRGV_CHART_CHANGE) THEN
    REWRITE_TAC[PAIR] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(E:num->A->bool) n INTER F0 SUBSET
      FST((c:num->(A->bool)#(A->real^N)) n) INTER FST(d:(A->bool)#(A->real^N))`
     (fun th -> REWRITE_TAC[th]) THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\y. lift(norm(mfd_chart_integrand atlas (g:A->real^N^N) f
                      ((c:num->(A->bool)#(A->real^N)) n) y)))
      absolutely_integrable_on
      IMAGE (SND(c n)) ((E:num->A->bool) n INTER F0)`
     (fun th -> REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN ASM_REWRITE_TAC[ETA_AX];
      ALL_TAC] THEN
    STRIP_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`mfd_chart_integrand atlas (g:A->real^N^N) f (d:(A->bool)#(A->real^N))`;
    `\n. IMAGE (SND (d:(A->bool)#(A->real^N))) ((E:num->A->bool) n INTER F0)`]
   GRGV_ABS_INTEGRABLE_UNIONS) THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`SND (d:(A->bool)#(A->real^N))`; `F0:A->bool`; `S:A->bool`;
                 `E:num->A->bool`] GRGV_UNIONS_IMAGE_PIECES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN
   `(\n. drop(integral (IMAGE (SND (d:(A->bool)#(A->real^N)))
                              ((E:num->A->bool) n INTER F0))
                       (mfd_chart_integrand atlas (g:A->real^N^N) f d))) = a /\
    (\n. drop(integral (IMAGE (SND d) (E n INTER F0))
                (\y. lift(norm(mfd_chart_integrand atlas g f d y))))) = b`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN CONJ_TAC THEN X_GEN_TAC `n:num` THEN
    USE_THEN "PP" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[];
    ALL_TAC] THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN USE_THEN "PP" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC GRGV_DISJOINT_IMAGE_INJ THEN
    EXISTS_TAC `FST(d:(A->bool)#(A->real^N))` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "P2" (MP_TAC o C MATCH_MP (ASSUME `~(m:num = n)`) o
                   SPECL [`m:num`; `n:num`]) THEN
    UNDISCH_TAC `(F0:A->bool) SUBSET FST(d:(A->bool)#(A->real^N))` THEN
    SET_TAC[];
    X_GEN_TAC `n:num` THEN USE_THEN "PP" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[];
    ASM_REWRITE_TAC[]]);;

let MFD_HAS_INTEGRAL_PARTITION = prove
 (`!top atlas (g:A->real^N^N) f S v c E.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_has_integral (top,atlas) g f S v /\
        mfd_chart_partition atlas S c E
        ==> (!n. mfd_chart_integrand atlas g f (c n) absolutely_integrable_on
                 IMAGE (SND(c n)) (E n)) /\
            real_summable (from 0)
              (\n. drop(integral (IMAGE (SND(c n)) (E n))
                     (\y. lift(norm(mfd_chart_integrand atlas g f (c n) y))))) /\
            ((\n. drop(integral (IMAGE (SND(c n)) (E n))
                        (mfd_chart_integrand atlas g f (c n)))) real_sums v)
            (from 0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "PC")))) THEN
  REWRITE_TAC[mfd_has_integral] THEN
  DISCH_THEN(X_CHOOSE_THEN `c0:num->(A->bool)#(A->real^N)`
   (X_CHOOSE_THEN `E0:num->A->bool` (CONJUNCTS_THEN2 (LABEL_TAC "PC0")
     (CONJUNCTS_THEN2 (LABEL_TAC "AI0")
       (CONJUNCTS_THEN2 (MP_TAC o REWRITE_RULE[GSYM REAL_SUMS_INFSUM])
                        (LABEL_TAC "SV")))))) THEN
  ABBREV_TAC
   `w = real_infsum (from 0)
         (\n. drop(integral (IMAGE (SND((c0:num->(A->bool)#(A->real^N)) n))
                                   ((E0:num->A->bool) n))
                 (\y. lift(norm(mfd_chart_integrand atlas (g:A->real^N^N) f
                                  (c0 n) y)))))` THEN
  DISCH_THEN(LABEL_TAC "SW") THEN
  USE_THEN "PC0" (MP_TAC o GEN_REWRITE_RULE I [mfd_chart_partition]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "Q1")
   (CONJUNCTS_THEN2 (LABEL_TAC "Q2") (LABEL_TAC "Q3"))) THEN
  USE_THEN "PC" (MP_TAC o GEN_REWRITE_RULE I [mfd_chart_partition]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "R1")
   (CONJUNCTS_THEN2 (LABEL_TAC "R2") (LABEL_TAC "R3"))) THEN
  SUBGOAL_THEN `(!n. (E0:num->A->bool) n SUBSET S) /\
                (!m. (E:num->A->bool) m SUBSET S)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "Q3" (SUBST1_TAC o SYM); USE_THEN "R3" (SUBST1_TAC o SYM)] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (!m. lebesgue_measurable
               (IMAGE (SND((c0:num->(A->bool)#(A->real^N)) n))
                      ((E0:num->A->bool) n INTER (E:num->A->bool) m))) /\
        (!m. mfd_chart_integrand atlas (g:A->real^N^N) f (c0 n)
             absolutely_integrable_on IMAGE (SND(c0 n)) (E0 n INTER E m)) /\
        ((\m. drop(integral (IMAGE (SND(c0 n)) (E0 n INTER E m))
                            (mfd_chart_integrand atlas g f (c0 n)))) real_sums
         drop(integral (IMAGE (SND(c0 n)) (E0 n))
                       (mfd_chart_integrand atlas g f (c0 n)))) (from 0) /\
        ((\m. drop(integral (IMAGE (SND(c0 n)) (E0 n INTER E m))
                (\y. lift(norm(mfd_chart_integrand atlas g f (c0 n) y))))) real_sums
         drop(integral (IMAGE (SND(c0 n)) (E0 n))
                (\y. lift(norm(mfd_chart_integrand atlas g f (c0 n) y))))) (from 0)`
  (LABEL_TAC "ROW") THENL
   [X_GEN_TAC `n:num` THEN MATCH_MP_TAC GRGV_REFINE_ONE THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `S:A->bool`; `c:num->(A->bool)#(A->real^N)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\n m. drop(integral (IMAGE (SND((c0:num->(A->bool)#(A->real^N)) n))
                                ((E0:num->A->bool) n INTER (E:num->A->bool) m))
                  (mfd_chart_integrand atlas (g:A->real^N^N) f (c0 n)))`;
    `\n m. drop(integral (IMAGE (SND((c0:num->(A->bool)#(A->real^N)) n))
                                ((E0:num->A->bool) n INTER (E:num->A->bool) m))
                  (\y. lift(norm(mfd_chart_integrand atlas (g:A->real^N^N) f
                                   (c0 n) y))))`;
    `\n. drop(integral (IMAGE (SND((c0:num->(A->bool)#(A->real^N)) n))
                              ((E0:num->A->bool) n))
                (mfd_chart_integrand atlas (g:A->real^N^N) f (c0 n)))`;
    `\n. drop(integral (IMAGE (SND((c0:num->(A->bool)#(A->real^N)) n))
                              ((E0:num->A->bool) n))
                (\y. lift(norm(mfd_chart_integrand atlas (g:A->real^N^N) f
                                 (c0 n) y))))`;
    `v:real`; `w:real`] GRGV_FUBINI_SERIES) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[ETA_AX] THEN MAP_EVERY X_GEN_TAC [`n:num`; `m:num`] THEN
    REWRITE_TAC[GSYM NORM_1] THEN MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
    REWRITE_TAC[LIFT_DROP; REAL_LE_REFL] THEN
    SUBGOAL_THEN
     `mfd_chart_integrand atlas (g:A->real^N^N) f
        ((c0:num->(A->bool)#(A->real^N)) n) absolutely_integrable_on
      IMAGE (SND(c0 n)) ((E0:num->A->bool) n INTER (E:num->A->bool) m)`
    ASSUME_TAC THENL
     [USE_THEN "ROW" (MP_TAC o SPEC `n:num`) THEN SIMP_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_LIFT_NORM_INTEGRABLE THEN
      ASM_REWRITE_TAC[ETA_AX]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:num->real` (X_CHOOSE_THEN `D:num->real`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!m. mfd_chart_integrand atlas (g:A->real^N^N) f
          ((c:num->(A->bool)#(A->real^N)) m)
        absolutely_integrable_on IMAGE (SND(c m)) ((E:num->A->bool) m) /\
        drop(integral (IMAGE (SND(c m)) (E m))
                      (mfd_chart_integrand atlas g f (c m))) = (C:num->real) m /\
        drop(integral (IMAGE (SND(c m)) (E m))
               (\y. lift(norm(mfd_chart_integrand atlas g f (c m) y)))) =
        (D:num->real) m`
  (LABEL_TAC "COL") THENL
   [X_GEN_TAC `m:num` THEN
    MP_TAC(ISPECL
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
      `f:A->real`; `(c:num->(A->bool)#(A->real^N)) m`; `(E:num->A->bool) m`;
      `S:A->bool`; `c0:num->(A->bool)#(A->real^N)`; `E0:num->A->bool`;
      `\n. drop(integral (IMAGE (SND((c0:num->(A->bool)#(A->real^N)) n))
                                ((E0:num->A->bool) n INTER (E:num->A->bool) m))
                  (mfd_chart_integrand atlas (g:A->real^N^N) f (c0 n)))`;
      `\n. drop(integral (IMAGE (SND((c0:num->(A->bool)#(A->real^N)) n))
                                ((E0:num->A->bool) n INTER (E:num->A->bool) m))
                  (\y. lift(norm(mfd_chart_integrand atlas (g:A->real^N^N) f
                                   (c0 n) y))))`] GRGV_REFINE_TWO) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_SUMS_SUMMABLE THEN EXISTS_TAC `(D:num->real) m` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_SERIES_UNIQUE THENL
     [EXISTS_TAC
       `\n. drop(integral (IMAGE (SND((c0:num->(A->bool)#(A->real^N)) n))
                                 ((E0:num->A->bool) n INTER (E:num->A->bool) m))
                   (mfd_chart_integrand atlas (g:A->real^N^N) f (c0 n)))`;
      EXISTS_TAC
       `\n. drop(integral (IMAGE (SND((c0:num->(A->bool)#(A->real^N)) n))
                                 ((E0:num->A->bool) n INTER (E:num->A->bool) m))
                   (\y. lift(norm(mfd_chart_integrand atlas (g:A->real^N^N) f
                                    (c0 n) y))))`] THEN
    EXISTS_TAC `from 0` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `m:num` THEN USE_THEN "COL" (MP_TAC o SPEC `m:num`) THEN SIMP_TAC[];
    MATCH_MP_TAC REAL_SUMS_SUMMABLE THEN EXISTS_TAC `w:real` THEN
    MATCH_MP_TAC REAL_SUMS_EQ THEN EXISTS_TAC `D:num->real` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    USE_THEN "COL" (MP_TAC o SPEC `m:num`) THEN SIMP_TAC[];
    MATCH_MP_TAC REAL_SUMS_EQ THEN EXISTS_TAC `C:num->real` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    USE_THEN "COL" (MP_TAC o SPEC `m:num`) THEN SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Uniqueness, the integral, measurability, the formula in one chart.       *)
(* ------------------------------------------------------------------------- *)

let GRGV_DENSITY_POS = prove
 (`!atlas (g:A->real^N^N) (c:(A->bool)#(A->real^N)) y.
        riemannian_metric atlas g /\ c IN atlas /\ y IN IMAGE (SND c) (FST c)
        ==> &0 < mfd_density atlas c g y`,
  REWRITE_TAC[riemannian_metric; metric_field; mfd_density] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SQRT_POS_LT THEN
  MATCH_MP_TAC DET_POSITIVE_DEFINITE THEN
  REWRITE_TAC[positive_definite; symmetric_matrix] THEN ASM_MESON_TAC[]);;

let MFD_HAS_INTEGRAL_UNIQUE = prove
 (`!top atlas (g:A->real^N^N) f S v w.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_has_integral (top,atlas) g f S v /\
        mfd_has_integral (top,atlas) g f S w
        ==> v = w`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC))) THEN
  REWRITE_TAC[mfd_has_integral] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num->(A->bool)#(A->real^N)`
   (X_CHOOSE_THEN `E:num->A->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `f:A->real`; `S:A->bool`; `w:real`;
                 `c:num->(A->bool)#(A->real^N)`; `E:num->A->bool`]
                MFD_HAS_INTEGRAL_PARTITION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_SERIES_UNIQUE THEN
  MAP_EVERY EXISTS_TAC
   [`\n. drop(integral (IMAGE (SND((c:num->(A->bool)#(A->real^N)) n))
                              ((E:num->A->bool) n))
               (mfd_chart_integrand atlas (g:A->real^N^N) f (c n)))`;
    `from 0`] THEN
  ASM_REWRITE_TAC[]);;

let MFD_HAS_INTEGRAL_INTEGRAL = prove
 (`!top atlas (g:A->real^N^N) f S v.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_has_integral (top,atlas) g f S v
        ==> mfd_integrable_on (top,atlas) g f S /\
            mfd_integral (top,atlas) g S f = v`,
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[mfd_integrable_on] THEN ASM_MESON_TAC[];
    REWRITE_TAC[mfd_integral] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    REWRITE_TAC[] THEN ASM_MESON_TAC[MFD_HAS_INTEGRAL_UNIQUE]]);;

let GRGV_IMAGE_INTER_UNIONS = prove
 (`!(f:A->real^N) A (E:num->A->bool).
        IMAGE f (A INTER UNIONS {E n | n IN (:num)}) =
        UNIONS {IMAGE f (A INTER E n) | n IN (:num)}`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^N` THEN
  REWRITE_TAC[IN_IMAGE; IN_INTER; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:A` (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t:A->bool`
       (CONJUNCTS_THEN2 (X_CHOOSE_TAC `n:num`) ASSUME_TAC))))) THEN
    EXISTS_TAC `IMAGE (f:A->real^N) (A INTER (E:num->A->bool) n)` THEN
    CONJ_TAC THENL [EXISTS_TAC `n:num` THEN REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `x:A` THEN ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool`
     (CONJUNCTS_THEN2 (X_CHOOSE_TAC `n:num`) MP_TAC)) THEN
    ASM_REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `(E:num->A->bool) n` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `n:num` THEN REWRITE_TAC[]]);;

let MFD_HAS_INTEGRAL_IMP_MEASURABLE = prove
 (`!top atlas (g:A->real^N^N) f S v.
        smooth_manifold_atlas top atlas /\
        mfd_has_integral (top,atlas) g f S v
        ==> mfd_lebesgue_measurable (top,atlas) S`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mfd_has_integral; mfd_chart_partition; mfd_lebesgue_measurable] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `c:num->(A->bool)#(A->real^N)`
     (X_CHOOSE_THEN `E:num->A->bool`
       (CONJUNCTS_THEN2
         (CONJUNCTS_THEN2 (LABEL_TAC "P1")
           (CONJUNCTS_THEN2 (LABEL_TAC "P2") (LABEL_TAC "P3")))
         (K ALL_TAC))))) THEN
  USE_THEN "P3" (SUBST1_TAC o SYM) THEN CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; IN_UNIV] THEN X_GEN_TAC `n:num` THEN
    USE_THEN "P1" (MP_TAC o SPEC `n:num`) THEN STRIP_TAC THENL
     [ASM_REWRITE_TAC[EMPTY_SUBSET]; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `FST((c:num->(A->bool)#(A->real^N)) n)` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[GRGD_ATLAS_CHART];
    X_GEN_TAC `d:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    REWRITE_TAC[GRGV_IMAGE_INTER_UNIONS] THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_COUNTABLE_UNIONS_EXPLICIT THEN
    X_GEN_TAC `n:num` THEN USE_THEN "P1" (MP_TAC o SPEC `n:num`) THEN
    STRIP_TAC THENL
     [ASM_REWRITE_TAC[INTER_EMPTY; IMAGE_CLAUSES; LEBESGUE_MEASURABLE_EMPTY];
      MATCH_MP_TAC GRGV_PIECE_MEASURABLE THEN
      MAP_EVERY EXISTS_TAC
       [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
        `(c:num->(A->bool)#(A->real^N)) n`] THEN
      ASM_REWRITE_TAC[]]]);;

(* The one-piece partition of a set inside one chart. *)

let GRGV_SINGLE_PARTITION = prove
 (`!atlas (c:(A->bool)#(A->real^N)) S.
        c IN atlas /\ S SUBSET FST c /\ lebesgue_measurable (IMAGE (SND c) S)
        ==> mfd_chart_partition atlas S (\n. c) (\n. if n = 0 then S else {})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_chart_partition] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[EMPTY_SUBSET; IMAGE_CLAUSES; LEBESGUE_MEASURABLE_EMPTY];
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT COND_CASES_TAC THEN
    ASM_REWRITE_TAC[DISJOINT_EMPTY] THEN ASM_MESON_TAC[];
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
    X_GEN_TAC `y:A` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `t:A->bool`
       (CONJUNCTS_THEN2 (X_CHOOSE_TAC `n:num`) MP_TAC)) THEN
      ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[NOT_IN_EMPTY];
      DISCH_TAC THEN EXISTS_TAC `S:A->bool` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `0` THEN REWRITE_TAC[]]]);;

let GRGV_SINGLE_SUMS = prove
 (`!(f:A->real^N) S (H:real^N->real^1).
        ((\n. drop(integral (IMAGE f (if n = 0 then S else {})) H)) real_sums
         drop(integral (IMAGE f S) H)) (from 0)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `\n. drop(integral (IMAGE (f:A->real^N) (if n = 0 then S else {}))
                                  (H:real^N->real^1))` GRGV_SUMS_FIRST) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [SIMP_TAC[IMAGE_CLAUSES; INTEGRAL_EMPTY; DROP_VEC]; SIMP_TAC[]]);;

let MFD_HAS_INTEGRAL_CHART = prove
 (`!top atlas (g:A->real^N^N) f c S v.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        c IN atlas /\ S SUBSET FST c
        ==> (mfd_has_integral (top,atlas) g f S v <=>
             lebesgue_measurable (IMAGE (SND c) S) /\
             mfd_chart_integrand atlas g f c absolutely_integrable_on
             IMAGE (SND c) S /\
             drop(integral (IMAGE (SND c) S) (mfd_chart_integrand atlas g f c)) = v)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `lebesgue_measurable (IMAGE (SND (c:(A->bool)#(A->real^N))) S)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `f:A->real`; `S:A->bool`; `v:real`]
                    MFD_HAS_INTEGRAL_IMP_MEASURABLE) THEN
      ASM_REWRITE_TAC[mfd_lebesgue_measurable] THEN
      DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)` o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `FST (c:(A->bool)#(A->real^N)) INTER S = S`
        (fun th -> REWRITE_TAC[th]) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `f:A->real`; `S:A->bool`; `v:real`;
                   `\n:num. (c:(A->bool)#(A->real^N))`;
                   `\n:num. if n = 0 then S else {}:A->bool`]
                  MFD_HAS_INTEGRAL_PARTITION) THEN
    ASM_SIMP_TAC[GRGV_SINGLE_PARTITION] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `0`) (MP_TAC o CONJUNCT2)) THEN
    REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_SERIES_UNIQUE THEN
    MAP_EVERY EXISTS_TAC
     [`\n. drop(integral (IMAGE (SND (c:(A->bool)#(A->real^N)))
                                (if n = 0 then S else {}))
                 (mfd_chart_integrand atlas (g:A->real^N^N) f c))`; `from 0`] THEN
    ASM_REWRITE_TAC[GRGV_SINGLE_SUMS];
    STRIP_TAC THEN REWRITE_TAC[mfd_has_integral] THEN
    MAP_EVERY EXISTS_TAC
     [`\n:num. (c:(A->bool)#(A->real^N))`;
      `\n:num. if n = 0 then S else {}:A->bool`] THEN
    ASM_SIMP_TAC[GRGV_SINGLE_PARTITION] THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; ABSOLUTELY_INTEGRABLE_ON_EMPTY];
      MATCH_MP_TAC REAL_SUMS_SUMMABLE THEN
      EXISTS_TAC `drop(integral (IMAGE (SND (c:(A->bool)#(A->real^N))) S)
                    (\y. lift(norm(mfd_chart_integrand atlas (g:A->real^N^N) f c y))))` THEN
      REWRITE_TAC[GRGV_SINGLE_SUMS];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
      REWRITE_TAC[GRGV_SINGLE_SUMS]]]);;

(* ------------------------------------------------------------------------- *)
(* Linearity, positivity, monotonicity, absolute values, subsets, unions.    *)
(* ------------------------------------------------------------------------- *)

let GRGV_INTEGRAND_EQ_ON = prove
 (`!top atlas (g:A->real^N^N) f h (c:(A->bool)#(A->real^N)) E S.
        smooth_manifold_atlas top atlas /\ (E = {} \/ c IN atlas) /\
        E SUBSET FST c /\ E SUBSET S /\ (!x. x IN S ==> f x = h x)
        ==> !y. y IN IMAGE (SND c) E
                ==> mfd_chart_integrand atlas g f c y =
                    mfd_chart_integrand atlas g h c y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 DISJ_CASES_TAC
    STRIP_ASSUME_TAC)) THENL
   [ASM_REWRITE_TAC[IMAGE_CLAUSES; NOT_IN_EMPTY]; ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; mfd_chart_integrand] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) (SND c x) = x` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
                  CHART_INV) THEN
    ASM_REWRITE_TAC[PAIR] THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:A->real) x = h x` (fun th -> REWRITE_TAC[th]) THEN
  ASM_MESON_TAC[SUBSET]);;

let MFD_HAS_INTEGRAL_EQ = prove
 (`!top atlas (g:A->real^N^N) f h S v.
        smooth_manifold_atlas top atlas /\ (!x. x IN S ==> f x = h x)
        ==> (mfd_has_integral (top,atlas) g f S v <=>
             mfd_has_integral (top,atlas) g h S v)`,
  SUBGOAL_THEN
   `!top atlas (g:A->real^N^N) f h S v.
        smooth_manifold_atlas top atlas /\ (!x. x IN S ==> f x = h x) /\
        mfd_has_integral (top,atlas) g f S v
        ==> mfd_has_integral (top,atlas) g h S v`
  (fun th -> MESON_TAC[th]) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_has_integral] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `c:num->(A->bool)#(A->real^N)`
     (X_CHOOSE_THEN `E:num->A->bool` STRIP_ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`c:num->(A->bool)#(A->real^N)`; `E:num->A->bool`] THEN
  SUBGOAL_THEN
   `!n y. y IN IMAGE (SND((c:num->(A->bool)#(A->real^N)) n)) ((E:num->A->bool) n)
          ==> mfd_chart_integrand atlas (g:A->real^N^N) f (c n) y =
              mfd_chart_integrand atlas g h (c n) y`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC GRGV_INTEGRAND_EQ_ON THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `S:A->bool`] THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [mfd_chart_partition]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `n:num`) (MP_TAC o CONJUNCT2)) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (mfd_chart_integrand atlas (g:A->real^N^N) f
           ((c:num->(A->bool)#(A->real^N)) n) absolutely_integrable_on
         IMAGE (SND(c n)) ((E:num->A->bool) n) <=>
         mfd_chart_integrand atlas g h (c n) absolutely_integrable_on
         IMAGE (SND(c n)) (E n)) /\
        integral (IMAGE (SND(c n)) (E n)) (mfd_chart_integrand atlas g f (c n)) =
        integral (IMAGE (SND(c n)) (E n)) (mfd_chart_integrand atlas g h (c n)) /\
        integral (IMAGE (SND(c n)) (E n))
          (\y. lift(norm(mfd_chart_integrand atlas g f (c n) y))) =
        integral (IMAGE (SND(c n)) (E n))
          (\y. lift(norm(mfd_chart_integrand atlas g h (c n) y)))`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASM_REWRITE_TAC[]) THEN
  GEN_TAC THEN
  MP_TAC(ISPECL
   [`mfd_chart_integrand atlas (g:A->real^N^N) f ((c:num->(A->bool)#(A->real^N)) n)`;
    `mfd_chart_integrand atlas (g:A->real^N^N) h ((c:num->(A->bool)#(A->real^N)) n)`;
    `IMAGE (SND((c:num->(A->bool)#(A->real^N)) n)) ((E:num->A->bool) n)`]
   GRGV_AI_EQ) THEN
  MP_TAC(ISPECL
   [`\y. lift(norm(mfd_chart_integrand atlas (g:A->real^N^N) f
                     ((c:num->(A->bool)#(A->real^N)) n) y))`;
    `\y. lift(norm(mfd_chart_integrand atlas (g:A->real^N^N) h
                     ((c:num->(A->bool)#(A->real^N)) n) y))`;
    `IMAGE (SND((c:num->(A->bool)#(A->real^N)) n)) ((E:num->A->bool) n)`]
   GRGV_AI_EQ) THEN
  ASM_SIMP_TAC[]);;

let MFD_HAS_INTEGRAL_ADD = prove
 (`!top atlas (g:A->real^N^N) f h S v w.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_has_integral (top,atlas) g f S v /\
        mfd_has_integral (top,atlas) g h S w
        ==> mfd_has_integral (top,atlas) g (\x. f x + h x) S (v + w)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC))) THEN
  REWRITE_TAC[mfd_has_integral] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num->(A->bool)#(A->real^N)`
   (X_CHOOSE_THEN `E:num->A->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `h:A->real`; `S:A->bool`; `w:real`;
                 `c:num->(A->bool)#(A->real^N)`; `E:num->A->bool`]
                MFD_HAS_INTEGRAL_PARTITION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`c:num->(A->bool)#(A->real^N)`; `E:num->A->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!c0. mfd_chart_integrand atlas (g:A->real^N^N) (\x. f x + h x) c0 =
         (\y. mfd_chart_integrand atlas g f c0 y + mfd_chart_integrand atlas g h c0 y)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM; mfd_chart_integrand; GSYM LIFT_ADD; REAL_ADD_RDISTRIB];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ADD THEN
    ASM_REWRITE_TAC[ETA_AX];
    MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
    EXISTS_TAC
     `\n. drop(integral (IMAGE (SND((c:num->(A->bool)#(A->real^N)) n))
                               ((E:num->A->bool) n))
                (\y. lift(norm(mfd_chart_integrand atlas (g:A->real^N^N) f (c n) y)))) +
          drop(integral (IMAGE (SND(c n)) (E n))
                (\y. lift(norm(mfd_chart_integrand atlas g h (c n) y))))` THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_SUMMABLE_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN BETA_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_DROP_POS THEN REWRITE_TAC[LIFT_DROP; NORM_POS_LE] THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_LIFT_NORM_INTEGRABLE THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ADD THEN ASM_REWRITE_TAC[ETA_AX];
      REWRITE_TAC[GSYM DROP_ADD] THEN
      ASM_SIMP_TAC[GSYM INTEGRAL_ADD; ABSOLUTELY_INTEGRABLE_IMP_LIFT_NORM_INTEGRABLE;
                   ETA_AX] THEN
      MATCH_MP_TAC INTEGRAL_DROP_LE THEN
      ASM_SIMP_TAC[INTEGRABLE_ADD; ABSOLUTELY_INTEGRABLE_IMP_LIFT_NORM_INTEGRABLE;
                   ABSOLUTELY_INTEGRABLE_ADD; ETA_AX] THEN
      REWRITE_TAC[DROP_ADD; LIFT_DROP; NORM_TRIANGLE]];
    ASM_SIMP_TAC[INTEGRAL_ADD; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; DROP_ADD;
                 ETA_AX] THEN
    MATCH_MP_TAC REAL_SERIES_ADD THEN ASM_REWRITE_TAC[]]);;

let MFD_HAS_INTEGRAL_SUB = prove
 (`!top atlas (g:A->real^N^N) f h S v w.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_has_integral (top,atlas) g f S v /\
        mfd_has_integral (top,atlas) g h S w
        ==> mfd_has_integral (top,atlas) g (\x. f x - h x) S (v - w)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:A. f x - h x) = (\x. f x + -- &1 * h x) /\
                v - w = v + -- &1 * w`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MFD_HAS_INTEGRAL_ADD THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MFD_HAS_INTEGRAL_CMUL THEN ASM_REWRITE_TAC[]);;

let GRGV_HAS_INTEGRAL_POS = prove
 (`!top atlas (g:A->real^N^N) f S v.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_has_integral (top,atlas) g f S v /\ (!x. x IN S ==> &0 <= f x)
        ==> &0 <= v`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC))) THEN
  REWRITE_TAC[mfd_has_integral; mfd_chart_partition] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num->(A->bool)#(A->real^N)`
   (X_CHOOSE_THEN `E:num->A->bool`
     (CONJUNCTS_THEN2
       (CONJUNCTS_THEN2 (LABEL_TAC "P1")
         (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "P3")))
       STRIP_ASSUME_TAC))) THEN
  MATCH_MP_TAC REAL_SERIES_POS THEN
  MAP_EVERY EXISTS_TAC
   [`\n. drop(integral (IMAGE (SND((c:num->(A->bool)#(A->real^N)) n))
                              ((E:num->A->bool) n))
               (mfd_chart_integrand atlas (g:A->real^N^N) f (c n)))`;
    `from 0`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC INTEGRAL_DROP_POS THEN
  ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; ETA_AX] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; mfd_chart_integrand; LIFT_DROP] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  USE_THEN "P1" (MP_TAC o SPEC `n:num`) THEN STRIP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `chart_inv ((c:num->(A->bool)#(A->real^N)) n) (SND (c n) x) = x`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST((c:num->(A->bool)#(A->real^N)) n)`;
                   `SND((c:num->(A->bool)#(A->real^N)) n)`] CHART_INV) THEN
    ASM_REWRITE_TAC[PAIR] THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    USE_THEN "P3" (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC GRGV_DENSITY_POS THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[]]);;

let MFD_HAS_INTEGRAL_LE = prove
 (`!top atlas (g:A->real^N^N) f h S v w.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_has_integral (top,atlas) g f S v /\
        mfd_has_integral (top,atlas) g h S w /\
        (!x. x IN S ==> f x <= h x)
        ==> v <= w`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
  MATCH_MP_TAC GRGV_HAS_INTEGRAL_POS THEN
  MAP_EVERY EXISTS_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
    `\x:A. h x - f x`; `S:A->bool`] THEN
  ASM_SIMP_TAC[MFD_HAS_INTEGRAL_SUB; REAL_SUB_LE]);;

(* Absolute values. *)

let GRGV_ABS_INTEGRAND = prove
 (`!atlas (g:A->real^N^N) f (c:(A->bool)#(A->real^N)) y.
        riemannian_metric atlas g /\ c IN atlas /\ y IN IMAGE (SND c) (FST c)
        ==> mfd_chart_integrand atlas g (\x. abs(f x)) c y =
            lift(norm(mfd_chart_integrand atlas g f c y))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_chart_integrand; NORM_LIFT; REAL_ABS_MUL] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
  REWRITE_TAC[REAL_ABS_REFL] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
  MATCH_MP_TAC GRGV_DENSITY_POS THEN ASM_REWRITE_TAC[]);;

let MFD_INTEGRABLE_ABS = prove
 (`!top atlas (g:A->real^N^N) f S.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_integrable_on (top,atlas) g f S
        ==> mfd_integrable_on (top,atlas) g (\x. abs(f x)) S /\
            abs(mfd_integral (top,atlas) g S f) <=
            mfd_integral (top,atlas) g S (\x. abs(f x))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[MFD_INTEGRABLE_INTEGRAL] THEN
  ABBREV_TAC `v = mfd_integral (top,atlas) (g:A->real^N^N) S f` THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [mfd_has_integral]) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num->(A->bool)#(A->real^N)`
   (X_CHOOSE_THEN `E:num->A->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!n y. y IN IMAGE (SND((c:num->(A->bool)#(A->real^N)) n)) ((E:num->A->bool) n)
          ==> mfd_chart_integrand atlas (g:A->real^N^N) (\x. abs(f x)) (c n) y =
              lift(norm(mfd_chart_integrand atlas g f (c n) y))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `n:num` o CONJUNCT1 o
      GEN_REWRITE_RULE I [mfd_chart_partition]) THEN
    STRIP_TAC THENL [ASM_REWRITE_TAC[IMAGE_CLAUSES; NOT_IN_EMPTY]; ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC GRGV_ABS_INTEGRAND THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (mfd_chart_integrand atlas (g:A->real^N^N) (\x. abs(f x))
           ((c:num->(A->bool)#(A->real^N)) n) absolutely_integrable_on
         IMAGE (SND(c n)) ((E:num->A->bool) n) <=>
         (\y. lift(norm(mfd_chart_integrand atlas g f (c n) y)))
         absolutely_integrable_on IMAGE (SND(c n)) (E n)) /\
        integral (IMAGE (SND(c n)) (E n))
          (mfd_chart_integrand atlas g (\x. abs(f x)) (c n)) =
        integral (IMAGE (SND(c n)) (E n))
          (\y. lift(norm(mfd_chart_integrand atlas g f (c n) y))) /\
        integral (IMAGE (SND(c n)) (E n))
          (\y. lift(norm(mfd_chart_integrand atlas g (\x. abs(f x)) (c n) y))) =
        integral (IMAGE (SND(c n)) (E n))
          (\y. lift(norm(mfd_chart_integrand atlas g f (c n) y)))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL
     [`mfd_chart_integrand atlas (g:A->real^N^N) (\x. abs(f x))
         ((c:num->(A->bool)#(A->real^N)) n)`;
      `\y. lift(norm(mfd_chart_integrand atlas (g:A->real^N^N) f
                       ((c:num->(A->bool)#(A->real^N)) n) y))`;
      `IMAGE (SND((c:num->(A->bool)#(A->real^N)) n)) ((E:num->A->bool) n)`]
     GRGV_AI_EQ) THEN
    MP_TAC(ISPECL
     [`\y. lift(norm(mfd_chart_integrand atlas (g:A->real^N^N) (\x. abs(f x))
                       ((c:num->(A->bool)#(A->real^N)) n) y))`;
      `\y. lift(norm(mfd_chart_integrand atlas (g:A->real^N^N) f
                       ((c:num->(A->bool)#(A->real^N)) n) y))`;
      `IMAGE (SND((c:num->(A->bool)#(A->real^N)) n)) ((E:num->A->bool) n)`]
     GRGV_AI_EQ) THEN
    ASM_SIMP_TAC[NORM_LIFT; REAL_ABS_NORM];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_SUMS_INFSUM] o
    check (fun th -> can (term_match [] `real_summable s f`) (concl th))) THEN
  ABBREV_TAC
   `w = real_infsum (from 0)
         (\n. drop(integral (IMAGE (SND((c:num->(A->bool)#(A->real^N)) n))
                                   ((E:num->A->bool) n))
                 (\y. lift(norm(mfd_chart_integrand atlas (g:A->real^N^N) f
                                  (c n) y)))))` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `mfd_has_integral (top,atlas) (g:A->real^N^N) (\x. abs(f x)) S w`
  ASSUME_TAC THENL
   [REWRITE_TAC[mfd_has_integral] THEN
    MAP_EVERY EXISTS_TAC [`c:num->(A->bool)#(A->real^N)`; `E:num->A->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN
      ASM_REWRITE_TAC[ETA_AX];
      MATCH_MP_TAC REAL_SUMS_SUMMABLE THEN EXISTS_TAC `w:real` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `\x:A. abs(f x)`; `S:A->bool`; `w:real`]
                MFD_HAS_INTEGRAL_INTEGRAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_SERIES_BOUND THEN
  MAP_EVERY EXISTS_TAC
   [`\n. drop(integral (IMAGE (SND((c:num->(A->bool)#(A->real^N)) n))
                              ((E:num->A->bool) n))
               (mfd_chart_integrand atlas (g:A->real^N^N) f (c n)))`;
    `\n. drop(integral (IMAGE (SND((c:num->(A->bool)#(A->real^N)) n))
                              ((E:num->A->bool) n))
               (\y. lift(norm(mfd_chart_integrand atlas (g:A->real^N^N) f (c n) y))))`;
    `from 0`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM NORM_1] THEN MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
  REWRITE_TAC[LIFT_DROP; REAL_LE_REFL] THEN
  ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; ETA_AX] THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_LIFT_NORM_INTEGRABLE THEN
  ASM_REWRITE_TAC[ETA_AX]);;

let GRGV_UNIONS_INTER = prove
 (`!(E:num->A->bool) S.
        S SUBSET UNIONS {E n | n IN (:num)}
        ==> UNIONS {E n INTER S | n IN (:num)} = S`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:A` THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `t:A->bool`
     (CONJUNCTS_THEN2 (X_CHOOSE_TAC `n:num`) MP_TAC)) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN SIMP_TAC[];
    DISCH_TAC THEN
    SUBGOAL_THEN `?n. (x:A) IN (E:num->A->bool) n` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(S:A->bool) SUBSET UNIONS {(E:num->A->bool) n | n IN (:num)}` THEN
      UNDISCH_TAC `(x:A) IN S` THEN
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[];
      EXISTS_TAC `(E:num->A->bool) n INTER S` THEN ASM_REWRITE_TAC[IN_INTER] THEN
      EXISTS_TAC `n:num` THEN REWRITE_TAC[]]]);;

(* Measurable subsets. *)

let MFD_INTEGRABLE_SUBSET = prove
 (`!top atlas (g:A->real^N^N) f S S'.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_integrable_on (top,atlas) g f S' /\
        mfd_lebesgue_measurable (top,atlas) S /\ S SUBSET S'
        ==> mfd_integrable_on (top,atlas) g f S`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC))) THEN
  REWRITE_TAC[mfd_integrable_on; mfd_has_integral; mfd_chart_partition] THEN
  DISCH_THEN(X_CHOOSE_THEN `v':real` (X_CHOOSE_THEN `c:num->(A->bool)#(A->real^N)`
   (X_CHOOSE_THEN `E:num->A->bool`
     (CONJUNCTS_THEN2
       (CONJUNCTS_THEN2 (LABEL_TAC "P1")
         (CONJUNCTS_THEN2 (LABEL_TAC "P2") (LABEL_TAC "P3")))
       STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN
   `!n. lebesgue_measurable (IMAGE (SND((c:num->(A->bool)#(A->real^N)) n))
                                   ((E:num->A->bool) n INTER S))`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN USE_THEN "P1" (MP_TAC o SPEC `n:num`) THEN
    STRIP_TAC THENL
     [ASM_REWRITE_TAC[INTER_EMPTY; IMAGE_CLAUSES; LEBESGUE_MEASURABLE_EMPTY];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `IMAGE (SND((c:num->(A->bool)#(A->real^N)) n)) ((E:num->A->bool) n INTER S) =
      IMAGE (SND(c n)) (E n) INTER IMAGE (SND(c n)) (FST(c n) INTER S)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC GRGV_IMAGE_INTER_INJ THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST((c:num->(A->bool)#(A->real^N)) n)`;
                     `SND((c:num->(A->bool)#(A->real^N)) n)`]
                    SMOOTH_MANIFOLD_ATLAS_CHART_INJ) THEN
      ASM_REWRITE_TAC[PAIR] THEN MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_INTER THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `mfd_lebesgue_measurable
                   (top,atlas:((A->bool)#(A->real^N))->bool) (S:A->bool)` THEN
    REWRITE_TAC[mfd_lebesgue_measurable] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. mfd_chart_integrand atlas (g:A->real^N^N) f
          ((c:num->(A->bool)#(A->real^N)) n) absolutely_integrable_on
        IMAGE (SND(c n)) ((E:num->A->bool) n INTER S)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `IMAGE (SND((c:num->(A->bool)#(A->real^N)) n)) ((E:num->A->bool) n)` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `real_summable (from 0)
     (\n. drop(integral (IMAGE (SND((c:num->(A->bool)#(A->real^N)) n))
                               ((E:num->A->bool) n INTER S))
                (\y. lift(norm(mfd_chart_integrand atlas (g:A->real^N^N) f (c n) y)))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
    EXISTS_TAC
     `\n. drop(integral (IMAGE (SND((c:num->(A->bool)#(A->real^N)) n))
                               ((E:num->A->bool) n))
                (\y. lift(norm(mfd_chart_integrand atlas (g:A->real^N^N) f (c n) y))))` THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN BETA_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_DROP_POS THEN REWRITE_TAC[LIFT_DROP; NORM_POS_LE] THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_LIFT_NORM_INTEGRABLE THEN
      ASM_REWRITE_TAC[ETA_AX];
      MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
      REWRITE_TAC[LIFT_DROP; NORM_POS_LE] THEN
      CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_LIFT_NORM_INTEGRABLE THEN
      ASM_REWRITE_TAC[ETA_AX]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?l. ((\n. drop(integral (IMAGE (SND((c:num->(A->bool)#(A->real^N)) n))
                                  ((E:num->A->bool) n INTER S))
                   (mfd_chart_integrand atlas (g:A->real^N^N) f (c n)))) real_sums l)
        (from 0)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_SERIES_COMPARISON THEN
    EXISTS_TAC
     `\n. drop(integral (IMAGE (SND((c:num->(A->bool)#(A->real^N)) n))
                               ((E:num->A->bool) n INTER S))
                (\y. lift(norm(mfd_chart_integrand atlas (g:A->real^N^N) f (c n) y))))` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[GSYM real_summable]; ALL_TAC] THEN
    EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN BETA_TAC THEN
    REWRITE_TAC[GSYM NORM_1] THEN MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
    REWRITE_TAC[LIFT_DROP; REAL_LE_REFL] THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; ETA_AX] THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_LIFT_NORM_INTEGRABLE THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`l:real`; `c:num->(A->bool)#(A->real^N)`; `\n. (E:num->A->bool) n INTER S`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN USE_THEN "P1" (MP_TAC o SPEC `n:num`) THEN SET_TAC[];
    REPEAT STRIP_TAC THEN
    USE_THEN "P2" (MP_TAC o C MATCH_MP (ASSUME `~(m:num = n)`) o
                   SPECL [`m:num`; `n:num`]) THEN
    SET_TAC[];
    MATCH_MP_TAC GRGV_UNIONS_INTER THEN
    UNDISCH_TAC `(S:A->bool) SUBSET S'` THEN USE_THEN "P3" (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[]]);;

(* Finite additivity: interleaving two partitions. *)

let GRGV_SUMS_INTERLEAVE = prove
 (`!(a:num->real) b v w.
        (a real_sums v) (from 0) /\ (b real_sums w) (from 0)
        ==> ((\n. if EVEN n then a (n DIV 2) else b (n DIV 2)) real_sums (v + w))
            (from 0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:num->real`; `v:real`; `0`] REAL_SERIES_EVEN) THEN
  MP_TAC(ISPECL [`b:num->real`; `w:real`; `0`] REAL_SERIES_ODD) THEN
  ASM_REWRITE_TAC[ARITH] THEN DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `((\i. if ODD i then (b:num->real)(i DIV 2) else &0) real_sums w) (from 0)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\i. if ODD i then (b:num->real)(i DIV 2) else &0`;
                   `w:real`; `1`; `0`] REAL_SUMS_OFFSET_REV) THEN
    ASM_REWRITE_TAC[ARITH; SUM_SING_NUMSEG; REAL_ADD_RID];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_SUMS_EQ THEN
  EXISTS_TAC `\i. (if EVEN i then (a:num->real)(i DIV 2) else &0) +
                  (if ODD i then (b:num->real)(i DIV 2) else &0)` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[GSYM NOT_EVEN] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_ADD_LID; REAL_ADD_RID];
    MATCH_MP_TAC REAL_SERIES_ADD THEN ASM_REWRITE_TAC[]]);;

let GRGV_PARITY_DIV = prove
 (`!m n. (EVEN m <=> EVEN n) /\ m DIV 2 = n DIV 2 ==> m = n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`m:num`; `2`] DIVISION) THEN MP_TAC(SPECL [`n:num`; `2`] DIVISION) THEN
  REWRITE_TAC[ARITH_EQ] THEN
  UNDISCH_TAC `EVEN m <=> EVEN n` THEN REWRITE_TAC[EVEN_MOD] THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let MFD_HAS_INTEGRAL_UNION = prove
 (`!top atlas (g:A->real^N^N) f S S' v w.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_has_integral (top,atlas) g f S v /\
        mfd_has_integral (top,atlas) g f S' w /\ DISJOINT S S'
        ==> mfd_has_integral (top,atlas) g f (S UNION S') (v + w)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)))) THEN
  REWRITE_TAC[mfd_has_integral; mfd_chart_partition] THEN
  DISCH_THEN(X_CHOOSE_THEN `c':num->(A->bool)#(A->real^N)`
   (X_CHOOSE_THEN `E':num->A->bool`
     (CONJUNCTS_THEN2
       (CONJUNCTS_THEN2 (LABEL_TAC "Q1")
         (CONJUNCTS_THEN2 (LABEL_TAC "Q2") (LABEL_TAC "Q3")))
       (CONJUNCTS_THEN2 (LABEL_TAC "QA")
         (CONJUNCTS_THEN2 (LABEL_TAC "QS") (LABEL_TAC "QV")))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num->(A->bool)#(A->real^N)`
   (X_CHOOSE_THEN `E:num->A->bool`
     (CONJUNCTS_THEN2
       (CONJUNCTS_THEN2 (LABEL_TAC "P1")
         (CONJUNCTS_THEN2 (LABEL_TAC "P2") (LABEL_TAC "P3")))
       (CONJUNCTS_THEN2 (LABEL_TAC "PA")
         (CONJUNCTS_THEN2 (LABEL_TAC "PS") (LABEL_TAC "PV")))))) THEN
  SUBGOAL_THEN `(!n. (E:num->A->bool) n SUBSET S) /\
                (!n. (E':num->A->bool) n SUBSET S')`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "P3" (SUBST1_TAC o SYM); USE_THEN "Q3" (SUBST1_TAC o SYM)] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`\n. if EVEN n then (c:num->(A->bool)#(A->real^N)) (n DIV 2)
         else (c':num->(A->bool)#(A->real^N)) (n DIV 2)`;
    `\n. if EVEN n then (E:num->A->bool) (n DIV 2) else (E':num->A->bool) (n DIV 2)`] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN ASM_CASES_TAC `EVEN n` THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN DISCH_TAC THEN
    ASM_CASES_TAC `EVEN m` THEN ASM_CASES_TAC `EVEN n` THEN ASM_REWRITE_TAC[] THENL
     [USE_THEN "P2" MATCH_MP_TAC THEN
      DISCH_TAC THEN UNDISCH_TAC `~(m:num = n)` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC GRGV_PARITY_DIV THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(SET_RULE
       `!s t. DISJOINT s t /\ a SUBSET s /\ b SUBSET t ==> DISJOINT (a:A->bool) b`) THEN
      MAP_EVERY EXISTS_TAC [`S:A->bool`; `S':A->bool`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(SET_RULE
       `!s t. DISJOINT s t /\ a SUBSET t /\ b SUBSET s ==> DISJOINT (a:A->bool) b`) THEN
      MAP_EVERY EXISTS_TAC [`S:A->bool`; `S':A->bool`] THEN ASM_REWRITE_TAC[];
      USE_THEN "Q2" MATCH_MP_TAC THEN
      DISCH_TAC THEN UNDISCH_TAC `~(m:num = n)` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC GRGV_PARITY_DIV THEN ASM_REWRITE_TAC[]];
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:A` THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV; IN_UNION] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `t:A->bool`
       (CONJUNCTS_THEN2 (X_CHOOSE_TAC `n:num`) MP_TAC)) THEN
      ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM SET_TAC[];
      STRIP_TAC THENL
       [SUBGOAL_THEN `?k. (x:A) IN (E:num->A->bool) k` STRIP_ASSUME_TAC THENL
         [UNDISCH_TAC `(x:A) IN S` THEN USE_THEN "P3" (SUBST1_TAC o SYM) THEN
          REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[];
          ALL_TAC] THEN
        EXISTS_TAC `(E:num->A->bool) k` THEN ASM_REWRITE_TAC[] THEN
        EXISTS_TAC `2 * k` THEN REWRITE_TAC[EVEN_DOUBLE] THEN
        AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC DIV_UNIQ THEN
        EXISTS_TAC `0` THEN ARITH_TAC;
        SUBGOAL_THEN `?k. (x:A) IN (E':num->A->bool) k` STRIP_ASSUME_TAC THENL
         [UNDISCH_TAC `(x:A) IN S'` THEN USE_THEN "Q3" (SUBST1_TAC o SYM) THEN
          REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[];
          ALL_TAC] THEN
        EXISTS_TAC `(E':num->A->bool) k` THEN ASM_REWRITE_TAC[] THEN
        EXISTS_TAC `2 * k + 1` THEN
        REWRITE_TAC[EVEN_ADD; EVEN_DOUBLE; ARITH_EVEN] THEN
        AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC DIV_UNIQ THEN
        EXISTS_TAC `1` THEN ARITH_TAC]];
    GEN_TAC THEN ASM_CASES_TAC `EVEN n` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[real_summable] THEN
    EXISTS_TAC
     `real_infsum (from 0)
        (\n. drop(integral (IMAGE (SND((c:num->(A->bool)#(A->real^N)) n))
                                  ((E:num->A->bool) n))
                (\y. lift(norm(mfd_chart_integrand atlas (g:A->real^N^N) f
                                 (c n) y))))) +
      real_infsum (from 0)
        (\n. drop(integral (IMAGE (SND((c':num->(A->bool)#(A->real^N)) n))
                                  ((E':num->A->bool) n))
                (\y. lift(norm(mfd_chart_integrand atlas (g:A->real^N^N) f
                                 (c' n) y)))))` THEN
    MATCH_MP_TAC REAL_SUMS_EQ THEN
    EXISTS_TAC
     `\n. if EVEN n
          then drop(integral (IMAGE (SND((c:num->(A->bool)#(A->real^N)) (n DIV 2)))
                                    ((E:num->A->bool) (n DIV 2)))
                  (\y. lift(norm(mfd_chart_integrand atlas (g:A->real^N^N) f
                                   (c (n DIV 2)) y))))
          else drop(integral (IMAGE (SND((c':num->(A->bool)#(A->real^N)) (n DIV 2)))
                                    ((E':num->A->bool) (n DIV 2)))
                  (\y. lift(norm(mfd_chart_integrand atlas (g:A->real^N^N) f
                                   (c' (n DIV 2)) y))))` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN DISCH_TAC THEN ASM_CASES_TAC `EVEN n` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC GRGV_SUMS_INTERLEAVE THEN
      REWRITE_TAC[REAL_SUMS_INFSUM] THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC REAL_SUMS_EQ THEN
    EXISTS_TAC
     `\n. if EVEN n
          then drop(integral (IMAGE (SND((c:num->(A->bool)#(A->real^N)) (n DIV 2)))
                                    ((E:num->A->bool) (n DIV 2)))
                  (mfd_chart_integrand atlas (g:A->real^N^N) f (c (n DIV 2))))
          else drop(integral (IMAGE (SND((c':num->(A->bool)#(A->real^N)) (n DIV 2)))
                                    ((E':num->A->bool) (n DIV 2)))
                  (mfd_chart_integrand atlas (g:A->real^N^N) f (c' (n DIV 2))))` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN DISCH_TAC THEN ASM_CASES_TAC `EVEN n` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC GRGV_SUMS_INTERLEAVE THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Measurable subsets of a manifold.                                         *)
(* ------------------------------------------------------------------------- *)

let MFD_LEBESGUE_MEASURABLE_OPEN = prove
 (`!top atlas (W:A->bool).
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        open_in top W
        ==> mfd_lebesgue_measurable (top,atlas) W`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_lebesgue_measurable] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET];
    X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_OPEN THEN
    MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
    ASM_MESON_TAC[MFDM_CHART]]);;

let MFD_LEBESGUE_MEASURABLE_DIFF = prove
 (`!top atlas (S:A->bool) S'.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        mfd_lebesgue_measurable (top,atlas) S /\
        mfd_lebesgue_measurable (top,atlas) S'
        ==> mfd_lebesgue_measurable (top,atlas) (S DIFF S')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_lebesgue_measurable] THEN STRIP_TAC THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER (S DIFF S')) =
    IMAGE (SND c) (FST c INTER S) DIFF IMAGE (SND c) (FST c INTER S')`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER; IN_DIFF] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC LEBESGUE_MEASURABLE_DIFF THEN ASM_SIMP_TAC[]]);;

let MFD_LEBESGUE_MEASURABLE_CLOSED = prove
 (`!top atlas (C:A->bool).
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        closed_in top C
        ==> mfd_lebesgue_measurable (top,atlas) C`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [closed_in]) THEN
  SUBGOAL_THEN `C:A->bool = topspace top DIFF (topspace top DIFF C)` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MFD_LEBESGUE_MEASURABLE_DIFF THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN MATCH_MP_TAC MFD_LEBESGUE_MEASURABLE_OPEN THEN
  ASM_REWRITE_TAC[OPEN_IN_TOPSPACE]);;

let MFD_LEBESGUE_MEASURABLE_COUNTABLE_UNIONS = prove
 (`!top atlas (S:num->A->bool).
        (!n. mfd_lebesgue_measurable
               (top,atlas:((A->bool)#(A->real^N))->bool) (S n))
        ==> mfd_lebesgue_measurable (top,atlas) (UNIONS {S n | n IN (:num)})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_lebesgue_measurable] THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; IN_UNIV] THEN ASM_MESON_TAC[];
    X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    REWRITE_TAC[GRGV_IMAGE_INTER_UNIONS] THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_COUNTABLE_UNIONS_EXPLICIT THEN
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Scaling the metric: integrals scale by sqrt(k pow N).                     *)
(* ------------------------------------------------------------------------- *)

let GRGV_INTEGRAND_SCALE = prove
 (`!atlas (g:A->real^N^N) f (c:(A->bool)#(A->real^N)) k.
        mfd_chart_integrand atlas (\x. k %% g x) f c =
        mfd_chart_integrand atlas g (\x. sqrt(k pow dimindex(:N)) * f x) c`,
  REWRITE_TAC[FUN_EQ_THM; mfd_chart_integrand; mfd_density; METRIC_LOCAL_CMUL;
              DET_CMUL; SQRT_MUL] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let MFD_HAS_INTEGRAL_SCALE = prove
 (`!top atlas (g:A->real^N^N) f S v k.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ &0 < k
        ==> (mfd_has_integral (top,atlas) (\x. k %% g x) f S
                              (sqrt(k pow dimindex(:N)) * v) <=>
             mfd_has_integral (top,atlas) g f S v)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_has_integral; GRGV_INTEGRAND_SCALE] THEN
  REWRITE_TAC[GSYM mfd_has_integral] THEN
  ABBREV_TAC `s = sqrt(k pow dimindex(:N))` THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN MATCH_MP_TAC SQRT_POS_LT THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC `inv s:real` o MATCH_MP MFD_HAS_INTEGRAL_CMUL) THEN
    ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_LID;
                 ETA_AX];
    DISCH_THEN(MP_TAC o SPEC `s:real` o MATCH_MP MFD_HAS_INTEGRAL_CMUL) THEN
    REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Volume.                                                                   *)
(* ------------------------------------------------------------------------- *)

let GRGV_INTEGRAND_ONE = prove
 (`!atlas (g:A->real^N^N) (c:(A->bool)#(A->real^N)).
        mfd_chart_integrand atlas g (\x. &1) c = (\y. lift(mfd_density atlas c g y))`,
  REWRITE_TAC[FUN_EQ_THM; mfd_chart_integrand; REAL_MUL_LID]);;

let MFD_HAS_VOLUME_CHART = prove
 (`!top atlas (g:A->real^N^N) c S v.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        c IN atlas /\ S SUBSET FST c
        ==> (mfd_has_volume (top,atlas) g S v <=>
             lebesgue_measurable (IMAGE (SND c) S) /\
             (\y. lift(mfd_density atlas c g y)) absolutely_integrable_on
             IMAGE (SND c) S /\
             drop(integral (IMAGE (SND c) S) (\y. lift(mfd_density atlas c g y))) = v)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_has_volume] THEN
  ASM_SIMP_TAC[MFD_HAS_INTEGRAL_CHART; GRGV_INTEGRAND_ONE]);;

let MFD_HAS_VOLUME_UNIQUE = prove
 (`!top atlas (g:A->real^N^N) S v w.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_has_volume (top,atlas) g S v /\ mfd_has_volume (top,atlas) g S w
        ==> v = w`,
  REWRITE_TAC[mfd_has_volume] THEN MESON_TAC[MFD_HAS_INTEGRAL_UNIQUE]);;

let MFD_HAS_VOLUME_VOLUME = prove
 (`!top atlas (g:A->real^N^N) S v.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_has_volume (top,atlas) g S v
        ==> mfd_volume (top,atlas) g S = v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_volume] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN REWRITE_TAC[] THEN
  ASM_MESON_TAC[MFD_HAS_VOLUME_UNIQUE]);;

let MFD_HAS_VOLUME_POS_LE = prove
 (`!top atlas (g:A->real^N^N) S v.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_has_volume (top,atlas) g S v
        ==> &0 <= v`,
  REWRITE_TAC[mfd_has_volume] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC GRGV_HAS_INTEGRAL_POS THEN
  MAP_EVERY EXISTS_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
    `\x:A. &1`; `S:A->bool`] THEN
  ASM_REWRITE_TAC[REAL_POS]);;

let MFD_HAS_VOLUME_UNION = prove
 (`!top atlas (g:A->real^N^N) S S' v w.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_has_volume (top,atlas) g S v /\ mfd_has_volume (top,atlas) g S' w /\
        DISJOINT S S'
        ==> mfd_has_volume (top,atlas) g (S UNION S') (v + w)`,
  REWRITE_TAC[mfd_has_volume] THEN MESON_TAC[MFD_HAS_INTEGRAL_UNION]);;

let MFD_HAS_VOLUME_MONO = prove
 (`!top atlas (g:A->real^N^N) S S' v w.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_has_volume (top,atlas) g S v /\ mfd_has_volume (top,atlas) g S' w /\
        S SUBSET S'
        ==> v <= w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `mfd_lebesgue_measurable (top,atlas:((A->bool)#(A->real^N))->bool)
      ((S':A->bool) DIFF S)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_LEBESGUE_MEASURABLE_DIFF THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[mfd_has_volume]) THEN
    ASM_MESON_TAC[MFD_HAS_INTEGRAL_IMP_MEASURABLE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_integrable_on (top,atlas) (g:A->real^N^N) (\x. &1) ((S':A->bool) DIFF S)`
  MP_TAC THENL
   [MATCH_MP_TAC MFD_INTEGRABLE_SUBSET THEN EXISTS_TAC `S':A->bool` THEN
    ASM_REWRITE_TAC[SUBSET_DIFF; mfd_integrable_on] THEN
    ASM_MESON_TAC[mfd_has_volume];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_integrable_on; GSYM mfd_has_volume] THEN
  DISCH_THEN(X_CHOOSE_TAC `u:real`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `S:A->bool`; `(S':A->bool) DIFF S`;
                 `v:real`; `u:real`] MFD_HAS_VOLUME_UNION) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(S:A->bool) UNION (S' DIFF S) = S'` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `w = v + u` SUBST1_TAC THENL
   [ASM_MESON_TAC[MFD_HAS_VOLUME_UNIQUE]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= u ==> v <= v + u`) THEN
  ASM_MESON_TAC[MFD_HAS_VOLUME_POS_LE]);;

let MFD_HAS_VOLUME_SUBSET = prove
 (`!top atlas (g:A->real^N^N) S S' w.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_lebesgue_measurable (top,atlas) S /\ S SUBSET S' /\
        mfd_has_volume (top,atlas) g S' w
        ==> mfd_has_volume (top,atlas) g S (mfd_volume (top,atlas) g S) /\
            mfd_volume (top,atlas) g S <= w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_integrable_on (top,atlas) (g:A->real^N^N) (\x. &1) S` MP_TAC THENL
   [MATCH_MP_TAC MFD_INTEGRABLE_SUBSET THEN EXISTS_TAC `S':A->bool` THEN
    ASM_REWRITE_TAC[mfd_integrable_on] THEN ASM_MESON_TAC[mfd_has_volume];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_integrable_on; GSYM mfd_has_volume] THEN
  DISCH_THEN(X_CHOOSE_TAC `u:real`) THEN
  SUBGOAL_THEN `mfd_volume (top,atlas) (g:A->real^N^N) S = u` SUBST1_TAC THENL
   [MATCH_MP_TAC MFD_HAS_VOLUME_VOLUME THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_HAS_VOLUME_MONO THEN
  ASM_MESON_TAC[]);;

let MFD_HAS_VOLUME_SCALE = prove
 (`!top atlas (g:A->real^N^N) S v k.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ &0 < k
        ==> (mfd_has_volume (top,atlas) (\x. k %% g x) S
                            (sqrt(k pow dimindex(:N)) * v) <=>
             mfd_has_volume (top,atlas) g S v)`,
  REWRITE_TAC[mfd_has_volume] THEN MESON_TAC[MFD_HAS_INTEGRAL_SCALE]);;

(* Flat real^N: the volume is Lebesgue measure. *)

let MFD_HAS_VOLUME_EUCLIDEAN = prove
 (`!U S:real^N->bool v.
        open U /\ S SUBSET U
        ==> (mfd_has_volume (subtopology euclidean U,{(U,\x:real^N. x)})
                            (\x. mat 1) S v <=>
             S has_measure v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `U:real^N->bool` MFD_EUCLIDEAN_OPEN) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (U:real^N->bool)`;
                 `{(U:real^N->bool,\x:real^N. x)}`;
                 `(\x. mat 1):real^N->real^N^N`; `(U:real^N->bool,\x:real^N. x)`;
                 `S:real^N->bool`; `v:real`] MFD_HAS_VOLUME_CHART) THEN
  ASM_REWRITE_TAC[IN_SING; FST; SND; IMAGE_ID] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`\y:real^N. lift(mfd_density {(U:real^N->bool,\x:real^N. x)} (U,\x. x)
                                    (\x. mat 1) y)`;
                 `\y:real^N. vec 1:real^1`; `S:real^N->bool`] GRGV_AI_EQ) THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM LIFT_NUM] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC GRGV_DENSITY_EUCLIDEAN THEN ASM SET_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[ABSOLUTELY_INTEGRABLE_ON_CONST; VEC_EQ; ARITH_EQ] THEN
  REWRITE_TAC[HAS_MEASURE_MEASURABLE_MEASURE] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[INTEGRAL_MEASURE; LIFT_DROP;
                                          MEASURABLE_IMP_LEBESGUE_MEASURABLE] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[INTEGRAL_MEASURE; LIFT_DROP]);;

(* Teeth: Euclidean balls in the plane and in space. *)

let MFD_VOLUME_EUCLIDEAN_BALL_2 = prove
 (`!r. &0 <= r
       ==> mfd_has_volume (euclidean,{((:real^2),\x:real^2. x)}) (\x. mat 1)
                          (ball(vec 0,r)) (pi * r pow 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^2)`; `ball(vec 0:real^2,r)`; `pi * r pow 2`]
                MFD_HAS_VOLUME_EUCLIDEAN) THEN
  REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; SUBTOPOLOGY_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[HAS_MEASURE_MEASURABLE_MEASURE; MEASURABLE_BALL; AREA_BALL]);;

let MFD_VOLUME_EUCLIDEAN_BALL_3 = prove
 (`!r. &0 <= r
       ==> mfd_has_volume (euclidean,{((:real^3),\x:real^3. x)}) (\x. mat 1)
                          (ball(vec 0,r)) (&4 / &3 * pi * r pow 3)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^3)`; `ball(vec 0:real^3,r)`; `&4 / &3 * pi * r pow 3`]
                MFD_HAS_VOLUME_EUCLIDEAN) THEN
  REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; SUBTOPOLOGY_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[HAS_MEASURE_MEASURABLE_MEASURE; MEASURABLE_BALL; VOLUME_BALL]);;

(* ------------------------------------------------------------------------- *)
(* Invariance under isometries (Lee ISM 2nd ed., Prop. 16.42(c) p. 432,      *)
(* diffeomorphism invariance, for the Riemannian density of Prop. 16.45      *)
(* p. 432, which an isometry pulls back to the Riemannian density).  First   *)
(* the change of variables between a chart of the source and a chart of the  *)
(* target, through the transition map SND d o f o chart_inv c.               *)
(* ------------------------------------------------------------------------- *)

let GRGV_ISOMETRY_TRANS = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) f f' c d.
        smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
        mfd_isometry (top,atlas) g (top',atlas') g' f f' /\
        c IN atlas /\ d IN atlas'
        ==> open (IMAGE (SND c) {x | x IN FST c /\ f x IN FST d}) /\
            (!y. y IN IMAGE (SND c) {x | x IN FST c /\ f x IN FST d}
                 ==> (SND d o f o chart_inv c) differentiable (at y)) /\
            (!y y'. y IN IMAGE (SND c) {x | x IN FST c /\ f x IN FST d} /\
                    y' IN IMAGE (SND c) {x | x IN FST c /\ f x IN FST d} /\
                    (SND d o f o chart_inv c) y = (SND d o f o chart_inv c) y'
                    ==> y = y') /\
            (!y. y IN IMAGE (SND c) {x | x IN FST c /\ f x IN FST d}
                 ==> metric_local atlas c g y =
                     mpullback (SND d o f o chart_inv c)
                               (metric_local atlas' d g') y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GRGD_ISOMETRY_FACTS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `d:(B->bool)#(B->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FST(c:(A->bool)#(A->real^N)) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `{x | x IN FST c INTER topspace top /\
         (f:A->B) x IN FST(d:(B->bool)#(B->real^N))} =
    {x | x IN FST(c:(A->bool)#(A->real^N)) /\ f x IN FST d}`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `open (IMAGE (SND(c:(A->bool)#(A->real^N)))
               {x | x IN FST c /\ (f:A->B) x IN FST(d:(B->bool)#(B->real^N))})`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`; `d:(B->bool)#(B->real^N)`;
                   `topspace top:A->bool`; `f:A->B`] MFDM_CHART_DOMAIN_OPEN) THEN
    ASM_SIMP_TAC[OPEN_IN_TOPSPACE];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC
     `IMAGE (SND(c:(A->bool)#(A->real^N)))
            {x | x IN FST c /\ (f:A->B) x IN FST(d:(B->bool)#(B->real^N))}` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `mfd_smooth_map (atlas:((A->bool)#(A->real^N))->bool)
                  (atlas':((B->bool)#(B->real^N))->bool) (topspace top) (f:A->B)` THEN
    REWRITE_TAC[mfd_smooth_map] THEN
    DISCH_THEN(MP_TAC o SPECL [`c:(A->bool)#(A->real^N)`;
                               `d:(B->bool)#(B->real^N)`]) THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`y:real^N`; `y':real^N`] THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC)
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `x':A` STRIP_ASSUME_TAC) MP_TAC)) THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[o_THM] THEN DISCH_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `(f:A->B) x = f x'` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[SUBSET];
    UNDISCH_TAC
     `mfd_isometry (top,atlas) (g:A->real^N^N) (top',atlas') (g':B->real^N^N)
                   f f'` THEN
    REWRITE_TAC[mfd_isometry] THEN
    DISCH_THEN(MP_TAC o SPECL [`c:(A->bool)#(A->real^N)`;
                               `d:(B->bool)#(B->real^N)`] o CONJUNCT2) THEN
    ASM_REWRITE_TAC[]]);;

let GRGV_ISOMETRY_DENSITY = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) f f' c d x.
        smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
        mfd_isometry (top,atlas) g (top',atlas') g' f f' /\
        c IN atlas /\ d IN atlas' /\ x IN FST c /\ f x IN FST d
        ==> mfd_density atlas c g (SND c x) =
            abs(det(matrix(frechet_derivative (SND d o f o chart_inv c)
                                              (at (SND c x))))) *
            mfd_density atlas' d g' (SND d (f x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^N))->bool`; `g':B->real^N^N`;
                 `f:A->B`; `f':B->A`; `c:(A->bool)#(A->real^N)`;
                 `d:(B->bool)#(B->real^N)`] GRGV_ISOMETRY_TRANS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `SND(c:(A->bool)#(A->real^N)) x` o last o CONJUNCTS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[mfd_density] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[mpullback; GRGV_DET_PULLBACK_SQRT] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ASM_MESON_TAC[MFDM_CHART]);;

let GRGV_ISOMETRY_CHANGE_GEN = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) f f' c d Q
    (H:real^N->real^1) H' b.
        smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
        mfd_isometry (top,atlas) g (top',atlas') g' f f' /\
        c IN atlas /\ d IN atlas' /\
        Q SUBSET {x | x IN FST c /\ f x IN FST d} /\
        lebesgue_measurable (IMAGE (SND c) Q) /\
        (!x. x IN Q
             ==> H'(SND c x) =
                 abs(det(matrix(frechet_derivative (SND d o f o chart_inv c)
                                                   (at (SND c x))))) %
                 H(SND d (f x)))
        ==> lebesgue_measurable (IMAGE (SND d) (IMAGE f Q)) /\
            (H' absolutely_integrable_on IMAGE (SND c) Q /\
             integral (IMAGE (SND c) Q) H' = b <=>
             H absolutely_integrable_on IMAGE (SND d) (IMAGE f Q) /\
             integral (IMAGE (SND d) (IMAGE f Q)) H = b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^N))->bool`; `g':B->real^N^N`;
                 `f:A->B`; `f':B->A`; `c:(A->bool)#(A->real^N)`;
                 `d:(B->bool)#(B->real^N)`] GRGV_ISOMETRY_TRANS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "TINJ") ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `IMAGE (SND(c:(A->bool)#(A->real^N))) Q SUBSET
    IMAGE (SND c) {x | x IN FST c /\ (f:A->B) x IN FST(d:(B->bool)#(B->real^N))}`
  ASSUME_TAC THENL [ASM_SIMP_TAC[IMAGE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN Q
        ==> (SND(d:(B->bool)#(B->real^N)) o (f:A->B) o
             chart_inv(c:(A->bool)#(A->real^N))) (SND c x) = SND d (f x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (SND(d:(B->bool)#(B->real^N)) o (f:A->B) o
           chart_inv(c:(A->bool)#(A->real^N))) (IMAGE (SND c) Q) =
    IMAGE (SND d) (IMAGE f Q)`
  ASSUME_TAC THENL
   [REMOVE_THEN "TINJ" (K ALL_TAC) THEN REWRITE_TAC[GSYM IMAGE_o] THEN
    MATCH_MP_TAC(SET_RULE
     `(!x:A. x IN s ==> (u:A->real^N) x = v x) ==> IMAGE u s = IMAGE v s`) THEN
    ASM_SIMP_TAC[o_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN IMAGE (SND(c:(A->bool)#(A->real^N))) Q
        ==> ((SND(d:(B->bool)#(B->real^N)) o (f:A->B) o chart_inv c) has_derivative
             frechet_derivative (SND d o f o chart_inv c) (at y))
            (at y within IMAGE (SND c) Q)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
    REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y y'. y IN IMAGE (SND(c:(A->bool)#(A->real^N))) Q /\
           y' IN IMAGE (SND c) Q /\
           (SND(d:(B->bool)#(B->real^N)) o (f:A->B) o chart_inv c) y =
           (SND d o f o chart_inv c) y'
           ==> y = y'`
  (LABEL_TAC "QINJ") THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  REMOVE_THEN "TINJ" (K ALL_TAC) THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `IMAGE (SND(d:(B->bool)#(B->real^N))) (IMAGE (f:A->B) Q) =
      IMAGE (SND d o f o chart_inv(c:(A->bool)#(A->real^N))) (IMAGE (SND c) Q)`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_DIFFERENTIABLE_IMAGE THEN
    ASM_REWRITE_TAC[LE_REFL; differentiable_on; differentiable] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`H:real^N->real^1`;
    `SND(d:(B->bool)#(B->real^N)) o (f:A->B) o chart_inv(c:(A->bool)#(A->real^N))`;
    `\y. frechet_derivative (SND(d:(B->bool)#(B->real^N)) o (f:A->B) o
                             chart_inv(c:(A->bool)#(A->real^N))) (at y)`;
    `IMAGE (SND(c:(A->bool)#(A->real^N))) Q`; `b:real^1`]
   HAS_ABSOLUTE_INTEGRAL_CHANGE_OF_VARIABLES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REMOVE_THEN "QINJ" (K ALL_TAC) THEN
  MATCH_MP_TAC(MESON[]
   `(p <=> p') /\ (i:real^1) = i' ==> (p /\ i = b <=> p' /\ i' = b)`) THEN
  MATCH_MP_TAC GRGV_AI_EQ THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN ASM_SIMP_TAC[]);;

let GRGV_ISOMETRY_CHANGE = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) f f' c d Q h b.
        smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
        mfd_isometry (top,atlas) g (top',atlas') g' f f' /\
        c IN atlas /\ d IN atlas' /\
        Q SUBSET {x | x IN FST c /\ f x IN FST d} /\
        lebesgue_measurable (IMAGE (SND c) Q)
        ==> lebesgue_measurable (IMAGE (SND d) (IMAGE f Q)) /\
            (mfd_chart_integrand atlas g (h o f) c absolutely_integrable_on
             IMAGE (SND c) Q /\
             integral (IMAGE (SND c) Q) (mfd_chart_integrand atlas g (h o f) c) = b <=>
             mfd_chart_integrand atlas' g' h d absolutely_integrable_on
             IMAGE (SND d) (IMAGE f Q) /\
             integral (IMAGE (SND d) (IMAGE f Q))
                      (mfd_chart_integrand atlas' g' h d) = b) /\
            ((\y. lift(norm(mfd_chart_integrand atlas g (h o f) c y)))
             absolutely_integrable_on IMAGE (SND c) Q /\
             integral (IMAGE (SND c) Q)
               (\y. lift(norm(mfd_chart_integrand atlas g (h o f) c y))) = b <=>
             (\y. lift(norm(mfd_chart_integrand atlas' g' h d y)))
             absolutely_integrable_on IMAGE (SND d) (IMAGE f Q) /\
             integral (IMAGE (SND d) (IMAGE f Q))
               (\y. lift(norm(mfd_chart_integrand atlas' g' h d y))) = b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. x IN Q
        ==> chart_inv (c:(A->bool)#(A->real^N)) (SND c x) = x /\
            chart_inv (d:(B->bool)#(B->real^N)) (SND d ((f:A->B) x)) = f x /\
            mfd_density atlas c (g:A->real^N^N) (SND c x) =
            abs(det(matrix(frechet_derivative (SND d o f o chart_inv c)
                                              (at (SND c x))))) *
            mfd_density atlas' d (g':B->real^N^N) (SND d (f x))`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:A) IN FST(c:(A->bool)#(A->real^N)) /\
                  (f:A->B) x IN FST(d:(B->bool)#(B->real^N))`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MFDM_CHART]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MFDM_CHART]; ALL_TAC] THEN
    MATCH_MP_TAC GRGV_ISOMETRY_DENSITY THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `top':B topology`; `f':B->A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN Q
        ==> mfd_chart_integrand atlas (g:A->real^N^N) ((h:B->real) o (f:A->B))
                                (c:(A->bool)#(A->real^N)) (SND c x) =
            abs(det(matrix(frechet_derivative
                     (SND(d:(B->bool)#(B->real^N)) o f o chart_inv c)
                     (at (SND c x))))) %
            mfd_chart_integrand atlas' (g':B->real^N^N) h d (SND d (f x))`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(x:A) IN Q`)) THEN
    ASM_REWRITE_TAC[mfd_chart_integrand; o_THM] THEN
    REWRITE_TAC[GSYM LIFT_CMUL] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN Q
        ==> (\y. lift(norm(mfd_chart_integrand atlas (g:A->real^N^N)
                             ((h:B->real) o (f:A->B))
                             (c:(A->bool)#(A->real^N)) y))) (SND c x) =
            abs(det(matrix(frechet_derivative
                     (SND(d:(B->bool)#(B->real^N)) o f o chart_inv c)
                     (at (SND c x))))) %
            (\y. lift(norm(mfd_chart_integrand atlas' (g':B->real^N^N) h d y)))
            (SND d (f x))`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(x:A) IN Q`)) THEN
    ASM_REWRITE_TAC[mfd_chart_integrand; o_THM] THEN
    REWRITE_TAC[GSYM LIFT_CMUL; NORM_LIFT] THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_ABS] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
    `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `g':B->real^N^N`;
    `f:A->B`; `f':B->A`; `c:(A->bool)#(A->real^N)`; `d:(B->bool)#(B->real^N)`;
    `Q:A->bool`;
    `\y. lift(norm(mfd_chart_integrand atlas' (g':B->real^N^N) (h:B->real)
                     (d:(B->bool)#(B->real^N)) y))`;
    `\y. lift(norm(mfd_chart_integrand atlas (g:A->real^N^N)
                     ((h:B->real) o (f:A->B)) (c:(A->bool)#(A->real^N)) y))`;
    `b:real^1`] GRGV_ISOMETRY_CHANGE_GEN) THEN
  MP_TAC(ISPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
    `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `g':B->real^N^N`;
    `f:A->B`; `f':B->A`; `c:(A->bool)#(A->real^N)`; `d:(B->bool)#(B->real^N)`;
    `Q:A->bool`;
    `mfd_chart_integrand atlas' (g':B->real^N^N) (h:B->real)
                         (d:(B->bool)#(B->real^N))`;
    `mfd_chart_integrand atlas (g:A->real^N^N) ((h:B->real) o (f:A->B))
                         (c:(A->bool)#(A->real^N))`;
    `b:real^1`] GRGV_ISOMETRY_CHANGE_GEN) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Chart partitions compatible with a continuous map: each piece inside the  *)
(* domain of its chart is mapped into the domain of a chart of the target.   *)
(* The chart domains are covered by countably many preimages of target       *)
(* charts (LINDELOF in real^N), which are then made disjoint and enumerated  *)
(* with NUMPAIR.                                                             *)
(* ------------------------------------------------------------------------- *)

let GRGV_CHART_COVER_SEQ = prove
 (`!top atlas top' atlas' (f:A->B) c.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^M))->bool) /\
        continuous_map (top,top') f /\ c IN atlas /\ ~(FST c = {})
        ==> ?d:num->(B->bool)#(B->real^M).
                (!k. d k IN atlas') /\
                (!x. x IN FST c ==> ?k. f x IN FST(d k))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `FST(c:(A->bool)#(A->real^N)) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN FST(c:(A->bool)#(A->real^N))
        ==> ?e. e IN atlas' /\ (f:A->B) x IN FST(e:(B->bool)#(B->real^M))`
  (LABEL_TAC "COV") THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(f:A->B) x IN topspace top'` MP_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC
     `smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^M))->bool)` THEN
    REWRITE_TAC[smooth_manifold_atlas; EXISTS_PAIR_THM; FST] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC
   `{IMAGE (SND(c:(A->bool)#(A->real^N)))
           {x | x IN FST c /\ (f:A->B) x IN FST(e:(B->bool)#(B->real^M))} |
     e IN atlas'}` LINDELOF) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `e:(B->bool)#(B->real^M)` THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^M))->bool`;
                   `c:(A->bool)#(A->real^N)`; `e:(B->bool)#(B->real^M)`;
                   `topspace top:A->bool`; `f:A->B`] MFDM_CHART_DOMAIN_OPEN) THEN
    ASM_REWRITE_TAC[OPEN_IN_TOPSPACE; SUBTOPOLOGY_TOPSPACE] THEN
    MATCH_MP_TAC(TAUT `(q <=> r) ==> p /\ q ==> r`) THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!x. x IN FST(c:(A->bool)#(A->real^N))
        ==> SND c x IN UNIONS(u:(real^N->bool)->bool)`
  (LABEL_TAC "UN") THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "COV" (X_CHOOSE_TAC `e:(B->bool)#(B->real^M)` o
      C MATCH_MP (ASSUME `(x:A) IN FST(c:(A->bool)#(A->real^N))`)) THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
    EXISTS_TAC `e:(B->bool)#(B->real^M)` THEN
    ASM_REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(u:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [UNDISCH_TAC `~(FST(c:(A->bool)#(A->real^N)) = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `x0:A`) THEN
    USE_THEN "UN" (MP_TAC o C MATCH_MP
      (ASSUME `(x0:A) IN FST(c:(A->bool)#(A->real^N))`)) THEN
    REWRITE_TAC[IN_UNIONS] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `u:(real^N->bool)->bool` COUNTABLE_AS_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num->real^N->bool` SUBST_ALL_TAC) THEN
  SUBGOAL_THEN
   `!k. ?e. e IN atlas' /\
            (s:num->real^N->bool) k =
            IMAGE (SND(c:(A->bool)#(A->real^N)))
                  {x | x IN FST c /\ (f:A->B) x IN FST(e:(B->bool)#(B->real^M))}`
  MP_TAC THENL
   [X_GEN_TAC `k:num` THEN
    SUBGOAL_THEN `(s:num->real^N->bool) k IN IMAGE s (:num)` MP_TAC THENL
     [REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC
     `IMAGE (s:num->real^N->bool) (:num) SUBSET
      {IMAGE (SND(c:(A->bool)#(A->real^N)))
             {x | x IN FST c /\ (f:A->B) x IN FST(e:(B->bool)#(B->real^M))} |
       e IN atlas'}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num->(B->bool)#(B->real^M)` (LABEL_TAC "D")) THEN
  EXISTS_TAC `d:num->(B->bool)#(B->real^M)` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `SND(c:(A->bool)#(A->real^N)) x IN UNIONS (IMAGE (s:num->real^N->bool) (:num))`
  MP_TAC THENL [USE_THEN "UN" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN EXISTS_TAC `k:num` THEN
  REMOVE_THEN "D" (MP_TAC o CONJUNCT2 o SPEC `k:num`) THEN
  DISCH_THEN(fun th ->
    UNDISCH_TAC `SND(c:(A->bool)#(A->real^N)) x IN s(k:num)` THEN
    REWRITE_TAC[th]) THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `x':A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `x:A = x'` (fun th -> ASM_REWRITE_TAC[th]) THEN
  ASM_MESON_TAC[]);;

let GRGV_CUT_MEASURABLE = prove
 (`!top atlas top' atlas' (f:A->B) c E (D:num->(B->bool)#(B->real^M)) k.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^M))->bool) /\
        continuous_map (top,top') f /\ c IN atlas /\ (!j. D j IN atlas') /\
        E SUBSET FST c /\ lebesgue_measurable (IMAGE (SND c) E)
        ==> lebesgue_measurable
             (IMAGE (SND c) {x | x IN E /\ f x IN FST(D k) /\
                                 !j. j < k ==> ~(f x IN FST(D j))})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `FST(c:(A->bool)#(A->real^N)) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. x IN FST(c:(A->bool)#(A->real^N)) /\ y IN FST c /\ SND c x = SND c y
          ==> x = y`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. open (IMAGE (SND(c:(A->bool)#(A->real^N)))
                    {x | x IN FST c /\
                         (f:A->B) x IN FST((D:num->(B->bool)#(B->real^M)) j)})`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^M))->bool`;
                   `c:(A->bool)#(A->real^N)`;
                   `(D:num->(B->bool)#(B->real^M)) j`;
                   `topspace top:A->bool`; `f:A->B`] MFDM_CHART_DOMAIN_OPEN) THEN
    ASM_REWRITE_TAC[OPEN_IN_TOPSPACE; SUBTOPOLOGY_TOPSPACE] THEN
    MATCH_MP_TAC(TAUT `(q <=> r) ==> p /\ q ==> r`) THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (SND(c:(A->bool)#(A->real^N)))
      {x | x IN E /\ (f:A->B) x IN FST((D:num->(B->bool)#(B->real^M)) k) /\
           !j. j < k ==> ~(f x IN FST(D j))} =
    (IMAGE (SND c) E INTER IMAGE (SND c) {x | x IN FST c /\ f x IN FST(D k)}) DIFF
    UNIONS {IMAGE (SND c) {x | x IN FST c /\ f x IN FST(D j)} | j < k}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^N` THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER; IN_DIFF; IN_ELIM_THM; UNIONS_GSPEC] THEN
    EQ_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC)
                      (X_CHOOSE_THEN `x':A` STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
    EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `x':A = x` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC LEBESGUE_MEASURABLE_DIFF THEN CONJ_TAC THENL
   [MATCH_MP_TAC LEBESGUE_MEASURABLE_INTER THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN];
    MATCH_MP_TAC LEBESGUE_MEASURABLE_OPEN THEN MATCH_MP_TAC OPEN_UNIONS THEN
    ASM_REWRITE_TAC[FORALL_IN_GSPEC]]);;

let GRGV_NUMPAIR_PIECES = prove
 (`!(P:num->num->A->bool).
        (!n k n' k'. ~(n = n' /\ k = k') ==> DISJOINT (P n k) (P n' k'))
        ==> (!m m'. ~(m = m')
                    ==> DISJOINT (if NUMPAIR (NUMFST m) (NUMSND m) = m
                                  then P (NUMFST m) (NUMSND m) else {})
                                 (if NUMPAIR (NUMFST m') (NUMSND m') = m'
                                  then P (NUMFST m') (NUMSND m') else {})) /\
            UNIONS {(if NUMPAIR (NUMFST m) (NUMSND m) = m
                     then P (NUMFST m) (NUMSND m) else {}) | m IN (:num)} =
            UNIONS {P n k | n IN (:num) /\ k IN (:num)}`,
  GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    REPEAT COND_CASES_TAC THEN REWRITE_TAC[DISJOINT_EMPTY] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:A` THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `t:A->bool`
       (CONJUNCTS_THEN2 (X_CHOOSE_TAC `m:num`) MP_TAC)) THEN
      ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[NOT_IN_EMPTY] THEN
      DISCH_TAC THEN EXISTS_TAC `(P:num->num->A->bool) (NUMFST m) (NUMSND m)` THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `t:A->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `n:num` (X_CHOOSE_TAC `k:num`)) MP_TAC)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      EXISTS_TAC `(P:num->num->A->bool) n k` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `NUMPAIR n k` THEN REWRITE_TAC[NUMPAIR_DEST]]]);;

let GRGV_COMPATIBLE_PARTITION = prove
 (`!top atlas top' atlas' (f:A->B) S c E.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^M))->bool) /\
        continuous_map (top,top') f /\
        mfd_chart_partition atlas S c E
        ==> ?c' Q (d:num->(B->bool)#(B->real^M)).
                mfd_chart_partition atlas S c' Q /\
                (!m. Q m = {} \/ d m IN atlas') /\
                (!m x. x IN Q m ==> f x IN FST(d m))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [mfd_chart_partition]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "PE")
    (CONJUNCTS_THEN2 (LABEL_TAC "PD") (LABEL_TAC "PU"))) THEN
  SUBGOAL_THEN
   `?D:num->num->(B->bool)#(B->real^M).
      !n. ~((E:num->A->bool) n = {})
          ==> (!k. D n k IN atlas') /\
              (!x. x IN FST((c:num->(A->bool)#(A->real^N)) n)
                   ==> ?k. (f:A->B) x IN FST(D n k))`
  (X_CHOOSE_THEN `D:num->num->(B->bool)#(B->real^M)` (LABEL_TAC "DD")) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `n:num` THEN
    ASM_CASES_TAC `(E:num->A->bool) n = {}` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(c:num->(A->bool)#(A->real^N)) n IN atlas /\
                  (E:num->A->bool) n SUBSET FST(c n)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC GRGV_CHART_COVER_SEQ THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `top':B topology`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(E:num->A->bool) n SUBSET FST((c:num->(A->bool)#(A->real^N)) n)` THEN
    UNDISCH_TAC `~((E:num->A->bool) n = {})` THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `P = \n k. {x | x IN (E:num->A->bool) n /\
                   (f:A->B) x IN FST((D:num->num->(B->bool)#(B->real^M)) n k) /\
                   !j. j < k ==> ~(f x IN FST(D n j))}` THEN
  SUBGOAL_THEN
   `!n k x. x IN (P:num->num->A->bool) n k <=>
            x IN (E:num->A->bool) n /\
            (f:A->B) x IN FST((D:num->num->(B->bool)#(B->real^M)) n k) /\
            !j. j < k ==> ~(f x IN FST(D n j))`
  (LABEL_TAC "PIN") THENL
   [EXPAND_TAC "P" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `!n k. (P:num->num->A->bool) n k SUBSET (E:num->A->bool) n`
  (LABEL_TAC "PSUB") THENL
   [ASM_REWRITE_TAC[SUBSET] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n k. ~((P:num->num->A->bool) n k = {})
          ==> (c:num->(A->bool)#(A->real^N)) n IN atlas /\
              (D:num->num->(B->bool)#(B->real^M)) n k IN atlas'`
  (LABEL_TAC "PNE") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((E:num->A->bool) n = {})` ASSUME_TAC THENL
     [USE_THEN "PSUB" (MP_TAC o SPECL [`n:num`; `k:num`]) THEN
      UNDISCH_TAC `~((P:num->num->A->bool) n k = {})` THEN SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REMOVE_THEN "PE" (MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      REMOVE_THEN "DD" (MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n k. lebesgue_measurable
            (IMAGE (SND((c:num->(A->bool)#(A->real^N)) n))
                   ((P:num->num->A->bool) n k))`
  (LABEL_TAC "PMEAS") THENL
   [REPEAT GEN_TAC THEN
    ASM_CASES_TAC `(E:num->A->bool) n = {}` THENL
     [SUBGOAL_THEN `(P:num->num->A->bool) n k = {}` SUBST1_TAC THENL
       [REMOVE_THEN "PSUB" (MP_TAC o SPECL [`n:num`; `k:num`]) THEN
        ASM_REWRITE_TAC[SUBSET_EMPTY];
        REWRITE_TAC[IMAGE_CLAUSES; LEBESGUE_MEASURABLE_EMPTY]];
      ALL_TAC] THEN
    EXPAND_TAC "P" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC GRGV_CUT_MEASURABLE THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
      `top':B topology`; `atlas':((B->bool)#(B->real^M))->bool`] THEN
    REMOVE_THEN "PE" (MP_TAC o SPEC `n:num`) THEN
    REMOVE_THEN "DD" (MP_TAC o SPEC `n:num`) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n k n' k'. ~(n = n' /\ k = k')
                ==> DISJOINT ((P:num->num->A->bool) n k) (P n' k')`
  (LABEL_TAC "PDIS") THENL
   [REPEAT GEN_TAC THEN ASM_CASES_TAC `n:num = n'` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[] THEN DISCH_TAC THEN
      ASM_REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
      X_GEN_TAC `x:A` THEN
      FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP
        (ARITH_RULE `~(k:num = k') ==> k < k' \/ k' < k`)) THEN
      ASM_MESON_TAC[];
      DISCH_TAC THEN
      USE_THEN "PSUB" (MP_TAC o SPECL [`n:num`; `k:num`]) THEN
      USE_THEN "PSUB" (MP_TAC o SPECL [`n':num`; `k':num`]) THEN
      USE_THEN "PD" (MP_TAC o C MATCH_MP (ASSUME `~(n:num = n')`) o
                     SPECL [`n:num`; `n':num`]) THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS {(P:num->num->A->bool) n k | n IN (:num) /\ k IN (:num)} = S`
  (LABEL_TAC "PUN") THENL
   [USE_THEN "PU" (fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:A` THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `t:A->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `n:num` (X_CHOOSE_TAC `k:num`)) MP_TAC)) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      EXISTS_TAC `(E:num->A->bool) n` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `n:num` THEN REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `t:A->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_TAC `n:num`) MP_TAC)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `~((E:num->A->bool) n = {})` ASSUME_TAC THENL
       [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `x:A` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `?k. (f:A->B) x IN FST((D:num->num->(B->bool)#(B->real^M)) n k)`
      MP_TAC THENL
       [REMOVE_THEN "DD" (MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
        USE_THEN "PE" (MP_TAC o CONJUNCT1 o CONJUNCT2 o SPEC `n:num`) THEN
        UNDISCH_TAC `(x:A) IN (E:num->A->bool) n` THEN SET_TAC[];
        ALL_TAC] THEN
      GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
      DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(P:num->num->A->bool) n k` THEN
      CONJ_TAC THENL
       [MAP_EVERY EXISTS_TAC [`n:num`; `k:num`] THEN REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n k. ((P:num->num->A->bool) n k = {} \/
           (c:num->(A->bool)#(A->real^N)) n IN atlas) /\
          P n k SUBSET FST(c n) /\
          lebesgue_measurable (IMAGE (SND(c n)) (P n k)) /\
          (P n k = {} \/ (D:num->num->(B->bool)#(B->real^M)) n k IN atlas') /\
          (!x. x IN P n k ==> (f:A->B) x IN FST(D n k))`
  (LABEL_TAC "PALL") THENL
   [REPEAT GEN_TAC THEN
    USE_THEN "PMEAS" (fun th -> REWRITE_TAC[th]) THEN
    CONJ_TAC THENL
     [USE_THEN "PNE" (MP_TAC o SPECL [`n:num`; `k:num`]) THEN MESON_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(E:num->A->bool) n` THEN
      USE_THEN "PSUB" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "PE" (fun th -> REWRITE_TAC[th]);
      ALL_TAC] THEN
    CONJ_TAC THENL
     [USE_THEN "PNE" (MP_TAC o SPECL [`n:num`; `k:num`]) THEN MESON_TAC[];
      ALL_TAC] THEN
    USE_THEN "PIN" (fun th -> REWRITE_TAC[th]) THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `P:num->num->A->bool` GRGV_NUMPAIR_PIECES) THEN
  ANTS_TAC THENL [USE_THEN "PDIS" ACCEPT_TAC; ALL_TAC] THEN
  USE_THEN "PUN" SUBST1_TAC THEN STRIP_TAC THEN
  EXISTS_TAC `\m. (c:num->(A->bool)#(A->real^N)) (NUMFST m)` THEN
  EXISTS_TAC `\m. if NUMPAIR (NUMFST m) (NUMSND m) = m
                  then (P:num->num->A->bool) (NUMFST m) (NUMSND m) else {}` THEN
  EXISTS_TAC `\m. (D:num->num->(B->bool)#(B->real^M)) (NUMFST m) (NUMSND m)` THEN
  REWRITE_TAC[mfd_chart_partition] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `m:num` THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[EMPTY_SUBSET; IMAGE_CLAUSES; LEBESGUE_MEASURABLE_EMPTY;
                  NOT_IN_EMPTY]);;

(* The image of a compatible partition under an isometry. *)

let GRGV_ISOMETRY_IMAGE_PARTITION = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) f f' S c Q d.
        smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
        mfd_isometry (top,atlas) g (top',atlas') g' f f' /\
        mfd_chart_partition atlas S c Q /\
        (!m. Q m = {} \/ d m IN atlas') /\
        (!m x. x IN Q m ==> f x IN FST(d m))
        ==> mfd_chart_partition atlas' (IMAGE f S) d (\m. IMAGE f (Q m))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GRGD_ISOMETRY_FACTS) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [mfd_chart_partition]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "PE")
    (CONJUNCTS_THEN2 (LABEL_TAC "PD") (LABEL_TAC "PU"))) THEN
  SUBGOAL_THEN `!m. (Q:num->A->bool) m SUBSET topspace top` (LABEL_TAC "QT") THENL
   [X_GEN_TAC `m:num` THEN
    USE_THEN "PE" (STRIP_ASSUME_TAC o SPEC `m:num`) THENL
     [ASM_REWRITE_TAC[EMPTY_SUBSET]; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `FST((c:num->(A->bool)#(A->real^N)) m)` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(c:num->(A->bool)#(A->real^N)) m`] MFDM_CHART) THEN
    ASM_SIMP_TAC[OPEN_IN_SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_chart_partition] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `m:num` THEN
    ASM_CASES_TAC `(Q:num->A->bool) m = {}` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; EMPTY_SUBSET; LEBESGUE_MEASURABLE_EMPTY] THEN
    SUBGOAL_THEN
     `(d:num->(B->bool)#(B->real^N)) m IN atlas' /\
      (c:num->(A->bool)#(A->real^N)) m IN atlas /\
      (Q:num->A->bool) m SUBSET FST(c m) /\
      lebesgue_measurable (IMAGE (SND(c m)) (Q m))`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[];
      MP_TAC(ISPECL
       [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
        `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
        `g':B->real^N^N`; `f:A->B`; `f':B->A`;
        `(c:num->(A->bool)#(A->real^N)) m`; `(d:num->(B->bool)#(B->real^N)) m`;
        `(Q:num->A->bool) m`; `\x:B. &0`; `vec 0:real^1`]
       GRGV_ISOMETRY_CHANGE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; SIMP_TAC[]]];
    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN DISCH_TAC THEN
    MATCH_MP_TAC(SET_RULE
     `!U. (!x y. x IN U /\ y IN U /\ (f:A->B) x = f y ==> x = y) /\
          A SUBSET U /\ B SUBSET U /\ DISJOINT A B
          ==> DISJOINT (IMAGE f A) (IMAGE f B)`) THEN
    EXISTS_TAC `topspace top:A->bool` THEN
    USE_THEN "QT" (fun th -> REWRITE_TAC[th]) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    USE_THEN "PD" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "PU" (fun th -> REWRITE_TAC[SYM th]) THEN
    REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[]]);;

(* One direction of the invariance; the other follows with the inverse. *)

let GRGV_ISOMETRY_HAS_INTEGRAL_IMP = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) f f' h S v.
        smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
        riemannian_metric atlas g /\
        mfd_isometry (top,atlas) g (top',atlas') g' f f' /\
        mfd_has_integral (top,atlas) g (h o f) S v
        ==> mfd_has_integral (top',atlas') g' h (IMAGE f S) v`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GRGD_ISOMETRY_FACTS) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [mfd_has_integral]) THEN
  DISCH_THEN(X_CHOOSE_THEN `c0:num->(A->bool)#(A->real^N)`
   (X_CHOOSE_THEN `E0:num->A->bool` (ASSUME_TAC o CONJUNCT1))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `f:A->B`; `S:A->bool`; `c0:num->(A->bool)#(A->real^N)`;
                 `E0:num->A->bool`] GRGV_COMPATIBLE_PARTITION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBTOPOLOGY_TOPSPACE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num->(A->bool)#(A->real^N)`
   (X_CHOOSE_THEN `Q:num->A->bool`
     (X_CHOOSE_THEN `d:num->(B->bool)#(B->real^N)` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(h:B->real) o (f:A->B)`; `S:A->bool`; `v:real`;
                 `c:num->(A->bool)#(A->real^N)`; `Q:num->A->bool`]
                MFD_HAS_INTEGRAL_PARTITION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "AI")
    (CONJUNCTS_THEN2 (LABEL_TAC "SM") (LABEL_TAC "SV"))) THEN
  SUBGOAL_THEN
   `!m. mfd_chart_integrand atlas' (g':B->real^N^N) h
          ((d:num->(B->bool)#(B->real^N)) m) absolutely_integrable_on
        IMAGE (SND(d m)) (IMAGE (f:A->B) ((Q:num->A->bool) m)) /\
        integral (IMAGE (SND(d m)) (IMAGE f (Q m)))
                 (mfd_chart_integrand atlas' g' h (d m)) =
        integral (IMAGE (SND((c:num->(A->bool)#(A->real^N)) m)) (Q m))
                 (mfd_chart_integrand atlas (g:A->real^N^N) (h o f) (c m)) /\
        (\y. lift(norm(mfd_chart_integrand atlas' g' h (d m) y)))
        absolutely_integrable_on IMAGE (SND(d m)) (IMAGE f (Q m)) /\
        integral (IMAGE (SND(d m)) (IMAGE f (Q m)))
                 (\y. lift(norm(mfd_chart_integrand atlas' g' h (d m) y))) =
        integral (IMAGE (SND(c m)) (Q m))
                 (\y. lift(norm(mfd_chart_integrand atlas g (h o f) (c m) y)))`
  (LABEL_TAC "TERM") THENL
   [X_GEN_TAC `m:num` THEN
    ASM_CASES_TAC `(Q:num->A->bool) m = {}` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; INTEGRAL_EMPTY; ABSOLUTELY_INTEGRABLE_ON_EMPTY] THEN
    SUBGOAL_THEN
     `(d:num->(B->bool)#(B->real^N)) m IN atlas' /\
      (c:num->(A->bool)#(A->real^N)) m IN atlas /\
      (Q:num->A->bool) m SUBSET FST(c m) /\
      lebesgue_measurable (IMAGE (SND(c m)) (Q m))`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `mfd_chart_partition (atlas:((A->bool)#(A->real^N))->bool) S
                     (c:num->(A->bool)#(A->real^N)) Q` THEN
      REWRITE_TAC[mfd_chart_partition] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(Q:num->A->bool) m SUBSET
      {x | x IN FST((c:num->(A->bool)#(A->real^N)) m) /\
           (f:A->B) x IN FST((d:num->(B->bool)#(B->real^N)) m)}`
    ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
      `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
      `g':B->real^N^N`; `f:A->B`; `f':B->A`;
      `(c:num->(A->bool)#(A->real^N)) m`; `(d:num->(B->bool)#(B->real^N)) m`;
      `(Q:num->A->bool) m`; `h:B->real`;
      `integral (IMAGE (SND((c:num->(A->bool)#(A->real^N)) m)) ((Q:num->A->bool) m))
         (\y. lift(norm(mfd_chart_integrand atlas (g:A->real^N^N)
                          ((h:B->real) o (f:A->B)) (c m) y)))`]
     GRGV_ISOMETRY_CHANGE) THEN
    MP_TAC(ISPECL
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
      `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
      `g':B->real^N^N`; `f:A->B`; `f':B->A`;
      `(c:num->(A->bool)#(A->real^N)) m`; `(d:num->(B->bool)#(B->real^N)) m`;
      `(Q:num->A->bool) m`; `h:B->real`;
      `integral (IMAGE (SND((c:num->(A->bool)#(A->real^N)) m)) ((Q:num->A->bool) m))
         (mfd_chart_integrand atlas (g:A->real^N^N) ((h:B->real) o (f:A->B)) (c m))`]
     GRGV_ISOMETRY_CHANGE) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "AI" (ASSUME_TAC o SPEC `m:num`) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_NORM) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_has_integral] THEN
  MAP_EVERY EXISTS_TAC [`d:num->(B->bool)#(B->real^N)`;
                        `\m. IMAGE (f:A->B) ((Q:num->A->bool) m)`] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC GRGV_ISOMETRY_IMAGE_PARTITION THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
      `top':B topology`; `g':B->real^N^N`; `f':B->A`;
      `c:num->(A->bool)#(A->real^N)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "TERM" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "SM" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "SV" (fun th -> REWRITE_TAC[th]));;

let MFD_HAS_INTEGRAL_ISOMETRY = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) f f' h S v.
        smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
        riemannian_metric atlas g /\ riemannian_metric atlas' g' /\
        mfd_isometry (top,atlas) g (top',atlas') g' f f' /\
        S SUBSET topspace top
        ==> (mfd_has_integral (top',atlas') g' h (IMAGE f S) v <=>
             mfd_has_integral (top,atlas) g (h o f) S v)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GRGD_ISOMETRY_FACTS) THEN
  EQ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `IMAGE (f':B->A) (IMAGE (f:A->B) S) = S` (SUBST1_TAC o SYM) THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC GRGV_ISOMETRY_HAS_INTEGRAL_IMP THEN
    MAP_EVERY EXISTS_TAC
     [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
      `g':B->real^N^N`; `f:A->B`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_ISOMETRY_INVERSE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                   `g':B->real^N^N`; `h:B->real`;
                   `((h:B->real) o (f:A->B)) o (f':B->A)`;
                   `IMAGE (f:A->B) S`; `v:real`] MFD_HAS_INTEGRAL_EQ) THEN
    ANTS_TAC THENL [ALL_TAC; DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]] THEN
    ASM_REWRITE_TAC[FORALL_IN_IMAGE; o_THM] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    DISCH_TAC THEN MATCH_MP_TAC GRGV_ISOMETRY_HAS_INTEGRAL_IMP THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
      `g:A->real^N^N`; `f':B->A`] THEN
    ASM_REWRITE_TAC[]]);;

let MFD_HAS_VOLUME_ISOMETRY = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) f f' S v.
        smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
        riemannian_metric atlas g /\ riemannian_metric atlas' g' /\
        mfd_isometry (top,atlas) g (top',atlas') g' f f' /\
        S SUBSET topspace top
        ==> (mfd_has_volume (top',atlas') g' (IMAGE f S) v <=>
             mfd_has_volume (top,atlas) g S v)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_has_volume] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^N))->bool`; `g':B->real^N^N`;
                 `f:A->B`; `f':B->A`; `\x:B. &1`; `S:A->bool`; `v:real`]
                MFD_HAS_INTEGRAL_ISOMETRY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM]);;

(* ------------------------------------------------------------------------- *)
(* Change of the metric on a fixed atlas: the density ratio                  *)
(* sqrt(det(g' x)) / sqrt(det(g x)) does not depend on the chart, since      *)
(* metric_local atlas c g y is g x conjugated by a Jacobian J that does not *)
(* depend on g                                                              *)
(* (used by the pc_rfa units).                                               *)
(* ------------------------------------------------------------------------- *)

let GRGV_SQRT_DET_POS = prove
 (`!top atlas (g:A->real^N^N) x.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        x IN topspace top
        ==> &0 < sqrt(det(g x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM mfd_density] THEN
  MATCH_MP_TAC GRGV_DENSITY_POS THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `x:A`] CHART_AT) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE]);;

(* Transfer of the integral when the chart integrands agree on S. *)

let GRGV_HAS_INTEGRAL_TRANSFER = prove
 (`!top atlas (g:A->real^N^N) g' f f' S v.
        (!c y. c IN atlas /\ y IN IMAGE (SND c) (FST c INTER S)
               ==> mfd_chart_integrand atlas g' f' c y =
                   mfd_chart_integrand atlas g f c y)
        ==> (mfd_has_integral (top,atlas) g' f' S v <=>
             mfd_has_integral (top,atlas) g f S v)`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "H") THEN
  REWRITE_TAC[mfd_has_integral] THEN
  AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
  ASM_CASES_TAC
   `mfd_chart_partition (atlas:((A->bool)#(A->real^N))->bool) S
                        (c:num->(A->bool)#(A->real^N)) (E:num->A->bool)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!n y. y IN IMAGE (SND((c:num->(A->bool)#(A->real^N)) n)) ((E:num->A->bool) n)
          ==> mfd_chart_integrand atlas (g':A->real^N^N) f' (c n) y =
              mfd_chart_integrand atlas (g:A->real^N^N) f (c n) y`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN USE_THEN "H" MATCH_MP_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [mfd_chart_partition]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `n:num`)
                               (MP_TAC o CONJUNCT2)) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN STRIP_TAC THENL
     [UNDISCH_TAC
       `(y:real^N) IN IMAGE (SND((c:num->(A->bool)#(A->real^N)) n))
                            ((E:num->A->bool) n)` THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; NOT_IN_EMPTY];
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC
       `(y:real^N) IN IMAGE (SND((c:num->(A->bool)#(A->real^N)) n))
                            ((E:num->A->bool) n)` THEN
      UNDISCH_TAC `(E:num->A->bool) n SUBSET FST((c:num->(A->bool)#(A->real^N)) n)` THEN
      REWRITE_TAC[IN_IMAGE; IN_INTER; IN_UNIONS; IN_ELIM_THM; SUBSET; IN_UNIV] THEN
      MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (mfd_chart_integrand atlas (g':A->real^N^N) f'
           ((c:num->(A->bool)#(A->real^N)) n) absolutely_integrable_on
         IMAGE (SND(c n)) ((E:num->A->bool) n) <=>
         mfd_chart_integrand atlas (g:A->real^N^N) f (c n) absolutely_integrable_on
         IMAGE (SND(c n)) (E n)) /\
        integral (IMAGE (SND(c n)) (E n)) (mfd_chart_integrand atlas g' f' (c n)) =
        integral (IMAGE (SND(c n)) (E n)) (mfd_chart_integrand atlas g f (c n)) /\
        integral (IMAGE (SND(c n)) (E n))
          (\y. lift(norm(mfd_chart_integrand atlas g' f' (c n) y))) =
        integral (IMAGE (SND(c n)) (E n))
          (\y. lift(norm(mfd_chart_integrand atlas g f (c n) y)))`
  (fun th -> REWRITE_TAC[th]) THEN
  GEN_TAC THEN
  MP_TAC(ISPECL
   [`mfd_chart_integrand atlas (g':A->real^N^N) f'
                         ((c:num->(A->bool)#(A->real^N)) n)`;
    `mfd_chart_integrand atlas (g:A->real^N^N) f
                         ((c:num->(A->bool)#(A->real^N)) n)`;
    `IMAGE (SND((c:num->(A->bool)#(A->real^N)) n)) ((E:num->A->bool) n)`]
   GRGV_AI_EQ) THEN
  MP_TAC(ISPECL
   [`\y. lift(norm(mfd_chart_integrand atlas (g':A->real^N^N) f'
                     ((c:num->(A->bool)#(A->real^N)) n) y))`;
    `\y. lift(norm(mfd_chart_integrand atlas (g:A->real^N^N) f
                     ((c:num->(A->bool)#(A->real^N)) n) y))`;
    `IMAGE (SND((c:num->(A->bool)#(A->real^N)) n)) ((E:num->A->bool) n)`]
   GRGV_AI_EQ) THEN
  ASM_SIMP_TAC[]);;

let MFD_HAS_INTEGRAL_CHANGE_METRIC = prove
 (`!top atlas (g:A->real^N^N) g' f S v.
     smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ riemannian_metric atlas g' /\
     S SUBSET topspace top
     ==> (mfd_has_integral (top,atlas) g' f S v <=>
          mfd_has_integral (top,atlas) g
            (\x. f x * sqrt(det(g' x)) / sqrt(det(g x))) S v)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC GRGV_HAS_INTEGRAL_TRANSFER THEN
  REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
  MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^N)`; `y:real^N`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) (SND c x) = x` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFDM_CHART]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(det((g:A->real^N^N) x))` MP_TAC THENL
   [MATCH_MP_TAC GRGV_SQRT_DET_POS THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[mfd_chart_integrand; mfd_density; metric_local;
                  GRGV_DET_PULLBACK_SQRT] THEN
  DISCH_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `&0 < sqrt(det((g:A->real^N^N) x))` THEN CONV_TAC REAL_FIELD);;

let MFD_HAS_VOLUME_COMPARE = prove
 (`!top atlas (g:A->real^N^N) g' S v v' c.
     smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ riemannian_metric atlas g' /\
     mfd_has_volume (top,atlas) g S v /\ mfd_has_volume (top,atlas) g' S v' /\
     &0 <= c /\
     (!x. x IN S ==> sqrt(det(g' x)) <= c * sqrt(det(g x)))
     ==> v' <= c * v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(S:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `\x:A. &1`; `S:A->bool`; `v:real`]
                  MFD_HAS_INTEGRAL_IMP_MEASURABLE) THEN
    ASM_REWRITE_TAC[GSYM mfd_has_volume] THEN SIMP_TAC[mfd_lebesgue_measurable];
    ALL_TAC] THEN
  MATCH_MP_TAC MFD_HAS_INTEGRAL_LE THEN
  MAP_EVERY EXISTS_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
    `\x:A. &1 * sqrt(det((g':A->real^N^N) x)) / sqrt(det((g:A->real^N^N) x))`;
    `\x:A. (c:real)`; `S:A->bool`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `g':A->real^N^N`; `\x:A. &1`; `S:A->bool`;
                   `v':real`] MFD_HAS_INTEGRAL_CHANGE_METRIC) THEN
    ASM_REWRITE_TAC[GSYM mfd_has_volume];
    MATCH_MP_TAC MFD_HAS_INTEGRAL_CONST THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN REWRITE_TAC[REAL_MUL_LID] THEN
    SUBGOAL_THEN `&0 < sqrt(det((g:A->real^N^N) x))` ASSUME_TAC THENL
     [MATCH_MP_TAC GRGV_SQRT_DET_POS THEN
      MAP_EVERY EXISTS_TAC
       [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ]]);;

(* ------------------------------------------------------------------------- *)
(* Compact sets have finite volume, nonempty open sets positive volume, and  *)
(* metric balls of complete manifolds finite positive volume.  The density   *)
(* is continuous on chart images, so it is integrable on closed intervals    *)
(* inside them (ABSOLUTELY_INTEGRABLE_CONTINUOUS); compactness then gives    *)
(* finitely many such pieces.                                                *)
(* ------------------------------------------------------------------------- *)

let GRGV_DENSITY_CONTINUOUS = prove
 (`!atlas (g:A->real^N^N) (c:(A->bool)#(A->real^N)).
        riemannian_metric atlas g /\ c IN atlas
        ==> (\y. lift(mfd_density atlas c g y)) continuous_on
            IMAGE (SND c) (FST c)`,
  REWRITE_TAC[riemannian_metric; metric_field; smooth_map_on] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `0` o CONJUNCT1 o CONJUNCT2) THEN
  REWRITE_TAC[continuously_differentiable; o_DEF] THEN DISCH_TAC THEN
  REWRITE_TAC[mfd_density] THEN
  MATCH_MP_TAC CONTINUOUS_ON_LIFT_SQRT_COMPOSE THEN
  REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_DET_VECTORIZE THEN
  ASM_REWRITE_TAC[]);;

let GRGV_HAS_VOLUME_UNION_GEN = prove
 (`!top atlas (g:A->real^N^N) S1 S2 v w.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_has_volume (top,atlas) g S1 v /\ mfd_has_volume (top,atlas) g S2 w
        ==> ?u. mfd_has_volume (top,atlas) g (S1 UNION S2) u`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(S1:A->bool) UNION S2 = S1 UNION (S2 DIFF S1)` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_lebesgue_measurable (top,atlas:((A->bool)#(A->real^N))->bool) S1 /\
    mfd_lebesgue_measurable (top,atlas) S2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MFD_HAS_INTEGRAL_IMP_MEASURABLE THEN
    MAP_EVERY EXISTS_TAC [`g:A->real^N^N`; `\x:A. &1`] THEN
    ASM_MESON_TAC[mfd_has_volume];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `S2 DIFF S1:A->bool`; `S2:A->bool`; `w:real`]
                MFD_HAS_VOLUME_SUBSET) THEN
  ASM_SIMP_TAC[MFD_LEBESGUE_MEASURABLE_DIFF; SUBSET_DIFF] THEN STRIP_TAC THEN
  EXISTS_TAC `v + mfd_volume (top,atlas) (g:A->real^N^N) (S2 DIFF S1)` THEN
  MATCH_MP_TAC MFD_HAS_VOLUME_UNION THEN ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let GRGV_HAS_VOLUME_FINITE_UNIONS = prove
 (`!top atlas (g:A->real^N^N) u.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        FINITE u /\ (!s. s IN u ==> ?v. mfd_has_volume (top,atlas) g s v)
        ==> ?v. mfd_has_volume (top,atlas) g (UNIONS u) v`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[IMP_CONJ] THEN
  SPEC_TAC(`u:(A->bool)->bool`,`u:(A->bool)->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_0; UNIONS_INSERT; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  CONJ_TAC THENL [MESON_TAC[MFD_HAS_VOLUME_EMPTY]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:A->bool`; `u:(A->bool)->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(fun th -> DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `v:real`)
                                                 (MP_TAC o MATCH_MP th))) THEN
  DISCH_THEN(X_CHOOSE_TAC `w:real`) THEN
  MATCH_MP_TAC GRGV_HAS_VOLUME_UNION_GEN THEN
  MAP_EVERY EXISTS_TAC [`v:real`; `w:real`] THEN ASM_REWRITE_TAC[]);;

(* Every point has an open neighbourhood whose measurable subsets have      *)
(* finite volume.                                                            *)

let GRGV_LOCAL_FINITE_VOLUME = prove
 (`!top atlas (g:A->real^N^N) x.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        x IN topspace top
        ==> ?W. open_in top W /\ x IN W /\
                !S. mfd_lebesgue_measurable (top,atlas) S /\ S SUBSET W
                    ==> ?v. mfd_has_volume (top,atlas) g S v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?a b. SND(c:(A->bool)#(A->real^N)) x IN interval(a,b) /\
          interval[a,b] SUBSET IMAGE (SND c) (FST c)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `open (IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))` THEN
    REWRITE_TAC[OPEN_CONTAINS_INTERVAL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  EXISTS_TAC
   `{z:A | z IN FST(c:(A->bool)#(A->real^N)) /\ SND c z IN interval(a:real^N,b)}` THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `interval(a:real^N,b)`] GRGD_CHART_PREIMAGE_OPEN) THEN
    ASM_REWRITE_TAC[PAIR; OPEN_INTERVAL];
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  X_GEN_TAC `S:A->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(S:A->bool) SUBSET FST(c:(A->bool)#(A->real^N))` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `c:(A->bool)#(A->real^N)`; `S:A->bool`]
                MFD_HAS_VOLUME_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `lebesgue_measurable (IMAGE (SND(c:(A->bool)#(A->real^N))) S)`
  ASSUME_TAC THENL
   [UNDISCH_TAC
     `mfd_lebesgue_measurable (top,atlas:((A->bool)#(A->real^N))->bool) S` THEN
    REWRITE_TAC[mfd_lebesgue_measurable] THEN
    DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `drop(integral (IMAGE (SND(c:(A->bool)#(A->real^N))) S)
                 (\y. lift(mfd_density atlas c (g:A->real^N^N) y)))` THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
  EXISTS_TAC `interval[a:real^N,b]` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
    ASM_SIMP_TAC[GRGV_DENSITY_CONTINUOUS];
    MP_TAC(ISPECL [`a:real^N`; `b:real^N`] INTERVAL_OPEN_SUBSET_CLOSED) THEN
    ASM SET_TAC[]]);;

let MFD_HAS_VOLUME_COMPACT = prove
 (`!top atlas (g:A->real^N^N) K.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ compact_in top K
        ==> ?v. mfd_has_volume (top,atlas) g K v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `mfd_lebesgue_measurable (top,atlas:((A->bool)#(A->real^N))->bool) K`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_LEBESGUE_MEASURABLE_CLOSED THEN
    ASM_SIMP_TAC[COMPACT_IN_IMP_CLOSED_IN];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [compact_in]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (MP_TAC o SPEC
     `{W:A->bool | open_in top W /\
                   !S. mfd_lebesgue_measurable
                         (top,atlas:((A->bool)#(A->real^N))->bool) S /\
                       S SUBSET W
                       ==> ?v. mfd_has_volume (top,atlas) (g:A->real^N^N) S v}`)) THEN
  ANTS_TAC THENL
   [SIMP_TAC[IN_ELIM_THM] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] GRGV_LOCAL_FINITE_VOLUME) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `K = UNIONS {K INTER s:A->bool | s IN V}` SUBST1_TAC THENL
   [UNDISCH_TAC `(K:A->bool) SUBSET UNIONS V` THEN
    REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC GRGV_HAS_VOLUME_FINITE_UNIONS THEN
  ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `s:A->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `open_in top (s:A->bool) /\
    !S. mfd_lebesgue_measurable (top,atlas:((A->bool)#(A->real^N))->bool) S /\
        S SUBSET s
        ==> ?v. mfd_has_volume (top,atlas) (g:A->real^N^N) S v`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(s:A->bool) IN V` THEN
    UNDISCH_TAC
     `(V:(A->bool)->bool) SUBSET
      {W:A->bool | open_in top W /\
                   !S. mfd_lebesgue_measurable
                         (top,atlas:((A->bool)#(A->real^N))->bool) S /\
                       S SUBSET W
                       ==> ?v. mfd_has_volume (top,atlas) (g:A->real^N^N) S v}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[INTER_SUBSET] THEN
  SUBGOAL_THEN `K INTER s:A->bool = K DIFF (K DIFF s)` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MFD_LEBESGUE_MEASURABLE_DIFF THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MFD_LEBESGUE_MEASURABLE_DIFF THEN
  ASM_SIMP_TAC[MFD_LEBESGUE_MEASURABLE_OPEN]);;

(* Compact sets have a volume and open sets are measurable (used by the
   pc_rfa units). *)

let MFD_VOLUME_COMPACT_MEASURABLE_OPEN = prove
 (`!top atlas (g:A->real^N^N) K W.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ compact_in top K /\ open_in top W
     ==> (?v. mfd_has_volume (top,atlas) g K v) /\
         mfd_lebesgue_measurable (top,atlas) W`,
  MESON_TAC[MFD_HAS_VOLUME_COMPACT; MFD_LEBESGUE_MEASURABLE_OPEN]);;

(* Metric balls of a compact manifold have a volume (used by the pc_rfa
   units). *)

let MFD_HAS_VOLUME_BALL_COMPACT = prove
 (`!top atlas (g:A->real^N^N) x r.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     compact_space top /\ riemannian_metric atlas g
     ==> ?v. mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g x r) v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `topspace top:A->bool`] MFD_HAS_VOLUME_COMPACT) THEN
  ASM_REWRITE_TAC[GSYM compact_space] THEN
  DISCH_THEN(X_CHOOSE_TAC `w:real`) THEN
  EXISTS_TAC `mfd_volume (top,atlas) (g:A->real^N^N)
                (mfd_ball (top,atlas) g (x:A) r)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `mfd_ball (top,atlas) (g:A->real^N^N) (x:A) r`;
                 `topspace top:A->bool`; `w:real`] MFD_HAS_VOLUME_SUBSET) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `r:real`] MFD_BALL_OPEN) THEN
  ASM_SIMP_TAC[MFD_LEBESGUE_MEASURABLE_OPEN; OPEN_IN_SUBSET]);;

let MFD_HAS_VOLUME_OPEN_POS = prove
 (`!top atlas (g:A->real^N^N) W v.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        open_in top W /\ ~(W = {}) /\ mfd_has_volume (top,atlas) g W v
        ==> &0 < v`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `x:A`) THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `W' = FST(c:(A->bool)#(A->real^N)) INTER W` THEN
  SUBGOAL_THEN `open_in top (W':A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "W'" THEN ASM_SIMP_TAC[OPEN_IN_INTER]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN W'` ASSUME_TAC THENL
   [EXPAND_TAC "W'" THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(W':A->bool) SUBSET FST(c:(A->bool)#(A->real^N)) /\ W' SUBSET W`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "W'" THEN SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `W':A->bool`; `W:A->bool`; `v:real`]
                MFD_HAS_VOLUME_SUBSET) THEN
  ASM_SIMP_TAC[MFD_LEBESGUE_MEASURABLE_OPEN] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `mfd_volume (top,atlas) (g:A->real^N^N) W'` THEN
  ASM_REWRITE_TAC[REAL_LT_LE] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[MFD_HAS_VOLUME_POS_LE]; ALL_TAC] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  UNDISCH_TAC `mfd_has_volume (top,atlas) (g:A->real^N^N) W' (&0)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `c:(A->bool)#(A->real^N)`; `W':A->bool`; `&0`]
                MFD_HAS_VOLUME_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `((\y. lift(mfd_density atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N) y))
     has_integral vec 0) (IMAGE (SND c) W')`
  MP_TAC THENL
   [SUBGOAL_THEN
     `vec 0:real^1 =
      integral (IMAGE (SND(c:(A->bool)#(A->real^N))) W')
               (\y. lift(mfd_density atlas c (g:A->real^N^N) y))`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM DROP_EQ; DROP_VEC] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC INTEGRABLE_INTEGRAL THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\y. lift(mfd_density atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N) y)`;
    `IMAGE (SND(c:(A->bool)#(A->real^N))) W'`] HAS_INTEGRAL_NEGLIGIBLE_EQ) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_1; ARITH_RULE `1 <= i /\ i <= 1 <=> i = 1`] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[LIFT_COMPONENT] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC GRGV_DENSITY_POS THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `{y | y IN IMAGE (SND(c:(A->bool)#(A->real^N))) W' /\
         ~(lift(mfd_density atlas c (g:A->real^N^N) y) = vec 0)} =
    IMAGE (SND c) W'`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `(!y. y IN s ==> P y) ==> {y:real^N | y IN s /\ P y} = s`) THEN
    REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC GRGV_DENSITY_POS THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC OPEN_NOT_NEGLIGIBLE THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IMAGE_EQ_EMPTY] THEN ASM SET_TAC[]]);;

(* Balls of complete manifolds have finite volume, positive if nonempty. *)

let MFD_HAS_VOLUME_BALL = prove
 (`!top atlas (g:A->real^N^N) x r.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g
        ==> mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g x r)
                           (mfd_volume (top,atlas) g (mfd_ball (top,atlas) g x r)) /\
            (x IN topspace top /\ &0 < r
             ==> &0 < mfd_volume (top,atlas) g (mfd_ball (top,atlas) g x r))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `(x:A) IN topspace top` THENL
   [ALL_TAC;
    SUBGOAL_THEN `mfd_ball (top,atlas) (g:A->real^N^N) (x:A) r = {}` SUBST1_TAC THENL
     [REWRITE_TAC[mfd_ball; EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `{}:A->bool`; `&0`] MFD_HAS_VOLUME_VOLUME) THEN
      ASM_REWRITE_TAC[MFD_HAS_VOLUME_EMPTY] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[MFD_HAS_VOLUME_EMPTY]]] THEN
  SUBGOAL_THEN
   `open_in top (mfd_ball (top,atlas) (g:A->real^N^N) (x:A) r)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[MFD_BALL_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_has_volume (top,atlas) (g:A->real^N^N) (mfd_ball (top,atlas) g (x:A) r)
                   (mfd_volume (top,atlas) g (mfd_ball (top,atlas) g x r))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `mfd_cball (top,atlas) (g:A->real^N^N) (x:A) r`]
                  MFD_HAS_VOLUME_COMPACT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `mfd_complete (top,atlas:((A->bool)#(A->real^N))->bool)
                                (g:A->real^N^N)` THEN
      REWRITE_TAC[mfd_complete] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `w:real`) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `mfd_ball (top,atlas) (g:A->real^N^N) (x:A) r`;
                   `mfd_cball (top,atlas) (g:A->real^N^N) (x:A) r`; `w:real`]
                  MFD_HAS_VOLUME_SUBSET) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_SIMP_TAC[MFD_LEBESGUE_MEASURABLE_OPEN] THEN
    REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN
    MESON_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC MFD_HAS_VOLUME_OPEN_POS THEN
  MAP_EVERY EXISTS_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
    `mfd_ball (top,atlas) (g:A->real^N^N) (x:A) r`] THEN
  ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  EXISTS_TAC `x:A` THEN REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[MFD_JOINABLE_REFL; MFD_DIST_REFL]);;

