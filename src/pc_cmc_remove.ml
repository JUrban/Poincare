(* ========================================================================= *)
(* Unit pc_cmc_remove: energy bounds for the limits of CMC_GLOBAL, W^{1,2}   *)
(* on punctured balls, removal of the finite singular set (CM_REMOVABLE),    *)
(* and the limit as a planar harmonic map (cmc_pmap, cmc_pharm).  First: the *)
(* G-energy dominates the Euclidean energy; L^2 bounds of the partials of    *)
(* limits on compact sets.                                                   *)
(* ========================================================================= *)

needs "src/pc_cmc_global.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Energy bounds.                                                            *)
(* ------------------------------------------------------------------------- *)

let CMC_PEN_DOMINATES = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> ?lam. &0 < lam /\
               !(w:real^2->real^K) K i.
                  cmc_pmap S w /\ lebesgue_measurable K /\ 1 <= i /\ i <= 2
                  ==> wan_wd (:real^2) i w IN lspace K (&2) /\
                      lam * lnorm K (&2) (wan_wd (:real^2) i w) pow 2 <= cmc_pen G K w`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC) o
    MATCH_MP HMD_TARGET_ELLIPTIC) THEN
  EXISTS_TAC `lam:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_wd (:real^2) i (w:real^2->real^K) IN lspace K (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `w:real^2->real^K`; `i:num`] CMC_PMAP_WD) THEN
    ASM_SIMP_TAC[ETA_AX];
    ASM_REWRITE_TAC[]] THEN
  ASM_SIMP_TAC[WAN_SOB_LNORM2_SQ] THEN
  REWRITE_TAC[cmc_pen] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `w:real^2->real^K`;
                 `K:real^2->bool`] CMC_PEN_INTEGRABLE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x. lift(norm(wan_wd (:real^2) i (w:real^2->real^K) x) pow 2))
                integrable_on K` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  SUBGOAL_THEN
   `lam * drop(integral K (\x. lift(norm(wan_wd (:real^2) i (w:real^2->real^K) x) pow 2))) =
    drop(integral K (\x. lam % lift(norm(wan_wd (:real^2) i w x) pow 2)))`
  SUBST1_TAC THENL [ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL]; ALL_TAC] THEN
  MATCH_MP_TAC INTEGRAL_DROP_LE THEN
  ASM_SIMP_TAC[INTEGRABLE_CMUL; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  REWRITE_TAC[DROP_CMUL; LIFT_DROP; CMC_TRACE_GRAM] THEN
  SUBGOAL_THEN
   `!l. lam * norm(wan_wd (:real^2) l (w:real^2->real^K) x) pow 2 <=
        wan_wd (:real^2) l w x dot ((G:real^K->real^K^K)(w x) ** wan_wd (:real^2) l w x) /\
        &0 <= wan_wd (:real^2) l w x dot (G(w x) ** wan_wd (:real^2) l w x)`
  ASSUME_TAC THENL
   [GEN_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lam * norm(wan_wd (:real^2) l (w:real^2->real^K) x) pow 2` THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `i = 1 \/ i = 2` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `1` (ASSUME
   `!l. lam * norm(wan_wd (:real^2) l (w:real^2->real^K) x) pow 2 <=
        wan_wd (:real^2) l w x dot ((G:real^K->real^K^K)(w x) ** wan_wd (:real^2) l w x) /\
        &0 <= wan_wd (:real^2) l w x dot (G(w x) ** wan_wd (:real^2) l w x)`)) THEN
  MP_TAC(SPEC `2` (ASSUME
   `!l. lam * norm(wan_wd (:real^2) l (w:real^2->real^K) x) pow 2 <=
        wan_wd (:real^2) l w x dot ((G:real^K->real^K^K)(w x) ** wan_wd (:real^2) l w x) /\
        &0 <= wan_wd (:real^2) l w x dot (G(w x) ** wan_wd (:real^2) l w x)`)) THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* L^2 bounds of the partials of a limit; W^{1,2} on punctured balls.        *)
(* ------------------------------------------------------------------------- *)

let CMC_LIMIT_PD_BOUND = prove
 (`!S (G:real^K->real^K^K) d lam (w:num->real^2->real^K) b K E i.
     cm_target S G d /\ &0 < lam /\
     (!(w:real^2->real^K) K i.
        cmc_pmap S w /\ lebesgue_measurable K /\ 1 <= i /\ i <= 2
        ==> wan_wd (:real^2) i w IN lspace K (&2) /\
            lam * lnorm K (&2) (wan_wd (:real^2) i w) pow 2 <= cmc_pen G K w) /\
     (!j. cmc_pmap S (w j) /\ wan_gdir (:real^2) G (w j) <= E) /\
     lebesgue_measurable K /\ cmc_l2conv K w b /\ 1 <= i /\ i <= 2
     ==> (\x. partial_derivative i b x) IN lspace K (&2) /\
         lam * lnorm K (&2) (\x. partial_derivative i b x) pow 2 <= E`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "DOM") STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [cmc_l2conv]) THEN
  DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!j. wan_wd (:real^2) i ((w:num->real^2->real^K) j) IN lspace K (&2) /\
                    lam * lnorm K (&2) (wan_wd (:real^2) i (w j)) pow 2 <= E`
  ASSUME_TAC THENL
   [GEN_TAC THEN USE_THEN "DOM" (MP_TAC o SPECL
      [`(w:num->real^2->real^K) j`; `K:real^2->bool`; `i:num`]) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `cmc_pen G K ((w:num->real^2->real^K) j)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `cmc_pen G (:real^2) ((w:num->real^2->real^K) j)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CMC_PEN_MONO THEN MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_UNIV; SUBSET_UNIV];
      MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                     `(w:num->real^2->real^K) j`; `(:real^2)`] CMC_GDIR_PEN) THEN
      ASM_SIMP_TAC[OPEN_UNIV] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. partial_derivative i (b:real^2->real^K) x) IN lspace K (&2)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\x. partial_derivative i (b:real^2->real^K) x) =
                  (\x. wan_wd (:real^2) i ((w:num->real^2->real^K) 0) x -
                       (wan_wd (:real^2) i (w 0) x - partial_derivative i b x))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC LSPACE_SUB THEN ASM_SIMP_TAC[ETA_AX] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UBOUND) THEN
  EXISTS_TAC `\j. lam * lnorm K (&2) (wan_wd (:real^2) i ((w:num->real^2->real^K) j)) pow 2` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_LMUL THEN MATCH_MP_TAC REALLIM_POW THEN
    MP_TAC(ISPECL [`K:real^2->bool`;
                   `\j. wan_wd (:real^2) i ((w:num->real^2->real^K) j)`;
                   `\x. partial_derivative i (b:real^2->real^K) x`] WAN_LNORM2_CONV) THEN
    ASM_SIMP_TAC[ETA_AX];
    MATCH_MP_TAC ALWAYS_EVENTUALLY THEN ASM_SIMP_TAC[]]);;

let CMC_PD_L2_EXHAUST = prove
 (`!S (G:real^K->real^K^K) d lam (w:num->real^2->real^K) b U P (f:num->real^2->bool) E i.
     cm_target S G d /\ &0 < lam /\
     (!(w:real^2->real^K) K i.
        cmc_pmap S w /\ lebesgue_measurable K /\ 1 <= i /\ i <= 2
        ==> wan_wd (:real^2) i w IN lspace K (&2) /\
            lam * lnorm K (&2) (wan_wd (:real^2) i w) pow 2 <= cmc_pen G K w) /\
     (!j. cmc_pmap S (w j) /\ wan_gdir (:real^2) G (w j) <= E) /\
     (!K. compact K /\ K SUBSET U ==> cmc_l2conv K w b) /\
     (!j. compact (f j) /\ f j SUBSET U) /\ (!j. f j SUBSET f (SUC j)) /\
     UNIONS {f j | j IN (:num)} = P /\ 1 <= i /\ i <= 2
     ==> (\x. partial_derivative i b x) IN lspace P (&2) /\
         lam * lnorm P (&2) (\x. partial_derivative i b x) pow 2 <= E`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "DOM") STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN
   `!j. (\x. partial_derivative i (b:real^2->real^K) x) IN lspace (f j) (&2) /\
        lam * lnorm ((f:num->real^2->bool) j) (&2) (\x. partial_derivative i b x) pow 2 <= E`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CMC_LIMIT_PD_BOUND THEN
    MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                          `w:num->real^2->real^K`] THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`P:real^2->bool`; `f:num->real^2->bool`;
                 `\x. partial_derivative i (b:real^2->real^K) x`; `E / lam`]
                WAN_LNORM2_EXHAUST) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT; REAL_LE_RDIV_EQ] THEN
    GEN_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UBOUND) THEN
  EXISTS_TAC `\j. lnorm ((f:num->real^2->bool) j) (&2)
                        (\x. partial_derivative i (b:real^2->real^K) x) pow 2` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN MATCH_MP_TAC ALWAYS_EVENTUALLY THEN
  GEN_TAC THEN REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Exhaustions; W^{1,2} on punctured balls; removal of the singular set.     *)
(* ------------------------------------------------------------------------- *)

let CMC_PUNCT_EXHAUST = prove
 (`!(x:real^2) r.
     &0 < r
     ==> ?f. (!j. compact(f j) /\ f j SUBSET ball(x,r) DELETE x) /\
             (!j. f j SUBSET f (SUC j)) /\
             UNIONS {f j | j IN (:num)} = ball(x,r) DELETE x`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `\j. cball(x:real^2,r - r / &(j + 2)) DIFF ball(x,r / &(j + 2))` THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `!j. &0 < r / &(j + 2) /\ r / &(j + 2) < r` ASSUME_TAC THENL
   [GEN_TAC THEN ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_LDIV_EQ; REAL_OF_NUM_LT;
                              ARITH_RULE `0 < j + 2`] THEN
    MATCH_MP_TAC(REAL_ARITH `r * &1 < r * n ==> r < r * n`) THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN SIMP_TAC[COMPACT_DIFF; COMPACT_CBALL; OPEN_BALL] THEN
    REWRITE_TAC[SUBSET; IN_DIFF; IN_CBALL; IN_BALL; IN_DELETE] THEN
    X_GEN_TAC `y:real^2` THEN FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN
    REWRITE_TAC[dist] THEN STRIP_TAC THEN REWRITE_TAC[REAL_NOT_LT] THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
    UNDISCH_TAC `r / &(j + 2) <= norm(x - y:real^2)` THEN
    ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN ASM_REAL_ARITH_TAC;
    GEN_TAC THEN
    SUBGOAL_THEN `r / &(SUC j + 2) <= r / &(j + 2)` ASSUME_TAC THENL
     [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_DIFF; IN_CBALL; IN_BALL] THEN GEN_TAC THEN
    ASM_REAL_ARITH_TAC;
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN X_GEN_TAC `y:real^2` THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `s:real^2->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `j:num` ASSUME_TAC) MP_TAC)) THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (is_forall o concl)) THEN
      REWRITE_TAC[IN_DIFF; IN_CBALL; IN_BALL; IN_DELETE; dist] THEN STRIP_TAC THEN
      REWRITE_TAC[REAL_NOT_LT] THEN STRIP_TAC THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
      UNDISCH_TAC `r / &(j + 2) <= norm(x - y:real^2)` THEN
      ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IN_DELETE; IN_BALL; dist] THEN STRIP_TAC THEN
      SUBGOAL_THEN `&0 < norm(x - y:real^2)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
      MP_TAC(ISPEC `r / min (norm(x - y:real^2)) (r - norm(x - y))` REAL_ARCH_SIMPLE) THEN
      DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
      EXISTS_TAC `cball(x:real^2,r - r / &(n + 2)) DIFF ball(x,r / &(n + 2))` THEN
      CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `r / &(n + 2) <= min (norm(x - y:real^2)) (r - norm(x - y))` MP_TAC THENL
       [SUBGOAL_THEN `&0 < min (norm(x - y:real^2)) (r - norm(x - y))` ASSUME_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; ARITH_RULE `0 < n + 2`] THEN
        UNDISCH_TAC `r / min (norm(x - y:real^2)) (r - norm(x - y)) <= &n` THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN DISCH_TAC THEN
        SUBGOAL_THEN `&n * min (norm(x - y:real^2)) (r - norm(x - y)) <=
                      min (norm(x - y)) (r - norm(x - y)) * &(n + 2)` MP_TAC THENL
         [GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
          CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC];
          UNDISCH_TAC `r <= &n * min (norm(x - y:real^2)) (r - norm(x - y))` THEN
          REAL_ARITH_TAC];
        REWRITE_TAC[IN_DIFF; IN_CBALL; IN_BALL; dist; REAL_NOT_LT] THEN REAL_ARITH_TAC]]]);;

let CMC_COFINITE_EXHAUST = prove
 (`!X:real^2->bool.
     FINITE X
     ==> ?f. (!j. compact(f j) /\ f j SUBSET (:real^2) DIFF X) /\
             (!j. f j SUBSET f (SUC j)) /\
             UNIONS {f j | j IN (:num)} = (:real^2) DIFF X`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `\j. cball(vec 0:real^2,&j) DIFF
                  UNIONS (IMAGE (\x:real^2. ball(x,inv(&j + &1))) X)` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[COMPACT_CBALL] THEN
      MATCH_MP_TAC OPEN_UNIONS THEN REWRITE_TAC[FORALL_IN_IMAGE; OPEN_BALL];
      REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIV; IN_UNIONS; EXISTS_IN_IMAGE] THEN
      X_GEN_TAC `y:real^2` THEN STRIP_TAC THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN REWRITE_TAC[] THEN
      EXISTS_TAC `y:real^2` THEN
      ASM_REWRITE_TAC[CENTRE_IN_BALL; REAL_LT_INV_EQ] THEN REAL_ARITH_TAC];
    GEN_TAC THEN
    REWRITE_TAC[SUBSET; IN_DIFF; IN_CBALL_0; IN_UNIONS; EXISTS_IN_IMAGE; IN_BALL] THEN
    X_GEN_TAC `y:real^2` THEN
    SUBGOAL_THEN `inv(&(SUC j) + &1) <= inv(&j + &1) /\ &j <= &(SUC j)` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE; ARITH_RULE `j <= SUC j`] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT;
                                                   REAL_OF_NUM_LE] THEN ARITH_TAC;
      ALL_TAC] THEN
    MESON_TAC[REAL_LE_TRANS; REAL_LTE_TRANS; REAL_LT_TRANS; REAL_LET_TRANS];
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV; IN_DIFF] THEN X_GEN_TAC `y:real^2` THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `s:real^2->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `j:num` ASSUME_TAC) MP_TAC)) THEN
      ASM_REWRITE_TAC[IN_DIFF; IN_UNIONS; EXISTS_IN_IMAGE] THEN STRIP_TAC THEN
      DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN REWRITE_TAC[] THEN
      EXISTS_TAC `y:real^2` THEN
      ASM_REWRITE_TAC[CENTRE_IN_BALL; REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
      DISCH_TAC THEN
      MP_TAC(ISPEC `(y:real^2) INSERT X` CMC_FINITE_SEPARATED) THEN
      ASM_REWRITE_TAC[FINITE_INSERT] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPEC `max (norm(y:real^2)) (inv e)` REAL_ARCH_SIMPLE) THEN
      DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
      EXISTS_TAC `cball(vec 0:real^2,&n) DIFF
                  UNIONS (IMAGE (\x:real^2. ball(x,inv(&n + &1))) X)` THEN
      CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_DIFF; IN_CBALL_0; IN_UNIONS; EXISTS_IN_IMAGE; IN_BALL] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^2`; `x:real^2`] o check (is_forall o concl)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INSERT] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `inv(&n + &1) < e` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_LINV THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `dist(x:real^2,y) < inv(&n + &1)` THEN REWRITE_TAC[dist] THEN
        CONV_TAC NORM_ARITH]]]);;

(* ------------------------------------------------------------------------- *)
(* W^{1,2} on punctured balls and removal of the finite singular set.        *)
(* ------------------------------------------------------------------------- *)

let CMC_SMOOTH_LSPACE_PD = prove
 (`!S (G:real^K->real^K^K) d (w:num->real^2->real^K) b U P E.
     cm_target S G d /\ (!j. cmc_pmap S (w j) /\ wan_gdir (:real^2) G (w j) <= E) /\
     (!K. compact K /\ K SUBSET U ==> cmc_l2conv K w b) /\
     (?f. (!j. compact(f j) /\ f j SUBSET U) /\ (!j. f j SUBSET f (SUC j)) /\
          UNIONS {f j | j IN (:num)} = P)
     ==> !i. 1 <= i /\ i <= 2 ==> (\x. partial_derivative i b x) IN lspace P (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] CMC_PEN_DOMINATES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `lam:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `lam:real`;
                 `w:num->real^2->real^K`; `b:real^2->real^K`; `U:real^2->bool`;
                 `P:real^2->bool`; `f:num->real^2->bool`; `E:real`; `i:num`]
                CMC_PD_L2_EXHAUST) THEN
  ASM_SIMP_TAC[]);;

let CMC_PUNCTURED_W12 = prove
 (`!S (G:real^K->real^K^K) d (w:num->real^2->real^K) b U E x r.
     cm_target S G d /\ (!j. cmc_pmap S (w j) /\ wan_gdir (:real^2) G (w j) <= E) /\
     (!K. compact K /\ K SUBSET U ==> cmc_l2conv K w b) /\
     open U /\ smooth_map_on U b /\ (!y. y IN U ==> b y IN S) /\
     &0 < r /\ ball(x,r) DELETE x SUBSET U
     ==> wan_w12 (ball(x,r) DELETE x) b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  SUBGOAL_THEN `open(ball(x:real^2,r) DELETE x) /\ bounded(ball(x:real^2,r) DELETE x)`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[OPEN_DELETE; OPEN_BALL] THEN MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `ball(x:real^2,r)` THEN REWRITE_TAC[BOUNDED_BALL] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (ball(x:real^2,r) DELETE x) (b:real^2->real^K)` ASSUME_TAC
  THENL [ASM_MESON_TAC[SMOOTH_MAP_ON_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(:2)`; `(:K)`] WAN_W12_C1) THEN REWRITE_TAC[WAN_W12_C1_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`ball(x:real^2,r) DELETE x`; `b:real^2->real^K`]) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[DIMINDEX_2] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `smooth_map_on (ball(x:real^2,r) DELETE x) (b:real^2->real^K)` THEN
    SIMP_TAC[smooth_map_on];
    SUBGOAL_THEN `?MS. !z:real^K. z IN S ==> norm z <= MS` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[COMPACT_IMP_BOUNDED; bounded]; ALL_TAC] THEN
    MP_TAC(ISPECL [`ball(x:real^2,r) DELETE x`; `b:real^2->real^K`; `MS:real`]
                  CMC_BOUNDED_LNORM) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_SIMP_TAC[MEASURABLE_OPEN] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; SMOOTH_MAP_ON_CONTINUOUS_ON];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
    MATCH_MP_TAC CMC_SMOOTH_LSPACE_PD THEN
    MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                          `w:num->real^2->real^K`; `U:real^2->bool`; `E:real`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`x:real^2`; `r:real`] CMC_PUNCT_EXHAUST) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Removal of the finite singular set: the limit extends to a harmonic map   *)
(* on the whole plane with L^2 partials and values in TT.                    *)
(* ------------------------------------------------------------------------- *)

let CMC_LSPACE_COFINITE = prove
 (`!U (f:real^2->real^K).
     FINITE((:real^2) DIFF U) /\ f continuous_on (:real^2) /\ f IN lspace U (&2)
     ==> f IN lspace (:real^2) (&2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lspace; IN_ELIM_THM] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CONTINUOUS_IMP_MEASURABLE_ON] THEN
  MP_TAC(ISPECL [`\x. lift(norm((f:real^2->real^K) x) rpow &2)`; `U:real^2->bool`;
                 `(:real^2)`] INTEGRABLE_SPIKE_SET) THEN
  ANTS_TAC THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
  MATCH_MP_TAC NEGLIGIBLE_FINITE THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `(:real^2) DIFF U` THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let CMC_REMOVE_POINTS = prove
 (`!S (G:real^K->real^K^K) d (w:num->real^2->real^K) b U E TT.
     CM_REMOVABLE_STATEMENT (:K) /\ cm_target S G d /\ closed TT /\
     (!j. cmc_pmap S (w j) /\ wan_gdir (:real^2) G (w j) <= E) /\
     open U /\ FINITE((:real^2) DIFF U) /\ cm_harmonic S G U b /\
     (!x. x IN U ==> b x IN TT) /\
     (!K. compact K /\ K SUBSET U ==> cmc_l2conv K w b)
     ==> ?b'. cm_harmonic S G (:real^2) b' /\ (!x. x IN U ==> b' x = b x) /\
              (!x. b' x IN TT) /\
              (!i. 1 <= i /\ i <= 2
                   ==> (\x. partial_derivative i b' x) IN lspace (:real^2) (&2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_harmonic]) THEN
  ABBREV_TAC `X = (:real^2) DIFF U` THEN
  SUBGOAL_THEN `!y:real^2. y IN U <=> ~(y IN X)` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `X:real^2->bool` CMC_FINITE_SEPARATED) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x:real^2. x IN X ==> ball(x,e / &2) DELETE x SUBSET U` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET; IN_DELETE; IN_BALL] THEN
    X_GEN_TAC `y:real^2` THEN STRIP_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^2`; `y:real^2`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `e:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `dist(x:real^2,y) < e / &2` THEN
    UNDISCH_TAC `&0 < e` THEN REWRITE_TAC[dist] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* The local extensions. *)
  SUBGOAL_THEN
   `!x:real^2. ?h:real^2->real^K.
        x IN X ==> cm_harmonic S G (ball(x,e / &2)) h /\
                   !y. y IN ball(x,e / &2) DELETE x ==> h y = b y`
  MP_TAC THENL
   [X_GEN_TAC `x:real^2` THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
    UNDISCH_TAC `CM_REMOVABLE_STATEMENT (:K)` THEN REWRITE_TAC[CM_REMOVABLE_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`x:real^2`; `e / &2`; `b:real^2->real^K`]) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC HMC_HARMONIC_SUBSET THEN EXISTS_TAC `U:real^2->bool` THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC CMC_PUNCTURED_W12 THEN
      MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                            `w:num->real^2->real^K`; `U:real^2->bool`; `E:real`] THEN
      ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `h:real^2->real^2->real^K` (LABEL_TAC "H"))] THEN
  ABBREV_TAC `b' = \y:real^2. if y IN X then (h:real^2->real^2->real^K) y y
                              else (b:real^2->real^K) y` THEN
  SUBGOAL_THEN `!y:real^2. y IN U ==> (b':real^2->real^K) y = b y` ASSUME_TAC THENL
   [EXPAND_TAC "b'" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y:real^2. x IN X /\ y IN ball(x,e / &2)
                 ==> (b':real^2->real^K) y = (h:real^2->real^2->real^K) x y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `y:real^2 = x` THENL
     [EXPAND_TAC "b'" THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `(y:real^2) IN U` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN CONV_TAC SYM_CONV THEN
      USE_THEN "H" (MP_TAC o SPEC `x:real^2`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[IN_DELETE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < e / &2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* Smoothness and harmonicity on the plane. *)
  SUBGOAL_THEN `cm_harmonic S G (:real^2) (b':real^2->real^K)` ASSUME_TAC THENL
   [MATCH_MP_TAC CMC_HARMONIC_LOCAL THEN EXISTS_TAC `d:real` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    SUBGOAL_THEN
     `!y:real^2. ?r. &0 < r /\ cm_harmonic S G (ball(y,r)) (b':real^2->real^K)`
    ASSUME_TAC THENL
     [X_GEN_TAC `y:real^2` THEN ASM_CASES_TAC `(y:real^2) IN X` THENL
       [EXISTS_TAC `e / &2` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC HMD_HARMONIC_CONG THEN
        EXISTS_TAC `(h:real^2->real^2->real^K) y` THEN
        CONJ_TAC THENL
         [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
          ASM_REWRITE_TAC[];
          USE_THEN "H" (MP_TAC o SPEC `y:real^2`) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
        SUBGOAL_THEN `(y:real^2) IN U` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        MP_TAC(ISPEC `U:real^2->bool` OPEN_CONTAINS_BALL) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o SPEC `y:real^2`) THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HMD_HARMONIC_CONG THEN
        EXISTS_TAC `b:real^2->real^K` THEN CONJ_TAC THENL
         [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
          ASM SET_TAC[];
          MATCH_MP_TAC HMC_HARMONIC_SUBSET THEN EXISTS_TAC `U:real^2->bool` THEN
          ASM_REWRITE_TAC[]]];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
      X_GEN_TAC `y:real^2` THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC o SPEC `y:real^2`) THEN
      EXISTS_TAC `ball(y:real^2,r)` THEN ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
      ASM_MESON_TAC[cm_harmonic];
      CONJ_TAC THENL
       [X_GEN_TAC `y:real^2` THEN
        FIRST_X_ASSUM(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC o SPEC `y:real^2`) THEN
        ASM_MESON_TAC[cm_harmonic; CENTRE_IN_BALL];
        X_GEN_TAC `y:real^2` THEN
        FIRST_X_ASSUM(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC o SPEC `y:real^2`) THEN
        EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[SUBSET_UNIV]]];
    ALL_TAC] THEN
  EXISTS_TAC `b':real^2->real^K` THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_MESON_TAC[];
    (* values in TT *)
    X_GEN_TAC `x:real^2` THEN ASM_CASES_TAC `(x:real^2) IN X` THENL
     [ALL_TAC; ASM_MESON_TAC[]] THEN
    MATCH_MP_TAC(ISPEC `at (x:real^2)` LIM_IN_CLOSED_SET) THEN
    EXISTS_TAC `b':real^2->real^K` THEN ASM_REWRITE_TAC[TRIVIAL_LIMIT_AT] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[EVENTUALLY_AT] THEN EXISTS_TAC `e / &2` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `y:real^2` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(y:real^2) IN U` ASSUME_TAC THENL
       [MP_TAC(SPEC `x:real^2` (ASSUME
         `!x:real^2. x IN X ==> ball(x,e / &2) DELETE x SUBSET U`)) THEN
        REWRITE_TAC[SUBSET; IN_DELETE; IN_BALL] THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN MATCH_MP_TAC] THEN
        CONJ_TAC THENL [ASM_MESON_TAC[DIST_SYM]; ALL_TAC] THEN
        DISCH_TAC THEN UNDISCH_TAC `&0 < dist(y:real^2,x)` THEN
        ASM_REWRITE_TAC[DIST_REFL; REAL_LT_REFL];
        ASM_SIMP_TAC[]];
      REWRITE_TAC[GSYM CONTINUOUS_AT] THEN
      SUBGOAL_THEN `(b':real^2->real^K) continuous_on (:real^2)` MP_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_MESON_TAC[cm_harmonic];
        SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV]]];
    (* L^2 partials *)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC CMC_LSPACE_COFINITE THEN
    EXISTS_TAC `U:real^2->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC CMC_PD_CONTINUOUS THEN
      ASM_MESON_TAC[cm_harmonic; OPEN_UNIV];
      ALL_TAC] THEN
    SUBGOAL_THEN `(\x. partial_derivative i (b:real^2->real^K) x) IN lspace U (&2)`
    MP_TAC THENL
     [MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                     `w:num->real^2->real^K`; `b:real^2->real^K`; `U:real^2->bool`;
                     `U:real^2->bool`; `E:real`] CMC_SMOOTH_LSPACE_PD) THEN
      ANTS_TAC THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `X:real^2->bool` CMC_COFINITE_EXHAUST) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^2->bool`; `{}:real^2->bool`;
                   `\x. partial_derivative i (b:real^2->real^K) x`;
                   `\x. partial_derivative i (b':real^2->real^K) x`; `&2`]
                  WAN_LSPACE_LNORM_SPIKE) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    REWRITE_TAC[NEGLIGIBLE_EMPTY; DIFF_EMPTY] THEN
    X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN
    EXISTS_TAC `U:real^2->bool` THEN ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The global limit as a planar harmonic map.                                *)
(* ------------------------------------------------------------------------- *)

let CMC_L2CONV_CONG2 = prove
 (`!U E (w:num->real^2->real^K) u u'.
     open U /\ E SUBSET U /\ (!x. x IN U ==> u x = u' x) /\ cmc_l2conv E w u
     ==> cmc_l2conv E w u'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!i x. x IN E ==> partial_derivative i (u:real^2->real^K) x =
                                 partial_derivative i u' x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN
    EXISTS_TAC `U:real^2->bool` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN E ==> (u:real^2->real^K) x = u' x` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!j. (\x. (w:num->real^2->real^K) j x - u' x) IN lspace E (&2) <=>
         (\x. w j x - u x) IN lspace E (&2)) /\
    (!j. lnorm E (&2) (\x. (w:num->real^2->real^K) j x - u' x) =
         lnorm E (&2) (\x. w j x - u x))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN GEN_TAC THEN
    MP_TAC(ISPECL [`E:real^2->bool`; `{}:real^2->bool`;
                   `\x. (w:num->real^2->real^K) j x - u' x`;
                   `\x. (w:num->real^2->real^K) j x - u x`; `&2`] WAN_LSPACE_LNORM_SPIKE) THEN
    ASM_SIMP_TAC[NEGLIGIBLE_EMPTY; DIFF_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!i j. (\x. wan_wd (:real^2) i ((w:num->real^2->real^K) j) x -
                partial_derivative i u' x) IN lspace E (&2) <=>
           (\x. wan_wd (:real^2) i (w j) x - partial_derivative i u x) IN lspace E (&2)) /\
    (!i j. lnorm E (&2) (\x. wan_wd (:real^2) i ((w:num->real^2->real^K) j) x -
                             partial_derivative i u' x) =
           lnorm E (&2) (\x. wan_wd (:real^2) i (w j) x - partial_derivative i u x))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`E:real^2->bool`; `{}:real^2->bool`;
                   `\x. wan_wd (:real^2) i ((w:num->real^2->real^K) j) x -
                        partial_derivative i (u':real^2->real^K) x`;
                   `\x. wan_wd (:real^2) i ((w:num->real^2->real^K) j) x -
                        partial_derivative i (u:real^2->real^K) x`; `&2`]
                  WAN_LSPACE_LNORM_SPIKE) THEN
    ASM_SIMP_TAC[NEGLIGIBLE_EMPTY; DIFF_EMPTY];
    ALL_TAC] THEN
  UNDISCH_TAC `cmc_l2conv E (w:num->real^2->real^K) u` THEN
  ASM_REWRITE_TAC[cmc_l2conv]);;

let CMC_PHARM_PMAP = prove
 (`!S (G:real^K->real^K^K) (b:real^2->real^K).
     cm_harmonic S G (:real^2) b /\
     (!i. 1 <= i /\ i <= 2 ==> (\x. partial_derivative i b x) IN lspace (:real^2) (&2))
     ==> cmc_pharm S G b /\ cmc_pmap S b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[cmc_pharm; cmc_pmap] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_harmonic]) THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[IN_UNIV]; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  EXISTS_TAC `\x. partial_derivative i (b:real^2->real^K) x` THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC WAN_WPD_C1 THEN REWRITE_TAC[OPEN_UNIV] THEN
  UNDISCH_TAC `smooth_map_on (:real^2) (b:real^2->real^K)` THEN SIMP_TAC[smooth_map_on]);;

let CMC_GLOBAL_PHARM = prove
 (`!S (G:real^K->real^K^K) d eL (C:num->real) e0 (w:num->real^2->real^K) eta E TT.
     CM_REMOVABLE_STATEMENT (:K) /\
     cm_target S G d /\ cmc_regc S G eL C /\ &0 < e0 /\ e0 <= eL /\
     (eta ---> &0) sequentially /\ closed TT /\ (!j x. w j x IN TT) /\
     (!j. cmc_pmap S (w j) /\ cmc_ah S G e0 (eta j) (w j) /\
          wan_gdir (:real^2) G (w j) <= E)
     ==> ?(t:num->num) U (b:real^2->real^K).
           (!m n. m < n ==> t m < t n) /\ open U /\ FINITE((:real^2) DIFF U) /\
           cmc_pharm S G b /\ cmc_pmap S b /\ (!x. b x IN TT) /\
           (!K. compact K /\ K SUBSET U ==> cmc_l2conv K (\j. w (t j)) b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `eL:real`;
                 `C:num->real`; `e0:real`; `w:num->real^2->real^K`; `eta:num->real`;
                 `E:real`; `TT:real^K->bool`] CMC_GLOBAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num->num` (X_CHOOSE_THEN `U:real^2->bool`
    (X_CHOOSE_THEN `b:real^2->real^K` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`;
                 `\j. (w:num->real^2->real^K) ((t:num->num) j)`; `b:real^2->real^K`;
                 `U:real^2->bool`; `E:real`; `TT:real^K->bool`] CMC_REMOVE_POINTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b':real^2->real^K` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`t:num->num`; `U:real^2->bool`; `b':real^2->real^K`] THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CMC_PHARM_PMAP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CMC_L2CONV_CONG2 THEN
  MAP_EVERY EXISTS_TAC [`U:real^2->bool`; `b:real^2->real^K`] THEN
  ASM_SIMP_TAC[]);;

