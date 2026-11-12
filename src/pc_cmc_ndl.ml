(* ========================================================================= *)
(* Unit pc_cmc_ndl: CM Prop B.29 (angular energy on long necks of almost     *)
(* harmonic maps, by the covering argument) and the neck energy decay used   *)
(* for the energy identity.  First integrals over concentric annuli.         *)
(* ========================================================================= *)

needs "src/pc_cmc_neck.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Integrals over concentric annuli.                                         *)
(* ------------------------------------------------------------------------- *)

let CMC_ANN_SPLIT = prove
 (`!(h:real^2->real) (y:real^2) r1 r2 r3.
     r1 <= r2 /\ r2 <= r3 /\
     (\x. lift(h x)) absolutely_integrable_on cmc_ann y r1 r3
     ==> drop(integral (cmc_ann y r1 r3) (\x. lift(h x))) =
         drop(integral (cmc_ann y r1 r2) (\x. lift(h x))) +
         drop(integral (cmc_ann y r2 r3) (\x. lift(h x)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `cmc_ann (y:real^2) r1 r2 SUBSET cmc_ann y r1 r3 /\
                cmc_ann (y:real^2) r2 r3 SUBSET cmc_ann y r1 r3`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; cmc_ann; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(\x. lift((h:real^2->real) x)) integrable_on cmc_ann y r1 r2 /\
                (\x. lift(h x)) integrable_on cmc_ann y r2 r3`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `cmc_ann (y:real^2) r1 r3` THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; CMC_OPEN_ANN];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM DROP_ADD] THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`\x. lift((h:real^2->real) x)`; `cmc_ann (y:real^2) r1 r2`;
                 `cmc_ann (y:real^2) r2 r3`] INTEGRAL_UNION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `{}:real^2->bool` THEN REWRITE_TAC[NEGLIGIBLE_EMPTY] THEN
    REWRITE_TAC[SUBSET; IN_INTER; cmc_ann; IN_ELIM_THM; NOT_IN_EMPTY] THEN REAL_ARITH_TAC;
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC INTEGRAL_SPIKE_SET THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `sphere(y:real^2,r2)` THEN REWRITE_TAC[NEGLIGIBLE_SPHERE] THEN
  REWRITE_TAC[SUBSET; IN_DIFF; IN_UNION; cmc_ann; IN_ELIM_THM; IN_SPHERE] THEN
  X_GEN_TAC `x:real^2` THEN REWRITE_TAC[dist] THEN
  MP_TAC(ISPECL [`x:real^2`; `y:real^2`] NORM_SUB) THEN
  UNDISCH_TAC `r1:real <= r2` THEN UNDISCH_TAC `r2:real <= r3` THEN REAL_ARITH_TAC);;

let CMC_ANN_SUM = prove
 (`!(h:real^2->real) (y:real^2) (r:num->real) n.
     (!k. k <= n ==> r k <= r (SUC k)) /\
     (\x. lift(h x)) absolutely_integrable_on cmc_ann y (r 0) (r (SUC n))
     ==> drop(integral (cmc_ann y (r 0) (r (SUC n))) (\x. lift(h x))) =
         sum(0..n) (\k. drop(integral (cmc_ann y (r k) (r (SUC k))) (\x. lift(h x))))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[SUM_SING_NUMSEG]; ALL_TAC] THEN
  STRIP_TAC THEN REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
  SUBGOAL_THEN `r 0 <= (r:num->real) (SUC n) /\ r (SUC n) <= r (SUC(SUC n))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `!k. k <= SUC n ==> (r:num->real) 0 <= r k` (fun th -> MATCH_MP_TAC th) THENL
       [INDUCT_TAC THENL [REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
        DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(r:num->real) k` THEN
        CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `SUC`)) (concl th))) THEN ASM_ARITH_TAC;
        ARITH_TAC];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:real^2->real`; `y:real^2`; `(r:num->real) 0`; `(r:num->real) (SUC n)`;
                 `(r:num->real) (SUC(SUC n))`] CMC_ANN_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `cmc_ann (y:real^2) (r 0) (r (SUC(SUC n)))` THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; CMC_OPEN_ANN] THEN
    REWRITE_TAC[SUBSET; cmc_ann; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* CM Prop B.29, one annulus: the angular energy of the middle part is       *)
(* controlled by the energy, or by the error of one harmonic replacement.    *)
(* ------------------------------------------------------------------------- *)

let CMC_B29_BALL = prove
 (`!(y:real^2) rho l.
     &0 < rho /\ &1 <= l
     ==> &0 < rho * (&1 - exp(--(&3 * l))) / &2 /\
         cball(y + rho % basis 1,rho * (&1 - exp(--(&3 * l))) / &2) SUBSET
         cmc_nk y rho (&3 * l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `l:real` CMC_EXP_LADDER) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&4 <= exp(&3 * l)` ASSUME_TAC THENL
   [MP_TAC(SPEC `&3 * l` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_CBALL; cmc_nk; cmc_ann; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  SUBGOAL_THEN `norm((y + rho % basis 1) - y:real^2) = rho` ASSUME_TAC THENL
   [REWRITE_TAC[VECTOR_ARITH `((y:real^2) + rho % b) - y = rho % b`; NORM_MUL] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_2; ARITH] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `dist(y + rho % basis 1,x:real^2) <= rho * (&1 - exp(--(&3 * l))) / &2` THEN
  REWRITE_TAC[dist] THEN DISCH_TAC THEN
  SUBGOAL_THEN `norm(x - y:real^2) <= rho + rho * (&1 - exp(--(&3 * l))) / &2 /\
                rho - rho * (&1 - exp(--(&3 * l))) / &2 <= norm(x - y)` MP_TAC THENL
   [MATCH_MP_TAC(NORM_ARITH `!c x y:real^2 rho r0.
                                norm(c - y) = rho /\ norm(c - x) <= r0
                                ==> norm(x - y) <= rho + r0 /\ rho - r0 <= norm(x - y)`) THEN
    EXISTS_TAC `y + rho % basis 1:real^2` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `rho * exp(--(&3 * l)) < rho * (&1 - (&1 - exp(--(&3 * l))) / &2) /\
                rho * (&1 + (&1 - exp(--(&3 * l))) / &2) < rho * exp(&3 * l)`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let CMC_B29_ONE = prove
 (`!S (G:real^K->real^K^K) d eL (C:num->real) lam Lam delta l e2 mu
    (w:real^2->real^K) (y:real^2) rho.
     cm_target S G d /\ cmc_regc S G eL C /\ &0 < lam /\ &0 < mu /\ &1 <= l /\
     e2 <= eL /\ &0 <= delta /\
     (!(w:real^2->real^K) E. cmc_pmap S w /\ lebesgue_measurable E
                             ==> lam * cmc_eE E w <= cmc_pen G E w /\
                                 cmc_pen G E w <= Lam * cmc_eE E w) /\
     (!(w:real^2->real^K) y rho.
        cmc_pmap S w /\ &0 < rho /\
        cmc_pen G (cmc_nk y rho (&3 * l)) w <= e2 /\
        cmc_srb S G mu (cmc_nk y rho (&3 * l)) w
        ==> cmc_angE y (cmc_nk y rho l) w <= delta * cmc_eE (cmc_nk y rho (&3 * l)) w) /\
     cmc_pmap S w /\ &0 < rho /\ cmc_pen G (cmc_nk y rho (&3 * l)) w <= e2
     ==> ?c r (v:real^2->real^K).
           &0 < r /\ cball(c,r) SUBSET cmc_nk y rho (&3 * l) /\
           cm_minimizer S G (ball(c,r / &8)) v /\
           wan_w120 (ball(c,r / &8)) (\x. v x - w x) /\
           cmc_angE y (cmc_nk y rho l) w <=
           delta * cmc_eE (cmc_nk y rho (&3 * l)) w +
           (&2 / (lam * mu)) * wan_dir (ball(c,r / &8)) (\x. w x - v x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cmc_regc]) THEN
  MP_TAC(ISPECL [`y:real^2`; `rho:real`; `l:real`; `&3 * l`] CMC_NK_FACTS) THEN
  MP_TAC(ISPECL [`y:real^2`; `rho:real`; `&3 * l`; `&3 * l`] CMC_NK_FACTS) THEN
  ASM_SIMP_TAC[REAL_LE_REFL; REAL_ARITH `&1 <= l ==> &0 <= l /\ l <= &3 * l /\ &0 <= &3 * l`] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  SUBGOAL_THEN `!c r (v:real^2->real^K).
                  &0 < r /\ cball(c,r) SUBSET cmc_nk y rho (&3 * l) /\
                  wan_w120 (ball(c,r / &8)) (\x. v x - w x)
                  ==> &0 <= wan_dir (ball(c,r / &8)) (\x. w x - v x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_DIR_POS THEN
    MP_TAC(ISPECL [`ball(c:real^2,r / &8)`; `\x. (v:real^2->real^K) x - w x`]
                  WAN_W120_NEG) THEN
    ASM_REWRITE_TAC[OPEN_BALL; VECTOR_NEG_SUB] THEN SIMP_TAC[wan_w120];
    ALL_TAC] THEN
  ASM_CASES_TAC `cmc_srb S G mu (cmc_nk y rho (&3 * l)) (w:real^2->real^K)` THENL
   [(* good annulus: any ball with its replacement *)
    MP_TAC(ISPECL [`y:real^2`; `rho:real`; `l:real`] CMC_B29_BALL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ABBREV_TAC `c0 = y + rho % basis 1:real^2` THEN
    ABBREV_TAC `r0 = rho * (&1 - exp(--(&3 * l))) / &2` THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `eL:real`; `C:num->real`;
                   `w:real^2->real^K`; `c0:real^2`; `r0 / &8`] CMC_REP_ONE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `cmc_pen G (cmc_nk y rho (&3 * l)) (w:real^2->real^K)` THEN
      CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[REAL_LE_TRANS]] THEN
      MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `w:real^2->real^K`;
                     `ball(c0:real^2,r0 / &8)`] CMC_GDIR_PEN) THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC CMC_PEN_MONO THEN MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
      ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(c0:real^2,r0)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `ball(c0:real^2,r0)` THEN REWRITE_TAC[BALL_SUBSET_CBALL] THEN
      MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^2->real^K` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`c0:real^2`; `r0:real`; `v:real^2->real^K`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b /\ &0 <= c ==> a <= b + c`) THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `cmc_srb:(real^K->bool)->(real^K->real^K^K)->real->(real^2->bool)->(real^2->real^K)->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    (* bad annulus: the violating ball *)
    UNDISCH_TAC `~cmc_srb S G mu (cmc_nk y rho (&3 * l)) (w:real^2->real^K)` THEN
    REWRITE_TAC[cmc_srb; NOT_FORALL_THM; NOT_IMP; REAL_NOT_LE] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real^2` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real^2->real^K` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= b /\ a <= c ==> a <= b + c`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CMC_EE_POS THEN EXISTS_TAC `S:real^K->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 * cmc_eE (cmc_nk y rho (&3 * l)) (w:real^2->real^K)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&2 * cmc_eE (cmc_nk y rho l) (w:real^2->real^K)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC CMC_ANGE_LE_EE THEN EXISTS_TAC `S:real^K->bool` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC CMC_EE_MONO THEN EXISTS_TAC `S:real^K->bool` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&2 / lam) * cmc_pen G (cmc_nk y rho (&3 * l)) (w:real^2->real^K)` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`w:real^2->real^K`; `cmc_nk y rho (&3 * l)`]
        (ASSUME `!(w:real^2->real^K) E. cmc_pmap S w /\ lebesgue_measurable E
                                         ==> lam * cmc_eE E w <= cmc_pen G E w /\
                                             cmc_pen G E w <= Lam * cmc_eE E w`)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      SUBGOAL_THEN `&2 * cmc_eE (cmc_nk y rho (&3 * l)) (w:real^2->real^K) =
                    (&2 / lam) * (lam * cmc_eE (cmc_nk y rho (&3 * l)) w)` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(&2 / (lam * mu)) * wan_dir (ball(c,r / &8)) (\x. (w:real^2->real^K) x - v x) =
                  (&2 / lam) * (wan_dir (ball(c,r / &8)) (\x. w x - v x) / mu)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < lam` THEN UNDISCH_TAC `&0 < mu` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* CM Prop B.29 for one family of consecutive annuli.                        *)
(* ------------------------------------------------------------------------- *)

let CMC_EE_ABS_INTEGRABLE = prove
 (`!S (w:real^2->real^K) E.
     cmc_pmap S w /\ lebesgue_measurable E
     ==> (\x. lift(norm(wan_wd (:real^2) 1 w x) pow 2 + norm(wan_wd (:real^2) 2 w x) pow 2))
         absolutely_integrable_on E`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `w:real^2->real^K`; `E:real^2->bool`] CMC_EE_INTEGRABLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[DIMINDEX_1; ARITH_RULE `1 <= i /\ i <= 1 <=> i = 1`] THEN
  SIMP_TAC[LIFT_COMPONENT; REAL_LE_ADD; REAL_LE_POW_2]);;

let CMC_NK_EXP = prove
 (`!(y:real^2) b t l.
     cmc_nk y (b * exp((&6 * &t + &3) * l)) (&3 * l) =
     cmc_ann y (b * exp(&6 * &t * l)) (b * exp(&6 * &(t + 1) * l))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmc_nk; GSYM REAL_MUL_ASSOC; GSYM REAL_EXP_ADD] THEN
  BINOP_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC);;

let CMC_ANN_DISJOINT = prove
 (`!(y:real^2) r1 r2 r3 r4. r2 <= r3 ==> DISJOINT (cmc_ann y r1 r2) (cmc_ann y r3 r4)`,
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; cmc_ann; IN_ELIM_THM] THEN
  REAL_ARITH_TAC);;

let CMC_PEN_UNIONS_GEN = prove
 (`!S (G:real^K->real^K^K) d (w:real^2->real^K) (B:A->real^2->bool) Y.
     cm_target S G d /\ cmc_pmap S w /\ FINITE Y /\
     (!y. y IN Y ==> lebesgue_measurable(B y)) /\
     (!y y'. y IN Y /\ y' IN Y /\ ~(y = y') ==> DISJOINT (B y) (B y'))
     ==> sum Y (\y. cmc_pen G (B y) w) = cmc_pen G (UNIONS (IMAGE B Y)) w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!Y. FINITE Y
        ==> ((!y. y IN Y ==> lebesgue_measurable((B:A->real^2->bool) y)) /\
             (!y y'. y IN Y /\ y' IN Y /\ ~(y = y') ==> DISJOINT (B y) (B y'))
             ==> sum Y (\y. cmc_pen G (B y) (w:real^2->real^K)) =
                 cmc_pen G (UNIONS (IMAGE B Y)) w)`
  (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[SUM_CLAUSES; IMAGE_CLAUSES; UNIONS_0; cmc_pen; INTEGRAL_EMPTY; DROP_VEC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y:A`; `Z:A->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH") STRIP_ASSUME_TAC) THEN STRIP_TAC THEN
  ASM_SIMP_TAC[SUM_CLAUSES; IMAGE_CLAUSES; UNIONS_INSERT] THEN
  SUBGOAL_THEN `sum Z (\y. cmc_pen G ((B:A->real^2->bool) y) (w:real^2->real^K)) =
                cmc_pen G (UNIONS (IMAGE B Z)) w` SUBST1_TAC THENL
   [USE_THEN "IH" MATCH_MP_TAC THEN CONJ_TAC THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC CMC_PEN_UNION THEN
  MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    MATCH_MP_TAC LEBESGUE_MEASURABLE_UNIONS THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    REWRITE_TAC[DISJOINT; INTER_UNIONS; EMPTY_UNIONS; FORALL_IN_GSPEC; FORALL_IN_IMAGE] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM DISJOINT] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]);;

let CMC_ANN_FAMILY_DISJ = prove
 (`!(y:real^2) b l t t'.
     &0 < b /\ &0 <= l /\ ~(t = t')
     ==> DISJOINT (cmc_ann y (b * exp(&6 * &t * l)) (b * exp(&6 * &(t + 1) * l)))
                  (cmc_ann y (b * exp(&6 * &t' * l)) (b * exp(&6 * &(t' + 1) * l)))`,
  SUBGOAL_THEN
   `!(y:real^2) b l t t'.
      &0 < b /\ &0 <= l /\ t < t'
      ==> DISJOINT (cmc_ann y (b * exp(&6 * &t * l)) (b * exp(&6 * &(t + 1) * l)))
                   (cmc_ann y (b * exp(&6 * &t' * l)) (b * exp(&6 * &(t' + 1) * l)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMC_ANN_DISJOINT THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_EXP_MONO_LE] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `t < t' \/ t' < (t:num)` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[DISJOINT_SYM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

let CMC_B29_FAMILY = prove
 (`!S (G:real^K->real^K^K) d eL (C:num->real) lam Lam delta l e2 mu e0 eta
    (w:real^2->real^K) (y:real^2) b m.
     cm_target S G d /\ cmc_regc S G eL C /\ &0 < lam /\ &0 < mu /\ &1 <= l /\
     e2 <= eL /\ &0 <= delta /\ e2 < e0 /\
     (!(w:real^2->real^K) E. cmc_pmap S w /\ lebesgue_measurable E
                             ==> lam * cmc_eE E w <= cmc_pen G E w /\
                                 cmc_pen G E w <= Lam * cmc_eE E w) /\
     (!(w:real^2->real^K) y rho.
        cmc_pmap S w /\ &0 < rho /\
        cmc_pen G (cmc_nk y rho (&3 * l)) w <= e2 /\
        cmc_srb S G mu (cmc_nk y rho (&3 * l)) w
        ==> cmc_angE y (cmc_nk y rho l) w <= delta * cmc_eE (cmc_nk y rho (&3 * l)) w) /\
     cmc_pmap S w /\ cmc_ah S G e0 eta w /\ &0 < b /\
     cmc_pen G (cmc_ann y b (b * exp(&6 * &(m + 1) * l))) w <= e2
     ==> sum(0..m) (\t. cmc_angE y (cmc_nk y (b * exp((&6 * &t + &3) * l)) l) w)
         <= delta * cmc_eE (cmc_ann y b (b * exp(&6 * &(m + 1) * l))) w +
            (&2 / (lam * mu)) * eta`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  ABBREV_TAC `N0 = cmc_ann (y:real^2) b (b * exp(&6 * &(m + 1) * l))` THEN
  SUBGOAL_THEN `!t. t <= m
                    ==> cmc_ann (y:real^2) (b * exp(&6 * &t * l)) (b * exp(&6 * &(t + 1) * l))
                        SUBSET N0`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:num` THEN DISCH_TAC THEN EXPAND_TAC "N0" THEN
    REWRITE_TAC[SUBSET; cmc_ann; IN_ELIM_THM] THEN X_GEN_TAC `x:real^2` THEN
    SUBGOAL_THEN `b <= b * exp(&6 * &t * l) /\ b * exp(&6 * &(t + 1) * l) <= b * exp(&6 * &(m + 1) * l)`
    MP_TAC THENL
     [CONJ_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_EXP_MONO_LE] THEN
        REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE] THEN
        ASM_ARITH_TAC];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the replacement balls *)
  SUBGOAL_THEN
   `!t. t IN 0..m
        ==> ?c r (v:real^2->real^K).
              &0 < r /\
              cball(c,r) SUBSET cmc_ann y (b * exp(&6 * &t * l)) (b * exp(&6 * &(t + 1) * l)) /\
              cm_minimizer S G (ball(c,r / &8)) v /\
              wan_w120 (ball(c,r / &8)) (\x. v x - w x) /\
              cmc_angE y (cmc_nk y (b * exp((&6 * &t + &3) * l)) l) w <=
              delta * cmc_eE (cmc_ann y (b * exp(&6 * &t * l)) (b * exp(&6 * &(t + 1) * l))) w +
              (&2 / (lam * mu)) * wan_dir (ball(c,r / &8)) (\x. w x - v x)`
  MP_TAC THENL
   [X_GEN_TAC `t:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM CMC_NK_EXP] THEN MATCH_MP_TAC CMC_B29_ONE THEN
    MAP_EVERY EXISTS_TAC [`d:real`; `eL:real`; `C:num->real`; `Lam:real`; `e2:real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `cmc_pen G N0 (w:real^2->real^K)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CMC_PEN_MONO THEN
    MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
    ASM_SIMP_TAC[CMC_NK_EXP] THEN
    EXPAND_TAC "N0" THEN SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; CMC_OPEN_ANN];
    REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:num->real^2` (X_CHOOSE_THEN `r:num->real`
      (X_CHOOSE_THEN `v:num->real^2->real^K` (LABEL_TAC "BALLS"))))] THEN
  (* the errors of the replacements, by (B) *)
  SUBGOAL_THEN
   `sum(0..m) (\t. wan_dir (ball((c:num->real^2) t,(r:num->real) t / &8))
                     (\x. (w:real^2->real^K) x - (v:num->real^2->real^K) t x)) <= eta`
  ASSUME_TAC THENL
   [UNDISCH_TAC `cmc_ah S G e0 eta (w:real^2->real^K)` THEN REWRITE_TAC[cmc_ah] THEN
    DISCH_THEN(MP_TAC o SPECL [`m + 1`; `\k. (c:num->real^2) (k - 1)`;
                               `\k. (r:num->real) (k - 1)`;
                               `\k. (v:num->real^2->real^K) (k - 1)`]) THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `!f:num->real. sum(1..m + 1) (\k. f(k - 1)) = sum(0..m) f`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN MP_TAC(ISPECL [`1`; `\k:num. (f:num->real)(k - 1)`; `0`; `m:num`] SUM_OFFSET) THEN
      REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `(i + 1) - 1 = i`; ETA_AX] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ADD_SUB; ETA_AX];
      ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      USE_THEN "BALLS" (MP_TAC o SPEC `k - 1`) THEN
      ANTS_TAC THENL [REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC; SIMP_TAC[]];
      MAP_EVERY X_GEN_TAC [`k:num`; `k':num`] THEN STRIP_TAC THEN
      USE_THEN "BALLS" (MP_TAC o SPEC `k - 1`) THEN
      ANTS_TAC THENL [REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
      USE_THEN "BALLS" (MP_TAC o SPEC `k' - 1`) THEN
      ANTS_TAC THENL [REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
      MATCH_MP_TAC(SET_RULE `!a b s t. a SUBSET s /\ b SUBSET t /\ DISJOINT s t
                                       ==> DISJOINT (a:real^2->bool) b`) THEN
      MAP_EVERY EXISTS_TAC
       [`cmc_ann (y:real^2) (b * exp(&6 * &(k - 1) * l)) (b * exp(&6 * &((k - 1) + 1) * l))`;
        `cmc_ann (y:real^2) (b * exp(&6 * &(k' - 1) * l)) (b * exp(&6 * &((k' - 1) + 1) * l))`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CMC_ANN_DISJOINT THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_EXP_MONO_LE] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC;
      ALL_TAC;
      X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      USE_THEN "BALLS" (MP_TAC o SPEC `k - 1`) THEN
      ANTS_TAC THENL [REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC; SIMP_TAC[]]] THEN
    (* the total energy of the balls *)
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `e2:real` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `cmc_pen G N0 (w:real^2->real^K)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `sum(0..m) (\t. wan_gdir (ball((c:num->real^2) t,(r:num->real) t)) G (w:real^2->real^K)) =
      cmc_pen G (UNIONS (IMAGE (\t. ball(c t,r t)) (0..m))) w`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `w:real^2->real^K`;
                     `\t. ball((c:num->real^2) t,(r:num->real) t)`; `0..m`] CMC_PEN_UNIONS_GEN) THEN
      REWRITE_TAC[FINITE_NUMSEG; LEBESGUE_MEASURABLE_BALL] THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`t:num`; `t':num`] THEN STRIP_TAC THEN
        MATCH_MP_TAC(SET_RULE `!a b s t. a SUBSET s /\ b SUBSET t /\ DISJOINT s t
                                         ==> DISJOINT (a:real^2->bool) b`) THEN
        MAP_EVERY EXISTS_TAC
         [`cmc_ann (y:real^2) (b * exp(&6 * &t * l)) (b * exp(&6 * &(t + 1) * l))`;
          `cmc_ann (y:real^2) (b * exp(&6 * &t' * l)) (b * exp(&6 * &(t' + 1) * l))`] THEN
        USE_THEN "BALLS" (MP_TAC o SPEC `t:num`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
        USE_THEN "BALLS" (MP_TAC o SPEC `t':num`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
        REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball((c:num->real^2) t,(r:num->real) t)` THEN
          ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
          MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball((c:num->real^2) t',(r:num->real) t')` THEN
          ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
          MATCH_MP_TAC CMC_ANN_FAMILY_DISJ THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
        DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
        REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC CMC_GDIR_PEN THEN
        MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
        ASM_REWRITE_TAC[OPEN_BALL]];
      ALL_TAC] THEN
    MATCH_MP_TAC CMC_PEN_MONO THEN MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LEBESGUE_MEASURABLE_UNIONS THEN
      SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; FORALL_IN_IMAGE; LEBESGUE_MEASURABLE_BALL];
      EXPAND_TAC "N0" THEN SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; CMC_OPEN_ANN];
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `t:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `cmc_ann (y:real^2) (b * exp(&6 * &t * l)) (b * exp(&6 * &(t + 1) * l))` THEN
      CONJ_TAC THENL
       [USE_THEN "BALLS" (MP_TAC o SPEC `t:num`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball((c:num->real^2) t,(r:num->real) t)` THEN
        ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
        FIRST_X_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC `t IN 0..m` THEN
        REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC]];
    ALL_TAC] THEN
  (* summing up *)
  SUBGOAL_THEN
   `sum(0..m) (\t. cmc_eE (cmc_ann (y:real^2) (b * exp(&6 * &t * l)) (b * exp(&6 * &(t + 1) * l)))
                          (w:real^2->real^K)) = cmc_eE N0 w`
  ASSUME_TAC THENL
   [EXPAND_TAC "N0" THEN REWRITE_TAC[cmc_eE] THEN
    MP_TAC(ISPECL [`\x. norm(wan_wd (:real^2) 1 (w:real^2->real^K) x) pow 2 +
                        norm(wan_wd (:real^2) 2 w x) pow 2`;
                   `y:real^2`; `\t. b * exp(&6 * &t * l)`; `m:num`] CMC_ANN_SUM) THEN
    REWRITE_TAC[ADD1; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_EXP_0; REAL_MUL_RID] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_EXP_MONO_LE] THEN
        REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE] THEN ARITH_TAC;
        MATCH_MP_TAC CMC_EE_ABS_INTEGRABLE THEN EXISTS_TAC `S:real^K->bool` THEN
        ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; CMC_OPEN_ANN]];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(0..m) (\t. delta * cmc_eE (cmc_ann (y:real^2) (b * exp(&6 * &t * l))
                                       (b * exp(&6 * &(t + 1) * l))) (w:real^2->real^K) +
                   (&2 / (lam * mu)) *
                   wan_dir (ball((c:num->real^2) t,(r:num->real) t / &8))
                     (\x. w x - (v:num->real^2->real^K) t x))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `t:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "BALLS" (MP_TAC o SPEC `t:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[IN_NUMSEG]; SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG; SUM_LMUL] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN REWRITE_TAC[REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

(* ------------------------------------------------------------------------- *)
(* CM Prop B.29: angular energy on long necks.                               *)
(* ------------------------------------------------------------------------- *)

let CMC_SUM_MOD3 = prove
 (`!(f:num->real) m.
     sum(0..3 * m + 2) f =
     sum(0..m) (\t. f(3 * t)) + sum(0..m) (\t. f(3 * t + 1)) + sum(0..m) (\t. f(3 * t + 2))`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUM_SING_NUMSEG] THEN
    REWRITE_TAC[ARITH_RULE `2 = SUC(SUC 0)`; SUM_CLAUSES_NUMSEG; LE_0] THEN
    REWRITE_TAC[ARITH; SUM_SING_NUMSEG] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `3 * SUC m + 2 = SUC(SUC(SUC(3 * m + 2)))`] THEN
  ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THEN
  REWRITE_TAC[ARITH_RULE `SUC(3 * m + 2) = 3 * SUC m /\ SUC(SUC(3 * m + 2)) = 3 * SUC m + 1 /\
                          SUC(SUC(SUC(3 * m + 2))) = 3 * SUC m + 2`] THEN
  REAL_ARITH_TAC);;

let CMC_NK_MID = prove
 (`!(y:real^2) s r t l.
     cmc_nk y ((s * exp(&2 * &r * l)) * exp((&6 * &t + &3) * l)) l =
     cmc_ann y (s * exp((&2 * &(3 * t + r) + &2) * l)) (s * exp((&2 * &(3 * t + r) + &4) * l))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmc_nk; GSYM REAL_MUL_ASSOC; GSYM REAL_EXP_ADD] THEN
  BINOP_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC);;

let CMC_B29 = prove
 (`!S (G:real^K->real^K^K) d eL (C:num->real) lam Lam delta l e2 mu e0 eta
    (w:real^2->real^K) (y:real^2) s m.
     cm_target S G d /\ cmc_regc S G eL C /\ &0 < lam /\ &0 < mu /\ &1 <= l /\
     e2 <= eL /\ &0 <= delta /\ e2 < e0 /\
     (!(w:real^2->real^K) E. cmc_pmap S w /\ lebesgue_measurable E
                             ==> lam * cmc_eE E w <= cmc_pen G E w /\
                                 cmc_pen G E w <= Lam * cmc_eE E w) /\
     (!(w:real^2->real^K) y rho.
        cmc_pmap S w /\ &0 < rho /\
        cmc_pen G (cmc_nk y rho (&3 * l)) w <= e2 /\
        cmc_srb S G mu (cmc_nk y rho (&3 * l)) w
        ==> cmc_angE y (cmc_nk y rho l) w <= delta * cmc_eE (cmc_nk y rho (&3 * l)) w) /\
     cmc_pmap S w /\ cmc_ah S G e0 eta w /\ &0 < s /\
     cmc_pen G (cmc_ann y s (s * exp((&6 * &m + &10) * l))) w <= e2
     ==> cmc_angE y (cmc_ann y (s * exp(&2 * l)) (s * exp((&6 * &m + &8) * l))) w
         <= &3 * delta * cmc_eE (cmc_ann y s (s * exp((&6 * &m + &10) * l))) w +
            (&6 / (lam * mu)) * eta`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  ABBREV_TAC `N = cmc_ann (y:real^2) s (s * exp((&6 * &m + &10) * l))` THEN
  ABBREV_TAC `f = \k. cmc_angE (y:real^2)
                        (cmc_ann y (s * exp((&2 * &k + &2) * l)) (s * exp((&2 * &k + &4) * l)))
                        (w:real^2->real^K)` THEN
  SUBGOAL_THEN `cmc_angE (y:real^2) (cmc_ann y (s * exp(&2 * l)) (s * exp((&6 * &m + &8) * l)))
                  (w:real^2->real^K) = sum(0..3 * m + 2) f` SUBST1_TAC THENL
   [EXPAND_TAC "f" THEN REWRITE_TAC[cmc_angE] THEN
    MP_TAC(ISPECL [`\x. norm(cmc_angd (y:real^2) x (wan_wd (:real^2) 1 (w:real^2->real^K) x)
                                            (wan_wd (:real^2) 2 w x)) pow 2`;
                   `y:real^2`; `\k. s * exp((&2 * &k + &2) * l)`; `3 * m + 2`] CMC_ANN_SUM) THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `!k. s * exp((&2 * &(SUC k) + &2) * l) = s * exp((&2 * &k + &4) * l)`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `s * exp((&2 * &0 + &2) * l) = s * exp(&2 * l) /\
                  s * exp((&2 * &(3 * m + 2) + &4) * l) = s * exp((&6 * &m + &8) * l)`
    (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [X_GEN_TAC `k:num` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_EXP_MONO_LE] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
    REWRITE_TAC[DIMINDEX_1; ARITH_RULE `1 <= i /\ i <= 1 <=> i = 1`] THEN
    SIMP_TAC[LIFT_COMPONENT; REAL_LE_POW_2] THEN
    MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `w:real^2->real^K`; `y:real^2`;
                   `cmc_ann (y:real^2) (s * exp(&2 * l)) (s * exp((&6 * &m + &8) * l))`]
                  CMC_ENERGIES_L2) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[CMC_OPEN_ANN] THEN
    REWRITE_TAC[cmc_ann; IN_ELIM_THM; VECTOR_SUB_REFL; NORM_0] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x < &0 /\ &0 < y)`) THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT];
    ALL_TAC] THEN
  REWRITE_TAC[CMC_SUM_MOD3] THEN
  SUBGOAL_THEN
   `!r. r <= 2
        ==> sum(0..m) (\t. (f:num->real) (3 * t + r)) <=
            delta * cmc_eE N (w:real^2->real^K) + (&2 / (lam * mu)) * eta`
  MP_TAC THENL
   [X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    ABBREV_TAC `b = s * exp(&2 * &r * l)` THEN
    SUBGOAL_THEN `&0 < b /\ cmc_ann (y:real^2) b (b * exp(&6 * &(m + 1) * l)) SUBSET N`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "b" THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
      EXPAND_TAC "N" THEN REWRITE_TAC[SUBSET; cmc_ann; IN_ELIM_THM] THEN X_GEN_TAC `x:real^2` THEN
      SUBGOAL_THEN `s <= s * exp(&2 * &r * l) /\
                    (s * exp(&2 * &r * l)) * exp(&6 * &(m + 1) * l) <=
                    s * exp((&6 * &m + &10) * l)` MP_TAC THENL
       [CONJ_TAC THENL
         [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
          GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
          MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
          MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
          REWRITE_TAC[GSYM REAL_MUL_ASSOC; GSYM REAL_EXP_ADD] THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_EXP_MONO_LE] THEN
          REWRITE_TAC[GSYM REAL_ADD_RDISTRIB; REAL_MUL_ASSOC] THEN
          MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
          REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
          UNDISCH_TAC `r <= 2` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC];
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `delta * cmc_eE (cmc_ann (y:real^2) b (b * exp(&6 * &(m + 1) * l)))
                               (w:real^2->real^K) + (&2 / (lam * mu)) * eta` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "f" THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `!t. cmc_ann (y:real^2) (s * exp((&2 * &(3 * t + r) + &2) * l))
                               (s * exp((&2 * &(3 * t + r) + &4) * l)) =
            cmc_nk y (b * exp((&6 * &t + &3) * l)) l`
      (fun th -> REWRITE_TAC[th]) THENL
       [GEN_TAC THEN EXPAND_TAC "b" THEN REWRITE_TAC[CMC_NK_MID]; ALL_TAC] THEN
      MATCH_MP_TAC CMC_B29_FAMILY THEN
      MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `eL:real`;
                            `C:num->real`; `Lam:real`; `e2:real`; `e0:real`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `cmc_pen G N (w:real^2->real^K)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CMC_PEN_MONO THEN MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "N" THEN
      SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; CMC_OPEN_ANN];
      REWRITE_TAC[REAL_LE_RADD] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CMC_EE_MONO THEN EXISTS_TAC `S:real^K->bool` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "N" THEN SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; CMC_OPEN_ANN]];
    DISCH_THEN(fun th -> MP_TAC(SPEC `0` th) THEN MP_TAC(SPEC `1` th) THEN
                         MP_TAC(SPEC `2` th)) THEN
    REWRITE_TAC[ARITH; ADD_CLAUSES] THEN
    SUBGOAL_THEN `&6 / (lam * mu) * eta = &3 * (&2 / (lam * mu) * eta)` SUBST1_TAC THENL
     [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Radial and angular parts: the energy density is at most three times the *)
(* angular density plus twice the conformality defect.                     *)
(* ------------------------------------------------------------------------- *)

let CMC_RAD_ANG_ALG = prove
 (`!(H:real^K^K) (g1:real^K) g2 u1 u2.
     transp H = H /\ u1 pow 2 + u2 pow 2 = &1
     ==> g1 dot (H ** g1) + g2 dot (H ** g2) =
         (u1 % g1 + u2 % g2) dot (H ** (u1 % g1 + u2 % g2)) +
         (--u2 % g1 + u1 % g2) dot (H ** (--u2 % g1 + u1 % g2)) /\
         (g1 dot (H ** g1)) * (g2 dot (H ** g2)) - (g1 dot (H ** g2)) pow 2 =
         ((u1 % g1 + u2 % g2) dot (H ** (u1 % g1 + u2 % g2))) *
         ((--u2 % g1 + u1 % g2) dot (H ** (--u2 % g1 + u1 % g2))) -
         ((u1 % g1 + u2 % g2) dot (H ** (--u2 % g1 + u1 % g2))) pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(g2:real^K) dot ((H:real^K^K) ** g1) = g1 dot (H ** g2)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [DOT_SYM] THEN
    REWRITE_TAC[GSYM DOT_MATRIX_TRANSP_RMUL] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL; DOT_LADD; DOT_RADD;
              DOT_LMUL; DOT_RMUL] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `p = (g1:real^K) dot ((H:real^K^K) ** g1)` THEN
  ABBREV_TAC `q = (g1:real^K) dot ((H:real^K^K) ** g2)` THEN
  ABBREV_TAC `t = (g2:real^K) dot ((H:real^K^K) ** g2)` THEN
  UNDISCH_TAC `u1 pow 2 + u2 pow 2 = &1` THEN CONV_TAC REAL_RING);;

let CMC_DEFECT_PW = prove
 (`!(G:real^K->real^K^K) (w:real^2->real^K) (y:real^2) x Lam.
     (!z. transp(G z) = G z) /\ (!z v. &0 <= v dot (G z ** v)) /\
     (!z (xi:real^K). xi dot (G z ** xi) <= Lam * norm xi pow 2) /\ ~(x = y)
     ==> trace(cmc_gram G w x) <=
         &3 * Lam * norm(cmc_angd y x (wan_wd (:real^2) 1 w x) (wan_wd (:real^2) 2 w x)) pow 2 +
         &2 * (trace(cmc_gram G w x) - cmc_tden G G w x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `w:real^2->real^K`; `x:real^2`] CMC_GRAM_PSD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CMC_TRACE_GRAM] THEN
  SUBGOAL_THEN `det(cmc_gram G (w:real^2->real^K) x) =
                (wan_wd (:real^2) 1 w x dot (G(w x) ** wan_wd (:real^2) 1 w x)) *
                (wan_wd (:real^2) 2 w x dot (G(w x) ** wan_wd (:real^2) 2 w x)) -
                (wan_wd (:real^2) 1 w x dot (G(w x) ** wan_wd (:real^2) 2 w x)) pow 2`
  SUBST1_TAC THENL
   [REWRITE_TAC[DET_2; CMC_GRAM2_ENTRIES; REAL_POW_2] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [DOT_SYM] THEN
    REWRITE_TAC[GSYM DOT_MATRIX_TRANSP_RMUL] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `g1 = wan_wd (:real^2) 1 (w:real^2->real^K) x` THEN
  ABBREV_TAC `g2 = wan_wd (:real^2) 2 (w:real^2->real^K) x` THEN
  ABBREV_TAC `H = (G:real^K->real^K^K) (w(x:real^2))` THEN
  SUBGOAL_THEN `transp(H:real^K^K) = H /\ (!v. &0 <= v dot (H ** v)) /\
                (!xi. xi dot (H ** xi) <= Lam * norm(xi:real^K) pow 2)`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "H" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `n = norm(x - y:real^2)` THEN
  SUBGOAL_THEN `&0 < n` ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
  ABBREV_TAC `u1 = (x - y:real^2)$1 / n` THEN ABBREV_TAC `u2 = (x - y:real^2)$2 / n` THEN
  SUBGOAL_THEN `u1 pow 2 + u2 pow 2 = &1` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["u1"; "u2"] THEN
    SUBGOAL_THEN `n pow 2 = ((x - y:real^2)$1) pow 2 + ((x - y)$2) pow 2` MP_TAC THENL
     [EXPAND_TAC "n" THEN REWRITE_TAC[NORM_POW_2; DOT_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&0 < n` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `cmc_angd y x (g1:real^K) g2 = --u2 % g1 + u1 % g2` SUBST1_TAC THENL
   [REWRITE_TAC[cmc_angd] THEN ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["u1"; "u2"] THEN
    REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC; real_div] THEN
    REWRITE_TAC[REAL_MUL_RNEG; REAL_MUL_LNEG] THEN BINOP_TAC THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`H:real^K^K`; `g1:real^K`; `g2:real^K`; `u1:real`; `u2:real`]
                CMC_RAD_ANG_ALG) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC) THEN
  ABBREV_TAC `r:real^K = u1 % g1 + u2 % g2` THEN
  ABBREV_TAC `a:real^K = --u2 % g1 + u1 % g2` THEN
  ABBREV_TAC `R = (r:real^K) dot ((H:real^K^K) ** r)` THEN
  ABBREV_TAC `A = (a:real^K) dot ((H:real^K^K) ** a)` THEN
  ABBREV_TAC `X = (r:real^K) dot ((H:real^K^K) ** a)` THEN
  SUBGOAL_THEN `&0 <= R /\ &0 <= A /\ A <= Lam * norm(a:real^K) pow 2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["R"; "A"] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(R * A - X pow 2) <= sqrt R * sqrt A` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SQRT_MUL] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
    MP_TAC(SPEC `X:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 * (sqrt R * sqrt A) <= R + &4 * A` ASSUME_TAC THENL
   [MP_TAC(SPEC `sqrt R - &2 * sqrt A` REAL_LE_POW_2) THEN
    ASM_SIMP_TAC[REAL_ARITH `(a - &2 * b) pow 2 = a pow 2 - &4 * (a * b) + &4 * b pow 2`;
                 SQRT_POW_2] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let CMC_DEFECT_FACTS = prove
 (`!S (G:real^K->real^K^K) d (w:real^2->real^K) E.
     cm_target S G d /\ cmc_pmap S w /\ lebesgue_measurable E
     ==> (\x. lift(cmc_tden G G w x)) absolutely_integrable_on E /\
         (\x. lift(trace(cmc_gram G w x) - cmc_tden G G w x)) absolutely_integrable_on E /\
         (!x. &0 <= trace(cmc_gram G w x) - cmc_tden G G w x) /\
         cmc_pen G E w - cmc_ptr G G E w =
         drop(integral E (\x. lift(trace(cmc_gram G w x) - cmc_tden G G w x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `G:real^K->real^K^K`]
                CMC_PTR_FACTS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `w:real^2->real^K`;
                 `E:real^2->bool`] CMC_PEN_INTEGRABLE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x. lift(cmc_tden G G (w:real^2->real^K) x)) absolutely_integrable_on E`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] HMD_TARGET_ELLIPTIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `Lam:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!x. &0 <= trace(cmc_gram G (w:real^2->real^K) x) - cmc_tden G G w x`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`G:real^K->real^K^K`; `w:real^2->real^K`; `x:real^2`] CMC_GRAM_PSD_FACTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `lam * norm(v:real^K) pow 2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_POW_2];
      REAL_ARITH_TAC];
    ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[LIFT_SUB] THEN CONJ_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[cmc_pen; cmc_ptr; GSYM DROP_SUB] THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_SUB THEN
  ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE]);;

let CMC_DEFECT_MONO = prove
 (`!S (G:real^K->real^K^K) d (w:real^2->real^K) E E'.
     cm_target S G d /\ cmc_pmap S w /\ lebesgue_measurable E /\ lebesgue_measurable E' /\
     E SUBSET E'
     ==> &0 <= cmc_pen G E w - cmc_ptr G G E w /\
         cmc_pen G E w - cmc_ptr G G E w <= cmc_pen G E' w - cmc_ptr G G E' w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `w:real^2->real^K`;
                 `E:real^2->bool`] CMC_DEFECT_FACTS) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `w:real^2->real^K`;
                 `E':real^2->bool`] CMC_DEFECT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC INTEGRAL_DROP_POS THEN
    ASM_SIMP_TAC[LIFT_DROP; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
    MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
    ASM_SIMP_TAC[LIFT_DROP; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE]]);;

let CMC_PEN_DEFECT_BOUND = prove
 (`!S (G:real^K->real^K^K) d Lam (w:real^2->real^K) (y:real^2) E.
     cm_target S G d /\ (!z (xi:real^K). xi dot (G z ** xi) <= Lam * norm xi pow 2) /\
     cmc_pmap S w /\ open E /\ ~(y IN E)
     ==> cmc_pen G E w <= &3 * Lam * cmc_angE y E w + &2 * (cmc_pen G E w - cmc_ptr G G E w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMC_TARGET_BASICS) THEN
  SUBGOAL_THEN `lebesgue_measurable(E:real^2->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `w:real^2->real^K`;
                 `E:real^2->bool`] CMC_DEFECT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `w:real^2->real^K`; `y:real^2`; `E:real^2->bool`]
                CMC_ENERGIES_L2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `w:real^2->real^K`;
                 `E:real^2->bool`] CMC_PEN_INTEGRABLE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[cmc_angE; cmc_pen] THEN
  SUBGOAL_THEN
   `(\x. lift(norm(cmc_angd y x (wan_wd (:real^2) 1 (w:real^2->real^K) x)
                                (wan_wd (:real^2) 2 w x)) pow 2)) integrable_on E`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `fa = \x. norm(cmc_angd y x (wan_wd (:real^2) 1 (w:real^2->real^K) x)
                                           (wan_wd (:real^2) 2 w x)) pow 2` THEN
  ABBREV_TAC `fd = \x. trace(cmc_gram G (w:real^2->real^K) x) - cmc_tden G G w x` THEN
  SUBGOAL_THEN `(\x. lift((fa:real^2->real) x)) integrable_on E /\
                (\x. lift((fd:real^2->real) x)) integrable_on E /\
                (\x. lift(trace(cmc_gram G (w:real^2->real^K) x))) integrable_on E`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["fa"; "fd"] THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN E ==> trace(cmc_gram G (w:real^2->real^K) x) <=
                               &3 * Lam * (fa:real^2->real) x + &2 * fd x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN MAP_EVERY EXPAND_TAC ["fa"; "fd"] THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC CMC_DEFECT_PW THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] HMD_TARGET_ELLIPTIC) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `lam * norm(v:real^K) pow 2` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_POW_2];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral E (\x. lift(&3 * Lam * (fa:real^2->real) x + &2 * fd x)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_SIMP_TAC[LIFT_DROP] THEN
    REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN MATCH_MP_TAC INTEGRABLE_ADD THEN
    ASM_SIMP_TAC[INTEGRABLE_CMUL];
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN
  ASM_SIMP_TAC[INTEGRAL_ADD; INTEGRAL_CMUL; INTEGRABLE_CMUL; DROP_ADD; DROP_CMUL] THEN
  MAP_EVERY EXPAND_TAC ["fa"; "fd"] THEN REWRITE_TAC[REAL_LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* The neck energy decay.                                                    *)
(* ------------------------------------------------------------------------- *)

let CMC_AH_ETA_POS = prove
 (`!S (G:real^K->real^K^K) e0 eta (w:real^2->real^K). cmc_ah S G e0 eta w /\ &0 < e0 ==> &0 <= eta`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmc_ah] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `(\k. vec 0):num->real^2`; `(\k. &1):num->real`;
                                `(\k x. vec 0):num->real^2->real^K`]) THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH] THEN ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[]);;

let CMC_NECK_DECAY = prove
 (`!S (G:real^K->real^K^K) d eL (C:num->real) e0.
     cm_target S G d /\ cmc_regc S G eL C /\ &0 < e0
     ==> ?l e2 Kc. &1 <= l /\ &0 < e2 /\ &0 <= Kc /\
           !(w:real^2->real^K) eta (y:real^2) s m.
             cmc_pmap S w /\ cmc_ah S G e0 eta w /\ &0 < s /\
             cmc_pen G (cmc_ann y s (s * exp((&6 * &m + &10) * l))) w <= e2
             ==> cmc_pen G (cmc_ann y (s * exp(&2 * l)) (s * exp((&6 * &m + &8) * l))) w
                 <= cmc_pen G (cmc_ann y s (s * exp((&6 * &m + &10) * l))) w / &2 +
                    Kc * (eta + (cmc_pen G (cmc_ann y s (s * exp((&6 * &m + &10) * l))) w -
                                 cmc_ptr G G (cmc_ann y s (s * exp((&6 * &m + &10) * l))) w))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] CMC_EE_PEN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `Lam:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "EP"))))) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`] HMD_TARGET_ELLIPTIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam2:real` (X_CHOOSE_THEN `Lam2:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `&0 < Lam2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!z (xi:real^K). xi dot ((G:real^K->real^K^K) z ** xi) <= Lam2 * norm xi pow 2`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `eL:real`; `C:num->real`;
                 `lam / (&18 * Lam2)`] CMC_B31) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real` (X_CHOOSE_THEN `e2:real` (X_CHOOSE_THEN `mu:real`
    STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cmc_regc]) THEN
  SUBGOAL_THEN
   `!(w:real^2->real^K) (y:real^2) rho.
        cmc_pmap S w /\ &0 < rho /\
        cmc_pen G (cmc_nk y rho (&3 * l)) w <= min e2 (min eL (e0 / &2)) /\
        cmc_srb S G mu (cmc_nk y rho (&3 * l)) w
        ==> cmc_angE y (cmc_nk y rho l) w <=
            (lam / (&18 * Lam2)) * cmc_eE (cmc_nk y rho (&3 * l)) w`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `cmc_pen G (cmc_nk (y:real^2) rho (&3 * l)) (w:real^2->real^K) <=
                 min e2 (min eL (e0 / &2))` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`l:real`; `min e2 (min eL (e0 / &2))`;
                        `max (&18 * Lam2 / (lam * mu)) (&2)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`w:real^2->real^K`; `eta:real`; `y:real^2`; `s:real`; `m:num`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= eta` ASSUME_TAC THENL
   [MATCH_MP_TAC CMC_AH_ETA_POS THEN
    MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `e0:real`;
                          `w:real^2->real^K`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= exp(&2 * l)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 + &2 * l` THEN
    REWRITE_TAC[REAL_EXP_LE_X] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s * exp(&2 * l)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `cmc_ann (y:real^2) (s * exp(&2 * l)) (s * exp((&6 * &m + &8) * l)) SUBSET
    cmc_ann y s (s * exp((&6 * &m + &10) * l))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `s <= s * exp(&2 * l) /\
                  s * exp((&6 * &m + &8) * l) <= s * exp((&6 * &m + &10) * l)`
    MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `s * &1 <= s * e ==> s <= s * e`) THEN
        ASM_SIMP_TAC[REAL_LE_LMUL_EQ];
        ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[SUBSET; cmc_ann; IN_ELIM_THM] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `eL:real`; `C:num->real`;
                 `lam:real`; `Lam:real`; `lam / (&18 * Lam2)`; `l:real`;
                 `min e2 (min eL (e0 / &2))`; `mu:real`; `e0:real`; `eta:real`;
                 `w:real^2->real^K`; `y:real^2`; `s:real`; `m:num`] CMC_B29) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LE_DIV) THEN
    ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `Lam2:real`;
                 `w:real^2->real^K`; `y:real^2`;
                 `cmc_ann (y:real^2) (s * exp(&2 * l)) (s * exp((&6 * &m + &8) * l))`]
                CMC_PEN_DEFECT_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CMC_OPEN_ANN] THEN
    REWRITE_TAC[cmc_ann; IN_ELIM_THM; VECTOR_SUB_REFL; NORM_0] THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `w:real^2->real^K`;
                 `cmc_ann (y:real^2) (s * exp(&2 * l)) (s * exp((&6 * &m + &8) * l))`;
                 `cmc_ann (y:real^2) s (s * exp((&6 * &m + &10) * l))`] CMC_DEFECT_MONO) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; CMC_OPEN_ANN]; STRIP_TAC] THEN
  USE_THEN "EP" (MP_TAC o SPECL [`w:real^2->real^K`;
                                 `cmc_ann (y:real^2) s (s * exp((&6 * &m + &10) * l))`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; CMC_OPEN_ANN]; STRIP_TAC] THEN
  ABBREV_TAC `aI = cmc_angE (y:real^2)
                     (cmc_ann y (s * exp(&2 * l)) (s * exp((&6 * &m + &8) * l)))
                     (w:real^2->real^K)` THEN
  ABBREV_TAC `eN = cmc_eE (cmc_ann (y:real^2) s (s * exp((&6 * &m + &10) * l)))
                          (w:real^2->real^K)` THEN
  SUBGOAL_THEN `(&3 * Lam2) * aI <= (lam * eN) / &2 + (&18 * Lam2 / (lam * mu)) * eta`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&3 * Lam2) * (&3 * (lam / (&18 * Lam2)) * eN + (&6 / (lam * mu)) * eta)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      SUBGOAL_THEN `~(Lam2 = &0) /\ ~(lam = &0) /\ ~(mu = &0)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= cmc_pen G (cmc_ann (y:real^2) s (s * exp((&6 * &m + &10) * l)))
                         (w:real^2->real^K) -
                       cmc_ptr G G (cmc_ann y s (s * exp((&6 * &m + &10) * l))) w`
  ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(&18 * Lam2 / (lam * mu)) * eta <= max (&18 * Lam2 / (lam * mu)) (&2) * eta /\
    &2 * (cmc_pen G (cmc_ann (y:real^2) s (s * exp((&6 * &m + &10) * l))) (w:real^2->real^K) -
          cmc_ptr G G (cmc_ann y s (s * exp((&6 * &m + &10) * l))) w) <=
    max (&18 * Lam2 / (lam * mu)) (&2) *
         (cmc_pen G (cmc_ann y s (s * exp((&6 * &m + &10) * l))) w -
          cmc_ptr G G (cmc_ann y s (s * exp((&6 * &m + &10) * l))) w)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Kc = max (&18 * Lam2 / (lam * mu)) (&2)` THEN
  ASM_REAL_ARITH_TAC);;

let CMC_PEN_ANN_SPLIT = prove
 (`!S (G:real^K->real^K^K) d (w:real^2->real^K) (y:real^2) r1 r2 r3.
     cm_target S G d /\ cmc_pmap S w /\ r1 <= r2 /\ r2 <= r3
     ==> cmc_pen G (cmc_ann y r1 r3) w =
         cmc_pen G (cmc_ann y r1 r2) w + cmc_pen G (cmc_ann y r2 r3) w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cmc_pen] THEN
  MP_TAC(ISPECL [`\x. trace(cmc_gram (G:real^K->real^K^K) (w:real^2->real^K) x)`;
                 `y:real^2`; `r1:real`; `r2:real`; `r3:real`] CMC_ANN_SPLIT) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `w:real^2->real^K`;
                 `cmc_ann (y:real^2) r1 r3`] CMC_PEN_INTEGRABLE) THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; CMC_OPEN_ANN]);;

let CMC_PEN_ANN_SPLIT3 = prove
 (`!S (G:real^K->real^K^K) d (w:real^2->real^K) (y:real^2) r0 r1 r2 r3.
     cm_target S G d /\ cmc_pmap S w /\ r0 <= r1 /\ r1 <= r2 /\ r2 <= r3
     ==> cmc_pen G (cmc_ann y r0 r3) w =
         cmc_pen G (cmc_ann y r0 r1) w + cmc_pen G (cmc_ann y r1 r2) w +
         cmc_pen G (cmc_ann y r2 r3) w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `w:real^2->real^K`;
                 `y:real^2`; `r0:real`; `r1:real`; `r3:real`] CMC_PEN_ANN_SPLIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `w:real^2->real^K`;
                 `y:real^2`; `r1:real`; `r2:real`; `r3:real`] CMC_PEN_ANN_SPLIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REAL_ARITH_TAC);;

let CMC_PEN_ANN_MONO = prove
 (`!S (G:real^K->real^K^K) d (w:real^2->real^K) (y:real^2) r1 r2 r1' r2'.
     cm_target S G d /\ cmc_pmap S w /\ r1' <= r1 /\ r2 <= r2'
     ==> cmc_pen G (cmc_ann y r1 r2) w <= cmc_pen G (cmc_ann y r1' r2') w`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CMC_PEN_MONO THEN
  MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; CMC_OPEN_ANN] THEN
  REWRITE_TAC[SUBSET; cmc_ann; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC);;

let CMC_NECK_INDEX = prove
 (`!a b l. &0 < a /\ &0 < l /\ a * exp(&10 * l) <= b
           ==> ?m. a * exp((&6 * &m + &10) * l) <= b /\
                   b < a * exp((&6 * &m + &16) * l)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?n. b < a * exp((&6 * &n + &16) * l)` MP_TAC THENL
   [MP_TAC(SPEC `l:real` REAL_ARCH) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `n:num` o SPEC `b / a`) THEN
    EXISTS_TAC `n:num` THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `a * &n * l` THEN CONJ_TAC THENL
     [UNDISCH_TAC `b / a < &n * l` THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 + (&6 * &n + &16) * l` THEN
      REWRITE_TAC[REAL_EXP_LE_X] THEN
      SUBGOAL_THEN `&0 <= &n * l` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `&0 < l` THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&6 * &(n - 1) + &16 = &6 * &n + &10` SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; ARITH_RULE `~(n = 0) ==> 1 <= n`] THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let CMC_NECK_ENERGY = prove
 (`!S (G:real^K->real^K^K) d eL (C:num->real) e0.
     cm_target S G d /\ cmc_regc S G eL C /\ &0 < e0
     ==> ?L e2 Kc. &0 < L /\ &0 < e2 /\ &0 <= Kc /\
           !(w:real^2->real^K) eta (y:real^2) a b.
             cmc_pmap S w /\ cmc_ah S G e0 eta w /\ &0 < a /\ a * exp L <= b /\
             cmc_pen G (cmc_ann y a b) w <= e2
             ==> cmc_pen G (cmc_ann y a b) w <=
                 &2 * cmc_pen G (cmc_ann y a (a * exp L)) w +
                 &2 * cmc_pen G (cmc_ann y (b * exp(--L)) b) w +
                 Kc * (eta + (cmc_pen G (cmc_ann y a b) w -
                              cmc_ptr G G (cmc_ann y a b) w))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `eL:real`; `C:num->real`;
                 `e0:real`] CMC_NECK_DECAY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real` (X_CHOOSE_THEN `e2:real` (X_CHOOSE_THEN `Kc:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ND"))))))) THEN
  MAP_EVERY EXISTS_TAC [`&10 * l`; `e2:real`; `&2 * Kc`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`w:real^2->real^K`; `eta:real`; `y:real^2`; `a:real`; `b:real`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`a:real`; `b:real`; `l:real`] CMC_NECK_INDEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 <= eta` ASSUME_TAC THENL
   [MATCH_MP_TAC CMC_AH_ETA_POS THEN
    MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `e0:real`;
                          `w:real^2->real^K`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `a <= a * exp(&2 * l) /\ a * exp(&2 * l) <= a * exp((&6 * &m + &8) * l) /\
    a * exp((&6 * &m + &8) * l) <= a * exp((&6 * &m + &10) * l) /\
    a * exp(&2 * l) <= a * exp(&10 * l) /\
    b * exp(--(&10 * l)) <= a * exp((&6 * &m + &8) * l)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_EXP_MONO_LE] THEN
    SUBGOAL_THEN `&0 <= &m * l` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `a * &1 <= a * e ==> a <= a * e`) THEN
      ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 + &2 * l` THEN
      REWRITE_TAC[REAL_EXP_LE_X] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(a * exp((&6 * &m + &16) * l)) * exp(--(&10 * l))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_EXP_POS_LE];
        REWRITE_TAC[GSYM REAL_MUL_ASSOC; GSYM REAL_EXP_ADD] THEN
        ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  USE_THEN "ND" (MP_TAC o SPECL [`w:real^2->real^K`; `eta:real`; `y:real^2`; `a:real`;
                                 `m:num`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `cmc_pen G (cmc_ann (y:real^2) a b) (w:real^2->real^K)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CMC_PEN_ANN_MONO THEN
    MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `w:real^2->real^K`;
                 `y:real^2`; `a:real`; `a * exp(&2 * l)`; `a * exp((&6 * &m + &8) * l)`;
                 `b:real`] CMC_PEN_ANN_SPLIT3) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `w:real^2->real^K`;
                 `y:real^2`; `a:real`; `a * exp(&2 * l)`; `a * exp((&6 * &m + &8) * l)`;
                 `a * exp((&6 * &m + &10) * l)`] CMC_PEN_ANN_SPLIT3) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `w:real^2->real^K`;
                 `y:real^2`; `a * exp((&6 * &m + &8) * l)`; `a * exp((&6 * &m + &10) * l)`;
                 `a * exp((&6 * &m + &8) * l)`; `b:real`] CMC_PEN_ANN_MONO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `w:real^2->real^K`;
                 `y:real^2`; `a:real`; `a * exp(&2 * l)`; `a:real`;
                 `a * exp(&10 * l)`] CMC_PEN_ANN_MONO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `w:real^2->real^K`;
                 `y:real^2`; `a * exp((&6 * &m + &8) * l)`; `b:real`;
                 `b * exp(--(&10 * l))`; `b:real`] CMC_PEN_ANN_MONO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `w:real^2->real^K`;
                 `cmc_ann (y:real^2) a (a * exp((&6 * &m + &10) * l))`;
                 `cmc_ann (y:real^2) a b`] CMC_DEFECT_MONO) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; CMC_OPEN_ANN] THEN
    REWRITE_TAC[SUBSET; cmc_ann; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC] THEN
  SUBGOAL_THEN
   `Kc * (eta + (cmc_pen G (cmc_ann (y:real^2) a (a * exp((&6 * &m + &10) * l)))
                         (w:real^2->real^K) -
                 cmc_ptr G G (cmc_ann y a (a * exp((&6 * &m + &10) * l))) w)) <=
    Kc * (eta + (cmc_pen G (cmc_ann y a b) w - cmc_ptr G G (cmc_ann y a b) w))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

